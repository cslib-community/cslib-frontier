/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.WordRAM.Resizable.Randomized.HighProbability
public import CslibFrontier.DataStructure.Dictionary.Dynamic.Spec
public import CslibFrontier.DataStructure.Dictionary.WordRAM.BitPackedArray
import CslibFrontier.Foundations.Analysis.ENNRealTsum
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.SupportTsum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Shared `1 · OPT` Incremental Background Rebuild and Dual-Epoch Deamortization

This module develops a model-faithful, reusable incremental background rebuild and dual-epoch
(`DualEpoch`) deamortization framework on the word-granular **Resizable Word RAM**
(`Cslib.WordRAM.Resizable`), shared across resizable succinct data structures with high-probability
worst-case step bounds—including both the resizable SOSA 2024 succinct dictionary
([Bender, Farach-Colton, J. Kuszmaul, and W. Kuszmaul, SOSA 2024,
Sections 5–6][BenderFarachColtonKuszmaulKuszmaul2024]) and resizable deamortized `k`-kick trees
([W. Kuszmaul, J. Liang, and R. Zhou, SODA 2026, Section 5.1][KuszmaulLiangZhou2026]).

## Why naive Overmars global rebuilding exceeds `1 · OPT`

Standard Overmars global rebuilding maintains both an old table and a shadow table simultaneously,
duplicating the `OPT`-bit payload array and reaching `2 · OPT` space during migration. Storing both
epochs at opposite ends of a fixed-capacity arena `(n_trig + Q) · w_slot` likewise exceeds `1 · OPT`
whenever the caller performs deletions during migration.

## Strict `1 · OPT` `DualEpoch` architecture

1. **Single-epoch capacity safe-band invariant (`EpochCapSafe`):**
   Capacity `0` denotes the small below-threshold regime (`n_t < 2 · threshold`, `0` epoch metadata
   words), while capacities `N ≥ threshold` denote large hashed epochs (`N / 4 < n_t ≤ N ≤ U`).
2. **Deamortized `1 · OPT` paged pair arena (`PagePairState`) and succinct word accounting:**
   During background migration, `PagePairState` exposes two independent `0`-based dense item
   arrays `V_false[0 .. n_0)` (`E_src`) and `V_true[0 .. n_1)` (`E_dst`) backed by **exact**
   `n_0 + n_1 = n_t` physical slots (`0` extra item slots, valid even when `V = 2 ^ w` and `w ≫ N`)
   using `O(N)` page-directory bits (`dualEpochWords_le_optBits_add`,
   `dualEpochWords_le_succinctWords`), with `O(1)` worst-case deamortized `stepAppend`,
   `stepPopBack`, and background page promotion/demotion ticks.
3. **Distributional WHP state-transition deamortizer (`HighProbStateTransitionImpl`):**
   Couples a functional `StateTransitionSpec` (`[D.HasStepFn stepFn]`) with a distributional
   invariant `distInv` (accommodating stored epoch hash seeds sampled during `init` or background
   migration) and rare `≤ failureProb s o` fallback to certified `1 · OPT` `ExecRCodeDist` recovery,
   lifting automatically to `HighProbObliviousImpl` via `toHighProbObliviousImpl`.

## Main definitions

* `Cslib.DataStructure.WordRAM.Resizable.Randomized.EpochCapSafe`: single-epoch capacity safe-band
  predicate across the small (`N = 0`) and large hashed (`threshold ≤ N`) regimes.
* `Cslib.DataStructure.WordRAM.Resizable.Randomized.PagePairState`, `PagePairState.Valid`,
  `PagePairState.WellBalanced`, `PagePairState.stepAppend`, `PagePairState.stepPopBack`:
  `1 · OPT` shared physical arena for two virtual dense arrays.
* `Cslib.DataStructure.WordRAM.Resizable.Randomized.HighProbStateTransitionImpl`:
  distributional WHP state-transition certificate with `.toHighProbObliviousImpl`.

## Main results

* `PagePairState.stepAppend_spec`, `PagePairState.stepPopBack_spec`: virtual-array preservation,
  `Valid` / `WellBalanced` maintenance, and bounded `PhysSwap` counts (`≤ 17`) per append/pop.
* `dualEpochWords_le_optBits_add`, `dualEpochWords_le_succinctWords`: general `1 · OPT` word-space
  theorems parameterized by an arbitrary redundancy function `redFn : ℕ → ℕ` and specialized to
  `Dynamic.succinctWords`.
* `HighProbStateTransitionImpl.toHighProbObliviousImpl`: union-bound sequence lifting to
  `HighProbObliviousImpl`.

## References

* [M. A. Bender, M. Farach-Colton, J. Kuszmaul, and W. Kuszmaul, *Modern Hashing Made Simple*,
  Sections 5–6][BenderFarachColtonKuszmaulKuszmaul2024]
* [W. Kuszmaul, J. Liang, and R. Zhou, *Succinct Dynamic Rank/Select: Bypassing the Tree-Structure
  Bottleneck*, Section 5.1][KuszmaulLiangZhou2026]
-/

public section

open scoped ENNReal

namespace Cslib.DataStructure.WordRAM.Resizable.Randomized

open Cslib.WordRAM Cslib.WordRAM.Resizable Cslib.DataStructure Cslib.Probability
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.WordRAM.Resizable

/-! ## Section 1: Single-Epoch Capacity Safe-Band Invariant (`EpochCapSafe`) -/

/-- Single-epoch safe-band invariant for epoch capacity `N` (`0` = small regime, `> 0` = hashed
large epoch) at live item count `n_t` under universe `U` and cutoff `threshold`. -/
@[expose] def EpochCapSafe (threshold U N n_t : ℕ) : Prop :=
  if N = 0 then
    n_t < 2 * threshold ∧ n_t ≤ U
  else
    threshold ≤ N ∧ N ≤ U ∧ N < 4 * n_t ∧ n_t ≤ N

/-! ## Section 2: Shared `1 · OPT` Paged Pair Arena (`PagePairState`) & Succinct Space Bounds -/

/-- Elementary physical swap between slots `p₁` and `p₂` in the shared `[0, totalItems)` arena. -/
structure PhysSwap where
  /-- First physical slot index in `[0, totalItems)`. -/
  p₁ : ℕ
  /-- Second physical slot index in `[0, totalItems)`. -/
  p₂ : ℕ
  deriving DecidableEq, Repr

namespace PhysSwap

/-- Apply a single physical swap `(p₁ ↔ p₂)` to an arbitrary slot array `arr : ℕ → α`. -/
@[expose] def apply {α : Type*} (sw : PhysSwap) (arr : ℕ → α) : ℕ → α :=
  if sw.p₁ = sw.p₂ then
    arr
  else
    Function.update (Function.update arr sw.p₁ (arr sw.p₂)) sw.p₂ (arr sw.p₁)

@[simp] theorem apply_p₁ {α : Type*} (sw : PhysSwap) (arr : ℕ → α) :
    sw.apply arr sw.p₁ = arr sw.p₂ := by
  unfold apply
  split_ifs with h
  · rw [h]
  · rw [Function.update_of_ne h, Function.update_self]

@[simp] theorem apply_p₂ {α : Type*} (sw : PhysSwap) (arr : ℕ → α) :
    sw.apply arr sw.p₂ = arr sw.p₁ := by
  unfold apply
  split_ifs with h
  · rw [h]
  · rw [Function.update_self]

theorem apply_of_ne {α : Type*} (sw : PhysSwap) (arr : ℕ → α) {p : ℕ}
    (h₁ : p ≠ sw.p₁) (h₂ : p ≠ sw.p₂) :
    sw.apply arr p = arr p := by
  unfold apply
  split_ifs
  · rfl
  · rw [Function.update_of_ne h₂, Function.update_of_ne h₁]

end PhysSwap

/-- Apply a list of physical swaps left-to-right to `arr : ℕ → α`. -/
@[expose] def applySwaps {α : Type*} (sws : List PhysSwap) (arr : ℕ → α) : ℕ → α :=
  sws.foldl (fun a sw => sw.apply a) arr

@[simp] theorem applySwaps_nil {α : Type*} (arr : ℕ → α) :
    applySwaps [] arr = arr := rfl

@[simp] theorem applySwaps_cons {α : Type*} (sw : PhysSwap) (sws : List PhysSwap) (arr : ℕ → α) :
    applySwaps (sw :: sws) arr = applySwaps sws (sw.apply arr) := rfl

theorem applySwaps_append {α : Type*} (sws₁ sws₂ : List PhysSwap) (arr : ℕ → α) :
    applySwaps (sws₁ ++ sws₂) arr = applySwaps sws₂ (applySwaps sws₁ arr) :=
  List.foldl_append

/-- Recover `p - base` in `O(1)` from `p % M` whenever `base ≤ p < base + M`. -/
theorem offsetOfMod {M base p : ℕ} (hM : 0 < M) (hlo : base ≤ p) (hhi : p < base + M) :
    (p % M + M - base % M) % M = p - base := by
  set d := p - base
  have hd_lt : d < M := by omega
  have hb_lt : base % M < M := Nat.mod_lt base hM
  have hdiv := Nat.div_add_mod base M
  by_cases hsum : base % M + d < M
  · have hp_eq : p = (base % M + d) + M * (base / M) := by omega
    have hmod : p % M = base % M + d := by
      rw [hp_eq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hsum]
    rw [hmod, show base % M + d + M - base % M = d + M by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt hd_lt]
  · have hsub_lt : base % M + d - M < M := by omega
    have hp_eq : p = (base % M + d - M) + M * (base / M + 1) := by
      rw [Nat.mul_add, Nat.mul_one]; omega
    have hmod : p % M = base % M + d - M := by
      rw [hp_eq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hsub_lt]
    rw [hmod, show base % M + d - M + M - base % M = d by omega, Nat.mod_eq_of_lt hd_lt]

/-- Modular inverse identity `(base + (res + M - base % M) % M) % M = res` for `res < M`. -/
theorem add_offset_mod {M base res : ℕ} (hres : res < M) :
    (base + (res + M - base % M) % M) % M = res := by
  have hM : 0 < M := by omega
  have hb_lt : base % M < M := Nat.mod_lt base hM
  calc (base + (res + M - base % M) % M) % M
      = (base % M + (res + M - base % M) % M % M) % M := Nat.add_mod _ _ _
    _ = ((base % M) % M + (res + M - base % M) % M) % M := by
          rw [Nat.mod_mod base M, Nat.mod_mod _ M]
    _ = (base % M + (res + M - base % M)) % M := (Nat.add_mod _ _ _).symm
    _ = (res + M) % M := by congr 1; omega
    _ = res := by rw [Nat.add_mod_right, Nat.mod_eq_of_lt hres]

/-- Modulo `M` is injective on any interval `[L, L + M)` of length `M`. -/
theorem mod_inj_of_range {M L a b : ℕ} (hM : 0 < M)
    (ha_lo : L ≤ a) (ha_hi : a < L + M) (hb_lo : L ≤ b) (hb_hi : b < L + M)
    (heq : a % M = b % M) : a = b := by
  have ha := offsetOfMod hM ha_lo ha_hi
  have hb := offsetOfMod hM hb_lo hb_hi
  rw [heq] at ha
  omega

/-- Reconstruct physical tail index `p ∈ [base, base + 8 * B)` from `res = p % (8 * B)`. -/
@[expose] def physOfRes (base B res : ℕ) : ℕ :=
  base + (res + 8 * B - base % (8 * B)) % (8 * B)

theorem le_physOfRes (base B res : ℕ) : base ≤ physOfRes base B res :=
  Nat.le_add_right _ _

theorem physOfRes_lt {base B res : ℕ} (hB : 0 < B) :
    physOfRes base B res < base + 8 * B :=
  Nat.add_lt_add_left (Nat.mod_lt _ (by positivity)) base

theorem physOfRes_mod {base B p : ℕ} (hB : 0 < B) (hlo : base ≤ p) (hhi : p < base + 8 * B) :
    physOfRes base B (p % (8 * B)) = p := by
  unfold physOfRes
  rw [offsetOfMod (by positivity) hlo hhi]
  omega

theorem mod_physOfRes {base B res : ℕ} (hres : res < 8 * B) :
    physOfRes base B res % (8 * B) = res :=
  add_offset_mod hres

/-- Recover logical tail offset `t < 4 * B` from ring slot `k = (head + t) % (4 * B)`. -/
@[expose] def ringIdxOfSlot (head B k : ℕ) : ℕ :=
  (k + 4 * B - head % (4 * B)) % (4 * B)

theorem ringIdxOfSlot_mod {head B t : ℕ} (hB : 0 < B) (ht : t < 4 * B) :
    ringIdxOfSlot head B ((head + t) % (4 * B)) = t := by
  unfold ringIdxOfSlot
  have h := offsetOfMod (M := 4 * B) (base := head) (p := head + t) (by positivity)
    (Nat.le_add_right _ _) (Nat.add_lt_add_left ht head)
  omega

theorem mod_add_ringIdxOfSlot {head B k : ℕ} (hk : k < 4 * B) :
    (head + ringIdxOfSlot head B k) % (4 * B) = k :=
  add_offset_mod hk

/-- Background page-promotion / page-demotion cursor state for `PagePairState`. -/
inductive PageJob : Type where
  /-- No page transition in flight. -/
  | idle
  /-- Promoting `B` tail entries `0 .. B - 1` of `side` into physical page `Q` (`cur ≤ B`). -/
  | promote (side : Bool) (cur : ℕ)
  /-- Swapping physical page `pageOf side (q_side - 1)` with `Q - 1` (`cur ≤ B`). -/
  | demoteSwap (side : Bool) (cur : ℕ)
  /-- Staging `B` tail directory entries for physical page `Q - 1` before decrementing `Q`
  (`cur ≤ B`). -/
  | demoteBuild (side : Bool) (cur : ℕ)
  deriving DecidableEq, Repr

/-- Named pure metadata state of the `1 · OPT` shared two-array paged arena (`0` projection chains).
Exposes two independent `0`-based virtual arrays `V_false[0 .. virtLen false)` (`E_src`) and
`V_true[0 .. virtLen true)` (`E_dst`) backed by **exact** `virtLen false + virtLen true = n_t`
physical slots `[0, n_t)`, with circular `4 * B` per-side tail rings and `8 * B` physical residue
indexing so promotion and demotion commit in `O(1)` without bulk array shifts. -/
structure PagePairState where
  /-- Page size `B` (`32 ≤ B` under `WellBalanced`, `B = max 32 (Nat.clog 2 (N + 2))` uses `O(N)`
  total metadata bits). -/
  pageSize : ℕ
  /-- Virtual full-page count `q_side` for `side ∈ {false, true}`. -/
  fullPages : Bool → ℕ
  /-- Tail item count `r_side < 4 * B` (`virtLen side = fullPages side * pageSize + tailCount
  side`). -/
  tailCount : Bool → ℕ
  /-- Circular ring head `< 4 * B` for `side`'s tail directory. -/
  tailHead : Bool → ℕ
  /-- Physical page index `P < totalPages` assigned to `(side, vp)`. -/
  pageOf : Bool → ℕ → ℕ
  /-- Inverse side of physical page `P < totalPages`. -/
  ownerSide : ℕ → Bool
  /-- Inverse virtual page index of physical page `P < totalPages`. -/
  ownerVp : ℕ → ℕ
  /-- Residue `p % (8 * B)` of tail ring slot `k < 4 * B` of `side`. -/
  tailRes : Bool → ℕ → ℕ
  /-- Inverse side of physical tail residue `res = p % (8 * B) < 8 * B`. -/
  tailOwnerSide : ℕ → Bool
  /-- Inverse ring slot `< 4 * B` of physical tail residue `res = p % (8 * B) < 8 * B`. -/
  tailOwnerRing : ℕ → ℕ
  /-- Active incremental page promotion/demotion job. -/
  job : PageJob

namespace PagePairState

/-- Update a two-argument `(Bool → ℕ → ℕ)` table at `(s, k)`. -/
@[expose] def set2 (f : Bool → ℕ → ℕ) (s : Bool) (k val : ℕ) : Bool → ℕ → ℕ :=
  fun s' k' => if s' = s ∧ k' = k then val else f s' k'

@[simp] theorem set2_self (f : Bool → ℕ → ℕ) (s : Bool) (k val : ℕ) :
    set2 f s k val s k = val := by simp [set2]

theorem set2_of_ne (f : Bool → ℕ → ℕ) (s s' : Bool) (k k' val : ℕ)
    (hne : ¬(s' = s ∧ k' = k)) :
    set2 f s k val s' k' = f s' k' := by simp [set2, hne]

/-- Total committed physical pages `Q = fullPages false + fullPages true`. -/
@[expose] def totalPages (st : PagePairState) : ℕ :=
  st.fullPages false + st.fullPages true

/-- Virtual length `n_side = fullPages side * pageSize + tailCount side` of array `side`. -/
@[expose] def virtLen (st : PagePairState) (side : Bool) : ℕ :=
  st.fullPages side * st.pageSize + st.tailCount side

/-- Total physical slot count `n_t = virtLen false + virtLen true` (`0` extra item slots). -/
@[expose] def totalItems (st : PagePairState) : ℕ :=
  st.virtLen false + st.virtLen true

/-- Total physical items equals `totalPages * pageSize + tailCount false + tailCount true`. -/
theorem totalItems_eq (st : PagePairState) :
    st.totalItems =
      st.totalPages * st.pageSize + st.tailCount false + st.tailCount true := by
  unfold totalItems virtLen totalPages
  ring

/-- Effective physical page for `(P, u)` accounting for an in-flight `demoteSwap` on `0 .. cur - 1`.
Acts as an involution on `[0, totalPages)` for each fixed intra-page offset `u`. -/
@[expose] def effPage (st : PagePairState) (P u : ℕ) : ℕ :=
  match st.job with
  | .demoteSwap s cur =>
    if u < cur ∧ 0 < st.fullPages s then
      let P_dem := st.pageOf s (st.fullPages s - 1)
      let P_last := st.totalPages - 1
      if P = P_dem then P_last
      else if P = P_last then P_dem
      else P
    else P
  | _ => P

/-- Circular ring index `(tailHead side + t) % (4 * pageSize)` of tail offset `t`. -/
@[expose] def ringSlot (st : PagePairState) (side : Bool) (t : ℕ) : ℕ :=
  (st.tailHead side + t) % (4 * st.pageSize)

/-- Physical slot `p ∈ [totalPages * pageSize, totalItems)` of tail entry `(side, t)`. -/
@[expose] def tailPhys (st : PagePairState) (side : Bool) (t : ℕ) : ℕ :=
  physOfRes (st.totalPages * st.pageSize) st.pageSize (st.tailRes side (st.ringSlot side t))

/-- `O(1)` translation from virtual coordinate `(side, idx)` (`idx < virtLen side`) to physical slot
`p < totalItems`. -/
@[expose] def toPhys (st : PagePairState) (side : Bool) (idx : ℕ) : ℕ :=
  let fullLim := st.fullPages side * st.pageSize
  if idx < fullLim then
    st.effPage (st.pageOf side (idx / st.pageSize)) (idx % st.pageSize) * st.pageSize +
      idx % st.pageSize
  else
    st.tailPhys side (idx - fullLim)

/-- Logical read at virtual coordinate `(side, idx)` from any physical slot array `arr : ℕ → α`. -/
@[expose] def virtAt {α : Type*} (st : PagePairState) (arr : ℕ → α) (side : Bool) (idx : ℕ) : α :=
  arr (st.toPhys side idx)

/-- Structural bijection invariant certifying that `toPhys` maps `(false, [0, virtLen false)) ⊔
(true, [0, virtLen true))` **bijectively** onto `[0, totalItems)`. -/
structure Valid (st : PagePairState) : Prop where
  pageSize_pos : 0 < st.pageSize
  tailCount_lt : ∀ side, st.tailCount side < 4 * st.pageSize
  tailSum_lt : st.tailCount false + st.tailCount true < 8 * st.pageSize
  tailHead_lt : ∀ side, st.tailHead side < 4 * st.pageSize
  page_lt : ∀ side vp, vp < st.fullPages side → st.pageOf side vp < st.totalPages
  owner_pageOf : ∀ side vp, vp < st.fullPages side →
    st.ownerSide (st.pageOf side vp) = side ∧ st.ownerVp (st.pageOf side vp) = vp
  pageOf_owner : ∀ P, P < st.totalPages →
    st.ownerVp P < st.fullPages (st.ownerSide P) ∧
      st.pageOf (st.ownerSide P) (st.ownerVp P) = P
  tailRes_lt : ∀ side t, t < st.tailCount side →
    st.tailRes side (st.ringSlot side t) < 8 * st.pageSize
  tail_lt : ∀ side t, t < st.tailCount side →
    st.tailPhys side t < st.totalItems
  owner_tail : ∀ side t, t < st.tailCount side →
    let res := st.tailRes side (st.ringSlot side t)
    st.tailOwnerSide res = side ∧ st.tailOwnerRing res = st.ringSlot side t
  tail_owner : ∀ p, st.totalPages * st.pageSize ≤ p → p < st.totalItems →
    let res := p % (8 * st.pageSize)
    let side := st.tailOwnerSide res
    let k := st.tailOwnerRing res
    let t := ringIdxOfSlot (st.tailHead side) st.pageSize k
    k < 4 * st.pageSize ∧ t < st.tailCount side ∧ st.tailPhys side t = p

theorem Valid.effPage_lt {st : PagePairState} (hv : st.Valid) {P : ℕ} (hP : P < st.totalPages)
    (u : ℕ) : st.effPage P u < st.totalPages := by
  unfold effPage
  cases st.job with
  | demoteSwap s cur =>
    dsimp only
    split_ifs with hc h1 h2
    · omega
    · exact hv.page_lt s (st.fullPages s - 1) (by omega)
    · exact hP
    · exact hP
  | _ => exact hP

theorem effPage_involutive (st : PagePairState) (P u : ℕ) :
    st.effPage (st.effPage P u) u = P := by
  unfold effPage
  cases st.job with
  | demoteSwap s cur =>
    dsimp only
    by_cases hc : u < cur ∧ 0 < st.fullPages s
    · simp only [hc, and_self, ↓reduceIte]
      set Pd := st.pageOf s (st.fullPages s - 1)
      set Pl := st.totalPages - 1
      by_cases h1 : P = Pd
      · subst h1; split_ifs <;> omega
      · by_cases h2 : P = Pl
        · subst h2; simp [h1]
        · simp [h1, h2]
    · simp [hc]
  | _ => rfl

/-- Every valid virtual coordinate `(side, idx)` (`idx < st.virtLen side`) maps to a physical slot
strictly below `st.totalItems`. -/
theorem Valid.toPhys_lt {st : PagePairState} (hv : st.Valid) {side : Bool} {idx : ℕ}
    (hidx : idx < st.virtLen side) :
    st.toPhys side idx < st.totalItems := by
  unfold toPhys
  dsimp only
  split_ifs with hlt
  · have hvp : idx / st.pageSize < st.fullPages side :=
      (Nat.div_lt_iff_lt_mul hv.pageSize_pos).mpr hlt
    have hp_lt := hv.effPage_lt (hv.page_lt side (idx / st.pageSize) hvp) (idx % st.pageSize)
    have hmod := Nat.mod_lt idx hv.pageSize_pos
    have hle : (st.effPage (st.pageOf side (idx / st.pageSize)) (idx % st.pageSize) + 1) *
        st.pageSize ≤ st.totalPages * st.pageSize := Nat.mul_le_mul_right _ hp_lt
    rw [Nat.add_mul, Nat.one_mul] at hle
    rw [st.totalItems_eq]
    omega
  · unfold virtLen at hidx
    exact hv.tail_lt side _ (by omega)

/-- **Injectivity of `toPhys` across both virtual arrays (`Valid.toPhys_inj`).**
Distinct virtual coordinates `(side₁, idx₁) ≠ (side₂, idx₂)` NEVER alias to the same physical slot
in `[0, st.totalItems)`. -/
theorem Valid.toPhys_inj {st : PagePairState} (hv : st.Valid)
    {side₁ side₂ : Bool} {idx₁ idx₂ : ℕ}
    (h₁ : idx₁ < st.virtLen side₁) (h₂ : idx₂ < st.virtLen side₂)
    (heq : st.toPhys side₁ idx₁ = st.toPhys side₂ idx₂) :
    side₁ = side₂ ∧ idx₁ = idx₂ := by
  unfold toPhys at heq
  dsimp only at heq
  have hpage_lt : ∀ s i, i < st.fullPages s * st.pageSize →
      st.effPage (st.pageOf s (i / st.pageSize)) (i % st.pageSize) * st.pageSize +
        i % st.pageSize < st.totalPages * st.pageSize := fun s i hi => by
    have hvp : i / st.pageSize < st.fullPages s :=
      (Nat.div_lt_iff_lt_mul hv.pageSize_pos).mpr hi
    have hp_lt := hv.effPage_lt (hv.page_lt s (i / st.pageSize) hvp) (i % st.pageSize)
    have hmod := Nat.mod_lt i hv.pageSize_pos
    have hle : (st.effPage (st.pageOf s (i / st.pageSize)) (i % st.pageSize) + 1) *
        st.pageSize ≤ st.totalPages * st.pageSize := Nat.mul_le_mul_right _ hp_lt
    rw [Nat.add_mul, Nat.one_mul] at hle
    omega
  split_ifs at heq with hf₁ hf₂ hf₂
  · have hmod₁ := Nat.mod_lt idx₁ hv.pageSize_pos
    have hmod₂ := Nat.mod_lt idx₂ hv.pageSize_pos
    have heff_eq : st.effPage (st.pageOf side₁ (idx₁ / st.pageSize)) (idx₁ % st.pageSize) =
        st.effPage (st.pageOf side₂ (idx₂ / st.pageSize)) (idx₂ % st.pageSize) := by
      have h1 : (st.effPage (st.pageOf side₁ (idx₁ / st.pageSize)) (idx₁ % st.pageSize) *
          st.pageSize + idx₁ % st.pageSize) / st.pageSize =
            st.effPage (st.pageOf side₁ (idx₁ / st.pageSize)) (idx₁ % st.pageSize) := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ hv.pageSize_pos,
          Nat.div_eq_of_lt hmod₁, zero_add]
      have h2 : (st.effPage (st.pageOf side₂ (idx₂ / st.pageSize)) (idx₂ % st.pageSize) *
          st.pageSize + idx₂ % st.pageSize) / st.pageSize =
            st.effPage (st.pageOf side₂ (idx₂ / st.pageSize)) (idx₂ % st.pageSize) := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ hv.pageSize_pos,
          Nat.div_eq_of_lt hmod₂, zero_add]
      rw [← h1, ← h2, heq]
    have hrem_eq : idx₁ % st.pageSize = idx₂ % st.pageSize := by
      rw [heff_eq] at heq; omega
    rw [hrem_eq] at heff_eq
    have hdiv_eq : st.pageOf side₁ (idx₁ / st.pageSize) =
        st.pageOf side₂ (idx₂ / st.pageSize) := by
      have hi := congrArg (fun P => st.effPage P (idx₂ % st.pageSize)) heff_eq
      simpa only [effPage_involutive] using hi
    have hvp₁ : idx₁ / st.pageSize < st.fullPages side₁ :=
      (Nat.div_lt_iff_lt_mul hv.pageSize_pos).mpr hf₁
    have hvp₂ : idx₂ / st.pageSize < st.fullPages side₂ :=
      (Nat.div_lt_iff_lt_mul hv.pageSize_pos).mpr hf₂
    have ho₁ := hv.owner_pageOf side₁ (idx₁ / st.pageSize) hvp₁
    have ho₂ := hv.owner_pageOf side₂ (idx₂ / st.pageSize) hvp₂
    rw [hdiv_eq] at ho₁
    refine ⟨ho₁.1.symm.trans ho₂.1, ?_⟩
    have hd₁ := Nat.div_add_mod idx₁ st.pageSize
    have hd₂ := Nat.div_add_mod idx₂ st.pageSize
    rw [ho₁.2.symm.trans ho₂.2, hrem_eq] at hd₁
    omega
  · exfalso
    have hlt := hpage_lt side₁ idx₁ hf₁
    have hge := le_physOfRes (st.totalPages * st.pageSize) st.pageSize
      (st.tailRes side₂ (st.ringSlot side₂ (idx₂ - st.fullPages side₂ * st.pageSize)))
    change _ ≤ st.tailPhys side₂ _ at hge
    omega
  · exfalso
    have hlt := hpage_lt side₂ idx₂ hf₂
    have hge := le_physOfRes (st.totalPages * st.pageSize) st.pageSize
      (st.tailRes side₁ (st.ringSlot side₁ (idx₁ - st.fullPages side₁ * st.pageSize)))
    change _ ≤ st.tailPhys side₁ _ at hge
    omega
  · set t₁ := idx₁ - st.fullPages side₁ * st.pageSize
    set t₂ := idx₂ - st.fullPages side₂ * st.pageSize
    have ht₁ : t₁ < st.tailCount side₁ := by unfold virtLen at h₁; omega
    have ht₂ : t₂ < st.tailCount side₂ := by unfold virtLen at h₂; omega
    have hmod_eq : st.tailRes side₁ (st.ringSlot side₁ t₁) =
        st.tailRes side₂ (st.ringSlot side₂ t₂) := by
      have hm₁ := mod_physOfRes (base := st.totalPages * st.pageSize)
        (hv.tailRes_lt side₁ t₁ ht₁)
      have hm₂ := mod_physOfRes (base := st.totalPages * st.pageSize)
        (hv.tailRes_lt side₂ t₂ ht₂)
      change st.tailPhys side₁ t₁ % _ = _ at hm₁
      change st.tailPhys side₂ t₂ % _ = _ at hm₂
      rw [← hm₁, ← hm₂, heq]
    have ho₁ := hv.owner_tail side₁ t₁ ht₁
    have ho₂ := hv.owner_tail side₂ t₂ ht₂
    dsimp only at ho₁ ho₂
    rw [hmod_eq] at ho₁
    have hs_eq : side₁ = side₂ := ho₁.1.symm.trans ho₂.1
    subst hs_eq
    have hr_eq : st.ringSlot side₁ t₁ = st.ringSlot side₁ t₂ := ho₁.2.symm.trans ho₂.2
    have hri₁ := ringIdxOfSlot_mod (head := st.tailHead side₁) hv.pageSize_pos
      (ht₁.trans (hv.tailCount_lt side₁))
    have hri₂ := ringIdxOfSlot_mod (head := st.tailHead side₁) hv.pageSize_pos
      (ht₂.trans (hv.tailCount_lt side₁))
    change ringIdxOfSlot _ _ (st.ringSlot side₁ t₁) = t₁ at hri₁
    change ringIdxOfSlot _ _ (st.ringSlot side₁ t₂) = t₂ at hri₂
    rw [hr_eq] at hri₁
    have ht_eq : t₁ = t₂ := hri₁.symm.trans hri₂
    exact ⟨rfl, by omega⟩

/-- Active-job structural invariant for `promote`, `demoteSwap`, and `demoteBuild`. -/
@[expose] def JobValid (st : PagePairState) : Prop :=
  match st.job with
  | .idle => True
  | .promote s cur =>
    cur ≤ st.pageSize ∧ st.pageSize < st.tailCount s ∧
      ∀ u < cur, st.tailPhys s u = st.totalPages * st.pageSize + u
  | .demoteSwap s cur =>
    cur ≤ st.pageSize ∧ 0 < st.fullPages s ∧
      st.pageOf s (st.fullPages s - 1) < st.totalPages - 1
  | .demoteBuild s cur =>
    cur ≤ st.pageSize ∧ 0 < st.fullPages s ∧
      st.pageOf s (st.fullPages s - 1) = st.totalPages - 1 ∧
      st.tailCount s < 3 * st.pageSize ∧
      st.tailCount false + st.tailCount true ≤ 7 * st.pageSize ∧
      ∀ u < cur,
        let k := (st.tailHead s + 3 * st.pageSize + u) % (4 * st.pageSize)
        let res := ((st.totalPages - 1) * st.pageSize + u) % (8 * st.pageSize)
        st.tailRes s k = res ∧ st.tailOwnerSide res = s ∧ st.tailOwnerRing res = k

/-- Tail deviation from the interior target `2 * B`. -/
@[expose] def dev (B q r : ℕ) : ℕ :=
  max (r - 2 * B) (if 0 < q then 2 * B - r else 0)

/-- Summed tail deviation across `false` (`E_src`) and `true` (`E_dst`). -/
@[expose] def phi (st : PagePairState) : ℕ :=
  dev st.pageSize (st.fullPages false) (st.tailCount false) +
    dev st.pageSize (st.fullPages true) (st.tailCount true)

/-- Remaining ticks (`≤ 2 * B + 2`) until `st.job` commits to `.idle`. -/
@[expose] def remTicks (st : PagePairState) : ℕ :=
  match st.job with
  | .idle => 0
  | .promote _ cur => st.pageSize + 1 - cur
  | .demoteSwap _ cur => 2 * st.pageSize + 2 - cur
  | .demoteBuild _ cur => st.pageSize + 1 - cur

/-- Drift bound on the active job's own side with slack `K_side` (`6 * B + 2` at rest). -/
@[expose] def ActiveSideBound (st : PagePairState) (K_side : ℕ) : Prop :=
  match st.job with
  | .idle => True
  | .promote s _ =>
    16 * (3 * st.pageSize - st.tailCount s) + st.remTicks ≤ K_side
  | .demoteSwap s _ | .demoteBuild s _ =>
    16 * (st.tailCount s - st.pageSize) + st.remTicks ≤ K_side

/-- **Hysteresis & Deamortization Invariant (`WellBalanced`).**
Guarantees `32 ≤ pageSize`, `Valid`, `JobValid`, `tailCount s < 4 * B`, `tailSum ≤ 6 * B`, and
`0 < tailCount s` whenever `0 < fullPages s`, preserved by `O(1)`-worst-case `stepAppend` and
`stepPopBack` (`16` background ticks per call). -/
structure WellBalanced (st : PagePairState) : Prop where
  valid : st.Valid
  pageSize_ge : 32 ≤ st.pageSize
  jobValid : st.JobValid
  pot_bound : if st.job = .idle then
      16 * st.phi ≤ 24 * st.pageSize - 8
    else
      16 * st.phi + st.remTicks ≤ 28 * st.pageSize
  side_bound : st.ActiveSideBound (6 * st.pageSize + 2)

theorem WellBalanced.phi_le {st : PagePairState} (hw : st.WellBalanced) :
    16 * st.phi ≤ 28 * st.pageSize := by
  have hp := hw.pot_bound
  have hB := hw.pageSize_ge
  split_ifs at hp <;> omega

theorem WellBalanced.tailCount_le {st : PagePairState} (hw : st.WellBalanced) (side : Bool) :
    4 * st.tailCount side ≤ 15 * st.pageSize := by
  have hp := hw.phi_le
  unfold phi dev at hp
  cases side <;> omega

theorem WellBalanced.tailSum_le {st : PagePairState} (hw : st.WellBalanced) :
    4 * (st.tailCount false + st.tailCount true) ≤ 23 * st.pageSize := by
  have hp := hw.phi_le
  unfold phi dev at hp
  omega

theorem WellBalanced.tailCount_pos_of_fullPages {st : PagePairState} (hw : st.WellBalanced)
    {side : Bool} (hq : 0 < st.fullPages side) :
    0 < st.tailCount side := by
  have hp := hw.phi_le
  have hB := hw.pageSize_ge
  unfold phi dev at hp
  cases side <;> simp only [hq, ↓reduceIte] at hp <;> omega

theorem WellBalanced.tailCount_pos_of_virtLen {st : PagePairState} (hw : st.WellBalanced)
    {side : Bool} (hv : 0 < st.virtLen side) :
    0 < st.tailCount side := by
  by_cases hq : 0 < st.fullPages side
  · exact hw.tailCount_pos_of_fullPages hq
  · have hq0 : st.fullPages side = 0 := by omega
    unfold virtLen at hv
    rw [hq0, zero_mul, zero_add] at hv
    exact hv

/-- Canonical Phase-2 entry `PagePairState` (`virtLen false = n_0`, `virtLen true = 0`,
`WellBalanced`, and identity physical mapping `toPhys false i = i` on `[0, n_0)`—zero item
movement at Phase 1 → Phase 2 handoff). -/
@[expose] def initFromSrc (B n_0 : ℕ) : PagePairState :=
  let B' := max B 32
  let base_r := B' + B' / 2
  let q_0 := if n_0 < B' + base_r then 0 else (n_0 - base_r) / B'
  let r_0 := n_0 - q_0 * B'
  { pageSize := B'
    fullPages := fun side => if side then 0 else q_0
    tailCount := fun side => if side then 0 else r_0
    tailHead := fun _ => 0
    pageOf := fun _ vp => vp
    ownerSide := fun _ => false
    ownerVp := fun P => P
    tailRes := fun _ k => (q_0 * B' + k) % (8 * B')
    tailOwnerSide := fun _ => false
    tailOwnerRing := fun res => (res + 8 * B' - (q_0 * B') % (8 * B')) % (8 * B')
    job := .idle }

/-- `initFromSrc B n_0` satisfies `WellBalanced` (and `Valid`), has `virtLen false = n_0`,
`virtLen true = 0`, and maps every `idx < n_0` identically to physical slot `idx`. -/
theorem wellBalanced_initFromSrc (B n_0 : ℕ) :
    let st := initFromSrc B n_0
    st.WellBalanced ∧ st.Valid ∧ st.virtLen false = n_0 ∧ st.virtLen true = 0 ∧
      ∀ idx < n_0, st.toPhys false idx = idx := by
  dsimp only
  set st := initFromSrc B n_0
  set B' := max B 32
  have hB32 : 32 ≤ B' := le_max_right B 32
  have hB_pos : 0 < B' := by omega
  set base_r := B' + B' / 2
  set q_0 := if n_0 < B' + base_r then 0 else (n_0 - base_r) / B'
  set r_0 := n_0 - q_0 * B'
  have hq_mul : q_0 * B' ≤ n_0 := by
    dsimp only [q_0]
    split_ifs with hlt
    · simp
    · exact (Nat.div_mul_le_self (n_0 - base_r) B').trans (by omega)
  have hr_hi : r_0 < B' + base_r := by
    dsimp only [r_0, q_0]
    split_ifs with hlt
    · simp [hlt]
    · have hmod : (n_0 - base_r) % B' < B' := Nat.mod_lt _ hB_pos
      have hd := Nat.div_add_mod (n_0 - base_r) B'
      rw [Nat.mul_comm] at hd
      omega
  have hr_lo : 0 < q_0 → base_r ≤ r_0 := by
    intro hq_pos
    dsimp only [q_0] at hq_pos
    split_ifs at hq_pos with hlt
    · omega
    · dsimp only [r_0, q_0]
      simp only [hlt, ↓reduceIte]
      have hd : ((n_0 - base_r) / B') * B' ≤ n_0 - base_r := Nat.div_mul_le_self _ _
      omega
  have htotP : st.totalPages = q_0 := by simp [st, initFromSrc, totalPages, B', base_r, q_0]
  have hv0 : st.virtLen false = n_0 := by
    dsimp only [st, initFromSrc, virtLen]
    simp only [Bool.false_eq_true, ↓reduceIte]
    change q_0 * B' + r_0 = n_0
    omega
  have hv1 : st.virtLen true = 0 := by simp [st, initFromSrc, virtLen]
  have htotI : st.totalItems = n_0 := by simp [totalItems, hv0, hv1]
  have htailPhys_eq : ∀ t < 4 * B', st.tailPhys false t = q_0 * B' + t := by
    intro t ht
    have hrs : st.ringSlot false t = t := by
      dsimp only [st, initFromSrc, ringSlot]
      change (0 + t) % (4 * B') = t
      rw [zero_add, Nat.mod_eq_of_lt ht]
    unfold tailPhys
    rw [htotP, hrs]
    change physOfRes (q_0 * B') B' ((q_0 * B' + t) % (8 * B')) = q_0 * B' + t
    exact physOfRes_mod hB_pos (Nat.le_add_right _ _) (by omega)
  have hval : st.Valid := by
    have hps : st.pageSize = B' := rfl
    have htc_f : st.tailCount false = r_0 := rfl
    have htc_t : st.tailCount true = 0 := rfl
    refine ⟨hps ▸ hB_pos, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro side
      rw [hps]
      cases side
      · rw [htc_f]; omega
      · rw [htc_t]; omega
    · rw [hps, htc_f, htc_t]; omega
    · intro side; rw [hps]; dsimp only [st, initFromSrc]; positivity
    · intro side vp hvp; rw [htotP]
      cases side
      · simpa [st, initFromSrc, B', base_r, q_0] using hvp
      · simp [st, initFromSrc] at hvp
    · intro side vp hvp
      cases side
      · exact ⟨rfl, rfl⟩
      · simp [st, initFromSrc] at hvp
    · intro P hP; rw [htotP] at hP
      exact ⟨by simpa [st, initFromSrc, B', base_r, q_0] using hP, rfl⟩
    · intro side t _; rw [hps]; dsimp only [st, initFromSrc]; exact Nat.mod_lt _ (by positivity)
    · intro side t ht; rw [htotI]
      cases side
      · rw [htc_f] at ht
        rw [htailPhys_eq t (by omega)]; omega
      · simp [st, initFromSrc] at ht
    · intro side t ht
      cases side
      · rw [htc_f] at ht
        have hrs : st.ringSlot false t = t := by
          dsimp only [st, initFromSrc, ringSlot]
          change (0 + t) % (4 * B') = t
          rw [zero_add, Nat.mod_eq_of_lt (by omega)]
        rw [hrs]
        refine ⟨rfl, ?_⟩
        change (((q_0 * B' + t) % (8 * B') + 8 * B' - (q_0 * B') % (8 * B')) % (8 * B')) = t
        have := offsetOfMod (M := 8 * B') (base := q_0 * B') (p := q_0 * B' + t)
          (by positivity) (Nat.le_add_right _ _) (by omega)
        omega
      · simp [st, initFromSrc] at ht
    · intro p hlo hhi
      rw [htotP, hps] at hlo; rw [htotI] at hhi
      set t := p - q_0 * B'
      have ht_r0 : t < r_0 := by omega
      have hk_eq : st.tailOwnerRing (p % (8 * st.pageSize)) = t := by
        change (p % (8 * B') + 8 * B' - (q_0 * B') % (8 * B')) % (8 * B') = p - q_0 * B'
        exact offsetOfMod (by positivity) hlo (by omega)
      dsimp only
      rw [hk_eq]
      have hri : ringIdxOfSlot (st.tailHead (st.tailOwnerSide (p % (8 * st.pageSize))))
          st.pageSize t = t := by
        change (t + 4 * B' - 0 % (4 * B')) % (4 * B') = t
        rw [Nat.zero_mod, Nat.sub_zero, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      rw [hri]
      have hs_eq : st.tailOwnerSide (p % (8 * st.pageSize)) = false := rfl
      rw [hs_eq, hps, htc_f]
      refine ⟨by omega, ht_r0, ?_⟩
      rw [htailPhys_eq t (by omega)]
      omega
  have hwb : st.WellBalanced := by
    refine ⟨hval, hB32, trivial, ?_, trivial⟩
    have hj : st.job = .idle := rfl
    simp only [hj, ↓reduceIte]
    unfold phi dev
    dsimp only [st, initFromSrc]
    simp only [Bool.false_eq_true, ↓reduceIte, lt_irrefl, Nat.zero_sub, max_self, add_zero]
    change 16 * max (r_0 - 2 * B') (if 0 < q_0 then 2 * B' - r_0 else 0) ≤ 24 * B' - 8
    by_cases hq0 : 0 < q_0
    · have hrl := hr_lo hq0
      simp only [hq0, ↓reduceIte]
      omega
    · simp only [hq0, ↓reduceIte]
      omega
  refine ⟨hwb, hval, hv0, hv1, fun idx hidx => ?_⟩
  unfold toPhys effPage
  have hj : st.job = .idle := rfl
  rw [hj]
  dsimp only [st, initFromSrc]
  simp only [Bool.false_eq_true, ↓reduceIte]
  change (if idx < q_0 * B' then idx / B' * B' + idx % B'
    else st.tailPhys false (idx - q_0 * B')) = idx
  split_ifs with hlt
  · rw [Nat.mul_comm (idx / B') B', Nat.div_add_mod]
  · rw [htailPhys_eq (idx - q_0 * B') (by omega)]
    omega

/-- Swap two physical tail slots `p₁, p₂ ∈ [totalPages * pageSize, totalItems)` in `O(1)`. -/
@[expose] def swapTailSlots (st : PagePairState) (p₁ p₂ : ℕ) : PagePairState × List PhysSwap :=
  if p₁ = p₂ then
    (st, [])
  else
    let M := 8 * st.pageSize
    let r₁ := p₁ % M
    let r₂ := p₂ % M
    let s₁ := st.tailOwnerSide r₁
    let k₁ := st.tailOwnerRing r₁
    let s₂ := st.tailOwnerSide r₂
    let k₂ := st.tailOwnerRing r₂
    ({ st with
        tailRes := set2 (set2 st.tailRes s₁ k₁ r₂) s₂ k₂ r₁
        tailOwnerSide := Function.update (Function.update st.tailOwnerSide r₁ s₂) r₂ s₁
        tailOwnerRing := Function.update (Function.update st.tailOwnerRing r₁ k₂) r₂ k₁ },
      [⟨p₁, p₂⟩])

theorem swapTailSlots_spec {st : PagePairState} (hv : st.Valid) {p₁ p₂ : ℕ}
    (hp₁_lo : st.totalPages * st.pageSize ≤ p₁) (hp₁_hi : p₁ < st.totalItems)
    (hp₂_lo : st.totalPages * st.pageSize ≤ p₂) (hp₂_hi : p₂ < st.totalItems) :
    let res := st.swapTailSlots p₁ p₂
    let st' := res.1
    let sws := res.2
    st'.Valid ∧
    st'.pageSize = st.pageSize ∧
    st'.fullPages = st.fullPages ∧
    st'.tailCount = st.tailCount ∧
    st'.tailHead = st.tailHead ∧
    st'.pageOf = st.pageOf ∧
    st'.ownerSide = st.ownerSide ∧
    st'.ownerVp = st.ownerVp ∧
    st'.job = st.job ∧
    sws.length ≤ 1 ∧
    (∀ sw ∈ sws, sw.p₁ < st.totalItems ∧ sw.p₂ < st.totalItems) ∧
    (∀ s t, t < st.tailCount s →
      st'.tailPhys s t =
        if st.tailPhys s t = p₁ then p₂
        else if st.tailPhys s t = p₂ then p₁
        else st.tailPhys s t) ∧
    (∀ {α : Type*} (arr : ℕ → α) (s : Bool) (idx : ℕ), idx < st.virtLen s →
      st'.virtAt (applySwaps sws arr) s idx = st.virtAt arr s idx) := by
  dsimp only
  unfold swapTailSlots
  by_cases hp_eq : p₁ = p₂
  · rw [ite_eq_left hp_eq]
    dsimp only
    refine ⟨hv, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide, by simp, fun s t _ => ?_,
      fun _ _ _ _ => rfl⟩
    subst hp_eq
    split_ifs with h <;> omega
  · rw [ite_eq_right hp_eq]
    dsimp only
    set B := st.pageSize
    set M := 8 * B
    have hB : 0 < B := hv.pageSize_pos
    have hM : 0 < M := by positivity
    have hts : st.tailCount false + st.tailCount true < M := hv.tailSum_lt
    have htot_hi : st.totalItems < st.totalPages * B + M := by
      rw [st.totalItems_eq]; change st.totalPages * B + _ + _ < _; omega
    change st.totalPages * B ≤ p₁ at hp₁_lo
    change st.totalPages * B ≤ p₂ at hp₂_lo
    set r₁ := p₁ % M
    set r₂ := p₂ % M
    have hr_ne : r₁ ≠ r₂ := fun h =>
      hp_eq (mod_inj_of_range hM hp₁_lo (hp₁_hi.trans htot_hi) hp₂_lo (hp₂_hi.trans htot_hi) h)
    have hr₁_lt : r₁ < M := Nat.mod_lt p₁ hM
    have hr₂_lt : r₂ < M := Nat.mod_lt p₂ hM
    obtain ⟨hk₁_lt, ht₁_lt, htp₁⟩ := hv.tail_owner p₁ hp₁_lo hp₁_hi
    obtain ⟨hk₂_lt, ht₂_lt, htp₂⟩ := hv.tail_owner p₂ hp₂_lo hp₂_hi
    set s₁ := st.tailOwnerSide r₁
    set k₁ := st.tailOwnerRing r₁
    set t₁ := ringIdxOfSlot (st.tailHead s₁) B k₁
    set s₂ := st.tailOwnerSide r₂
    set k₂ := st.tailOwnerRing r₂
    set t₂ := ringIdxOfSlot (st.tailHead s₂) B k₂
    have hrs₁ : st.ringSlot s₁ t₁ = k₁ := mod_add_ringIdxOfSlot hk₁_lt
    have hrs₂ : st.ringSlot s₂ t₂ = k₂ := mod_add_ringIdxOfSlot hk₂_lt
    have hsk_ne : ¬(s₁ = s₂ ∧ k₁ = k₂) := by
      rintro ⟨hs_eq, hkeq⟩
      have hteq : t₁ = t₂ := by dsimp only [t₁, t₂]; rw [hs_eq, hkeq]
      have htp_eq : st.tailPhys s₁ t₁ = st.tailPhys s₂ t₂ := by rw [hs_eq, hteq]
      rw [htp₁, htp₂] at htp_eq
      exact hp_eq htp_eq
    set st' : PagePairState :=
      { st with
        tailRes := set2 (set2 st.tailRes s₁ k₁ r₂) s₂ k₂ r₁
        tailOwnerSide := Function.update (Function.update st.tailOwnerSide r₁ s₂) r₂ s₁
        tailOwnerRing := Function.update (Function.update st.tailOwnerRing r₁ k₂) r₂ k₁ }
    have htotP' : st'.totalPages = st.totalPages := rfl
    have htotI' : st'.totalItems = st.totalItems := rfl
    have htp_formula : ∀ s t, t < st.tailCount s →
        st'.tailPhys s t =
          if st.tailPhys s t = p₁ then p₂
          else if st.tailPhys s t = p₂ then p₁
          else st.tailPhys s t := by
      intro s t ht
      have hrs_eq : st'.ringSlot s t = st.ringSlot s t := rfl
      by_cases hc₁ : s = s₁ ∧ st.ringSlot s t = k₁
      · obtain ⟨hs_eq, hrk⟩ := hc₁
        subst s
        have ht_eq : t = t₁ := by
          have h1 := ringIdxOfSlot_mod (head := st.tailHead s₁) hB (ht.trans (hv.tailCount_lt s₁))
          change ringIdxOfSlot (st.tailHead s₁) B (st.ringSlot s₁ t) = t at h1
          rw [hrk] at h1; exact h1.symm
        subst t
        rw [htp₁, ite_eq_left rfl]
        unfold tailPhys
        rw [htotP', hrs_eq, hrs₁]
        change physOfRes (st.totalPages * B) B
          (set2 (set2 st.tailRes s₁ k₁ r₂) s₂ k₂ r₁ s₁ k₁) = p₂
        rw [set2_of_ne _ s₂ s₁ k₂ k₁ r₁ hsk_ne, set2_self]
        exact physOfRes_mod hB hp₂_lo (hp₂_hi.trans htot_hi)
      · by_cases hc₂ : s = s₂ ∧ st.ringSlot s t = k₂
        · obtain ⟨hs_eq, hrk⟩ := hc₂
          subst s
          have ht_eq : t = t₂ := by
            have h1 := ringIdxOfSlot_mod (head := st.tailHead s₂) hB (ht.trans (hv.tailCount_lt s₂))
            change ringIdxOfSlot (st.tailHead s₂) B (st.ringSlot s₂ t) = t at h1
            rw [hrk] at h1; exact h1.symm
          subst t
          rw [htp₂, ite_eq_right (Ne.symm hp_eq), ite_eq_left rfl]
          unfold tailPhys
          rw [htotP', hrs_eq, hrs₂]
          change physOfRes (st.totalPages * B) B
            (set2 (set2 st.tailRes s₁ k₁ r₂) s₂ k₂ r₁ s₂ k₂) = p₁
          rw [set2_self]
          exact physOfRes_mod hB hp₁_lo (hp₁_hi.trans htot_hi)
        · have hne₁ : st.tailPhys s t ≠ p₁ := by
            intro hp
            have hm : st.tailPhys s t % M = r₁ := congrArg (· % M) hp
            have hmod_res := mod_physOfRes (base := st.totalPages * B) (hv.tailRes_lt s t ht)
            change st.tailPhys s t % M = st.tailRes s (st.ringSlot s t) at hmod_res
            have ho := hv.owner_tail s t ht
            dsimp only at ho
            rw [← hmod_res, hm] at ho
            exact hc₁ ⟨ho.1.symm, ho.2.symm⟩
          have hne₂ : st.tailPhys s t ≠ p₂ := by
            intro hp
            have hm : st.tailPhys s t % M = r₂ := congrArg (· % M) hp
            have hmod_res := mod_physOfRes (base := st.totalPages * B) (hv.tailRes_lt s t ht)
            change st.tailPhys s t % M = st.tailRes s (st.ringSlot s t) at hmod_res
            have ho := hv.owner_tail s t ht
            dsimp only at ho
            rw [← hmod_res, hm] at ho
            exact hc₂ ⟨ho.1.symm, ho.2.symm⟩
          rw [ite_eq_right hne₁, ite_eq_right hne₂]
          unfold tailPhys
          rw [htotP', hrs_eq]
          change physOfRes (st.totalPages * B) B
            (set2 (set2 st.tailRes s₁ k₁ r₂) s₂ k₂ r₁ s (st.ringSlot s t)) = _
          rw [set2_of_ne _ _ _ _ _ _ hc₂, set2_of_ne _ _ _ _ _ _ hc₁]
    have hvalid' : st'.Valid := by
      refine ⟨hB, hv.tailCount_lt, hv.tailSum_lt, hv.tailHead_lt, hv.page_lt, hv.owner_pageOf,
        hv.pageOf_owner, ?_, ?_, ?_, ?_⟩
      · intro s t ht
        change set2 (set2 st.tailRes s₁ k₁ r₂) s₂ k₂ r₁ s (st.ringSlot s t) < M
        by_cases h2 : s = s₂ ∧ st.ringSlot s t = k₂
        · rw [set2, ite_eq_left h2]; exact hr₁_lt
        · rw [set2_of_ne _ _ _ _ _ _ h2]
          by_cases h1 : s = s₁ ∧ st.ringSlot s t = k₁
          · rw [set2, ite_eq_left h1]; exact hr₂_lt
          · rw [set2_of_ne _ _ _ _ _ _ h1]; exact hv.tailRes_lt s t ht
      · intro s t ht
        rw [htotI', htp_formula s t ht]
        split_ifs
        · exact hp₂_hi
        · exact hp₁_hi
        · exact hv.tail_lt s t ht
      · intro s t ht
        have hrs_eq : st'.ringSlot s t = st.ringSlot s t := rfl
        rw [hrs_eq]
        by_cases hc₂ : s = s₂ ∧ st.ringSlot s t = k₂
        · obtain ⟨hs_eq, hrk⟩ := hc₂
          subst s
          change (let res := set2 (set2 st.tailRes s₁ k₁ r₂) s₂ k₂ r₁ s₂ (st.ringSlot s₂ t);
            Function.update (Function.update st.tailOwnerSide r₁ s₂) r₂ s₁ res = s₂ ∧
            Function.update (Function.update st.tailOwnerRing r₁ k₂) r₂ k₁ res = st.ringSlot s₂ t)
          rw [hrk, set2_self]
          dsimp only
          rw [Function.update_of_ne hr_ne, Function.update_self,
            Function.update_of_ne hr_ne, Function.update_self]
          exact ⟨rfl, rfl⟩
        · by_cases hc₁ : s = s₁ ∧ st.ringSlot s t = k₁
          · obtain ⟨hs_eq, hrk⟩ := hc₁
            subst s
            change (let res := set2 (set2 st.tailRes s₁ k₁ r₂) s₂ k₂ r₁ s₁ (st.ringSlot s₁ t);
              Function.update (Function.update st.tailOwnerSide r₁ s₂) r₂ s₁ res = s₁ ∧
              Function.update (Function.update st.tailOwnerRing r₁ k₂) r₂ k₁ res = st.ringSlot s₁ t)
            rw [hrk, set2_of_ne _ _ _ _ _ _ hsk_ne, set2_self]
            dsimp only
            rw [Function.update_self, Function.update_self]
            exact ⟨rfl, rfl⟩
          · have hres_eq : st'.tailRes s (st.ringSlot s t) = st.tailRes s (st.ringSlot s t) := by
              change set2 (set2 st.tailRes s₁ k₁ r₂) s₂ k₂ r₁ s (st.ringSlot s t) = _
              rw [set2_of_ne _ _ _ _ _ _ hc₂, set2_of_ne _ _ _ _ _ _ hc₁]
            have ho := hv.owner_tail s t ht
            dsimp only at ho ⊢
            rw [hres_eq]
            have hnr₁ : st.tailRes s (st.ringSlot s t) ≠ r₁ := by
              intro heq; rw [heq] at ho; exact hc₁ ⟨ho.1.symm, ho.2.symm⟩
            have hnr₂ : st.tailRes s (st.ringSlot s t) ≠ r₂ := by
              intro heq; rw [heq] at ho; exact hc₂ ⟨ho.1.symm, ho.2.symm⟩
            change Function.update (Function.update st.tailOwnerSide r₁ s₂) r₂ s₁ _ = s ∧
              Function.update (Function.update st.tailOwnerRing r₁ k₂) r₂ k₁ _ = _
            rw [Function.update_of_ne hnr₂, Function.update_of_ne hnr₁,
              Function.update_of_ne hnr₂, Function.update_of_ne hnr₁]
            exact ho
      · intro p hplo hphi
        rw [htotP'] at hplo; rw [htotI'] at hphi
        change st.totalPages * B ≤ p at hplo
        by_cases hp1 : p = p₁
        · subst p
          change (let res := r₁;
            let side := Function.update (Function.update st.tailOwnerSide r₁ s₂) r₂ s₁ res;
            let k := Function.update (Function.update st.tailOwnerRing r₁ k₂) r₂ k₁ res;
            let t := ringIdxOfSlot (st.tailHead side) B k;
            k < 4 * B ∧ t < st.tailCount side ∧ st'.tailPhys side t = p₁)
          dsimp only
          rw [Function.update_of_ne hr_ne, Function.update_self,
            Function.update_of_ne hr_ne, Function.update_self]
          refine ⟨hk₂_lt, ht₂_lt, ?_⟩
          rw [htp_formula s₂ t₂ ht₂_lt, htp₂, ite_eq_right (Ne.symm hp_eq), ite_eq_left rfl]
        · by_cases hp2 : p = p₂
          · subst p
            change (let res := r₂;
              let side := Function.update (Function.update st.tailOwnerSide r₁ s₂) r₂ s₁ res;
              let k := Function.update (Function.update st.tailOwnerRing r₁ k₂) r₂ k₁ res;
              let t := ringIdxOfSlot (st.tailHead side) B k;
              k < 4 * B ∧ t < st.tailCount side ∧ st'.tailPhys side t = p₂)
            dsimp only
            rw [Function.update_self, Function.update_self]
            refine ⟨hk₁_lt, ht₁_lt, ?_⟩
            rw [htp_formula s₁ t₁ ht₁_lt, htp₁, ite_eq_left rfl]
          · have hnr₁ : p % M ≠ r₁ := fun h =>
              hp1 (mod_inj_of_range hM hplo (hphi.trans htot_hi) hp₁_lo (hp₁_hi.trans htot_hi) h)
            have hnr₂ : p % M ≠ r₂ := fun h =>
              hp2 (mod_inj_of_range hM hplo (hphi.trans htot_hi) hp₂_lo (hp₂_hi.trans htot_hi) h)
            obtain ⟨hkp, htp, htpp⟩ := hv.tail_owner p hplo hphi
            change (let res := p % M;
              let side := Function.update (Function.update st.tailOwnerSide r₁ s₂) r₂ s₁ res;
              let k := Function.update (Function.update st.tailOwnerRing r₁ k₂) r₂ k₁ res;
              let t := ringIdxOfSlot (st.tailHead side) B k;
              k < 4 * B ∧ t < st.tailCount side ∧ st'.tailPhys side t = p)
            dsimp only
            rw [Function.update_of_ne hnr₂, Function.update_of_ne hnr₁,
              Function.update_of_ne hnr₂, Function.update_of_ne hnr₁]
            refine ⟨hkp, htp, ?_⟩
            rw [htp_formula _ _ htp, htpp, ite_eq_right hp1, ite_eq_right hp2]
    change st'.Valid ∧ _
    refine ⟨hvalid', rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, le_rfl, ?_, htp_formula, ?_⟩
    · intro sw hsw; simp only [List.mem_singleton] at hsw; subst hsw; exact ⟨hp₁_hi, hp₂_hi⟩
    · intro α arr s idx hidx
      unfold virtAt toPhys
      dsimp only
      have heff : ∀ P u, st'.effPage P u = st.effPage P u := fun _ _ => rfl
      have hps' : st'.pageSize = B := rfl
      have hfp' : st'.fullPages = st.fullPages := rfl
      have hpo' : st'.pageOf = st.pageOf := rfl
      rw [hps', hfp', hpo']
      split_ifs with hlt
      · rw [heff]
        have hvp : idx / B < st.fullPages s := (Nat.div_lt_iff_lt_mul hB).mpr hlt
        have hp_lt := hv.effPage_lt (hv.page_lt s (idx / B) hvp) (idx % B)
        have hmod := Nat.mod_lt idx hB
        set E := st.effPage (st.pageOf s (idx / B)) (idx % B)
        have hle : (E + 1) * B ≤ st.totalPages * B := Nat.mul_le_mul_right _ hp_lt
        rw [Nat.add_mul, Nat.one_mul] at hle
        have hlt_tot : E * B + idx % B < st.totalPages * B := by omega
        exact PhysSwap.apply_of_ne ⟨p₁, p₂⟩ arr
          (Nat.ne_of_lt (hlt_tot.trans_le hp₁_lo))
          (Nat.ne_of_lt (hlt_tot.trans_le hp₂_lo))
      · have ht : idx - st.fullPages s * B < st.tailCount s := by
          unfold virtLen at hidx; change _ < st.fullPages s * B + _ at hidx; omega
        rw [htp_formula s _ ht]
        split_ifs with h1 h2
        · rw [h1]; exact PhysSwap.apply_p₂ ⟨p₁, p₂⟩ arr
        · rw [h2]; exact PhysSwap.apply_p₁ ⟨p₁, p₂⟩ arr
        · exact PhysSwap.apply_of_ne ⟨p₁, p₂⟩ arr h1 h2

theorem swapTailSlots_preserves_staged {st : PagePairState} (hv : st.Valid)
    {p₁ p₂ : ℕ} (hp₁_lo : st.totalPages * st.pageSize ≤ p₁) (hp₁_hi : p₁ < st.totalItems)
    (hp₂_lo : st.totalPages * st.pageSize ≤ p₂) (hp₂_hi : p₂ < st.totalItems)
    {s : Bool} {k res : ℕ}
    (hk_ne : ∀ t < st.tailCount s, st.ringSlot s t ≠ k)
    (hres_ne : ∀ p, st.totalPages * st.pageSize ≤ p → p < st.totalItems →
      p % (8 * st.pageSize) ≠ res) :
    let st' := (st.swapTailSlots p₁ p₂).1
    st'.tailRes s k = st.tailRes s k ∧
    st'.tailOwnerSide res = st.tailOwnerSide res ∧
    st'.tailOwnerRing res = st.tailOwnerRing res := by
  dsimp only
  unfold swapTailSlots
  split_ifs with hp_eq
  · exact ⟨rfl, rfl, rfl⟩
  · obtain ⟨hk₁_lt, ht₁_lt, _⟩ := hv.tail_owner p₁ hp₁_lo hp₁_hi
    obtain ⟨hk₂_lt, ht₂_lt, _⟩ := hv.tail_owner p₂ hp₂_lo hp₂_hi
    have hrs₁ : st.ringSlot (st.tailOwnerSide (p₁ % (8 * st.pageSize)))
        (ringIdxOfSlot (st.tailHead (st.tailOwnerSide (p₁ % (8 * st.pageSize)))) st.pageSize
          (st.tailOwnerRing (p₁ % (8 * st.pageSize)))) =
        st.tailOwnerRing (p₁ % (8 * st.pageSize)) := mod_add_ringIdxOfSlot hk₁_lt
    have hrs₂ : st.ringSlot (st.tailOwnerSide (p₂ % (8 * st.pageSize)))
        (ringIdxOfSlot (st.tailHead (st.tailOwnerSide (p₂ % (8 * st.pageSize)))) st.pageSize
          (st.tailOwnerRing (p₂ % (8 * st.pageSize)))) =
        st.tailOwnerRing (p₂ % (8 * st.pageSize)) := mod_add_ringIdxOfSlot hk₂_lt
    have hc₁ : ¬(s = st.tailOwnerSide (p₁ % (8 * st.pageSize)) ∧
        k = st.tailOwnerRing (p₁ % (8 * st.pageSize))) := by
      rintro ⟨rfl, rfl⟩; exact hk_ne _ ht₁_lt hrs₁
    have hc₂ : ¬(s = st.tailOwnerSide (p₂ % (8 * st.pageSize)) ∧
        k = st.tailOwnerRing (p₂ % (8 * st.pageSize))) := by
      rintro ⟨rfl, rfl⟩; exact hk_ne _ ht₂_lt hrs₂
    have hnr₁ : res ≠ p₁ % (8 * st.pageSize) := (hres_ne p₁ hp₁_lo hp₁_hi).symm
    have hnr₂ : res ≠ p₂ % (8 * st.pageSize) := (hres_ne p₂ hp₂_lo hp₂_hi).symm
    refine ⟨?_, ?_, ?_⟩
    · change set2 (set2 st.tailRes _ _ _) _ _ _ s k = _
      rw [set2_of_ne _ _ _ _ _ _ hc₂, set2_of_ne _ _ _ _ _ _ hc₁]
    · change Function.update (Function.update st.tailOwnerSide _ _) _ _ res = _
      rw [Function.update_of_ne hnr₂, Function.update_of_ne hnr₁]
    · change Function.update (Function.update st.tailOwnerRing _ _) _ _ res = _
      rw [Function.update_of_ne hnr₂, Function.update_of_ne hnr₁]

/-- Launch a background promotion or demotion job if `st.job = .idle` and either side has crossed
its hysteresis threshold (`4 * r ≥ 11 * B` or `0 < q ∧ 4 * r ≤ 5 * B`). -/
@[expose] def maybeStartJob (st : PagePairState) : PagePairState :=
  match st.job with
  | .idle =>
    let B := st.pageSize
    let startSide (s : Bool) : Option PageJob :=
      if 11 * B ≤ 4 * st.tailCount s then
        some (.promote s 0)
      else if 0 < st.fullPages s ∧ 4 * st.tailCount s ≤ 5 * B then
        if st.pageOf s (st.fullPages s - 1) = st.totalPages - 1 then
          some (.demoteBuild s 0)
        else
          some (.demoteSwap s 0)
      else
        none
    match startSide false with
    | some j => { st with job := j }
    | none =>
      match startSide true with
      | some j => { st with job := j }
      | none => st
  | _ => st

theorem maybeStartJob_toPhys (st : PagePairState) (side : Bool) (idx : ℕ) :
    (maybeStartJob st).toPhys side idx = st.toPhys side idx := by
  unfold maybeStartJob
  cases hj : st.job <;> try rfl
  dsimp only
  have heff : ∀ j : PageJob,
      (j = .idle ∨ (∃ s, j = .promote s 0) ∨ (∃ s, j = .demoteSwap s 0) ∨
        (∃ s, j = .demoteBuild s 0)) →
      ({ st with job := j } : PagePairState).toPhys side idx = st.toPhys side idx := by
    intro j hcases
    unfold toPhys tailPhys ringSlot effPage totalPages
    rw [hj]
    rcases hcases with rfl | ⟨s, rfl⟩ | ⟨s, rfl⟩ | ⟨s, rfl⟩ <;> simp
  generalize hs0 : (if 11 * st.pageSize ≤ 4 * st.tailCount false then some (PageJob.promote false 0)
    else if 0 < st.fullPages false ∧ 4 * st.tailCount false ≤ 5 * st.pageSize then
      if st.pageOf false (st.fullPages false - 1) = st.totalPages - 1 then
        some (PageJob.demoteBuild false 0)
      else some (PageJob.demoteSwap false 0)
    else none) = o0
  cases o0 with
  | some j =>
    refine heff j ?_
    split_ifs at hs0 with h1 h2 h3 <;> simp only [Option.some.injEq] at hs0 <;> subst hs0
    · exact Or.inr (Or.inl ⟨false, rfl⟩)
    · exact Or.inr (Or.inr (Or.inr ⟨false, rfl⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨false, rfl⟩))
  | none =>
    generalize hs1 : (if 11 * st.pageSize ≤ 4 * st.tailCount true then some (PageJob.promote true 0)
      else if 0 < st.fullPages true ∧ 4 * st.tailCount true ≤ 5 * st.pageSize then
        if st.pageOf true (st.fullPages true - 1) = st.totalPages - 1 then
          some (PageJob.demoteBuild true 0)
        else some (PageJob.demoteSwap true 0)
      else none) = o1
    cases o1 with
    | some j =>
      refine heff j ?_
      split_ifs at hs1 with h1 h2 h3 <;> simp only [Option.some.injEq] at hs1 <;> subst hs1
      · exact Or.inr (Or.inl ⟨true, rfl⟩)
      · exact Or.inr (Or.inr (Or.inr ⟨true, rfl⟩))
      · exact Or.inr (Or.inr (Or.inl ⟨true, rfl⟩))
    | none => rfl

/-- Single `O(1)` tick of the `PagePairState` background promotion/demotion state machine. -/
@[expose] def tickOne (st : PagePairState) : PagePairState × List PhysSwap :=
  let B := st.pageSize
  let Q := st.totalPages
  match st.job with
  | .idle => (st, [])
  | .promote s cur =>
    if cur < B then
      let (st₁, sws) := st.swapTailSlots (st.tailPhys s cur) (Q * B + cur)
      ({ st₁ with job := .promote s (cur + 1) }, sws)
    else
      let q_s := st.fullPages s
      ({ st with
          fullPages := Function.update st.fullPages s (q_s + 1)
          tailCount := Function.update st.tailCount s (st.tailCount s - B)
          tailHead := Function.update st.tailHead s ((st.tailHead s + B) % (4 * B))
          pageOf := set2 st.pageOf s q_s Q
          ownerSide := Function.update st.ownerSide Q s
          ownerVp := Function.update st.ownerVp Q q_s
          job := .idle }, [])
  | .demoteSwap s cur =>
    let P_dem := st.pageOf s (st.fullPages s - 1)
    let P_last := Q - 1
    if cur < B then
      ({ st with job := .demoteSwap s (cur + 1) }, [⟨P_dem * B + cur, P_last * B + cur⟩])
    else
      let s_last := st.ownerSide P_last
      let vp_last := st.ownerVp P_last
      ({ st with
          pageOf := set2 (set2 st.pageOf s_last vp_last P_dem) s (st.fullPages s - 1) P_last
          ownerSide := Function.update (Function.update st.ownerSide P_dem s_last) P_last s
          ownerVp := Function.update (Function.update st.ownerVp P_dem vp_last) P_last
            (st.fullPages s - 1)
          job := .demoteBuild s 0 }, [])
  | .demoteBuild s cur =>
    if cur < B then
      let k_cur := (st.tailHead s + 3 * B + cur) % (4 * B)
      let res_cur := ((Q - 1) * B + cur) % (8 * B)
      ({ st with
          tailRes := set2 st.tailRes s k_cur res_cur
          tailOwnerSide := Function.update st.tailOwnerSide res_cur s
          tailOwnerRing := Function.update st.tailOwnerRing res_cur k_cur
          job := .demoteBuild s (cur + 1) }, [])
    else
      ({ st with
          fullPages := Function.update st.fullPages s (st.fullPages s - 1)
          tailCount := Function.update st.tailCount s (st.tailCount s + B)
          tailHead := Function.update st.tailHead s ((st.tailHead s + 3 * B) % (4 * B))
          job := .idle }, [])

/-- Advance `tickOne` and immediately launch the next pending job if `tickOne` reached `.idle`. -/
@[expose] def tick (st : PagePairState) : PagePairState × List PhysSwap :=
  let (st₁, sws) := st.tickOne
  (st₁.maybeStartJob, sws)

/-- Iterate `tick` `k` times, accumulating physical swaps left-to-right. -/
@[expose] def runTicks : ℕ → PagePairState → PagePairState × List PhysSwap
  | 0, st => (st, [])
  | k + 1, st =>
    let (st₁, sws₁) := st.tick
    let (st₂, sws₂) := runTicks k st₁
    (st₂, sws₁ ++ sws₂)

/-- Raw `O(1)` tail append allocating physical slot `st.totalItems` to `(side, st.virtLen side)`. -/
@[expose] def rawAppend (st : PagePairState) (side : Bool) : PagePairState :=
  let B := st.pageSize
  let r_s := st.tailCount side
  let k_new := st.ringSlot side r_s
  let res_new := st.totalItems % (8 * B)
  { st with
    tailCount := Function.update st.tailCount side (r_s + 1)
    tailRes := set2 st.tailRes side k_new res_new
    tailOwnerSide := Function.update st.tailOwnerSide res_new side
    tailOwnerRing := Function.update st.tailOwnerRing res_new k_new }

/-- Deamortized `O(1)` virtual append: allocates physical slot `st.totalItems` at
`(side, st.virtLen side)` and runs `16` background rebalance ticks (`≤ 16` swaps). -/
@[expose] def stepAppend (st : PagePairState) (side : Bool) : PagePairState × List PhysSwap :=
  runTicks 16 ((st.rawAppend side).maybeStartJob)

/-- Raw `O(1)` tail pop removing `(side, st.virtLen side - 1)` and freeing physical slot
`st.totalItems - 1` via at most `1` physical swap. -/
@[expose] def rawPopBack (st : PagePairState) (side : Bool) : PagePairState × List PhysSwap :=
  let r_s := st.tailCount side
  let res := st.swapTailSlots (st.tailPhys side (r_s - 1)) (st.totalItems - 1)
  ({ res.1 with tailCount := Function.update res.1.tailCount side (r_s - 1) }, res.2)

/-- Parameterized `k`-tick virtual popBack helper (kept abstract in `k` during elaboration so `whnf`
never unfolds `runTicks 16`). -/
@[expose] def stepPopBackTicks (k : ℕ) (st : PagePairState) (side : Bool) :
    PagePairState × List PhysSwap :=
  let res₀ := st.rawPopBack side
  let res₁ := runTicks k res₀.1.maybeStartJob
  (res₁.1, res₀.2 ++ res₁.2)

/-- Deamortized `O(1)` virtual popBack: removes `(side, st.virtLen side - 1)`, frees physical slot
`st.totalItems - 1`, and runs `16` background rebalance ticks (`≤ 17` swaps total). -/
@[expose] def stepPopBack (st : PagePairState) (side : Bool) : PagePairState × List PhysSwap :=
  st.stepPopBackTicks 16 side

/-! ### Preservation Theorems for `tick`, `runTicks`, `stepAppend`, and `stepPopBack` -/

/-- Parametrized intermediate rebalance invariant with `slack ≤ 16` remaining ticks before
restoring `WellBalanced`. -/
structure DriftInv (st : PagePairState) (slack : ℕ) : Prop where
  valid : st.Valid
  pageSize_ge : 32 ≤ st.pageSize
  jobValid : st.JobValid
  slack_le : slack ≤ 16
  pot_bound : if st.job = .idle then
      16 * st.phi ≤ 24 * st.pageSize - 8
    else
      16 * st.phi + st.remTicks ≤ 28 * st.pageSize + slack
  side_bound : st.ActiveSideBound (6 * st.pageSize + 2 + slack)

theorem WellBalanced.toDriftInv {st : PagePairState} (hw : st.WellBalanced) :
    DriftInv st 0 :=
  ⟨hw.valid, hw.pageSize_ge, hw.jobValid, Nat.zero_le 16,
    by simpa only [add_zero] using hw.pot_bound,
    by simpa only [add_zero] using hw.side_bound⟩

theorem DriftInv.toWellBalanced {st : PagePairState} (hd : DriftInv st 0) :
    st.WellBalanced :=
  ⟨hd.valid, hd.pageSize_ge, hd.jobValid,
    by simpa only [add_zero] using hd.pot_bound,
    by simpa only [add_zero] using hd.side_bound⟩

private theorem Valid.with_job {st : PagePairState} (hv : st.Valid) (j : PageJob) :
    ({ st with job := j } : PagePairState).Valid :=
  ⟨hv.1, hv.2, hv.3, hv.4, hv.5, hv.6, hv.7, hv.8, hv.9, hv.10, hv.11⟩

private theorem ActiveSideBound.mono {st : PagePairState} {K₁ K₂ : ℕ}
    (ha : st.ActiveSideBound K₁) (hle : K₁ ≤ K₂) : st.ActiveSideBound K₂ := by
  unfold ActiveSideBound at ha ⊢
  cases hj : st.job <;> simp only [hj] at ha ⊢ <;> omega

private theorem DriftInv.mono {st : PagePairState} {s₁ s₂ : ℕ}
    (hd : DriftInv st s₁) (hle : s₁ ≤ s₂) (hs₂ : s₂ ≤ 16) : DriftInv st s₂ where
  valid := hd.valid
  pageSize_ge := hd.pageSize_ge
  jobValid := hd.jobValid
  slack_le := hs₂
  pot_bound := by
    have hp := hd.pot_bound
    split_ifs at hp ⊢ <;> omega
  side_bound := hd.side_bound.mono (by omega)

private theorem DriftInv.phi_le {st : PagePairState} {slack : ℕ} (hd : DriftInv st slack) :
    16 * st.phi ≤ 28 * st.pageSize + 16 := by
  have hp := hd.pot_bound
  have hs := hd.slack_le
  have hB := hd.pageSize_ge
  split_ifs at hp <;> omega

private theorem maybeStartJob_driftInv {st : PagePairState}
    (hv : st.Valid) (hB : 32 ≤ st.pageSize) (hj : st.job = .idle)
    (hphi : 16 * st.phi ≤ 24 * st.pageSize + 49) :
    DriftInv st.maybeStartJob 0 := by
  have launch_prom : ∀ s, 11 * st.pageSize ≤ 4 * st.tailCount s →
      DriftInv { st with job := .promote s 0 } 0 := fun s h11 => by
    refine ⟨hv.with_job _, hB, ?_, Nat.zero_le 16, ?_, ?_⟩
    · simp only [JobValid]
      exact ⟨Nat.zero_le _, by omega, fun _ hu => absurd hu (Nat.not_lt_zero _)⟩
    · rw [ite_eq_right (by rintro ⟨⟩)]
      change 16 * st.phi + (st.pageSize + 1 - 0) ≤ 28 * st.pageSize + 0
      omega
    · simp only [ActiveSideBound, remTicks]
      omega
  have launch_demBuild : ∀ s, 0 < st.fullPages s ∧ 4 * st.tailCount s ≤ 5 * st.pageSize →
      st.pageOf s (st.fullPages s - 1) = st.totalPages - 1 →
      DriftInv { st with job := .demoteBuild s 0 } 0 := fun s ⟨hq, hr5⟩ hp_eq => by
    refine ⟨hv.with_job _, hB, ?_, Nat.zero_le 16, ?_, ?_⟩
    · simp only [JobValid]
      refine ⟨Nat.zero_le _, hq, hp_eq, by omega, ?_,
        fun _ hu => absurd hu (Nat.not_lt_zero _)⟩
      unfold phi dev at hphi
      cases s <;> omega
    · rw [ite_eq_right (by rintro ⟨⟩)]
      change 16 * st.phi + (st.pageSize + 1 - 0) ≤ 28 * st.pageSize + 0
      omega
    · simp only [ActiveSideBound, remTicks]
      omega
  have launch_demSwap : ∀ s, 0 < st.fullPages s ∧ 4 * st.tailCount s ≤ 5 * st.pageSize →
      st.pageOf s (st.fullPages s - 1) ≠ st.totalPages - 1 →
      DriftInv { st with job := .demoteSwap s 0 } 0 := fun s ⟨hq, hr5⟩ hp_ne => by
    have hp_lt := hv.page_lt s (st.fullPages s - 1) (by omega)
    refine ⟨hv.with_job _, hB, ?_, Nat.zero_le 16, ?_, ?_⟩
    · simp only [JobValid]
      exact ⟨Nat.zero_le _, hq, by change _ < st.totalPages - 1; omega⟩
    · rw [ite_eq_right (by rintro ⟨⟩)]
      change 16 * st.phi + (2 * st.pageSize + 2 - 0) ≤ 28 * st.pageSize + 0
      omega
    · simp only [ActiveSideBound, remTicks]
      omega
  unfold maybeStartJob
  rw [hj]
  dsimp only
  by_cases h1f : 11 * st.pageSize ≤ 4 * st.tailCount false
  · rw [ite_eq_left h1f]; exact launch_prom false h1f
  · rw [ite_eq_right h1f]
    by_cases h2f : 0 < st.fullPages false ∧ 4 * st.tailCount false ≤ 5 * st.pageSize
    · rw [ite_eq_left h2f]
      by_cases h3f : st.pageOf false (st.fullPages false - 1) = st.totalPages - 1
      · rw [ite_eq_left h3f]; exact launch_demBuild false h2f h3f
      · rw [ite_eq_right h3f]; exact launch_demSwap false h2f h3f
    · rw [ite_eq_right h2f]
      dsimp only
      by_cases h1t : 11 * st.pageSize ≤ 4 * st.tailCount true
      · rw [ite_eq_left h1t]; exact launch_prom true h1t
      · rw [ite_eq_right h1t]
        by_cases h2t : 0 < st.fullPages true ∧ 4 * st.tailCount true ≤ 5 * st.pageSize
        · rw [ite_eq_left h2t]
          by_cases h3t : st.pageOf true (st.fullPages true - 1) = st.totalPages - 1
          · rw [ite_eq_left h3t]; exact launch_demBuild true h2t h3t
          · rw [ite_eq_right h3t]; exact launch_demSwap true h2t h3t
        · rw [ite_eq_right h2t]
          dsimp only
          refine ⟨hv, hB, by simp [JobValid, hj], Nat.zero_le 16, ?_,
            by simp [ActiveSideBound, hj]⟩
          simp only [hj, ↓reduceIte]
          have hdev_f : 4 * dev st.pageSize (st.fullPages false) (st.tailCount false) ≤
              3 * st.pageSize - 1 := by
            unfold dev
            by_cases hqf : 0 < st.fullPages false
            · have : ¬(4 * st.tailCount false ≤ 5 * st.pageSize) := fun h => h2f ⟨hqf, h⟩
              simp only [hqf, ↓reduceIte]; omega
            · simp only [hqf, ↓reduceIte]; omega
          have hdev_t : 4 * dev st.pageSize (st.fullPages true) (st.tailCount true) ≤
              3 * st.pageSize - 1 := by
            unfold dev
            by_cases hqt : 0 < st.fullPages true
            · have : ¬(4 * st.tailCount true ≤ 5 * st.pageSize) := fun h => h2t ⟨hqt, h⟩
              simp only [hqt, ↓reduceIte]; omega
            · simp only [hqt, ↓reduceIte]; omega
          unfold phi
          omega

private theorem maybeStartJob_meta (st : PagePairState) :
    (maybeStartJob st).pageSize = st.pageSize ∧
    (maybeStartJob st).fullPages = st.fullPages ∧
    (maybeStartJob st).tailCount = st.tailCount ∧
    (maybeStartJob st).virtLen = st.virtLen ∧
    (maybeStartJob st).totalItems = st.totalItems := by
  unfold maybeStartJob
  cases st.job <;> try exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  dsimp only
  split_ifs <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

private theorem mod_ring_shift_add {B head d u : ℕ} (hB : 0 < B) :
    ((head + d) % (4 * B) + u) % (4 * B) = (head + (d + u)) % (4 * B) := by
  have hM : 0 < 4 * B := by positivity
  calc ((head + d) % (4 * B) + u) % (4 * B)
      = ((head + d) % (4 * B) % (4 * B) + u % (4 * B)) % (4 * B) := Nat.add_mod _ _ _
    _ = ((head + d) % (4 * B) + u % (4 * B)) % (4 * B) := by rw [Nat.mod_mod]
    _ = (head + d + u) % (4 * B) := (Nat.add_mod _ _ _).symm
    _ = (head + (d + u)) % (4 * B) := by rw [Nat.add_assoc]

private theorem tickOne_promote_commit {st : PagePairState} {slack : ℕ} {s : Bool} {cur : ℕ}
    (hd : DriftInv st slack) (hj : st.job = .promote s cur) (hcur : ¬(cur < st.pageSize)) :
    let st₁ : PagePairState :=
      { st with
        fullPages := Function.update st.fullPages s (st.fullPages s + 1)
        tailCount := Function.update st.tailCount s (st.tailCount s - st.pageSize)
        tailHead := Function.update st.tailHead s
          ((st.tailHead s + st.pageSize) % (4 * st.pageSize))
        pageOf := set2 st.pageOf s (st.fullPages s) st.totalPages
        ownerSide := Function.update st.ownerSide st.totalPages s
        ownerVp := Function.update st.ownerVp st.totalPages (st.fullPages s)
        job := .idle }
    st₁.Valid ∧
    16 * st₁.phi ≤ 24 * st.pageSize + 49 ∧
    st₁.virtLen = st.virtLen ∧
    st₁.totalItems = st.totalItems ∧
    ∀ side idx, idx < st.virtLen side → st₁.toPhys side idx = st.toPhys side idx := by
  intro st₁
  have hv := hd.valid
  have hB32 : 32 ≤ st.pageSize := hd.pageSize_ge
  have hB : 0 < st.pageSize := hv.pageSize_pos
  have hjv := hd.jobValid; unfold JobValid at hjv; rw [hj] at hjv
  obtain ⟨hcur_le, hB_lt_r, hstaged⟩ := hjv
  have hcur_eq : cur = st.pageSize := by omega
  subst cur
  have htotP₁ : st₁.totalPages = st.totalPages + 1 := by
    dsimp only [st₁, totalPages]; cases s <;> simp <;> omega
  have hvirt₁ : st₁.virtLen = st.virtLen := by
    ext side
    dsimp only [st₁, virtLen]
    by_cases hs : side = s
    · subst hs; simp only [Function.update_self]; rw [Nat.add_mul, one_mul]; omega
    · simp [hs]
  have htotI₁ : st₁.totalItems = st.totalItems := by
    unfold totalItems; rw [hvirt₁]
  have hring_shift : ∀ t', st₁.ringSlot s t' = st.ringSlot s (st.pageSize + t') := fun t' => by
    dsimp only [st₁, ringSlot]
    rw [Function.update_self]
    exact mod_ring_shift_add hB
  -- Unpromoted tail slots (`side ≠ s` or `t ≥ st.pageSize` on `s`) have `tailPhys ≥ (Q + 1) * B`:
  have htail_ge_Q1 : ∀ side t, t < st.tailCount side → (side = s → st.pageSize ≤ t) →
      (st.totalPages + 1) * st.pageSize ≤ st.tailPhys side t := by
    intro side t ht hgeB
    have hlo : st.totalPages * st.pageSize ≤ st.tailPhys side t := le_physOfRes _ _ _
    by_contra hlt_Q1
    set u := st.tailPhys side t - st.totalPages * st.pageSize with hu_def
    have hu_lt : u < st.pageSize := by rw [Nat.add_mul, one_mul] at hlt_Q1; omega
    have hu_eq : st.tailPhys s u = st.tailPhys side t := by rw [hstaged u hu_lt]; omega
    have hidx1 : st.fullPages s * st.pageSize + u < st.virtLen s := by unfold virtLen; omega
    have hidx2 : st.fullPages side * st.pageSize + t < st.virtLen side := by unfold virtLen; omega
    have htp1 : st.toPhys s (st.fullPages s * st.pageSize + u) = st.tailPhys s u := by
      unfold toPhys; dsimp only; rw [ite_eq_right (by omega), Nat.add_sub_cancel_left]
    have htp2 : st.toPhys side (st.fullPages side * st.pageSize + t) = st.tailPhys side t := by
      unfold toPhys; dsimp only; rw [ite_eq_right (by omega), Nat.add_sub_cancel_left]
    obtain ⟨hse, hie⟩ := hv.toPhys_inj hidx1 hidx2 (by rw [htp1, htp2, hu_eq])
    subst hse
    have := hgeB rfl
    omega
  have htot_hi : st.totalItems < (st.totalPages + 1) * st.pageSize + 8 * st.pageSize := by
    rw [st.totalItems_eq]
    have hts := hv.tailSum_lt
    rw [Nat.add_mul, one_mul]; omega
  have htp₁_eq : ∀ side t', t' < st₁.tailCount side →
      st₁.tailPhys side t' =
        st.tailPhys side (if side = s then st.pageSize + t' else t') := by
    intro side t' ht'
    by_cases hs : side = s
    · subst hs
      dsimp only [st₁] at ht'
      rw [Function.update_self] at ht'
      simp only [↓reduceIte]
      have ht_lt : st.pageSize + t' < st.tailCount side := by omega
      have hp_ge := htail_ge_Q1 side (st.pageSize + t') ht_lt (fun _ => Nat.le_add_right _ t')
      have hp_hi := (hv.tail_lt side (st.pageSize + t') ht_lt).trans htot_hi
      have hmod := mod_physOfRes (base := st.totalPages * st.pageSize)
        (hv.tailRes_lt side (st.pageSize + t') ht_lt)
      change st.tailPhys side (st.pageSize + t') % (8 * st.pageSize) = _ at hmod
      change physOfRes (st₁.totalPages * st₁.pageSize) st₁.pageSize
        (st₁.tailRes side (st₁.ringSlot side t')) = _
      rw [htotP₁, show st₁.pageSize = st.pageSize from rfl, hring_shift t',
        show st₁.tailRes = st.tailRes from rfl, ← hmod]
      exact physOfRes_mod hB hp_ge hp_hi
    · dsimp only [st₁] at ht'
      rw [Function.update_of_ne hs] at ht'
      simp only [hs, ↓reduceIte]
      have hp_ge := htail_ge_Q1 side t' ht' (fun h => absurd h hs)
      have hp_hi := (hv.tail_lt side t' ht').trans htot_hi
      have hmod := mod_physOfRes (base := st.totalPages * st.pageSize)
        (hv.tailRes_lt side t' ht')
      change st.tailPhys side t' % (8 * st.pageSize) = _ at hmod
      have hrs_eq : st₁.ringSlot side t' = st.ringSlot side t' := by
        dsimp only [st₁, ringSlot]; rw [Function.update_of_ne hs]
      change physOfRes (st₁.totalPages * st₁.pageSize) st₁.pageSize
        (st₁.tailRes side (st₁.ringSlot side t')) = _
      rw [htotP₁, show st₁.pageSize = st.pageSize from rfl, hrs_eq,
        show st₁.tailRes = st.tailRes from rfl, ← hmod]
      exact physOfRes_mod hB hp_ge hp_hi
  have hv₁ : st₁.Valid := by
    refine ⟨hB, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro side; dsimp only [st₁]
      by_cases hs : side = s
      · subst hs; rw [Function.update_self]; have := hv.tailCount_lt side; omega
      · rw [Function.update_of_ne hs]; exact hv.tailCount_lt side
    · dsimp only [st₁]; have := hv.tailSum_lt; cases s <;> simp <;> omega
    · intro side; dsimp only [st₁]
      by_cases hs : side = s
      · subst hs; rw [Function.update_self]; exact Nat.mod_lt _ (by positivity)
      · rw [Function.update_of_ne hs]; exact hv.tailHead_lt side
    · intro side vp hvp; rw [htotP₁]
      dsimp only [st₁] at hvp ⊢
      by_cases hc : side = s ∧ vp = st.fullPages s
      · rw [set2, ite_eq_left hc]; omega
      · rw [set2_of_ne _ _ _ _ _ _ hc]
        have hvp' : vp < st.fullPages side := by
          by_cases hs : side = s
          · subst hs; rw [Function.update_self] at hvp
            have hne : vp ≠ st.fullPages side := fun h => hc ⟨rfl, h⟩
            omega
          · rwa [Function.update_of_ne hs] at hvp
        exact (hv.page_lt side vp hvp').trans (Nat.lt_succ_self st.totalPages)
    · intro side vp hvp
      dsimp only [st₁] at hvp ⊢
      by_cases hc : side = s ∧ vp = st.fullPages s
      · obtain ⟨rfl, rfl⟩ := hc
        simp [set2]
      · rw [set2_of_ne _ _ _ _ _ _ hc]
        have hvp' : vp < st.fullPages side := by
          by_cases hs : side = s
          · subst hs; rw [Function.update_self] at hvp
            have hne : vp ≠ st.fullPages side := fun h => hc ⟨rfl, h⟩
            omega
          · rwa [Function.update_of_ne hs] at hvp
        have hp_ne : st.pageOf side vp ≠ st.totalPages := Nat.ne_of_lt (hv.page_lt side vp hvp')
        rw [Function.update_of_ne hp_ne, Function.update_of_ne hp_ne]
        exact hv.owner_pageOf side vp hvp'
    · intro P hP; rw [htotP₁] at hP
      dsimp only [st₁]
      by_cases hPQ : P = st.totalPages
      · subst hPQ; simp [set2]
      · have hP_lt : P < st.totalPages := by omega
        rw [Function.update_of_ne hPQ, Function.update_of_ne hPQ]
        obtain ⟨hvp_lt, hpo⟩ := hv.pageOf_owner P hP_lt
        refine ⟨?_, ?_⟩
        · by_cases hs : st.ownerSide P = s
          · rw [hs, Function.update_self]; rw [hs] at hvp_lt; omega
          · rwa [Function.update_of_ne hs]
        · have hc : ¬(st.ownerSide P = s ∧ st.ownerVp P = st.fullPages s) := by
            rintro ⟨hs, hveq⟩; rw [hs, hveq] at hvp_lt; omega
          rw [set2_of_ne _ _ _ _ _ _ hc]; exact hpo
    · intro side t' ht'
      by_cases hs : side = s
      · subst hs; dsimp only [st₁] at ht'; rw [Function.update_self] at ht'
        rw [hring_shift t']; exact hv.tailRes_lt side (st.pageSize + t') (by omega)
      · dsimp only [st₁] at ht'; rw [Function.update_of_ne hs] at ht'
        have hrs : st₁.ringSlot side t' = st.ringSlot side t' := by
          dsimp only [st₁, ringSlot]; rw [Function.update_of_ne hs]
        rw [hrs]; exact hv.tailRes_lt side t' ht'
    · intro side t' ht'
      rw [htotI₁, htp₁_eq side t' ht']
      by_cases hs : side = s
      · subst hs; dsimp only [st₁] at ht'; rw [Function.update_self] at ht'
        simp only [↓reduceIte]; exact hv.tail_lt side (st.pageSize + t') (by omega)
      · dsimp only [st₁] at ht'; rw [Function.update_of_ne hs] at ht'
        simp only [hs, ↓reduceIte]; exact hv.tail_lt side t' ht'
    · intro side t' ht'
      by_cases hs : side = s
      · subst hs; dsimp only [st₁] at ht'; rw [Function.update_self] at ht'
        rw [hring_shift t']; exact hv.owner_tail side (st.pageSize + t') (by omega)
      · dsimp only [st₁] at ht'; rw [Function.update_of_ne hs] at ht'
        have hrs : st₁.ringSlot side t' = st.ringSlot side t' := by
          dsimp only [st₁, ringSlot]; rw [Function.update_of_ne hs]
        rw [hrs]; exact hv.owner_tail side t' ht'
    · intro p hplo hphi_p
      rw [htotP₁] at hplo; rw [htotI₁] at hphi_p
      change (st.totalPages + 1) * st.pageSize ≤ p at hplo
      have hp_lo0 : st.totalPages * st.pageSize ≤ p := by rw [Nat.add_mul, one_mul] at hplo; omega
      obtain ⟨hkp, htp, htpp⟩ := hv.tail_owner p hp_lo0 hphi_p
      set res := p % (8 * st.pageSize)
      set side := st.tailOwnerSide res
      set k := st.tailOwnerRing res
      by_cases hs : side = s
      · have ht_geB : st.pageSize ≤ ringIdxOfSlot (st.tailHead s) st.pageSize k := by
          by_contra hltB
          have hltB' : ringIdxOfSlot (st.tailHead s) st.pageSize k < st.pageSize := by omega
          have hp_eq : st.tailPhys side (ringIdxOfSlot (st.tailHead side) st.pageSize k) = p := htpp
          rw [hs, hstaged _ hltB'] at hp_eq
          rw [Nat.add_mul, one_mul] at hplo; omega
        set t₀ := ringIdxOfSlot (st.tailHead s) st.pageSize k with ht₀_def
        have hk_eq : k = (st.tailHead s + t₀) % (4 * st.pageSize) :=
          (mod_add_ringIdxOfSlot hkp).symm
        have ht₀_lt : t₀ < st.tailCount s := by
          have htp' : ringIdxOfSlot (st.tailHead side) st.pageSize k < st.tailCount side := htp
          rwa [hs] at htp'
        have ht₁_eq : ringIdxOfSlot (st₁.tailHead s) st.pageSize k = t₀ - st.pageSize := by
          dsimp only [st₁]; rw [Function.update_self, hk_eq]
          have hsh : (st.tailHead s + t₀) % (4 * st.pageSize) =
              ((st.tailHead s + st.pageSize) % (4 * st.pageSize) + (t₀ - st.pageSize)) %
                (4 * st.pageSize) := by
            rw [mod_ring_shift_add hB, show st.pageSize + (t₀ - st.pageSize) = t₀ by omega]
          rw [hsh]
          have htc_lt := hv.tailCount_lt s
          exact ringIdxOfSlot_mod hB (by omega)
        change k < 4 * st.pageSize ∧
          ringIdxOfSlot (st₁.tailHead side) st.pageSize k < st₁.tailCount side ∧
          st₁.tailPhys side (ringIdxOfSlot (st₁.tailHead side) st.pageSize k) = p
        rw [hs, ht₁_eq]
        have ht'_lt : t₀ - st.pageSize < st₁.tailCount s := by
          dsimp only [st₁]; rw [Function.update_self]; omega
        refine ⟨hkp, ht'_lt, ?_⟩
        rw [htp₁_eq s (t₀ - st.pageSize) ht'_lt, ite_eq_left rfl,
          show st.pageSize + (t₀ - st.pageSize) = t₀ by omega]
        simpa only [hs] using htpp
      · have hth_eq : st₁.tailHead side = st.tailHead side := by
          dsimp only [st₁]; rw [Function.update_of_ne hs]
        have htc_eq : st₁.tailCount side = st.tailCount side := by
          dsimp only [st₁]; rw [Function.update_of_ne hs]
        change k < 4 * st.pageSize ∧
          ringIdxOfSlot (st₁.tailHead side) st.pageSize k < st₁.tailCount side ∧
          st₁.tailPhys side (ringIdxOfSlot (st₁.tailHead side) st.pageSize k) = p
        rw [hth_eq]
        have ht'_lt : ringIdxOfSlot (st.tailHead side) st.pageSize k < st₁.tailCount side := by
          rw [htc_eq]; exact htp
        refine ⟨hkp, ht'_lt, ?_⟩
        rw [htp₁_eq side _ ht'_lt, ite_eq_right hs]
        exact htpp
  -- Potential drop at `.promote` commit:
  have hphi₁ : 16 * st₁.phi ≤ 24 * st.pageSize + 49 := by
    have hp_b := hd.pot_bound
    have hs_b := hd.side_bound
    have hsl := hd.slack_le
    rw [hj, ite_eq_right (by rintro ⟨⟩)] at hp_b
    simp only [remTicks, hj] at hp_b
    simp only [ActiveSideBound, hj, remTicks] at hs_b
    unfold phi dev at hp_b ⊢
    dsimp only [st₁]
    cases s <;> simp only [Function.update_self,
      Function.update_of_ne (by decide : false ≠ true),
      Function.update_of_ne (by decide : true ≠ false), Nat.succ_pos, ↓reduceIte] <;>
      split_ifs at hp_b ⊢ <;> omega
  refine ⟨hv₁, hphi₁, hvirt₁, htotI₁, fun side idx hidx => ?_⟩
  unfold toPhys
  dsimp only
  have heff₁ : ∀ P u, st₁.effPage P u = P := fun _ _ => rfl
  have heff₀ : ∀ P u, st.effPage P u = P := by intro P u; simp [effPage, hj]
  rw [show st₁.pageSize = st.pageSize from rfl]
  by_cases hs : side = s
  · subst hs
    have hfp₁ : st₁.fullPages side = st.fullPages side + 1 := by
      dsimp only [st₁]; rw [Function.update_self]
    rw [hfp₁]
    by_cases hlt0 : idx < st.fullPages side * st.pageSize
    · have hlt1 : idx < (st.fullPages side + 1) * st.pageSize := by
        rw [Nat.add_mul, one_mul]; omega
      rw [ite_eq_left hlt1, ite_eq_left hlt0, heff₁, heff₀]
      have hvp_ne : idx / st.pageSize ≠ st.fullPages side :=
        Nat.ne_of_lt ((Nat.div_lt_iff_lt_mul hB).mpr hlt0)
      dsimp only [st₁]
      rw [set2_of_ne _ _ _ _ _ _ (fun h => hvp_ne h.2)]
    · by_cases hlt1 : idx < (st.fullPages side + 1) * st.pageSize
      · rw [ite_eq_left hlt1, ite_eq_right hlt0, heff₁]
        have hvp_eq : idx / st.pageSize = st.fullPages side := by
          have h1 : st.fullPages side ≤ idx / st.pageSize :=
            (Nat.le_div_iff_mul_le hB).mpr (by omega)
          have h2 : idx / st.pageSize < st.fullPages side + 1 :=
            (Nat.div_lt_iff_lt_mul hB).mpr hlt1
          omega
        have hu_eq : idx - st.fullPages side * st.pageSize = idx % st.pageSize := by
          have hd := Nat.div_add_mod idx st.pageSize
          rw [hvp_eq, Nat.mul_comm st.pageSize (st.fullPages side)] at hd
          omega
        dsimp only [st₁]
        rw [hvp_eq, set2_self, hu_eq, hstaged (idx % st.pageSize) (Nat.mod_lt idx hB)]
      · rw [ite_eq_right hlt1, ite_eq_right hlt0]
        set t' := idx - (st.fullPages side + 1) * st.pageSize with ht'_def
        have ht'_lt : t' < st₁.tailCount side := by
          have hv_eq : st₁.virtLen side = st.virtLen side := congrFun hvirt₁ side
          unfold virtLen at hv_eq hidx
          rw [hfp₁, show st₁.pageSize = st.pageSize from rfl] at hv_eq
          rw [Nat.add_mul, one_mul] at hv_eq ht'_def hlt1
          omega
        rw [htp₁_eq side t' ht'_lt, ite_eq_left rfl]
        congr 1; rw [Nat.add_mul, one_mul] at *; omega
  · have hfp₁ : st₁.fullPages side = st.fullPages side := by
      dsimp only [st₁]; rw [Function.update_of_ne hs]
    rw [hfp₁]
    split_ifs with hlt
    · rw [heff₁, heff₀]
      dsimp only [st₁]
      rw [set2_of_ne _ _ _ _ _ _ (fun h => hs h.1)]
    · have ht'_lt : idx - st.fullPages side * st.pageSize < st₁.tailCount side := by
        dsimp only [st₁]; rw [Function.update_of_ne hs]
        unfold virtLen at hidx; omega
      rw [htp₁_eq side _ ht'_lt, ite_eq_right hs]

private theorem tickOne_demoteSwap_commit {st : PagePairState} {slack : ℕ} {s : Bool} {cur : ℕ}
    (hd : DriftInv st slack) (hj : st.job = .demoteSwap s cur) (hcur : ¬(cur < st.pageSize)) :
    let P_dem := st.pageOf s (st.fullPages s - 1)
    let P_last := st.totalPages - 1
    let s_last := st.ownerSide P_last
    let vp_last := st.ownerVp P_last
    let st₁ : PagePairState :=
      { st with
        pageOf := set2 (set2 st.pageOf s_last vp_last P_dem) s (st.fullPages s - 1) P_last
        ownerSide := Function.update (Function.update st.ownerSide P_dem s_last) P_last s
        ownerVp := Function.update (Function.update st.ownerVp P_dem vp_last) P_last
          (st.fullPages s - 1)
        job := .demoteBuild s 0 }
    DriftInv st₁ (slack - 1) ∧
    st₁.virtLen = st.virtLen ∧
    st₁.totalItems = st.totalItems ∧
    ∀ side idx, idx < st.virtLen side → st₁.toPhys side idx = st.toPhys side idx := by
  intro P_dem P_last s_last vp_last st₁
  have hv := hd.valid
  have hB32 : 32 ≤ st.pageSize := hd.pageSize_ge
  have hB : 0 < st.pageSize := hv.pageSize_pos
  have hjv := hd.jobValid; unfold JobValid at hjv; rw [hj] at hjv
  obtain ⟨hcur_le, hq_pos, hP_lt⟩ := hjv
  have hcur_eq : cur = st.pageSize := by omega
  subst cur
  have hQ_pos : 0 < st.totalPages := by unfold totalPages; cases s <;> omega
  have hPl_def : P_last = st.totalPages - 1 := rfl
  have hPd_def : P_dem = st.pageOf s (st.fullPages s - 1) := rfl
  have hPl_lt : P_last < st.totalPages := by omega
  have hPd_lt : P_dem < st.totalPages := by omega
  have hP_ne : P_dem ≠ P_last := Nat.ne_of_lt hP_lt
  obtain ⟨hvpl_lt, hpol⟩ := hv.pageOf_owner P_last hPl_lt
  have hsk_ne : ¬(s = s_last ∧ st.fullPages s - 1 = vp_last) := by
    rintro ⟨hse, hve⟩
    have : P_dem = P_last := by dsimp only [P_dem]; subst hse; rw [hve]; exact hpol
    exact hP_ne this
  have heff_page : ∀ side vp, vp < st.fullPages side → ∀ u < st.pageSize,
      st₁.pageOf side vp = st.effPage (st.pageOf side vp) u := by
    intro side vp hvp u hu
    unfold effPage
    rw [hj]
    dsimp only [st₁]
    rw [ite_eq_left ⟨hu, hq_pos⟩]
    change set2 (set2 st.pageOf s_last vp_last P_dem) s (st.fullPages s - 1) P_last side vp =
      if st.pageOf side vp = P_dem then P_last
      else if st.pageOf side vp = P_last then P_dem
      else st.pageOf side vp
    by_cases hc1 : side = s ∧ vp = st.fullPages s - 1
    · obtain ⟨rfl, rfl⟩ := hc1
      rw [set2_self]; simp [P_dem]
    · rw [set2_of_ne _ _ _ _ _ _ hc1]
      have hne_Pd : st.pageOf side vp ≠ P_dem := by
        intro heq
        have ho1 := hv.owner_pageOf side vp hvp
        have ho2 := hv.owner_pageOf s (st.fullPages s - 1) (by omega)
        change st.ownerSide P_dem = s ∧ st.ownerVp P_dem = st.fullPages s - 1 at ho2
        rw [heq] at ho1
        exact hc1 ⟨ho1.1.symm.trans ho2.1, ho1.2.symm.trans ho2.2⟩
      rw [ite_eq_right hne_Pd]
      by_cases hc2 : side = s_last ∧ vp = vp_last
      · obtain ⟨rfl, rfl⟩ := hc2
        rw [set2_self, hpol, ite_eq_left rfl]
      · rw [set2_of_ne _ _ _ _ _ _ hc2]
        have hne_Pl : st.pageOf side vp ≠ P_last := by
          intro heq
          have ho1 := hv.owner_pageOf side vp hvp
          rw [heq] at ho1
          exact hc2 ⟨ho1.1.symm, ho1.2.symm⟩
        rw [ite_eq_right hne_Pl]
  have hv₁ : st₁.Valid := by
    refine ⟨hB, hv.tailCount_lt, hv.tailSum_lt, hv.tailHead_lt, ?_, ?_, ?_,
      hv.tailRes_lt, hv.tail_lt, hv.owner_tail, hv.tail_owner⟩
    · intro side vp hvp
      change st₁.pageOf side vp < st.totalPages
      rw [heff_page side vp hvp 0 hB]
      exact hv.effPage_lt (hv.page_lt side vp hvp) 0
    · intro side vp hvp
      dsimp only [st₁]
      by_cases hc1 : side = s ∧ vp = st.fullPages s - 1
      · obtain ⟨rfl, rfl⟩ := hc1
        rw [set2_self, Function.update_self, Function.update_self]
        exact ⟨rfl, rfl⟩
      · rw [set2_of_ne _ _ _ _ _ _ hc1]
        by_cases hc2 : side = s_last ∧ vp = vp_last
        · obtain ⟨rfl, rfl⟩ := hc2
          rw [set2_self, Function.update_of_ne hP_ne, Function.update_self,
            Function.update_of_ne hP_ne, Function.update_self]
          exact ⟨rfl, rfl⟩
        · rw [set2_of_ne _ _ _ _ _ _ hc2]
          have hne_Pd : st.pageOf side vp ≠ P_dem := by
            intro heq
            have ho1 := hv.owner_pageOf side vp hvp
            have ho2 := hv.owner_pageOf s (st.fullPages s - 1) (by omega)
            rw [heq] at ho1; exact hc1 ⟨ho1.1.symm.trans ho2.1, ho1.2.symm.trans ho2.2⟩
          have hne_Pl : st.pageOf side vp ≠ P_last := by
            intro heq
            have ho1 := hv.owner_pageOf side vp hvp
            rw [heq] at ho1; exact hc2 ⟨ho1.1.symm, ho1.2.symm⟩
          rw [Function.update_of_ne hne_Pl, Function.update_of_ne hne_Pd,
            Function.update_of_ne hne_Pl, Function.update_of_ne hne_Pd]
          exact hv.owner_pageOf side vp hvp
    · intro P hP
      dsimp only [st₁]
      by_cases hPl : P = P_last
      · subst hPl
        rw [Function.update_self, Function.update_self]
        exact ⟨by omega, set2_self ..⟩
      · by_cases hPd : P = P_dem
        · subst hPd
          rw [Function.update_of_ne hP_ne, Function.update_self,
            Function.update_of_ne hP_ne, Function.update_self]
          refine ⟨hvpl_lt, ?_⟩
          rw [set2_of_ne _ _ _ _ _ _ (fun h => hsk_ne ⟨h.1.symm, h.2.symm⟩), set2_self]
        · rw [Function.update_of_ne hPl, Function.update_of_ne hPd,
            Function.update_of_ne hPl, Function.update_of_ne hPd]
          obtain ⟨hvpP, hpoP⟩ := hv.pageOf_owner P hP
          refine ⟨hvpP, ?_⟩
          have hc1 : ¬(st.ownerSide P = s ∧ st.ownerVp P = st.fullPages s - 1) := by
            rintro ⟨h1, h2⟩; apply hPd; rw [← hpoP, h1, h2]
          have hc2 : ¬(st.ownerSide P = s_last ∧ st.ownerVp P = vp_last) := by
            rintro ⟨h1, h2⟩; apply hPl; rw [← hpoP, h1, h2]; exact hpol
          rw [set2_of_ne _ _ _ _ _ _ hc1, set2_of_ne _ _ _ _ _ _ hc2, hpoP]
  have hp_b := hd.pot_bound
  have hs_b := hd.side_bound
  have hsl := hd.slack_le
  rw [hj, ite_eq_right (by rintro ⟨⟩)] at hp_b
  simp only [remTicks, hj] at hp_b
  simp only [ActiveSideBound, hj, remTicks] at hs_b
  have hjv₁ : st₁.JobValid := by
    unfold JobValid
    dsimp only [st₁]
    refine ⟨Nat.zero_le _, hq_pos, set2_self .., by omega, ?_,
      fun _ hu => absurd hu (Nat.not_lt_zero _)⟩
    have hphi_le := hd.phi_le
    unfold phi dev at hphi_le
    cases s <;> omega
  have hd₁ : DriftInv st₁ (slack - 1) := by
    refine ⟨hv₁, hB32, hjv₁, by omega, ?_, ?_⟩
    · rw [ite_eq_right (by rintro ⟨⟩)]
      change 16 * st.phi + (st.pageSize + 1 - 0) ≤ 28 * st.pageSize + (slack - 1)
      omega
    · unfold ActiveSideBound remTicks
      dsimp only [st₁]
      omega
  refine ⟨hd₁, rfl, rfl, fun side idx _ => ?_⟩
  unfold toPhys
  dsimp only
  rw [show st₁.pageSize = st.pageSize from rfl, show st₁.fullPages = st.fullPages from rfl]
  split_ifs with hlt
  · have hvp : idx / st.pageSize < st.fullPages side := (Nat.div_lt_iff_lt_mul hB).mpr hlt
    have heff₁ : st₁.effPage (st₁.pageOf side (idx / st.pageSize)) (idx % st.pageSize) =
        st₁.pageOf side (idx / st.pageSize) := rfl
    rw [heff₁, heff_page side (idx / st.pageSize) hvp (idx % st.pageSize) (Nat.mod_lt idx hB)]
  · rfl

private theorem tickOne_demoteBuild_commit {st : PagePairState} {slack : ℕ} {s : Bool} {cur : ℕ}
    (hd : DriftInv st slack) (hj : st.job = .demoteBuild s cur) (hcur : ¬(cur < st.pageSize)) :
    let st₁ : PagePairState :=
      { st with
        fullPages := Function.update st.fullPages s (st.fullPages s - 1)
        tailCount := Function.update st.tailCount s (st.tailCount s + st.pageSize)
        tailHead := Function.update st.tailHead s
          ((st.tailHead s + 3 * st.pageSize) % (4 * st.pageSize))
        job := .idle }
    st₁.Valid ∧
    16 * st₁.phi ≤ 24 * st.pageSize + 49 ∧
    st₁.virtLen = st.virtLen ∧
    st₁.totalItems = st.totalItems ∧
    ∀ side idx, idx < st.virtLen side → st₁.toPhys side idx = st.toPhys side idx := by
  intro st₁
  have hv := hd.valid
  have hB32 : 32 ≤ st.pageSize := hd.pageSize_ge
  have hB : 0 < st.pageSize := hv.pageSize_pos
  have hjv := hd.jobValid; unfold JobValid at hjv; rw [hj] at hjv
  obtain ⟨hcur_le, hq_pos, hp_last, htc_3B, hts_7B, hstaged⟩ := hjv
  have hcur_eq : cur = st.pageSize := by omega
  subst cur
  have hQ_pos : 0 < st.totalPages := by unfold totalPages; cases s <;> omega
  have htotP₁ : st₁.totalPages = st.totalPages - 1 := by
    dsimp only [st₁, totalPages]; cases s <;> simp <;> omega
  have hvirt₁ : st₁.virtLen = st.virtLen := by
    ext side
    dsimp only [st₁, virtLen]
    by_cases hs : side = s
    · subst hs; rw [Function.update_self, Function.update_self]
      have : (st.fullPages side - 1) * st.pageSize + st.pageSize =
          st.fullPages side * st.pageSize := by
        calc (st.fullPages side - 1) * st.pageSize + st.pageSize
            = (st.fullPages side - 1 + 1) * st.pageSize := by ring
          _ = st.fullPages side * st.pageSize := by rw [Nat.sub_add_cancel hq_pos]
      omega
    · simp [hs]
  have htotI₁ : st₁.totalItems = st.totalItems := by
    unfold totalItems; rw [hvirt₁]
  have hQB : st.totalPages * st.pageSize = (st.totalPages - 1) * st.pageSize + st.pageSize := by
    calc st.totalPages * st.pageSize
        = (st.totalPages - 1 + 1) * st.pageSize := by rw [Nat.sub_add_cancel hQ_pos]
      _ = (st.totalPages - 1) * st.pageSize + st.pageSize := by ring
  have htot_hi : st.totalItems < (st.totalPages - 1) * st.pageSize + 8 * st.pageSize := by
    have hts_lt7 : st.tailCount false + st.tailCount true < 7 * st.pageSize := by
      have hphi_le := hd.phi_le
      have hs_b := hd.side_bound
      have hsl := hd.slack_le
      simp only [ActiveSideBound, hj, remTicks] at hs_b
      unfold phi dev at hphi_le
      cases s <;> split_ifs at hphi_le <;> omega
    rw [st.totalItems_eq, hQB]
    omega
  have hring_s : ∀ t', st₁.ringSlot s t' =
      if t' < st.pageSize then (st.tailHead s + 3 * st.pageSize + t') % (4 * st.pageSize)
      else st.ringSlot s (t' - st.pageSize) := by
    intro t'
    dsimp only [st₁, ringSlot]
    rw [Function.update_self, mod_ring_shift_add hB]
    split_ifs with hlt
    · rw [Nat.add_assoc]
    · have heq : 3 * st.pageSize + t' = (t' - st.pageSize) + 4 * st.pageSize := by omega
      rw [heq, ← Nat.add_assoc, Nat.add_mod_right]
  have htp₁_s_ltB : ∀ u < st.pageSize,
      st₁.tailPhys s u = (st.totalPages - 1) * st.pageSize + u := by
    intro u hu
    obtain ⟨htr_u, _, _⟩ := hstaged u hu
    change physOfRes (st₁.totalPages * st₁.pageSize) st₁.pageSize
      (st₁.tailRes s (st₁.ringSlot s u)) = _
    rw [htotP₁, show st₁.pageSize = st.pageSize from rfl, hring_s u, ite_eq_left hu,
      show st₁.tailRes = st.tailRes from rfl, htr_u]
    exact physOfRes_mod hB (Nat.le_add_right _ _) (by omega)
  have htp₁_old : ∀ side t, t < st.tailCount side →
      st₁.tailPhys side (if side = s then st.pageSize + t else t) = st.tailPhys side t := by
    intro side t ht
    have hp_lo : (st.totalPages - 1) * st.pageSize ≤ st.tailPhys side t := by
      have h1 : st.totalPages * st.pageSize ≤ st.tailPhys side t := le_physOfRes _ _ _
      omega
    have hp_hi : st.tailPhys side t < (st.totalPages - 1) * st.pageSize + 8 * st.pageSize :=
      (hv.tail_lt side t ht).trans htot_hi
    have hmod := mod_physOfRes (base := st.totalPages * st.pageSize) (hv.tailRes_lt side t ht)
    change st.tailPhys side t % (8 * st.pageSize) = _ at hmod
    by_cases hs : side = s
    · subst hs
      simp only [↓reduceIte]
      change physOfRes (st₁.totalPages * st₁.pageSize) st₁.pageSize
        (st₁.tailRes side (st₁.ringSlot side (st.pageSize + t))) = _
      rw [htotP₁, show st₁.pageSize = st.pageSize from rfl, hring_s (st.pageSize + t),
        ite_eq_right (by omega), Nat.add_sub_cancel_left,
        show st₁.tailRes = st.tailRes from rfl, ← hmod]
      exact physOfRes_mod hB hp_lo hp_hi
    · simp only [hs, ↓reduceIte]
      have hrs : st₁.ringSlot side t = st.ringSlot side t := by
        dsimp only [st₁, ringSlot]; rw [Function.update_of_ne hs]
      change physOfRes (st₁.totalPages * st₁.pageSize) st₁.pageSize
        (st₁.tailRes side (st₁.ringSlot side t)) = _
      rw [htotP₁, show st₁.pageSize = st.pageSize from rfl, hrs,
        show st₁.tailRes = st.tailRes from rfl, ← hmod]
      exact physOfRes_mod hB hp_lo hp_hi
  have hv₁ : st₁.Valid := by
    refine ⟨hB, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro side; dsimp only [st₁]
      by_cases hs : side = s
      · subst hs; rw [Function.update_self]; omega
      · rw [Function.update_of_ne hs]; exact hv.tailCount_lt side
    · dsimp only [st₁]
      have hp_b := hd.pot_bound; have hs_b := hd.side_bound; have hsl := hd.slack_le
      rw [hj, ite_eq_right (by rintro ⟨⟩)] at hp_b
      simp only [remTicks, hj] at hp_b
      simp only [ActiveSideBound, hj, remTicks] at hs_b
      unfold phi dev at hp_b
      cases s <;> simp at hs_b ⊢ <;> omega
    · intro side; dsimp only [st₁]
      by_cases hs : side = s
      · subst hs; rw [Function.update_self]; exact Nat.mod_lt _ (by positivity)
      · rw [Function.update_of_ne hs]; exact hv.tailHead_lt side
    · intro side vp hvp; rw [htotP₁]
      have hvp' : vp < st.fullPages side := by
        dsimp only [st₁] at hvp; by_cases hs : side = s
        · subst hs; rw [Function.update_self] at hvp; omega
        · rwa [Function.update_of_ne hs] at hvp
      have hp_lt := hv.page_lt side vp hvp'
      have hp_ne : st.pageOf side vp ≠ st.totalPages - 1 := by
        intro heq
        have ho1 := hv.owner_pageOf side vp hvp'
        have ho2 := hv.owner_pageOf s (st.fullPages s - 1) (by omega)
        rw [hp_last] at ho2; rw [heq] at ho1
        have hse := ho1.1.symm.trans ho2.1; subst hse
        have hve := ho1.2.symm.trans ho2.2
        dsimp only [st₁] at hvp; rw [Function.update_self] at hvp; omega
      exact Nat.lt_of_le_of_ne (Nat.le_sub_one_of_lt hp_lt) hp_ne
    · intro side vp hvp
      have hvp' : vp < st.fullPages side := by
        dsimp only [st₁] at hvp; by_cases hs : side = s
        · subst hs; rw [Function.update_self] at hvp; omega
        · rwa [Function.update_of_ne hs] at hvp
      exact hv.owner_pageOf side vp hvp'
    · intro P hP; rw [htotP₁] at hP
      obtain ⟨hvpP, hpoP⟩ := hv.pageOf_owner P (by omega)
      refine ⟨?_, hpoP⟩
      dsimp only [st₁]
      by_cases hs : st.ownerSide P = s
      · rw [hs, Function.update_self]
        rw [hs] at hvpP hpoP
        have hne_v : st.ownerVp P ≠ st.fullPages s - 1 := by
          intro heq; rw [heq, hp_last] at hpoP; omega
        omega
      · rwa [Function.update_of_ne hs]
    · intro side t' ht'
      by_cases hs : side = s
      · subst hs; dsimp only [st₁] at ht'; rw [Function.update_self] at ht'
        rw [hring_s t']
        split_ifs with hlt
        · rw [(hstaged t' hlt).1]; exact Nat.mod_lt _ (by positivity)
        · exact hv.tailRes_lt side (t' - st.pageSize) (by omega)
      · dsimp only [st₁] at ht'; rw [Function.update_of_ne hs] at ht'
        have hrs : st₁.ringSlot side t' = st.ringSlot side t' := by
          dsimp only [st₁, ringSlot]; rw [Function.update_of_ne hs]
        rw [hrs]; exact hv.tailRes_lt side t' ht'
    · intro side t' ht'; rw [htotI₁]
      by_cases hs : side = s
      · subst hs; dsimp only [st₁] at ht'; rw [Function.update_self] at ht'
        by_cases hlt : t' < st.pageSize
        · rw [htp₁_s_ltB t' hlt]
          have hti := st.totalItems_eq; omega
        · have h1 := htp₁_old side (t' - st.pageSize) (by omega)
          simp only [↓reduceIte, show st.pageSize + (t' - st.pageSize) = t' by omega] at h1
          rw [h1]; exact hv.tail_lt side (t' - st.pageSize) (by omega)
      · dsimp only [st₁] at ht'; rw [Function.update_of_ne hs] at ht'
        have h1 := htp₁_old side t' ht'
        simp only [hs, ↓reduceIte] at h1
        rw [h1]; exact hv.tail_lt side t' ht'
    · intro side t' ht'
      by_cases hs : side = s
      · subst hs; dsimp only [st₁] at ht'; rw [Function.update_self] at ht'
        rw [hring_s t']
        split_ifs with hlt
        · obtain ⟨htr, hos, hor⟩ := hstaged t' hlt
          dsimp only [st₁]; rw [htr]; exact ⟨hos, hor⟩
        · exact hv.owner_tail side (t' - st.pageSize) (by omega)
      · dsimp only [st₁] at ht'; rw [Function.update_of_ne hs] at ht'
        have hrs : st₁.ringSlot side t' = st.ringSlot side t' := by
          dsimp only [st₁, ringSlot]; rw [Function.update_of_ne hs]
        rw [hrs]; exact hv.owner_tail side t' ht'
    · intro p hplo hphi_p
      rw [htotP₁] at hplo; rw [htotI₁] at hphi_p
      change (st.totalPages - 1) * st.pageSize ≤ p at hplo
      by_cases hp_ltQ : p < st.totalPages * st.pageSize
      · set u := p - (st.totalPages - 1) * st.pageSize with hu_def
        have hu_lt : u < st.pageSize := by omega
        have hp_eq : p = (st.totalPages - 1) * st.pageSize + u := by omega
        obtain ⟨_, hos, hor⟩ := hstaged u hu_lt
        set res := ((st.totalPages - 1) * st.pageSize + u) % (8 * st.pageSize)
        set k_u := (st.tailHead s + 3 * st.pageSize + u) % (4 * st.pageSize)
        have hk_lt : k_u < 4 * st.pageSize := Nat.mod_lt _ (by positivity)
        have hri_u : ringIdxOfSlot (st₁.tailHead s) st.pageSize k_u = u := by
          dsimp only [st₁, k_u]; rw [Function.update_self]
          have hsh : (st.tailHead s + 3 * st.pageSize + u) % (4 * st.pageSize) =
              ((st.tailHead s + 3 * st.pageSize) % (4 * st.pageSize) + u) %
                (4 * st.pageSize) := by
            rw [mod_ring_shift_add hB, Nat.add_assoc]
          rw [hsh]
          exact ringIdxOfSlot_mod hB (by omega)
        rw [hp_eq]
        change (let side := st.tailOwnerSide res;
          let k := st.tailOwnerRing res;
          let t := ringIdxOfSlot (st₁.tailHead side) st.pageSize k;
          k < 4 * st.pageSize ∧ t < st₁.tailCount side ∧
            st₁.tailPhys side t = (st.totalPages - 1) * st.pageSize + u)
        dsimp only
        rw [hos, hor, hri_u]
        refine ⟨hk_lt, ?_, htp₁_s_ltB u hu_lt⟩
        dsimp only [st₁]; rw [Function.update_self]; omega
      · have hp_geQ : st.totalPages * st.pageSize ≤ p := by omega
        obtain ⟨hkp, htp, htpp⟩ := hv.tail_owner p hp_geQ hphi_p
        set res := p % (8 * st.pageSize)
        set side := st.tailOwnerSide res
        set k := st.tailOwnerRing res
        set t₀ := ringIdxOfSlot (st.tailHead side) st.pageSize k with ht₀_def
        by_cases hs : side = s
        · have hk_eq : k = (st.tailHead s + t₀) % (4 * st.pageSize) :=
            hs ▸ (mod_add_ringIdxOfSlot hkp).symm
          have htp_s : t₀ < st.tailCount s := by
            have htp' : t₀ < st.tailCount side := htp
            rwa [hs] at htp'
          have ht₀_3B : t₀ < 3 * st.pageSize := htp_s.trans htc_3B
          have hri_1 : ringIdxOfSlot (st₁.tailHead s) st.pageSize k = st.pageSize + t₀ := by
            dsimp only [st₁]; rw [Function.update_self, hk_eq]
            have hsh : (st.tailHead s + t₀) % (4 * st.pageSize) =
                ((st.tailHead s + 3 * st.pageSize) % (4 * st.pageSize) + (st.pageSize + t₀)) %
                  (4 * st.pageSize) := by
              rw [mod_ring_shift_add hB,
                show 3 * st.pageSize + (st.pageSize + t₀) = t₀ + 4 * st.pageSize by omega,
                ← Nat.add_assoc, Nat.add_mod_right]
            rw [hsh]
            exact ringIdxOfSlot_mod hB (by omega)
          change k < 4 * st.pageSize ∧
            ringIdxOfSlot (st₁.tailHead side) st.pageSize k < st₁.tailCount side ∧
            st₁.tailPhys side (ringIdxOfSlot (st₁.tailHead side) st.pageSize k) = p
          rw [hs, hri_1]
          have ht'_lt : st.pageSize + t₀ < st₁.tailCount s := by
            dsimp only [st₁]; rw [Function.update_self]; omega
          refine ⟨hkp, ht'_lt, ?_⟩
          have h1 := htp₁_old s t₀ htp_s
          simp only [↓reduceIte] at h1
          rw [h1]; simpa only [hs] using htpp
        · have hth_eq : st₁.tailHead side = st.tailHead side := by
            dsimp only [st₁]; rw [Function.update_of_ne hs]
          have htc_eq : st₁.tailCount side = st.tailCount side := by
            dsimp only [st₁]; rw [Function.update_of_ne hs]
          change k < 4 * st.pageSize ∧
            ringIdxOfSlot (st₁.tailHead side) st.pageSize k < st₁.tailCount side ∧
            st₁.tailPhys side (ringIdxOfSlot (st₁.tailHead side) st.pageSize k) = p
          rw [hth_eq, htc_eq]
          refine ⟨hkp, htp, ?_⟩
          have h1 := htp₁_old side t₀ htp
          simp only [hs, ↓reduceIte] at h1
          rw [h1]; exact htpp
  -- Potential drop at `.demoteBuild` commit:
  have hphi₁ : 16 * st₁.phi ≤ 24 * st.pageSize + 49 := by
    have hp_b := hd.pot_bound
    have hs_b := hd.side_bound
    have hsl := hd.slack_le
    rw [hj, ite_eq_right (by rintro ⟨⟩)] at hp_b
    simp only [remTicks, hj] at hp_b
    simp only [ActiveSideBound, hj, remTicks] at hs_b
    unfold phi dev at hp_b ⊢
    dsimp only [st₁]
    cases s <;> simp only [Function.update_self,
      Function.update_of_ne (by decide : false ≠ true),
      Function.update_of_ne (by decide : true ≠ false), hq_pos, ↓reduceIte] at hp_b ⊢ <;>
      split_ifs at hp_b ⊢ <;> omega
  refine ⟨hv₁, hphi₁, hvirt₁, htotI₁, fun side idx hidx => ?_⟩
  unfold toPhys
  dsimp only
  have heff₁ : ∀ P u, st₁.effPage P u = P := fun _ _ => rfl
  have heff₀ : ∀ P u, st.effPage P u = P := by intro P u; simp [effPage, hj]
  rw [show st₁.pageSize = st.pageSize from rfl]
  by_cases hs : side = s
  · subst hs
    have hfp₁ : st₁.fullPages side = st.fullPages side - 1 := by
      dsimp only [st₁]; rw [Function.update_self]
    rw [hfp₁]
    have hQB_s : (st.fullPages side - 1) * st.pageSize + st.pageSize =
        st.fullPages side * st.pageSize := by
      calc (st.fullPages side - 1) * st.pageSize + st.pageSize
          = (st.fullPages side - 1 + 1) * st.pageSize := by ring
        _ = st.fullPages side * st.pageSize := by rw [Nat.sub_add_cancel hq_pos]
    by_cases hlt0 : idx < (st.fullPages side - 1) * st.pageSize
    · have hlt1 : idx < st.fullPages side * st.pageSize := by omega
      rw [ite_eq_left hlt0, ite_eq_left hlt1, heff₁, heff₀]
    · by_cases hlt1 : idx < st.fullPages side * st.pageSize
      · rw [ite_eq_right hlt0, ite_eq_left hlt1, heff₀]
        set u := idx - (st.fullPages side - 1) * st.pageSize with hu_def
        have hu_lt : u < st.pageSize := by omega
        have hvp_eq : idx / st.pageSize = st.fullPages side - 1 := by
          have h1 : st.fullPages side - 1 ≤ idx / st.pageSize :=
            (Nat.le_div_iff_mul_le hB).mpr (by omega)
          have h2 : idx / st.pageSize < st.fullPages side :=
            (Nat.div_lt_iff_lt_mul hB).mpr hlt1
          omega
        have hu_mod : idx % st.pageSize = u := by
          have hd := Nat.div_add_mod idx st.pageSize
          rw [hvp_eq, Nat.mul_comm st.pageSize] at hd
          omega
        rw [htp₁_s_ltB u hu_lt, hvp_eq, hp_last, hu_mod]
      · rw [ite_eq_right hlt0, ite_eq_right hlt1]
        set t := idx - st.fullPages side * st.pageSize with ht_def
        have ht_lt : t < st.tailCount side := by
          unfold virtLen at hidx; omega
        have heq_idx : idx - (st.fullPages side - 1) * st.pageSize = st.pageSize + t := by omega
        rw [heq_idx]
        simpa only [↓reduceIte] using htp₁_old side t ht_lt
  · have hfp₁ : st₁.fullPages side = st.fullPages side := by
      dsimp only [st₁]; rw [Function.update_of_ne hs]
    rw [hfp₁]
    split_ifs with hlt
    · rw [heff₁, heff₀]
    · have ht_lt : idx - st.fullPages side * st.pageSize < st.tailCount side := by
        unfold virtLen at hidx; omega
      simpa only [hs, ↓reduceIte] using htp₁_old side _ ht_lt

theorem tick_driftInv {st : PagePairState} {slack : ℕ} (hd : DriftInv st slack) :
    let res := st.tick
    let st' := res.1
    let sws := res.2
    DriftInv st' (slack - 1) ∧
    st'.pageSize = st.pageSize ∧
    st'.virtLen = st.virtLen ∧
    st'.totalItems = st.totalItems ∧
    sws.length ≤ 1 ∧
    (∀ sw ∈ sws, sw.p₁ < st.totalItems ∧ sw.p₂ < st.totalItems) ∧
    (∀ {α : Type*} (arr : ℕ → α) (side : Bool) (idx : ℕ), idx < st.virtLen side →
      st'.virtAt (applySwaps sws arr) side idx = st.virtAt arr side idx) := by
  dsimp only
  unfold tick tickOne
  have hv := hd.valid
  have hB32 := hd.pageSize_ge
  have hB := hv.pageSize_pos
  cases hj : st.job with
  | idle =>
    dsimp only
    have hp := hd.pot_bound; simp only [hj, ↓reduceIte] at hp
    have hd0 := maybeStartJob_driftInv hv hB32 hj (by omega)
    obtain ⟨hps, _, _, hvl, hti⟩ := maybeStartJob_meta st
    exact ⟨hd0.mono (Nat.zero_le _) (by have := hd.slack_le; omega), hps, hvl, hti,
      Nat.zero_le 1, by simp, fun arr side idx _ => by
        rw [applySwaps_nil, virtAt, maybeStartJob_toPhys]; rfl⟩
  | promote s cur =>
    dsimp only
    by_cases hcur : cur < st.pageSize
    · rw [ite_eq_left hcur]
      dsimp only
      have hjv := hd.jobValid; unfold JobValid at hjv; rw [hj] at hjv
      obtain ⟨_, hB_lt_r, hstaged⟩ := hjv
      have hp1_lo : st.totalPages * st.pageSize ≤ st.tailPhys s cur := le_physOfRes _ _ _
      have hp1_hi : st.tailPhys s cur < st.totalItems := hv.tail_lt s cur (by omega)
      have hp2_lo : st.totalPages * st.pageSize ≤ st.totalPages * st.pageSize + cur :=
        Nat.le_add_right _ _
      have hp2_hi : st.totalPages * st.pageSize + cur < st.totalItems := by
        rw [st.totalItems_eq]; cases s <;> omega
      obtain ⟨hv1, hps1, hfp1, htc1, hth1, hpo1, hos1, hov1, hj1, hsw_len, hsw_lt, htp_f,
        hvirt_sw⟩ := swapTailSlots_spec hv hp1_lo hp1_hi hp2_lo hp2_hi
      set st₁ := (st.swapTailSlots (st.tailPhys s cur) (st.totalPages * st.pageSize + cur)).1
      set sws := (st.swapTailSlots (st.tailPhys s cur) (st.totalPages * st.pageSize + cur)).2
      set st₂ : PagePairState := { st₁ with job := .promote s (cur + 1) }
      have hms : st₂.maybeStartJob = st₂ := rfl
      rw [hms]
      have htotP1 : st₁.totalPages = st.totalPages := by unfold totalPages; rw [hfp1]
      have hjv₂ : st₂.JobValid := by
        unfold JobValid
        change cur + 1 ≤ st₁.pageSize ∧ st₁.pageSize < st₁.tailCount s ∧
          ∀ u < cur + 1, st₁.tailPhys s u = st₁.totalPages * st₁.pageSize + u
        rw [hps1, htc1, htotP1]
        refine ⟨by omega, hB_lt_r, fun u hu => ?_⟩
        rw [htp_f s u (by omega)]
        rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hu) with rfl | hlt
        · simp
        · have hu_eq := hstaged u hlt
          have hne2 : st.tailPhys s u ≠ st.totalPages * st.pageSize + cur := by omega
          have hne1 : st.tailPhys s u ≠ st.tailPhys s cur := by
            intro heq
            have hidx_u : st.fullPages s * st.pageSize + u < st.virtLen s := by
              unfold virtLen; omega
            have hidx_c : st.fullPages s * st.pageSize + cur < st.virtLen s := by
              unfold virtLen; omega
            have htpu : st.toPhys s (st.fullPages s * st.pageSize + u) = st.tailPhys s u := by
              unfold toPhys; dsimp only; rw [ite_eq_right (by omega), Nat.add_sub_cancel_left]
            have htpc : st.toPhys s (st.fullPages s * st.pageSize + cur) = st.tailPhys s cur := by
              unfold toPhys; dsimp only; rw [ite_eq_right (by omega), Nat.add_sub_cancel_left]
            obtain ⟨_, hie⟩ := hv.toPhys_inj hidx_u hidx_c (by rw [htpu, htpc, heq])
            omega
          rw [ite_eq_right hne1, ite_eq_right hne2, hu_eq]
      have hp_b := hd.pot_bound; have hs_b := hd.side_bound; have hsl := hd.slack_le
      rw [hj, ite_eq_right (by rintro ⟨⟩)] at hp_b
      simp only [remTicks, hj] at hp_b
      simp only [ActiveSideBound, hj, remTicks] at hs_b
      have hphi₂ : st₂.phi = st.phi := by unfold phi; dsimp only [st₂]; rw [hps1, hfp1, htc1]
      have hd₂ : DriftInv st₂ (slack - 1) := by
        refine ⟨hv1.with_job _, hps1 ▸ hB32, hjv₂, by omega, ?_, ?_⟩
        · rw [ite_eq_right (by rintro ⟨⟩)]
          change 16 * st₂.phi + (st₁.pageSize + 1 - (cur + 1)) ≤ 28 * st₁.pageSize + (slack - 1)
          rw [hphi₂, hps1]
          omega
        · unfold ActiveSideBound remTicks
          dsimp only [st₂]
          rw [hps1, htc1]
          omega
      have hvl₂ : st₂.virtLen = st.virtLen := by
        ext side; unfold virtLen; dsimp only [st₂]; rw [hps1, hfp1, htc1]
      have hti₂ : st₂.totalItems = st.totalItems := by unfold totalItems; rw [hvl₂]
      refine ⟨hd₂, hps1, hvl₂, hti₂, hsw_len, hsw_lt, fun arr side idx hidx => ?_⟩
      have htp_eq : st₂.toPhys side idx = st₁.toPhys side idx := by
        unfold toPhys effPage; dsimp only [st₂]; rw [hj1, hj]; rfl
      unfold virtAt; rw [htp_eq]; exact hvirt_sw arr side idx hidx
    · rw [ite_eq_right hcur]
      dsimp only
      obtain ⟨hv1, hphi1, hvl1, hti1, htp1⟩ := tickOne_promote_commit hd hj hcur
      have hd_ms := maybeStartJob_driftInv hv1 hB32 rfl hphi1
      obtain ⟨hps_m, _, _, hvl_m, hti_m⟩ := maybeStartJob_meta _
      refine ⟨hd_ms.mono (Nat.zero_le _) (by have := hd.slack_le; omega), hps_m,
        hvl_m.trans hvl1, hti_m.trans hti1, Nat.zero_le 1, by simp,
        fun arr side idx hidx => ?_⟩
      simp only [applySwaps_nil, virtAt, maybeStartJob_toPhys, htp1 side idx hidx]
  | demoteSwap s cur =>
    dsimp only
    by_cases hcur : cur < st.pageSize
    · rw [ite_eq_left hcur]
      dsimp only
      have hjv := hd.jobValid; unfold JobValid at hjv; rw [hj] at hjv
      obtain ⟨_, hq_pos, hP_lt⟩ := hjv
      set P_dem := st.pageOf s (st.fullPages s - 1) with hPd_def
      set P_last := st.totalPages - 1 with hPl_def
      set st₂ : PagePairState := { st with job := .demoteSwap s (cur + 1) }
      have hms : st₂.maybeStartJob = st₂ := rfl
      rw [hms]
      have hp_b := hd.pot_bound; have hs_b := hd.side_bound; have hsl := hd.slack_le
      rw [hj, ite_eq_right (by rintro ⟨⟩)] at hp_b
      simp only [remTicks, hj] at hp_b
      simp only [ActiveSideBound, hj, remTicks] at hs_b
      have hjv₂ : st₂.JobValid := by
        unfold JobValid
        dsimp only [st₂]
        exact ⟨by omega, hq_pos, hP_lt⟩
      have hd₂ : DriftInv st₂ (slack - 1) := by
        refine ⟨hv.with_job _, hB32, hjv₂, by omega, ?_, ?_⟩
        · rw [ite_eq_right (by rintro ⟨⟩)]
          change 16 * st.phi + (2 * st.pageSize + 2 - (cur + 1)) ≤ 28 * st.pageSize + (slack - 1)
          omega
        · unfold ActiveSideBound remTicks
          dsimp only [st₂]
          omega
      have hQ_pos : 0 < st.totalPages := by unfold totalPages; cases s <;> omega
      have hPd_hi : P_dem * st.pageSize + cur < st.totalPages * st.pageSize := by
        have h1 : (P_dem + 1) * st.pageSize ≤ st.totalPages * st.pageSize :=
          Nat.mul_le_mul_right st.pageSize (by omega)
        rw [Nat.add_mul, one_mul] at h1; omega
      have hPl_hi : P_last * st.pageSize + cur < st.totalPages * st.pageSize := by
        have h1 : (P_last + 1) * st.pageSize ≤ st.totalPages * st.pageSize :=
          Nat.mul_le_mul_right st.pageSize (by omega)
        rw [Nat.add_mul, one_mul] at h1; omega
      have htot_ge : st.totalPages * st.pageSize ≤ st.totalItems := by
        rw [st.totalItems_eq]; omega
      refine ⟨hd₂, rfl, rfl, rfl, le_rfl, ?_, fun arr side idx _ => ?_⟩
      · intro sw hsw; simp only [List.mem_singleton] at hsw; subst hsw
        exact ⟨hPd_hi.trans_le htot_ge, hPl_hi.trans_le htot_ge⟩
      · simp only [applySwaps_cons, applySwaps_nil, virtAt]
        unfold toPhys
        dsimp only [st₂]
        split_ifs with hlt
        · set P := st.pageOf side (idx / st.pageSize)
          set u := idx % st.pageSize
          by_cases hu_eq : u = cur
          · have heff2 : st₂.effPage P u =
                if P = P_dem then P_last else if P = P_last then P_dem else P := by
              unfold effPage
              change (if u < cur + 1 ∧ 0 < st.fullPages s then
                if P = P_dem then P_last else if P = P_last then P_dem else P else P) = _
              rw [hu_eq, ite_eq_left ⟨Nat.lt_succ_self cur, hq_pos⟩]
            have heff0 : st.effPage P u = P := by
              unfold effPage; rw [hj]; dsimp only
              rw [hu_eq, ite_eq_right (fun h => Nat.lt_irrefl cur h.1)]
            rw [heff2, heff0, hu_eq]
            by_cases h1 : P = P_dem
            · rw [ite_eq_left h1, h1]; exact PhysSwap.apply_p₂ _ arr
            · rw [ite_eq_right h1]
              by_cases h2 : P = P_last
              · rw [ite_eq_left h2, h2]; exact PhysSwap.apply_p₁ _ arr
              · rw [ite_eq_right h2]
                have hne1 : P * st.pageSize + cur ≠ P_dem * st.pageSize + cur := fun h =>
                  h1 (Nat.eq_of_mul_eq_mul_right hB (by omega))
                have hne2 : P * st.pageSize + cur ≠ P_last * st.pageSize + cur := fun h =>
                  h2 (Nat.eq_of_mul_eq_mul_right hB (by omega))
                exact PhysSwap.apply_of_ne _ arr hne1 hne2
          · have heff_eq : st₂.effPage P u = st.effPage P u := by
              unfold effPage; rw [hj]
              change (if u < cur + 1 ∧ 0 < st.fullPages s then
                if P = P_dem then P_last else if P = P_last then P_dem else P else P) =
                (if u < cur ∧ 0 < st.fullPages s then
                if P = P_dem then P_last else if P = P_last then P_dem else P else P)
              have hiff : (u < cur + 1 ∧ 0 < st.fullPages s) ↔ (u < cur ∧ 0 < st.fullPages s) :=
                ⟨fun ⟨h1, h2⟩ => ⟨by omega, h2⟩, fun ⟨h1, h2⟩ => ⟨by omega, h2⟩⟩
              by_cases hc : u < cur ∧ 0 < st.fullPages s
              · rw [ite_eq_left (hiff.mpr hc), ite_eq_left hc]
              · rw [ite_eq_right (mt hiff.mp hc), ite_eq_right hc]
            rw [heff_eq]
            have hu_lt : u < st.pageSize := Nat.mod_lt idx hB
            have hne1 : st.effPage P u * st.pageSize + u ≠ P_dem * st.pageSize + cur := by
              intro h
              have hm := congrArg (· % st.pageSize) h
              rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hu_lt,
                Nat.add_comm (P_dem * st.pageSize), Nat.add_mul_mod_self_right,
                Nat.mod_eq_of_lt hcur] at hm
              exact hu_eq hm
            have hne2 : st.effPage P u * st.pageSize + u ≠ P_last * st.pageSize + cur := by
              intro h
              have hm := congrArg (· % st.pageSize) h
              rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hu_lt,
                Nat.add_comm (P_last * st.pageSize), Nat.add_mul_mod_self_right,
                Nat.mod_eq_of_lt hcur] at hm
              exact hu_eq hm
            exact PhysSwap.apply_of_ne _ arr hne1 hne2
        · have hge : st.totalPages * st.pageSize ≤
              st.tailPhys side (idx - st.fullPages side * st.pageSize) :=
            le_physOfRes _ _ _
          exact PhysSwap.apply_of_ne _ arr
            (Nat.ne_of_gt (hPd_hi.trans_le hge))
            (Nat.ne_of_gt (hPl_hi.trans_le hge))
    · rw [ite_eq_right hcur]
      dsimp only
      obtain ⟨hd1, hvl1, hti1, htp1⟩ := tickOne_demoteSwap_commit hd hj hcur
      refine ⟨hd1, rfl, hvl1, hti1, Nat.zero_le 1, by simp, fun arr side idx hidx => ?_⟩
      simp only [applySwaps_nil, virtAt, maybeStartJob_toPhys, htp1 side idx hidx]
  | demoteBuild s cur =>
    dsimp only
    by_cases hcur : cur < st.pageSize
    · rw [ite_eq_left hcur]
      dsimp only
      have hjv := hd.jobValid; unfold JobValid at hjv; rw [hj] at hjv
      obtain ⟨_, hq_pos, hp_last, htc_3B, hts_7B, hstaged⟩ := hjv
      have hQ_pos : 0 < st.totalPages := by unfold totalPages; cases s <;> omega
      set k_cur := (st.tailHead s + 3 * st.pageSize + cur) % (4 * st.pageSize) with hk_def
      set res_cur := ((st.totalPages - 1) * st.pageSize + cur) % (8 * st.pageSize) with hr_def
      set st₁ : PagePairState :=
        { st with
          tailRes := set2 st.tailRes s k_cur res_cur
          tailOwnerSide := Function.update st.tailOwnerSide res_cur s
          tailOwnerRing := Function.update st.tailOwnerRing res_cur k_cur
          job := .demoteBuild s (cur + 1) }
      have hms : st₁.maybeStartJob = st₁ := rfl
      rw [hms]
      have hk_ne_live : ∀ t < st.tailCount s, st.ringSlot s t ≠ k_cur := by
        intro t ht heq
        have h1 := ringIdxOfSlot_mod (head := st.tailHead s) hB (by omega : t < 4 * st.pageSize)
        have h2 := ringIdxOfSlot_mod (head := st.tailHead s) hB
          (by omega : 3 * st.pageSize + cur < 4 * st.pageSize)
        change ringIdxOfSlot (st.tailHead s) st.pageSize (st.ringSlot s t) = t at h1
        have heq' : st.ringSlot s t =
            (st.tailHead s + (3 * st.pageSize + cur)) % (4 * st.pageSize) := by
          rw [heq, hk_def, Nat.add_assoc]
        rw [heq', h2] at h1
        omega
      have hQB : st.totalPages * st.pageSize =
          (st.totalPages - 1) * st.pageSize + st.pageSize := by
        calc st.totalPages * st.pageSize
            = (st.totalPages - 1 + 1) * st.pageSize := by rw [Nat.sub_add_cancel hQ_pos]
          _ = (st.totalPages - 1) * st.pageSize + st.pageSize := by ring
      have hres_ne_live : ∀ p, st.totalPages * st.pageSize ≤ p → p < st.totalItems →
          p % (8 * st.pageSize) ≠ res_cur := by
        intro p hplo hphi_p heq
        have htot_hi : st.totalItems ≤ (st.totalPages - 1) * st.pageSize + 8 * st.pageSize := by
          have hti := st.totalItems_eq; have hts := hv.tailSum_lt; omega
        have h_eq := mod_inj_of_range (M := 8 * st.pageSize)
          (L := (st.totalPages - 1) * st.pageSize) (by positivity)
          (by omega) (by omega) (Nat.le_add_right _ _) (by omega) (heq.trans hr_def)
        omega
      have htp₁_eq : ∀ side t, t < st.tailCount side →
          st₁.tailPhys side t = st.tailPhys side t := by
        intro side t ht
        have hc : ¬(side = s ∧ st.ringSlot side t = k_cur) := by
          rintro ⟨rfl, hr⟩; exact hk_ne_live t ht hr
        change physOfRes (st.totalPages * st.pageSize) st.pageSize
          (set2 st.tailRes s k_cur res_cur side (st.ringSlot side t)) = _
        rw [set2_of_ne _ _ _ _ _ _ hc]
        rfl
      have hv₁ : st₁.Valid := by
        refine ⟨hB, hv.tailCount_lt, hv.tailSum_lt, hv.tailHead_lt, hv.page_lt, hv.owner_pageOf,
          hv.pageOf_owner, ?_, ?_, ?_, ?_⟩
        · intro side t ht
          have hc : ¬(side = s ∧ st.ringSlot side t = k_cur) := by
            rintro ⟨rfl, hr⟩; exact hk_ne_live t ht hr
          change set2 st.tailRes s k_cur res_cur side (st.ringSlot side t) < 8 * st.pageSize
          rw [set2_of_ne _ _ _ _ _ _ hc]; exact hv.tailRes_lt side t ht
        · intro side t ht; rw [htp₁_eq side t ht]; exact hv.tail_lt side t ht
        · intro side t ht
          have hc : ¬(side = s ∧ st.ringSlot side t = k_cur) := by
            rintro ⟨rfl, hr⟩; exact hk_ne_live t ht hr
          have hp_lo : st.totalPages * st.pageSize ≤ st.tailPhys side t := le_physOfRes _ _ _
          have hp_hi : st.tailPhys side t < st.totalItems := hv.tail_lt side t ht
          have hmod := mod_physOfRes (base := st.totalPages * st.pageSize)
            (hv.tailRes_lt side t ht)
          change st.tailPhys side t % (8 * st.pageSize) = _ at hmod
          have hnr : st.tailRes side (st.ringSlot side t) ≠ res_cur := by
            rw [← hmod]; exact hres_ne_live _ hp_lo hp_hi
          change (let res := set2 st.tailRes s k_cur res_cur side (st.ringSlot side t);
            Function.update st.tailOwnerSide res_cur s res = side ∧
            Function.update st.tailOwnerRing res_cur k_cur res = st.ringSlot side t)
          rw [set2_of_ne _ _ _ _ _ _ hc]
          dsimp only
          rw [Function.update_of_ne hnr, Function.update_of_ne hnr]
          exact hv.owner_tail side t ht
        · intro p hplo hphi_p
          have hnr : p % (8 * st.pageSize) ≠ res_cur := hres_ne_live p hplo hphi_p
          obtain ⟨hkp, htp, htpp⟩ := hv.tail_owner p hplo hphi_p
          change (let side := Function.update st.tailOwnerSide res_cur s (p % (8 * st.pageSize));
            let k := Function.update st.tailOwnerRing res_cur k_cur (p % (8 * st.pageSize));
            let t := ringIdxOfSlot (st.tailHead side) st.pageSize k;
            k < 4 * st.pageSize ∧ t < st.tailCount side ∧ st₁.tailPhys side t = p)
          rw [Function.update_of_ne hnr, Function.update_of_ne hnr]
          refine ⟨hkp, htp, ?_⟩
          rw [htp₁_eq _ _ htp, htpp]
      have hjv₁ : st₁.JobValid := by
        unfold JobValid
        change cur + 1 ≤ st.pageSize ∧ 0 < st.fullPages s ∧
          st.pageOf s (st.fullPages s - 1) = st.totalPages - 1 ∧
          st.tailCount s < 3 * st.pageSize ∧
          st.tailCount false + st.tailCount true ≤ 7 * st.pageSize ∧
          ∀ u < cur + 1,
            let k := (st.tailHead s + 3 * st.pageSize + u) % (4 * st.pageSize)
            let res := ((st.totalPages - 1) * st.pageSize + u) % (8 * st.pageSize)
            set2 st.tailRes s k_cur res_cur s k = res ∧
            Function.update st.tailOwnerSide res_cur s res = s ∧
            Function.update st.tailOwnerRing res_cur k_cur res = k
        refine ⟨by omega, hq_pos, hp_last, htc_3B, hts_7B, fun u hu => ?_⟩
        dsimp only
        rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hu) with rfl | hlt
        · rw [← hk_def, ← hr_def]
          exact ⟨set2_self .., Function.update_self .., Function.update_self ..⟩
        · obtain ⟨h1, h2, h3⟩ := hstaged u hlt
          have hku_ne : (st.tailHead s + 3 * st.pageSize + u) % (4 * st.pageSize) ≠ k_cur := by
            intro heq
            have r1 := ringIdxOfSlot_mod (head := st.tailHead s) hB
              (by omega : 3 * st.pageSize + u < 4 * st.pageSize)
            have r2 := ringIdxOfSlot_mod (head := st.tailHead s) hB
              (by omega : 3 * st.pageSize + cur < 4 * st.pageSize)
            have heq' : (st.tailHead s + (3 * st.pageSize + u)) % (4 * st.pageSize) =
                (st.tailHead s + (3 * st.pageSize + cur)) % (4 * st.pageSize) := by
              rw [← Nat.add_assoc, heq, hk_def, Nat.add_assoc]
            rw [heq', r2] at r1; omega
          have hru_ne : ((st.totalPages - 1) * st.pageSize + u) % (8 * st.pageSize) ≠ res_cur := by
            intro heq
            have h_eq := mod_inj_of_range (M := 8 * st.pageSize)
              (L := (st.totalPages - 1) * st.pageSize) (by positivity)
              (Nat.le_add_right _ _) (by omega) (Nat.le_add_right _ _) (by omega)
              (heq.trans hr_def)
            omega
          refine ⟨?_, ?_, ?_⟩
          · rw [set2_of_ne _ _ _ _ _ _ (fun h => hku_ne h.2)]; exact h1
          · rw [Function.update_of_ne hru_ne]; exact h2
          · rw [Function.update_of_ne hru_ne]; exact h3
      have hp_b := hd.pot_bound; have hs_b := hd.side_bound; have hsl := hd.slack_le
      rw [hj, ite_eq_right (by rintro ⟨⟩)] at hp_b
      simp only [remTicks, hj] at hp_b
      simp only [ActiveSideBound, hj, remTicks] at hs_b
      have hd₁ : DriftInv st₁ (slack - 1) := by
        refine ⟨hv₁, hB32, hjv₁, by omega, ?_, ?_⟩
        · rw [ite_eq_right (by rintro ⟨⟩)]
          change 16 * st.phi + (st.pageSize + 1 - (cur + 1)) ≤ 28 * st.pageSize + (slack - 1)
          omega
        · unfold ActiveSideBound remTicks
          dsimp only [st₁]
          omega
      refine ⟨hd₁, rfl, rfl, rfl, Nat.zero_le 1, by simp, fun arr side idx hidx => ?_⟩
      simp only [applySwaps_nil, virtAt]
      unfold toPhys
      dsimp only
      rw [show st₁.pageSize = st.pageSize from rfl, show st₁.fullPages = st.fullPages from rfl]
      split_ifs with hlt
      · have heff1 : st₁.effPage (st₁.pageOf side (idx / st.pageSize)) (idx % st.pageSize) =
            st.pageOf side (idx / st.pageSize) := rfl
        have heff0 : st.effPage (st.pageOf side (idx / st.pageSize)) (idx % st.pageSize) =
            st.pageOf side (idx / st.pageSize) := by simp [effPage, hj]
        rw [heff1, heff0]
      · have ht_lt : idx - st.fullPages side * st.pageSize < st.tailCount side := by
          unfold virtLen at hidx; omega
        rw [htp₁_eq side _ ht_lt]
    · rw [ite_eq_right hcur]
      dsimp only
      obtain ⟨hv1, hphi1, hvl1, hti1, htp1⟩ := tickOne_demoteBuild_commit hd hj hcur
      have hd_ms := maybeStartJob_driftInv hv1 hB32 rfl hphi1
      obtain ⟨hps_m, _, _, hvl_m, hti_m⟩ := maybeStartJob_meta _
      refine ⟨hd_ms.mono (Nat.zero_le _) (by have := hd.slack_le; omega), hps_m,
        hvl_m.trans hvl1, hti_m.trans hti1, Nat.zero_le 1, by simp,
        fun arr side idx hidx => ?_⟩
      simp only [applySwaps_nil, virtAt, maybeStartJob_toPhys, htp1 side idx hidx]

/-- Single background `tick` preserves `WellBalanced`, emits `≤ 1` physical swap in
`[0, st.totalItems)`, and preserves every virtual coordinate `virtAt`. -/
theorem tick_spec {st : PagePairState} (hw : st.WellBalanced) :
    let res := st.tick
    let st' := res.1
    let sws := res.2
    st'.WellBalanced ∧
    st'.pageSize = st.pageSize ∧
    st'.virtLen = st.virtLen ∧
    st'.totalItems = st.totalItems ∧
    sws.length ≤ 1 ∧
    (∀ sw ∈ sws, sw.p₁ < st.totalItems ∧ sw.p₂ < st.totalItems) ∧
    (∀ {α : Type*} (arr : ℕ → α) (side : Bool) (idx : ℕ), idx < st.virtLen side →
      st'.virtAt (applySwaps sws arr) side idx = st.virtAt arr side idx) := by
  obtain ⟨hd', hps, hvl, hti, hlen, hsw, hvirt⟩ := tick_driftInv hw.toDriftInv
  exact ⟨hd'.toWellBalanced, hps, hvl, hti, hlen, hsw, hvirt⟩

private theorem runTicks_driftInv (k : ℕ) {st : PagePairState} {slack : ℕ}
    (hd : DriftInv st slack) :
    let res := runTicks k st
    let st' := res.1
    let sws := res.2
    DriftInv st' (slack - k) ∧
    st'.pageSize = st.pageSize ∧
    st'.virtLen = st.virtLen ∧
    st'.totalItems = st.totalItems ∧
    sws.length ≤ k ∧
    (∀ sw ∈ sws, sw.p₁ < st.totalItems ∧ sw.p₂ < st.totalItems) ∧
    (∀ {α : Type*} (arr : ℕ → α) (side : Bool) (idx : ℕ), idx < st.virtLen side →
      st'.virtAt (applySwaps sws arr) side idx = st.virtAt arr side idx) := by
  induction k generalizing st slack with
  | zero =>
    exact ⟨hd, rfl, rfl, rfl, le_rfl, by simp [runTicks], fun _ _ _ _ => rfl⟩
  | succ k ih =>
    dsimp only [runTicks]
    obtain ⟨hd₁, hps₁, hvl₁, hti₁, hlen₁, hsw₁, hvirt₁⟩ := tick_driftInv hd
    obtain ⟨hd₂, hps₂, hvl₂, hti₂, hlen₂, hsw₂, hvirt₂⟩ := ih hd₁
    rw [Nat.sub_sub, Nat.add_comm 1 k] at hd₂
    refine ⟨hd₂, hps₂.trans hps₁, hvl₂.trans hvl₁, hti₂.trans hti₁,
      by rw [List.length_append]; omega, ?_, fun arr side idx hidx => ?_⟩
    · intro sw hsw
      rcases List.mem_append.mp hsw with h1 | h2
      · exact hsw₁ sw h1
      · rw [hti₁] at hsw₂; exact hsw₂ sw h2
    · rw [applySwaps_append, hvirt₂ _ side idx (hvl₁ ▸ hidx), hvirt₁ arr side idx hidx]

/-- Running `k` background ticks preserves `WellBalanced` and emits `≤ k` swaps in
`[0, st.totalItems)`. -/
theorem runTicks_spec (k : ℕ) {st : PagePairState} (hw : st.WellBalanced) :
    let res := runTicks k st
    let st' := res.1
    let sws := res.2
    st'.WellBalanced ∧
    st'.pageSize = st.pageSize ∧
    st'.virtLen = st.virtLen ∧
    st'.totalItems = st.totalItems ∧
    sws.length ≤ k ∧
    (∀ sw ∈ sws, sw.p₁ < st.totalItems ∧ sw.p₂ < st.totalItems) ∧
    (∀ {α : Type*} (arr : ℕ → α) (side : Bool) (idx : ℕ), idx < st.virtLen side →
      st'.virtAt (applySwaps sws arr) side idx = st.virtAt arr side idx) := by
  obtain ⟨hd', hps, hvl, hti, hlen, hsw, hvirt⟩ := runTicks_driftInv k hw.toDriftInv
  rw [Nat.zero_sub] at hd'
  exact ⟨hd'.toWellBalanced, hps, hvl, hti, hlen, hsw, hvirt⟩

theorem rawAppend_driftInv {st : PagePairState} (hw : st.WellBalanced) (side : Bool) :
    let st_r := st.rawAppend side
    DriftInv st_r.maybeStartJob 16 ∧
    st_r.virtLen side = st.virtLen side + 1 ∧
    (∀ s ≠ side, st_r.virtLen s = st.virtLen s) ∧
    st_r.totalItems = st.totalItems + 1 ∧
    st_r.tailPhys side (st.tailCount side) = st.totalItems ∧
    (∀ s t, t < st.tailCount s → st_r.tailPhys s t = st.tailPhys s t) := by
  intro st_r
  have hv := hw.valid
  have hB32 := hw.pageSize_ge
  have hB := hv.pageSize_pos
  have htc_le := hw.tailCount_le side
  have hts_le := hw.tailSum_le
  have hr_add_lt : st.tailCount side + 1 < 4 * st.pageSize := by omega
  have hts_add_lt : st_r.tailCount false + st_r.tailCount true < 8 * st.pageSize := by
    dsimp only [st_r, rawAppend]; cases side <;> simp <;> omega
  have hvl_r_side : st_r.virtLen side = st.virtLen side + 1 := by
    dsimp only [st_r, rawAppend, virtLen]; rw [Function.update_self]; omega
  have hvl_r_other : ∀ s ≠ side, st_r.virtLen s = st.virtLen s := fun s hs => by
    dsimp only [st_r, rawAppend, virtLen]; rw [Function.update_of_ne hs]
  have hti_r : st_r.totalItems = st.totalItems + 1 := by
    dsimp only [totalItems]; cases side
    · rw [hvl_r_side, hvl_r_other true (by decide)]; omega
    · rw [hvl_r_side, hvl_r_other false (by decide)]; omega
  have hk_ne_old : ∀ t < st.tailCount side,
      st.ringSlot side t ≠ st.ringSlot side (st.tailCount side) := by
    intro t ht heq
    have r1 := ringIdxOfSlot_mod (head := st.tailHead side) hB (by omega : t < 4 * st.pageSize)
    have r2 := ringIdxOfSlot_mod (head := st.tailHead side) hB
      (by omega : st.tailCount side < 4 * st.pageSize)
    change ringIdxOfSlot (st.tailHead side) st.pageSize (st.ringSlot side t) = t at r1
    change ringIdxOfSlot (st.tailHead side) st.pageSize
      (st.ringSlot side (st.tailCount side)) = st.tailCount side at r2
    rw [heq, r2] at r1; omega
  have htot_lo : st.totalPages * st.pageSize ≤ st.totalItems := by
    rw [st.totalItems_eq]; omega
  have htot_hi8 : st.totalItems < st.totalPages * st.pageSize + 8 * st.pageSize := by
    rw [st.totalItems_eq]; omega
  have hres_ne_old : ∀ p, st.totalPages * st.pageSize ≤ p → p < st.totalItems →
      p % (8 * st.pageSize) ≠ st.totalItems % (8 * st.pageSize) := by
    intro p hplo hphi_p heq
    have := mod_inj_of_range (by positivity : 0 < 8 * st.pageSize) hplo
      (hphi_p.trans htot_hi8) htot_lo htot_hi8 heq
    omega
  have htp_r_old : ∀ s t, t < st.tailCount s → st_r.tailPhys s t = st.tailPhys s t := by
    intro s t ht
    have hc : ¬(s = side ∧ st.ringSlot s t = st.ringSlot side (st.tailCount side)) := by
      rintro ⟨rfl, hr⟩; exact hk_ne_old t ht hr
    change physOfRes (st.totalPages * st.pageSize) st.pageSize
      (set2 st.tailRes side (st.ringSlot side (st.tailCount side))
        (st.totalItems % (8 * st.pageSize)) s (st.ringSlot s t)) = _
    rw [set2_of_ne _ _ _ _ _ _ hc]
    rfl
  have htp_r_new : st_r.tailPhys side (st.tailCount side) = st.totalItems := by
    change physOfRes (st.totalPages * st.pageSize) st.pageSize
      (set2 st.tailRes side (st.ringSlot side (st.tailCount side))
        (st.totalItems % (8 * st.pageSize)) side (st.ringSlot side (st.tailCount side))) = _
    rw [set2_self]
    exact physOfRes_mod hB htot_lo htot_hi8
  have hv_r : st_r.Valid := by
    refine ⟨hB, ?_, hts_add_lt, hv.tailHead_lt, hv.page_lt, hv.owner_pageOf, hv.pageOf_owner,
      ?_, ?_, ?_, ?_⟩
    · intro s; dsimp only [st_r, rawAppend]
      by_cases hs : s = side
      · subst hs; rw [Function.update_self]; exact hr_add_lt
      · rw [Function.update_of_ne hs]; exact hv.tailCount_lt s
    · intro s t ht
      change set2 st.tailRes side (st.ringSlot side (st.tailCount side))
        (st.totalItems % (8 * st.pageSize)) s (st.ringSlot s t) < 8 * st.pageSize
      by_cases hc : s = side ∧ t = st.tailCount side
      · obtain ⟨hse, hte⟩ := hc; subst hse; subst hte
        rw [set2_self]; exact Nat.mod_lt _ (by positivity)
      · have ht' : t < st.tailCount s := by
          dsimp only [st_r, rawAppend] at ht
          by_cases hs : s = side
          · subst hs; rw [Function.update_self] at ht
            have hne : t ≠ st.tailCount s := fun h => hc ⟨rfl, h⟩
            omega
          · rwa [Function.update_of_ne hs] at ht
        have hc' : ¬(s = side ∧ st.ringSlot s t = st.ringSlot side (st.tailCount side)) := by
          rintro ⟨rfl, hr⟩; exact hk_ne_old t ht' hr
        rw [set2_of_ne _ _ _ _ _ _ hc']; exact hv.tailRes_lt s t ht'
    · intro s t ht; rw [hti_r]
      by_cases hc : s = side ∧ t = st.tailCount side
      · obtain ⟨hse, hte⟩ := hc; subst hse; subst hte
        rw [htp_r_new]; exact Nat.lt_succ_self _
      · have ht' : t < st.tailCount s := by
          dsimp only [st_r, rawAppend] at ht
          by_cases hs : s = side
          · subst hs; rw [Function.update_self] at ht
            have hne : t ≠ st.tailCount s := fun h => hc ⟨rfl, h⟩
            omega
          · rwa [Function.update_of_ne hs] at ht
        rw [htp_r_old s t ht']; exact (hv.tail_lt s t ht').trans (Nat.lt_succ_self _)
    · intro s t ht
      rw [show st_r.ringSlot s t = st.ringSlot s t from rfl]
      by_cases hc : s = side ∧ t = st.tailCount side
      · obtain ⟨hse, hte⟩ := hc; subst hse; subst hte
        dsimp only [st_r, rawAppend]
        rw [set2_self]
        exact ⟨Function.update_self .., Function.update_self ..⟩
      · have ht' : t < st.tailCount s := by
          dsimp only [st_r, rawAppend] at ht
          by_cases hs : s = side
          · subst hs; rw [Function.update_self] at ht
            have hne : t ≠ st.tailCount s := fun h => hc ⟨rfl, h⟩
            omega
          · rwa [Function.update_of_ne hs] at ht
        have hc' : ¬(s = side ∧ st.ringSlot s t = st.ringSlot side (st.tailCount side)) := by
          rintro ⟨rfl, hr⟩; exact hk_ne_old t ht' hr
        have hp_lo : st.totalPages * st.pageSize ≤ st.tailPhys s t := le_physOfRes _ _ _
        have hp_hi : st.tailPhys s t < st.totalItems := hv.tail_lt s t ht'
        have hmod := mod_physOfRes (base := st.totalPages * st.pageSize) (hv.tailRes_lt s t ht')
        change st.tailPhys s t % (8 * st.pageSize) = _ at hmod
        have hnr : st.tailRes s (st.ringSlot s t) ≠ st.totalItems % (8 * st.pageSize) := by
          rw [← hmod]; exact hres_ne_old _ hp_lo hp_hi
        dsimp only [st_r, rawAppend]
        rw [set2_of_ne _ _ _ _ _ _ hc', Function.update_of_ne hnr, Function.update_of_ne hnr]
        exact hv.owner_tail s t ht'
    · intro p hplo hphi_p; rw [hti_r] at hphi_p
      change st.totalPages * st.pageSize ≤ p at hplo
      by_cases hp_eq : p = st.totalItems
      · subst hp_eq
        dsimp only [st_r, rawAppend]
        rw [Function.update_self, Function.update_self, Function.update_self]
        have hri : ringIdxOfSlot (st.tailHead side) st.pageSize
            (st.ringSlot side (st.tailCount side)) = st.tailCount side :=
          ringIdxOfSlot_mod hB (by omega)
        rw [hri]
        exact ⟨Nat.mod_lt _ (by positivity), Nat.lt_succ_self _, htp_r_new⟩
      · have hp_lt : p < st.totalItems := by omega
        have hnr : p % (8 * st.pageSize) ≠ st.totalItems % (8 * st.pageSize) :=
          hres_ne_old p hplo hp_lt
        obtain ⟨hkp, htp, htpp⟩ := hv.tail_owner p hplo hp_lt
        dsimp only [st_r, rawAppend]
        rw [Function.update_of_ne hnr, Function.update_of_ne hnr]
        refine ⟨hkp, ?_, ?_⟩
        · by_cases hs : st.tailOwnerSide (p % (8 * st.pageSize)) = side
          · rw [hs, Function.update_self]; rw [hs] at htp; omega
          · rwa [Function.update_of_ne hs]
        · exact (htp_r_old _ _ htp).trans htpp
  have hphi_r : st_r.phi ≤ st.phi + 1 := by
    unfold phi dev; dsimp only [st_r, rawAppend]
    cases side <;> simp only [Function.update_self,
      Function.update_of_ne (by decide : false ≠ true),
      Function.update_of_ne (by decide : true ≠ false)] <;> split_ifs <;> omega
  refine ⟨?_, hvl_r_side, hvl_r_other, hti_r, htp_r_new, htp_r_old⟩
  cases hj : st.job with
  | idle =>
    have hp := hw.pot_bound; simp only [hj, ↓reduceIte] at hp
    have hj_r : st_r.job = .idle := hj
    have hps_r : st_r.pageSize = st.pageSize := rfl
    exact (maybeStartJob_driftInv hv_r hB32 hj_r (by rw [hps_r]; omega)).mono
      (Nat.zero_le 16) le_rfl
  | promote s cur =>
    have hj_r : st_r.job = .promote s cur := hj
    have hms : st_r.maybeStartJob = st_r := by simp [maybeStartJob, hj_r]
    rw [hms]
    have hjv := hw.jobValid; unfold JobValid at hjv; rw [hj] at hjv
    obtain ⟨hc_le, hBr, hst_u⟩ := hjv
    have hp := hw.pot_bound; rw [hj, ite_eq_right (by rintro ⟨⟩)] at hp
    simp only [remTicks, hj] at hp
    have hs_b := hw.side_bound; simp only [ActiveSideBound, hj, remTicks] at hs_b
    refine ⟨hv_r, hB32, ?_, le_rfl, ?_, ?_⟩
    · unfold JobValid; rw [hj_r]
      change cur ≤ st.pageSize ∧ st.pageSize < st_r.tailCount s ∧
        ∀ u < cur, st_r.tailPhys s u = st.totalPages * st.pageSize + u
      refine ⟨hc_le, ?_, fun u hu => ?_⟩
      · dsimp only [st_r, rawAppend]
        by_cases hss : s = side
        · subst hss; rw [Function.update_self]; omega
        · rwa [Function.update_of_ne hss]
      · rw [htp_r_old s u (by omega)]; exact hst_u u hu
    · rw [hj_r, ite_eq_right (by rintro ⟨⟩)]; simp only [remTicks, hj_r]
      change 16 * st_r.phi + (st.pageSize + 1 - cur) ≤ 28 * st.pageSize + 16; omega
    · simp only [ActiveSideBound, hj_r, remTicks]
      dsimp only [st_r, rawAppend]
      by_cases hss : s = side
      · subst hss; rw [Function.update_self]; omega
      · rw [Function.update_of_ne hss]; omega
  | demoteSwap s cur =>
    have hj_r : st_r.job = .demoteSwap s cur := hj
    have hms : st_r.maybeStartJob = st_r := by simp [maybeStartJob, hj_r]
    rw [hms]
    have hjv := hw.jobValid; unfold JobValid at hjv; rw [hj] at hjv
    have hp := hw.pot_bound; rw [hj, ite_eq_right (by rintro ⟨⟩)] at hp
    simp only [remTicks, hj] at hp
    have hs_b := hw.side_bound; simp only [ActiveSideBound, hj, remTicks] at hs_b
    refine ⟨hv_r, hB32, ?_, le_rfl, ?_, ?_⟩
    · unfold JobValid; rw [hj_r]; exact hjv
    · rw [hj_r, ite_eq_right (by rintro ⟨⟩)]; simp only [remTicks, hj_r]
      change 16 * st_r.phi + (2 * st.pageSize + 2 - cur) ≤ 28 * st.pageSize + 16; omega
    · simp only [ActiveSideBound, hj_r, remTicks]
      dsimp only [st_r, rawAppend]
      by_cases hss : s = side
      · subst hss; rw [Function.update_self]; omega
      · rw [Function.update_of_ne hss]; omega
  | demoteBuild s cur =>
    have hj_r : st_r.job = .demoteBuild s cur := hj
    have hms : st_r.maybeStartJob = st_r := by simp [maybeStartJob, hj_r]
    rw [hms]
    have hjv := hw.jobValid; unfold JobValid at hjv; rw [hj] at hjv
    obtain ⟨hc_le, hq_pos, hp_last, _, _, hst_u⟩ := hjv
    have hp := hw.pot_bound; rw [hj, ite_eq_right (by rintro ⟨⟩)] at hp
    simp only [remTicks, hj] at hp
    have hs_b := hw.side_bound; simp only [ActiveSideBound, hj, remTicks] at hs_b
    have hQ_pos : 0 < st.totalPages := by unfold totalPages; cases s <;> omega
    have htc_s2B : st.tailCount s < 2 * st.pageSize := by omega
    refine ⟨hv_r, hB32, ?_, le_rfl, ?_, ?_⟩
    · unfold JobValid; rw [hj_r]
      change cur ≤ st.pageSize ∧ 0 < st.fullPages s ∧
        st.pageOf s (st.fullPages s - 1) = st.totalPages - 1 ∧
        st_r.tailCount s < 3 * st.pageSize ∧
        st_r.tailCount false + st_r.tailCount true ≤ 7 * st.pageSize ∧
        ∀ u < cur,
          let k := (st.tailHead s + 3 * st.pageSize + u) % (4 * st.pageSize)
          let res := ((st.totalPages - 1) * st.pageSize + u) % (8 * st.pageSize)
          set2 st.tailRes side (st.ringSlot side (st.tailCount side))
            (st.totalItems % (8 * st.pageSize)) s k = res ∧
          Function.update st.tailOwnerSide (st.totalItems % (8 * st.pageSize)) side res = s ∧
          Function.update st.tailOwnerRing (st.totalItems % (8 * st.pageSize))
            (st.ringSlot side (st.tailCount side)) res = k
      refine ⟨hc_le, hq_pos, hp_last, ?_, ?_, fun u hu => ?_⟩
      · dsimp only [st_r, rawAppend]
        by_cases hss : s = side
        · subst hss; rw [Function.update_self]; omega
        · rw [Function.update_of_ne hss]; omega
      · dsimp only [st_r, rawAppend]; cases side <;> simp <;> omega
      · dsimp only
        obtain ⟨h1, h2, h3⟩ := hst_u u hu
        have hc_ne : ¬(s = side ∧ (st.tailHead s + 3 * st.pageSize + u) % (4 * st.pageSize) =
            st.ringSlot side (st.tailCount side)) := by
          rintro ⟨rfl, hr⟩
          have r1 := ringIdxOfSlot_mod (head := st.tailHead s) hB
            (by omega : 3 * st.pageSize + u < 4 * st.pageSize)
          have r2 := ringIdxOfSlot_mod (head := st.tailHead s) hB
            (by omega : st.tailCount s < 4 * st.pageSize)
          rw [Nat.add_assoc] at hr
          change (st.tailHead s + (3 * st.pageSize + u)) % (4 * st.pageSize) =
            st.ringSlot s (st.tailCount s) at hr
          change ringIdxOfSlot (st.tailHead s) st.pageSize (st.ringSlot s (st.tailCount s)) =
            st.tailCount s at r2
          rw [hr, r2] at r1; omega
        have hQB : st.totalPages * st.pageSize =
            (st.totalPages - 1) * st.pageSize + st.pageSize := by
          calc st.totalPages * st.pageSize
              = (st.totalPages - 1 + 1) * st.pageSize := by rw [Nat.sub_add_cancel hQ_pos]
            _ = (st.totalPages - 1) * st.pageSize + st.pageSize := by ring
        have htot_hi7 : st.totalItems < (st.totalPages - 1) * st.pageSize + 8 * st.pageSize := by
          have hti := st.totalItems_eq; omega
        have hru_ne : ((st.totalPages - 1) * st.pageSize + u) % (8 * st.pageSize) ≠
            st.totalItems % (8 * st.pageSize) := by
          intro heq
          have := mod_inj_of_range (by positivity : 0 < 8 * st.pageSize)
            (Nat.le_add_right _ _) (by omega) (by omega) htot_hi7 heq
          omega
        exact ⟨by rw [set2_of_ne _ _ _ _ _ _ hc_ne]; exact h1,
          by rw [Function.update_of_ne hru_ne]; exact h2,
          by rw [Function.update_of_ne hru_ne]; exact h3⟩
    · rw [hj_r, ite_eq_right (by rintro ⟨⟩)]; simp only [remTicks, hj_r]
      change 16 * st_r.phi + (st.pageSize + 1 - cur) ≤ 28 * st.pageSize + 16; omega
    · simp only [ActiveSideBound, hj_r, remTicks]
      dsimp only [st_r, rawAppend]
      by_cases hss : s = side
      · subst hss; rw [Function.update_self]; omega
      · rw [Function.update_of_ne hss]; omega

/-- **`stepAppend` Preservation & Virtual-Array Specification (`stepAppend_spec`).**
Appending at `(side, st.virtLen side)` on a `WellBalanced` state preserves `WellBalanced`, emits at
most `16` swaps strictly inside `[0, st.totalItems + 1)`, maps `(side, st.virtLen side)` to the new
item originally placed at physical slot `st.totalItems`, and leaves every existing entry `(s, idx)`
unchanged across both virtual arrays. -/
theorem stepAppend_spec {st : PagePairState} (hw : st.WellBalanced) (side : Bool) :
    let res := st.stepAppend side
    let st' := res.1
    let sws := res.2
    st'.WellBalanced ∧
    st'.pageSize = st.pageSize ∧
    st'.virtLen side = st.virtLen side + 1 ∧
    (∀ s ≠ side, st'.virtLen s = st.virtLen s) ∧
    st'.totalItems = st.totalItems + 1 ∧
    sws.length ≤ 16 ∧
    (∀ sw ∈ sws, sw.p₁ < st.totalItems + 1 ∧ sw.p₂ < st.totalItems + 1) ∧
    (∀ {α : Type*} (arr : ℕ → α) (s : Bool) (idx : ℕ), idx < st'.virtLen s →
      st'.virtAt (applySwaps sws arr) s idx =
        if s = side ∧ idx = st.virtLen side then arr st.totalItems
        else st.virtAt arr s idx) := by
  set st_r := st.rawAppend side
  obtain ⟨hd_ms, hvl_r_side, hvl_r_other, hti_r, htp_r_new, htp_r_old⟩ :=
    rawAppend_driftInv hw side
  dsimp only [stepAppend]
  obtain ⟨hps_m, _, _, hvl_m, hti_m⟩ := maybeStartJob_meta st_r
  obtain ⟨hd', hps', hvl', hti', hlen', hsw', hvirt'⟩ := runTicks_driftInv 16 hd_ms
  rw [Nat.sub_self] at hd'
  have hvl_fin : (runTicks 16 st_r.maybeStartJob).1.virtLen = st_r.virtLen := hvl'.trans hvl_m
  have hti_fin : (runTicks 16 st_r.maybeStartJob).1.totalItems = st.totalItems + 1 :=
    (hti'.trans hti_m).trans hti_r
  refine ⟨hd'.toWellBalanced, hps'.trans hps_m, ?_, ?_, hti_fin, hlen', ?_,
    fun arr s idx hidx => ?_⟩
  · rw [hvl_fin]; exact hvl_r_side
  · intro s hs; rw [hvl_fin]; exact hvl_r_other s hs
  · intro sw hsw; rw [hti_m, hti_r] at hsw'; exact hsw' sw hsw
  · rw [hvl_fin] at hidx
    rw [hvirt' arr s idx (hvl_m.symm ▸ hidx)]
    unfold virtAt
    rw [maybeStartJob_toPhys]
    by_cases hc : s = side ∧ idx = st.virtLen side
    · obtain ⟨hse, hie⟩ := hc; subst hse; subst hie
      rw [ite_eq_left ⟨rfl, rfl⟩]
      unfold toPhys; dsimp only [st_r, rawAppend]
      have hlt_f : ¬(st.virtLen s < st.fullPages s * st.pageSize) := by unfold virtLen; omega
      rw [ite_eq_right hlt_f]
      have hsub : st.virtLen s - st.fullPages s * st.pageSize = st.tailCount s := by
        unfold virtLen; omega
      rw [hsub]; exact congrArg arr htp_r_new
    · rw [ite_eq_right hc]
      have hidx_old : idx < st.virtLen s := by
        by_cases hs : s = side
        · subst hs; rw [hvl_r_side] at hidx
          have hne : idx ≠ st.virtLen s := fun h => hc ⟨rfl, h⟩
          omega
        · rwa [hvl_r_other s hs] at hidx
      congr 1
      unfold toPhys; dsimp only [st_r, rawAppend]
      split_ifs with hlt
      · rfl
      · have ht_lt : idx - st.fullPages s * st.pageSize < st.tailCount s := by
          unfold virtLen at hidx_old; omega
        exact htp_r_old s _ ht_lt

private theorem rawPopBack_valid {st : PagePairState} (hw : st.WellBalanced) {side : Bool}
    (hpos : 0 < st.virtLen side) :
    let res := st.rawPopBack side
    let st_r := res.1
    let sws₀ := res.2
    st_r.Valid ∧
    st_r.phi ≤ st.phi + 1 ∧
    st_r.pageSize = st.pageSize ∧
    st_r.virtLen side = st.virtLen side - 1 ∧
    (∀ s ≠ side, st_r.virtLen s = st.virtLen s) ∧
    st_r.totalItems = st.totalItems - 1 ∧
    sws₀.length ≤ 1 ∧
    (∀ sw ∈ sws₀, sw.p₁ < st.totalItems ∧ sw.p₂ < st.totalItems) ∧
    (∀ {α : Type*} (arr : ℕ → α) (s : Bool) (idx : ℕ), idx < st_r.virtLen s →
      st_r.virtAt (applySwaps sws₀ arr) s idx = st.virtAt arr s idx) := by
  dsimp only [rawPopBack]
  have hv := hw.valid
  have hB := hv.pageSize_pos
  have hr_pos : 0 < st.tailCount side := hw.tailCount_pos_of_virtLen hpos
  have htot_pos : 0 < st.totalItems := by unfold totalItems; cases side <;> omega
  have hp1_lo : st.totalPages * st.pageSize ≤ st.tailPhys side (st.tailCount side - 1) :=
    le_physOfRes _ _ _
  have hp1_hi : st.tailPhys side (st.tailCount side - 1) < st.totalItems :=
    hv.tail_lt side (st.tailCount side - 1) (by omega)
  have hp2_lo : st.totalPages * st.pageSize ≤ st.totalItems - 1 := by
    rw [st.totalItems_eq]; cases side <;> omega
  have hp2_hi : st.totalItems - 1 < st.totalItems := by omega
  obtain ⟨hv1, hps1, hfp1, htc1, _, _, _, _, _, hsw0_len, hsw0_lt, htp_f, hvirt0⟩ :=
    swapTailSlots_spec hv hp1_lo hp1_hi hp2_lo hp2_hi
  set st₁ := (st.swapTailSlots (st.tailPhys side (st.tailCount side - 1)) (st.totalItems - 1)).1
  set sws₀ := (st.swapTailSlots (st.tailPhys side (st.tailCount side - 1)) (st.totalItems - 1)).2
  set st_r : PagePairState :=
    { st₁ with tailCount := Function.update st₁.tailCount side (st.tailCount side - 1) }
  have hti1 : st₁.totalItems = st.totalItems := by unfold totalItems virtLen; rw [hps1, hfp1, htc1]
  have htp_last : st₁.tailPhys side (st.tailCount side - 1) = st.totalItems - 1 := by
    rw [htp_f side (st.tailCount side - 1) (by omega), ite_eq_left rfl]
  have hvl_r_side : st_r.virtLen side = st.virtLen side - 1 := by
    unfold virtLen; dsimp only [st_r]; rw [hps1, hfp1, Function.update_self]; omega
  have hvl_r_other : ∀ s ≠ side, st_r.virtLen s = st.virtLen s := fun s hs => by
    unfold virtLen; dsimp only [st_r]; rw [hps1, hfp1, Function.update_of_ne hs, htc1]
  have hti_r : st_r.totalItems = st.totalItems - 1 := by
    unfold totalItems; cases side
    · rw [hvl_r_side, hvl_r_other true (by decide)]; unfold totalItems at htot_pos; omega
    · rw [hvl_r_side, hvl_r_other false (by decide)]; unfold totalItems at htot_pos; omega
  have htp_r_eq : ∀ s t, st_r.tailPhys s t = st₁.tailPhys s t := fun _ _ => rfl
  have hv_r : st_r.Valid := by
    refine ⟨hps1 ▸ hB, ?_, ?_, hv1.tailHead_lt, hv1.page_lt, hv1.owner_pageOf, hv1.pageOf_owner,
      ?_, ?_, ?_, ?_⟩
    · intro s; dsimp only [st_r]; rw [hps1]
      by_cases hs : s = side
      · subst hs; rw [Function.update_self]; have := hv.tailCount_lt s; omega
      · rw [Function.update_of_ne hs, htc1]; exact hv.tailCount_lt s
    · dsimp only [st_r]; rw [hps1, htc1]; have := hv.tailSum_lt; cases side <;> simp <;> omega
    · intro s t ht
      have ht1 : t < st₁.tailCount s := by
        dsimp only [st_r] at ht; by_cases hs : s = side
        · subst hs; rw [Function.update_self] at ht; rw [htc1]; omega
        · rwa [Function.update_of_ne hs] at ht
      exact hv1.tailRes_lt s t ht1
    · intro s t ht; rw [hti_r, htp_r_eq]
      have ht1 : t < st₁.tailCount s := by
        dsimp only [st_r] at ht; by_cases hs : s = side
        · subst hs; rw [Function.update_self] at ht; rw [htc1]; omega
        · rwa [Function.update_of_ne hs] at ht
      have hp_lt := hv1.tail_lt s t ht1; rw [hti1] at hp_lt
      have hp_ne : st₁.tailPhys s t ≠ st.totalItems - 1 := by
        intro heq
        rw [← htp_last] at heq
        have hidx1 : st₁.fullPages s * st₁.pageSize + t < st₁.virtLen s := by
          unfold virtLen; omega
        have hidx2 : st₁.fullPages side * st₁.pageSize + (st.tailCount side - 1) <
            st₁.virtLen side := by
          unfold virtLen; rw [htc1]; omega
        have htp1 : st₁.toPhys s (st₁.fullPages s * st₁.pageSize + t) = st₁.tailPhys s t := by
          unfold toPhys; dsimp only; rw [ite_eq_right (by omega), Nat.add_sub_cancel_left]
        have htp2 : st₁.toPhys side (st₁.fullPages side * st₁.pageSize + (st.tailCount side - 1)) =
            st₁.tailPhys side (st.tailCount side - 1) := by
          unfold toPhys; dsimp only; rw [ite_eq_right (by omega), Nat.add_sub_cancel_left]
        obtain ⟨hse, hie⟩ := hv1.toPhys_inj hidx1 hidx2 (by rw [htp1, htp2, heq])
        subst hse
        dsimp only [st_r] at ht; rw [Function.update_self] at ht; omega
      omega
    · intro s t ht
      have ht1 : t < st₁.tailCount s := by
        dsimp only [st_r] at ht; by_cases hs : s = side
        · subst hs; rw [Function.update_self] at ht; rw [htc1]; omega
        · rwa [Function.update_of_ne hs] at ht
      exact hv1.owner_tail s t ht1
    · intro p hplo hphi_p; rw [hti_r] at hphi_p
      have hplo1 : st₁.totalPages * st₁.pageSize ≤ p := hplo
      have hp_lt1 : p < st₁.totalItems := by rw [hti1]; omega
      obtain ⟨hkp, htp, htpp⟩ := hv1.tail_owner p hplo1 hp_lt1
      dsimp only [st_r]
      refine ⟨hkp, ?_, htpp⟩
      by_cases hs : st₁.tailOwnerSide (p % (8 * st₁.pageSize)) = side
      · rw [hs, Function.update_self]
        rw [hs] at htp htpp
        have hne_t : ringIdxOfSlot (st₁.tailHead side) st₁.pageSize
            (st₁.tailOwnerRing (p % (8 * st₁.pageSize))) ≠ st.tailCount side - 1 := by
          intro heq; rw [heq, htp_last] at htpp; omega
        rw [htc1] at htp; omega
      · rwa [Function.update_of_ne hs]
  have hphi_r : st_r.phi ≤ st.phi + 1 := by
    unfold phi dev; dsimp only [st_r]; rw [hps1, hfp1, htc1]
    cases side <;> simp only [Function.update_self,
      Function.update_of_ne (by decide : false ≠ true),
      Function.update_of_ne (by decide : true ≠ false)] <;> split_ifs <;> omega
  refine ⟨hv_r, hphi_r, hps1, hvl_r_side, hvl_r_other, hti_r, hsw0_len, hsw0_lt,
    fun arr s idx hidx => ?_⟩
  have hidx_old : idx < st.virtLen s := by
    by_cases hs : s = side
    · subst hs; rw [hvl_r_side] at hidx; omega
    · rwa [hvl_r_other s hs] at hidx
  have htp_r1 : st_r.toPhys s idx = st₁.toPhys s idx := by
    unfold toPhys effPage; dsimp only [st_r]; rfl
  unfold virtAt
  rw [htp_r1]
  exact hvirt0 arr s idx hidx_old

private theorem popTail_driftInv_of_swap {st st₁ : PagePairState} {side : Bool}
    (hw : st.WellBalanced) (hpos : 0 < st.virtLen side)
    (hv_r : ({ st₁ with
        tailCount := Function.update st₁.tailCount side (st.tailCount side - 1) } :
      PagePairState).Valid)
    (hphi_r : ({ st₁ with
        tailCount := Function.update st₁.tailCount side (st.tailCount side - 1) } :
      PagePairState).phi ≤ st.phi + 1)
    (hps1 : st₁.pageSize = st.pageSize)
    (hfp1 : st₁.fullPages = st.fullPages)
    (htc1 : st₁.tailCount = st.tailCount)
    (hth1 : st₁.tailHead = st.tailHead)
    (hpo1 : st₁.pageOf = st.pageOf)
    (hj1 : st₁.job = st.job)
    (htp_f : ∀ s t, t < st.tailCount s →
      st₁.tailPhys s t =
        if st.tailPhys s t = st.tailPhys side (st.tailCount side - 1) then st.totalItems - 1
        else if st.tailPhys s t = st.totalItems - 1 then st.tailPhys side (st.tailCount side - 1)
        else st.tailPhys s t)
    (hst_pres : ∀ {s : Bool} {u : ℕ},
      (∀ t < st.tailCount s, st.ringSlot s t ≠
        (st.tailHead s + 3 * st.pageSize + u) % (4 * st.pageSize)) →
      (∀ p, st.totalPages * st.pageSize ≤ p → p < st.totalItems →
        p % (8 * st.pageSize) ≠ ((st.totalPages - 1) * st.pageSize + u) % (8 * st.pageSize)) →
      st₁.tailRes s ((st.tailHead s + 3 * st.pageSize + u) % (4 * st.pageSize)) =
        st.tailRes s ((st.tailHead s + 3 * st.pageSize + u) % (4 * st.pageSize)) ∧
      st₁.tailOwnerSide (((st.totalPages - 1) * st.pageSize + u) % (8 * st.pageSize)) =
        st.tailOwnerSide (((st.totalPages - 1) * st.pageSize + u) % (8 * st.pageSize)) ∧
      st₁.tailOwnerRing (((st.totalPages - 1) * st.pageSize + u) % (8 * st.pageSize)) =
        st.tailOwnerRing (((st.totalPages - 1) * st.pageSize + u) % (8 * st.pageSize))) :
    DriftInv ({ st₁ with
        tailCount := Function.update st₁.tailCount side (st.tailCount side - 1) } :
      PagePairState).maybeStartJob 16 := by
  set st_r : PagePairState :=
    { st₁ with tailCount := Function.update st₁.tailCount side (st.tailCount side - 1) }
  have hv := hw.valid
  have hB32 := hw.pageSize_ge
  have hB := hv.pageSize_pos
  have hr_pos : 0 < st.tailCount side := hw.tailCount_pos_of_virtLen hpos
  have hpsr : st_r.pageSize = st.pageSize := hps1
  have htotPr : st_r.totalPages = st.totalPages := by
    unfold totalPages; dsimp only [st_r]; rw [hfp1]
  cases hj : st.job with
  | idle =>
    have hp := hw.pot_bound; simp only [hj, ↓reduceIte] at hp
    have hj_r : st_r.job = .idle := by dsimp only [st_r]; rw [hj1, hj]
    exact (maybeStartJob_driftInv hv_r (hpsr ▸ hB32) hj_r (by rw [hpsr]; omega)).mono
      (Nat.zero_le 16) le_rfl
  | promote s cur =>
    have hj_r : st_r.job = .promote s cur := by dsimp only [st_r]; rw [hj1, hj]
    have hms : st_r.maybeStartJob = st_r := by simp [maybeStartJob, hj_r]
    rw [hms]
    have hjv := hw.jobValid; unfold JobValid at hjv; rw [hj] at hjv
    obtain ⟨hc_le, _, hst_u⟩ := hjv
    have hp := hw.pot_bound; rw [hj, ite_eq_right (by rintro ⟨⟩)] at hp
    simp only [remTicks, hj] at hp
    have hs_b := hw.side_bound; simp only [ActiveSideBound, hj, remTicks] at hs_b
    have htc_s2B : 2 * st.pageSize < st.tailCount s := by omega
    have htot_gt_QB : st.totalPages * st.pageSize + st.pageSize < st.totalItems - 1 := by
      rw [st.totalItems_eq]; cases s <;> omega
    refine ⟨hv_r, hpsr ▸ hB32, ?_, le_rfl, ?_, ?_⟩
    · unfold JobValid; rw [hj_r]
      change cur ≤ st_r.pageSize ∧ st_r.pageSize < st_r.tailCount s ∧
        ∀ u < cur, st₁.tailPhys s u = st_r.totalPages * st_r.pageSize + u
      rw [hpsr, htotPr]
      refine ⟨hc_le, ?_, fun u hu => ?_⟩
      · dsimp only [st_r]
        by_cases hss : s = side
        · subst hss; rw [Function.update_self]; omega
        · rw [Function.update_of_ne hss, htc1]; omega
      · rw [htp_f s u (by omega)]
        have hu_eq := hst_u u hu
        have hne2 : st.tailPhys s u ≠ st.totalItems - 1 := by omega
        have hne1 : st.tailPhys s u ≠ st.tailPhys side (st.tailCount side - 1) := by
          intro heq
          have hidx1 : st.fullPages s * st.pageSize + u < st.virtLen s := by
            unfold virtLen; omega
          have hidx2 : st.fullPages side * st.pageSize + (st.tailCount side - 1) <
              st.virtLen side := by
            unfold virtLen; omega
          have htp1 : st.toPhys s (st.fullPages s * st.pageSize + u) = st.tailPhys s u := by
            unfold toPhys; dsimp only; rw [ite_eq_right (by omega), Nat.add_sub_cancel_left]
          have htp2 : st.toPhys side (st.fullPages side * st.pageSize +
              (st.tailCount side - 1)) = st.tailPhys side (st.tailCount side - 1) := by
            unfold toPhys; dsimp only; rw [ite_eq_right (by omega), Nat.add_sub_cancel_left]
          obtain ⟨hse, hie⟩ := hv.toPhys_inj hidx1 hidx2 (by rw [htp1, htp2, heq])
          subst hse; omega
        rw [ite_eq_right hne1, ite_eq_right hne2, hu_eq]
    · rw [hj_r, ite_eq_right (by rintro ⟨⟩)]
      unfold remTicks; rw [hj_r]; dsimp only; rw [hpsr]
      omega
    · unfold ActiveSideBound remTicks; rw [hj_r]; dsimp only; rw [hpsr]
      dsimp only [st_r]
      by_cases hss : s = side
      · subst hss; rw [Function.update_self]; omega
      · rw [Function.update_of_ne hss, htc1]; omega
  | demoteSwap s cur =>
    have hj_r : st_r.job = .demoteSwap s cur := by dsimp only [st_r]; rw [hj1, hj]
    have hms : st_r.maybeStartJob = st_r := by simp [maybeStartJob, hj_r]
    rw [hms]
    have hjv := hw.jobValid; unfold JobValid at hjv; rw [hj] at hjv
    have hp := hw.pot_bound; rw [hj, ite_eq_right (by rintro ⟨⟩)] at hp
    simp only [remTicks, hj] at hp
    have hs_b := hw.side_bound; simp only [ActiveSideBound, hj, remTicks] at hs_b
    refine ⟨hv_r, hpsr ▸ hB32, ?_, le_rfl, ?_, ?_⟩
    · unfold JobValid; rw [hj_r]
      change cur ≤ st_r.pageSize ∧ 0 < st₁.fullPages s ∧
        st₁.pageOf s (st₁.fullPages s - 1) < st_r.totalPages - 1
      rw [hpsr, hfp1, hpo1, htotPr]
      exact hjv
    · rw [hj_r, ite_eq_right (by rintro ⟨⟩)]
      unfold remTicks; rw [hj_r]; dsimp only; rw [hpsr]
      omega
    · unfold ActiveSideBound remTicks; rw [hj_r]; dsimp only; rw [hpsr]
      dsimp only [st_r]
      by_cases hss : s = side
      · subst hss; rw [Function.update_self]; omega
      · rw [Function.update_of_ne hss, htc1]; omega
  | demoteBuild s cur =>
    have hj_r : st_r.job = .demoteBuild s cur := by dsimp only [st_r]; rw [hj1, hj]
    have hms : st_r.maybeStartJob = st_r := by simp [maybeStartJob, hj_r]
    rw [hms]
    have hjv := hw.jobValid; unfold JobValid at hjv; rw [hj] at hjv
    obtain ⟨hc_le, hq_pos, hp_last, htc_3B, hts_7B, hst_u⟩ := hjv
    have hp := hw.pot_bound; rw [hj, ite_eq_right (by rintro ⟨⟩)] at hp
    simp only [remTicks, hj] at hp
    have hs_b := hw.side_bound; simp only [ActiveSideBound, hj, remTicks] at hs_b
    have hQ_pos : 0 < st.totalPages := by unfold totalPages; cases s <;> omega
    refine ⟨hv_r, hpsr ▸ hB32, ?_, le_rfl, ?_, ?_⟩
    · unfold JobValid; rw [hj_r]
      change cur ≤ st_r.pageSize ∧ 0 < st₁.fullPages s ∧
        st₁.pageOf s (st₁.fullPages s - 1) = st_r.totalPages - 1 ∧
        st_r.tailCount s < 3 * st_r.pageSize ∧
        st_r.tailCount false + st_r.tailCount true ≤ 7 * st_r.pageSize ∧
        ∀ u < cur,
          let k := (st₁.tailHead s + 3 * st_r.pageSize + u) % (4 * st_r.pageSize)
          let res := ((st_r.totalPages - 1) * st_r.pageSize + u) % (8 * st_r.pageSize)
          st₁.tailRes s k = res ∧
          st₁.tailOwnerSide res = s ∧
          st₁.tailOwnerRing res = k
      rw [hpsr, hfp1, hpo1, hth1, htotPr]
      refine ⟨hc_le, hq_pos, hp_last, ?_, ?_, fun u hu => ?_⟩
      · dsimp only [st_r]
        by_cases hss : s = side
        · subst hss; rw [Function.update_self]; omega
        · rw [Function.update_of_ne hss, htc1]; exact htc_3B
      · dsimp only [st_r]; rw [htc1]; cases side <;> simp <;> omega
      · dsimp only
        obtain ⟨h1, h2, h3⟩ := hst_u u hu
        have hk_ne : ∀ t < st.tailCount s, st.ringSlot s t ≠
            (st.tailHead s + 3 * st.pageSize + u) % (4 * st.pageSize) := by
          intro t ht heq
          have r1 := ringIdxOfSlot_mod (head := st.tailHead s) hB
            (by omega : t < 4 * st.pageSize)
          have r2 := ringIdxOfSlot_mod (head := st.tailHead s) hB
            (by omega : 3 * st.pageSize + u < 4 * st.pageSize)
          change ringIdxOfSlot (st.tailHead s) st.pageSize (st.ringSlot s t) = t at r1
          rw [Nat.add_assoc] at heq
          change st.ringSlot s t =
            (st.tailHead s + (3 * st.pageSize + u)) % (4 * st.pageSize) at heq
          rw [heq, r2] at r1; omega
        have hQB : st.totalPages * st.pageSize =
            (st.totalPages - 1) * st.pageSize + st.pageSize := by
          calc st.totalPages * st.pageSize
              = (st.totalPages - 1 + 1) * st.pageSize := by rw [Nat.sub_add_cancel hQ_pos]
            _ = (st.totalPages - 1) * st.pageSize + st.pageSize := by ring
        have htot_hi7 : st.totalItems ≤ (st.totalPages - 1) * st.pageSize + 8 * st.pageSize := by
          rw [st.totalItems_eq, hQB]; have hts := hv.tailSum_lt; omega
        have hres_ne : ∀ p, st.totalPages * st.pageSize ≤ p → p < st.totalItems →
            p % (8 * st.pageSize) ≠ ((st.totalPages - 1) * st.pageSize + u) %
              (8 * st.pageSize) := by
          intro p hplo hphi_p heq
          have := mod_inj_of_range (M := 8 * st.pageSize)
            (L := (st.totalPages - 1) * st.pageSize) (by positivity)
            (by omega) (by omega) (Nat.le_add_right _ _) (by omega) heq
          omega
        obtain ⟨hp1, hp2, hp3⟩ := hst_pres hk_ne hres_ne
        exact ⟨hp1.trans h1, hp2.trans h2, hp3.trans h3⟩
    · rw [hj_r, ite_eq_right (by rintro ⟨⟩)]
      unfold remTicks; rw [hj_r]; dsimp only; rw [hpsr]
      omega
    · unfold ActiveSideBound remTicks; rw [hj_r]; dsimp only; rw [hpsr]
      dsimp only [st_r]
      by_cases hss : s = side
      · subst hss; rw [Function.update_self]; omega
      · rw [Function.update_of_ne hss, htc1]; omega

theorem rawPopBack_driftInv {st : PagePairState} (hw : st.WellBalanced) {side : Bool}
    (hpos : 0 < st.virtLen side) :
    let res := st.rawPopBack side
    let st_r := res.1
    let sws₀ := res.2
    DriftInv st_r.maybeStartJob 16 ∧
    st_r.pageSize = st.pageSize ∧
    st_r.virtLen side = st.virtLen side - 1 ∧
    (∀ s ≠ side, st_r.virtLen s = st.virtLen s) ∧
    st_r.totalItems = st.totalItems - 1 ∧
    sws₀.length ≤ 1 ∧
    (∀ sw ∈ sws₀, sw.p₁ < st.totalItems ∧ sw.p₂ < st.totalItems) ∧
    (∀ {α : Type*} (arr : ℕ → α) (s : Bool) (idx : ℕ), idx < st_r.virtLen s →
      st_r.virtAt (applySwaps sws₀ arr) s idx = st.virtAt arr s idx) := by
  obtain ⟨hv_r, hphi_r, hpsr, hvl_r_side, hvl_r_other, hti_r, hsw0_len, hsw0_lt, hvirt0⟩ :=
    rawPopBack_valid hw hpos
  have hv := hw.valid
  have hr_pos : 0 < st.tailCount side := hw.tailCount_pos_of_virtLen hpos
  have htot_pos : 0 < st.totalItems := by unfold totalItems; cases side <;> omega
  have hp1_lo : st.totalPages * st.pageSize ≤ st.tailPhys side (st.tailCount side - 1) :=
    le_physOfRes _ _ _
  have hp1_hi : st.tailPhys side (st.tailCount side - 1) < st.totalItems :=
    hv.tail_lt side (st.tailCount side - 1) (by omega)
  have hp2_lo : st.totalPages * st.pageSize ≤ st.totalItems - 1 := by
    rw [st.totalItems_eq]; cases side <;> omega
  have hp2_hi : st.totalItems - 1 < st.totalItems := by omega
  obtain ⟨_, hps1, hfp1, htc1, hth1, hpo1, _, _, hj1, _, _, htp_f, _⟩ :=
    swapTailSlots_spec.{0} hv hp1_lo hp1_hi hp2_lo hp2_hi
  have hd_ms := popTail_driftInv_of_swap hw hpos hv_r hphi_r hps1 hfp1 htc1 hth1 hpo1 hj1 htp_f
    (fun hk_ne hres_ne =>
      swapTailSlots_preserves_staged hv hp1_lo hp1_hi hp2_lo hp2_hi hk_ne hres_ne)
  exact ⟨hd_ms, hpsr, hvl_r_side, hvl_r_other, hti_r, hsw0_len, hsw0_lt, hvirt0⟩

private theorem stepPopBack_spec_aux.{u} (k : ℕ) (hk : 16 ≤ k)
    {st : PagePairState} (hw : st.WellBalanced) {side : Bool} (hpos : 0 < st.virtLen side) :
    let res := st.stepPopBackTicks k side
    let st' := res.1
    let sws := res.2
    st'.WellBalanced ∧
    st'.pageSize = st.pageSize ∧
    st'.virtLen side = st.virtLen side - 1 ∧
    (∀ s ≠ side, st'.virtLen s = st.virtLen s) ∧
    st'.totalItems = st.totalItems - 1 ∧
    sws.length ≤ k + 1 ∧
    (∀ sw ∈ sws, sw.p₁ < st.totalItems ∧ sw.p₂ < st.totalItems) ∧
    (∀ {α : Type u} (arr : ℕ → α) (s : Bool) (idx : ℕ), idx < st'.virtLen s →
      st'.virtAt (applySwaps sws arr) s idx = st.virtAt arr s idx) := by
  dsimp only [stepPopBackTicks]
  obtain ⟨hd_ms, hps1, hvl_r_side, hvl_r_other, hti_r, hsw0_len, hsw0_lt, hvirt0⟩ :=
    rawPopBack_driftInv.{u} hw hpos
  obtain ⟨hps_m, _, _, hvl_m, hti_m⟩ := maybeStartJob_meta (st.rawPopBack side).1
  obtain ⟨hd', hps', hvl', hti', hlen', hsw', hvirt'⟩ := runTicks_driftInv.{u} k hd_ms
  rw [Nat.sub_eq_zero_of_le hk] at hd'
  have hvl_fin : (runTicks k (st.rawPopBack side).1.maybeStartJob).1.virtLen =
      (st.rawPopBack side).1.virtLen := hvl'.trans hvl_m
  have hti_fin : (runTicks k (st.rawPopBack side).1.maybeStartJob).1.totalItems =
      st.totalItems - 1 := (hti'.trans hti_m).trans hti_r
  refine ⟨hd'.toWellBalanced, (hps'.trans hps_m).trans hps1, ?_, ?_, hti_fin,
    by rw [List.length_append]; omega, ?_, fun arr s idx hidx => ?_⟩
  · rw [hvl_fin]; exact hvl_r_side
  · intro s hs; rw [hvl_fin]; exact hvl_r_other s hs
  · intro sw hsw
    rcases List.mem_append.mp hsw with h1 | h2
    · exact hsw0_lt sw h1
    · rw [hti_m, hti_r] at hsw'
      obtain ⟨h1', h2'⟩ := hsw' sw h2
      exact ⟨by omega, by omega⟩
  · rw [hvl_fin] at hidx
    rw [applySwaps_append, hvirt' _ s idx (hvl_m.symm ▸ hidx)]
    unfold virtAt
    rw [maybeStartJob_toPhys]
    exact hvirt0 arr s idx hidx

/-- **`stepPopBack` Preservation & Virtual-Array Specification (`stepPopBack_spec`).**
Popping `(side, st.virtLen side - 1)` on a `WellBalanced` state (`0 < st.virtLen side`) preserves
`WellBalanced`, emits at most `17` swaps strictly inside `[0, st.totalItems)`, and preserves every
remaining virtual coordinate `idx < st'.virtLen s` across both arrays. -/
theorem stepPopBack_spec.{u} {st : PagePairState} (hw : st.WellBalanced) {side : Bool}
    (hpos : 0 < st.virtLen side) :
    let res := st.stepPopBack side
    let st' := res.1
    let sws := res.2
    st'.WellBalanced ∧
    st'.pageSize = st.pageSize ∧
    st'.virtLen side = st.virtLen side - 1 ∧
    (∀ s ≠ side, st'.virtLen s = st.virtLen s) ∧
    st'.totalItems = st.totalItems - 1 ∧
    sws.length ≤ 17 ∧
    (∀ sw ∈ sws, sw.p₁ < st.totalItems ∧ sw.p₂ < st.totalItems) ∧
    (∀ {α : Type u} (arr : ℕ → α) (s : Bool) (idx : ℕ), idx < st'.virtLen s →
      st'.virtAt (applySwaps sws arr) s idx = st.virtAt arr s idx) :=
  stepPopBack_spec_aux.{u} 16 le_rfl hw hpos

end PagePairState


/-- **General `1 · OPT` Dual-Epoch Word-Space Theorem (`dualEpochWords_le_optBits_add`).**
Parameterized by an **arbitrary** redundancy function `redFn : ℕ → ℕ` (instantiable to both
`Dynamic.logLogFactor` for SOSA 2024 and `iteratedLog k` for resizable `k`-kick trees):
whenever source metadata words `M_src ≤ (B_src + w - 1) / w + c_src`, destination metadata words
`M_dst ≤ (B_dst + w - 1) / w + c_dst`, and `B_src + B_dst + n_t * w_slot ≤ Dynamic.optBits U V n_t
+ C_red * n_t * redFn n_t`, the entire dual-epoch layout `hdrWords + M_src + M_dst + 4 +
packedWords n_t w_slot w` uses at most `(Dynamic.optBits U V n_t + C_red * n_t * redFn n_t + w - 1)
/ w + (hdrWords + c_src + c_dst + 9)` words—never `2 · OPT`. -/
theorem dualEpochWords_le_optBits_add {hdrWords M_src M_dst B_src B_dst c_src c_dst
    U V w n_t w_slot C_red : ℕ} {redFn : ℕ → ℕ}
    (hsrc : M_src ≤ (B_src + w - 1) / w + c_src)
    (hdst : M_dst ≤ (B_dst + w - 1) / w + c_dst)
    (hbits : B_src + B_dst + n_t * w_slot ≤ Dynamic.optBits U V n_t + C_red * n_t * redFn n_t) :
    hdrWords + M_src + M_dst + 4 + packedWords n_t w_slot w ≤
      (Dynamic.optBits U V n_t + C_red * n_t * redFn n_t + w - 1) / w +
        (hdrWords + c_src + c_dst + 9) := by
  have h12 : ((B_src + w - 1) / w + c_src) + ((B_dst + w - 1) / w + c_dst) ≤
      (B_src + B_dst + w - 1) / w + (c_src + c_dst + 1) := by
    have h := div_add_packedWords_le B_src c_src B_dst 1 w
    unfold packedWords at h
    rw [Nat.mul_one] at h
    omega
  have h123 := div_add_packedWords_le (B_src + B_dst) (c_src + c_dst + 1) n_t w_slot w
  have hdiv : (B_src + B_dst + n_t * w_slot + w - 1) / w ≤
      (Dynamic.optBits U V n_t + C_red * n_t * redFn n_t + w - 1) / w :=
    Nat.div_le_div_right (by omega)
  omega

/-- Specialization of `dualEpochWords_le_optBits_add` to `Dynamic.succinctWords`. -/
theorem dualEpochWords_le_succinctWords {hdrWords M_src M_dst B_src B_dst c_src c_dst
    U V w n_t w_slot C_red : ℕ}
    (hsrc : M_src ≤ (B_src + w - 1) / w + c_src)
    (hdst : M_dst ≤ (B_dst + w - 1) / w + c_dst)
    (hbits : B_src + B_dst + n_t * w_slot ≤
      Dynamic.optBits U V n_t + C_red * n_t * Dynamic.logLogFactor n_t) :
    hdrWords + M_src + M_dst + 4 + packedWords n_t w_slot w ≤
      Dynamic.succinctWords C_red (hdrWords + c_src + c_dst + 9) U V w n_t := by
  unfold Dynamic.succinctWords
  exact dualEpochWords_le_optBits_add (redFn := Dynamic.logLogFactor) hsrc hdst hbits

/-! ## Section 4: Distributional WHP State-Transition Deamortizer (`HighProbStateTransitionImpl`)
-/

universe u v z

/-- Reusable Resizable Word RAM distributional WHP implementation certificate for a functional
`D : StateTransitionSpec` (`[D.HasStepFn stepFn]`):
* Couples the post-prefix machine distribution `ν : PMF (LatentRState Latent r_ds)` to the
  reference state `s = (D.run s₀ pref).1` via a distributional invariant `distInv pref ν`
  (accommodating stored epoch hash seeds sampled during `init` or Phase 1).
* Bounds the slow-path fallback event `(ν.bind μ_step).toOuterMeasure {¬WithinBudget} ≤
  failureProb s o` in expectation over `ν` (so rare bad epoch seeds fall back to certified `1 · OPT`
  `ExecRCodeDist` recovery without sacrificing exactness or `1 · OPT` peak space).
* Lifts automatically via `toHighProbObliviousImpl` to `HighProbObliviousImpl` over
  `D.toObliviousSequenceSpec s₀`. -/
structure HighProbStateTransitionImpl {B : Basis} {r_ds k_init : ℕ}
    (P : SubroutineCode B r_ds k_init)
    (D : DataStructure.StateTransitionSpec.{u, v, z})
    {stepFn : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn stepFn]
    (w base : ℕ) (params : Fin k_init → ℕ) (s₀ : D.State) :
    Type (max u v (z + 1)) where
  /-- Internal latent state type. -/
  Latent : Type z
  /-- State-indexed resting word-footprint upper bound `x.frontier ≤ base + spaceBound s`. -/
  spaceBound : D.State → ℕ
  /-- State-and-operation peak word-footprint bound `y.frontier ≤ base + peakSpaceBound s o`. -/
  peakSpaceBound : D.State → D.Op → ℕ
  /-- Worst-case instruction budget for `P.initCode`. -/
  initSteps : ℕ
  /-- Operation-indexed deterministic worst-case body instruction budget. -/
  worstCaseTime : D.Op → ℕ
  /-- State-and-operation slow-path failure probability bound. -/
  failureProb : D.State → D.Op → ℝ≥0∞
  /-- Pointwise representation invariant `rep s l x` coupling abstract state `s` to `(l, x)`. -/
  rep : D.State → Latent → RData r_ds → Prop
  /-- Distributional invariant on the post-prefix `(latent, data)` law (e.g. uniform epoch hash
  seeds). -/
  distInv : List D.Op → PMF (LatentRState Latent r_ds) → Prop
  /-- Standalone register encoding for argument delivery. -/
  encode : D.Op → Fin r_ds → ℕ
  /-- Output decoder reading typed operation observations from final registers. -/
  decode : (o : D.Op) → (Fin r_ds → ℕ) → Option (D.Result o)
  /-- States satisfying `rep` are `w`-bit word-bounded. -/
  bounded : ∀ {s l x}, rep s l x → x.Bounded w
  /-- States satisfying `rep s l x` satisfy `base ≤ x.frontier ≤ base + spaceBound s` and
  `x.regs P.baseReg = base`. -/
  frontier_le : ∀ {s l x}, rep s l x →
    base ≤ x.frontier ∧ x.frontier ≤ base + spaceBound s ∧ x.regs P.baseReg = base
  /-- Standalone encoded arguments fit in `w`-bit words on admissible operations `D.valid s o`. -/
  arguments_fit : ∀ {s : D.State} (o : D.Op),
    D.valid s o → ∀ i, P.input i = true → Fits w (encode o i)
  /-- Worst-case bounded initialization of `P.initCode` from `x₀.frontier = base` within
  `initSteps` instructions, establishing `distInv [] ν₀` and `rep s₀`. -/
  init_exec : ∀ {x₀ : RData r_ds},
    x₀.Bounded w → x₀.frontier = base → (∀ j, x₀.regs (P.initParams j) = params j) →
    Fits w (base + spaceBound s₀) →
    ∃ ν₀ : PMF (LatentRState Latent r_ds),
      ExecRCodeSteps w P.initCode x₀
        (ν₀.map fun t => ⟨t.data, initSteps, true⟩) (base + spaceBound s₀) ∧
      distInv [] ν₀ ∧
      ∀ t ∈ ν₀.support,
        rep s₀ t.latent t.data ∧ ∀ addr < base, t.data.mem addr = x₀.mem addr
  /-- Single-operation distributional WHP transition from any `ν` satisfying `distInv pref ν`. -/
  step_exec : ∀ (pref : List D.Op) (o : D.Op) (ν : PMF (LatentRState Latent r_ds)),
    let s := (D.run s₀ pref).1
    D.ValidHistory s₀ pref → D.valid s o → Fits w (base + peakSpaceBound s o) →
    distInv pref ν → (∀ t ∈ ν.support, rep s t.latent t.data) →
    ∃ μ_step : LatentRState Latent r_ds → PMF (WhpStepROutcome Latent (D.Result o) r_ds),
      (∀ t ∈ ν.support,
        ExecRCodeSteps w P.code (P.prepare encode o t.data)
          ((μ_step t).map WhpStepROutcome.toCodeOutcome) (base + peakSpaceBound s o) ∧
        ∀ q ∈ (μ_step t).support,
          q.result = (D.stepFn s o).2 ∧
          decode o q.data.regs = some q.result ∧
          rep (D.stepFn s o).1 q.latent q.data ∧
          (∀ addr < base, q.data.mem addr = t.data.mem addr)) ∧
      distInv (pref ++ [o]) (ν.bind fun t => (μ_step t).map fun q => ⟨q.latent, q.data⟩) ∧
      (ν.bind μ_step).toOuterMeasure {q | ¬q.WithinBudget (worstCaseTime o)} ≤ failureProb s o

namespace HighProbStateTransitionImpl

variable {B : Basis} {r_ds k_init w base : ℕ}
  {P : SubroutineCode B r_ds k_init}
  {D : DataStructure.StateTransitionSpec.{u, v, z}}
  {stepFn : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn stepFn]
  {params : Fin k_init → ℕ} {s₀ : D.State}

/-- Project a `WhpSeqROutcome` to its `(latent, data)` pair. -/
private abbrev projLatent {Latent : Type z} (tr : WhpSeqROutcome Latent D.Result r_ds) :
    LatentRState Latent r_ds :=
  ⟨tr.latent, tr.data⟩

/-- Outer-measure union bound across a single `WhpSeqROutcome.appendStep` transition. -/
private theorem outerMeasure_appendStep_le {Latent : Type z} {o : D.Op} {B_op : ℕ}
    (τ : PMF (WhpSeqROutcome Latent D.Result r_ds))
    (μ_step : LatentRState Latent r_ds → PMF (WhpStepROutcome Latent (D.Result o) r_ds)) :
    (τ.bind fun tr => (μ_step (projLatent tr)).map (tr.appendStep o B_op)).toOuterMeasure
        {u | u.allWithinBudget = false} ≤
      τ.toOuterMeasure {tr | tr.allWithinBudget = false} +
        ((τ.map projLatent).bind μ_step).toOuterMeasure {q | ¬q.WithinBudget B_op} := by
  classical
  let τ' := τ.bind fun tr => (μ_step (projLatent tr)).map (tr.appendStep o B_op)
  let S_bad : Set (WhpSeqROutcome Latent D.Result r_ds) := {u | u.allWithinBudget = false}
  let S_prev : Set (WhpSeqROutcome Latent D.Result r_ds) := {tr | tr.allWithinBudget = false}
  let S_step : Set (WhpStepROutcome Latent (D.Result o) r_ds) := {q | ¬q.WithinBudget B_op}
  have h1 : τ'.toOuterMeasure S_bad =
      ∑' tr, τ tr * ∑' q, μ_step (projLatent tr) q *
        S_bad.indicator (fun _ => (1 : ℝ≥0∞)) (tr.appendStep o B_op q) := by
    rw [PMF.toOuterMeasure_apply]
    have hmul : (∑' u, S_bad.indicator τ' u) =
        ∑' u, τ' u * S_bad.indicator (fun _ => (1 : ℝ≥0∞)) u := by
      refine tsum_congr fun u => ?_
      by_cases h : u ∈ S_bad <;> simp [h]
    rw [hmul]
    dsimp only [τ']
    rw [Cslib.Probability.PMF.tsum_bind_mul]
    refine tsum_congr fun tr => congrArg (τ tr * ·) ?_
    rw [Cslib.Probability.PMF.tsum_map_mul]
  have h2 : τ.toOuterMeasure S_prev =
      ∑' tr, τ tr * S_prev.indicator (fun _ => (1 : ℝ≥0∞)) tr := by
    rw [PMF.toOuterMeasure_apply]
    refine tsum_congr fun tr => ?_
    by_cases h : tr ∈ S_prev <;> simp [h]
  have h3 : ((τ.map projLatent).bind μ_step).toOuterMeasure S_step =
      ∑' tr, τ tr * ∑' q, μ_step (projLatent tr) q *
        S_step.indicator (fun _ => (1 : ℝ≥0∞)) q := by
    rw [PMF.toOuterMeasure_apply]
    have hmul : (∑' q, S_step.indicator ((τ.map projLatent).bind μ_step) q) =
        ∑' q, ((τ.map projLatent).bind μ_step) q *
          S_step.indicator (fun _ => (1 : ℝ≥0∞)) q := by
      refine tsum_congr fun q => ?_
      by_cases h : q ∈ S_step <;> simp [h]
    rw [hmul, Cslib.Probability.PMF.tsum_bind_mul, Cslib.Probability.PMF.tsum_map_mul]
  rw [h1, h2, h3, ← Summable.tsum_add CompleteLattice.summable CompleteLattice.summable]
  refine tsum_le_tsum fun tr => ?_
  have hpure : S_prev.indicator (fun _ => (1 : ℝ≥0∞)) tr =
      ∑' q, μ_step (projLatent tr) q * S_prev.indicator (fun _ => (1 : ℝ≥0∞)) tr := by
    rw [ENNReal.tsum_mul_right, (μ_step (projLatent tr)).tsum_coe, one_mul]
  rw [hpure, ← mul_add, ← Summable.tsum_add CompleteLattice.summable CompleteLattice.summable]
  refine mul_le_mul_right (tsum_le_tsum fun q => ?_) (τ tr)
  rw [← mul_add]
  refine mul_le_mul_right ?_ _
  by_cases hprev : tr.allWithinBudget = false
  · have hm : tr ∈ S_prev := hprev
    rw [Set.indicator_of_mem hm]
    by_cases hbad : tr.appendStep o B_op q ∈ S_bad
    · rw [Set.indicator_of_mem hbad]; simp
    · rw [Set.indicator_of_notMem hbad]; simp
  · have htr_ok : tr.allWithinBudget = true := by
      cases h : tr.allWithinBudget <;> simp_all
    rw [Set.indicator_of_notMem (show tr ∉ S_prev from hprev), zero_add]
    by_cases hq_ok : q.WithinBudget B_op
    · obtain ⟨ht_q, hs_q⟩ := hq_ok
      have hnot_bad : tr.appendStep o B_op q ∉ S_bad := by
        dsimp only [S_bad, Set.mem_ofPred_eq, WhpSeqROutcome.appendStep]
        simp [htr_ok, ht_q, hs_q]
      rw [Set.indicator_of_notMem hnot_bad]; exact zero_le
    · have hm_q : q ∈ S_step := hq_ok
      rw [Set.indicator_of_mem hm_q]
      by_cases hbad : tr.appendStep o B_op q ∈ S_bad
      · rw [Set.indicator_of_mem hbad]
      · rw [Set.indicator_of_notMem hbad]; simp

/-- Inductive sequence execution across `remOps` after prefix `prefOps` for
`HighProbStateTransitionImpl`. -/
private theorem steps_exec_aux
    (C : HighProbStateTransitionImpl P D (stepFn := stepFn) w base params s₀)
    (prefOps remOps : List D.Op)
    (τ : PMF (WhpSeqROutcome C.Latent D.Result r_ds))
    (hv_pref : D.ValidHistory s₀ prefOps)
    (hv_rem : D.ValidHistory (D.run s₀ prefOps).1 remOps)
    (hfit_rem : ObliviousPeakFits w base
      (fun p o => C.peakSpaceBound (D.run s₀ p).1 o) prefOps remOps)
    (hd_inv : C.distInv prefOps (τ.map projLatent))
    (hsupp : ∀ tr ∈ τ.support,
      C.rep (D.run s₀ prefOps).1 tr.latent tr.data ∧
      tr.transcript = (D.run s₀ prefOps).2) :
    ∃ τ_final : PMF (WhpSeqROutcome C.Latent D.Result r_ds),
      ExecWhpSteps P (D.toObliviousSequenceSpec s₀) C.Latent w base
        (fun p => C.spaceBound (D.run s₀ p).1)
        (fun p o => C.peakSpaceBound (D.run s₀ p).1 o)
        C.worstCaseTime C.encode C.decode prefOps remOps τ τ_final ∧
      (∀ tr ∈ τ_final.support,
        C.rep (D.run s₀ (prefOps ++ remOps)).1 tr.latent tr.data ∧
        tr.transcript = (D.run s₀ (prefOps ++ remOps)).2) ∧
      τ_final.toOuterMeasure {tr | tr.allWithinBudget = false} ≤
        τ.toOuterMeasure {tr | tr.allWithinBudget = false} +
          totalFailureProb (fun p o => C.failureProb (D.run s₀ p).1 o) prefOps remOps := by
  induction remOps generalizing prefOps τ with
  | nil =>
    refine ⟨τ, ExecWhpSteps.nil (S := D.toObliviousSequenceSpec s₀) prefOps τ, ?_, ?_⟩
    · simpa only [List.append_nil] using hsupp
    · simp
  | cons o ops ih =>
    obtain ⟨hv_o, hv_ops⟩ := hv_rem
    obtain ⟨hfit_o, hfit_ops⟩ := hfit_rem
    have hrep_ν : ∀ t ∈ (τ.map projLatent).support,
        C.rep (D.run s₀ prefOps).1 t.latent t.data := by
      intro t ht; rw [PMF.mem_support_map_iff] at ht; obtain ⟨tr, htr, rfl⟩ := ht
      exact (hsupp tr htr).1
    obtain ⟨μ_step, hstep_all, hd_next, hfail_step⟩ :=
      C.step_exec prefOps o (τ.map projLatent) hv_pref hv_o hfit_o hd_inv hrep_ν
    let τ_next := τ.bind fun tr =>
      (μ_step (projLatent tr)).map (tr.appendStep o (C.worstCaseTime o))
    have hrun_append : D.run s₀ (prefOps ++ [o]) =
        ((D.stepFn (D.run s₀ prefOps).1 o).1,
          (D.run s₀ prefOps).2 ++ [⟨o, (D.stepFn (D.run s₀ prefOps).1 o).2⟩]) := by
      rw [D.run_append, D.run_cons, D.run_nil]
    have hv_pref' : D.ValidHistory s₀ (prefOps ++ [o]) :=
      (D.validHistory_append s₀ prefOps [o]).mpr ⟨hv_pref, hv_o, trivial⟩
    have hv_ops' : D.ValidHistory (D.run s₀ (prefOps ++ [o])).1 ops := by
      rw [hrun_append]; exact hv_ops
    have hd_next' : C.distInv (prefOps ++ [o]) (τ_next.map projLatent) := by
      have heq_map : τ_next.map projLatent =
          (τ.map projLatent).bind fun t => (μ_step t).map fun q => ⟨q.latent, q.data⟩ := by
        dsimp only [τ_next]
        rw [PMF.map_bind, PMF.bind_map]
        refine congrArg (τ.bind ·) (funext fun tr => ?_)
        rw [PMF.map_comp]
        rfl
      rwa [heq_map]
    have hsupp_next : ∀ u ∈ τ_next.support,
        C.rep (D.run s₀ (prefOps ++ [o])).1 u.latent u.data ∧
        u.transcript = (D.run s₀ (prefOps ++ [o])).2 := by
      intro u hu
      dsimp only [τ_next] at hu
      rw [PMF.mem_support_bind_iff] at hu; obtain ⟨tr, htr, hmap⟩ := hu
      rw [PMF.mem_support_map_iff] at hmap; obtain ⟨q, hq, rfl⟩ := hmap
      have ht_mem : projLatent tr ∈ (τ.map projLatent).support :=
        (PMF.mem_support_map_iff _ _ _).mpr ⟨tr, htr, rfl⟩
      obtain ⟨_, hq_spec⟩ := hstep_all (projLatent tr) ht_mem
      obtain ⟨hq_res, _, hq_rep, _⟩ := hq_spec q hq
      obtain ⟨_, htr_lbl⟩ := hsupp tr htr
      rw [hrun_append]
      exact ⟨hq_rep, by simp [WhpSeqROutcome.appendStep, htr_lbl, hq_res]⟩
    obtain ⟨τ_final, hex_rest, hsupp_fin, hfail_rest⟩ :=
      ih (prefOps ++ [o]) τ_next hv_pref' hv_ops' hfit_ops hd_next' hsupp_next
    refine ⟨τ_final, .cons (μ_step := fun tr => μ_step (projLatent tr)) (fun tr htr => ?_) hex_rest,
      by simpa only [List.append_assoc, List.singleton_append] using hsupp_fin, ?_⟩
    · obtain ⟨hrep_tr, _⟩ := hsupp tr htr
      have hbdd_tr : tr.data.Bounded w := C.bounded hrep_tr
      have hfit_arg := C.arguments_fit o hv_o
      have ht_mem : projLatent tr ∈ (τ.map projLatent).support :=
        (PMF.mem_support_map_iff _ _ _).mpr ⟨tr, htr, rfl⟩
      obtain ⟨he_tr, hq_spec⟩ := hstep_all (projLatent tr) ht_mem
      refine ⟨hbdd_tr, hfit_arg, P.prepare_bounded hbdd_tr hfit_arg, he_tr, fun q hq => ?_⟩
      obtain ⟨_, hdec_q, hrep_q, hcaller_q⟩ := hq_spec q hq
      have hrep_q' : C.rep (D.run s₀ (prefOps ++ [o])).1 q.latent q.data := by
        rw [hrun_append]; exact hrep_q
      exact ⟨C.bounded hrep_q', C.frontier_le hrep_q', hdec_q, hcaller_q⟩
    · have hub := outerMeasure_appendStep_le (B_op := C.worstCaseTime o) τ μ_step
      calc τ_final.toOuterMeasure {tr | tr.allWithinBudget = false}
          ≤ τ_next.toOuterMeasure {tr | tr.allWithinBudget = false} +
              totalFailureProb (fun p o' => C.failureProb (D.run s₀ p).1 o')
                (prefOps ++ [o]) ops := hfail_rest
        _ ≤ (τ.toOuterMeasure {tr | tr.allWithinBudget = false} +
              ((τ.map projLatent).bind μ_step).toOuterMeasure
                {q | ¬q.WithinBudget (C.worstCaseTime o)}) +
              totalFailureProb (fun p o' => C.failureProb (D.run s₀ p).1 o')
                (prefOps ++ [o]) ops := add_le_add hub le_rfl
        _ ≤ (τ.toOuterMeasure {tr | tr.allWithinBudget = false} +
              C.failureProb (D.run s₀ prefOps).1 o) +
              totalFailureProb (fun p o' => C.failureProb (D.run s₀ p).1 o')
                (prefOps ++ [o]) ops := add_le_add (add_le_add le_rfl hfail_step) le_rfl
        _ = τ.toOuterMeasure {tr | tr.allWithinBudget = false} +
              totalFailureProb (fun p o' => C.failureProb (D.run s₀ p).1 o')
                prefOps (o :: ops) := by simp [add_assoc]

/-- **Canonical Embedding into `HighProbObliviousImpl` (`toHighProbObliviousImpl`).**
Packages any `HighProbStateTransitionImpl` over a functional `StateTransitionSpec` into a
`HighProbObliviousImpl` realizing `D.toObliviousSequenceSpec s₀` with trajectory-indexed resting
bound `pref ↦ C.spaceBound (D.run s₀ pref).1`, peak bound `(pref, o) ↦ C.peakSpaceBound
(D.run s₀ pref).1 o`, operation-indexed `worstCaseTime`, and per-step `failureProb`. -/
@[expose] noncomputable def toHighProbObliviousImpl
    (C : HighProbStateTransitionImpl P D (stepFn := stepFn) w base params s₀) :
    HighProbObliviousImpl.{v, z, z} P (D.toObliviousSequenceSpec s₀) w base params where
  Latent := C.Latent
  spaceBound := fun pref => C.spaceBound (D.run s₀ pref).1
  peakSpaceBound := fun pref o => C.peakSpaceBound (D.run s₀ pref).1 o
  initSteps := C.initSteps
  worstCaseTime := C.worstCaseTime
  failureProb := fun pref o => C.failureProb (D.run s₀ pref).1 o
  initInv ν₀ := C.distInv [] ν₀ ∧ ∀ t ∈ ν₀.support, C.rep s₀ t.latent t.data
  validOp _ o := ∃ s, D.valid s o
  encode := C.encode
  decode := C.decode
  bounded hinv t ht := C.bounded (hinv.2 t ht)
  frontier_le hinv t ht := by
    simpa only [D.run_nil] using C.frontier_le (hinv.2 t ht)
  arguments_fit := fun o ⟨_, hv⟩ => C.arguments_fit o hv
  init_exec hx₀ hfr hpar hfit := by
    rw [D.run_nil] at hfit
    obtain ⟨ν₀, he, hd_inv, hsupp⟩ := C.init_exec hx₀ hfr hpar hfit
    refine ⟨ν₀, ?_, ⟨hd_inv, fun t ht => (hsupp t ht).1⟩, fun t ht => (hsupp t ht).2⟩
    simpa only [D.run_nil] using he
  steps_exec ops ν₀ hv hfit_ops hinv := by
    obtain ⟨hd_inv, hrep₀⟩ := hinv
    let τ₀ : PMF (WhpSeqROutcome C.Latent D.Result r_ds) :=
      ν₀.map WhpSeqROutcome.ofLatentRState
    have hproj₀ : τ₀.map projLatent = ν₀ := by
      dsimp only [τ₀]; rw [PMF.map_comp]; exact PMF.map_id ν₀
    have hv_hist : D.ValidHistory s₀ ops :=
      (D.validOpSeq_iff_validHistory s₀ ops).mp hv
    have hv_rem : D.ValidHistory (D.run s₀ []).1 ops := by
      rw [D.run_nil]; exact hv_hist
    have hd₀ : C.distInv [] (τ₀.map projLatent) := hproj₀.symm ▸ hd_inv
    have hsupp₀ : ∀ tr ∈ τ₀.support,
        C.rep (D.run s₀ []).1 tr.latent tr.data ∧ tr.transcript = (D.run s₀ []).2 := by
      intro tr htr; rw [PMF.mem_support_map_iff] at htr; obtain ⟨t, ht, rfl⟩ := htr
      rw [D.run_nil]; exact ⟨hrep₀ t ht, rfl⟩
    obtain ⟨τ_final, hex, hsupp_fin, hfail⟩ :=
      C.steps_exec_aux [] ops τ₀ trivial hv_rem hfit_ops hd₀ hsupp₀
    have hzero : τ₀.toOuterMeasure {tr | tr.allWithinBudget = false} = 0 := by
      rw [PMF.toOuterMeasure_apply]
      refine tsum_eq_zero_iff.mpr fun tr => ?_
      by_cases htr : tr ∈ τ₀.support
      · rw [PMF.mem_support_map_iff] at htr; obtain ⟨_, _, rfl⟩ := htr
        simp [WhpSeqROutcome.ofLatentRState]
      · simp [(PMF.apply_eq_zero_iff _ _).mpr htr]
    rw [hzero, zero_add] at hfail
    refine ⟨τ_final, hex, ?_, hfail⟩
    rw [D.toObliviousSequenceSpec_contract_iff_of_hasStepFn s₀ hv_hist]
    intro lbl hlbl
    rw [PMF.mem_support_map_iff] at hlbl; obtain ⟨tr, htr, rfl⟩ := hlbl
    obtain ⟨_, htr_eq⟩ := hsupp_fin tr htr
    rw [List.nil_append] at htr_eq
    exact htr_eq

end HighProbStateTransitionImpl

end Cslib.DataStructure.WordRAM.Resizable.Randomized
