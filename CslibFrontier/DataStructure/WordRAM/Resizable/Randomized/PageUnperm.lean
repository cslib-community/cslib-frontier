/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.WordRAM.Resizable.Randomized.IncrementalRebuild
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Shared Deamortized In-Place Page-Arena Unpermutation (`PageUnpermState`)

This module extends `PagePairState` (`IncrementalRebuild.lean`) with an original, reusable 4-stage
`O(1)`-step background unpermuter once `E_src` drains (`virtLen false = 0`), motivated by the
dynamic-resizing discussion of [Bender, Farach-Colton, J. Kuszmaul, W. Kuszmaul, and M. Liu,
STOC 2022, Section 5.2][BenderFarachColtonKuszmaulKuszmaulLiu2022] for `1 · OPT` dual-epoch
resizable succinct data structures on the **Resizable Word RAM** (`Cslib.WordRAM.Resizable`),
including both the resizable SOSA 2024 succinct dictionary
([Bender, Farach-Colton, J. Kuszmaul, and W. Kuszmaul, SOSA 2024,
Sections 5–6][BenderFarachColtonKuszmaulKuszmaul2024]) and resizable deamortized `k`-kick trees
([W. Kuszmaul, J. Liang, and R. Zhou, SODA 2026, Section 5.1][KuszmaulLiangZhou2026]).

Once `virtLen false = 0`, `PageUnpermState` drains any in-flight `PageJob` (`cleanPhase = 1`),
swaps permuted full pages `0 .. Q - 1` into identity positions (`cleanPhase = 2`), unpermutes tail
slots `0 .. r - 1` (`cleanPhase = 3`), and reaches `cleanPhase = 4` (`toPhys true idx = idx` for
every `idx < virtLen true`) in `< N_pg / 128` operations (`512` steps per operation) while serving
concurrent `O(1)` worst-case virtual reads, writes, `appendSlot`, and `popBackSlot` operations on
`E_dst` (`side = true`).

## Main definitions

* `Cslib.DataStructure.WordRAM.Resizable.Randomized.PageUnpermState`: 4-stage unpermutation wrapper
  over `PagePairState`.
* `PageUnpermState.InvWithSlack`, `PageUnpermState.Valid`, `PageUnpermState.unpermStep`,
  `PageUnpermState.runUnpermSteps`, `PageUnpermState.unpermRank`,
  `PageUnpermState.appendSlot`, `PageUnpermState.popBackSlot`.

## Main results

* `PageUnpermState.unpermStep_spec`, `PageUnpermState.unpermRank_lt_of_unpermStep`,
  `PageUnpermState.runUnpermSteps_restores_valid`: exact bijection preservation, strict Lyapunov
  rank descent, and slack restoration across concurrent `E_dst` updates.
* `PageUnpermState.appendSlot_spec`, `PageUnpermState.popBackSlot_spec`: virtual-array preservation
  and bounded slack (`InvWithSlack 24`) under concurrent `E_dst` appends and pops.

## References

* [M. A. Bender, M. Farach-Colton, J. Kuszmaul, W. Kuszmaul, and M. Liu,
  *On the Optimal Time/Space Tradeoff for Hash Tables*,
  Section 5.2][BenderFarachColtonKuszmaulKuszmaulLiu2022]
* [M. A. Bender, M. Farach-Colton, J. Kuszmaul, and W. Kuszmaul, *Modern Hashing Made Simple*,
  Sections 5–6][BenderFarachColtonKuszmaulKuszmaul2024]
* [W. Kuszmaul, J. Liang, and R. Zhou, *Succinct Dynamic Rank/Select: Bypassing the Tree-Structure
  Bottleneck*, Section 5.1][KuszmaulLiangZhou2026]
-/

public section

namespace Cslib.DataStructure.WordRAM.Resizable.Randomized

/-- Extended paged-pair state supporting both active two-epoch migration (`cleanPhase = 0`) and
4-stage deamortized in-place unpermutation (`cleanPhase ∈ {1, 2, 3, 4}`) once `virtLen false = 0`
(`0` projection chains). -/
structure PageUnpermState where
  /-- Underlying `PagePairState`. -/
  st : PagePairState
  /-- Unpermutation stage (`0`: active migration, `1`: draining active job, `2`: unpermuting full
  pages `0 .. Q - 1`, `3`: unpermuting tail `0 .. r - 1`, `4`: identity layout achieved). -/
  cleanPhase : ℕ
  /-- Page index `< Q` in `cleanPhase ∈ {1, 2}`, or tail index `< r` in `cleanPhase = 3`. -/
  cleanVp : ℕ
  /-- Intra-page swap cursor `0 .. B` while `cleanPhase = 2` is swapping `pageOf true cleanVp` with
  physical page `cleanVp`. -/
  cleanOff : ℕ

namespace PageUnpermState

/-- Embed an initial `PagePairState` at `cleanPhase = 0`. -/
@[expose] def ofPagePair (st : PagePairState) : PageUnpermState :=
  ⟨st, 0, 0, 0⟩

/-- Effective physical page during `cleanPhase = 2` when `0 < cleanOff` is swapping `P_cur =
st.pageOf true cleanVp` with `cleanVp` on offsets `0 .. cleanOff - 1`. -/
@[expose] def effCleanPage (u : PageUnpermState) (P off : ℕ) : ℕ :=
  if u.cleanPhase = 2 ∧ 0 < u.cleanOff then
    let P_cur := u.st.pageOf true u.cleanVp
    if off < u.cleanOff then
      if P = P_cur then u.cleanVp
      else if P = u.cleanVp then P_cur
      else P
    else P
  else
    u.st.effPage P off

theorem effCleanPage_involutive (u : PageUnpermState) (P off : ℕ) :
    u.effCleanPage (u.effCleanPage P off) off = P := by
  unfold effCleanPage
  by_cases hc : u.cleanPhase = 2 ∧ 0 < u.cleanOff
  · simp only [hc, and_self, ↓reduceIte]
    by_cases ho : off < u.cleanOff
    · simp only [ho, ↓reduceIte]
      set Pc := u.st.pageOf true u.cleanVp
      by_cases h1 : P = Pc
      · subst h1; split_ifs <;> omega
      · by_cases h2 : P = u.cleanVp
        · subst h2; simp [h1]
        · simp [h1, h2]
    · simp [ho]
  · simp only [hc, ↓reduceIte]
    exact PagePairState.effPage_involutive u.st P off

/-- `O(1)` virtual-to-physical slot translation accounting for an in-flight `cleanPhase = 2` page
swap. -/
@[expose] def toPhys (u : PageUnpermState) (side : Bool) (idx : ℕ) : ℕ :=
  let B := u.st.pageSize
  let fullLim := u.st.fullPages side * B
  if idx < fullLim then
    u.effCleanPage (u.st.pageOf side (idx / B)) (idx % B) * B + idx % B
  else
    u.st.tailPhys side (idx - fullLim)

/-- Logical read at `(side, idx)` from physical array `arr : ℕ → α`. -/
@[expose] def virtAt {α : Type*} (u : PageUnpermState) (arr : ℕ → α) (side : Bool) (idx : ℕ) : α :=
  arr (u.toPhys side idx)

@[simp] theorem toPhys_of_not_cleanSwap (u : PageUnpermState)
    (h : ¬(u.cleanPhase = 2 ∧ 0 < u.cleanOff)) (side : Bool) (idx : ℕ) :
    u.toPhys side idx = u.st.toPhys side idx := by
  unfold toPhys PagePairState.toPhys effCleanPage
  simp [h]

/-- Transition from `cleanPhase = 0` into Phase 2c/2d unpermutation once `virtLen false = 0`. -/
@[expose] def beginUnperm (u : PageUnpermState) : PageUnpermState :=
  if u.cleanPhase = 0 ∧ u.st.virtLen false = 0 then
    ⟨u.st, if u.st.job = .idle then 2 else 1, 0, 0⟩
  else
    u

/-- Elementary `O(1)` unpermutation step emitting `≤ 1` physical swap. -/
@[expose] def unpermStep (u : PageUnpermState) : PageUnpermState × List PhysSwap :=
  let st := u.st
  let B := st.pageSize
  let Q := st.fullPages true
  if u.cleanPhase = 1 then
    if st.job = .idle then
      (⟨st, 2, min u.cleanVp Q, 0⟩, [])
    else
      let (st', sws) := st.tick
      (⟨st', 1, min u.cleanVp (st'.fullPages true), 0⟩, sws)
  else if u.cleanPhase = 2 then
    if u.cleanOff = 0 then
      if Q ≤ u.cleanVp then
        (⟨st, 3, 0, 0⟩, [])
      else
        let P_cur := st.pageOf true u.cleanVp
        if P_cur = u.cleanVp then
          (⟨st, 2, u.cleanVp + 1, 0⟩, [])
        else
          (⟨st, 2, u.cleanVp, 1⟩, [⟨P_cur * B, u.cleanVp * B⟩])
    else if u.cleanOff < B then
      let P_cur := st.pageOf true u.cleanVp
      (⟨st, 2, u.cleanVp, u.cleanOff + 1⟩,
        [⟨P_cur * B + u.cleanOff, u.cleanVp * B + u.cleanOff⟩])
    else
      let P_cur := st.pageOf true u.cleanVp
      let vp_other := st.ownerVp u.cleanVp
      let st_c : PagePairState :=
        { st with
          pageOf := PagePairState.set2
            (PagePairState.set2 st.pageOf true vp_other P_cur) true u.cleanVp u.cleanVp
          ownerVp := Function.update
            (Function.update st.ownerVp P_cur vp_other) u.cleanVp u.cleanVp }
      let st_ms := st_c.maybeStartJob
      let ph' := if st_ms.job = .idle then 2 else 1
      (⟨st_ms, ph', min (u.cleanVp + 1) (st_ms.fullPages true), 0⟩, [])
  else if u.cleanPhase = 3 then
    if st.tailCount true ≤ u.cleanVp then
      (⟨st, 4, u.cleanVp, 0⟩, [])
    else
      let (st', sws) := st.swapTailSlots (st.tailPhys true u.cleanVp) (Q * B + u.cleanVp)
      (⟨st', 3, u.cleanVp + 1, 0⟩, sws)
  else
    (u, [])

/-- Iterate `unpermStep` `k` times left-to-right. -/
@[expose] def runUnpermSteps : ℕ → PageUnpermState → PageUnpermState × List PhysSwap
  | 0, u => (u, [])
  | k + 1, u =>
    let (u₁, sws₁) := u.unpermStep
    let (u₂, sws₂) := runUnpermSteps k u₁
    (u₂, sws₁ ++ sws₂)

/-- Deamortized `O(1)` virtual append across both active migration and Phase-2c/2d unpermutation. -/
@[expose] def appendSlot (u : PageUnpermState) (side : Bool) : PageUnpermState × List PhysSwap :=
  if u.cleanPhase = 0 then
    let (st', sws) := u.st.stepAppend side
    (⟨st', 0, 0, 0⟩, sws)
  else if u.cleanPhase = 1 ∨ (u.cleanPhase = 2 ∧ u.cleanOff = 0) then
    let (st', sws) := u.st.stepAppend side
    let ph' := if st'.job = .idle then 2 else 1
    (⟨st', ph', min u.cleanVp (st'.fullPages true), 0⟩, sws)
  else
    (⟨u.st.rawAppend side, u.cleanPhase, u.cleanVp, u.cleanOff⟩, [])

/-- Deamortized `O(1)` virtual popBack across both active migration and Phase-2c/2d
unpermutation. -/
@[expose] def popBackSlot (u : PageUnpermState) (side : Bool) : PageUnpermState × List PhysSwap :=
  if u.cleanPhase = 0 then
    let (st', sws) := u.st.stepPopBack side
    (⟨st', 0, 0, 0⟩, sws)
  else if u.cleanPhase = 1 ∨ (u.cleanPhase = 2 ∧ u.cleanOff = 0) then
    let (st', sws) := u.st.stepPopBack side
    let ph' := if st'.job = .idle then 2 else 1
    (⟨st', ph', min u.cleanVp (st'.fullPages true), 0⟩, sws)
  else if u.cleanPhase = 2 then
    let (st', sws) := u.st.rawPopBack side
    (⟨st', 2, u.cleanVp, u.cleanOff⟩, sws)
  else
    let (st', sws) := u.st.rawPopBack side
    (⟨st', u.cleanPhase, min u.cleanVp (st'.tailCount true), 0⟩, sws)

/-- State-local invariant parameterized by drift slack `slack ∈ {0, 24}` (`0` between operations,
`24` immediately after a single `appendSlot true` or `popBackSlot true` before `runUnpermSteps
512`). -/
structure InvWithSlack (u : PageUnpermState) (slack : ℕ) : Prop where
  valid : u.st.Valid
  pageSize_ge : 32 ≤ u.st.pageSize
  phase_le : u.cleanPhase ≤ 4
  slack_le : slack ≤ 24
  phase0_wb : u.cleanPhase = 0 → u.st.WellBalanced ∧ u.cleanVp = 0 ∧ u.cleanOff = 0
  src_empty : 0 < u.cleanPhase → u.st.fullPages false = 0 ∧ u.st.tailCount false = 0
  prefix_fixed : 0 < u.cleanPhase →
    ∀ vp < (if u.cleanPhase ≤ 2 then u.cleanVp else u.st.fullPages true),
      u.st.pageOf true vp = vp
  phase1_wb : u.cleanPhase = 1 →
    u.st.WellBalanced ∧ u.cleanVp ≤ u.st.fullPages true ∧ u.cleanOff = 0
  phase2_zero : u.cleanPhase = 2 → u.cleanOff = 0 →
    u.st.WellBalanced ∧ u.st.job = .idle ∧ u.cleanVp ≤ u.st.fullPages true
  phase2_pos : u.cleanPhase = 2 → 0 < u.cleanOff →
    u.st.job = .idle ∧ u.cleanVp < u.st.fullPages true ∧ u.cleanOff ≤ u.st.pageSize ∧
      u.st.pageOf true u.cleanVp ≠ u.cleanVp ∧
      16 * u.st.phi + (u.st.pageSize - u.cleanOff) / 16 ≤ 25 * u.st.pageSize + slack
  phase3_inv : u.cleanPhase = 3 →
    u.st.job = .idle ∧ u.cleanOff = 0 ∧ u.cleanVp ≤ u.st.tailCount true ∧
      (∀ t < u.cleanVp, u.st.tailPhys true t = u.st.fullPages true * u.st.pageSize + t) ∧
      16 * u.st.phi + (u.st.tailCount true - u.cleanVp) / 16 ≤ 25 * u.st.pageSize + slack
  phase4_id : u.cleanPhase = 4 →
    u.st.job = .idle ∧ u.cleanOff = 0 ∧
      ∀ idx < u.st.virtLen true, u.toPhys true idx = idx

/-- Resting validity invariant (`slack = 0`) maintained across operations. -/
abbrev Valid (u : PageUnpermState) : Prop := u.InvWithSlack 0

theorem InvWithSlack.mono {u : PageUnpermState} {s₁ s₂ : ℕ}
    (hi : u.InvWithSlack s₁) (hle : s₁ ≤ s₂) (hs₂ : s₂ ≤ 24) : u.InvWithSlack s₂ where
  valid := hi.valid
  pageSize_ge := hi.pageSize_ge
  phase_le := hi.phase_le
  slack_le := hs₂
  phase0_wb := hi.phase0_wb
  src_empty := hi.src_empty
  prefix_fixed := hi.prefix_fixed
  phase1_wb := hi.phase1_wb
  phase2_zero := hi.phase2_zero
  phase2_pos := fun h2 hp => by
    obtain ⟨h1, h2', h3, h4, h5⟩ := hi.phase2_pos h2 hp
    exact ⟨h1, h2', h3, h4, by omega⟩
  phase3_inv := fun h3 => by
    obtain ⟨h1, h2, h3', h4, h5⟩ := hi.phase3_inv h3
    exact ⟨h1, h2, h3', h4, by omega⟩
  phase4_id := hi.phase4_id

theorem valid_ofPagePair {st : PagePairState} (hw : st.WellBalanced) :
    (ofPagePair st).Valid where
  valid := hw.valid
  pageSize_ge := hw.pageSize_ge
  phase_le := Nat.zero_le 4
  slack_le := Nat.zero_le _
  phase0_wb := fun _ => ⟨hw, rfl, rfl⟩
  src_empty := fun h => absurd h (Nat.lt_irrefl 0)
  prefix_fixed := fun h => absurd h (Nat.lt_irrefl 0)
  phase1_wb := fun h => absurd h (by dsimp only [ofPagePair]; decide)
  phase2_zero := fun h => absurd h (by dsimp only [ofPagePair]; decide)
  phase2_pos := fun h => absurd h (by dsimp only [ofPagePair]; decide)
  phase3_inv := fun h => absurd h (by dsimp only [ofPagePair]; decide)
  phase4_id := fun h => absurd h (by dsimp only [ofPagePair]; decide)

theorem InvWithSlack.toPhys_lt {u : PageUnpermState} {slack : ℕ} (hi : u.InvWithSlack slack)
    {side : Bool} {idx : ℕ} (hidx : idx < u.st.virtLen side) :
    u.toPhys side idx < u.st.totalItems := by
  by_cases hcs : u.cleanPhase = 2 ∧ 0 < u.cleanOff
  · obtain ⟨_, hvp_lt, _, _, _⟩ := hi.phase2_pos hcs.1 hcs.2
    obtain ⟨hf0, _⟩ := hi.src_empty (by omega)
    have hB := hi.valid.pageSize_pos
    unfold toPhys
    dsimp only
    by_cases hlt : idx < u.st.fullPages side * u.st.pageSize
    · rw [ite_eq_left hlt]
      have hvp_s : idx / u.st.pageSize < u.st.fullPages side :=
        (Nat.div_lt_iff_lt_mul hB).mpr hlt
      have hp_s := hi.valid.page_lt side (idx / u.st.pageSize) hvp_s
      have htotP : u.st.totalPages = u.st.fullPages true := by
        unfold PagePairState.totalPages; rw [hf0, zero_add]
      have hp_c := hi.valid.page_lt true u.cleanVp hvp_lt
      set E := u.effCleanPage (u.st.pageOf side (idx / u.st.pageSize)) (idx % u.st.pageSize)
      have heff_lt : E < u.st.totalPages := by
        dsimp only [E, effCleanPage]
        simp only [hcs.1, hcs.2, and_self, ↓reduceIte]
        split_ifs <;> omega
      have hmod := Nat.mod_lt idx hB
      have hle : (E + 1) * u.st.pageSize ≤ u.st.totalPages * u.st.pageSize :=
        Nat.mul_le_mul_right _ heff_lt
      rw [Nat.add_one_mul] at hle
      rw [u.st.totalItems_eq]
      omega
    · rw [ite_eq_right hlt]
      unfold PagePairState.virtLen at hidx
      exact hi.valid.tail_lt side _ (by omega)
  · rw [toPhys_of_not_cleanSwap u hcs]
    exact hi.valid.toPhys_lt hidx

theorem InvWithSlack.toPhys_inj {u : PageUnpermState} {slack : ℕ} (hi : u.InvWithSlack slack)
    {side₁ side₂ : Bool} {idx₁ idx₂ : ℕ}
    (h₁ : idx₁ < u.st.virtLen side₁) (h₂ : idx₂ < u.st.virtLen side₂)
    (heq : u.toPhys side₁ idx₁ = u.toPhys side₂ idx₂) :
    side₁ = side₂ ∧ idx₁ = idx₂ := by
  by_cases hcs : u.cleanPhase = 2 ∧ 0 < u.cleanOff
  · obtain ⟨_, hvp_lt, _, _, _⟩ := hi.phase2_pos hcs.1 hcs.2
    obtain ⟨hf0, _⟩ := hi.src_empty (by omega)
    have hB := hi.valid.pageSize_pos
    have htotP : u.st.totalPages = u.st.fullPages true := by
      unfold PagePairState.totalPages; rw [hf0, zero_add]
    have hpage_lt : ∀ s i, i < u.st.fullPages s * u.st.pageSize →
        u.effCleanPage (u.st.pageOf s (i / u.st.pageSize)) (i % u.st.pageSize) * u.st.pageSize +
          i % u.st.pageSize < u.st.totalPages * u.st.pageSize := fun s i hi_lt => by
      have hvp : i / u.st.pageSize < u.st.fullPages s := (Nat.div_lt_iff_lt_mul hB).mpr hi_lt
      have hp1 := hi.valid.page_lt s (i / u.st.pageSize) hvp
      have hp2 := hi.valid.page_lt true u.cleanVp hvp_lt
      set E := u.effCleanPage (u.st.pageOf s (i / u.st.pageSize)) (i % u.st.pageSize)
      have he_lt : E < u.st.totalPages := by
        dsimp only [E, effCleanPage]; simp only [hcs.1, hcs.2, and_self, ↓reduceIte]
        split_ifs <;> omega
      have hmod := Nat.mod_lt i hB
      have hle : (E + 1) * u.st.pageSize ≤ u.st.totalPages * u.st.pageSize :=
        Nat.mul_le_mul_right u.st.pageSize he_lt
      rw [Nat.add_one_mul] at hle; omega
    unfold toPhys at heq; dsimp only at heq
    split_ifs at heq with hf₁ hf₂ hf₂
    · have hm₁ := Nat.mod_lt idx₁ hB
      have hm₂ := Nat.mod_lt idx₂ hB
      have heff_eq : u.effCleanPage (u.st.pageOf side₁ (idx₁ / u.st.pageSize))
            (idx₁ % u.st.pageSize) =
          u.effCleanPage (u.st.pageOf side₂ (idx₂ / u.st.pageSize))
            (idx₂ % u.st.pageSize) := by
        have hd1 : (u.effCleanPage (u.st.pageOf side₁ (idx₁ / u.st.pageSize))
              (idx₁ % u.st.pageSize) * u.st.pageSize + idx₁ % u.st.pageSize) / u.st.pageSize =
            u.effCleanPage (u.st.pageOf side₁ (idx₁ / u.st.pageSize)) (idx₁ % u.st.pageSize) := by
          rw [Nat.add_comm, Nat.add_mul_div_right _ _ hB, Nat.div_eq_of_lt hm₁, zero_add]
        have hd2 : (u.effCleanPage (u.st.pageOf side₂ (idx₂ / u.st.pageSize))
              (idx₂ % u.st.pageSize) * u.st.pageSize + idx₂ % u.st.pageSize) / u.st.pageSize =
            u.effCleanPage (u.st.pageOf side₂ (idx₂ / u.st.pageSize)) (idx₂ % u.st.pageSize) := by
          rw [Nat.add_comm, Nat.add_mul_div_right _ _ hB, Nat.div_eq_of_lt hm₂, zero_add]
        rw [← hd1, ← hd2, heq]
      have hrem_eq : idx₁ % u.st.pageSize = idx₂ % u.st.pageSize := by rw [heff_eq] at heq; omega
      rw [hrem_eq] at heff_eq
      have hpo_eq : u.st.pageOf side₁ (idx₁ / u.st.pageSize) =
          u.st.pageOf side₂ (idx₂ / u.st.pageSize) := by
        have hinv := congrArg (fun P => u.effCleanPage P (idx₂ % u.st.pageSize)) heff_eq
        simpa only [effCleanPage_involutive] using hinv
      have hvp₁ : idx₁ / u.st.pageSize < u.st.fullPages side₁ := (Nat.div_lt_iff_lt_mul hB).mpr hf₁
      have hvp₂ : idx₂ / u.st.pageSize < u.st.fullPages side₂ := (Nat.div_lt_iff_lt_mul hB).mpr hf₂
      have ho₁ := hi.valid.owner_pageOf side₁ (idx₁ / u.st.pageSize) hvp₁
      have ho₂ := hi.valid.owner_pageOf side₂ (idx₂ / u.st.pageSize) hvp₂
      rw [hpo_eq] at ho₁
      refine ⟨ho₁.1.symm.trans ho₂.1, ?_⟩
      have hd₁ := Nat.div_add_mod idx₁ u.st.pageSize
      have hd₂ := Nat.div_add_mod idx₂ u.st.pageSize
      rw [ho₁.2.symm.trans ho₂.2, hrem_eq] at hd₁; omega
    · exfalso
      have hlt := hpage_lt side₁ idx₁ hf₁
      have hge := le_physOfRes (u.st.totalPages * u.st.pageSize) u.st.pageSize
        (u.st.tailRes side₂ (u.st.ringSlot side₂ (idx₂ - u.st.fullPages side₂ * u.st.pageSize)))
      change _ ≤ u.st.tailPhys side₂ _ at hge; omega
    · exfalso
      have hlt := hpage_lt side₂ idx₂ hf₂
      have hge := le_physOfRes (u.st.totalPages * u.st.pageSize) u.st.pageSize
        (u.st.tailRes side₁ (u.st.ringSlot side₁ (idx₁ - u.st.fullPages side₁ * u.st.pageSize)))
      change _ ≤ u.st.tailPhys side₁ _ at hge; omega
    · have htp₁ : u.st.toPhys side₁ idx₁ =
          u.st.tailPhys side₁ (idx₁ - u.st.fullPages side₁ * u.st.pageSize) := by
        unfold PagePairState.toPhys; dsimp only; rw [ite_eq_right hf₁]
      have htp₂ : u.st.toPhys side₂ idx₂ =
          u.st.tailPhys side₂ (idx₂ - u.st.fullPages side₂ * u.st.pageSize) := by
        unfold PagePairState.toPhys; dsimp only; rw [ite_eq_right hf₂]
      exact hi.valid.toPhys_inj h₁ h₂ (by rw [htp₁, htp₂, heq])
  · rw [toPhys_of_not_cleanSwap u hcs, toPhys_of_not_cleanSwap u hcs] at heq
    exact hi.valid.toPhys_inj h₁ h₂ heq

theorem beginUnperm_spec {u : PageUnpermState} (hv : u.Valid) :
    let u' := u.beginUnperm
    u'.Valid ∧
    (u.cleanPhase = 0 ∧ u.st.virtLen false = 0 → 0 < u'.cleanPhase) ∧
    (∀ side idx, u'.toPhys side idx = u.toPhys side idx) := by
  dsimp only
  unfold beginUnperm
  by_cases hc : u.cleanPhase = 0 ∧ u.st.virtLen false = 0
  · rw [ite_eq_left hc]
    obtain ⟨hwb, _, _⟩ := hv.phase0_wb hc.1
    have hB_pos := hv.valid.pageSize_pos
    have hvl0 := hc.2
    unfold PagePairState.virtLen at hvl0
    have hf0 : u.st.fullPages false = 0 := by
      by_contra hnz
      have : 1 * u.st.pageSize ≤ u.st.fullPages false * u.st.pageSize :=
        Nat.mul_le_mul_right _ (Nat.pos_of_ne_zero hnz)
      omega
    have ht0 : u.st.tailCount false = 0 := by rw [hf0, zero_mul, zero_add] at hvl0; exact hvl0
    have hnot1 : ¬((if u.st.job = .idle then 2 else 1) = 2 ∧ 0 < (0 : ℕ)) := by simp
    have hnot0 : ¬(u.cleanPhase = 2 ∧ 0 < u.cleanOff) := by omega
    refine ⟨?_, fun _ => by dsimp only; split_ifs <;> decide, fun side idx => ?_⟩
    · split_ifs with hj
      · refine ⟨hv.valid, hv.pageSize_ge, by dsimp only; decide, Nat.zero_le _,
          fun h => absurd h (by dsimp only; decide), fun _ => ⟨hf0, ht0⟩,
          fun _ _ hvp => by dsimp only at hvp; exact absurd hvp (Nat.not_lt_zero _),
          fun h => absurd h (by dsimp only; decide),
          fun _ _ => ⟨hwb, hj, Nat.zero_le _⟩,
          fun _ hp => by dsimp only at hp; exact absurd hp (Nat.lt_irrefl 0),
          fun h => absurd h (by dsimp only; decide),
          fun h => absurd h (by dsimp only; decide)⟩
      · refine ⟨hv.valid, hv.pageSize_ge, by dsimp only; decide, Nat.zero_le _,
          fun h => absurd h (by dsimp only; decide), fun _ => ⟨hf0, ht0⟩,
          fun _ _ hvp => by dsimp only at hvp; exact absurd hvp (Nat.not_lt_zero _),
          fun _ => ⟨hwb, Nat.zero_le _, rfl⟩,
          fun h => absurd h (by dsimp only; decide),
          fun h => absurd h (by dsimp only; decide),
          fun h => absurd h (by dsimp only; decide),
          fun h => absurd h (by dsimp only; decide)⟩
    · rw [toPhys_of_not_cleanSwap _ hnot1, toPhys_of_not_cleanSwap u hnot0]
  · rw [ite_eq_right hc]
    exact ⟨hv, fun h => absurd h hc, fun _ _ => rfl⟩

/-- When `st.Valid`, `32 ≤ st.pageSize`, `st.job = .idle`, `st.tailCount false = 0`, and
`16 * st.phi ≤ 26 * st.pageSize - 2`, `st.maybeStartJob` is immediately `WellBalanced`. -/
private theorem maybeStartJob_wellBalanced_of_src_empty {st : PagePairState}
    (hv : st.Valid) (hB : 32 ≤ st.pageSize) (hj : st.job = .idle)
    (ht0 : st.tailCount false = 0) (hphi : 16 * st.phi ≤ 26 * st.pageSize - 2) :
    st.maybeStartJob.WellBalanced := by
  have hvalid_job : ∀ j, ({ st with job := j } : PagePairState).Valid := fun j =>
    ⟨hv.1, hv.2, hv.3, hv.4, hv.5, hv.6, hv.7, hv.8, hv.9, hv.10, hv.11⟩
  have launch_prom : ∀ s, 11 * st.pageSize ≤ 4 * st.tailCount s →
      PagePairState.WellBalanced { st with job := .promote s 0 } := fun s h11 => by
    refine ⟨hvalid_job _, hB, ?_, ?_, ?_⟩
    · simp only [PagePairState.JobValid]
      exact ⟨Nat.zero_le _, by omega, fun _ hu => absurd hu (Nat.not_lt_zero _)⟩
    · rw [ite_eq_right (by rintro ⟨⟩)]
      change 16 * st.phi + (st.pageSize + 1 - 0) ≤ 28 * st.pageSize; omega
    · simp only [PagePairState.ActiveSideBound, PagePairState.remTicks]; omega
  have launch_demBuild : ∀ s, 0 < st.fullPages s ∧ 4 * st.tailCount s ≤ 5 * st.pageSize →
      st.pageOf s (st.fullPages s - 1) = st.totalPages - 1 →
      PagePairState.WellBalanced { st with job := .demoteBuild s 0 } := fun s ⟨hq, hr5⟩ hp_eq => by
    have htc_t := hv.tailCount_lt true
    refine ⟨hvalid_job _, hB, ?_, ?_, ?_⟩
    · simp only [PagePairState.JobValid]
      refine ⟨Nat.zero_le _, hq, hp_eq, by omega, by omega,
        fun _ hu => absurd hu (Nat.not_lt_zero _)⟩
    · rw [ite_eq_right (by rintro ⟨⟩)]
      change 16 * st.phi + (st.pageSize + 1 - 0) ≤ 28 * st.pageSize; omega
    · simp only [PagePairState.ActiveSideBound, PagePairState.remTicks]; omega
  have launch_demSwap : ∀ s, 0 < st.fullPages s ∧ 4 * st.tailCount s ≤ 5 * st.pageSize →
      st.pageOf s (st.fullPages s - 1) ≠ st.totalPages - 1 →
      PagePairState.WellBalanced { st with job := .demoteSwap s 0 } := fun s ⟨hq, hr5⟩ hp_ne => by
    have hp_lt := hv.page_lt s (st.fullPages s - 1) (by omega)
    refine ⟨hvalid_job _, hB, ?_, ?_, ?_⟩
    · simp only [PagePairState.JobValid]
      exact ⟨Nat.zero_le _, hq, by change _ < st.totalPages - 1; omega⟩
    · rw [ite_eq_right (by rintro ⟨⟩)]
      change 16 * st.phi + (2 * st.pageSize + 2 - 0) ≤ 28 * st.pageSize; omega
    · simp only [PagePairState.ActiveSideBound, PagePairState.remTicks]; omega
  unfold PagePairState.maybeStartJob
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
    · rw [ite_eq_right h2f]; dsimp only
      by_cases h1t : 11 * st.pageSize ≤ 4 * st.tailCount true
      · rw [ite_eq_left h1t]; exact launch_prom true h1t
      · rw [ite_eq_right h1t]
        by_cases h2t : 0 < st.fullPages true ∧ 4 * st.tailCount true ≤ 5 * st.pageSize
        · rw [ite_eq_left h2t]
          by_cases h3t : st.pageOf true (st.fullPages true - 1) = st.totalPages - 1
          · rw [ite_eq_left h3t]; exact launch_demBuild true h2t h3t
          · rw [ite_eq_right h3t]; exact launch_demSwap true h2t h3t
        · rw [ite_eq_right h2t]; dsimp only
          refine ⟨hv, hB, by simp [PagePairState.JobValid, hj], ?_,
            by simp [PagePairState.ActiveSideBound, hj]⟩
          simp only [hj, ↓reduceIte]
          have hdev_f : 4 * PagePairState.dev st.pageSize (st.fullPages false)
              (st.tailCount false) ≤ 3 * st.pageSize - 1 := by
            unfold PagePairState.dev
            by_cases hqf : 0 < st.fullPages false
            · have : ¬(4 * st.tailCount false ≤ 5 * st.pageSize) := fun h => h2f ⟨hqf, h⟩
              simp only [hqf, ↓reduceIte]; omega
            · simp only [hqf, ↓reduceIte]; omega
          have hdev_t : 4 * PagePairState.dev st.pageSize (st.fullPages true)
              (st.tailCount true) ≤ 3 * st.pageSize - 1 := by
            unfold PagePairState.dev
            by_cases hqt : 0 < st.fullPages true
            · have : ¬(4 * st.tailCount true ≤ 5 * st.pageSize) := fun h => h2t ⟨hqt, h⟩
              simp only [hqt, ↓reduceIte]; omega
            · simp only [hqt, ↓reduceIte]; omega
          unfold PagePairState.phi; omega

/-- Self-contained prefix invariant on `[0, k)` (`k ≤ fullPages true`, `fullPages false = 0`),
preserved across `rawAppend true`, `rawPopBack true`, `maybeStartJob`, `tick`, `runTicks`,
`stepAppend true`, and `stepPopBack true` without requiring `WellBalanced` on intermediate ticks. -/
private structure PrefixFixed (st : PagePairState) (k : ℕ) : Prop where
  pageSize_pos : 0 < st.pageSize
  fp_false : st.fullPages false = 0
  tc_false : st.tailCount false = 0
  job_true : ∀ cur, st.job ≠ .promote false cur ∧ st.job ≠ .demoteSwap false cur ∧
    st.job ≠ .demoteBuild false cur
  k_le : k ≤ st.fullPages true
  fixed_lt : ∀ vp < k, st.pageOf true vp = vp ∧ st.ownerSide vp = true ∧ st.ownerVp vp = vp
  ge_of_ge : ∀ vp, k ≤ vp → vp < st.fullPages true → k ≤ st.pageOf true vp
  own_ge_of_ge : ∀ P, k ≤ P → P < st.fullPages true → k ≤ st.ownerVp P

private theorem PrefixFixed.of_valid {st : PagePairState} (hv : st.Valid)
    (hf0 : st.fullPages false = 0) (ht0 : st.tailCount false = 0)
    (hjv : st.JobValid) {k : ℕ} (hk : k ≤ st.fullPages true)
    (hpref : ∀ vp < k, st.pageOf true vp = vp) : PrefixFixed st k where
  pageSize_pos := hv.pageSize_pos
  fp_false := hf0
  tc_false := ht0
  job_true := fun cur => by
    refine ⟨?_, ?_, ?_⟩ <;> (intro hj; unfold PagePairState.JobValid at hjv; rw [hj] at hjv; omega)
  k_le := hk
  fixed_lt := fun vp hvp => by
    have hpo := hpref vp hvp
    obtain ⟨hos, hov⟩ := hv.owner_pageOf true vp (hvp.trans_le hk)
    rw [hpo] at hos hov
    exact ⟨hpo, hos, hov⟩
  ge_of_ge := fun vp hlo hhi => by
    by_contra hlt
    have hpo := hpref (st.pageOf true vp) (Nat.lt_of_not_ge hlt)
    obtain ⟨_, hov⟩ := hv.owner_pageOf true vp hhi
    obtain ⟨_, hov2⟩ := hv.owner_pageOf true (st.pageOf true vp)
      ((Nat.lt_of_not_ge hlt).trans_le hk)
    rw [hpo] at hov2
    omega
  own_ge_of_ge := fun P hlo hhi => by
    have htot : st.totalPages = st.fullPages true := by
      unfold PagePairState.totalPages; rw [hf0, zero_add]
    obtain ⟨_, hpo⟩ := hv.pageOf_owner P (htot ▸ hhi)
    have hos : st.ownerSide P = true := by
      obtain ⟨h1, _⟩ := hv.pageOf_owner P (htot ▸ hhi)
      cases hs : st.ownerSide P
      · rw [hs, hf0] at h1; exact absurd h1 (Nat.not_lt_zero _)
      · rfl
    rw [hos] at hpo
    by_contra hlt
    have hp := hpref (st.ownerVp P) (Nat.lt_of_not_ge hlt)
    omega

private theorem PrefixFixed.maybeStartJob {st : PagePairState} {k : ℕ}
    (hp : PrefixFixed st k) : PrefixFixed st.maybeStartJob k := by
  unfold PagePairState.maybeStartJob
  cases hj : st.job with
  | idle =>
    dsimp only
    have h1f : ¬(11 * st.pageSize ≤ 4 * st.tailCount false) := by
      rw [hp.tc_false]; have := hp.pageSize_pos; omega
    have h2f : ¬(0 < st.fullPages false ∧ 4 * st.tailCount false ≤ 5 * st.pageSize) := by
      rw [hp.fp_false]; simp
    rw [ite_eq_right h1f, ite_eq_right h2f]
    dsimp only
    by_cases h1t : 11 * st.pageSize ≤ 4 * st.tailCount true
    · rw [ite_eq_left h1t]; dsimp only
      exact ⟨hp.1, hp.2, hp.3, fun _ => ⟨by rintro ⟨⟩, by rintro ⟨⟩, by rintro ⟨⟩⟩,
        hp.5, hp.6, hp.7, hp.8⟩
    · rw [ite_eq_right h1t]
      by_cases h2t : 0 < st.fullPages true ∧ 4 * st.tailCount true ≤ 5 * st.pageSize
      · rw [ite_eq_left h2t]
        by_cases h3t : st.pageOf true (st.fullPages true - 1) = st.totalPages - 1
        · rw [ite_eq_left h3t]; dsimp only
          exact ⟨hp.1, hp.2, hp.3, fun _ => ⟨by rintro ⟨⟩, by rintro ⟨⟩, by rintro ⟨⟩⟩,
            hp.5, hp.6, hp.7, hp.8⟩
        · rw [ite_eq_right h3t]; dsimp only
          exact ⟨hp.1, hp.2, hp.3, fun _ => ⟨by rintro ⟨⟩, by rintro ⟨⟩, by rintro ⟨⟩⟩,
            hp.5, hp.6, hp.7, hp.8⟩
      · rw [ite_eq_right h2t]; dsimp only; exact hp
  | _ => exact hp

private theorem swapTailSlots_meta_eq (st : PagePairState) (p₁ p₂ : ℕ) :
    let st' := (st.swapTailSlots p₁ p₂).1
    st'.pageSize = st.pageSize ∧ st'.fullPages = st.fullPages ∧
    st'.tailCount = st.tailCount ∧ st'.pageOf = st.pageOf ∧
    st'.ownerSide = st.ownerSide ∧ st'.ownerVp = st.ownerVp ∧ st'.job = st.job := by
  dsimp only; unfold PagePairState.swapTailSlots; split_ifs <;>
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem PrefixFixed.tick {st : PagePairState} {k : ℕ} (hp : PrefixFixed st k) :
    PrefixFixed st.tick.1 (min k (st.tick.1.fullPages true)) := by
  have hms_fp : ∀ s0 : PagePairState, s0.maybeStartJob.fullPages = s0.fullPages := fun s0 => by
    unfold PagePairState.maybeStartJob; cases s0.job <;> try rfl
    dsimp only; split_ifs <;> rfl
  unfold PagePairState.tick
  rw [hms_fp]
  refine PrefixFixed.maybeStartJob ?_
  unfold PagePairState.tickOne
  cases hj : st.job with
  | idle =>
    dsimp only; rw [Nat.min_eq_left hp.k_le]; exact hp
  | promote s cur =>
    cases s
    · exfalso; exact (hp.job_true cur).1 hj
    · dsimp only
      split_ifs with hcur
      · obtain ⟨hps, hfp, htc, hpo, hos, hov, _⟩ :=
          swapTailSlots_meta_eq st (st.tailPhys true cur) (st.totalPages * st.pageSize + cur)
        dsimp only
        rw [hfp, Nat.min_eq_left hp.k_le]
        exact ⟨by dsimp only; rw [hps]; exact hp.1,
          hp.2,
          by dsimp only; rw [htc]; exact hp.3,
          fun _ => ⟨by rintro ⟨⟩, by rintro ⟨⟩, by rintro ⟨⟩⟩,
          hp.5,
          fun vp hv => by dsimp only; rw [hpo, hos, hov]; exact hp.6 vp hv,
          fun vp h1 h2 => by dsimp only; rw [hpo]; exact hp.7 vp h1 h2,
          fun P h1 h2 => by dsimp only; rw [hov]; exact hp.8 P h1 h2⟩
      · dsimp only
        have htotP : st.totalPages = st.fullPages true := by
          unfold PagePairState.totalPages; rw [hp.fp_false, zero_add]
        have hmin : min k (Function.update st.fullPages true (st.fullPages true + 1) true) = k := by
          rw [Function.update_self]; have := hp.k_le; omega
        rw [hmin]
        refine ⟨hp.1, by simp [hp.fp_false], by simp [hp.tc_false],
          fun _ => ⟨by rintro ⟨⟩, by rintro ⟨⟩, by rintro ⟨⟩⟩,
          by dsimp only; simp only [Function.update_self]; have := hp.k_le; omega,
          fun vp hvp => ?_, fun vp hlo hhi => ?_, fun P hlo hhi => ?_⟩
        · dsimp only
          have hne : vp ≠ st.fullPages true := by have := hp.k_le; omega
          have hneP : vp ≠ st.totalPages := by omega
          rw [PagePairState.set2_of_ne _ _ _ _ _ _ (fun h => hne h.2),
            Function.update_of_ne hneP, Function.update_of_ne hneP]
          exact hp.fixed_lt vp hvp
        · dsimp only at hhi ⊢
          rw [Function.update_self] at hhi
          by_cases heq : vp = st.fullPages true
          · subst heq; rw [PagePairState.set2_self, htotP]; exact hp.k_le
          · rw [PagePairState.set2_of_ne _ _ _ _ _ _ (fun h => heq h.2)]
            exact hp.ge_of_ge vp hlo (by omega)
        · dsimp only at hhi ⊢
          rw [Function.update_self] at hhi
          by_cases heq : P = st.totalPages
          · subst heq; rw [Function.update_self]; exact hp.k_le
          · rw [Function.update_of_ne heq]
            exact hp.own_ge_of_ge P hlo (by omega)
  | demoteSwap s cur =>
    cases s
    · exfalso; exact (hp.job_true cur).2.1 hj
    · dsimp only
      split_ifs with hcur
      · dsimp only; rw [Nat.min_eq_left hp.k_le]
        exact ⟨hp.1, hp.2, hp.3, fun _ => ⟨by rintro ⟨⟩, by rintro ⟨⟩, by rintro ⟨⟩⟩,
          hp.5, hp.6, hp.7, hp.8⟩
      · dsimp only; rw [Nat.min_eq_left hp.k_le]
        have htotP : st.totalPages = st.fullPages true := by
          unfold PagePairState.totalPages; rw [hp.fp_false, zero_add]
        refine ⟨hp.1, hp.2, hp.3, fun _ => ⟨by rintro ⟨⟩, by rintro ⟨⟩, by rintro ⟨⟩⟩,
          hp.5, fun vp hvp => ?_, fun vp hlo hhi => ?_, fun P hlo hhi => ?_⟩
        · dsimp only
          have hQ_pos : 0 < st.fullPages true := lt_of_le_of_lt (Nat.zero_le vp)
            (lt_of_lt_of_le hvp hp.k_le)
          by_cases hk_eq : k = st.fullPages true
          · subst hk_eq
            obtain ⟨hpo_l, hos_l, hov_l⟩ := hp.fixed_lt (st.fullPages true - 1) (by omega)
            rw [htotP, hpo_l, hos_l, hov_l]
            obtain ⟨h1, h2, h3⟩ := hp.fixed_lt vp hvp
            by_cases hv_last : vp = st.fullPages true - 1
            · subst hv_last; simp [PagePairState.set2]
            · rw [PagePairState.set2_of_ne _ _ _ _ _ _ (fun h => hv_last h.2),
                PagePairState.set2_of_ne _ _ _ _ _ _ (fun h => hv_last h.2),
                Function.update_of_ne hv_last, Function.update_of_ne hv_last,
                Function.update_of_ne hv_last, Function.update_of_ne hv_last]
              exact ⟨h1, h2, h3⟩
          · have hk_lt : k ≤ st.fullPages true - 1 := by have := hp.k_le; omega
            have hPd_ge : k ≤ st.pageOf true (st.fullPages true - 1) :=
              hp.ge_of_ge _ hk_lt (by omega)
            have hvpl_ge : k ≤ st.ownerVp (st.totalPages - 1) := by
              rw [htotP]; exact hp.own_ge_of_ge _ hk_lt (by omega)
            rw [PagePairState.set2_of_ne _ _ _ _ _ _ (by rintro ⟨_, rfl⟩; omega),
              PagePairState.set2_of_ne _ _ _ _ _ _ (by rintro ⟨_, rfl⟩; omega),
              Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
            exact hp.fixed_lt vp hvp
        · dsimp only at hhi ⊢
          have hQ_pos : 0 < st.fullPages true := lt_of_le_of_lt (Nat.zero_le k)
            (lt_of_le_of_lt hlo hhi)
          by_cases hk_eq : k = st.fullPages true
          · omega
          · have hk_lt : k ≤ st.fullPages true - 1 := by have := hp.k_le; omega
            have hPd_ge : k ≤ st.pageOf true (st.fullPages true - 1) :=
              hp.ge_of_ge _ hk_lt (by omega)
            by_cases hc1 : vp = st.fullPages true - 1
            · subst hc1; rw [PagePairState.set2_self, htotP]; exact hk_lt
            · rw [PagePairState.set2_of_ne _ _ _ _ _ _ (fun h => hc1 h.2)]
              unfold PagePairState.set2
              split_ifs
              · exact hPd_ge
              · exact hp.ge_of_ge vp hlo hhi
        · dsimp only at hhi ⊢
          have hQ_pos : 0 < st.fullPages true := lt_of_le_of_lt (Nat.zero_le k)
            (lt_of_le_of_lt hlo hhi)
          by_cases hk_eq : k = st.fullPages true
          · omega
          · have hk_lt : k ≤ st.fullPages true - 1 := by have := hp.k_le; omega
            have hvpl_ge : k ≤ st.ownerVp (st.totalPages - 1) := by
              rw [htotP]; exact hp.own_ge_of_ge _ hk_lt (by omega)
            by_cases hc1 : P = st.totalPages - 1
            · rw [hc1, Function.update_self]; exact hk_lt
            · rw [Function.update_of_ne hc1]
              by_cases hc2 : P = st.pageOf true (st.fullPages true - 1)
              · rw [hc2, Function.update_self]; exact hvpl_ge
              · rw [Function.update_of_ne hc2]; exact hp.own_ge_of_ge P hlo hhi
  | demoteBuild s cur =>
    cases s
    · exfalso; exact (hp.job_true cur).2.2 hj
    · dsimp only
      split_ifs with hcur
      · dsimp only; rw [Nat.min_eq_left hp.k_le]
        exact ⟨hp.1, hp.2, hp.3, fun _ => ⟨by rintro ⟨⟩, by rintro ⟨⟩, by rintro ⟨⟩⟩,
          hp.5, hp.6, hp.7, hp.8⟩
      · dsimp only
        refine ⟨hp.1, by simp [hp.fp_false], by simp [hp.tc_false],
          fun _ => ⟨by rintro ⟨⟩, by rintro ⟨⟩, by rintro ⟨⟩⟩,
          min_le_right _ _,
          fun vp hvp => hp.fixed_lt vp (lt_of_lt_of_le hvp (min_le_left _ _)),
          fun vp hlo hhi => ?_, fun P hlo hhi => ?_⟩
        · dsimp only at hlo hhi ⊢
          rw [Function.update_self] at hlo hhi ⊢
          have hmin_k : min k (st.fullPages true - 1) = k := Nat.min_eq_left (by omega)
          rw [hmin_k] at hlo ⊢
          exact hp.ge_of_ge vp hlo (by omega)
        · dsimp only at hlo hhi ⊢
          rw [Function.update_self] at hlo hhi ⊢
          have hmin_k : min k (st.fullPages true - 1) = k := Nat.min_eq_left (by omega)
          rw [hmin_k] at hlo ⊢
          exact hp.own_ge_of_ge P hlo (by omega)

private theorem PrefixFixed.of_all {st : PagePairState}
    (hp : PrefixFixed st (st.fullPages true)) {k' : ℕ} (hk' : k' ≤ st.fullPages true) :
    PrefixFixed st k' where
  pageSize_pos := hp.1
  fp_false := hp.2
  tc_false := hp.3
  job_true := hp.4
  k_le := hk'
  fixed_lt := fun vp hvp => hp.fixed_lt vp (lt_of_lt_of_le hvp hk')
  ge_of_ge := fun vp hlo hhi => by rw [(hp.fixed_lt vp hhi).1]; exact hlo
  own_ge_of_ge := fun P hlo hhi => by rw [(hp.fixed_lt P hhi).2.2]; exact hlo

private theorem PrefixFixed.tick_all {st : PagePairState}
    (hp : PrefixFixed st (st.fullPages true)) :
    PrefixFixed st.tick.1 (st.tick.1.fullPages true) := by
  have hms_fp : ∀ s0 : PagePairState, s0.maybeStartJob.fullPages = s0.fullPages := fun s0 => by
    unfold PagePairState.maybeStartJob; cases s0.job <;> try rfl
    dsimp only; split_ifs <;> rfl
  by_cases hgrow : st.tick.1.fullPages true = st.fullPages true + 1
  · unfold PagePairState.tick at hgrow ⊢
    rw [hms_fp] at hgrow ⊢
    refine PrefixFixed.maybeStartJob ?_
    unfold PagePairState.tickOne at hgrow ⊢
    cases hj : st.job with
    | idle => rw [hj] at hgrow; dsimp only at hgrow; omega
    | promote s cur =>
      cases s
      · exfalso; exact (hp.job_true cur).1 hj
      · rw [hj] at hgrow; dsimp only at hgrow ⊢
        split_ifs at hgrow ⊢ with hcur
        · obtain ⟨_, hfp, _, _, _, _, _⟩ :=
            swapTailSlots_meta_eq st (st.tailPhys true cur) (st.totalPages * st.pageSize + cur)
          dsimp only at hgrow; rw [hfp] at hgrow; omega
        · dsimp only
          have htotP : st.totalPages = st.fullPages true := by
            unfold PagePairState.totalPages; rw [hp.fp_false, zero_add]
          refine ⟨hp.1, by simp [hp.fp_false], by simp [hp.tc_false],
            fun _ => ⟨by rintro ⟨⟩, by rintro ⟨⟩, by rintro ⟨⟩⟩, le_rfl,
            fun vp hvp => ?_, fun _ hlo hhi => absurd hhi (Nat.not_lt_of_ge hlo),
            fun _ hlo hhi => absurd hhi (Nat.not_lt_of_ge hlo)⟩
          dsimp only at hvp ⊢
          rw [Function.update_self] at hvp
          rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hvp) with rfl | hlt
          · rw [PagePairState.set2_self, htotP, Function.update_self, Function.update_self]
            exact ⟨rfl, rfl, rfl⟩
          · have hne : vp ≠ st.fullPages true := Nat.ne_of_lt hlt
            have hneP : vp ≠ st.totalPages := by omega
            rw [PagePairState.set2_of_ne _ _ _ _ _ _ (fun h => hne h.2),
              Function.update_of_ne hneP, Function.update_of_ne hneP]
            exact hp.fixed_lt vp hlt
    | demoteSwap s cur =>
      rw [hj] at hgrow; dsimp only at hgrow; split_ifs at hgrow <;> dsimp only at hgrow <;> omega
    | demoteBuild s cur =>
      cases s
      · exfalso; exact (hp.job_true cur).2.2 hj
      · rw [hj] at hgrow; dsimp only at hgrow; split_ifs at hgrow <;> dsimp only at hgrow
        · omega
        · rw [Function.update_self] at hgrow; omega
  · have hle : st.tick.1.fullPages true ≤ st.fullPages true := by
      unfold PagePairState.tick
      rw [hms_fp]
      unfold PagePairState.tickOne
      cases hj : st.job with
      | idle => exact le_rfl
      | promote s cur =>
        cases s
        · exfalso; exact (hp.job_true cur).1 hj
        · dsimp only; split_ifs with hcur
          · obtain ⟨_, hfp, _, _, _, _, _⟩ :=
              swapTailSlots_meta_eq st (st.tailPhys true cur) (st.totalPages * st.pageSize + cur)
            dsimp only; rw [hfp]
          · exfalso; apply hgrow; unfold PagePairState.tick; rw [hms_fp]
            simp [PagePairState.tickOne, hj, hcur]
      | demoteSwap s cur => dsimp only; split_ifs <;> exact le_rfl
      | demoteBuild s cur =>
        cases s
        · exfalso; exact (hp.job_true cur).2.2 hj
        · dsimp only; split_ifs
          · exact le_rfl
          · dsimp only; rw [Function.update_self]; omega
    simpa only [Nat.min_eq_right hle] using hp.tick

private theorem PrefixFixed.runTicks_all : ∀ (n : ℕ) {st : PagePairState},
    PrefixFixed st (st.fullPages true) →
    PrefixFixed (PagePairState.runTicks n st).1 ((PagePairState.runTicks n st).1.fullPages true)
  | 0, _, hp => hp
  | n + 1, _, hp => PrefixFixed.runTicks_all n hp.tick_all

private theorem PrefixFixed.runTicks : ∀ (n : ℕ) {st : PagePairState} {k : ℕ},
    PrefixFixed st k →
    PrefixFixed (PagePairState.runTicks n st).1
      (min k ((PagePairState.runTicks n st).1.fullPages true))
  | 0, st, k, hp => by dsimp only [PagePairState.runTicks]; rw [Nat.min_eq_left hp.k_le]; exact hp
  | n + 1, st, k, hp => by
    dsimp only [PagePairState.runTicks]
    by_cases hk_eq : k = st.fullPages true
    · subst hk_eq
      exact (PrefixFixed.runTicks_all (n + 1) hp).of_all (min_le_right _ _)
    · have hk_lt : k < st.fullPages true := lt_of_le_of_ne hp.k_le hk_eq
      have hge1 : k ≤ st.tick.1.fullPages true := by
        have hms_fp : ∀ s0 : PagePairState, s0.maybeStartJob.fullPages = s0.fullPages :=
          fun s0 => by
            unfold PagePairState.maybeStartJob; cases s0.job <;> try rfl
            dsimp only; split_ifs <;> rfl
        unfold PagePairState.tick; rw [hms_fp]; unfold PagePairState.tickOne
        cases hj : st.job with
        | idle => dsimp only; omega
        | promote s cur =>
          cases s
          · exfalso; exact (hp.job_true cur).1 hj
          · dsimp only; split_ifs
            · obtain ⟨_, hfp, _, _, _, _, _⟩ :=
                swapTailSlots_meta_eq st (st.tailPhys true cur) (st.totalPages * st.pageSize + cur)
              dsimp only; rw [hfp]; omega
            · dsimp only; rw [Function.update_self]; omega
        | demoteSwap s cur => dsimp only; split_ifs <;> dsimp only <;> omega
        | demoteBuild s cur =>
          cases s
          · exfalso; exact (hp.job_true cur).2.2 hj
          · dsimp only; split_ifs
            · dsimp only; omega
            · dsimp only; rw [Function.update_self]; omega
      have hp1 : PrefixFixed st.tick.1 k := by
        simpa only [Nat.min_eq_left hge1] using hp.tick
      exact PrefixFixed.runTicks n hp1

private theorem PrefixFixed.rawAppend_true {st : PagePairState} {k : ℕ}
    (hp : PrefixFixed st k) : PrefixFixed (st.rawAppend true) k := by
  unfold PagePairState.rawAppend
  exact ⟨hp.1, hp.2, by simp [hp.tc_false], hp.4, hp.5, hp.6, hp.7, hp.8⟩

private theorem PrefixFixed.rawPopBack_true {st : PagePairState} {k : ℕ}
    (hp : PrefixFixed st k) : PrefixFixed (st.rawPopBack true).1 k := by
  unfold PagePairState.rawPopBack
  obtain ⟨hps, hfp, htc, hpo, hos, hov, hj⟩ :=
    swapTailSlots_meta_eq st (st.tailPhys true (st.tailCount true - 1)) (st.totalItems - 1)
  dsimp only
  exact ⟨hps ▸ hp.1, by rw [hfp]; exact hp.2,
    by dsimp only; rw [Function.update_of_ne (by decide), htc]; exact hp.3,
    by rw [hj]; exact hp.4,
    by rw [hfp]; exact hp.5,
    fun vp hv => by rw [hpo, hos, hov]; exact hp.6 vp hv,
    fun vp h1 h2 => by rw [hfp] at h2; rw [hpo]; exact hp.7 vp h1 h2,
    fun P h1 h2 => by rw [hfp] at h2; rw [hov]; exact hp.8 P h1 h2⟩

/-- Single `unpermStep` preserves `InvWithSlack slack`, emits `≤ 1` swap strictly inside
`[0, u.st.totalItems)`, and preserves `virtAt` on both sides. -/
theorem unpermStep_spec {u : PageUnpermState} {slack : ℕ} (hi : u.InvWithSlack slack) :
    let res := u.unpermStep
    let u' := res.1
    let sws := res.2
    u'.InvWithSlack slack ∧
    u'.st.pageSize = u.st.pageSize ∧
    u'.st.virtLen = u.st.virtLen ∧
    u'.st.totalItems = u.st.totalItems ∧
    sws.length ≤ 1 ∧
    (∀ sw ∈ sws, sw.p₁ < u.st.totalItems ∧ sw.p₂ < u.st.totalItems) ∧
    (∀ {α : Type*} (arr : ℕ → α) (side : Bool) (idx : ℕ), idx < u.st.virtLen side →
      u'.virtAt (applySwaps sws arr) side idx = u.virtAt arr side idx) := by
  dsimp only
  have hv := hi.valid
  have hB32 := hi.pageSize_ge
  have hB := hv.pageSize_pos
  have hsl := hi.slack_le
  unfold unpermStep
  dsimp only
  by_cases hp1 : u.cleanPhase = 1
  · rw [ite_eq_left hp1]
    obtain ⟨hwb, hvp_le, hoff0⟩ := hi.phase1_wb hp1
    obtain ⟨hf0, ht0⟩ := hi.src_empty (by omega)
    have hpref0 : ∀ vp < u.cleanVp, u.st.pageOf true vp = vp := fun vp hvp => by
      have hp := hi.prefix_fixed (by omega) vp
      rw [ite_eq_left (by omega)] at hp
      exact hp hvp
    by_cases hj : u.st.job = .idle
    · rw [ite_eq_left hj]
      dsimp only
      have hnot_u : ¬(u.cleanPhase = 2 ∧ 0 < u.cleanOff) := by omega
      have hnot_u' : ¬((2 : ℕ) = 2 ∧ 0 < (0 : ℕ)) := by simp
      refine ⟨?_, rfl, rfl, rfl, Nat.zero_le 1, by simp, fun arr side idx _ => ?_⟩
      · refine ⟨hv, hB32, by dsimp only; decide, hsl,
          fun h => absurd h (by dsimp only; decide), fun _ => ⟨hf0, ht0⟩,
          fun _ vp hvp => ?_, fun h => absurd h (by dsimp only; decide),
          fun _ _ => ⟨hwb, hj, min_le_right _ _⟩,
          fun _ hp => absurd hp (Nat.lt_irrefl 0),
          fun h => absurd h (by dsimp only; decide),
          fun h => absurd h (by dsimp only; decide)⟩
        dsimp only at hvp; rw [ite_eq_left (by decide)] at hvp
        exact hpref0 vp (lt_of_lt_of_le hvp (min_le_left _ _))
      · simp only [applySwaps_nil, virtAt,
          toPhys_of_not_cleanSwap ⟨u.st, 2, min u.cleanVp (u.st.fullPages true), 0⟩ hnot_u',
          toPhys_of_not_cleanSwap u hnot_u]
    · rw [ite_eq_right hj]
      dsimp only
      obtain ⟨hwb', hps', hvl', hti', hlen', hsw', hvirt'⟩ := PagePairState.tick_spec hwb
      have hpf := (PrefixFixed.of_valid hv hf0 ht0 hwb.jobValid hvp_le hpref0).tick
      have hnot_u : ¬(u.cleanPhase = 2 ∧ 0 < u.cleanOff) := by omega
      have hnot_u' : ¬((1 : ℕ) = 2 ∧ 0 < (0 : ℕ)) := by simp
      refine ⟨?_, hps', hvl', hti', hlen', hsw', fun arr side idx hidx => ?_⟩
      · refine ⟨hwb'.valid, hps' ▸ hB32, by dsimp only; decide, hsl,
          fun h => absurd h (by dsimp only; decide), fun _ => ⟨hpf.fp_false, hpf.tc_false⟩,
          fun _ vp hvp => ?_,
          fun _ => ⟨hwb', min_le_right _ _, rfl⟩,
          fun h => absurd h (by dsimp only; decide), fun h => absurd h (by dsimp only; decide),
          fun h => absurd h (by dsimp only; decide), fun h => absurd h (by dsimp only; decide)⟩
        dsimp only at hvp; rw [ite_eq_left (by decide)] at hvp
        exact (hpf.fixed_lt vp hvp).1
      · simp only [virtAt,
          toPhys_of_not_cleanSwap ⟨u.st.tick.1, 1, min u.cleanVp (u.st.tick.1.fullPages true), 0⟩
            hnot_u',
          toPhys_of_not_cleanSwap u hnot_u]
        exact hvirt' arr side idx hidx
  · rw [ite_eq_right hp1]
    by_cases hp2 : u.cleanPhase = 2
    · rw [ite_eq_left hp2]
      obtain ⟨hf0, ht0⟩ := hi.src_empty (by omega)
      have htotP : u.st.totalPages = u.st.fullPages true := by
        unfold PagePairState.totalPages; rw [hf0, zero_add]
      have hpref0 : ∀ vp < u.cleanVp, u.st.pageOf true vp = vp := fun vp hvp => by
        have hp := hi.prefix_fixed (by omega) vp
        rw [ite_eq_left (by omega)] at hp
        exact hp hvp
      by_cases hoff0 : u.cleanOff = 0
      · rw [ite_eq_left hoff0]
        obtain ⟨hwb, hj, hvp_le⟩ := hi.phase2_zero hp2 hoff0
        have hpot_idle : 16 * u.st.phi ≤ 24 * u.st.pageSize - 8 := by
          have hp := hwb.pot_bound; simpa only [hj, ↓reduceIte] using hp
        have hnot_u : ¬(u.cleanPhase = 2 ∧ 0 < u.cleanOff) := by omega
        by_cases hdone_p : u.st.fullPages true ≤ u.cleanVp
        · rw [ite_eq_left hdone_p]
          dsimp only
          have htc_lt : u.st.tailCount true < 4 * u.st.pageSize := hv.tailCount_lt true
          have hnot_u' : ¬((3 : ℕ) = 2 ∧ 0 < (0 : ℕ)) := by simp
          refine ⟨?_, rfl, rfl, rfl, Nat.zero_le 1, by simp, fun arr side idx _ => ?_⟩
          · refine ⟨hv, hB32, by dsimp only; decide, hsl,
              fun h => absurd h (by dsimp only; decide), fun _ => ⟨hf0, ht0⟩,
              fun _ vp hvp => ?_,
              fun h => absurd h (by dsimp only; decide), fun h => absurd h (by dsimp only; decide),
              fun h => absurd h (by dsimp only; decide),
              fun _ => ⟨hj, rfl, Nat.zero_le _, fun _ ht => absurd ht (Nat.not_lt_zero _),
                by dsimp only; omega⟩,
              fun h => absurd h (by dsimp only; decide)⟩
            dsimp only at hvp; rw [ite_eq_right (by decide)] at hvp
            exact hpref0 vp (lt_of_lt_of_le hvp hdone_p)
          · simp only [applySwaps_nil, virtAt,
              toPhys_of_not_cleanSwap ⟨u.st, 3, 0, 0⟩ hnot_u',
              toPhys_of_not_cleanSwap u hnot_u]
        · rw [ite_eq_right hdone_p]
          have hvp_lt_Q : u.cleanVp < u.st.fullPages true := Nat.lt_of_not_ge hdone_p
          by_cases hP_eq : u.st.pageOf true u.cleanVp = u.cleanVp
          · rw [ite_eq_left hP_eq]
            dsimp only
            have hnot_u' : ¬((2 : ℕ) = 2 ∧ 0 < (0 : ℕ)) := by simp
            refine ⟨?_, rfl, rfl, rfl, Nat.zero_le 1, by simp, fun arr side idx _ => ?_⟩
            · refine ⟨hv, hB32, by dsimp only; decide, hsl,
                fun h => absurd h (by dsimp only; decide), fun _ => ⟨hf0, ht0⟩,
                fun _ vp hvp => ?_, fun h => absurd h (by dsimp only; decide),
                fun _ _ => ⟨hwb, hj, by dsimp only; omega⟩,
                fun _ hp => absurd hp (Nat.lt_irrefl 0),
                fun h => absurd h (by dsimp only; decide),
                fun h => absurd h (by dsimp only; decide)⟩
              dsimp only at hvp; rw [ite_eq_left (by decide)] at hvp
              rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hvp) with rfl | hlt
              · exact hP_eq
              · exact hpref0 vp hlt
            · simp only [applySwaps_nil, virtAt,
                toPhys_of_not_cleanSwap ⟨u.st, 2, u.cleanVp + 1, 0⟩ hnot_u',
                toPhys_of_not_cleanSwap u hnot_u]
          · rw [ite_eq_right hP_eq]
            dsimp only
            set P_cur := u.st.pageOf true u.cleanVp
            have hPc_lt : P_cur < u.st.totalPages := hv.page_lt true u.cleanVp hvp_lt_Q
            have h1_lt : P_cur * u.st.pageSize < u.st.totalPages * u.st.pageSize :=
              Nat.mul_lt_mul_of_pos_right hPc_lt hB
            have h2_lt : u.cleanVp * u.st.pageSize < u.st.totalPages * u.st.pageSize :=
              Nat.mul_lt_mul_of_pos_right (htotP ▸ hvp_lt_Q) hB
            have htot_ge : u.st.totalPages * u.st.pageSize ≤ u.st.totalItems := by
              rw [u.st.totalItems_eq]; omega
            refine ⟨?_, rfl, rfl, rfl, le_rfl, ?_, fun arr side idx _ => ?_⟩
            · refine ⟨hv, hB32, by dsimp only; decide, hsl,
                fun h => absurd h (by dsimp only; decide), fun _ => ⟨hf0, ht0⟩,
                fun _ vp hvp => ?_,
                fun h => absurd h (by dsimp only; decide),
                fun _ h0 => absurd h0 (by dsimp only; decide),
                fun _ _ => ⟨hj, hvp_lt_Q, by dsimp only; omega, hP_eq, by dsimp only; omega⟩,
                fun h => absurd h (by dsimp only; decide),
                fun h => absurd h (by dsimp only; decide)⟩
              dsimp only at hvp; rw [ite_eq_left (by decide)] at hvp
              exact hpref0 vp hvp
            · intro sw hsw; simp only [List.mem_singleton] at hsw; subst hsw
              exact ⟨h1_lt.trans_le htot_ge, h2_lt.trans_le htot_ge⟩
            · simp only [applySwaps_cons, applySwaps_nil, virtAt]
              rw [toPhys_of_not_cleanSwap u hnot_u]
              unfold toPhys PagePairState.toPhys effCleanPage PagePairState.effPage
              rw [hj]
              dsimp only
              by_cases hlt : idx < u.st.fullPages side * u.st.pageSize
              · rw [ite_eq_left hlt, ite_eq_left hlt]
                set P := u.st.pageOf side (idx / u.st.pageSize)
                set off := idx % u.st.pageSize
                have hoff_lt : off < u.st.pageSize := Nat.mod_lt idx hB
                by_cases ho0 : off = 0
                · simp only [ho0, Nat.lt_one_iff, ↓reduceIte, add_zero]
                  by_cases hc1 : P = P_cur
                  · rw [ite_eq_left hc1, hc1]; exact PhysSwap.apply_p₂ _ arr
                  · rw [ite_eq_right hc1]
                    by_cases hc2 : P = u.cleanVp
                    · rw [ite_eq_left hc2, hc2]; exact PhysSwap.apply_p₁ _ arr
                    · rw [ite_eq_right hc2]
                      exact PhysSwap.apply_of_ne _ arr
                        (fun h => hc1 (Nat.eq_of_mul_eq_mul_right hB h))
                        (fun h => hc2 (Nat.eq_of_mul_eq_mul_right hB h))
                · have hnot1 : ¬(off < 1) := by omega
                  simp only [hnot1, ↓reduceIte]
                  have hne1 : P * u.st.pageSize + off ≠ P_cur * u.st.pageSize := by
                    intro h; have hm := congrArg (· % u.st.pageSize) h
                    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hoff_lt,
                      Nat.mul_mod_left] at hm
                    exact ho0 hm
                  have hne2 : P * u.st.pageSize + off ≠ u.cleanVp * u.st.pageSize := by
                    intro h; have hm := congrArg (· % u.st.pageSize) h
                    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hoff_lt,
                      Nat.mul_mod_left] at hm
                    exact ho0 hm
                  exact PhysSwap.apply_of_ne _ arr hne1 hne2
              · rw [ite_eq_right hlt, ite_eq_right hlt]
                have hge := le_physOfRes (u.st.totalPages * u.st.pageSize) u.st.pageSize
                  (u.st.tailRes side
                    (u.st.ringSlot side (idx - u.st.fullPages side * u.st.pageSize)))
                change _ ≤ u.st.tailPhys side _ at hge
                exact PhysSwap.apply_of_ne ⟨P_cur * u.st.pageSize, u.cleanVp * u.st.pageSize⟩ arr
                  (Nat.ne_of_gt (h1_lt.trans_le hge))
                  (Nat.ne_of_gt (h2_lt.trans_le hge))
      · rw [ite_eq_right hoff0]
        have hoff_pos : 0 < u.cleanOff := Nat.pos_of_ne_zero hoff0
        obtain ⟨hj, hvp_lt_Q, hoff_le_B, hP_ne, hpot⟩ := hi.phase2_pos hp2 hoff_pos
        set P_cur := u.st.pageOf true u.cleanVp
        have hPc_lt : P_cur < u.st.totalPages := hv.page_lt true u.cleanVp hvp_lt_Q
        by_cases hoff_lt_B : u.cleanOff < u.st.pageSize
        · rw [ite_eq_left hoff_lt_B]
          dsimp only
          have h1_lt : P_cur * u.st.pageSize + u.cleanOff < u.st.totalPages * u.st.pageSize := by
            have hle := Nat.mul_le_mul_right u.st.pageSize hPc_lt
            rw [Nat.add_one_mul] at hle; omega
          have h2_lt : u.cleanVp * u.st.pageSize + u.cleanOff <
              u.st.totalPages * u.st.pageSize := by
            have hle := Nat.mul_le_mul_right u.st.pageSize (htotP ▸ hvp_lt_Q)
            rw [Nat.add_one_mul] at hle; omega
          have htot_ge : u.st.totalPages * u.st.pageSize ≤ u.st.totalItems := by
            rw [u.st.totalItems_eq]; omega
          have hdiv_le : (u.st.pageSize - (u.cleanOff + 1)) / 16 ≤
              (u.st.pageSize - u.cleanOff) / 16 := Nat.div_le_div_right (by omega)
          refine ⟨?_, rfl, rfl, rfl, le_rfl, ?_, fun arr side idx _ => ?_⟩
          · refine ⟨hv, hB32, by dsimp only; decide, hsl,
              fun h => absurd h (by dsimp only; decide), fun _ => ⟨hf0, ht0⟩,
              fun _ vp hvp => ?_,
              fun h => absurd h (by dsimp only; decide), fun _ h0 => by dsimp only at h0; omega,
              fun _ _ => ⟨hj, hvp_lt_Q, by dsimp only; omega, hP_ne, by dsimp only; omega⟩,
              fun h => absurd h (by dsimp only; decide),
              fun h => absurd h (by dsimp only; decide)⟩
            dsimp only at hvp; rw [ite_eq_left (by decide)] at hvp
            exact hpref0 vp hvp
          · intro sw hsw; simp only [List.mem_singleton] at hsw; subst hsw
            exact ⟨h1_lt.trans_le htot_ge, h2_lt.trans_le htot_ge⟩
          · simp only [applySwaps_cons, applySwaps_nil, virtAt]
            unfold toPhys effCleanPage
            dsimp only
            simp only [hp2, hoff_pos, Nat.succ_pos, and_self, ↓reduceIte]
            by_cases hlt : idx < u.st.fullPages side * u.st.pageSize
            · rw [ite_eq_left hlt, ite_eq_left hlt]
              set P := u.st.pageOf side (idx / u.st.pageSize)
              set off := idx % u.st.pageSize
              have hoff_mod : off < u.st.pageSize := Nat.mod_lt idx hB
              change (⟨P_cur * u.st.pageSize + u.cleanOff,
                       u.cleanVp * u.st.pageSize + u.cleanOff⟩ : PhysSwap).apply arr
                ((if off < u.cleanOff + 1 then
                    if P = P_cur then u.cleanVp else if P = u.cleanVp then P_cur else P
                  else P) * u.st.pageSize + off) =
                arr ((if off < u.cleanOff then
                    if P = P_cur then u.cleanVp else if P = u.cleanVp then P_cur else P
                  else P) * u.st.pageSize + off)
              by_cases ho_eq : off = u.cleanOff
              · rw [ho_eq, ite_eq_left (Nat.lt_succ_self _), ite_eq_right (lt_irrefl _)]
                by_cases hc1 : P = P_cur
                · rw [ite_eq_left hc1, hc1]; exact PhysSwap.apply_p₂ _ arr
                · rw [ite_eq_right hc1]
                  by_cases hc2 : P = u.cleanVp
                  · rw [ite_eq_left hc2, hc2]; exact PhysSwap.apply_p₁ _ arr
                  · rw [ite_eq_right hc2]
                    exact PhysSwap.apply_of_ne
                      ⟨P_cur * u.st.pageSize + u.cleanOff, u.cleanVp * u.st.pageSize + u.cleanOff⟩
                      arr
                      (fun h => hc1 (Nat.eq_of_mul_eq_mul_right hB (by dsimp only at h; omega)))
                      (fun h => hc2 (Nat.eq_of_mul_eq_mul_right hB (by dsimp only at h; omega)))
              · have hiff : off < u.cleanOff + 1 ↔ off < u.cleanOff := by omega
                by_cases ho_lt : off < u.cleanOff
                · rw [ite_eq_left (hiff.mpr ho_lt), ite_eq_left ho_lt]
                  set E := if P = P_cur then u.cleanVp else if P = u.cleanVp then P_cur else P
                  have hne1 : E * u.st.pageSize + off ≠ P_cur * u.st.pageSize + u.cleanOff := by
                    intro h; have hm := congrArg (· % u.st.pageSize) h
                    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hoff_mod,
                      Nat.add_comm (P_cur * u.st.pageSize), Nat.add_mul_mod_self_right,
                      Nat.mod_eq_of_lt hoff_lt_B] at hm
                    exact ho_eq hm
                  have hne2 : E * u.st.pageSize + off ≠ u.cleanVp * u.st.pageSize + u.cleanOff := by
                    intro h; have hm := congrArg (· % u.st.pageSize) h
                    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hoff_mod,
                      Nat.add_comm (u.cleanVp * u.st.pageSize), Nat.add_mul_mod_self_right,
                      Nat.mod_eq_of_lt hoff_lt_B] at hm
                    exact ho_eq hm
                  exact PhysSwap.apply_of_ne _ arr hne1 hne2
                · rw [ite_eq_right (mt hiff.mp ho_lt), ite_eq_right ho_lt]
                  have hne1 : P * u.st.pageSize + off ≠ P_cur * u.st.pageSize + u.cleanOff := by
                    intro h; have hm := congrArg (· % u.st.pageSize) h
                    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hoff_mod,
                      Nat.add_comm (P_cur * u.st.pageSize), Nat.add_mul_mod_self_right,
                      Nat.mod_eq_of_lt hoff_lt_B] at hm
                    exact ho_eq hm
                  have hne2 : P * u.st.pageSize + off ≠ u.cleanVp * u.st.pageSize + u.cleanOff := by
                    intro h; have hm := congrArg (· % u.st.pageSize) h
                    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hoff_mod,
                      Nat.add_comm (u.cleanVp * u.st.pageSize), Nat.add_mul_mod_self_right,
                      Nat.mod_eq_of_lt hoff_lt_B] at hm
                    exact ho_eq hm
                  exact PhysSwap.apply_of_ne _ arr hne1 hne2
            · rw [ite_eq_right hlt, ite_eq_right hlt]
              have hge := le_physOfRes (u.st.totalPages * u.st.pageSize) u.st.pageSize
                (u.st.tailRes side (u.st.ringSlot side (idx - u.st.fullPages side * u.st.pageSize)))
              change _ ≤ u.st.tailPhys side _ at hge
              exact PhysSwap.apply_of_ne
                ⟨P_cur * u.st.pageSize + u.cleanOff, u.cleanVp * u.st.pageSize + u.cleanOff⟩ arr
                (Nat.ne_of_gt (h1_lt.trans_le hge))
                (Nat.ne_of_gt (h2_lt.trans_le hge))
        · rw [ite_eq_right hoff_lt_B]
          have hoff_eq_B : u.cleanOff = u.st.pageSize := by omega
          dsimp only
          set vp_other := u.st.ownerVp u.cleanVp
          have hcv_tot : u.cleanVp < u.st.totalPages := htotP ▸ hvp_lt_Q
          obtain ⟨hvpo_lt, hpo_o⟩ := hv.pageOf_owner u.cleanVp hcv_tot
          have hos_true : ∀ P < u.st.totalPages, u.st.ownerSide P = true := fun P hP => by
            obtain ⟨h1, _⟩ := hv.pageOf_owner P hP
            cases hside : u.st.ownerSide P
            · rw [hside, hf0] at h1; exact absurd h1 (Nat.not_lt_zero _)
            · rfl
          have hos_cv : u.st.ownerSide u.cleanVp = true := hos_true u.cleanVp hcv_tot
          rw [hos_cv] at hvpo_lt hpo_o
          change vp_other < u.st.fullPages true at hvpo_lt
          change u.st.pageOf true vp_other = u.cleanVp at hpo_o
          have hvp_ne : u.cleanVp ≠ vp_other := by
            intro heq; rw [← heq] at hpo_o; exact hP_ne hpo_o
          set st_c : PagePairState :=
            { u.st with
              pageOf := PagePairState.set2
                (PagePairState.set2 u.st.pageOf true vp_other P_cur) true u.cleanVp u.cleanVp
              ownerVp := Function.update
                (Function.update u.st.ownerVp P_cur vp_other) u.cleanVp u.cleanVp }
          have heff_page : ∀ side vp, vp < u.st.fullPages side → ∀ off < u.st.pageSize,
              st_c.pageOf side vp = u.effCleanPage (u.st.pageOf side vp) off := by
            intro side vp hvp off hoff
            cases side
            · rw [hf0] at hvp; exact absurd hvp (Nat.not_lt_zero _)
            · unfold effCleanPage
              simp only [hp2, hoff_eq_B, hB, and_self, hoff, ↓reduceIte]
              dsimp only [st_c]
              by_cases hc1 : vp = u.cleanVp
              · subst hc1
                rw [PagePairState.set2_self, ite_eq_left rfl]
              · rw [PagePairState.set2_of_ne _ _ _ _ _ _ (fun h => hc1 h.2)]
                have hne_Pc : u.st.pageOf true vp ≠ P_cur := by
                  intro heq
                  have ho1 := hv.owner_pageOf true vp hvp
                  have ho2 := hv.owner_pageOf true u.cleanVp hvp_lt_Q
                  rw [heq] at ho1; exact hc1 (ho1.2.symm.trans ho2.2)
                rw [ite_eq_right hne_Pc]
                by_cases hc2 : vp = vp_other
                · subst hc2; rw [PagePairState.set2_self, hpo_o, ite_eq_left rfl]
                · rw [PagePairState.set2_of_ne _ _ _ _ _ _ (fun h => hc2 h.2)]
                  have hne_cv : u.st.pageOf true vp ≠ u.cleanVp := by
                    intro heq
                    have ho1 := hv.owner_pageOf true vp hvp
                    rw [heq] at ho1; exact hc2 ho1.2.symm
                  rw [ite_eq_right hne_cv]
          have hv_c : st_c.Valid := by
            refine ⟨hB, hv.tailCount_lt, hv.tailSum_lt, hv.tailHead_lt, ?_, ?_, ?_,
              hv.tailRes_lt, hv.tail_lt, hv.owner_tail, hv.tail_owner⟩
            · intro side vp hvp
              cases side
              · rw [hf0] at hvp; exact absurd hvp (Nat.not_lt_zero _)
              · change st_c.pageOf true vp < u.st.totalPages
                rw [heff_page true vp hvp 0 hB]
                unfold effCleanPage
                simp only [hp2, hoff_eq_B, hB, and_self, ↓reduceIte]
                split_ifs
                · exact hcv_tot
                · exact hPc_lt
                · exact hv.page_lt true vp hvp
            · intro side vp hvp
              cases side
              · rw [hf0] at hvp; exact absurd hvp (Nat.not_lt_zero _)
              · dsimp only [st_c]
                by_cases hc1 : vp = u.cleanVp
                · subst hc1
                  rw [PagePairState.set2_self, Function.update_self]
                  exact ⟨hos_cv, rfl⟩
                · rw [PagePairState.set2_of_ne _ _ _ _ _ _ (fun h => hc1 h.2)]
                  by_cases hc2 : vp = vp_other
                  · subst hc2
                    rw [PagePairState.set2_self, Function.update_of_ne hP_ne,
                      Function.update_self]
                    exact ⟨hos_true P_cur hPc_lt, rfl⟩
                  · rw [PagePairState.set2_of_ne _ _ _ _ _ _ (fun h => hc2 h.2)]
                    have hne_Pc : u.st.pageOf true vp ≠ P_cur := by
                      intro heq
                      have ho1 := hv.owner_pageOf true vp hvp
                      have ho2 := hv.owner_pageOf true u.cleanVp hvp_lt_Q
                      rw [heq] at ho1; exact hc1 (ho1.2.symm.trans ho2.2)
                    have hne_cv : u.st.pageOf true vp ≠ u.cleanVp := by
                      intro heq
                      have ho1 := hv.owner_pageOf true vp hvp
                      rw [heq] at ho1; exact hc2 ho1.2.symm
                    rw [Function.update_of_ne hne_cv, Function.update_of_ne hne_Pc]
                    exact hv.owner_pageOf true vp hvp
            · intro P hP
              have hosP := hos_true P hP
              dsimp only [st_c]
              by_cases h1 : P = u.cleanVp
              · subst h1
                rw [Function.update_self, hos_cv]
                exact ⟨hvp_lt_Q, PagePairState.set2_self ..⟩
              · by_cases h2 : P = P_cur
                · subst h2
                  rw [Function.update_of_ne h1, Function.update_self, hosP]
                  refine ⟨hvpo_lt, ?_⟩
                  rw [PagePairState.set2_of_ne _ _ _ _ _ _ (fun h => hvp_ne h.2.symm),
                    PagePairState.set2_self]
                · rw [Function.update_of_ne h1, Function.update_of_ne h2]
                  obtain ⟨hvpP, hpoP⟩ := hv.pageOf_owner P hP
                  refine ⟨hvpP, ?_⟩
                  rw [hosP] at hpoP ⊢
                  have hc1 : ¬(true = true ∧ u.st.ownerVp P = u.cleanVp) := by
                    rintro ⟨_, he⟩; apply h2; rw [← hpoP, he]
                  have hc2 : ¬(true = true ∧ u.st.ownerVp P = vp_other) := by
                    rintro ⟨_, he⟩; apply h1; rw [← hpoP, he]; exact hpo_o
                  rw [PagePairState.set2_of_ne _ _ _ _ _ _ hc1,
                    PagePairState.set2_of_ne _ _ _ _ _ _ hc2, hpoP]
          have hwb_ms : st_c.maybeStartJob.WellBalanced :=
            maybeStartJob_wellBalanced_of_src_empty hv_c hB32 hj ht0 (by
              change 16 * u.st.phi ≤ 26 * u.st.pageSize - 2; omega)
          have hms_po : st_c.maybeStartJob.pageOf = st_c.pageOf := by
            unfold PagePairState.maybeStartJob; rw [show st_c.job = .idle from hj]
            dsimp only; split_ifs <;> rfl
          have hms_fp : st_c.maybeStartJob.fullPages = u.st.fullPages := by
            unfold PagePairState.maybeStartJob; rw [show st_c.job = .idle from hj]
            dsimp only; split_ifs <;> rfl
          have hms_tc : st_c.maybeStartJob.tailCount = u.st.tailCount := by
            unfold PagePairState.maybeStartJob; rw [show st_c.job = .idle from hj]
            dsimp only; split_ifs <;> rfl
          have hms_ps : st_c.maybeStartJob.pageSize = u.st.pageSize := by
            unfold PagePairState.maybeStartJob; rw [show st_c.job = .idle from hj]
            dsimp only; split_ifs <;> rfl
          have hms_vl : st_c.maybeStartJob.virtLen = u.st.virtLen := by
            ext s0; unfold PagePairState.virtLen; rw [hms_fp, hms_ps, hms_tc]
          have hms_ti : st_c.maybeStartJob.totalItems = u.st.totalItems := by
            unfold PagePairState.totalItems; rw [hms_vl]
          have hpref_c : ∀ vp < u.cleanVp + 1, st_c.pageOf true vp = vp := fun vp hvp => by
            rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hvp) with rfl | hlt
            · exact PagePairState.set2_self ..
            · have hp_old := hpref0 vp hlt
              have hc1 : ¬(true = true ∧ vp = u.cleanVp) := fun h => by omega
              have hc2 : ¬(true = true ∧ vp = vp_other) := by
                rintro ⟨_, rfl⟩; rw [hpo_o] at hp_old; omega
              dsimp only [st_c]
              rw [PagePairState.set2_of_ne _ _ _ _ _ _ hc1,
                PagePairState.set2_of_ne _ _ _ _ _ _ hc2]
              exact hp_old
          set st_ms := st_c.maybeStartJob
          set ph' := if st_ms.job = .idle then 2 else 1
          have hnot_u' : ¬(ph' = 2 ∧ 0 < (0 : ℕ)) := by simp
          refine ⟨?_, hms_ps, hms_vl, hms_ti, Nat.zero_le 1, by simp,
            fun arr side idx _ => ?_⟩
          · refine ⟨hwb_ms.valid, hms_ps ▸ hB32, by dsimp only [ph']; split_ifs <;> decide, hsl,
              fun h => absurd h (by dsimp only [ph']; split_ifs <;> decide),
              fun _ => ⟨by rw [hms_fp]; exact hf0, by rw [hms_tc]; exact ht0⟩,
              fun _ vp hvp => ?_,
              fun _ => ⟨hwb_ms, min_le_right _ _, rfl⟩,
              fun h2 _ => ?_,
              fun _ hp => absurd hp (Nat.lt_irrefl 0),
              fun h => absurd h (by dsimp only [ph']; split_ifs <;> decide),
              fun h => absurd h (by dsimp only [ph']; split_ifs <;> decide)⟩
            · dsimp only at hvp
              have hle2 : ph' ≤ 2 := by dsimp only [ph']; split_ifs <;> decide
              rw [ite_eq_left hle2] at hvp
              rw [hms_po]
              exact hpref_c vp (by omega)
            · dsimp only [ph'] at h2
              by_cases hj_ms : st_ms.job = .idle
              · exact ⟨hwb_ms, hj_ms, min_le_right _ _⟩
              · rw [ite_eq_right hj_ms] at h2; cases h2
          · simp only [applySwaps_nil, virtAt]
            rw [toPhys_of_not_cleanSwap
              ⟨st_ms, ph', min (u.cleanVp + 1) (st_ms.fullPages true), 0⟩ hnot_u',
              PagePairState.maybeStartJob_toPhys]
            unfold PagePairState.toPhys toPhys
            dsimp only [st_c]
            split_ifs with hlt
            · have hvp : idx / u.st.pageSize < u.st.fullPages side :=
                (Nat.div_lt_iff_lt_mul hB).mpr hlt
              have heff_c : st_c.effPage (st_c.pageOf side (idx / u.st.pageSize))
                  (idx % u.st.pageSize) = st_c.pageOf side (idx / u.st.pageSize) := by
                unfold PagePairState.effPage; rw [show st_c.job = .idle from hj]
              rw [heff_c, heff_page side _ hvp _ (Nat.mod_lt idx hB)]
            · rfl
    · rw [ite_eq_right hp2]
      by_cases hp3 : u.cleanPhase = 3
      · rw [ite_eq_left hp3]
        obtain ⟨hf0, ht0⟩ := hi.src_empty (by omega)
        obtain ⟨hj, hoff0, hvp_le, htail_id, hpot⟩ := hi.phase3_inv hp3
        have hpref_all : ∀ vp < u.st.fullPages true, u.st.pageOf true vp = vp := fun vp hvp => by
          have hp := hi.prefix_fixed (by omega) vp
          rw [ite_eq_right (by omega)] at hp
          exact hp hvp
        have htotP : u.st.totalPages = u.st.fullPages true := by
          unfold PagePairState.totalPages; rw [hf0, zero_add]
        have hnot_u : ¬(u.cleanPhase = 2 ∧ 0 < u.cleanOff) := by omega
        by_cases hdone_t : u.st.tailCount true ≤ u.cleanVp
        · rw [ite_eq_left hdone_t]
          dsimp only
          have hnot_u' : ¬((4 : ℕ) = 2 ∧ 0 < (0 : ℕ)) := by simp
          refine ⟨?_, rfl, rfl, rfl, Nat.zero_le 1, by simp, fun arr side idx _ => ?_⟩
          · refine ⟨hv, hB32, by dsimp only; decide, hsl,
              fun h => absurd h (by dsimp only; decide), fun _ => ⟨hf0, ht0⟩,
              fun _ vp hvp => ?_,
              fun h => absurd h (by dsimp only; decide), fun h => absurd h (by dsimp only; decide),
              fun h => absurd h (by dsimp only; decide),
              fun h => absurd h (by dsimp only; decide),
              fun _ => ⟨hj, rfl, fun idx hidx => ?_⟩⟩
            · dsimp only at hvp; rw [ite_eq_right (by decide)] at hvp
              exact hpref_all vp hvp
            · rw [toPhys_of_not_cleanSwap ⟨u.st, 4, u.cleanVp, 0⟩ hnot_u']
              unfold PagePairState.toPhys PagePairState.effPage
              rw [hj]
              dsimp only
              split_ifs with hlt
              · have hvp : idx / u.st.pageSize < u.st.fullPages true :=
                  (Nat.div_lt_iff_lt_mul hB).mpr hlt
                rw [hpref_all _ hvp, Nat.mul_comm (idx / u.st.pageSize), Nat.div_add_mod]
              · dsimp only [PagePairState.virtLen] at hidx
                rw [htail_id _ (by omega)]
                omega
          · simp only [applySwaps_nil, virtAt,
              toPhys_of_not_cleanSwap ⟨u.st, 4, u.cleanVp, 0⟩ hnot_u',
              toPhys_of_not_cleanSwap u hnot_u]
        · rw [ite_eq_right hdone_t]
          have hvp_lt_tc : u.cleanVp < u.st.tailCount true := Nat.lt_of_not_ge hdone_t
          dsimp only
          have hp1_lo : u.st.totalPages * u.st.pageSize ≤ u.st.tailPhys true u.cleanVp :=
            le_physOfRes _ _ _
          have hp1_hi : u.st.tailPhys true u.cleanVp < u.st.totalItems :=
            hv.tail_lt true u.cleanVp hvp_lt_tc
          have hp2_lo : u.st.totalPages * u.st.pageSize ≤
              u.st.fullPages true * u.st.pageSize + u.cleanVp := by
            rw [htotP]; exact Nat.le_add_right _ _
          have hp2_hi : u.st.fullPages true * u.st.pageSize + u.cleanVp < u.st.totalItems := by
            rw [u.st.totalItems_eq, htotP]; omega
          obtain ⟨hv1, hps1, hfp1, htc1, _, hpo1, _, _, hj1, hsw_len, hsw_lt, htp_f, hvirt_sw⟩ :=
            PagePairState.swapTailSlots_spec hv hp1_lo hp1_hi hp2_lo hp2_hi
          set st' := (u.st.swapTailSlots (u.st.tailPhys true u.cleanVp)
            (u.st.fullPages true * u.st.pageSize + u.cleanVp)).1
          set sws := (u.st.swapTailSlots (u.st.tailPhys true u.cleanVp)
            (u.st.fullPages true * u.st.pageSize + u.cleanVp)).2
          have hphi1 : st'.phi = u.st.phi := by
            unfold PagePairState.phi; rw [hps1, hfp1, htc1]
          have hdiv_le : (st'.tailCount true - (u.cleanVp + 1)) / 16 ≤
              (u.st.tailCount true - u.cleanVp) / 16 := by
            rw [htc1]; exact Nat.div_le_div_right (by omega)
          have hvl1 : st'.virtLen = u.st.virtLen := by
            ext s0; unfold PagePairState.virtLen; rw [hfp1, hps1, htc1]
          have hti1 : st'.totalItems = u.st.totalItems := by
            unfold PagePairState.totalItems; rw [hvl1]
          have hnot_u' : ¬((3 : ℕ) = 2 ∧ 0 < (0 : ℕ)) := by simp
          refine ⟨?_, hps1, hvl1, hti1, hsw_len, hsw_lt, fun arr side idx hidx => ?_⟩
          · refine ⟨hv1, hps1 ▸ hB32, by dsimp only; decide, hsl,
              fun h => absurd h (by dsimp only; decide),
              fun _ => ⟨by rw [hfp1]; exact hf0, by rw [htc1]; exact ht0⟩,
              fun _ vp hvp => ?_,
              fun h => absurd h (by dsimp only; decide),
              fun h => absurd h (by dsimp only; decide),
              fun h => absurd h (by dsimp only; decide),
              fun _ => ⟨by rw [hj1]; exact hj, rfl,
                by dsimp only; rw [htc1]; omega, fun t ht => ?_,
                by dsimp only; rw [hphi1, hps1]; omega⟩,
              fun h => absurd h (by dsimp only; decide)⟩
            · dsimp only at hvp; rw [ite_eq_right (by decide), hfp1] at hvp
              rw [hpo1]; exact hpref_all vp hvp
            · dsimp only at ht ⊢
              rw [hfp1, hps1, htp_f true t (by omega)]
              rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp ht) with rfl | hlt
              · simp
              · have ht_eq := htail_id t hlt
                have hne2 : u.st.tailPhys true t ≠
                    u.st.fullPages true * u.st.pageSize + u.cleanVp := by omega
                have hne1 : u.st.tailPhys true t ≠ u.st.tailPhys true u.cleanVp := by
                  intro heq
                  have hi1 : u.st.fullPages true * u.st.pageSize + t < u.st.virtLen true := by
                    unfold PagePairState.virtLen; omega
                  have hi2 : u.st.fullPages true * u.st.pageSize + u.cleanVp <
                      u.st.virtLen true := by unfold PagePairState.virtLen; omega
                  have htp1 : u.st.toPhys true (u.st.fullPages true * u.st.pageSize + t) =
                      u.st.tailPhys true t := by
                    unfold PagePairState.toPhys; dsimp only
                    rw [ite_eq_right (by omega), Nat.add_sub_cancel_left]
                  have htp2 : u.st.toPhys true (u.st.fullPages true * u.st.pageSize + u.cleanVp) =
                      u.st.tailPhys true u.cleanVp := by
                    unfold PagePairState.toPhys; dsimp only
                    rw [ite_eq_right (by omega), Nat.add_sub_cancel_left]
                  obtain ⟨_, hie⟩ := hv.toPhys_inj hi1 hi2 (by rw [htp1, htp2, heq])
                  omega
                rw [ite_eq_right hne1, ite_eq_right hne2, ht_eq]
          · simp only [virtAt,
              toPhys_of_not_cleanSwap ⟨st', 3, u.cleanVp + 1, 0⟩ hnot_u',
              toPhys_of_not_cleanSwap u hnot_u]
            exact hvirt_sw arr side idx hidx
      · rw [ite_eq_right hp3]
        exact ⟨hi, rfl, rfl, rfl, Nat.zero_le 1, by simp, fun _ _ _ _ => rfl⟩

/-- Iterating `unpermStep` `k` times preserves `InvWithSlack slack`, emits `≤ k` swaps strictly
inside `[0, u.st.totalItems)`, and preserves `virtAt` on both sides. -/
theorem runUnpermSteps_spec (k : ℕ) {u : PageUnpermState} {slack : ℕ}
    (hi : u.InvWithSlack slack) :
    let res := runUnpermSteps k u
    let u' := res.1
    let sws := res.2
    u'.InvWithSlack slack ∧
    u'.st.pageSize = u.st.pageSize ∧
    u'.st.virtLen = u.st.virtLen ∧
    u'.st.totalItems = u.st.totalItems ∧
    sws.length ≤ k ∧
    (∀ sw ∈ sws, sw.p₁ < u.st.totalItems ∧ sw.p₂ < u.st.totalItems) ∧
    (∀ {α : Type*} (arr : ℕ → α) (side : Bool) (idx : ℕ), idx < u.st.virtLen side →
      u'.virtAt (applySwaps sws arr) side idx = u.virtAt arr side idx) := by
  induction k generalizing u with
  | zero =>
    exact ⟨hi, rfl, rfl, rfl, le_rfl, by simp [runUnpermSteps], fun _ _ _ _ => rfl⟩
  | succ k ih =>
    dsimp only [runUnpermSteps]
    obtain ⟨hi1, hps1, hvl1, hti1, hlen1, hsw1, hvirt1⟩ := unpermStep_spec hi
    obtain ⟨hi2, hps2, hvl2, hti2, hlen2, hsw2, hvirt2⟩ := ih hi1
    refine ⟨hi2, hps2.trans hps1, hvl2.trans hvl1, hti2.trans hti1,
      by rw [List.length_append]; omega, ?_, fun arr side idx hidx => ?_⟩
    · intro sw hsw
      rcases List.mem_append.mp hsw with h1 | h2
      · exact hsw1 sw h1
      · rw [hti1] at hsw2; exact hsw2 sw h2
    · rw [applySwaps_append, hvirt2 _ side idx (hvl1 ▸ hidx), hvirt1 arr side idx hidx]

private theorem runUnpermSteps_add_fst : ∀ (a b : ℕ) (w : PageUnpermState),
    (runUnpermSteps (a + b) w).1 = (runUnpermSteps b (runUnpermSteps a w).1).1
  | 0, b, w => by rw [Nat.zero_add]; rfl
  | a + 1, b, w => by rw [Nat.succ_add]; exact runUnpermSteps_add_fst a b w.unpermStep.1

private theorem runUnpermSteps_restores_valid_ge {K : ℕ} (hK : 512 ≤ K) {u : PageUnpermState}
    (hi : u.InvWithSlack 24) (hpos : 0 < u.cleanPhase) :
    (runUnpermSteps K u).1.Valid := by
  have hvalid_pres : ∀ m (w : PageUnpermState), w.Valid → (runUnpermSteps m w).1.Valid :=
    fun m _ hw => (runUnpermSteps_spec.{0} m hw).1
  by_cases hp1 : u.cleanPhase = 1
  · have hu0 : u.Valid :=
      ⟨hi.valid, hi.pageSize_ge, hi.phase_le, Nat.zero_le _, hi.phase0_wb, hi.src_empty,
        hi.prefix_fixed, hi.phase1_wb, fun h => absurd h (by omega), fun h => absurd h (by omega),
        fun h => absurd h (by omega), fun h => absurd h (by omega)⟩
    exact hvalid_pres K u hu0
  · by_cases hp2 : u.cleanPhase = 2
    · by_cases hoff0 : u.cleanOff = 0
      · have hu0 : u.Valid :=
          ⟨hi.valid, hi.pageSize_ge, hi.phase_le, Nat.zero_le _, hi.phase0_wb, hi.src_empty,
            hi.prefix_fixed, fun h => absurd h (by omega), hi.phase2_zero,
            fun _ hp => absurd hp (by omega),
            fun h => absurd h (by omega), fun h => absurd h (by omega)⟩
        exact hvalid_pres K u hu0
      · have hpos_off : 0 < u.cleanOff := Nat.pos_of_ne_zero hoff0
        obtain ⟨_, _, hoff_le, _, hpot⟩ := hi.phase2_pos hp2 hpos_off
        have hstep_adv : ∀ m (w : PageUnpermState),
            w.InvWithSlack 24 → w.cleanPhase = 2 → 0 < w.cleanOff →
            w.cleanOff + m ≤ w.st.pageSize →
            let w' := (runUnpermSteps m w).1
            w'.InvWithSlack 24 ∧ w'.cleanPhase = 2 ∧ w'.cleanOff = w.cleanOff + m ∧
            w'.st.phi = w.st.phi ∧ w'.st.pageSize = w.st.pageSize := by
          intro m
          induction m with
          | zero =>
            intro w hw hp2w _ _; exact ⟨hw, hp2w, (Nat.add_zero _).symm, rfl, rfl⟩
          | succ m ihm =>
            intro w hw hp2w hposw hlew
            dsimp only [runUnpermSteps]
            have hw1_spec := (unpermStep_spec.{0} hw).1
            have hltB : w.cleanOff < w.st.pageSize := by omega
            have hunp : w.unpermStep.1 = ⟨w.st, 2, w.cleanVp, w.cleanOff + 1⟩ := by
              unfold unpermStep; dsimp only
              rw [ite_eq_right (by omega), ite_eq_left hp2w, ite_eq_right (by omega),
                ite_eq_left hltB]
            rw [hunp] at hw1_spec ⊢
            obtain ⟨hi_m, hp2_m, hoff_m, hphi_m, hps_m⟩ :=
              ihm ⟨w.st, 2, w.cleanVp, w.cleanOff + 1⟩ hw1_spec rfl
                (by dsimp only; omega) (by dsimp only; omega)
            exact ⟨hi_m, hp2_m, by dsimp only at hoff_m; omega, hphi_m, hps_m⟩
        by_cases hsum : u.cleanOff + K ≤ u.st.pageSize
        · obtain ⟨hi_f, hp2_f, hoff_f, hphi_f, hps_f⟩ :=
            hstep_adv K u hi hp2 hpos_off hsum
          have hdiv32 : (u.st.pageSize - (u.cleanOff + K)) / 16 + 32 ≤
              (u.st.pageSize - u.cleanOff) / 16 := by
            have hle_num : (u.st.pageSize - (u.cleanOff + K)) + 16 * 32 ≤
                u.st.pageSize - u.cleanOff := by omega
            have hd := Nat.div_le_div_right (c := 16) hle_num
            rwa [Nat.add_mul_div_left _ _ (by decide : 0 < 16)] at hd
          refine ⟨hi_f.valid, hi_f.pageSize_ge, hi_f.phase_le, Nat.zero_le _,
            hi_f.phase0_wb, hi_f.src_empty, hi_f.prefix_fixed, hi_f.phase1_wb,
            hi_f.phase2_zero, fun h2 hp => ?_, fun h3 => absurd h3 (by omega), hi_f.phase4_id⟩
          obtain ⟨h1, h2', h3, h4, _⟩ := hi_f.phase2_pos h2 hp
          refine ⟨h1, h2', h3, h4, ?_⟩
          rw [hphi_f, hps_f, hoff_f]
          omega
        · set m := u.st.pageSize - u.cleanOff
          have hsplit : K = m + (1 + (K - 1 - m)) := by omega
          rw [hsplit, runUnpermSteps_add_fst m (1 + (K - 1 - m)) u,
            runUnpermSteps_add_fst 1 (K - 1 - m)]
          obtain ⟨hi_B, hp2_B, hoff_B, _, hps_B⟩ :=
            hstep_adv m u hi hp2 hpos_off (by omega)
          set wB := (runUnpermSteps m u).1
          have hw1 := (unpermStep_spec.{0} hi_B).1
          set wC := (runUnpermSteps 1 wB).1
          have hwC_off0 : wC.cleanOff = 0 ∧ (wC.cleanPhase = 1 ∨ wC.cleanPhase = 2) := by
            change wB.unpermStep.1.cleanOff = 0 ∧
              (wB.unpermStep.1.cleanPhase = 1 ∨ wB.unpermStep.1.cleanPhase = 2)
            unfold unpermStep; dsimp only
            have hB_pos : 0 < wB.st.pageSize := hi_B.valid.pageSize_pos
            rw [ite_eq_right (by omega), ite_eq_left hp2_B, ite_eq_right (by omega),
              ite_eq_right (by omega)]
            dsimp only
            exact ⟨rfl, by split_ifs <;> simp⟩
          have hwC_valid : wC.Valid :=
            ⟨hw1.valid, hw1.pageSize_ge, hw1.phase_le, Nat.zero_le _, hw1.phase0_wb,
              hw1.src_empty, hw1.prefix_fixed, hw1.phase1_wb, hw1.phase2_zero,
              fun _ hp => absurd hp (by omega), fun h => absurd h (by omega),
              fun h => absurd h (by omega)⟩
          exact hvalid_pres (K - 1 - m) wC hwC_valid
    · by_cases hp3 : u.cleanPhase = 3
      · obtain ⟨_, _, hvp_le, _, hpot⟩ := hi.phase3_inv hp3
        have hstep3 : ∀ m (w : PageUnpermState),
            w.InvWithSlack 24 → w.cleanPhase = 3 → w.cleanVp + m ≤ w.st.tailCount true →
            let w' := (runUnpermSteps m w).1
            w'.InvWithSlack 24 ∧ w'.cleanPhase = 3 ∧ w'.cleanVp = w.cleanVp + m ∧
            w'.st.tailCount true = w.st.tailCount true ∧
            w'.st.phi = w.st.phi ∧ w'.st.pageSize = w.st.pageSize := by
          intro m
          induction m with
          | zero =>
            intro w hw hp3w _; exact ⟨hw, hp3w, (Nat.add_zero _).symm, rfl, rfl, rfl⟩
          | succ m ihm =>
            intro w hw hp3w hlew
            dsimp only [runUnpermSteps]
            have hw1_spec := (unpermStep_spec.{0} hw).1
            have hlt_tc : w.cleanVp < w.st.tailCount true := by omega
            obtain ⟨hf0w, _⟩ := hw.src_empty (by omega)
            have htotPw : w.st.totalPages = w.st.fullPages true := by
              unfold PagePairState.totalPages; rw [hf0w, zero_add]
            obtain ⟨hps_eq, hfp_eq, htc_eq, _, _, _, _⟩ :=
              swapTailSlots_meta_eq w.st (w.st.tailPhys true w.cleanVp)
                (w.st.fullPages true * w.st.pageSize + w.cleanVp)
            have hunp : w.unpermStep.1 =
                ⟨(w.st.swapTailSlots (w.st.tailPhys true w.cleanVp)
                  (w.st.fullPages true * w.st.pageSize + w.cleanVp)).1,
                 3, w.cleanVp + 1, 0⟩ := by
              unfold unpermStep; dsimp only
              rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left hp3w,
                ite_eq_right (by omega)]
            rw [hunp] at hw1_spec ⊢
            have hphi_eq : (w.st.swapTailSlots (w.st.tailPhys true w.cleanVp)
                (w.st.fullPages true * w.st.pageSize + w.cleanVp)).1.phi = w.st.phi := by
              unfold PagePairState.phi; rw [hps_eq, hfp_eq, htc_eq]
            obtain ⟨hi_m, hp3_m, hvp_m, htc_m, hphi_m, hps_m⟩ :=
              ihm _ hw1_spec rfl (by dsimp only; rw [htc_eq]; omega)
            exact ⟨hi_m, hp3_m, by dsimp only at hvp_m; omega,
              htc_m.trans (by dsimp only; exact congrFun htc_eq true),
              hphi_m.trans hphi_eq, hps_m.trans (by dsimp only; exact hps_eq)⟩
        by_cases hsum : u.cleanVp + K ≤ u.st.tailCount true
        · obtain ⟨hi_f, hp3_f, hvp_f, htc_f, hphi_f, hps_f⟩ := hstep3 K u hi hp3 hsum
          refine ⟨hi_f.valid, hi_f.pageSize_ge, hi_f.phase_le, Nat.zero_le _,
            hi_f.phase0_wb, hi_f.src_empty, hi_f.prefix_fixed, hi_f.phase1_wb,
            hi_f.phase2_zero, fun h2 => absurd h2 (by omega), fun h3 => ?_, hi_f.phase4_id⟩
          obtain ⟨h1, h2, h3', h4, _⟩ := hi_f.phase3_inv h3
          refine ⟨h1, h2, h3', h4, ?_⟩
          rw [hphi_f, htc_f, hvp_f, hps_f]
          have hdiv32 : (u.st.tailCount true - (u.cleanVp + K)) / 16 + 32 ≤
              (u.st.tailCount true - u.cleanVp) / 16 := by
            have hle_num : (u.st.tailCount true - (u.cleanVp + K)) + 16 * 32 ≤
                u.st.tailCount true - u.cleanVp := by omega
            have hd := Nat.div_le_div_right (c := 16) hle_num
            rwa [Nat.add_mul_div_left _ _ (by decide : 0 < 16)] at hd
          omega
        · set m := u.st.tailCount true - u.cleanVp
          have hsplit : K = m + (1 + (K - 1 - m)) := by omega
          rw [hsplit, runUnpermSteps_add_fst m (1 + (K - 1 - m)) u,
            runUnpermSteps_add_fst 1 (K - 1 - m)]
          obtain ⟨hi_T, hp3_T, hvp_T, htc_T, _, _⟩ := hstep3 m u hi hp3 (by omega)
          set wT := (runUnpermSteps m u).1
          have hw1 := (unpermStep_spec.{0} hi_T).1
          set w4 := (runUnpermSteps 1 wT).1
          have hw4_ph : w4.cleanPhase = 4 := by
            change wT.unpermStep.1.cleanPhase = 4
            unfold unpermStep; dsimp only
            rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left hp3_T,
              ite_eq_left (by omega)]
          have hw4_valid : w4.Valid :=
            ⟨hw1.valid, hw1.pageSize_ge, hw1.phase_le, Nat.zero_le _,
              fun h => absurd h (by omega), hw1.src_empty, hw1.prefix_fixed,
              fun h => absurd h (by omega), fun h => absurd h (by omega),
              fun h => absurd h (by omega), fun h => absurd h (by omega), hw1.phase4_id⟩
          exact hvalid_pres (K - 1 - m) w4 hw4_valid
      · have hp4 : u.cleanPhase = 4 := by have := hi.phase_le; omega
        have hu0 : u.Valid :=
          ⟨hi.valid, hi.pageSize_ge, hi.phase_le, Nat.zero_le _,
            fun h => absurd h (by omega), hi.src_empty, hi.prefix_fixed,
            fun h => absurd h (by omega), fun h => absurd h (by omega),
            fun h => absurd h (by omega), fun h => absurd h (by omega), hi.phase4_id⟩
        exact hvalid_pres K u hu0

/-- Running `512` `unpermStep`s always restores resting `Valid` (`slack = 0`) from `InvWithSlack 24`
whenever `0 < u.cleanPhase`. -/
theorem runUnpermSteps_restores_valid {u : PageUnpermState}
    (hi : u.InvWithSlack 24) (hpos : 0 < u.cleanPhase) :
    (runUnpermSteps 512 u).1.Valid :=
  runUnpermSteps_restores_valid_ge le_rfl hi hpos

/-- Raw append validity under `16 * st.phi ≤ 25 * st.pageSize` and `tailCount false = 0`. -/
private theorem rawAppend_true_valid_of_phi {st : PagePairState} (hv : st.Valid)
    (hB32 : 32 ≤ st.pageSize) (ht0 : st.tailCount false = 0)
    (hphi : 16 * st.phi ≤ 25 * st.pageSize) :
    let st_r := st.rawAppend true
    st_r.Valid ∧
    st_r.phi ≤ st.phi + 1 ∧
    st_r.virtLen true = st.virtLen true + 1 ∧
    st_r.virtLen false = st.virtLen false ∧
    st_r.totalItems = st.totalItems + 1 ∧
    st_r.tailPhys true (st.tailCount true) = st.totalItems ∧
    (∀ s t, t < st.tailCount s → st_r.tailPhys s t = st.tailPhys s t) := by
  intro st_r
  have hB := hv.pageSize_pos
  have hr_add_lt : st.tailCount true + 1 < 4 * st.pageSize := by
    unfold PagePairState.phi PagePairState.dev at hphi; omega
  have hts_add_lt : st_r.tailCount false + st_r.tailCount true < 8 * st.pageSize := by
    dsimp only [st_r, PagePairState.rawAppend]
    simp only [Function.update_of_ne (by decide : false ≠ true), Function.update_self, ht0]; omega
  have hvl_t : st_r.virtLen true = st.virtLen true + 1 := by
    dsimp only [st_r, PagePairState.rawAppend, PagePairState.virtLen]
    rw [Function.update_self]; omega
  have hvl_f : st_r.virtLen false = st.virtLen false := by
    dsimp only [st_r, PagePairState.rawAppend, PagePairState.virtLen]
    rw [Function.update_of_ne (by decide)]
  have hti_r : st_r.totalItems = st.totalItems + 1 := by
    dsimp only [PagePairState.totalItems]; rw [hvl_f, hvl_t]; omega
  have hk_ne_old : ∀ t < st.tailCount true,
      st.ringSlot true t ≠ st.ringSlot true (st.tailCount true) := by
    intro t ht heq
    have r1 := ringIdxOfSlot_mod (head := st.tailHead true) hB (by omega : t < 4 * st.pageSize)
    have r2 := ringIdxOfSlot_mod (head := st.tailHead true) hB
      (by omega : st.tailCount true < 4 * st.pageSize)
    change ringIdxOfSlot (st.tailHead true) st.pageSize (st.ringSlot true t) = t at r1
    change ringIdxOfSlot (st.tailHead true) st.pageSize
      (st.ringSlot true (st.tailCount true)) = st.tailCount true at r2
    rw [heq, r2] at r1; omega
  have htot_lo : st.totalPages * st.pageSize ≤ st.totalItems := by rw [st.totalItems_eq]; omega
  have htot_hi8 : st.totalItems < st.totalPages * st.pageSize + 8 * st.pageSize := by
    rw [st.totalItems_eq]; omega
  have hres_ne_old : ∀ p, st.totalPages * st.pageSize ≤ p → p < st.totalItems →
      p % (8 * st.pageSize) ≠ st.totalItems % (8 * st.pageSize) := fun p hplo hphi_p heq => by
    have := mod_inj_of_range (by positivity : 0 < 8 * st.pageSize) hplo
      (hphi_p.trans htot_hi8) htot_lo htot_hi8 heq
    omega
  have htp_r_old : ∀ s t, t < st.tailCount s → st_r.tailPhys s t = st.tailPhys s t := by
    intro s t ht
    have hc : ¬(s = true ∧ st.ringSlot s t = st.ringSlot true (st.tailCount true)) := by
      rintro ⟨rfl, hr⟩; exact hk_ne_old t ht hr
    change physOfRes (st.totalPages * st.pageSize) st.pageSize
      (PagePairState.set2 st.tailRes true (st.ringSlot true (st.tailCount true))
        (st.totalItems % (8 * st.pageSize)) s (st.ringSlot s t)) = _
    rw [PagePairState.set2_of_ne _ _ _ _ _ _ hc]; rfl
  have htp_r_new : st_r.tailPhys true (st.tailCount true) = st.totalItems := by
    change physOfRes (st.totalPages * st.pageSize) st.pageSize
      (PagePairState.set2 st.tailRes true (st.ringSlot true (st.tailCount true))
        (st.totalItems % (8 * st.pageSize)) true (st.ringSlot true (st.tailCount true))) = _
    rw [PagePairState.set2_self]
    exact physOfRes_mod hB htot_lo htot_hi8
  have hv_r : st_r.Valid := by
    refine ⟨hB, ?_, hts_add_lt, hv.tailHead_lt, hv.page_lt, hv.owner_pageOf, hv.pageOf_owner,
      ?_, ?_, ?_, ?_⟩
    · intro s; dsimp only [st_r, PagePairState.rawAppend]
      cases s
      · rw [Function.update_of_ne (by decide)]; exact hv.tailCount_lt false
      · rw [Function.update_self]; exact hr_add_lt
    · intro s t ht
      change PagePairState.set2 st.tailRes true (st.ringSlot true (st.tailCount true))
        (st.totalItems % (8 * st.pageSize)) s (st.ringSlot s t) < 8 * st.pageSize
      by_cases hc : s = true ∧ t = st.tailCount true
      · obtain ⟨rfl, rfl⟩ := hc; rw [PagePairState.set2_self]; exact Nat.mod_lt _ (by positivity)
      · have ht' : t < st.tailCount s := by
          dsimp only [st_r, PagePairState.rawAppend] at ht
          cases s
          · rwa [Function.update_of_ne (by decide)] at ht
          · rw [Function.update_self] at ht; have : t ≠ st.tailCount true := fun h => hc ⟨rfl, h⟩
            omega
        rw [PagePairState.set2_of_ne _ _ _ _ _ _ (by rintro ⟨rfl, hr⟩; exact hk_ne_old t ht' hr)]
        exact hv.tailRes_lt s t ht'
    · intro s t ht; rw [hti_r]
      by_cases hc : s = true ∧ t = st.tailCount true
      · obtain ⟨rfl, rfl⟩ := hc; rw [htp_r_new]; exact Nat.lt_succ_self _
      · have ht' : t < st.tailCount s := by
          dsimp only [st_r, PagePairState.rawAppend] at ht
          cases s
          · rwa [Function.update_of_ne (by decide)] at ht
          · rw [Function.update_self] at ht; have : t ≠ st.tailCount true := fun h => hc ⟨rfl, h⟩
            omega
        rw [htp_r_old s t ht']; exact (hv.tail_lt s t ht').trans (Nat.lt_succ_self _)
    · intro s t ht
      rw [show st_r.ringSlot s t = st.ringSlot s t from rfl]
      by_cases hc : s = true ∧ t = st.tailCount true
      · obtain ⟨rfl, rfl⟩ := hc; dsimp only [st_r, PagePairState.rawAppend]
        rw [PagePairState.set2_self]; exact ⟨Function.update_self .., Function.update_self ..⟩
      · have ht' : t < st.tailCount s := by
          dsimp only [st_r, PagePairState.rawAppend] at ht
          cases s
          · rwa [Function.update_of_ne (by decide)] at ht
          · rw [Function.update_self] at ht; have : t ≠ st.tailCount true := fun h => hc ⟨rfl, h⟩
            omega
        have hp_lo : st.totalPages * st.pageSize ≤ st.tailPhys s t := le_physOfRes _ _ _
        have hp_hi : st.tailPhys s t < st.totalItems := hv.tail_lt s t ht'
        have hmod := mod_physOfRes (base := st.totalPages * st.pageSize) (hv.tailRes_lt s t ht')
        change st.tailPhys s t % (8 * st.pageSize) = _ at hmod
        have hnr : st.tailRes s (st.ringSlot s t) ≠ st.totalItems % (8 * st.pageSize) := by
          rw [← hmod]; exact hres_ne_old _ hp_lo hp_hi
        dsimp only [st_r, PagePairState.rawAppend]
        rw [PagePairState.set2_of_ne _ _ _ _ _ _ (by rintro ⟨rfl, hr⟩; exact hk_ne_old t ht' hr),
          Function.update_of_ne hnr, Function.update_of_ne hnr]
        exact hv.owner_tail s t ht'
    · intro p hplo hphi_p; rw [hti_r] at hphi_p
      change st.totalPages * st.pageSize ≤ p at hplo
      by_cases hp_eq : p = st.totalItems
      · subst hp_eq; dsimp only [st_r, PagePairState.rawAppend]
        rw [Function.update_self, Function.update_self, Function.update_self]
        unfold PagePairState.ringSlot
        rw [ringIdxOfSlot_mod hB (by omega)]
        exact ⟨Nat.mod_lt _ (by positivity), Nat.lt_succ_self _, htp_r_new⟩
      · have hp_lt : p < st.totalItems := by omega
        have hnr := hres_ne_old p hplo hp_lt
        obtain ⟨hkp, htp, htpp⟩ := hv.tail_owner p hplo hp_lt
        dsimp only [st_r, PagePairState.rawAppend]
        rw [Function.update_of_ne hnr, Function.update_of_ne hnr]
        refine ⟨hkp, ?_, (htp_r_old _ _ htp).trans htpp⟩
        cases hs : st.tailOwnerSide (p % (8 * st.pageSize))
        · rw [Function.update_of_ne (by decide)]; rwa [hs] at htp
        · rw [Function.update_self]; rw [hs] at htp; omega
  have hphi_r : st_r.phi ≤ st.phi + 1 := by
    unfold PagePairState.phi PagePairState.dev; dsimp only [st_r, PagePairState.rawAppend]
    simp only [Function.update_self, Function.update_of_ne (by decide : false ≠ true)]
    split_ifs <;> omega
  exact ⟨hv_r, hphi_r, hvl_t, hvl_f, hti_r, htp_r_new, htp_r_old⟩

/-- Raw popBack validity under `16 * st.phi ≤ 25 * st.pageSize`, `fullPages false = 0`,
`tailCount false = 0`, and `0 < st.virtLen true`. -/
private theorem rawPopBack_true_valid_of_phi {st : PagePairState} (hv : st.Valid)
    (hB32 : 32 ≤ st.pageSize) (hf0 : st.fullPages false = 0) (ht0 : st.tailCount false = 0)
    (hphi : 16 * st.phi ≤ 25 * st.pageSize) (hpos : 0 < st.virtLen true) :
    let res := st.rawPopBack true
    let st_r := res.1
    let sws₀ := res.2
    st_r.Valid ∧
    st_r.phi ≤ st.phi + 1 ∧
    st_r.pageSize = st.pageSize ∧
    st_r.fullPages = st.fullPages ∧
    st_r.tailCount true = st.tailCount true - 1 ∧
    st_r.tailCount false = 0 ∧
    st_r.pageOf = st.pageOf ∧
    st_r.job = st.job ∧
    st_r.virtLen true = st.virtLen true - 1 ∧
    st_r.virtLen false = 0 ∧
    st_r.totalItems = st.totalItems - 1 ∧
    sws₀.length ≤ 1 ∧
    (∀ sw ∈ sws₀, st.totalPages * st.pageSize ≤ sw.p₁ ∧ sw.p₁ < st.totalItems ∧
      st.totalPages * st.pageSize ≤ sw.p₂ ∧ sw.p₂ < st.totalItems) ∧
    (∀ t < st.tailCount true - 1,
      (∀ u < t + 1, st.tailPhys true u = st.fullPages true * st.pageSize + u) →
      st_r.tailPhys true t = st.fullPages true * st.pageSize + t) ∧
    (∀ {α : Type*} (arr : ℕ → α) (s : Bool) (idx : ℕ), idx < st_r.virtLen s →
      st_r.virtAt (applySwaps sws₀ arr) s idx = st.virtAt arr s idx) := by
  dsimp only [PagePairState.rawPopBack]
  have hB := hv.pageSize_pos
  have hr_pos : 0 < st.tailCount true := by
    by_cases hq : 0 < st.fullPages true
    · unfold PagePairState.phi PagePairState.dev at hphi
      simp only [hq, ↓reduceIte] at hphi; omega
    · have hq0 : st.fullPages true = 0 := by omega
      unfold PagePairState.virtLen at hpos; rw [hq0, zero_mul, zero_add] at hpos; exact hpos
  have hvl_f0 : st.virtLen false = 0 := by
    unfold PagePairState.virtLen; rw [hf0, ht0, zero_mul, add_zero]
  have htot_eq : st.totalItems = st.virtLen true := by
    unfold PagePairState.totalItems; rw [hvl_f0, zero_add]
  have htot_pos : 0 < st.totalItems := htot_eq ▸ hpos
  have hp1_lo : st.totalPages * st.pageSize ≤ st.tailPhys true (st.tailCount true - 1) :=
    le_physOfRes _ _ _
  have hp1_hi : st.tailPhys true (st.tailCount true - 1) < st.totalItems :=
    hv.tail_lt true (st.tailCount true - 1) (by omega)
  have hp2_lo : st.totalPages * st.pageSize ≤ st.totalItems - 1 := by
    rw [st.totalItems_eq]; omega
  have hp2_hi : st.totalItems - 1 < st.totalItems := by omega
  obtain ⟨hv1, hps1, hfp1, htc1, _, hpo1, _, _, hj1, hsw0_len, _, htp_f, hvirt0⟩ :=
    PagePairState.swapTailSlots_spec hv hp1_lo hp1_hi hp2_lo hp2_hi
  set st₁ := (st.swapTailSlots (st.tailPhys true (st.tailCount true - 1)) (st.totalItems - 1)).1
  set sws₀ := (st.swapTailSlots (st.tailPhys true (st.tailCount true - 1)) (st.totalItems - 1)).2
  set st_r : PagePairState :=
    { st₁ with tailCount := Function.update st₁.tailCount true (st.tailCount true - 1) }
  have hsw_bounds : ∀ sw ∈ sws₀, st.totalPages * st.pageSize ≤ sw.p₁ ∧ sw.p₁ < st.totalItems ∧
      st.totalPages * st.pageSize ≤ sw.p₂ ∧ sw.p₂ < st.totalItems := by
    intro sw hsw; dsimp only [sws₀, PagePairState.swapTailSlots] at hsw
    split_ifs at hsw with heq
    · cases hsw
    · simp only [List.mem_singleton] at hsw; subst hsw
      exact ⟨hp1_lo, hp1_hi, hp2_lo, hp2_hi⟩
  have hti1 : st₁.totalItems = st.totalItems := by
    unfold PagePairState.totalItems PagePairState.virtLen; rw [hps1, hfp1, htc1]
  have htp_last : st₁.tailPhys true (st.tailCount true - 1) = st.totalItems - 1 := by
    rw [htp_f true (st.tailCount true - 1) (by omega), ite_eq_left rfl]
  have hvl_r_t : st_r.virtLen true = st.virtLen true - 1 := by
    unfold PagePairState.virtLen; dsimp only [st_r]; rw [hps1, hfp1, Function.update_self]; omega
  have hvl_r_f : st_r.virtLen false = 0 := by
    unfold PagePairState.virtLen; dsimp only [st_r]
    rw [hps1, hfp1, Function.update_of_ne (by decide), htc1]; exact hvl_f0
  have hti_r : st_r.totalItems = st.totalItems - 1 := by
    unfold PagePairState.totalItems; rw [hvl_r_f, hvl_r_t, hvl_f0]; omega
  have hv_r : st_r.Valid := by
    refine ⟨hps1 ▸ hB, ?_, ?_, hv1.tailHead_lt, hv1.page_lt, hv1.owner_pageOf, hv1.pageOf_owner,
      ?_, ?_, ?_, ?_⟩
    · intro s; dsimp only [st_r]; rw [hps1]
      cases s
      · rw [Function.update_of_ne (by decide), htc1]; exact hv.tailCount_lt false
      · rw [Function.update_self]; have := hv.tailCount_lt true; omega
    · dsimp only [st_r]; rw [hps1, htc1]; have := hv.tailSum_lt; simp; omega
    · intro s t ht
      have ht1 : t < st₁.tailCount s := by
        dsimp only [st_r] at ht; cases s
        · rwa [Function.update_of_ne (by decide)] at ht
        · rw [Function.update_self] at ht; rw [htc1]; omega
      exact hv1.tailRes_lt s t ht1
    · intro s t ht; rw [hti_r]
      change st₁.tailPhys s t < _
      have ht1 : t < st₁.tailCount s := by
        dsimp only [st_r] at ht; cases s
        · rwa [Function.update_of_ne (by decide)] at ht
        · rw [Function.update_self] at ht; rw [htc1]; omega
      have hp_lt := hv1.tail_lt s t ht1; rw [hti1] at hp_lt
      have hp_ne : st₁.tailPhys s t ≠ st.totalItems - 1 := by
        intro heq; rw [← htp_last] at heq
        have hi1 : st₁.fullPages s * st₁.pageSize + t < st₁.virtLen s := by
          unfold PagePairState.virtLen; omega
        have hi2 : st₁.fullPages true * st₁.pageSize + (st.tailCount true - 1) <
            st₁.virtLen true := by unfold PagePairState.virtLen; rw [htc1]; omega
        have htp1 : st₁.toPhys s (st₁.fullPages s * st₁.pageSize + t) = st₁.tailPhys s t := by
          unfold PagePairState.toPhys; dsimp only
          rw [ite_eq_right (by omega), Nat.add_sub_cancel_left]
        have htp2 : st₁.toPhys true (st₁.fullPages true * st₁.pageSize + (st.tailCount true - 1)) =
            st₁.tailPhys true (st.tailCount true - 1) := by
          unfold PagePairState.toPhys; dsimp only
          rw [ite_eq_right (by omega), Nat.add_sub_cancel_left]
        obtain ⟨hse, _⟩ := hv1.toPhys_inj hi1 hi2 (by rw [htp1, htp2, heq])
        subst hse; dsimp only [st_r] at ht; rw [Function.update_self] at ht; omega
      omega
    · intro s t ht
      have ht1 : t < st₁.tailCount s := by
        dsimp only [st_r] at ht; cases s
        · rwa [Function.update_of_ne (by decide)] at ht
        · rw [Function.update_self] at ht; rw [htc1]; omega
      exact hv1.owner_tail s t ht1
    · intro p hplo hphi_p; rw [hti_r] at hphi_p
      obtain ⟨hkp, htp, htpp⟩ := hv1.tail_owner p hplo (by rw [hti1]; omega)
      dsimp only [st_r]
      refine ⟨hkp, ?_, htpp⟩
      cases hs : st₁.tailOwnerSide (p % (8 * st₁.pageSize))
      · rw [Function.update_of_ne (by decide)]; rwa [hs] at htp
      · rw [Function.update_self]; rw [hs] at htp htpp
        have hne_t : ringIdxOfSlot (st₁.tailHead true) st₁.pageSize
            (st₁.tailOwnerRing (p % (8 * st₁.pageSize))) ≠ st.tailCount true - 1 := by
          intro heq; rw [heq, htp_last] at htpp; omega
        rw [htc1] at htp; omega
  have hphi_r : st_r.phi ≤ st.phi + 1 := by
    unfold PagePairState.phi PagePairState.dev; dsimp only [st_r]; rw [hps1, hfp1, htc1]
    simp only [Function.update_self, Function.update_of_ne (by decide : false ≠ true)]
    split_ifs <;> omega
  refine ⟨hv_r, hphi_r, hps1, hfp1, Function.update_self ..,
    by rw [Function.update_of_ne (by decide), htc1]; exact ht0,
    hpo1, hj1, hvl_r_t, hvl_r_f, hti_r, hsw0_len, hsw_bounds,
    fun t ht hpref_t => ?_, fun arr s idx hidx => ?_⟩
  · change st₁.tailPhys true t = _
    rw [htp_f true t (by omega)]
    have ht_eq := hpref_t t (Nat.lt_succ_self t)
    have htot_val : st.totalItems = st.fullPages true * st.pageSize + st.tailCount true := by
      rw [htot_eq]; rfl
    have hne2 : st.tailPhys true t ≠ st.totalItems - 1 := by omega
    have hne1 : st.tailPhys true t ≠ st.tailPhys true (st.tailCount true - 1) := by
      intro heq
      have hi1 : st.fullPages true * st.pageSize + t < st.virtLen true := by
        unfold PagePairState.virtLen; omega
      have hi2 : st.fullPages true * st.pageSize + (st.tailCount true - 1) < st.virtLen true := by
        unfold PagePairState.virtLen; omega
      have htp1 : st.toPhys true (st.fullPages true * st.pageSize + t) = st.tailPhys true t := by
        unfold PagePairState.toPhys; dsimp only
        rw [ite_eq_right (by omega), Nat.add_sub_cancel_left]
      have htp2 : st.toPhys true (st.fullPages true * st.pageSize + (st.tailCount true - 1)) =
          st.tailPhys true (st.tailCount true - 1) := by
        unfold PagePairState.toPhys; dsimp only
        rw [ite_eq_right (by omega), Nat.add_sub_cancel_left]
      obtain ⟨_, _⟩ := hv.toPhys_inj hi1 hi2 (by rw [htp1, htp2, heq])
      omega
    rw [ite_eq_right hne1, ite_eq_right hne2, ht_eq]
  · have hidx_old : idx < st.virtLen s := by
      cases s
      · rw [hvl_r_f] at hidx; exact absurd hidx (Nat.not_lt_zero _)
      · rw [hvl_r_t] at hidx; omega
    exact hvirt0 arr s idx hidx_old

/-- **`appendSlot` Preservation & Virtual-Array Specification (`appendSlot_spec`).**
When `u.Valid` and `(0 < u.cleanPhase → side = true) ∧ u.cleanPhase < 4`, `appendSlot u side`
yields `u'.InvWithSlack 24` (and `u'.Valid` directly when `u.cleanPhase = 0`), emits `≤ 16` swaps
inside `[0, u.st.totalItems + 1)`, maps `(side, u.st.virtLen side)` to `arr u.st.totalItems`, and
preserves every existing coordinate `(s, idx)`. -/
theorem appendSlot_spec {u : PageUnpermState} {side : Bool} (hv : u.Valid)
    (hside : 0 < u.cleanPhase → side = true) (hph_lt : u.cleanPhase < 4) :
    let res := u.appendSlot side
    let u' := res.1
    let sws := res.2
    u'.InvWithSlack (if u.cleanPhase = 0 then 0 else 24) ∧
    (0 < u.cleanPhase → 0 < u'.cleanPhase) ∧
    u'.st.pageSize = u.st.pageSize ∧
    u'.st.virtLen side = u.st.virtLen side + 1 ∧
    (∀ s ≠ side, u'.st.virtLen s = u.st.virtLen s) ∧
    u'.st.totalItems = u.st.totalItems + 1 ∧
    sws.length ≤ 16 ∧
    (∀ sw ∈ sws, sw.p₁ < u.st.totalItems + 1 ∧ sw.p₂ < u.st.totalItems + 1) ∧
    (∀ {α : Type*} (arr : ℕ → α) (s : Bool) (idx : ℕ), idx < u'.st.virtLen s →
      u'.virtAt (applySwaps sws arr) s idx =
        if s = side ∧ idx = u.st.virtLen side then arr u.st.totalItems
        else u.virtAt arr s idx) := by
  dsimp only
  unfold appendSlot
  by_cases hp0 : u.cleanPhase = 0
  · rw [ite_eq_left hp0]
    dsimp only
    obtain ⟨hwb, _, _⟩ := hv.phase0_wb hp0
    obtain ⟨hwb', hps', hvl_s, hvl_o, hti', hlen', hsw', hvirt'⟩ :=
      PagePairState.stepAppend_spec hwb side
    have hu' : (ofPagePair (u.st.stepAppend side).1).Valid := valid_ofPagePair hwb'
    dsimp only [ofPagePair] at hu'
    have hnot_u : ¬(u.cleanPhase = 2 ∧ 0 < u.cleanOff) := by omega
    have hnot_u' : ¬((0 : ℕ) = 2 ∧ 0 < (0 : ℕ)) := by simp
    refine ⟨by simpa only [hp0, ↓reduceIte] using hu', fun h => absurd h (by omega),
      hps', hvl_s, hvl_o, hti', hlen', hsw', fun arr s idx hidx => ?_⟩
    simp only [virtAt,
      toPhys_of_not_cleanSwap ⟨(u.st.stepAppend side).1, 0, 0, 0⟩ hnot_u',
      toPhys_of_not_cleanSwap u hnot_u]
    exact hvirt' arr s idx hidx
  · rw [ite_eq_right hp0]
    have hp_pos : 0 < u.cleanPhase := Nat.pos_of_ne_zero hp0
    have hs_true : side = true := hside hp_pos
    subst hs_true
    obtain ⟨hf0, ht0⟩ := hv.src_empty hp_pos
    by_cases hwb_br : u.cleanPhase = 1 ∨ (u.cleanPhase = 2 ∧ u.cleanOff = 0)
    · rw [ite_eq_left hwb_br]
      dsimp only
      have hwb : u.st.WellBalanced := by
        rcases hwb_br with h1 | ⟨h2, h0⟩
        · exact (hv.phase1_wb h1).1
        · exact (hv.phase2_zero h2 h0).1
      have hvp_le : u.cleanVp ≤ u.st.fullPages true := by
        rcases hwb_br with h1 | ⟨h2, h0⟩
        · exact (hv.phase1_wb h1).2.1
        · exact (hv.phase2_zero h2 h0).2.2
      have hpref0 : ∀ vp < u.cleanVp, u.st.pageOf true vp = vp := fun vp hvp => by
        have hp := hv.prefix_fixed hp_pos vp
        rw [ite_eq_left (by rcases hwb_br with h1 | ⟨h2, _⟩ <;> omega)] at hp
        exact hp hvp
      obtain ⟨hwb', hps', hvl_s, hvl_o, hti', hlen', hsw', hvirt'⟩ :=
        PagePairState.stepAppend_spec hwb true
      have hpf0 := PrefixFixed.of_valid hv.valid hf0 ht0 hwb.jobValid hvp_le hpref0
      have hpf' := hpf0.rawAppend_true.maybeStartJob.runTicks 16
      set st' := (u.st.stepAppend true).1
      set ph' := if st'.job = .idle then 2 else 1
      have hnot_u : ¬(u.cleanPhase = 2 ∧ 0 < u.cleanOff) := by
        rcases hwb_br with h1 | ⟨_, h0⟩ <;> omega
      have hnot_u' : ¬(ph' = 2 ∧ 0 < (0 : ℕ)) := by simp
      refine ⟨?_, fun _ => by dsimp only [ph']; split_ifs <;> decide,
        hps', hvl_s, hvl_o, hti', hlen', hsw', fun arr s idx hidx => ?_⟩
      · rw [ite_eq_right hp0]
        refine ⟨hwb'.valid, hps' ▸ hv.pageSize_ge, by dsimp only [ph']; split_ifs <;> decide,
          by decide, fun h => absurd h (by dsimp only [ph']; split_ifs <;> decide),
          fun _ => ⟨hpf'.fp_false, hpf'.tc_false⟩,
          fun _ vp hvp => ?_,
          fun _ => ⟨hwb', min_le_right _ _, rfl⟩,
          fun h2 _ => (by
            dsimp only [ph'] at h2
            by_cases hj' : st'.job = .idle
            · exact ⟨hwb', hj', min_le_right _ _⟩
            · rw [ite_eq_right hj'] at h2; cases h2),
          fun _ hp => absurd hp (Nat.lt_irrefl 0),
          fun h => absurd h (by dsimp only [ph']; split_ifs <;> decide),
          fun h => absurd h (by dsimp only [ph']; split_ifs <;> decide)⟩
        dsimp only at hvp
        have hle2 : ph' ≤ 2 := by dsimp only [ph']; split_ifs <;> decide
        rw [ite_eq_left hle2] at hvp
        exact (hpf'.fixed_lt vp hvp).1
      · simp only [virtAt,
          toPhys_of_not_cleanSwap ⟨st', ph', min u.cleanVp (st'.fullPages true), 0⟩ hnot_u',
          toPhys_of_not_cleanSwap u hnot_u]
        exact hvirt' arr s idx hidx
    · rw [ite_eq_right hwb_br]
      dsimp only
      have h23 : (u.cleanPhase = 2 ∧ 0 < u.cleanOff) ∨ u.cleanPhase = 3 := by omega
      have hphi25 : 16 * u.st.phi ≤ 25 * u.st.pageSize := by
        rcases h23 with ⟨h2, ho⟩ | h3
        · have := (hv.phase2_pos h2 ho).2.2.2.2; omega
        · have := (hv.phase3_inv h3).2.2.2.2; omega
      obtain ⟨hv_r, hphi_r, hvl_t, hvl_f, hti_r, htp_new, htp_old⟩ :=
        rawAppend_true_valid_of_phi hv.valid hv.pageSize_ge ht0 hphi25
      set st_r := u.st.rawAppend true
      refine ⟨?_, fun _ => hp_pos, rfl, hvl_t,
        fun s hs => by cases s <;> [exact hvl_f; exact absurd rfl hs],
        hti_r, Nat.zero_le _, by simp, fun arr s idx hidx => ?_⟩
      · rw [ite_eq_right hp0]
        refine ⟨hv_r, hv.pageSize_ge, hv.phase_le, by decide,
          fun h => absurd h hp0,
          fun _ => ⟨hf0, by dsimp only [st_r, PagePairState.rawAppend]; simp [ht0]⟩,
          hv.prefix_fixed,
          fun h1 => absurd (Or.inl h1) hwb_br,
          fun h2 h0 => absurd (Or.inr ⟨h2, h0⟩) hwb_br,
          fun h2 ho => ?_, fun h3 => ?_, fun h4 => absurd h4 (by dsimp only; omega)⟩
        · obtain ⟨hj, hvp_lt, hoff_le, hP_ne, hpot⟩ := hv.phase2_pos h2 ho
          refine ⟨hj, hvp_lt, hoff_le, hP_ne, ?_⟩
          change 16 * st_r.phi + (u.st.pageSize - u.cleanOff) / 16 ≤ 25 * u.st.pageSize + 24
          omega
        · obtain ⟨hj, hoff0, hvp_le, htail_id, hpot⟩ := hv.phase3_inv h3
          refine ⟨hj, hoff0, ?_, fun t ht => ?_, ?_⟩
          · dsimp only [st_r, PagePairState.rawAppend]; rw [Function.update_self]; omega
          · rw [htp_old true t (ht.trans_le hvp_le)]; exact htail_id t ht
          · dsimp only [st_r, PagePairState.rawAppend]; rw [Function.update_self]
            have hdiv_add : (u.st.tailCount true + 1 - u.cleanVp) / 16 ≤
                (u.st.tailCount true - u.cleanVp) / 16 + 1 := by omega
            change 16 * st_r.phi + _ ≤ _
            omega
      · simp only [applySwaps_nil]
        by_cases hc : s = true ∧ idx = u.st.virtLen true
        · obtain ⟨rfl, rfl⟩ := hc
          rw [ite_eq_left ⟨rfl, rfl⟩]
          unfold virtAt toPhys; dsimp only [st_r, PagePairState.rawAppend]
          have hnot_lt : ¬(u.st.virtLen true < u.st.fullPages true * u.st.pageSize) := by
            unfold PagePairState.virtLen; omega
          rw [ite_eq_right hnot_lt]
          have hsub : u.st.virtLen true - u.st.fullPages true * u.st.pageSize =
              u.st.tailCount true := by unfold PagePairState.virtLen; omega
          change arr (st_r.tailPhys true _) = _
          rw [hsub, htp_new]
        · rw [ite_eq_right hc]
          have hidx_old : idx < u.st.virtLen s := by
            cases s
            · rwa [hvl_f] at hidx
            · rw [hvl_t] at hidx
              have : idx ≠ u.st.virtLen true := fun h => hc ⟨rfl, h⟩
              omega
          unfold virtAt toPhys; dsimp only
          have hfp_eq : st_r.fullPages s = u.st.fullPages s := rfl
          have hps_eq : st_r.pageSize = u.st.pageSize := rfl
          rw [hfp_eq, hps_eq]
          split_ifs with hlt
          · congr 2
          · have ht_lt : idx - u.st.fullPages s * u.st.pageSize < u.st.tailCount s := by
              unfold PagePairState.virtLen at hidx_old; omega
            exact congrArg arr (htp_old s _ ht_lt)

/-- **`popBackSlot` Preservation & Virtual-Array Specification (`popBackSlot_spec`).**
When `u.Valid`, `0 < u.st.virtLen side`, `(0 < u.cleanPhase → side = true)`, and
`u.cleanPhase < 4`, `popBackSlot u side` yields `u'.InvWithSlack (if u.cleanPhase = 0 then 0 else
24)`, emits `≤ 17` swaps inside `[0, u.st.totalItems)`, and preserves every surviving coordinate
`(s, idx)` (`idx < u'.st.virtLen s`). -/
theorem popBackSlot_spec {u : PageUnpermState} {side : Bool} (hv : u.Valid)
    (hpos : 0 < u.st.virtLen side)
    (hside : 0 < u.cleanPhase → side = true) (hph_lt : u.cleanPhase < 4) :
    let res := u.popBackSlot side
    let u' := res.1
    let sws := res.2
    u'.InvWithSlack (if u.cleanPhase = 0 then 0 else 24) ∧
    (0 < u.cleanPhase → 0 < u'.cleanPhase) ∧
    u'.st.pageSize = u.st.pageSize ∧
    u'.st.virtLen side = u.st.virtLen side - 1 ∧
    (∀ s ≠ side, u'.st.virtLen s = u.st.virtLen s) ∧
    u'.st.totalItems = u.st.totalItems - 1 ∧
    sws.length ≤ 17 ∧
    (∀ sw ∈ sws, sw.p₁ < u.st.totalItems ∧ sw.p₂ < u.st.totalItems) ∧
    (∀ {α : Type*} (arr : ℕ → α) (s : Bool) (idx : ℕ), idx < u'.st.virtLen s →
      u'.virtAt (applySwaps sws arr) s idx = u.virtAt arr s idx) := by
  dsimp only
  unfold popBackSlot
  by_cases hp0 : u.cleanPhase = 0
  · rw [ite_eq_left hp0]
    dsimp only
    obtain ⟨hwb, _, _⟩ := hv.phase0_wb hp0
    obtain ⟨hwb', hps', hvl_s, hvl_o, hti', hlen', hsw', hvirt'⟩ :=
      PagePairState.stepPopBack_spec hwb hpos
    have hu' : (ofPagePair (u.st.stepPopBack side).1).Valid := valid_ofPagePair hwb'
    dsimp only [ofPagePair] at hu'
    have hnot_u : ¬(u.cleanPhase = 2 ∧ 0 < u.cleanOff) := by omega
    have hnot_u' : ¬((0 : ℕ) = 2 ∧ 0 < (0 : ℕ)) := by simp
    refine ⟨by simpa only [hp0, ↓reduceIte] using hu', fun h => absurd h (by omega),
      hps', hvl_s, hvl_o, hti', hlen', hsw', fun arr s idx hidx => ?_⟩
    simp only [virtAt,
      toPhys_of_not_cleanSwap ⟨(u.st.stepPopBack side).1, 0, 0, 0⟩ hnot_u',
      toPhys_of_not_cleanSwap u hnot_u]
    exact hvirt' arr s idx hidx
  · rw [ite_eq_right hp0]
    have hp_pos : 0 < u.cleanPhase := Nat.pos_of_ne_zero hp0
    have hs_true : side = true := hside hp_pos
    subst hs_true
    obtain ⟨hf0, ht0⟩ := hv.src_empty hp_pos
    by_cases hwb_br : u.cleanPhase = 1 ∨ (u.cleanPhase = 2 ∧ u.cleanOff = 0)
    · rw [ite_eq_left hwb_br]
      dsimp only
      have hwb : u.st.WellBalanced := by
        rcases hwb_br with h1 | ⟨h2, h0⟩
        · exact (hv.phase1_wb h1).1
        · exact (hv.phase2_zero h2 h0).1
      have hvp_le : u.cleanVp ≤ u.st.fullPages true := by
        rcases hwb_br with h1 | ⟨h2, h0⟩
        · exact (hv.phase1_wb h1).2.1
        · exact (hv.phase2_zero h2 h0).2.2
      have hpref0 : ∀ vp < u.cleanVp, u.st.pageOf true vp = vp := fun vp hvp => by
        have hp := hv.prefix_fixed hp_pos vp
        rw [ite_eq_left (by rcases hwb_br with h1 | ⟨h2, _⟩ <;> omega)] at hp
        exact hp hvp
      obtain ⟨hwb', hps', hvl_s, hvl_o, hti', hlen', hsw', hvirt'⟩ :=
        PagePairState.stepPopBack_spec hwb hpos
      have hpf0 := PrefixFixed.of_valid hv.valid hf0 ht0 hwb.jobValid hvp_le hpref0
      have hpf' := hpf0.rawPopBack_true.maybeStartJob.runTicks 16
      set st' := (u.st.stepPopBack true).1
      set ph' := if st'.job = .idle then 2 else 1
      have hnot_u : ¬(u.cleanPhase = 2 ∧ 0 < u.cleanOff) := by
        rcases hwb_br with h1 | ⟨_, h0⟩ <;> omega
      have hnot_u' : ¬(ph' = 2 ∧ 0 < (0 : ℕ)) := by simp
      refine ⟨?_, fun _ => by dsimp only [ph']; split_ifs <;> decide,
        hps', hvl_s, hvl_o, hti', hlen', hsw', fun arr s idx hidx => ?_⟩
      · rw [ite_eq_right hp0]
        refine ⟨hwb'.valid, hps' ▸ hv.pageSize_ge, by dsimp only [ph']; split_ifs <;> decide,
          by decide, fun h => absurd h (by dsimp only [ph']; split_ifs <;> decide),
          fun _ => ⟨hpf'.fp_false, hpf'.tc_false⟩,
          fun _ vp hvp => ?_,
          fun _ => ⟨hwb', min_le_right _ _, rfl⟩,
          fun h2 _ => (by
            dsimp only [ph'] at h2
            by_cases hj' : st'.job = .idle
            · exact ⟨hwb', hj', min_le_right _ _⟩
            · rw [ite_eq_right hj'] at h2; cases h2),
          fun _ hp => absurd hp (Nat.lt_irrefl 0),
          fun h => absurd h (by dsimp only [ph']; split_ifs <;> decide),
          fun h => absurd h (by dsimp only [ph']; split_ifs <;> decide)⟩
        dsimp only at hvp
        have hle2 : ph' ≤ 2 := by dsimp only [ph']; split_ifs <;> decide
        rw [ite_eq_left hle2] at hvp
        exact (hpf'.fixed_lt vp hvp).1
      · simp only [virtAt,
          toPhys_of_not_cleanSwap ⟨st', ph', min u.cleanVp (st'.fullPages true), 0⟩ hnot_u',
          toPhys_of_not_cleanSwap u hnot_u]
        exact hvirt' arr s idx hidx
    · rw [ite_eq_right hwb_br]
      have h23 : (u.cleanPhase = 2 ∧ 0 < u.cleanOff) ∨ u.cleanPhase = 3 := by omega
      have hphi25 : 16 * u.st.phi ≤ 25 * u.st.pageSize := by
        rcases h23 with ⟨h2, ho⟩ | h3
        · have := (hv.phase2_pos h2 ho).2.2.2.2; omega
        · have := (hv.phase3_inv h3).2.2.2.2; omega
      obtain ⟨hv_r, hphi_r, hps_r, hfp_r, htc_t, htc_f, hpo_r, hj_r, hvl_t, hvl_f, hti_r,
        hlen_r, hsw_r, htail_pres, hvirt_r⟩ :=
        rawPopBack_true_valid_of_phi hv.valid hv.pageSize_ge hf0 ht0 hphi25 hpos
      set st_r := (u.st.rawPopBack true).1
      set sws₀ := (u.st.rawPopBack true).2
      have hvl_f_orig : u.st.virtLen false = 0 := by
        unfold PagePairState.virtLen; rw [hf0, ht0, zero_mul, add_zero]
      by_cases hp2 : u.cleanPhase = 2
      · rw [ite_eq_left hp2]
        dsimp only
        have hoff_pos : 0 < u.cleanOff := by omega
        obtain ⟨hj, hvp_lt, hoff_le, hP_ne, hpot⟩ := hv.phase2_pos hp2 hoff_pos
        refine ⟨?_, fun _ => by decide, hps_r, hvl_t,
          fun s hs => by cases s <;> [rw [hvl_f, hvl_f_orig]; exact absurd rfl hs],
          hti_r, by change sws₀.length ≤ 17; omega,
          fun sw hsw => ⟨(hsw_r sw hsw).2.1, (hsw_r sw hsw).2.2.2⟩,
          fun arr s idx hidx => ?_⟩
        · rw [ite_eq_right hp0]
          refine ⟨hv_r, hps_r ▸ hv.pageSize_ge, by dsimp only; decide, by decide,
            fun h => absurd h (by dsimp only; decide),
            fun _ => ⟨by rw [hfp_r]; exact hf0, htc_f⟩,
            fun _ vp hvp => by
              dsimp only at hvp; rw [ite_eq_left (by decide)] at hvp
              rw [hpo_r]
              have hp := hv.prefix_fixed hp_pos vp
              rw [ite_eq_left (by omega)] at hp
              exact hp hvp,
            fun h => absurd h (by dsimp only; decide),
            fun _ h0 => absurd h0 (by dsimp only; omega),
            fun _ _ => ⟨by rw [hj_r]; exact hj, by rw [hfp_r]; exact hvp_lt,
              by rw [hps_r]; exact hoff_le, by rw [hpo_r]; exact hP_ne,
              by
                change 16 * st_r.phi + (st_r.pageSize - u.cleanOff) / 16 ≤ 25 * st_r.pageSize + 24
                rw [hps_r]; omega⟩,
            fun h => absurd h (by dsimp only; decide),
            fun h => absurd h (by dsimp only; decide)⟩
        · change (⟨st_r, 2, u.cleanVp, u.cleanOff⟩ : PageUnpermState).virtAt
            (applySwaps sws₀ arr) s idx = u.virtAt arr s idx
          change idx < st_r.virtLen s at hidx
          by_cases hlt_full : idx < st_r.fullPages s * st_r.pageSize
          · have hB := hv.valid.pageSize_pos
            have htotP : u.st.totalPages = u.st.fullPages true := by
              unfold PagePairState.totalPages; rw [hf0, zero_add]
            unfold virtAt toPhys; dsimp only
            rw [hps_r, hfp_r] at hlt_full ⊢
            rw [ite_eq_left hlt_full, ite_eq_left hlt_full, hpo_r]
            simp only [effCleanPage, hp2, hoff_pos, and_self, ↓reduceIte]
            rw [hpo_r]
            have hvp_s : idx / u.st.pageSize < u.st.fullPages s :=
              (Nat.div_lt_iff_lt_mul hB).mpr hlt_full
            have hp_s := hv.valid.page_lt s (idx / u.st.pageSize) hvp_s
            have hp_c := hv.valid.page_lt true u.cleanVp hvp_lt
            set E := if idx % u.st.pageSize < u.cleanOff then
              if u.st.pageOf s (idx / u.st.pageSize) = u.st.pageOf true u.cleanVp then u.cleanVp
              else if u.st.pageOf s (idx / u.st.pageSize) = u.cleanVp then
                u.st.pageOf true u.cleanVp
              else u.st.pageOf s (idx / u.st.pageSize)
              else u.st.pageOf s (idx / u.st.pageSize)
            have hE_lt : E < u.st.totalPages := by dsimp only [E]; split_ifs <;> omega
            have hmod := Nat.mod_lt idx hB
            have hle_tot := Nat.mul_le_mul_right u.st.pageSize hE_lt
            rw [Nat.add_one_mul] at hle_tot
            have hp_lt_QB : E * u.st.pageSize + idx % u.st.pageSize <
                u.st.totalPages * u.st.pageSize := by omega
            change applySwaps sws₀ arr (E * u.st.pageSize + idx % u.st.pageSize) =
              arr (E * u.st.pageSize + idx % u.st.pageSize)
            rcases sws₀ with _ | ⟨sw, rest⟩
            · rfl
            · have hlen1 : rest = [] := by
                cases rest with
                | nil => rfl
                | cons _ _ => simp only [List.length_cons] at hlen_r; omega
              subst hlen1
              obtain ⟨h1_lo, _, h2_lo, _⟩ := hsw_r sw (List.mem_singleton_self sw)
              simp only [applySwaps_cons, applySwaps_nil]
              exact PhysSwap.apply_of_ne sw arr
                (Nat.ne_of_lt (hp_lt_QB.trans_le h1_lo))
                (Nat.ne_of_lt (hp_lt_QB.trans_le h2_lo))
          · have hlt_u : ¬(idx < u.st.fullPages s * u.st.pageSize) := by
              rwa [hfp_r, hps_r] at hlt_full
            have htp1 : (⟨st_r, 2, u.cleanVp, u.cleanOff⟩ : PageUnpermState).toPhys s idx =
                st_r.toPhys s idx := by
              unfold toPhys PagePairState.toPhys; dsimp only
              rw [ite_eq_right hlt_full, ite_eq_right hlt_full]
            have htp0 : u.toPhys s idx = u.st.toPhys s idx := by
              unfold toPhys PagePairState.toPhys; dsimp only
              rw [ite_eq_right hlt_u, ite_eq_right hlt_u]
            unfold virtAt; rw [htp1, htp0]
            exact hvirt_r arr s idx hidx
      · rw [ite_eq_right hp2]
        dsimp only
        have hp3 : u.cleanPhase = 3 := by omega
        obtain ⟨hj, hoff0, hvp_le, htail_id, hpot⟩ := hv.phase3_inv hp3
        have hnot_u : ¬(u.cleanPhase = 2 ∧ 0 < u.cleanOff) := by omega
        have hnot_u' : ¬(u.cleanPhase = 2 ∧ 0 < (0 : ℕ)) := by simp
        refine ⟨?_, fun _ => hp_pos, hps_r, hvl_t,
          fun s hs => by cases s <;> [rw [hvl_f, hvl_f_orig]; exact absurd rfl hs],
          hti_r, by change sws₀.length ≤ 17; omega,
          fun sw hsw => ⟨(hsw_r sw hsw).2.1, (hsw_r sw hsw).2.2.2⟩,
          fun arr s idx hidx => ?_⟩
        · rw [ite_eq_right hp0]
          refine ⟨hv_r, hps_r ▸ hv.pageSize_ge, hv.phase_le, by decide,
            fun h => absurd h hp0,
            fun _ => ⟨by rw [hfp_r]; exact hf0, htc_f⟩,
            fun _ vp hvp => by
              dsimp only at hvp; rw [ite_eq_right (by omega), hfp_r] at hvp
              rw [hpo_r]
              have hp := hv.prefix_fixed hp_pos vp
              rw [ite_eq_right (by omega)] at hp
              exact hp hvp,
            fun h1 => absurd (Or.inl h1) hwb_br,
            fun h2 => absurd h2 hp2,
            fun h2 => absurd h2 hp2,
            fun _ => ⟨by rw [hj_r]; exact hj, rfl, min_le_right _ _, fun t ht => ?_, ?_⟩,
            fun h4 => absurd h4 (by dsimp only; omega)⟩
          · dsimp only at ht ⊢
            change st_r.tailPhys true t = st_r.fullPages true * st_r.pageSize + t
            change t < min u.cleanVp (st_r.tailCount true) at ht
            rw [hfp_r, hps_r]
            rw [htc_t] at ht
            exact htail_pres t (lt_of_lt_of_le ht (min_le_right _ _))
              (fun u0 hu0 => htail_id u0 (by
                have h1 := lt_of_lt_of_le ht (min_le_left _ _); omega))
          · change 16 * st_r.phi +
                (st_r.tailCount true - min u.cleanVp (st_r.tailCount true)) / 16 ≤
              25 * st_r.pageSize + 24
            rw [htc_t, hps_r]
            have hsub_le : u.st.tailCount true - 1 - min u.cleanVp (u.st.tailCount true - 1) ≤
                u.st.tailCount true - u.cleanVp := by omega
            have hdiv_le :
                (u.st.tailCount true - 1 - min u.cleanVp (u.st.tailCount true - 1)) / 16 ≤
                  (u.st.tailCount true - u.cleanVp) / 16 := Nat.div_le_div_right hsub_le
            omega
        · change (⟨st_r, u.cleanPhase, min u.cleanVp (st_r.tailCount true), 0⟩ :
              PageUnpermState).virtAt (applySwaps sws₀ arr) s idx = u.virtAt arr s idx
          change idx < st_r.virtLen s at hidx
          simp only [virtAt,
            toPhys_of_not_cleanSwap ⟨st_r, u.cleanPhase, min u.cleanVp (st_r.tailCount true), 0⟩
              hnot_u',
            toPhys_of_not_cleanSwap u hnot_u]
          exact hvirt_r arr s idx hidx

/-- Job potential `16 * st.phi + (if st.job = .idle then 2 * B + 2 else st.remTicks)`, nonincreasing
under `maybeStartJob` and strictly decreasing by `≥ 1` on non-commit ticks and by `≥ 2 * B - 37` on
job commits (`32 ≤ B`). -/
@[expose] def jobPot (st : PagePairState) : ℕ :=
  16 * st.phi + if st.job = .idle then 2 * st.pageSize + 2 else st.remTicks

/-- Monotone natural-number termination rank for Phase-2c/2d unpermutation (`cleanPhase ∈ {1..4}`):
equals `0` iff `cleanPhase = 4`, and strictly decreases by `≥ 1` on **every** `unpermStep` while
`0 < cleanPhase < 4`. -/
@[expose] def unpermRank (u : PageUnpermState) : ℕ :=
  let B := u.st.pageSize
  let Q := u.st.fullPages true
  if u.cleanPhase = 0 ∨ 4 ≤ u.cleanPhase then
    0
  else if u.cleanPhase = 3 then
    u.st.tailCount true - min u.cleanVp (u.st.tailCount true) + 1
  else
    4 * B + 2 + 2 * jobPot u.st +
      (Q - min u.cleanVp Q) * (B + 2) - u.cleanOff +
      if u.cleanPhase = 1 then 1 else 0

private theorem jobPot_maybeStartJob_le (st : PagePairState) :
    jobPot st.maybeStartJob ≤ jobPot st := by
  unfold PagePairState.maybeStartJob
  cases hj : st.job <;> try exact le_rfl
  dsimp only
  have hrem_le : ∀ j : PageJob,
      ((∃ s, j = .promote s 0) ∨ (∃ s, j = .demoteSwap s 0) ∨ (∃ s, j = .demoteBuild s 0)) →
      jobPot { st with job := j } ≤ jobPot st := by
    intro j hcases
    unfold jobPot PagePairState.remTicks PagePairState.phi
    rw [hj]
    rcases hcases with ⟨s, rfl⟩ | ⟨s, rfl⟩ | ⟨s, rfl⟩ <;> simp <;> omega
  generalize hs0 :
    (if 11 * st.pageSize ≤ 4 * st.tailCount false then some (PageJob.promote false 0)
    else if 0 < st.fullPages false ∧ 4 * st.tailCount false ≤ 5 * st.pageSize then
      if st.pageOf false (st.fullPages false - 1) = st.totalPages - 1 then
        some (PageJob.demoteBuild false 0)
      else some (PageJob.demoteSwap false 0)
    else none) = o0
  cases o0 with
  | some j =>
    refine hrem_le j ?_
    split_ifs at hs0 <;> simp only [Option.some.injEq] at hs0 <;> subst hs0
    · exact Or.inl ⟨false, rfl⟩
    · exact Or.inr (Or.inr ⟨false, rfl⟩)
    · exact Or.inr (Or.inl ⟨false, rfl⟩)
  | none =>
    generalize hs1 :
      (if 11 * st.pageSize ≤ 4 * st.tailCount true then some (PageJob.promote true 0)
      else if 0 < st.fullPages true ∧ 4 * st.tailCount true ≤ 5 * st.pageSize then
        if st.pageOf true (st.fullPages true - 1) = st.totalPages - 1 then
          some (PageJob.demoteBuild true 0)
        else some (PageJob.demoteSwap true 0)
      else none) = o1
    cases o1 with
    | some j =>
      refine hrem_le j ?_
      split_ifs at hs1 <;> simp only [Option.some.injEq] at hs1 <;> subst hs1
      · exact Or.inl ⟨true, rfl⟩
      · exact Or.inr (Or.inr ⟨true, rfl⟩)
      · exact Or.inr (Or.inl ⟨true, rfl⟩)
    | none => exact le_rfl

private theorem jobPot_tick_lt {st : PagePairState} (hwb : st.WellBalanced)
    (hf0 : st.fullPages false = 0) (ht0 : st.tailCount false = 0) (hj : st.job ≠ .idle) :
    let st' := st.tick.1
    st'.pageSize = st.pageSize ∧
    (st'.fullPages true ≤ st.fullPages true ∧ jobPot st' + 1 ≤ jobPot st ∨
     st'.fullPages true = st.fullPages true + 1 ∧
       jobPot st' + (2 * st.pageSize - 37) ≤ jobPot st) := by
  dsimp only
  have hB32 := hwb.pageSize_ge
  have hle_ms := jobPot_maybeStartJob_le st.tickOne.1
  have hms_fp : st.tickOne.1.maybeStartJob.fullPages = st.tickOne.1.fullPages := by
    unfold PagePairState.maybeStartJob; cases st.tickOne.1.job <;> try rfl
    dsimp only; split_ifs <;> rfl
  have hms_ps : st.tickOne.1.maybeStartJob.pageSize = st.tickOne.1.pageSize := by
    unfold PagePairState.maybeStartJob; cases st.tickOne.1.job <;> try rfl
    dsimp only; split_ifs <;> rfl
  unfold PagePairState.tick
  dsimp only
  rw [hms_ps, hms_fp]
  unfold PagePairState.tickOne at hle_ms ⊢
  cases hjob : st.job with
  | idle => exact absurd hjob hj
  | promote s cur =>
    rw [hjob] at hle_ms
    have hjv := hwb.jobValid; unfold PagePairState.JobValid at hjv; rw [hjob] at hjv
    have hs_t : s = true := by cases s <;> [exact absurd hjv (by rw [ht0]; omega); rfl]
    subst hs_t
    dsimp only at hle_ms ⊢
    by_cases hcur : cur < st.pageSize
    · rw [ite_eq_left hcur] at hle_ms ⊢
      obtain ⟨hps1, hfp1, htc1, _, _, _, _⟩ :=
        swapTailSlots_meta_eq st (st.tailPhys true cur) (st.totalPages * st.pageSize + cur)
      refine ⟨hps1, Or.inl ⟨by dsimp only; rw [hfp1], ?_⟩⟩
      have hjp1 : jobPot { (st.swapTailSlots (st.tailPhys true cur)
          (st.totalPages * st.pageSize + cur)).1 with job := .promote true (cur + 1) } + 1 ≤
          jobPot st := by
        unfold jobPot PagePairState.remTicks PagePairState.phi
        rw [hjob]; dsimp only; rw [hps1, hfp1, htc1]
        have : cur ≤ st.pageSize := hjv.1
        simp only [reduceCtorEq, ↓reduceIte]; omega
      exact Nat.le_trans (Nat.add_le_add_right hle_ms 1) hjp1
    · rw [ite_eq_right hcur] at hle_ms ⊢
      have hcur_eq : cur = st.pageSize := by have := hjv.1; omega
      subst hcur_eq
      refine ⟨rfl, Or.inr ⟨by dsimp only; rw [Function.update_self], ?_⟩⟩
      have hsb := hwb.side_bound
      simp only [PagePairState.ActiveSideBound, PagePairState.remTicks, hjob] at hsb
      have hjp1 : jobPot
          { st with
            fullPages := Function.update st.fullPages true (st.fullPages true + 1)
            tailCount := Function.update st.tailCount true (st.tailCount true - st.pageSize)
            tailHead := Function.update st.tailHead true
              ((st.tailHead true + st.pageSize) % (4 * st.pageSize))
            pageOf := PagePairState.set2 st.pageOf true (st.fullPages true) st.totalPages
            ownerSide := Function.update st.ownerSide st.totalPages true
            ownerVp := Function.update st.ownerVp st.totalPages (st.fullPages true)
            job := .idle } + (2 * st.pageSize - 37) ≤ jobPot st := by
        unfold jobPot PagePairState.remTicks PagePairState.phi PagePairState.dev
        rw [hjob]; dsimp only
        simp only [Function.update_self, Function.update_of_ne (by decide : false ≠ true),
          Nat.succ_pos, ↓reduceIte, hf0, ht0, reduceCtorEq]
        split_ifs <;> omega
      exact Nat.le_trans (Nat.add_le_add_right hle_ms _) hjp1
  | demoteSwap s cur =>
    rw [hjob] at hle_ms
    dsimp only at hle_ms ⊢
    have hjv := hwb.jobValid; unfold PagePairState.JobValid at hjv; rw [hjob] at hjv
    by_cases hcur : cur < st.pageSize
    · rw [ite_eq_left hcur] at hle_ms ⊢
      refine ⟨rfl, Or.inl ⟨le_rfl, ?_⟩⟩
      have hjp1 : jobPot { st with job := .demoteSwap s (cur + 1) } + 1 ≤ jobPot st := by
        unfold jobPot PagePairState.remTicks PagePairState.phi
        rw [hjob]; dsimp only; simp only [reduceCtorEq, ↓reduceIte]; omega
      exact Nat.le_trans (Nat.add_le_add_right hle_ms 1) hjp1
    · rw [ite_eq_right hcur] at hle_ms ⊢
      have hcur_eq : cur = st.pageSize := by have := hjv.1; omega
      subst hcur_eq
      refine ⟨rfl, Or.inl ⟨le_rfl, ?_⟩⟩
      have hjp1 : jobPot
          { st with
            pageOf := PagePairState.set2
              (PagePairState.set2 st.pageOf (st.ownerSide (st.totalPages - 1))
                (st.ownerVp (st.totalPages - 1)) (st.pageOf s (st.fullPages s - 1)))
              s (st.fullPages s - 1) (st.totalPages - 1)
            ownerSide := Function.update
              (Function.update st.ownerSide (st.pageOf s (st.fullPages s - 1))
                (st.ownerSide (st.totalPages - 1))) (st.totalPages - 1) s
            ownerVp := Function.update
              (Function.update st.ownerVp (st.pageOf s (st.fullPages s - 1))
                (st.ownerVp (st.totalPages - 1))) (st.totalPages - 1) (st.fullPages s - 1)
            job := .demoteBuild s 0 } + 1 ≤ jobPot st := by
        unfold jobPot PagePairState.remTicks PagePairState.phi
        rw [hjob]; dsimp only; simp only [reduceCtorEq, ↓reduceIte]; omega
      exact Nat.le_trans (Nat.add_le_add_right hle_ms 1) hjp1
  | demoteBuild s cur =>
    rw [hjob] at hle_ms
    have hjv := hwb.jobValid; unfold PagePairState.JobValid at hjv; rw [hjob] at hjv
    have hs_t : s = true := by cases s <;> [exact absurd hjv (by dsimp only; rw [hf0]; omega); rfl]
    subst hs_t
    dsimp only at hle_ms ⊢
    by_cases hcur : cur < st.pageSize
    · rw [ite_eq_left hcur] at hle_ms ⊢
      refine ⟨rfl, Or.inl ⟨le_rfl, ?_⟩⟩
      have hjp1 : jobPot
          { st with
            tailRes := PagePairState.set2 st.tailRes true
              ((st.tailHead true + 3 * st.pageSize + cur) % (4 * st.pageSize))
              (((st.totalPages - 1) * st.pageSize + cur) % (8 * st.pageSize))
            tailOwnerSide := Function.update st.tailOwnerSide
              (((st.totalPages - 1) * st.pageSize + cur) % (8 * st.pageSize)) true
            tailOwnerRing := Function.update st.tailOwnerRing
              (((st.totalPages - 1) * st.pageSize + cur) % (8 * st.pageSize))
              ((st.tailHead true + 3 * st.pageSize + cur) % (4 * st.pageSize))
            job := .demoteBuild true (cur + 1) } + 1 ≤ jobPot st := by
        unfold jobPot PagePairState.remTicks PagePairState.phi
        rw [hjob]; dsimp only; simp only [reduceCtorEq, ↓reduceIte]; omega
      exact Nat.le_trans (Nat.add_le_add_right hle_ms 1) hjp1
    · rw [ite_eq_right hcur] at hle_ms ⊢
      have hcur_eq : cur = st.pageSize := by have := hjv.1; omega
      subst hcur_eq
      refine ⟨rfl, Or.inl ⟨by dsimp only; rw [Function.update_self]; omega, ?_⟩⟩
      have hsb := hwb.side_bound
      simp only [PagePairState.ActiveSideBound, PagePairState.remTicks, hjob] at hsb
      have hq_pos : 0 < st.fullPages true := hjv.2.1
      have hjp1 : jobPot
          { st with
            fullPages := Function.update st.fullPages true (st.fullPages true - 1)
            tailCount := Function.update st.tailCount true (st.tailCount true + st.pageSize)
            tailHead := Function.update st.tailHead true
              ((st.tailHead true + 3 * st.pageSize) % (4 * st.pageSize))
            job := .idle } + 1 ≤ jobPot st := by
        unfold jobPot PagePairState.remTicks PagePairState.phi PagePairState.dev
        rw [hjob]; dsimp only
        simp only [Function.update_self, Function.update_of_ne (by decide : false ≠ true),
          hf0, ht0, hq_pos, ↓reduceIte, reduceCtorEq]
        split_ifs <;> omega
      exact Nat.le_trans (Nat.add_le_add_right hle_ms 1) hjp1

/-- Every `unpermStep` while `0 < u.cleanPhase < 4` strictly decreases `unpermRank` by `≥ 1`. -/
theorem unpermRank_lt_of_unpermStep {u : PageUnpermState} {slack : ℕ}
    (hi : u.InvWithSlack slack) (hpos : 0 < u.cleanPhase) (hlt4 : u.cleanPhase < 4) :
    unpermRank u.unpermStep.1 + 1 ≤ unpermRank u := by
  have hB32 := hi.pageSize_ge
  obtain ⟨hf0, ht0⟩ := hi.src_empty hpos
  unfold unpermStep
  dsimp only
  by_cases hp1 : u.cleanPhase = 1
  · rw [ite_eq_left hp1]
    obtain ⟨hwb, hvp_le, hoff0⟩ := hi.phase1_wb hp1
    by_cases hj : u.st.job = .idle
    · rw [ite_eq_left hj]; dsimp only
      unfold unpermRank; dsimp only
      simp only [hp1, hoff0, Nat.min_eq_left hvp_le,
        Nat.reduceEqDiff, Nat.reduceLeDiff, or_self, ↓reduceIte]
      omega
    · rw [ite_eq_right hj]; dsimp only
      obtain ⟨hps', hcases⟩ := jobPot_tick_lt hwb hf0 ht0 hj
      unfold unpermRank; dsimp only
      simp only [hp1, hoff0, Nat.min_eq_left hvp_le, Nat.min_eq_left (min_le_right _ _), hps',
        Nat.reduceEqDiff, Nat.reduceLeDiff, or_self, ↓reduceIte]
      rcases hcases with ⟨hfp_le, hjp_lt⟩ | ⟨hfp_inc, hjp_drop⟩
      · have hsub_le : u.st.tick.1.fullPages true - min u.cleanVp (u.st.tick.1.fullPages true) ≤
            u.st.fullPages true - u.cleanVp := by omega
        have hmul_le := Nat.mul_le_mul_right (u.st.pageSize + 2) hsub_le
        omega
      · rw [hfp_inc, Nat.min_eq_left (by omega : u.cleanVp ≤ u.st.fullPages true + 1)]
        have hmul_eq : (u.st.fullPages true + 1 - u.cleanVp) * (u.st.pageSize + 2) =
            (u.st.fullPages true - u.cleanVp) * (u.st.pageSize + 2) + (u.st.pageSize + 2) := by
          rw [show u.st.fullPages true + 1 - u.cleanVp =
            (u.st.fullPages true - u.cleanVp) + 1 by omega, Nat.add_one_mul]
        rw [hmul_eq]
        omega
  · rw [ite_eq_right hp1]
    by_cases hp2 : u.cleanPhase = 2
    · rw [ite_eq_left hp2]
      by_cases hoff0 : u.cleanOff = 0
      · rw [ite_eq_left hoff0]
        obtain ⟨_, _, hvp_le⟩ := hi.phase2_zero hp2 hoff0
        by_cases hdone_p : u.st.fullPages true ≤ u.cleanVp
        · rw [ite_eq_left hdone_p]; dsimp only
          have htc_lt := hi.valid.tailCount_lt true
          unfold unpermRank; dsimp only
          simp only [hp2, hoff0, Nat.zero_min, Nat.sub_zero,
            Nat.reduceEqDiff, Nat.reduceLeDiff, or_self, ↓reduceIte]
          omega
        · rw [ite_eq_right hdone_p]
          have hvp_lt : u.cleanVp < u.st.fullPages true := Nat.lt_of_not_ge hdone_p
          by_cases hP_eq : u.st.pageOf true u.cleanVp = u.cleanVp
          · rw [ite_eq_left hP_eq]; dsimp only
            unfold unpermRank; dsimp only
            simp only [hp2, hoff0, Nat.min_eq_left hvp_le,
              Nat.min_eq_left (by omega : u.cleanVp + 1 ≤ u.st.fullPages true),
              Nat.reduceEqDiff, Nat.reduceLeDiff, or_self, ↓reduceIte]
            have hmul_gt : (u.st.fullPages true - (u.cleanVp + 1)) * (u.st.pageSize + 2) +
                (u.st.pageSize + 2) =
                (u.st.fullPages true - u.cleanVp) * (u.st.pageSize + 2) := by
              rw [← Nat.add_one_mul, show u.st.fullPages true - (u.cleanVp + 1) + 1 =
                u.st.fullPages true - u.cleanVp by omega]
            omega
          · rw [ite_eq_right hP_eq]; dsimp only
            unfold unpermRank; dsimp only
            simp only [hp2, hoff0, Nat.min_eq_left hvp_le,
              Nat.reduceEqDiff, Nat.reduceLeDiff, or_self, ↓reduceIte]
            have hge1 : u.st.pageSize + 2 ≤
                (u.st.fullPages true - u.cleanVp) * (u.st.pageSize + 2) :=
              Nat.le_mul_of_pos_left _ (by omega)
            omega
      · rw [ite_eq_right hoff0]
        have hoff_pos : 0 < u.cleanOff := Nat.pos_of_ne_zero hoff0
        obtain ⟨hj, hvp_lt, hoff_le, _, _⟩ := hi.phase2_pos hp2 hoff_pos
        by_cases hoff_lt : u.cleanOff < u.st.pageSize
        · rw [ite_eq_left hoff_lt]; dsimp only
          unfold unpermRank; dsimp only
          simp only [hp2, Nat.min_eq_left hvp_lt.le,
            Nat.reduceEqDiff, Nat.reduceLeDiff, or_self, ↓reduceIte]
          have hge1 : u.st.pageSize + 2 ≤
              (u.st.fullPages true - u.cleanVp) * (u.st.pageSize + 2) :=
            Nat.le_mul_of_pos_left _ (by omega)
          omega
        · rw [ite_eq_right hoff_lt]; dsimp only
          have hoff_eq : u.cleanOff = u.st.pageSize := by omega
          set st_c : PagePairState :=
            { u.st with
              pageOf := PagePairState.set2
                (PagePairState.set2 u.st.pageOf true (u.st.ownerVp u.cleanVp)
                  (u.st.pageOf true u.cleanVp)) true u.cleanVp u.cleanVp
              ownerVp := Function.update
                (Function.update u.st.ownerVp (u.st.pageOf true u.cleanVp)
                  (u.st.ownerVp u.cleanVp)) u.cleanVp u.cleanVp }
          have hjp_c : jobPot st_c.maybeStartJob ≤ jobPot u.st := by
            refine (jobPot_maybeStartJob_le st_c).trans ?_
            unfold jobPot PagePairState.phi; dsimp only [st_c]; exact le_rfl
          have hms_fp : st_c.maybeStartJob.fullPages = u.st.fullPages := by
            unfold PagePairState.maybeStartJob; rw [show st_c.job = .idle from hj]
            dsimp only; split_ifs <;> rfl
          have hms_ps : st_c.maybeStartJob.pageSize = u.st.pageSize := by
            unfold PagePairState.maybeStartJob; rw [show st_c.job = .idle from hj]
            dsimp only; split_ifs <;> rfl
          set st_ms := st_c.maybeStartJob
          set ph' := if st_ms.job = .idle then 2 else 1
          unfold unpermRank; dsimp only
          rw [hms_ps, hms_fp]
          have hph_not : ¬(ph' = 0 ∨ 4 ≤ ph') := by dsimp only [ph']; split_ifs <;> decide
          have hph_not3 : ph' ≠ 3 := by dsimp only [ph']; split_ifs <;> decide
          rw [ite_eq_right hph_not, ite_eq_right hph_not3]
          simp only [hp2, hoff_eq, Nat.min_eq_left hvp_lt.le,
            Nat.min_eq_left (by omega : u.cleanVp + 1 ≤ u.st.fullPages true),
            Nat.reduceEqDiff, Nat.reduceLeDiff, or_self, ↓reduceIte]
          have hmul_eq : (u.st.fullPages true - u.cleanVp) * (u.st.pageSize + 2) =
              (u.st.fullPages true - (u.cleanVp + 1)) * (u.st.pageSize + 2) +
                (u.st.pageSize + 2) := by
            rw [← Nat.add_one_mul, show u.st.fullPages true - (u.cleanVp + 1) + 1 =
              u.st.fullPages true - u.cleanVp by omega]
          have hph1 : (if ph' = 1 then 1 else 0) ≤ 1 := by split_ifs <;> decide
          omega
    · rw [ite_eq_right hp2]
      have hp3 : u.cleanPhase = 3 := by omega
      rw [ite_eq_left hp3]
      by_cases hdone_t : u.st.tailCount true ≤ u.cleanVp
      · rw [ite_eq_left hdone_t]; dsimp only
        unfold unpermRank; dsimp only
        simp [hp3]
      · rw [ite_eq_right hdone_t]; dsimp only
        have hlt_tc : u.cleanVp < u.st.tailCount true := Nat.lt_of_not_ge hdone_t
        obtain ⟨_, _, htc1, _, _, _, _⟩ :=
          swapTailSlots_meta_eq u.st (u.st.tailPhys true u.cleanVp)
            (u.st.fullPages true * u.st.pageSize + u.cleanVp)
        unfold unpermRank; dsimp only
        rw [htc1]
        simp only [hp3, Nat.min_eq_left hlt_tc.le,
          Nat.min_eq_left (by omega : u.cleanVp + 1 ≤ u.st.tailCount true),
          Nat.reduceEqDiff, Nat.reduceLeDiff, or_self, ↓reduceIte]
        omega

end PageUnpermState

end Cslib.DataStructure.WordRAM.Resizable.Randomized

end
