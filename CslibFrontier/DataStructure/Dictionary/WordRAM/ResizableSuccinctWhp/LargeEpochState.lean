/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeBlockPool
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeBTreeProg
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeTrieProg
import CslibFrontier.Computability.WordRAM.Realization.BoundedTactic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Per-Epoch Item-Pool Refinement, Small-Regime Epoch, and `1 · OPT` Fallback Pool

This module provides three foundational building blocks for individual epochs of the deamortized
worst-case WHP resizable succinct dictionary
([Bender, Farach-Colton, J. Kuszmaul, and W. Kuszmaul, SOSA 2024,
Sections 4–6][BenderFarachColtonKuszmaulKuszmaul2024]):

1. **Bijective quotient-value pool refinement (`PoolItemsRefines`):**
   A shared mathematical invariant relating a dense `[0, nSide)` array of `(owner, (quot, val))`
   entries under one-round Feistel quotienting (`feistelBucket` / `keyQuotient` /
   `feistelReconstruct`) to an abstract dictionary `s_abs : Fin U → Option (Fin V)`. Both the
   small-regime epoch (`bBits = 0`), the SOSA 2024 fast-path `BlockPoolState`, and the rare
   `1 · OPT` `FallbackPool` instantiate this single refinement structure.
2. **Unified small-regime epoch (`SmallEpochLayout`, `N = 0`, `nSide < 2 * whpThreshold c`):**
   Operates directly over `SlotIoLayout` (supporting both `usePaged = 0` direct streams and
   `usePaged ≠ 0` shared `PageUnpermState` arenas during Small ↔ Large Phase 2 migrations) in
   `O(nSide + 1) = O_c(1)` deterministic instructions via `RealizesBounded .exact` (`¬ReadsWidth`).
3. **Deterministic `1 · OPT` `FallbackPool` (`FallbackState`, `FallbackLayout`):**
   On the `≤ (1 / 2) * N ^ (-c)` bad-seed event `¬GoodEpochSeeds`, transitions in-place from
   `BlockPoolState` without resampling `(θ_bkt, θ_fp)` (preserving exact unconditioned uniform seed
   marginals across the epoch) and without allocating a single extra word (`1 · OPT` peak space),
   using Pigeonhole `K`-block promotion (`tailLen ≤ 6 * M * K`) to maintain `(Dynamic.spec U V U)`
   operations deterministically.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.PoolItemsRefines`
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.SmallEpochLayout`,
  `smallEpochInitProg`, `smallEpochQueryProg`, `smallEpochInsertProg`, `smallEpochDeleteProg`,
  `smallEpochPopAnyProg`
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.FallbackState`

## References

* [M. A. Bender, M. Farach-Colton, J. Kuszmaul, and W. Kuszmaul, *Modern Hashing Made Simple*,
  Sections 4–6][BenderFarachColtonKuszmaulKuszmaul2024]
-/

public section

open scoped BigOperators

namespace Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.WordRAM.Resizable
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.SuccinctWhp
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct
open Cslib.DataStructure.HashFamily.WordRAM
open Cslib.DataStructure.WordRAM.Resizable.Randomized
open Finset

attribute [local simp] Realization.memoryCost_bind'
attribute [local simp] prog_clientResult_bind prog_runClient_state_bind prog_clientResult_pure
attribute [local simp] prog_runClient_state_pure prog_clientResult_map prog_runClient_state_map
attribute [local simp] prog_memoryCost_map prog_clientResult_read prog_runClient_state_read
attribute [local simp] prog_memoryCost_read prog_clientResult_write prog_runClient_state_write
attribute [local simp] prog_memoryCost_write

/-! ## Section 1: Shared Bijective Quotient-Value Pool Refinement (`PoolItemsRefines`) -/

/-- Bijective refinement between `[0, nSide)` `(ownerFn p, pairFn p)` entries under `bBits`-bit
Feistel quotienting (`hBkt`) and an abstract dictionary `s_abs : Fin U → Option (Fin V)`. -/
structure PoolItemsRefines (U V bBits : ℕ) (hBkt : ℕ → ℕ) (nSide : ℕ)
    (ownerFn : ℕ → ℕ) (pairFn : ℕ → ℕ × ℕ) (s_abs : Fin U → Option (Fin V)) : Prop where
  /-- Every slot `p < nSide` has `< 2 ^ bBits` bucket, `< V` value, and a valid key `< U`. -/
  slot_valid : ∀ p < nSide,
    ownerFn p < 2 ^ bBits ∧
    (pairFn p).2 < V ∧
    ∃ u : Fin U,
      feistelBucket bBits hBkt u.val = ownerFn p ∧
      keyQuotient bBits u.val = (pairFn p).1
  /-- Distinct slots `p₁, p₂ < nSide` hold distinct `(bucket, quotient)` pairs. -/
  slot_inj : ∀ p₁ < nSide, ∀ p₂ < nSide,
    ownerFn p₁ = ownerFn p₂ → (pairFn p₁).1 = (pairFn p₂).1 → p₁ = p₂
  /-- Exact key-value correspondence with `s_abs`. -/
  models : ∀ (u : Fin U) (v : Fin V),
    s_abs u = some v ↔
      ∃ p < nSide,
        ownerFn p = feistelBucket bBits hBkt u.val ∧
        (pairFn p).1 = keyQuotient bBits u.val ∧
        (pairFn p).2 = v.val

namespace PoolItemsRefines

theorem empty (U V bBits : ℕ) (hBkt : ℕ → ℕ) (ownerFn : ℕ → ℕ) (pairFn : ℕ → ℕ × ℕ) :
    PoolItemsRefines U V bBits hBkt 0 ownerFn pairFn (fun _ => none) where
  slot_valid _ hp := absurd hp (Nat.not_lt_zero _)
  slot_inj _ hp := absurd hp (Nat.not_lt_zero _)
  models _ _ := ⟨by rintro ⟨⟩, fun ⟨_, hp, _⟩ => absurd hp (Nat.not_lt_zero _)⟩

theorem congr {U V bBits : ℕ} {hBkt : ℕ → ℕ} {nSide : ℕ}
    {ow₁ ow₂ : ℕ → ℕ} {pr₁ pr₂ : ℕ → ℕ × ℕ} {s_abs : Fin U → Option (Fin V)}
    (h : PoolItemsRefines U V bBits hBkt nSide ow₁ pr₁ s_abs)
    (how : ∀ p < nSide, ow₂ p = ow₁ p) (hpr : ∀ p < nSide, pr₂ p = pr₁ p) :
    PoolItemsRefines U V bBits hBkt nSide ow₂ pr₂ s_abs where
  slot_valid p hp := by
    rw [how p hp, hpr p hp]; exact h.slot_valid p hp
  slot_inj p₁ hp₁ p₂ hp₂ heq1 heq2 := by
    rw [how p₁ hp₁, how p₂ hp₂] at heq1
    rw [hpr p₁ hp₁, hpr p₂ hp₂] at heq2
    exact h.slot_inj p₁ hp₁ p₂ hp₂ heq1 heq2
  models u v := by
    rw [h.models u v]
    exact ⟨fun ⟨p, hp, h1, h2, h3⟩ =>
        ⟨p, hp, (how p hp).trans h1, by rw [hpr p hp]; exact h2, by rw [hpr p hp]; exact h3⟩,
      fun ⟨p, hp, h1, h2, h3⟩ =>
        ⟨p, hp, (how p hp).symm.trans h1, by rw [← hpr p hp]; exact h2,
          by rw [← hpr p hp]; exact h3⟩⟩

/-- Simultaneous `PhysSwap` on `ownerFn` and `pairFn` at `p₁, p₂ < nSide` preserves
`PoolItemsRefines`. -/
theorem apply_swap {U V bBits : ℕ} {hBkt : ℕ → ℕ} {nSide : ℕ}
    {ow : ℕ → ℕ} {pr : ℕ → ℕ × ℕ} {s_abs : Fin U → Option (Fin V)}
    (h : PoolItemsRefines U V bBits hBkt nSide ow pr s_abs)
    {sw : PhysSwap} (hp₁ : sw.p₁ < nSide) (hp₂ : sw.p₂ < nSide) :
    PoolItemsRefines U V bBits hBkt nSide (sw.apply ow) (sw.apply pr) s_abs := by
  let idxMap : ℕ → ℕ := fun p =>
    if p = sw.p₁ then sw.p₂ else if p = sw.p₂ then sw.p₁ else p
  have hinv : ∀ p, idxMap (idxMap p) = p := fun p => by
    dsimp only [idxMap]
    by_cases h1 : p = sw.p₁
    · subst h1; by_cases h12 : sw.p₂ = sw.p₁ <;> simp [h12]
    · by_cases h2 : p = sw.p₂
      · subst h2; simp [h1]
      · simp [h1, h2]
  have hlt : ∀ p < nSide, idxMap p < nSide := fun p hp => by
    dsimp only [idxMap]; split_ifs <;> assumption
  have how_eq : ∀ p, sw.apply ow p = ow (idxMap p) := fun p => by
    dsimp only [idxMap]; split_ifs with h1 h2
    · subst h1; exact sw.apply_p₁ ow
    · subst h2; exact sw.apply_p₂ ow
    · exact sw.apply_of_ne ow h1 h2
  have hpr_eq : ∀ p, sw.apply pr p = pr (idxMap p) := fun p => by
    dsimp only [idxMap]; split_ifs with h1 h2
    · subst h1; exact sw.apply_p₁ pr
    · subst h2; exact sw.apply_p₂ pr
    · exact sw.apply_of_ne pr h1 h2
  refine
    { slot_valid := fun p hp => by
        rw [how_eq p, hpr_eq p]; exact h.slot_valid _ (hlt p hp)
      slot_inj := fun q₁ hq₁ q₂ hq₂ he1 he2 => by
        rw [how_eq q₁, how_eq q₂] at he1
        rw [hpr_eq q₁, hpr_eq q₂] at he2
        have hin := h.slot_inj _ (hlt q₁ hq₁) _ (hlt q₂ hq₂) he1 he2
        have := congrArg idxMap hin
        rwa [hinv, hinv] at this
      models := fun u v => by
        rw [h.models u v]
        constructor
        · rintro ⟨p, hp, h1, h2, h3⟩
          refine ⟨idxMap p, hlt p hp, ?_, ?_, ?_⟩
          · rw [how_eq, hinv]; exact h1
          · rw [hpr_eq, hinv]; exact h2
          · rw [hpr_eq, hinv]; exact h3
        · rintro ⟨p, hp, h1, h2, h3⟩
          rw [how_eq] at h1; rw [hpr_eq] at h2 h3
          exact ⟨idxMap p, hlt p hp, h1, h2, h3⟩ }

/-- Reconstruct the unique live key-value pair `(u, v)` at `p < nSide`. -/
theorem slot_key_val {U V bBits : ℕ} {hBkt : ℕ → ℕ} {nSide : ℕ}
    {ow : ℕ → ℕ} {pr : ℕ → ℕ × ℕ} {s_abs : Fin U → Option (Fin V)}
    (h : PoolItemsRefines U V bBits hBkt nSide ow pr s_abs) {p : ℕ} (hp : p < nSide) :
    let u_val := feistelReconstruct bBits hBkt (ow p) (pr p).1
    ∃ (hu : u_val < U) (hv : (pr p).2 < V),
      feistelBucket bBits hBkt u_val = ow p ∧
      keyQuotient bBits u_val = (pr p).1 ∧
      s_abs ⟨u_val, hu⟩ = some ⟨(pr p).2, hv⟩ := by
  dsimp only
  obtain ⟨_, hv, ⟨u, hfb, hkq⟩⟩ := h.slot_valid p hp
  have hrec : feistelReconstruct bBits hBkt (ow p) (pr p).1 = u.val := by
    rw [← hfb, ← hkq, feistelReconstruct_feistelBucket]
  refine ⟨hrec ▸ u.isLt, hv, ?_, ?_, ?_⟩
  · rw [hrec]; exact hfb
  · rw [hrec]; exact hkq
  · have hm := (h.models ⟨feistelReconstruct bBits hBkt (ow p) (pr p).1, hrec ▸ u.isLt⟩
      ⟨(pr p).2, hv⟩).mpr
    exact hm ⟨p, hp, by dsimp only; rw [hrec, hfb], by dsimp only; rw [hrec, hkq], rfl⟩

/-- Lookup characterization: if `p < nSide` matches `(feistelBucket u, keyQuotient u)`, then
`s_abs u = some ⟨(pr p).2, _⟩`; if no `p < nSide` matches, `s_abs u = none`. -/
theorem lookup_eq_some {U V bBits : ℕ} {hBkt : ℕ → ℕ} {nSide : ℕ}
    {ow : ℕ → ℕ} {pr : ℕ → ℕ × ℕ} {s_abs : Fin U → Option (Fin V)}
    (h : PoolItemsRefines U V bBits hBkt nSide ow pr s_abs)
    {u : Fin U} {p : ℕ} (hp : p < nSide)
    (hfb : ow p = feistelBucket bBits hBkt u.val)
    (hkq : (pr p).1 = keyQuotient bBits u.val) :
    s_abs u = some ⟨(pr p).2, by exact (h.slot_valid p hp).2.1⟩ :=
  (h.models u ⟨(pr p).2, (h.slot_valid p hp).2.1⟩).mpr ⟨p, hp, hfb, hkq, rfl⟩

theorem lookup_eq_none {U V bBits : ℕ} {hBkt : ℕ → ℕ} {nSide : ℕ}
    {ow : ℕ → ℕ} {pr : ℕ → ℕ × ℕ} {s_abs : Fin U → Option (Fin V)}
    (h : PoolItemsRefines U V bBits hBkt nSide ow pr s_abs) {u : Fin U}
    (hmiss : ∀ p < nSide, ¬(ow p = feistelBucket bBits hBkt u.val ∧
      (pr p).1 = keyQuotient bBits u.val)) :
    s_abs u = none := by
  cases hs : s_abs u with
  | none => rfl
  | some v =>
    obtain ⟨p, hp, h1, h2, _⟩ := (h.models u v).mp hs
    exact absurd ⟨h1, h2⟩ (hmiss p hp)

/-- Overwriting `(pr p)` with `(keyQuotient u, v.val)` at matching `p < nSide` refines
`Function.update s_abs u (some v)`. -/
theorem update_at {U V bBits : ℕ} {hBkt : ℕ → ℕ} {nSide : ℕ}
    {ow : ℕ → ℕ} {pr pr' : ℕ → ℕ × ℕ} {s_abs : Fin U → Option (Fin V)}
    (h : PoolItemsRefines U V bBits hBkt nSide ow pr s_abs)
    {u : Fin U} (v : Fin V) {p : ℕ} (hp : p < nSide)
    (hfb : ow p = feistelBucket bBits hBkt u.val)
    (hkq : (pr p).1 = keyQuotient bBits u.val)
    (hpr_self : pr' p = (keyQuotient bBits u.val, v.val))
    (hpr_ne : ∀ q < nSide, q ≠ p → pr' q = pr q) :
    PoolItemsRefines U V bBits hBkt nSide ow pr' (Function.update s_abs u (some v)) where
  slot_valid q hq := by
    by_cases hqp : q = p
    · subst hqp
      rw [hpr_self]
      exact ⟨(h.slot_valid q hq).1, v.isLt, ⟨u, hfb.symm, rfl⟩⟩
    · rw [hpr_ne q hq hqp]; exact h.slot_valid q hq
  slot_inj q₁ hq₁ q₂ hq₂ he1 he2 := by
    have hq_fst : ∀ q < nSide, (pr' q).1 = (pr q).1 := fun q hq => by
      by_cases hqp : q = p
      · subst hqp; rw [hpr_self, hkq]
      · rw [hpr_ne q hq hqp]
    rw [hq_fst q₁ hq₁, hq_fst q₂ hq₂] at he2
    exact h.slot_inj q₁ hq₁ q₂ hq₂ he1 he2
  models u' v' := by
    by_cases hu : u' = u
    · subst hu
      rw [Function.update_self, Option.some.injEq]
      constructor
      · rintro rfl
        exact ⟨p, hp, hfb, by rw [hpr_self], by rw [hpr_self]⟩
      · rintro ⟨q, hq, h1, h2, h3⟩
        have hqp : q = p := by
          refine h.slot_inj q hq p hp (h1.trans hfb.symm) ?_
          have hfst : (pr' q).1 = (pr q).1 := by
            by_cases he : q = p
            · subst he; rw [hpr_self, hkq]
            · rw [hpr_ne q hq he]
          rw [← hfst, h2, hkq]
        subst hqp
        rw [hpr_self] at h3; dsimp only at h3
        exact Fin.ext h3
    · rw [Function.update_of_ne hu, h.models u' v']
      have hne_p : ∀ q < nSide, ow q = feistelBucket bBits hBkt u'.val →
          (pr q).1 = keyQuotient bBits u'.val → q ≠ p := by
        intro q _ h1 h2 rfl
        apply hu; apply Fin.ext
        exact eq_of_feistelBucket_eq_of_keyQuotient_eq (h1.symm.trans hfb) (h2.symm.trans hkq)
      constructor
      · rintro ⟨q, hq, h1, h2, h3⟩
        have hqp := hne_p q hq h1 h2
        rw [← hpr_ne q hq hqp] at h2 h3
        exact ⟨q, hq, h1, h2, h3⟩
      · rintro ⟨q, hq, h1, h2, h3⟩
        have hqp : q ≠ p := by
          rintro rfl
          rw [hpr_self] at h2; dsimp only at h2
          exact hu (Fin.ext (eq_of_feistelBucket_eq_of_keyQuotient_eq
            (h1.symm.trans hfb) h2.symm))
        rw [hpr_ne q hq hqp] at h2 h3
        exact ⟨q, hq, h1, h2, h3⟩

/-- Appending an absent key `(u, v)` at `nSide` refines `Function.update s_abs u (some v)`. -/
theorem append_new {U V bBits : ℕ} {hBkt : ℕ → ℕ} {nSide : ℕ}
    {ow ow' : ℕ → ℕ} {pr pr' : ℕ → ℕ × ℕ} {s_abs : Fin U → Option (Fin V)}
    (h : PoolItemsRefines U V bBits hBkt nSide ow pr s_abs)
    {u : Fin U} (v : Fin V) (habs : s_abs u = none)
    (how_new : ow' nSide = feistelBucket bBits hBkt u.val)
    (hpr_new : pr' nSide = (keyQuotient bBits u.val, v.val))
    (how_old : ∀ p < nSide, ow' p = ow p)
    (hpr_old : ∀ p < nSide, pr' p = pr p) :
    PoolItemsRefines U V bBits hBkt (nSide + 1) ow' pr' (Function.update s_abs u (some v)) := by
  have hno_old : ∀ p < nSide, ¬(ow p = feistelBucket bBits hBkt u.val ∧
      (pr p).1 = keyQuotient bBits u.val) := by
    intro p hp ⟨h1, h2⟩
    have hs := h.lookup_eq_some hp h1 h2
    rw [habs] at hs; cases hs
  refine
    { slot_valid := fun p hp => by
        rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hp) with rfl | hlt
        · rw [how_new, hpr_new]
          exact ⟨feistelBucket_lt bBits hBkt u.val, v.isLt, ⟨u, rfl, rfl⟩⟩
        · rw [how_old p hlt, hpr_old p hlt]
          exact h.slot_valid p hlt
      slot_inj := fun p₁ hp₁ p₂ hp₂ he1 he2 => by
        rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hp₁) with rfl | hlt₁
        · rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hp₂) with rfl | hlt₂
          · rfl
          · rw [how_new, how_old p₂ hlt₂] at he1
            rw [hpr_new, hpr_old p₂ hlt₂] at he2
            exact absurd ⟨he1.symm, he2.symm⟩ (hno_old p₂ hlt₂)
        · rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hp₂) with rfl | hlt₂
          · rw [how_old p₁ hlt₁, how_new] at he1
            rw [hpr_old p₁ hlt₁, hpr_new] at he2
            exact absurd ⟨he1, he2⟩ (hno_old p₁ hlt₁)
          · rw [how_old p₁ hlt₁, how_old p₂ hlt₂] at he1
            rw [hpr_old p₁ hlt₁, hpr_old p₂ hlt₂] at he2
            exact h.slot_inj p₁ hlt₁ p₂ hlt₂ he1 he2
      models := fun u' v' => by
        by_cases hu : u' = u
        · subst hu
          rw [Function.update_self, Option.some.injEq]
          constructor
          · rintro rfl
            exact ⟨nSide, Nat.lt_succ_self _, how_new, by rw [hpr_new], by rw [hpr_new]⟩
          · rintro ⟨p, hp, h1, h2, h3⟩
            rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hp) with rfl | hlt
            · rw [hpr_new] at h3; dsimp only at h3; exact Fin.ext h3
            · rw [how_old p hlt] at h1; rw [hpr_old p hlt] at h2
              exact absurd ⟨h1, h2⟩ (hno_old p hlt)
        · rw [Function.update_of_ne hu, h.models u' v']
          constructor
          · rintro ⟨p, hp, h1, h2, h3⟩
            refine ⟨p, Nat.lt_succ_of_lt hp, ?_, ?_, ?_⟩
            · rw [how_old p hp]; exact h1
            · rw [hpr_old p hp]; exact h2
            · rw [hpr_old p hp]; exact h3
          · rintro ⟨p, hp, h1, h2, h3⟩
            rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hp) with rfl | hlt
            · rw [how_new] at h1; rw [hpr_new] at h2; dsimp only at h2
              exact absurd (Fin.ext (eq_of_feistelBucket_eq_of_keyQuotient_eq h1.symm h2.symm)) hu
            · rw [how_old p hlt] at h1; rw [hpr_old p hlt] at h2 h3
              exact ⟨p, hlt, h1, h2, h3⟩ }

/-- Popping slot `nSide - 1` (`0 < nSide`) refines `Function.update s_abs u_top none`. -/
theorem pop_last {U V bBits : ℕ} {hBkt : ℕ → ℕ} {nSide : ℕ}
    {ow ow' : ℕ → ℕ} {pr pr' : ℕ → ℕ × ℕ} {s_abs : Fin U → Option (Fin V)}
    (h : PoolItemsRefines U V bBits hBkt nSide ow pr s_abs) (hpos : 0 < nSide)
    {u_top : Fin U}
    (hfb : ow (nSide - 1) = feistelBucket bBits hBkt u_top.val)
    (hkq : (pr (nSide - 1)).1 = keyQuotient bBits u_top.val)
    (how_old : ∀ p < nSide - 1, ow' p = ow p)
    (hpr_old : ∀ p < nSide - 1, pr' p = pr p) :
    PoolItemsRefines U V bBits hBkt (nSide - 1) ow' pr' (Function.update s_abs u_top none) where
  slot_valid p hp := by
    rw [how_old p hp, hpr_old p hp]
    exact h.slot_valid p (hp.trans_le (Nat.sub_le _ 1))
  slot_inj p₁ hp₁ p₂ hp₂ he1 he2 := by
    rw [how_old p₁ hp₁, how_old p₂ hp₂] at he1
    rw [hpr_old p₁ hp₁, hpr_old p₂ hp₂] at he2
    exact h.slot_inj p₁ (hp₁.trans_le (Nat.sub_le _ 1)) p₂ (hp₂.trans_le (Nat.sub_le _ 1)) he1 he2
  models u' v' := by
    have hlast_lt : nSide - 1 < nSide := Nat.sub_lt hpos Nat.one_pos
    by_cases hu : u' = u_top
    · subst hu
      rw [Function.update_self]
      refine ⟨by rintro ⟨⟩, fun ⟨p, hp, h1, h2, _⟩ => ?_⟩
      rw [how_old p hp] at h1; rw [hpr_old p hp] at h2
      have heq := h.slot_inj p (hp.trans_le (Nat.sub_le _ 1)) (nSide - 1) hlast_lt
        (h1.trans hfb.symm) (h2.trans hkq.symm)
      omega
    · rw [Function.update_of_ne hu, h.models u' v']
      constructor
      · rintro ⟨p, hp, h1, h2, h3⟩
        have hne : p ≠ nSide - 1 := by
          rintro rfl
          exact hu (Fin.ext (eq_of_feistelBucket_eq_of_keyQuotient_eq
            (h1.symm.trans hfb) (h2.symm.trans hkq)))
        have hlt : p < nSide - 1 := by omega
        exact ⟨p, hlt, (how_old p hlt).trans h1, by rw [hpr_old p hlt]; exact h2,
          by rw [hpr_old p hlt]; exact h3⟩
      · rintro ⟨p, hp, h1, h2, h3⟩
        rw [how_old p hp] at h1; rw [hpr_old p hp] at h2 h3
        exact ⟨p, hp.trans_le (Nat.sub_le _ 1), h1, h2, h3⟩

end PoolItemsRefines

/-! ## Section 2: Unified Small-Regime Epoch (`SmallEpochLayout`, `N = 0`) on `SlotIoLayout` -/

private theorem feistelBucket_zero (hBkt : ℕ → ℕ) (x : ℕ) :
    feistelBucket 0 hBkt x = 0 := by
  simp [feistelBucket, keyLow, Nat.mod_one]

private theorem keyQuotient_zero (x : ℕ) :
    keyQuotient 0 x = x := by
  simp [keyQuotient]

private theorem feistelReconstruct_zero (hBkt : ℕ → ℕ) (x : ℕ) :
    feistelReconstruct 0 hBkt 0 x = x := by
  simp [feistelReconstruct, Nat.mod_one]

/-- Unconditional read-only preservation of `s` by `slotIoReadRawProg`. -/
theorem clientState_slotIoReadRawProg (x : SlotIoCtx × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (slotIoReadRawProg x) = s := by
  rcases x with ⟨⟨⟨up, sb⟩, ⟨⟨⟨⟨mb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩, ⟨⟨qb, vb⟩, nc⟩⟩⟩, idx⟩
  unfold slotIoReadRawProg
  dsimp only
  by_cases h0 : up = 0
  · simp only [h0, ↓reduceIte]
    by_cases hidx : idx < nc
    · rw [ite_eq_left hidx]
      by_cases hs : sb = 0
      · rw [ite_eq_left hs]; exact clientState_readPairGenProg ..
      · rw [ite_eq_right hs, StateTransitionSpec.clientState_bind,
          show (Memory.spec 0).clientState s (Memory.read mb) = s from rfl]
        by_cases hlt : idx < (Memory.spec 0).clientResult s (Memory.read mb)
        · rw [ite_eq_left hlt]; exact clientState_readPairGenProg ..
        · rw [ite_eq_right hlt, StateTransitionSpec.clientState_bind, clientState_readPairGenProg]
          by_cases hq : qb < wv
          · rw [ite_eq_left hq]; rfl
          · rw [ite_eq_right hq]; rfl
    · rw [ite_eq_right hidx]; rfl
  · simp only [h0, ↓reduceIte, pure_bind]
    exact runClient_state_pageReadVirtBoundedProg _ s

/-- Named layout descriptor for a small-regime epoch (`N = 0`, `nSide ≤ io.pgL.nCap`) backed by
`SlotIoLayout` (supporting both `usePaged = 0` direct streams and `usePaged ≠ 0` shared
`PageUnpermState` arenas). -/
structure SmallEpochLayout where
  /-- Base word address of the epoch header (`+0` holds `N = 0`, `+1` holds `nSide`). -/
  metaBase : ℕ
  /-- Key universe bound `U`. -/
  U : ℕ
  /-- Value universe bound `V`. -/
  V : ℕ
  /-- Underlying `[0, nSide)` pair-slot array (`qBits = keyBits U`, `vBits = valBits V`). -/
  io : SlotIoLayout

/-- Word-address footprint owned by `SmallEpochLayout`. -/
@[expose] def SmallEpochLayout.OwnsAddr (L : SmallEpochLayout) (addr : ℕ) : Prop :=
  addr = L.metaBase ∨ addr = L.metaBase + 1 ∨ L.io.OwnsAddr addr

/-- Static frontier and bit-width validity for `SmallEpochLayout`. -/
structure SmallEpochLayout.Valid (L : SmallEpochLayout) (w frontier : ℕ) : Prop where
  io_valid : L.io.Valid w frontier
  w_eq : w = L.io.pgL.w
  qBits_eq : L.io.pgL.qBits = keyBits L.U
  vBits_eq : L.io.pgL.vBits = valBits L.V
  hdr_frontier : L.metaBase + 2 ≤ frontier
  disjoint_hdr : ∀ addr, (addr = L.metaBase ∨ addr = L.metaBase + 1) → L.io.OwnsAddr addr → False

/-- Dynamic state invariant of a small-regime epoch (`N = 0`), reusing `PoolItemsRefines` at
`bBits = 0`. -/
@[expose] def SmallEpochLayout.StateInv (L : SmallEpochLayout) (slack : ℕ) (mem : ℕ → ℕ)
    (s_abs : Fin L.U → Option (Fin L.V)) : Prop :=
  mem L.metaBase = 0 ∧
  mem (L.metaBase + 1) ≤ L.io.pgL.nCap ∧
  L.io.StateInv (mem (L.metaBase + 1)) slack mem ∧
  PoolItemsRefines L.U L.V 0 (fun _ => 0) (mem (L.metaBase + 1)) (fun _ => 0)
    (slotIoPairAt L.io mem) s_abs

theorem SmallEpochLayout.StateInv.mono_slack {L : SmallEpochLayout} {s₁ s₂ : ℕ} {mem : ℕ → ℕ}
    {s_abs : Fin L.U → Option (Fin L.V)} (h : L.StateInv s₁ mem s_abs) (hle : s₁ ≤ s₂)
    (hs₂ : s₂ ≤ 24) : L.StateInv s₂ mem s_abs :=
  ⟨h.1, h.2.1, h.2.2.1.mono_slack hle hs₂, h.2.2.2⟩

theorem SmallEpochLayout.congr_of_outside {L : SmallEpochLayout} {w fr slack : ℕ}
    {mem₁ mem₂ : ℕ → ℕ} {s_abs : Fin L.U → Option (Fin L.V)}
    (hv : L.Valid w fr) (hinv : L.StateInv slack mem₁ s_abs)
    (hout : ∀ addr, L.OwnsAddr addr → mem₂ addr = mem₁ addr) :
    L.StateInv slack mem₂ s_abs := by
  have hm0 : mem₂ L.metaBase = mem₁ L.metaBase := hout _ (Or.inl rfl)
  have hm1 : mem₂ (L.metaBase + 1) = mem₁ (L.metaBase + 1) := hout _ (Or.inr (Or.inl rfl))
  obtain ⟨hio₂, harr₂⟩ := L.io.congr_of_outside hv.io_valid.w_pos hinv.2.2.1
    (fun a ha => hout a (Or.inr (Or.inr ha)))
  unfold SmallEpochLayout.StateInv
  rw [hm0, hm1]
  exact ⟨hinv.1, hinv.2.1, hio₂, hinv.2.2.2.congr (fun _ _ => rfl) harr₂⟩

/-- Initialize an empty small-regime epoch (`mem metaBase := 0`, `mem (metaBase + 1) := 0`). -/
def smallEpochInitProg (metaBase : ℕ) : Memory.Prog Unit := do
  Memory.write metaBase 0
  Memory.write (metaBase + 1) 0

theorem realizesBounded_smallEpochInit :
    RealizesBounded .exact smallEpochInitProg
      (WordEncoding.encode (α := ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w mb s => 1 < 2 ^ w ∧ mb + 2 ≤ s.frontier) (fun _ _ => 0) := by
  realize
  all_goals (have hfr_w := hmem.1; dsimp only [Fits] at *; omega)

theorem smallEpochInitProg_frame {L : SmallEpochLayout} :
    BoundedFrameProg L.OwnsAddr 2 (smallEpochInitProg L.metaBase) :=
  BoundedFrameProg.bind_prog
    (BoundedFrameProg.write_prog (Or.inl rfl) 0)
    (fun _ => BoundedFrameProg.write_prog (Or.inr (Or.inl rfl)) 0)

theorem smallEpochInitProg_spec {L : SmallEpochLayout} {w fr slack : ℕ} {s : Memory.State}
    (hv : L.Valid w fr) (hio0 : L.io.StateInv 0 slack s.mem) :
    let s' := (Memory.spec 0).clientState s (smallEpochInitProg L.metaBase)
    s'.frontier = s.frontier ∧
    L.StateInv slack s'.mem (fun _ => none) ∧
    (L.io.usePaged ≠ 0 →
      extractPageUnperm L.io.pgL s'.mem = extractPageUnperm L.io.pgL s.mem ∧
      ∀ idx < (extractPagePair L.io.pgL s.mem).virtLen L.io.partner.side,
        slotIoPairAt L.io.partner s'.mem idx = slotIoPairAt L.io.partner s.mem idx) := by
  dsimp only
  set s' := (Memory.spec 0).clientState s (smallEpochInitProg L.metaBase)
  have hf := smallEpochInitProg_frame (L := L)
  have hout_io' : ∀ addr, L.io.OwnsAddr addr → s'.mem addr = s.mem addr := fun addr hia => by
    change Function.update (Function.update s.mem L.metaBase 0) (L.metaBase + 1) 0 addr = s.mem addr
    have hne1 : addr ≠ L.metaBase + 1 := fun heq => hv.disjoint_hdr addr (Or.inr heq) hia
    have hne0 : addr ≠ L.metaBase := fun heq => hv.disjoint_hdr addr (Or.inl heq) hia
    rw [Function.update_of_ne hne1, Function.update_of_ne hne0]
  obtain ⟨hio', _⟩ := L.io.congr_of_outside hv.io_valid.w_pos hio0 hout_io'
  have hm0 : s'.mem L.metaBase = 0 := by
    change Function.update (Function.update s.mem L.metaBase 0) (L.metaBase + 1) 0 L.metaBase = 0
    rw [Function.update_of_ne (by omega), Function.update_self]
  have hm1 : s'.mem (L.metaBase + 1) = 0 := by
    change Function.update (Function.update s.mem L.metaBase 0)
      (L.metaBase + 1) 0 (L.metaBase + 1) = 0
    rw [Function.update_self]
  refine ⟨hf.frontier_eq s,
    ⟨hm0, by rw [hm1]; exact Nat.zero_le _, by rwa [hm1], ?_⟩, fun hnz => ?_⟩
  · rw [hm1]; exact PoolItemsRefines.empty ..
  · have hown_pg : ∀ addr, L.io.pgL.OwnsAddr addr → s'.mem addr = s.mem addr := fun addr ha => by
      apply hout_io' addr
      unfold SlotIoLayout.OwnsAddr; rwa [ite_eq_right hnz]
    have hu_eq : extractPageUnperm L.io.pgL s'.mem = extractPageUnperm L.io.pgL s.mem :=
      extractPageUnperm_congr hv.io_valid.w_pos (fun a ha => hown_pg a (Or.inl ha))
    refine ⟨hu_eq, fun idx hidx => ?_⟩
    unfold SlotIoLayout.StateInv at hio0; rw [ite_eq_right hnz] at hio0
    have hp_lt : (extractPageUnperm L.io.pgL s.mem).toPhys L.io.partner.side idx <
        L.io.pgL.nCap := (hio0.1.toPhys_lt hidx).trans_le hio0.2.2.2.1
    unfold slotIoPairAt
    have hp_nz : L.io.partner.usePaged ≠ 0 := hnz
    rw [ite_eq_right hp_nz, ite_eq_right hp_nz, SlotIoLayout.partner_pgL, hu_eq]
    exact arenaPairAt_congr hv.io_valid.w_pos (fun a ha => hown_pg a (Or.inr ha)) hp_lt

/-- Single step of linear key scan on `(ioctx, (mb, (nSide, u_key)))`:
starts with `Memory.read mb` so `1 ≤ memoryCost` holds unconditionally! -/
private def smallEpochScanStepProg :
    (SlotIoCtx × (ℕ × (ℕ × ℕ))) × ((ℕ × ℕ) × (ℕ × ℕ)) → Memory.Prog ((ℕ × ℕ) × (ℕ × ℕ))
  | ((ioctx, (mb, (nSide, u_key))), ((cur, found), (hitIdx, hitVal))) => do
    let _ ← Memory.read mb
    if cur < nSide then do
      let qv ← slotIoReadRawProg (ioctx, cur)
      if found = 0 ∧ qv.1 = u_key then
        pure ((cur + 1, 1), (cur, qv.2))
      else
        pure ((cur + 1, found), (hitIdx, hitVal))
    else
      pure ((cur, found), (hitIdx, hitVal))

private theorem memoryCost_smallEpochScanStepProg_pos
    (x : (SlotIoCtx × (ℕ × (ℕ × ℕ))) × ((ℕ × ℕ) × (ℕ × ℕ))) (s : Memory.State) :
    1 ≤ memoryCost (smallEpochScanStepProg x) s := by
  rcases x with ⟨⟨_, ⟨_, ⟨_, _⟩⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩
  unfold smallEpochScanStepProg
  simp only [Realization.memoryCost_bind', prog_memoryCost_read]
  omega

private theorem smallEpochScanStep_state_eq
    (x : (SlotIoCtx × (ℕ × (ℕ × ℕ))) × ((ℕ × ℕ) × (ℕ × ℕ))) (s : Memory.State) :
    (Memory.spec 0).clientState s (smallEpochScanStepProg x) = s := by
  rcases x with ⟨⟨ioctx, ⟨mb, ⟨nSide, u_key⟩⟩⟩, ⟨⟨cur, found⟩, ⟨hitIdx, hitVal⟩⟩⟩
  unfold smallEpochScanStepProg; dsimp only
  rw [StateTransitionSpec.clientState_bind]
  have hr_mb : (Memory.spec 0).clientState s (Memory.read mb) = s := rfl
  rw [hr_mb]
  split_ifs with hlt
  · rw [StateTransitionSpec.clientState_bind, clientState_slotIoReadRawProg]
    split_ifs <;> rfl
  · rfl

private def SmallEpochScanStepPre (w : ℕ) :
    (SlotIoCtx × (ℕ × (ℕ × ℕ))) × ((ℕ × ℕ) × (ℕ × ℕ)) → Memory.State → Prop
  | ((ioctx, (mb, (nSide, _u_key))), ((cur, _found), (_hitIdx, _hitVal))), s =>
    1 < 2 ^ w ∧ mb + 2 ≤ s.frontier ∧ cur ≤ nSide ∧
    nSide ≤ (SlotIoLayout.ofCtx ioctx).pgL.nCap ∧
    (SlotIoLayout.ofCtx ioctx).Valid w s.frontier

private theorem realizesBounded_smallEpochScanStep :
    RealizesBounded .exact smallEpochScanStepProg
      (WordEncoding.encode (α := (SlotIoCtx × (ℕ × (ℕ × ℕ))) × ((ℕ × ℕ) × (ℕ × ℕ))))
      (WordEncoding.encode (α := (ℕ × ℕ) × (ℕ × ℕ)))
      SmallEpochScanStepPre (fun _ _ => 0) := by
  have hrr := realizesBounded_slotIoReadRaw
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨up, sb⟩, ⟨⟨⟨⟨pmb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩,
      ⟨⟨qb, vb⟩, nc⟩⟩⟩, ⟨mb, ⟨nSide, u_key⟩⟩⟩, ⟨⟨cur, found⟩, ⟨hitIdx, hitVal⟩⟩⟩
    obtain ⟨hw1, hmb_fr, hcur_le, hn_le, hvIo⟩ := h
    have hnc_w : nc < 2 ^ w := by
      unfold SlotIoLayout.Valid SlotIoLayout.ofCtx PageArenaLayout.ofCtx at hvIo
      dsimp only at hvIo
      by_cases h0 : up = 0
      · rw [ite_eq_left h0] at hvIo; exact hvIo.2.2.2.2.1
      · rw [ite_eq_right h0] at hvIo; exact hvIo.2.2.2.2.2.2.2.2.2.2.1
    have hfr_w := hmem.1
    try dsimp only [Fits, SlotIoLayout.ofCtx, PageArenaLayout.ofCtx,
      StateTransitionSpec.clientState] at *
    first | exact hvIo | omega)

private def smallEpochScanLoopProg :
    ((SlotIoCtx × (ℕ × (ℕ × ℕ))) × ((ℕ × ℕ) × (ℕ × ℕ))) × ℕ → Memory.Prog ((ℕ × ℕ) × (ℕ × ℕ))
  | ((d, acc), fuel) => iterate smallEpochScanStepProg d fuel acc

private theorem realizesBounded_smallEpochScanLoop :
    RealizesBounded .exact smallEpochScanLoopProg
      (WordEncoding.encode (α := ((SlotIoCtx × (ℕ × (ℕ × ℕ))) × ((ℕ × ℕ) × (ℕ × ℕ))) × ℕ))
      (WordEncoding.encode (α := (ℕ × ℕ) × (ℕ × ℕ)))
      (fun w ((d, acc), fuel) s =>
        iterationSafe smallEpochScanStepProg SmallEpochScanStepPre w d fuel acc s)
      (fun _ _ => 0) :=
  RealizesBounded.iterate₀
    (WordEncoding.encode (α := SlotIoCtx × (ℕ × (ℕ × ℕ))))
    (WordEncoding.encode (α := (ℕ × ℕ) × (ℕ × ℕ)))
    realizesBounded_smallEpochScanStep
    memoryCost_smallEpochScanStepProg_pos

/-- Scan `[0, nSide)` in `ioctx` for key `u_key`, returning `(foundFlag, (idx, val))`. -/
private def smallEpochScanRawProg : (SlotIoCtx × ℕ) × ℕ → Memory.Prog (ℕ × (ℕ × ℕ))
  | ((ioctx, mb), u_key) => do
    let nSide ← Memory.read (mb + 1)
    let (_, (_, nCap)) := ioctx.2
    if nSide ≤ nCap then do
      let z0 ← pure 0
      let res ← smallEpochScanLoopProg
        (((ioctx, (mb, (nSide, u_key))), ((z0, z0), (z0, z0))), nSide)
      pure (res.1.2, res.2)
    else
      pure (0, (0, 0))

private theorem smallEpochScanLoop_safe_and_state {io : SlotIoLayout} {w mb nSide u_key : ℕ}
    {s : Memory.State} (hw1 : 1 < 2 ^ w) (hmb_fr : mb + 2 ≤ s.frontier)
    (hn : nSide ≤ io.pgL.nCap) (hvIo : io.Valid w s.frontier) :
    ∀ fuel cur found hIdx hVal,
      cur + fuel ≤ nSide →
      iterationSafe smallEpochScanStepProg SmallEpochScanStepPre w
        (io.toCtx, (mb, (nSide, u_key))) fuel ((cur, found), (hIdx, hVal)) s ∧
      (Memory.spec 0).clientState s
        (iterate smallEpochScanStepProg (io.toCtx, (mb, (nSide, u_key))) fuel
          ((cur, found), (hIdx, hVal))) = s ∧
      memoryCost (iterate smallEpochScanStepProg (io.toCtx, (mb, (nSide, u_key))) fuel
        ((cur, found), (hIdx, hVal))) s ≤ 21 * fuel := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ _; exact ⟨trivial, rfl, Nat.zero_le _⟩
  | succ k ih =>
    intro cur found hIdx hVal hle
    have hpre : SmallEpochScanStepPre w
        ((io.toCtx, (mb, (nSide, u_key))), ((cur, found), (hIdx, hVal))) s := by
      dsimp only [SmallEpochScanStepPre]; rw [SlotIoLayout.ofCtx_toCtx]
      exact ⟨hw1, hmb_fr, by omega, hn, hvIo⟩
    have hst1 := smallEpochScanStep_state_eq
      ((io.toCtx, (mb, (nSide, u_key))), ((cur, found), (hIdx, hVal))) s
    have hlt : cur < nSide := by omega
    have hres_cur :
        ((Memory.spec 0).clientResult s
          (smallEpochScanStepProg
            ((io.toCtx, (mb, (nSide, u_key))), ((cur, found), (hIdx, hVal))))).1.1 = cur + 1 := by
      unfold smallEpochScanStepProg; dsimp only
      rw [prog_clientResult_bind]
      have hr0 : (Memory.spec 0).clientState s (Memory.read mb) = s := rfl
      rw [hr0, ite_eq_left hlt, prog_clientResult_bind, clientState_slotIoReadRawProg]
      split_ifs <;> rfl
    have hcost1 : memoryCost (smallEpochScanStepProg
        ((io.toCtx, (mb, (nSide, u_key))), ((cur, found), (hIdx, hVal)))) s ≤ 21 := by
      unfold smallEpochScanStepProg; dsimp only
      rw [Realization.memoryCost_bind', prog_memoryCost_read]
      have hr0 : (Memory.spec 0).clientState s (Memory.read mb) = s := rfl
      rw [hr0, ite_eq_left hlt, Realization.memoryCost_bind', clientState_slotIoReadRawProg]
      have hrc := (slotIoReadProg_frame io cur).cost_le s
      unfold slotIoReadProg at hrc
      set qv := (Memory.spec 0).clientResult s (slotIoReadRawProg (io.toCtx, cur))
      have hc2 : memoryCost (if found = 0 ∧ qv.1 = u_key then pure ((cur + 1, 1), (cur, qv.2))
          else pure ((cur + 1, found), (hIdx, hVal))) s = 0 := by split_ifs <;> rfl
      omega
    set nxt := (Memory.spec 0).clientResult s
      (smallEpochScanStepProg ((io.toCtx, (mb, (nSide, u_key))), ((cur, found), (hIdx, hVal))))
    rcases nxt_eq : nxt with ⟨⟨c1, f1⟩, ⟨i1, v1⟩⟩
    have hc1 : c1 = cur + 1 := by
      have : nxt.1.1 = cur + 1 := hres_cur
      rw [nxt_eq] at this; exact this
    obtain ⟨hs_k, hst_k, hc_k⟩ := ih c1 f1 i1 v1 (by omega)
    refine ⟨?_, ?_, ?_⟩
    · unfold iterationSafe; rw [hst1]; change _ ∧ iterationSafe _ _ _ _ k nxt s
      rw [nxt_eq]; exact ⟨hpre, hs_k⟩
    · unfold iterate; rw [StateTransitionSpec.clientState_bind, hst1]
      change (Memory.spec 0).clientState s (iterate _ _ k nxt) = s
      rw [nxt_eq]; exact hst_k
    · unfold iterate; rw [Realization.memoryCost_bind', hst1]
      change _ + memoryCost (iterate _ _ k nxt) s ≤ _
      rw [nxt_eq]; omega

private theorem clientState_smallEpochScanRawProg (x : (SlotIoCtx × ℕ) × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (smallEpochScanRawProg x) = s := by
  rcases x with ⟨⟨⟨⟨up, sb⟩, ⟨p1, ⟨p2, nCap⟩⟩⟩, mb⟩, u_key⟩
  unfold smallEpochScanRawProg; dsimp only
  rw [StateTransitionSpec.clientState_bind]
  have hr0 : (Memory.spec 0).clientState s (Memory.read (mb + 1)) = s := rfl
  have hr0_v : (Memory.spec 0).clientResult s (Memory.read (mb + 1)) = s.mem (mb + 1) := rfl
  rw [hr0, hr0_v]
  split_ifs with hcap
  · simp only [pure_bind]
    rw [StateTransitionSpec.clientState_bind]
    unfold smallEpochScanLoopProg
    dsimp only
    have hex : ∀ k c f i v,
        (Memory.spec 0).clientState s
          (iterate smallEpochScanStepProg
            (((up, sb), (p1, (p2, nCap))), (mb, (s.mem (mb + 1), u_key))) k
            ((c, f), (i, v))) = s := by
      intro k; induction k with
      | zero => intros; rfl
      | succ k ih =>
        intro c f i v; unfold iterate
        rw [StateTransitionSpec.clientState_bind, smallEpochScanStep_state_eq]
        rcases (Memory.spec 0).clientResult s _ with ⟨⟨_, _⟩, ⟨_, _⟩⟩
        exact ih ..
    rw [hex _ 0 0 0 0]; rfl
  · rfl

private theorem realizesBounded_smallEpochScanRaw :
    RealizesBounded .exact smallEpochScanRawProg
      (WordEncoding.encode (α := (SlotIoCtx × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      (fun w ((ioctx, mb), _) s =>
        1 < 2 ^ w ∧ mb + 2 ≤ s.frontier ∧ (SlotIoLayout.ofCtx ioctx).Valid w s.frontier)
      (fun _ _ => 0) := by
  have hsl := realizesBounded_smallEpochScanLoop
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨up, sb⟩, ⟨⟨⟨⟨pmb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩,
      ⟨⟨qb, vb⟩, nc⟩⟩⟩, mb⟩, u_key⟩
    obtain ⟨hw1, hmb_fr, hvIo⟩ := h
    have hfr_w := hmem.1
    dsimp only at *
    try dsimp only [Fits, StateTransitionSpec.clientState] at *
    first | omega | (
      set ioctx : SlotIoCtx :=
        ((up, sb), ((((pmb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc)))
      have hio_eq := SlotIoLayout.toCtx_ofCtx ioctx
      have hnc_eq : (SlotIoLayout.ofCtx ioctx).pgL.nCap = nc := rfl
      obtain ⟨hsafe, _, _⟩ := smallEpochScanLoop_safe_and_state (io := SlotIoLayout.ofCtx ioctx)
        (mb := mb) (u_key := u_key) hw1 hmb_fr (hnc_eq ▸ (by omega : s.mem (mb + 1) ≤ nc)) hvIo
        (s.mem (mb + 1)) 0 0 0 0 (by omega)
      rwa [hio_eq] at hsafe))

private theorem smallEpochScanRawProg_spec {L : SmallEpochLayout} {w slack : ℕ}
    {s_abs : Fin L.U → Option (Fin L.V)} {s : Memory.State}
    (hv : L.Valid w s.frontier) (hinv : L.StateInv slack s.mem s_abs) (u : Fin L.U) :
    let res := (Memory.spec 0).clientResult s
      (smallEpochScanRawProg ((L.io.toCtx, L.metaBase), u.val))
    (Memory.spec 0).clientState s (smallEpochScanRawProg ((L.io.toCtx, L.metaBase), u.val)) = s ∧
    memoryCost (smallEpochScanRawProg ((L.io.toCtx, L.metaBase), u.val)) s ≤
      21 * s.mem (L.metaBase + 1) + 4 ∧
    (match s_abs u with
     | none => res = (0, (0, 0))
     | some v =>
       res.1 = 1 ∧ res.2.1 < s.mem (L.metaBase + 1) ∧ res.2.2 = v.val ∧
       slotIoPairAt L.io s.mem res.2.1 = (u.val, v.val)) := by
  dsimp only
  set nSide := s.mem (L.metaBase + 1)
  obtain ⟨_, hn_cap, hio_inv, href⟩ := hinv
  have hloop_inv : ∀ fuel cur found hIdx hVal,
      cur + fuel = nSide →
      (found = 0 → hIdx = 0 ∧ hVal = 0 ∧
        ∀ i < cur, (slotIoPairAt L.io s.mem i).1 ≠ u.val) →
      (found = 1 → hIdx < cur ∧ slotIoPairAt L.io s.mem hIdx = (u.val, hVal)) →
      found ≤ 1 →
      let r := (Memory.spec 0).clientResult s
        (iterate smallEpochScanStepProg (L.io.toCtx, (L.metaBase, (nSide, u.val))) fuel
          ((cur, found), (hIdx, hVal)))
      (r.1.2 = 0 ∧ r.2 = (0, 0) ∧ ∀ i < nSide, (slotIoPairAt L.io s.mem i).1 ≠ u.val) ∨
      (r.1.2 = 1 ∧ r.2.1 < nSide ∧ slotIoPairAt L.io s.mem r.2.1 = (u.val, r.2.2)) := by
    intro fuel
    induction fuel with
    | zero =>
      intro cur found hIdx hVal hsum hf0 hf1 hfle
      have hcur : cur = nSide := by omega
      subst hcur
      rcases (by omega : found = 0 ∨ found = 1) with rfl | rfl
      · obtain ⟨rfl, rfl, hall⟩ := hf0 rfl
        exact Or.inl ⟨rfl, rfl, hall⟩
      · obtain ⟨hlt, hpair⟩ := hf1 rfl
        exact Or.inr ⟨rfl, hlt, hpair⟩
    | succ k ih =>
      intro cur found hIdx hVal hsum hf0 hf1 hfle
      have hlt : cur < nSide := by omega
      obtain ⟨hr_res, _⟩ := slotIoReadProg_spec hio_inv hlt
      unfold slotIoReadProg at hr_res
      have hst1 := smallEpochScanStep_state_eq
        ((L.io.toCtx, (L.metaBase, (nSide, u.val))), ((cur, found), (hIdx, hVal))) s
      have hstep_res : (Memory.spec 0).clientResult s
          (smallEpochScanStepProg
            ((L.io.toCtx, (L.metaBase, (nSide, u.val))), ((cur, found), (hIdx, hVal)))) =
          if found = 0 ∧ (slotIoPairAt L.io s.mem cur).1 = u.val then
            ((cur + 1, 1), (cur, (slotIoPairAt L.io s.mem cur).2))
          else
            ((cur + 1, found), (hIdx, hVal)) := by
        unfold smallEpochScanStepProg; dsimp only
        rw [prog_clientResult_bind]
        have hr0 : (Memory.spec 0).clientState s (Memory.read L.metaBase) = s := rfl
        rw [hr0, ite_eq_left hlt, prog_clientResult_bind, clientState_slotIoReadRawProg, hr_res]
        split_ifs <;> rfl
      unfold iterate
      rw [prog_clientResult_bind, hst1, hstep_res]
      by_cases hhit : found = 0 ∧ (slotIoPairAt L.io s.mem cur).1 = u.val
      · rw [ite_eq_left hhit]
        exact ih (cur + 1) 1 cur (slotIoPairAt L.io s.mem cur).2 (by omega)
          (fun h => absurd h Nat.one_ne_zero)
          (fun _ => ⟨Nat.lt_succ_self cur, Prod.ext hhit.2 rfl⟩) le_rfl
      · rw [ite_eq_right hhit]
        refine ih (cur + 1) found hIdx hVal (by omega) (fun hf => ?_) (fun hf => ?_) hfle
        · obtain ⟨hi0, hv0, hall⟩ := hf0 hf
          refine ⟨hi0, hv0, fun i hi => ?_⟩
          rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hi) with rfl | hlt_i
          · exact fun heq => hhit ⟨hf, heq⟩
          · exact hall i hlt_i
        · obtain ⟨hi_lt, hpair⟩ := hf1 hf
          exact ⟨Nat.lt_succ_of_lt hi_lt, hpair⟩
  have hw_pos : 0 < w := hv.w_eq ▸ hv.io_valid.w_pos
  have hw1 : 1 < 2 ^ w := Nat.one_lt_two_pow hw_pos.ne'
  obtain ⟨_, hloop_st, hloop_cost⟩ := smallEpochScanLoop_safe_and_state (io := L.io)
    (mb := L.metaBase) (u_key := u.val) hw1 hv.hdr_frontier hn_cap hv.io_valid
    nSide 0 0 0 0 (by omega)
  have hst_tot := clientState_smallEpochScanRawProg ((L.io.toCtx, L.metaBase), u.val) s
  have hcost_tot :
      memoryCost (smallEpochScanRawProg ((L.io.toCtx, L.metaBase), u.val)) s ≤
        21 * nSide + 4 := by
    unfold smallEpochScanRawProg smallEpochScanLoopProg
    dsimp only [SlotIoLayout.toCtx, PageArenaLayout.toCtx] at hloop_st hloop_cost ⊢
    rw [Realization.memoryCost_bind', prog_memoryCost_read]
    have hr0 : (Memory.spec 0).clientState s (Memory.read (L.metaBase + 1)) = s := rfl
    have hr0_v : (Memory.spec 0).clientResult s (Memory.read (L.metaBase + 1)) = nSide := rfl
    rw [hr0, hr0_v, ite_eq_left hn_cap]
    simp only [pure_bind, Realization.memoryCost_bind']
    dsimp only [nSide] at hloop_st hloop_cost ⊢
    rw [hloop_st, memoryCost_pure]
    omega
  have hres_eq : (Memory.spec 0).clientResult s
      (smallEpochScanRawProg ((L.io.toCtx, L.metaBase), u.val)) =
      let r := (Memory.spec 0).clientResult s
        (iterate smallEpochScanStepProg (L.io.toCtx, (L.metaBase, (nSide, u.val))) nSide
          ((0, 0), (0, 0)))
      (r.1.2, r.2) := by
    unfold smallEpochScanRawProg smallEpochScanLoopProg
    dsimp only [SlotIoLayout.toCtx, PageArenaLayout.toCtx] at hloop_st ⊢
    rw [prog_clientResult_bind]
    have hr0 : (Memory.spec 0).clientState s (Memory.read (L.metaBase + 1)) = s := rfl
    have hr0_v : (Memory.spec 0).clientResult s (Memory.read (L.metaBase + 1)) = nSide := rfl
    rw [hr0, hr0_v, ite_eq_left hn_cap]
    simp only [pure_bind, prog_clientResult_bind]
    dsimp only [nSide] at hloop_st ⊢
    rw [hloop_st, prog_clientResult_pure]
  refine ⟨hst_tot, hcost_tot, ?_⟩
  rw [hres_eq]
  have hout := hloop_inv nSide 0 0 0 0 (Nat.zero_add nSide)
    (fun _ => ⟨rfl, rfl, fun _ hi => absurd hi (Nat.not_lt_zero _)⟩)
    (fun hc => absurd hc Nat.zero_ne_one) (Nat.zero_le 1)
  rcases hout with ⟨hf0, hp0, hall⟩ | ⟨hf1, hlt_i, hpair_i⟩
  · have hnone : s_abs u = none := by
      refine href.lookup_eq_none fun p hp ⟨_, hkq⟩ => ?_
      rw [keyQuotient_zero] at hkq
      exact hall p hp hkq
    rw [hnone]; dsimp only; rw [hf0, hp0]
  · have hsome := href.lookup_eq_some hlt_i
      (feistelBucket_zero _ u.val).symm
      (by rw [keyQuotient_zero, hpair_i])
    rw [hsome]
    dsimp only
    have hv_eq : (slotIoPairAt L.io s.mem
        ((Memory.spec 0).clientResult s
          (iterate smallEpochScanStepProg (L.io.toCtx, (L.metaBase, (nSide, u.val))) nSide
            ((0, 0), (0, 0)))).2.1).2 =
        ((Memory.spec 0).clientResult s
          (iterate smallEpochScanStepProg (L.io.toCtx, (L.metaBase, (nSide, u.val))) nSide
            ((0, 0), (0, 0)))).2.2 := by
      rw [hpair_i]
    exact ⟨hf1, hlt_i, hv_eq.symm, hpair_i.trans (Prod.ext rfl hv_eq.symm)⟩

/-- Slot index `r.2.1` in a `(found, (slotIdx, val))` linear-scan result. -/
abbrev scanResSlot (r : ℕ × (ℕ × ℕ)) : ℕ := r.2.1

/-- Value word `r.2.2` in a `(found, (slotIdx, val))` linear-scan result. -/
abbrev scanResVal (r : ℕ × (ℕ × ℕ)) : ℕ := r.2.2

/-- Small-regime `query(u)` returning `(0, 0)` for `none` and `(1, v)` for `some v` (`¬ReadsWidth`).
-/
def smallEpochQueryRawProg : (SlotIoCtx × ℕ) × ℕ → Memory.Prog (ℕ × ℕ)
  | (ctx, u_key) => do
    let r ← smallEpochScanRawProg (ctx, u_key)
    pure (r.1, scanResVal r)

/-- Small-regime `query(u)` wrapper on `SmallEpochLayout` (`¬ReadsWidth`). -/
@[expose] def smallEpochQueryProg (L : SmallEpochLayout) (u_key : ℕ) : Memory.Prog (ℕ × ℕ) :=
  smallEpochQueryRawProg ((L.io.toCtx, L.metaBase), u_key)

theorem realizesBounded_smallEpochQueryRaw :
    RealizesBounded .exact smallEpochQueryRawProg
      (WordEncoding.encode (α := (SlotIoCtx × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w ((ioctx, mb), _) s =>
        1 < 2 ^ w ∧ mb + 2 ≤ s.frontier ∧ (SlotIoLayout.ofCtx ioctx).Valid w s.frontier)
      (fun _ _ => 0) := by
  have hsc := realizesBounded_smallEpochScanRaw
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨up, sb⟩, ⟨⟨⟨⟨pmb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩,
      ⟨⟨qb, vb⟩, nc⟩⟩⟩, mb⟩, u_key⟩
    first | exact h.1 | exact h.2.1 | exact h.2.2)

theorem smallEpochQueryProg_spec {L : SmallEpochLayout} {w slack : ℕ}
    {s_abs : Fin L.U → Option (Fin L.V)} {s : Memory.State}
    (hv : L.Valid w s.frontier) (hinv : L.StateInv slack s.mem s_abs) (u : Fin L.U) :
    (Memory.spec 0).clientState s (smallEpochQueryProg L u.val) = s ∧
    memoryCost (smallEpochQueryProg L u.val) s ≤ 21 * s.mem (L.metaBase + 1) + 4 ∧
    (Memory.spec 0).clientResult s (smallEpochQueryProg L u.val) =
      match s_abs u with
      | none => (0, 0)
      | some v => (1, v.val) := by
  obtain ⟨hst, hcost, hres⟩ := smallEpochScanRawProg_spec hv hinv u
  unfold smallEpochQueryProg smallEpochQueryRawProg
  refine ⟨?_, ?_, ?_⟩
  · rw [StateTransitionSpec.clientState_bind, hst]; rfl
  · rw [Realization.memoryCost_bind', hst, memoryCost_pure]; omega
  · rw [prog_clientResult_bind, hst, prog_clientResult_pure]
    cases hs : s_abs u with
    | none => rw [hs] at hres; rw [hres]
    | some v => rw [hs] at hres; exact Prod.ext hres.1 hres.2.2.1

/-- Small-regime `insert(u, v)` (`¬ReadsWidth`). -/
def smallEpochInsertRawProg : ((SlotIoCtx × ℕ) × ℕ) × ℕ → Memory.Prog Unit
  | (((ioctx, mb), u_key), v_val) => do
    let r ← smallEpochScanRawProg ((ioctx, mb), u_key)
    if r.1 = 1 then
      slotIoWriteRawProg ((ioctx, scanResSlot r), (u_key, v_val))
    else do
      let nSide ← Memory.read (mb + 1)
      let (_, (_, nCap)) := ioctx.2
      if nSide < nCap then do
        slotIoAppendRawProg ((ioctx, nSide), (u_key, v_val))
        Memory.write (mb + 1) (nSide + 1)
      else
        pure ()

/-- Small-regime `insert(u, v)` wrapper on `SmallEpochLayout` (`¬ReadsWidth`). -/
@[expose] def smallEpochInsertProg (L : SmallEpochLayout) (u_key v_val : ℕ) : Memory.Prog Unit :=
  smallEpochInsertRawProg (((L.io.toCtx, L.metaBase), u_key), v_val)

theorem realizesBounded_smallEpochInsertRaw :
    RealizesBounded .exact smallEpochInsertRawProg
      (WordEncoding.encode (α := ((SlotIoCtx × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (((ioctx, mb), _), _) s =>
        1 < 2 ^ w ∧ mb + 2 ≤ s.frontier ∧ (SlotIoLayout.ofCtx ioctx).Valid w s.frontier)
      (fun _ _ => 0) := by
  have hsc := realizesBounded_smallEpochScanRaw
  have hwr := realizesBounded_slotIoWriteRaw
  have hap := realizesBounded_slotIoAppendRaw
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨up, sb⟩, ⟨⟨⟨⟨pmb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩,
      ⟨⟨qb, vb⟩, nc⟩⟩⟩, mb⟩, u_key⟩, v_val⟩
    obtain ⟨hw1, hmb_fr, hvIo⟩ := h
    set ioctx : SlotIoCtx :=
      ((up, sb), ((((pmb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc)))
    have hnc_w : nc < 2 ^ w := by
      unfold SlotIoLayout.Valid SlotIoLayout.ofCtx PageArenaLayout.ofCtx at hvIo
      dsimp only at hvIo
      by_cases h0 : up = 0
      · rw [ite_eq_left h0] at hvIo; exact hvIo.2.2.2.2.1
      · rw [ite_eq_right h0] at hvIo; exact hvIo.2.2.2.2.2.2.2.2.2.2.1
    have hfr_w := hmem.1
    have hsc_eq : ((Memory.spec 0).runClient s
        (smallEpochScanRawProg ((ioctx, mb), u_key))).2.1 = s :=
      clientState_smallEpochScanRawProg ((ioctx, mb), u_key) s
    dsimp only at *
    try simp only [Fits, StateTransitionSpec.clientState, hsc_eq] at *
    dsimp only [ioctx] at *
    first | exact hw1 | exact hmb_fr | exact hvIo | omega)

theorem smallEpochInsertProg_frame {L : SmallEpochLayout} (hw : 0 < L.io.pgL.w)
    (u_key v_val : ℕ) (s : Memory.State) :
    ((Memory.spec 0).clientState s (smallEpochInsertProg L u_key v_val)).frontier = s.frontier ∧
    (∀ addr, ¬L.OwnsAddr addr →
      ((Memory.spec 0).clientState s (smallEpochInsertProg L u_key v_val)).mem addr =
        s.mem addr) := by
  unfold smallEpochInsertProg smallEpochInsertRawProg
  rw [StateTransitionSpec.clientState_bind, clientState_smallEpochScanRawProg]
  set r := (Memory.spec 0).clientResult s (smallEpochScanRawProg ((L.io.toCtx, L.metaBase), u_key))
  split_ifs with hr1
  · have hwf := slotIoWriteProg_frame (io := L.io) hw r.2.1 u_key v_val
    unfold slotIoWriteProg at hwf
    exact ⟨hwf.frontier_eq s,
      fun addr ha => hwf.mem_outside s addr (fun hio => ha (Or.inr (Or.inr hio)))⟩
  · dsimp only [SlotIoLayout.toCtx, PageArenaLayout.toCtx]
    rw [StateTransitionSpec.clientState_bind]
    have hr0 : (Memory.spec 0).clientState s (Memory.read (L.metaBase + 1)) = s := rfl
    have hr0_v : (Memory.spec 0).clientResult s (Memory.read (L.metaBase + 1)) =
        s.mem (L.metaBase + 1) := rfl
    rw [hr0, hr0_v]
    split_ifs with hlt
    · rw [StateTransitionSpec.clientState_bind]
      have haf := slotIoAppendProg_frame (io := L.io) hw (s.mem (L.metaBase + 1)) u_key v_val
      unfold slotIoAppendProg SlotIoLayout.toCtx PageArenaLayout.toCtx at haf
      set s₁ := (Memory.spec 0).clientState s
        (slotIoAppendRawProg ((L.io.toCtx, s.mem (L.metaBase + 1)), (u_key, v_val)))
      refine ⟨haf.frontier_eq s, fun addr ha => ?_⟩
      change Function.update s₁.mem (L.metaBase + 1) _ addr = s.mem addr
      rw [Function.update_of_ne (fun heq => ha (Or.inr (Or.inl heq)))]
      exact haf.mem_outside s addr (fun hio => ha (Or.inr (Or.inr hio)))
    · exact ⟨rfl, fun _ _ => rfl⟩

theorem smallEpochInsertProg_spec {L : SmallEpochLayout} {w : ℕ}
    {s_abs : Fin L.U → Option (Fin L.V)} {s : Memory.State}
    (hv : L.Valid w s.frontier)
    (hinv : L.StateInv 0 s.mem s_abs) (u : Fin L.U) (v : Fin L.V)
    (hcap_new : s_abs u = none →
      s.mem (L.metaBase + 1) < L.io.pgL.nCap ∧
      (L.io.usePaged ≠ 0 → (extractPagePair L.io.pgL s.mem).totalItems + 1 ≤ L.io.pgL.nCap)) :
    let s' := (Memory.spec 0).clientState s (smallEpochInsertProg L u.val v.val)
    let slack' :=
      if L.io.usePaged = 0 ∨ (extractPageUnperm L.io.pgL s.mem).cleanPhase = 0 then 0 else 24
    s'.frontier = s.frontier ∧
    memoryCost (smallEpochInsertProg L u.val v.val) s ≤ 21 * s.mem (L.metaBase + 1) + 1410 ∧
    L.StateInv slack' s'.mem (Function.update s_abs u (some v)) ∧
    (∀ addr, ¬L.OwnsAddr addr → s'.mem addr = s.mem addr) ∧
    (L.io.usePaged ≠ 0 →
      (extractPagePair L.io.pgL s'.mem).virtLen L.io.partner.side =
        (extractPagePair L.io.pgL s.mem).virtLen L.io.partner.side ∧
      ∀ idx < (extractPagePair L.io.pgL s.mem).virtLen L.io.partner.side,
        slotIoPairAt L.io.partner s'.mem idx = slotIoPairAt L.io.partner s.mem idx) := by
  dsimp only
  have hvIo : L.io.Valid L.io.pgL.w s.frontier := hv.w_eq ▸ hv.io_valid
  obtain ⟨hsc_st, hsc_cost, hsc_res⟩ := smallEpochScanRawProg_spec hv hinv u
  have hq_u : u.val < 2 ^ L.io.pgL.qBits := by
    rw [hv.qBits_eq]; exact u.isLt.trans_le (Nat.le_pow_clog Nat.one_lt_two L.U)
  have hv_v : v.val < 2 ^ L.io.pgL.vBits := by
    rw [hv.vBits_eq]; exact v.isLt.trans_le (Nat.le_pow_clog Nat.one_lt_two L.V)
  set slack' :=
    if L.io.usePaged = 0 ∨ (extractPageUnperm L.io.pgL s.mem).cleanPhase = 0 then 0 else 24
  have hsl_le : slack' ≤ 24 := by dsimp only [slack']; split_ifs <;> decide
  unfold smallEpochInsertProg smallEpochInsertRawProg
  rw [StateTransitionSpec.clientState_bind, Realization.memoryCost_bind', hsc_st]
  cases hs_u : s_abs u with
  | some v_old =>
    rw [hs_u] at hsc_res
    obtain ⟨hr1, hidx_lt, _, hpair_old⟩ := hsc_res
    rw [ite_eq_left hr1]; dsimp only
    set idx := ((Memory.spec 0).clientResult s
      (smallEpochScanRawProg ((L.io.toCtx, L.metaBase), u.val))).2.1
    have hwc := (slotIoWriteProg_frame (io := L.io) hvIo.w_pos idx u.val v.val).cost_le s
    unfold slotIoWriteProg at hwc
    obtain ⟨hio', harr', hpart'⟩ := slotIoWriteProg_spec hvIo hinv.2.2.1 hidx_lt hq_u hv_v
    unfold slotIoWriteProg at hio' harr' hpart'
    set s' := (Memory.spec 0).clientState s (slotIoWriteRawProg ((L.io.toCtx, idx), (u.val, v.val)))
    have hwf := slotIoWriteProg_frame (io := L.io) hvIo.w_pos idx u.val v.val
    unfold slotIoWriteProg at hwf
    have hm0 : s'.mem L.metaBase = 0 :=
      (hwf.mem_outside s L.metaBase (fun hio => hv.disjoint_hdr _ (Or.inl rfl) hio)).trans hinv.1
    have hm1 : s'.mem (L.metaBase + 1) = s.mem (L.metaBase + 1) :=
      hwf.mem_outside s (L.metaBase + 1) (fun hio => hv.disjoint_hdr _ (Or.inr rfl) hio)
    have href' := hinv.2.2.2.update_at (pr' := slotIoPairAt L.io s'.mem) v hidx_lt
      (feistelBucket_zero _ u.val).symm
      (by rw [keyQuotient_zero, hpair_old])
      (by rw [harr' _ hidx_lt, ite_eq_left rfl, keyQuotient_zero])
      (fun q hq hne => by rw [harr' q hq, ite_eq_right hne])
    refine ⟨hwf.frontier_eq s, by omega,
      ⟨hm0, hm1 ▸ hinv.2.1, hm1 ▸ hio'.mono_slack (Nat.zero_le _) hsl_le, hm1 ▸ href'⟩,
      fun addr ha => hwf.mem_outside s addr (fun hio => ha (Or.inr (Or.inr hio))),
      fun hnz => ?_⟩
    obtain ⟨hu_eq, hp_eq⟩ := hpart' hnz
    exact ⟨congrArg (fun x => x.st.virtLen L.io.partner.side) hu_eq, hp_eq⟩
  | none =>
    rw [hs_u] at hsc_res
    obtain ⟨hn_lt, hpg_cap⟩ := hcap_new hs_u
    have hr_ne1 : ((Memory.spec 0).clientResult s
        (smallEpochScanRawProg ((L.io.toCtx, L.metaBase), u.val))).1 ≠ 1 := by
      rw [hsc_res]; decide
    rw [ite_eq_right hr_ne1]
    have hcap_io : if L.io.usePaged = 0 then s.mem (L.metaBase + 1) + 1 ≤ L.io.pgL.nCap
        else (extractPagePair L.io.pgL s.mem).totalItems + 1 ≤ L.io.pgL.nCap := by
      split_ifs with h0 <;> [omega; exact hpg_cap h0]
    obtain ⟨hio₁, harr₁, hpart₁⟩ := slotIoAppendProg_spec hvIo hinv.2.2.1 hcap_io hq_u hv_v
    have hac := (slotIoAppendProg_frame (io := L.io) hvIo.w_pos (s.mem (L.metaBase + 1))
      u.val v.val).cost_le s
    have haf := slotIoAppendProg_frame (io := L.io) hvIo.w_pos (s.mem (L.metaBase + 1))
      u.val v.val
    unfold slotIoAppendProg at hio₁ harr₁ hpart₁ hac haf
    rw [StateTransitionSpec.clientState_bind, Realization.memoryCost_bind', prog_memoryCost_read]
    have hr0 : (Memory.spec 0).clientState s (Memory.read (L.metaBase + 1)) = s := rfl
    have hr0_v : (Memory.spec 0).clientResult s (Memory.read (L.metaBase + 1)) =
        s.mem (L.metaBase + 1) := rfl
    rw [hr0, hr0_v]
    have hmatch : (match L.io.toCtx.2 with
        | (_, _, nCap) =>
          if s.mem (L.metaBase + 1) < nCap then do
            slotIoAppendRawProg ((L.io.toCtx, s.mem (L.metaBase + 1)), (u.val, v.val))
            Memory.write (L.metaBase + 1) (s.mem (L.metaBase + 1) + 1)
          else pure ()) =
        (if s.mem (L.metaBase + 1) < L.io.pgL.nCap then do
          slotIoAppendRawProg ((L.io.toCtx, s.mem (L.metaBase + 1)), (u.val, v.val))
          Memory.write (L.metaBase + 1) (s.mem (L.metaBase + 1) + 1)
        else pure ()) := rfl
    rw [hmatch, ite_eq_left hn_lt, StateTransitionSpec.clientState_bind,
      Realization.memoryCost_bind']
    set s₁ := (Memory.spec 0).clientState s
      (slotIoAppendRawProg ((L.io.toCtx, s.mem (L.metaBase + 1)), (u.val, v.val)))
    set m_fin := Function.update s₁.mem (L.metaBase + 1) (s.mem (L.metaBase + 1) + 1)
    have hst_w : ((Memory.spec 0).clientState s₁
        (Memory.write (L.metaBase + 1) (s.mem (L.metaBase + 1) + 1))).mem = m_fin := rfl
    have hfr_w : ((Memory.spec 0).clientState s₁
        (Memory.write (L.metaBase + 1) (s.mem (L.metaBase + 1) + 1))).frontier = s₁.frontier := rfl
    have hcost_w : memoryCost (Memory.write (L.metaBase + 1) (s.mem (L.metaBase + 1) + 1)) s₁ =
        1 := rfl
    rw [hst_w, hfr_w, hcost_w]
    have hout_w : ∀ addr, L.io.OwnsAddr addr → m_fin addr = s₁.mem addr := fun addr hia =>
      Function.update_of_ne (fun heq => hv.disjoint_hdr addr (Or.inr heq) hia) _ s₁.mem
    obtain ⟨hio_fin, harr_fin⟩ := L.io.congr_of_outside hvIo.w_pos hio₁ hout_w
    have hm0 : m_fin L.metaBase = 0 := by
      dsimp only [m_fin]
      rw [Function.update_of_ne (by omega)]
      exact (haf.mem_outside s L.metaBase (fun hia => hv.disjoint_hdr _ (Or.inl rfl) hia)).trans
        hinv.1
    have hm1 : m_fin (L.metaBase + 1) = s.mem (L.metaBase + 1) + 1 := Function.update_self ..
    have href' := hinv.2.2.2.append_new (ow' := fun _ => 0) (pr' := slotIoPairAt L.io m_fin)
      v hs_u (feistelBucket_zero _ u.val).symm
      (by
        rw [harr_fin _ (Nat.lt_succ_self _), harr₁ _ (Nat.lt_succ_self _),
          ite_eq_left rfl, keyQuotient_zero])
      (fun p _ => rfl)
      (fun p hp => by
        rw [harr_fin p (Nat.lt_succ_of_lt hp), harr₁ p (Nat.lt_succ_of_lt hp),
          ite_eq_right (Nat.ne_of_lt hp)])
    refine ⟨haf.frontier_eq s, by omega, ⟨hm0, by rw [hm1]; omega, by rwa [hm1], by rwa [hm1]⟩,
      fun addr ha => ?_, fun hnz => ?_⟩
    · dsimp only [m_fin]
      rw [Function.update_of_ne (fun heq => ha (Or.inr (Or.inl heq)))]
      exact haf.mem_outside s addr (fun hia => ha (Or.inr (Or.inr hia)))
    · obtain ⟨hvl₁, _, hp₁⟩ := hpart₁ hnz
      have hown_pg : ∀ addr, L.io.pgL.OwnsAddr addr → m_fin addr = s₁.mem addr := fun addr ha => by
        apply hout_w addr; unfold SlotIoLayout.OwnsAddr; rwa [ite_eq_right hnz]
      have hu_fin : extractPageUnperm L.io.pgL m_fin = extractPageUnperm L.io.pgL s₁.mem :=
        extractPageUnperm_congr hvIo.w_pos (fun a ha => hown_pg a (Or.inl ha))
      have hst_fin : extractPagePair L.io.pgL m_fin = extractPagePair L.io.pgL s₁.mem :=
        congrArg PageUnpermState.st hu_fin
      refine ⟨by rw [hst_fin, hvl₁], fun idx hidx => ?_⟩
      have hp_fin : slotIoPairAt L.io.partner m_fin idx = slotIoPairAt L.io.partner s₁.mem idx := by
        unfold SlotIoLayout.StateInv at hio₁; rw [ite_eq_right hnz] at hio₁
        have hidx₁ : idx < (extractPagePair L.io.pgL s₁.mem).virtLen L.io.partner.side := by
          rwa [hvl₁]
        have hp_lt : (extractPageUnperm L.io.pgL s₁.mem).toPhys L.io.partner.side idx <
            L.io.pgL.nCap := (hio₁.1.toPhys_lt hidx₁).trans_le hio₁.2.2.2.1
        unfold slotIoPairAt
        have hp_nz : L.io.partner.usePaged ≠ 0 := hnz
        rw [ite_eq_right hp_nz, ite_eq_right hp_nz, SlotIoLayout.partner_pgL, hu_fin]
        exact arenaPairAt_congr hvIo.w_pos (fun a ha => hown_pg a (Or.inr ha)) hp_lt
      exact hp_fin.trans (hp₁ idx hidx)

/-- Small-regime `delete(u)` (`¬ReadsWidth`). -/
def smallEpochDeleteRawProg : (SlotIoCtx × ℕ) × ℕ → Memory.Prog Unit
  | ((ioctx, mb), u_key) => do
    let r ← smallEpochScanRawProg ((ioctx, mb), u_key)
    if r.1 = 1 then do
      let nSide ← Memory.read (mb + 1)
      if 0 < nSide then do
        let last ← pure (nSide - 1)
        slotIoSwapRawProg (ioctx, (scanResSlot r, last))
        slotIoPopBackRawProg ioctx
        Memory.write (mb + 1) last
      else
        pure ()
    else
      pure ()

/-- Small-regime `delete(u)` wrapper on `SmallEpochLayout` (`¬ReadsWidth`). -/
@[expose] def smallEpochDeleteProg (L : SmallEpochLayout) (u_key : ℕ) : Memory.Prog Unit :=
  smallEpochDeleteRawProg ((L.io.toCtx, L.metaBase), u_key)

theorem realizesBounded_smallEpochDeleteRaw :
    RealizesBounded .exact smallEpochDeleteRawProg
      (WordEncoding.encode (α := (SlotIoCtx × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((ioctx, mb), _) s =>
        1 < 2 ^ w ∧ mb + 2 ≤ s.frontier ∧ (SlotIoLayout.ofCtx ioctx).Valid w s.frontier)
      (fun _ _ => 0) := by
  have hsc := realizesBounded_smallEpochScanRaw
  have hsw := realizesBounded_slotIoSwapRaw
  have hpb := realizesBounded_slotIoPopBackRaw
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨up, sb⟩, ⟨⟨⟨⟨pmb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩,
      ⟨⟨qb, vb⟩, nc⟩⟩⟩, mb⟩, u_key⟩
    obtain ⟨hw1, hmb_fr, hvIo⟩ := h
    set ioctx : SlotIoCtx :=
      ((up, sb), ((((pmb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc)))
    have hfr_w := hmem.1
    have hns_w := hmem.2 (mb + 1)
    have hsc_eq : ((Memory.spec 0).runClient s
        (smallEpochScanRawProg ((ioctx, mb), u_key))).2.1 = s :=
      clientState_smallEpochScanRawProg ((ioctx, mb), u_key) s
    dsimp only at *
    try simp only [Fits, StateTransitionSpec.clientState, hsc_eq] at *
    first | exact hw1 | exact hmb_fr | exact hvIo | omega | (
      set r₁ := ((Memory.spec 0).runClient s (smallEpochScanRawProg ((ioctx, mb), u_key))).1
      have hfr_sw := (slotIoSwapProg_frame (io := SlotIoLayout.ofCtx ioctx) hvIo.w_pos
        r₁.2.1 (s.mem (mb + 1) - 1)).frontier_eq s
      unfold slotIoSwapProg at hfr_sw
      have hio_eq := SlotIoLayout.toCtx_ofCtx ioctx
      rw [hio_eq] at hfr_sw
      first
      | (change (SlotIoLayout.ofCtx ioctx).Valid w
          ((Memory.spec 0).clientState s _).frontier
         rwa [hfr_sw])))

theorem smallEpochDeleteProg_spec {L : SmallEpochLayout} {w : ℕ}
    {s_abs : Fin L.U → Option (Fin L.V)} {s : Memory.State}
    (hv : L.Valid w s.frontier)
    (hinv : L.StateInv 0 s.mem s_abs) (u : Fin L.U) :
    let s' := (Memory.spec 0).clientState s (smallEpochDeleteProg L u.val)
    let slack' :=
      if L.io.usePaged = 0 ∨ (extractPageUnperm L.io.pgL s.mem).cleanPhase = 0 then 0 else 24
    s'.frontier = s.frontier ∧
    memoryCost (smallEpochDeleteProg L u.val) s ≤ 21 * s.mem (L.metaBase + 1) + 1500 ∧
    L.StateInv slack' s'.mem (Function.update s_abs u none) ∧
    (∀ addr, ¬L.OwnsAddr addr → s'.mem addr = s.mem addr) ∧
    (L.io.usePaged ≠ 0 →
      (extractPagePair L.io.pgL s'.mem).virtLen L.io.partner.side =
        (extractPagePair L.io.pgL s.mem).virtLen L.io.partner.side ∧
      ∀ idx < (extractPagePair L.io.pgL s.mem).virtLen L.io.partner.side,
        slotIoPairAt L.io.partner s'.mem idx = slotIoPairAt L.io.partner s.mem idx) := by
  dsimp only
  have hvIo : L.io.Valid L.io.pgL.w s.frontier := hv.w_eq ▸ hv.io_valid
  obtain ⟨hsc_st, hsc_cost, hsc_res⟩ := smallEpochScanRawProg_spec hv hinv u
  set slack' :=
    if L.io.usePaged = 0 ∨ (extractPageUnperm L.io.pgL s.mem).cleanPhase = 0 then 0 else 24
  have hsl_le : slack' ≤ 24 := by dsimp only [slack']; split_ifs <;> decide
  unfold smallEpochDeleteProg smallEpochDeleteRawProg
  rw [StateTransitionSpec.clientState_bind, Realization.memoryCost_bind', hsc_st]
  cases hs_u : s_abs u with
  | none =>
    rw [hs_u] at hsc_res
    have hr_ne1 : ((Memory.spec 0).clientResult s
        (smallEpochScanRawProg ((L.io.toCtx, L.metaBase), u.val))).1 ≠ 1 := by
      rw [hsc_res]; decide
    rw [ite_eq_right hr_ne1, memoryCost_pure, Function.update_eq_self_iff.mpr hs_u.symm]
    exact ⟨rfl, by omega, hinv.mono_slack (Nat.zero_le _) hsl_le, fun _ _ => rfl,
      fun _ => ⟨rfl, fun _ _ => rfl⟩⟩
  | some v_old =>
    rw [hs_u] at hsc_res
    obtain ⟨hr1, hidx_lt, _, hpair_old⟩ := hsc_res
    dsimp only
    set idx := ((Memory.spec 0).clientResult s
      (smallEpochScanRawProg ((L.io.toCtx, L.metaBase), u.val))).2.1
    set nSide := s.mem (L.metaBase + 1)
    have hpos : 0 < nSide := Nat.zero_lt_of_lt hidx_lt
    have hlast_lt : nSide - 1 < nSide := Nat.sub_lt hpos Nat.one_pos
    rw [ite_eq_left hr1]
    rw [StateTransitionSpec.clientState_bind, Realization.memoryCost_bind', prog_memoryCost_read]
    have hr0 : (Memory.spec 0).clientState s (Memory.read (L.metaBase + 1)) = s := rfl
    have hr0_v : (Memory.spec 0).clientResult s (Memory.read (L.metaBase + 1)) = nSide := rfl
    rw [hr0, hr0_v, ite_eq_left hpos]
    simp only [pure_bind, Realization.memoryCost_bind']
    repeat rw [StateTransitionSpec.clientState_bind]
    obtain ⟨hio₁, harr₁, hpart₁⟩ := slotIoSwapProg_spec hvIo hinv.2.2.1 hidx_lt hlast_lt
    have hswf := slotIoSwapProg_frame (io := L.io) hvIo.w_pos idx (nSide - 1)
    unfold slotIoSwapProg at hio₁ harr₁ hpart₁ hswf
    set s₁ := (Memory.spec 0).clientState s (slotIoSwapRawProg (L.io.toCtx, (idx, nSide - 1)))
    have hfr₁ : s₁.frontier = s.frontier := hswf.frontier_eq s
    obtain ⟨hio₂_raw, harr₂, hpart₂⟩ :=
      slotIoPopBackProg_spec (hfr₁.symm ▸ hvIo) hio₁ hpos
    have hpbf := slotIoPopBackProg_frame (io := L.io) hvIo.w_pos
    unfold slotIoPopBackProg at hio₂_raw harr₂ hpart₂ hpbf
    have hsl_eq : (if L.io.usePaged = 0 ∨
        (extractPageUnperm L.io.pgL s₁.mem).cleanPhase = 0 then 0 else 24) = slack' := by
      by_cases h0 : L.io.usePaged = 0
      · simp [slack', h0]
      · simp only [slack', h0, false_or, (hpart₁ h0).1]
    have hio₂ : L.io.StateInv (nSide - 1) slack'
        ((Memory.spec 0).clientState s₁ (slotIoPopBackRawProg L.io.toCtx)).mem :=
      hsl_eq ▸ hio₂_raw
    set s₂ := (Memory.spec 0).clientState s₁ (slotIoPopBackRawProg L.io.toCtx)
    have hfr₂ : s₂.frontier = s.frontier := (hpbf.frontier_eq s₁).trans hfr₁
    set m_fin := Function.update s₂.mem (L.metaBase + 1) (nSide - 1)
    have hst_w : ((Memory.spec 0).clientState s₂ (Memory.write (L.metaBase + 1) (nSide - 1))).mem =
        m_fin := rfl
    have hfr_w : ((Memory.spec 0).clientState s₂
        (Memory.write (L.metaBase + 1) (nSide - 1))).frontier = s₂.frontier := rfl
    have hc_w : memoryCost (Memory.write (L.metaBase + 1) (nSide - 1)) s₂ = 1 := rfl
    rw [hst_w, hfr_w, hc_w]
    have hout_w : ∀ addr, L.io.OwnsAddr addr → m_fin addr = s₂.mem addr := fun addr hia =>
      Function.update_of_ne (fun heq => hv.disjoint_hdr addr (Or.inr heq) hia) _ s₂.mem
    obtain ⟨hio_fin, harr_fin⟩ := L.io.congr_of_outside hvIo.w_pos hio₂ hout_w
    have hm0 : m_fin L.metaBase = 0 := by
      dsimp only [m_fin]; rw [Function.update_of_ne (by omega)]
      exact (hpbf.mem_outside s₁ L.metaBase (fun hia => hv.disjoint_hdr _ (Or.inl rfl) hia)).trans
        ((hswf.mem_outside s L.metaBase (fun hia => hv.disjoint_hdr _ (Or.inl rfl) hia)).trans
          hinv.1)
    have hm1 : m_fin (L.metaBase + 1) = nSide - 1 := Function.update_self ..
    have href₁ := (hinv.2.2.2.apply_swap (sw := ⟨idx, nSide - 1⟩) hidx_lt hlast_lt).congr
      (ow₂ := fun _ => 0) (pr₂ := slotIoPairAt L.io s₁.mem)
      (fun p _ => by
        let sw0 : PhysSwap := ⟨idx, nSide - 1⟩
        by_cases h1 : p = idx
        · subst h1; exact (sw0.apply_p₁ (fun _ => 0)).symm
        · by_cases h2 : p = nSide - 1
          · subst h2; exact (sw0.apply_p₂ (fun _ => 0)).symm
          · exact (sw0.apply_of_ne (fun _ => 0) h1 h2).symm)
      (fun p hp => harr₁ p hp)
    have htop_u : (slotIoPairAt L.io s₁.mem (nSide - 1)).1 = keyQuotient 0 u.val := by
      rw [harr₁ (nSide - 1) hlast_lt, PhysSwap.apply_p₂, hpair_old, keyQuotient_zero]
    have href' := href₁.pop_last (ow' := fun _ => 0) (pr' := slotIoPairAt L.io m_fin)
      hpos (feistelBucket_zero _ u.val).symm htop_u
      (fun _ _ => rfl)
      (fun p hp => (harr_fin p hp).trans (harr₂ p hp))
    have hc1 := hswf.cost_le s
    have hc2 := hpbf.cost_le s₁
    refine ⟨hfr₂, by omega, ⟨hm0, by rw [hm1]; have := hinv.2.1; omega, by rwa [hm1], by rwa [hm1]⟩,
      fun addr ha => ?_, fun hnz => ?_⟩
    · dsimp only [m_fin]
      rw [Function.update_of_ne (fun heq => ha (Or.inr (Or.inl heq))),
        hpbf.mem_outside s₁ addr (fun hia => ha (Or.inr (Or.inr hia))),
        hswf.mem_outside s addr (fun hia => ha (Or.inr (Or.inr hia)))]
    · obtain ⟨hu₁, hp₁⟩ := hpart₁ hnz
      obtain ⟨hvl₂, _, hp₂⟩ := hpart₂ hnz
      have hst₁ : extractPagePair L.io.pgL s₁.mem = extractPagePair L.io.pgL s.mem :=
        congrArg PageUnpermState.st hu₁
      have hown_pg : ∀ addr, L.io.pgL.OwnsAddr addr → m_fin addr = s₂.mem addr := fun addr ha => by
        apply hout_w addr; unfold SlotIoLayout.OwnsAddr; rwa [ite_eq_right hnz]
      have hu_fin : extractPageUnperm L.io.pgL m_fin = extractPageUnperm L.io.pgL s₂.mem :=
        extractPageUnperm_congr hvIo.w_pos (fun a ha => hown_pg a (Or.inl ha))
      have hst_fin : extractPagePair L.io.pgL m_fin = extractPagePair L.io.pgL s₂.mem :=
        congrArg PageUnpermState.st hu_fin
      refine ⟨by rw [hst_fin, hvl₂, hst₁], fun idx₂ hidx₂ => ?_⟩
      have hp_fin :
          slotIoPairAt L.io.partner m_fin idx₂ = slotIoPairAt L.io.partner s₂.mem idx₂ := by
        unfold SlotIoLayout.StateInv at hio₂; rw [ite_eq_right hnz] at hio₂
        have hidx_s₂ : idx₂ < (extractPagePair L.io.pgL s₂.mem).virtLen L.io.partner.side := by
          rwa [hvl₂, hst₁]
        have hp_lt : (extractPageUnperm L.io.pgL s₂.mem).toPhys L.io.partner.side idx₂ <
            L.io.pgL.nCap := (hio₂.1.toPhys_lt hidx_s₂).trans_le hio₂.2.2.2.1
        unfold slotIoPairAt
        have hp_nz : L.io.partner.usePaged ≠ 0 := hnz
        rw [ite_eq_right hp_nz, ite_eq_right hp_nz, SlotIoLayout.partner_pgL, hu_fin]
        exact arenaPairAt_congr hvIo.w_pos (fun a ha => hown_pg a (Or.inr ha)) hp_lt
      exact hp_fin.trans ((hp₂ idx₂ (hst₁.symm ▸ hidx₂)).trans (hp₁ idx₂ hidx₂))

/-- Small-regime `popAny` (`0 < nSide`), returning `(u, v)` from slot `nSide - 1` (`¬ReadsWidth`).
-/
def smallEpochPopAnyRawProg : SlotIoCtx × ℕ → Memory.Prog (ℕ × ℕ)
  | (ioctx, mb) => do
    let nSide ← Memory.read (mb + 1)
    if 0 < nSide then do
      let last ← pure (nSide - 1)
      let qv ← slotIoReadRawProg (ioctx, last)
      slotIoPopBackRawProg ioctx
      Memory.write (mb + 1) last
      pure qv
    else
      pure (0, 0)

/-- Small-regime `popAny` wrapper on `SmallEpochLayout` (`¬ReadsWidth`). -/
@[expose] def smallEpochPopAnyProg (L : SmallEpochLayout) : Memory.Prog (ℕ × ℕ) :=
  smallEpochPopAnyRawProg (L.io.toCtx, L.metaBase)

theorem realizesBounded_smallEpochPopAnyRaw :
    RealizesBounded .exact smallEpochPopAnyRawProg
      (WordEncoding.encode (α := SlotIoCtx × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w (ioctx, mb) s =>
        1 < 2 ^ w ∧ mb + 2 ≤ s.frontier ∧ (SlotIoLayout.ofCtx ioctx).Valid w s.frontier)
      (fun _ _ => 0) := by
  have hrr := realizesBounded_slotIoReadRaw
  have hpb := realizesBounded_slotIoPopBackRaw
  realize
  all_goals (
    rcases d with ⟨⟨⟨up, sb⟩, ⟨⟨⟨⟨pmb, od⟩, ⟨ot, pb⟩⟩, ⟨⟨wv, pg⟩, ⟨mp, ib⟩⟩⟩,
      ⟨⟨qb, vb⟩, nc⟩⟩⟩, mb⟩
    obtain ⟨hw1, hmb_fr, hvIo⟩ := h
    set ioctx : SlotIoCtx :=
      ((up, sb), ((((pmb, od), (ot, pb)), ((wv, pg), (mp, ib))), ((qb, vb), nc)))
    have hfr_w := hmem.1
    have hns_w := hmem.2 (mb + 1)
    have hsr_eq := clientState_slotIoReadRawProg (ioctx, s.mem (mb + 1) - 1) s
    dsimp only [ioctx, StateTransitionSpec.clientState] at hsr_eq
    dsimp only at *
    try dsimp only [Fits, StateTransitionSpec.clientState] at *
    try rw [hsr_eq] at *
    first | exact hvIo | omega)

theorem smallEpochPopAnyProg_spec {L : SmallEpochLayout} {w : ℕ}
    {s_abs : Fin L.U → Option (Fin L.V)} {s : Memory.State}
    (hv : L.Valid w s.frontier)
    (hinv : L.StateInv 0 s.mem s_abs) (hpos : 0 < s.mem (L.metaBase + 1)) :
    let s' := (Memory.spec 0).clientState s (smallEpochPopAnyProg L)
    let uv := (Memory.spec 0).clientResult s (smallEpochPopAnyProg L)
    let slack' :=
      if L.io.usePaged = 0 ∨ (extractPageUnperm L.io.pgL s.mem).cleanPhase = 0 then 0 else 24
    s'.frontier = s.frontier ∧
    memoryCost (smallEpochPopAnyProg L) s ≤ 1430 ∧
    s'.mem (L.metaBase + 1) = s.mem (L.metaBase + 1) - 1 ∧
    (∃ (u : Fin L.U) (v : Fin L.V),
      uv = (u.val, v.val) ∧
      s_abs u = some v ∧
      L.StateInv slack' s'.mem (Function.update s_abs u none)) ∧
    (∀ addr, ¬L.OwnsAddr addr → s'.mem addr = s.mem addr) ∧
    (L.io.usePaged ≠ 0 →
      (extractPagePair L.io.pgL s'.mem).virtLen L.io.partner.side =
        (extractPagePair L.io.pgL s.mem).virtLen L.io.partner.side ∧
      (extractPagePair L.io.pgL s'.mem).totalItems =
        (extractPagePair L.io.pgL s.mem).totalItems - 1 ∧
      ∀ idx < (extractPagePair L.io.pgL s.mem).virtLen L.io.partner.side,
        slotIoPairAt L.io.partner s'.mem idx = slotIoPairAt L.io.partner s.mem idx) := by
  dsimp only
  have hvIo : L.io.Valid L.io.pgL.w s.frontier := hv.w_eq ▸ hv.io_valid
  set nSide := s.mem (L.metaBase + 1)
  have hlast_lt : nSide - 1 < nSide := Nat.sub_lt hpos Nat.one_pos
  obtain ⟨hr_res, hr_st⟩ := slotIoReadProg_spec hinv.2.2.1 hlast_lt
  have hrf := slotIoReadProg_frame L.io (nSide - 1)
  obtain ⟨hio₂, harr₂, hpart₂⟩ := slotIoPopBackProg_spec hvIo hinv.2.2.1 hpos
  have hpbf := slotIoPopBackProg_frame (io := L.io) hvIo.w_pos
  unfold slotIoReadProg at hr_res hr_st hrf
  unfold slotIoPopBackProg at hio₂ harr₂ hpart₂ hpbf
  set slack' :=
    if L.io.usePaged = 0 ∨ (extractPageUnperm L.io.pgL s.mem).cleanPhase = 0 then 0 else 24
  unfold smallEpochPopAnyProg smallEpochPopAnyRawProg
  rw [StateTransitionSpec.clientState_bind, prog_clientResult_bind,
    Realization.memoryCost_bind', prog_memoryCost_read]
  have hr0 : (Memory.spec 0).clientState s (Memory.read (L.metaBase + 1)) = s := rfl
  have hr0_v : (Memory.spec 0).clientResult s (Memory.read (L.metaBase + 1)) = nSide := rfl
  rw [hr0, hr0_v, ite_eq_left hpos]
  simp only [pure_bind, Realization.memoryCost_bind']
  repeat rw [StateTransitionSpec.clientState_bind]
  repeat rw [prog_clientResult_bind]
  rw [hr_st, hr_res]
  set s₂ := (Memory.spec 0).clientState s (slotIoPopBackRawProg L.io.toCtx)
  set m_fin := Function.update s₂.mem (L.metaBase + 1) (nSide - 1)
  have hst_w : ((Memory.spec 0).clientState s₂ (Memory.write (L.metaBase + 1) (nSide - 1))).mem =
      m_fin := rfl
  have hfr_w : ((Memory.spec 0).clientState s₂
      (Memory.write (L.metaBase + 1) (nSide - 1))).frontier = s₂.frontier := rfl
  have hc_w : memoryCost (Memory.write (L.metaBase + 1) (nSide - 1)) s₂ = 1 := rfl
  rw [StateTransitionSpec.clientState_pure, prog_clientResult_pure, memoryCost_pure,
    hst_w, hfr_w, hc_w]
  have hout_w : ∀ addr, L.io.OwnsAddr addr → m_fin addr = s₂.mem addr := fun addr hia =>
    Function.update_of_ne (fun heq => hv.disjoint_hdr addr (Or.inr heq) hia) _ s₂.mem
  obtain ⟨hio_fin, harr_fin⟩ := L.io.congr_of_outside hvIo.w_pos hio₂ hout_w
  have hm0 : m_fin L.metaBase = 0 := by
    dsimp only [m_fin]; rw [Function.update_of_ne (by omega)]
    exact (hpbf.mem_outside s L.metaBase (fun hia => hv.disjoint_hdr _ (Or.inl rfl) hia)).trans
      hinv.1
  have hm1 : m_fin (L.metaBase + 1) = nSide - 1 := Function.update_self ..
  have hsk := hinv.2.2.2.slot_key_val hlast_lt
  dsimp only at hsk
  simp only [feistelReconstruct_zero] at hsk
  obtain ⟨hu_lt, hv_lt, _, _, hs_top⟩ := hsk
  let u_top : Fin L.U := ⟨(slotIoPairAt L.io s.mem (nSide - 1)).1, hu_lt⟩
  let v_top : Fin L.V := ⟨(slotIoPairAt L.io s.mem (nSide - 1)).2, hv_lt⟩
  have href' := hinv.2.2.2.pop_last (ow' := fun _ => 0) (pr' := slotIoPairAt L.io m_fin)
    (u_top := u_top) hpos (feistelBucket_zero _ _).symm
    (keyQuotient_zero _).symm (fun _ _ => rfl)
    (fun p hp => (harr_fin p hp).trans (harr₂ p hp))
  have hc1 := hrf.cost_le s
  have hc2 := hpbf.cost_le s
  refine ⟨hpbf.frontier_eq s, by omega, hm1,
    ⟨u_top, v_top, Prod.ext rfl rfl, hs_top,
      ⟨hm0, by rw [hm1]; have := hinv.2.1; omega, by rwa [hm1], by rwa [hm1]⟩⟩,
    fun addr ha => ?_, fun hnz => ?_⟩
  · dsimp only [m_fin]
    rw [Function.update_of_ne (fun heq => ha (Or.inr (Or.inl heq)))]
    exact hpbf.mem_outside s addr (fun hia => ha (Or.inr (Or.inr hia)))
  · obtain ⟨hvl₂, hti₂, hp₂⟩ := hpart₂ hnz
    have hown_pg : ∀ addr, L.io.pgL.OwnsAddr addr → m_fin addr = s₂.mem addr := fun addr ha => by
      apply hout_w addr; unfold SlotIoLayout.OwnsAddr; rwa [ite_eq_right hnz]
    have hu_fin : extractPageUnperm L.io.pgL m_fin = extractPageUnperm L.io.pgL s₂.mem :=
      extractPageUnperm_congr hvIo.w_pos (fun a ha => hown_pg a (Or.inl ha))
    have hst_fin : extractPagePair L.io.pgL m_fin = extractPagePair L.io.pgL s₂.mem :=
      congrArg PageUnpermState.st hu_fin
    refine ⟨by rw [hst_fin, hvl₂], by rw [hst_fin, hti₂], fun idx hidx => ?_⟩
    have hp_fin : slotIoPairAt L.io.partner m_fin idx = slotIoPairAt L.io.partner s₂.mem idx := by
      unfold SlotIoLayout.StateInv at hio₂; rw [ite_eq_right hnz] at hio₂
      have hidx₂ : idx < (extractPagePair L.io.pgL s₂.mem).virtLen L.io.partner.side := by
        rwa [hvl₂]
      have hp_lt : (extractPageUnperm L.io.pgL s₂.mem).toPhys L.io.partner.side idx <
          L.io.pgL.nCap := (hio₂.1.toPhys_lt hidx₂).trans_le hio₂.2.2.2.1
      unfold slotIoPairAt
      have hp_nz : L.io.partner.usePaged ≠ 0 := hnz
      rw [ite_eq_right hp_nz, ite_eq_right hp_nz, SlotIoLayout.partner_pgL, hu_fin]
      exact arenaPairAt_congr hvIo.w_pos (fun a ha => hown_pg a (Or.inr ha)) hp_lt
    exact hp_fin.trans (hp₂ idx hidx)

/-! ## Section 3: Pure `FallbackState` Model and Pigeonhole `K`-Block Promotion -/

/-- Pure state of the deterministic `1 · OPT` fallback pool (`fallbackMode = 1`) for a large epoch:
`[0, fullBlocks * K)` is partitioned into `fullBlocks` single-bucket `K`-item blocks (`ownerBlk`),
while `[fullBlocks * K, nSide)` holds `tailLen ≤ 6 * M * K` individual tail items (`ownerTail`). -/
structure FallbackState where
  /-- Number of buckets `M = numBucketsWhp N`. -/
  M : ℕ
  /-- Slab size `K = slabSizeWhp N`. -/
  K : ℕ
  /-- Total live slots `nSide ≤ N`. -/
  nSide : ℕ
  /-- Number of full single-bucket `K`-item blocks at `[0, fullBlocks * K)`. -/
  fullBlocks : ℕ
  /-- Bucket owner `< M` of each full block `blk < fullBlocks`. -/
  ownerBlk : ℕ → ℕ
  /-- Bucket owner `< M` of each tail offset `t < nSide - fullBlocks * K`. -/
  ownerTail : ℕ → ℕ

namespace FallbackState

/-- Number of tail items `nSide - fullBlocks * K`. -/
@[expose] def tailLen (fb : FallbackState) : ℕ :=
  fb.nSide - fb.fullBlocks * fb.K

/-- Bucket owner `< M` of virtual slot `p < nSide`. -/
@[expose] def owner (fb : FallbackState) (p : ℕ) : ℕ :=
  if p < fb.fullBlocks * fb.K then
    fb.ownerBlk (p / fb.K)
  else
    fb.ownerTail (p - fb.fullBlocks * fb.K)

/-- Structural validity invariant of `FallbackState` with configurable tail bound `maxT`. -/
structure ValidWith (fb : FallbackState) (maxT : ℕ) : Prop where
  M_ge : 2 ≤ fb.M
  K_ge : 64 ≤ fb.K
  blocks_le : fb.fullBlocks * fb.K ≤ fb.nSide
  tail_le : fb.tailLen ≤ maxT
  blk_lt : ∀ blk < fb.fullBlocks, fb.ownerBlk blk < fb.M
  tail_lt : ∀ t < fb.tailLen, fb.ownerTail t < fb.M

/-- Resting `FallbackState` validity (`tailLen ≤ 6 * M * K`). -/
abbrev Valid (fb : FallbackState) : Prop :=
  fb.ValidWith (6 * fb.M * fb.K)

theorem ValidWith.owner_lt {fb : FallbackState} {maxT p : ℕ} (hv : fb.ValidWith maxT)
    (hp : p < fb.nSide) : fb.owner p < fb.M := by
  have hK : 0 < fb.K := by have := hv.K_ge; omega
  unfold owner
  split_ifs with hlt
  · exact hv.blk_lt _ ((Nat.div_lt_iff_lt_mul hK).mpr hlt)
  · exact hv.tail_lt _ (by unfold tailLen; omega)

/-- Pigeonhole principle for tail promotion: whenever `M * K ≤ tailLen` and every
`ownerTail t < M` (`t < tailLen`), some bucket `b < M` occurs at least `K` times in
`[0, tailLen)`. -/
theorem exists_heavy_tail_bkt {M K tailLen : ℕ} {ownerTail : ℕ → ℕ}
    (hM : 1 ≤ M) (hK : 1 ≤ K) (hlen : M * K ≤ tailLen)
    (hown : ∀ t < tailLen, ownerTail t < M) :
    ∃ b < M, K ≤ ((Finset.range tailLen).filter (fun t => ownerTail t = b)).card := by
  by_contra hall
  push Not at hall
  have hpart : ∑ b ∈ Finset.range M,
      ((Finset.range tailLen).filter (fun t => ownerTail t = b)).card = tailLen := by
    have hmaps : ∀ t ∈ Finset.range tailLen, ownerTail t ∈ Finset.range M :=
      fun t ht => mem_range.mpr (hown t (mem_range.mp ht))
    simpa only [card_range] using card_eq_sum_card_fiberwise hmaps |>.symm
  have hsum_le : ∑ b ∈ Finset.range M,
      ((Finset.range tailLen).filter (fun t => ownerTail t = b)).card ≤
      ∑ _b ∈ Finset.range M, (K - 1) :=
    Finset.sum_le_sum fun b hb => Nat.le_sub_one_of_lt (hall b (mem_range.mp hb))
  rw [hpart, sum_const, card_range, smul_eq_mul] at hsum_le
  have hlt_mk : M * (K - 1) < M * K := Nat.mul_lt_mul_of_pos_left (by omega) hM
  omega

end FallbackState

/-! ## Section 4: `FallbackLayout` Memory Coupling, `enterFallbackProg`, and Fallback Operations -/

/-- Extract pure `FallbackState` from `mp : BpMetaLayout` (`fullBlocks` in `+10`, `ownerBlk` in
`offSlabOwner` lane `1`, `ownerTail` in `offTailDir`). -/
@[expose] def extractFallback (mp : BpMetaLayout) (mem : ℕ → ℕ) : FallbackState where
  M := mp.M
  K := mp.K
  nSide := mem (mp.metaBase + 1)
  fullBlocks := mem (mp.metaBase + 10)
  ownerBlk := fun blk =>
    if blk < mp.maxBlocks then
      readPacked (mp.metaBase + mp.offSlabOwner) mp.ptrB mp.w mem (4 * blk + 1)
    else 0
  ownerTail := fun t =>
    if t < 8 * mp.M * mp.K then
      readPacked (mp.metaBase + mp.offTailDir) mp.ptrB mp.w mem t
    else 0

theorem extractFallback_congr {mp : BpMetaLayout} {mem₁ mem₂ : ℕ → ℕ} (hw : 0 < mp.w)
    (heq : ∀ addr, mp.OwnsMetaAddr addr → mem₁ addr = mem₂ addr) :
    extractFallback mp mem₁ = extractFallback mp mem₂ := by
  have hs1 : mem₁ (mp.metaBase + 1) = mem₂ (mp.metaBase + 1) := heq _ (Or.inl rfl)
  have hs10 : mem₁ (mp.metaBase + 10) = mem₂ (mp.metaBase + 10) :=
    heq _ (Or.inr (Or.inl ⟨le_rfl, by omega⟩))
  have hso : ∀ blk < mp.maxBlocks,
      readPacked (mp.metaBase + mp.offSlabOwner) mp.ptrB mp.w mem₁ (4 * blk + 1) =
        readPacked (mp.metaBase + mp.offSlabOwner) mp.ptrB mp.w mem₂ (4 * blk + 1) :=
    fun blk hblk => readPacked_congr hw (N := 4 * mp.maxBlocks)
      (fun a ha => heq a (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha))))))) (by omega)
  have htd : ∀ t < 8 * mp.M * mp.K,
      readPacked (mp.metaBase + mp.offTailDir) mp.ptrB mp.w mem₁ t =
        readPacked (mp.metaBase + mp.offTailDir) mp.ptrB mp.w mem₂ t :=
    fun t ht => readPacked_congr hw
      (fun a ha => heq a (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha)))))) ht
  unfold extractFallback
  rw [hs1, hs10]
  congr 1 <;> ext x <;> split_ifs with hx <;>
    [exact hso x hx; rfl; exact htd x hx; rfl]

theorem extractFallback_writeScalar_1 {mp : BpMetaLayout} {w fr val : ℕ} {s : Memory.State}
    (hv : mp.Valid w fr) (hval : val ≤ mp.nCap) :
    extractFallback mp ((Memory.spec 0).clientState s (bpWriteScalarProg ((mp.toCtx, 1), val))).mem
      = { extractFallback mp s.mem with nSide := val } := by
  have hw := hv.w_pos
  have ho32 := hv.offBktMeta_ge
  have hd1 := hv.offSlabDir_ge; have hd2 := hv.offTailDir_ge; have hd3 := hv.offSlabOwner_ge
  unfold bpWriteScalarProg; dsimp only [BpMetaLayout.toCtx]
  rw [ite_eq_left ⟨Or.inl rfl, hval⟩]
  change extractFallback mp (Function.update s.mem (mp.metaBase + 1) val) = _
  unfold extractFallback; dsimp only
  rw [Function.update_self, Function.update_of_ne (by omega)]
  congr 1 <;> ext x <;> split_ifs with hx <;> try rfl
  · exact readPacked_congr hw (N := 4 * mp.maxBlocks)
      (fun a ha => Function.update_of_ne (by omega) val s.mem) (by omega)
  · exact readPacked_congr hw (fun a ha => Function.update_of_ne (by omega) val s.mem) hx

theorem extractFallback_writeScalar_10 {mp : BpMetaLayout} {w fr val : ℕ} {s : Memory.State}
    (hv : mp.Valid w fr) (hval : val ≤ mp.nCap) :
    extractFallback mp
      ((Memory.spec 0).clientState s (bpWriteScalarProg ((mp.toCtx, 10), val))).mem =
      { extractFallback mp s.mem with fullBlocks := val } := by
  have hw := hv.w_pos
  have ho32 := hv.offBktMeta_ge
  have hd1 := hv.offSlabDir_ge; have hd2 := hv.offTailDir_ge; have hd3 := hv.offSlabOwner_ge
  unfold bpWriteScalarProg; dsimp only [BpMetaLayout.toCtx]
  rw [ite_eq_left ⟨Or.inr ⟨le_rfl, by omega⟩, hval⟩]
  change extractFallback mp (Function.update s.mem (mp.metaBase + 10) val) = _
  unfold extractFallback; dsimp only
  rw [Function.update_of_ne (by omega), Function.update_self]
  congr 1 <;> ext x <;> split_ifs with hx <;> try rfl
  · exact readPacked_congr hw (N := 4 * mp.maxBlocks)
      (fun a ha => Function.update_of_ne (by omega) val s.mem) (by omega)
  · exact readPacked_congr hw (fun a ha => Function.update_of_ne (by omega) val s.mem) hx

theorem extractFallback_writeOwnerBlk {mp : BpMetaLayout} {w fr blk val : ℕ}
    {s : Memory.State} (hv : mp.Valid w fr) (hblk : blk < mp.maxBlocks) (hval : val < 2 ^ mp.ptrB)
    (hval_nc : val ≤ mp.nCap) :
    extractFallback mp
      ((Memory.spec 0).clientState s (bpWriteSlabOwnerProg ((mp.toCtx, (blk, 1)), val))).mem =
      { extractFallback mp s.mem with
        ownerBlk := Function.update (extractFallback mp s.mem).ownerBlk blk val } := by
  have hw := hv.w_pos
  have ho32 := hv.offBktMeta_ge
  have hd1 := hv.offSlabDir_ge; have hd2 := hv.offTailDir_ge; have hd3 := hv.offSlabOwner_ge
  have hm_eq : ((Memory.spec 0).clientState s
      (bpWriteSlabOwnerProg ((mp.toCtx, (blk, 1)), val))).mem =
      writePacked (mp.metaBase + mp.offSlabOwner) mp.ptrB mp.w s.mem (4 * blk + 1) val := by
    unfold bpWriteSlabOwnerProg; dsimp only [BpMetaLayout.toCtx]
    rw [ite_eq_left ⟨hblk, by decide, hval_nc⟩]; simp only [pure_bind]
    exact congrArg Memory.State.mem (clientState_writePackedCompGenProg ..)
  rw [hm_eq]
  set m' := writePacked (mp.metaBase + mp.offSlabOwner) mp.ptrB mp.w s.mem (4 * blk + 1) val
  have hs1 : m' (mp.metaBase + 1) = s.mem (mp.metaBase + 1) :=
    writePacked_outside hw s.mem (N := 4 * mp.maxBlocks) (by omega) val (by omega)
  have hs10 : m' (mp.metaBase + 10) = s.mem (mp.metaBase + 10) :=
    writePacked_outside hw s.mem (N := 4 * mp.maxBlocks) (by omega) val (by omega)
  unfold extractFallback; dsimp only
  rw [hs1, hs10]
  congr 1
  · ext x
    by_cases hxb : x = blk
    · subst hxb; rw [Function.update_self, ite_eq_left hblk]
      exact readPacked_writePacked_self _ _ _ s.mem _ hval
    · rw [Function.update_of_ne hxb]
      split_ifs with hx
      · exact readPacked_writePacked_of_ne hw s.mem (by omega) val
      · rfl
  · ext t; split_ifs with ht
    · exact readPacked_congr hw (N := 8 * mp.M * mp.K) (fun a ha =>
        writePacked_outside hw s.mem (N := 4 * mp.maxBlocks) (by omega) val (by omega)) ht
    · rfl

theorem extractFallback_writeOwnerTail {mp : BpMetaLayout} {w fr t val : ℕ}
    {s : Memory.State} (hv : mp.Valid w fr) (ht : t < 8 * mp.M * mp.K) (hval : val < 2 ^ mp.ptrB)
    (hval_nc : val ≤ mp.nCap) :
    extractFallback mp
      ((Memory.spec 0).clientState s (bpWriteTailDirRawProg ((mp.toCtx, t), val))).mem =
      { extractFallback mp s.mem with
        ownerTail := Function.update (extractFallback mp s.mem).ownerTail t val } := by
  have hw := hv.w_pos
  have ho32 := hv.offBktMeta_ge
  have hd1 := hv.offSlabDir_ge; have hd2 := hv.offTailDir_ge; have hd3 := hv.offSlabOwner_ge
  have hm_eq : ((Memory.spec 0).clientState s
      (bpWriteTailDirRawProg ((mp.toCtx, t), val))).mem =
      writePacked (mp.metaBase + mp.offTailDir) mp.ptrB mp.w s.mem t val := by
    unfold bpWriteTailDirRawProg; dsimp only [BpMetaLayout.toCtx]
    rw [ite_eq_left ⟨ht, hval_nc⟩]
    exact congrArg Memory.State.mem (clientState_writePackedCompGenProg ..)
  rw [hm_eq]
  set m' := writePacked (mp.metaBase + mp.offTailDir) mp.ptrB mp.w s.mem t val
  have hs1 : m' (mp.metaBase + 1) = s.mem (mp.metaBase + 1) :=
    writePacked_outside hw s.mem ht val (by omega)
  have hs10 : m' (mp.metaBase + 10) = s.mem (mp.metaBase + 10) :=
    writePacked_outside hw s.mem ht val (by omega)
  unfold extractFallback; dsimp only
  rw [hs1, hs10]
  congr 1
  · ext blk; split_ifs with hblk
    · exact readPacked_congr hw (N := 4 * mp.maxBlocks)
        (fun a ha => writePacked_outside hw s.mem (N := 8 * mp.M * mp.K) ht val (by omega))
        (by omega)
    · rfl
  · ext x
    by_cases hxt : x = t
    · subst hxt; rw [Function.update_self, ite_eq_left ht]
      exact readPacked_writePacked_self _ _ _ s.mem _ hval
    · rw [Function.update_of_ne hxt]
      split_ifs with hx
      · exact readPacked_writePacked_of_ne hw s.mem (by omega) val
      · rfl

/-- Named memory layout descriptor for the `1 · OPT` `FallbackPool` (`fallbackMode = 1`) of a large
epoch `(c, U, V, w, N)`. -/
structure FallbackLayout where
  /-- Failure probability exponent `c`. -/
  c : ℕ
  /-- Key universe `U`. -/
  U : ℕ
  /-- Value universe `V`. -/
  V : ℕ
  /-- Underlying `BlockPoolLayout` (`bpL.mp = epochBpMetaLayout c w N metaBase`). -/
  bpL : BlockPoolLayout

/-- Epoch capacity `N = bpL.mp.nCap`. -/
abbrev FallbackLayout.N (fl : FallbackLayout) : ℕ :=
  fl.bpL.mp.nCap

/-- Word-address footprint modified by `FallbackPool` operations (`metaBase + 2` + `bpL.OwnsAddr`,
strictly disjoint from `[metaBase + offBktHash, metaBase + offBktMeta)` and `metaBase + 0`). -/
@[expose] def FallbackLayout.OwnsAddr (fl : FallbackLayout) (addr : ℕ) : Prop :=
  addr = fl.bpL.mp.metaBase + 2 ∨ fl.bpL.OwnsAddr addr

/-- Static frontier and parameter validity for `FallbackLayout`. -/
structure FallbackLayout.Valid (fl : FallbackLayout) (w frontier : ℕ) : Prop where
  bp_valid : fl.bpL.Valid w frontier
  mp_eq : fl.bpL.mp = epochBpMetaLayout fl.c w fl.N fl.bpL.mp.metaBase
  thresh_le : whpThreshold fl.c ≤ fl.N
  N_le_U : fl.N ≤ fl.U
  fits_U : Fits w fl.U
  V_le_pow : fl.V ≤ 2 ^ w
  qBits_le : quotBitsWhp fl.U fl.N ≤ fl.bpL.io.pgL.qBits
  vBits_eq : fl.bpL.io.pgL.vBits = valBits fl.V
  disjoint_hdr2 : ∀ addr, (addr = fl.bpL.mp.metaBase ∨ addr = fl.bpL.mp.metaBase + 2) →
    fl.bpL.io.OwnsAddr addr → False
  disjoint_seeds : ∀ addr,
    fl.bpL.mp.metaBase + offBktHash ≤ addr →
    addr < fl.bpL.mp.metaBase + offBktMeta fl.c w fl.N →
    fl.bpL.io.OwnsAddr addr → False

theorem FallbackLayout.Valid.not_owns_seeds {fl : FallbackLayout} {w fr addr : ℕ}
    (hv : fl.Valid w fr)
    (hlo : fl.bpL.mp.metaBase + offBktHash ≤ addr)
    (hhi : addr < fl.bpL.mp.metaBase + offBktMeta fl.c w fl.N) :
    ¬fl.OwnsAddr addr := by
  rintro (rfl | hma | hia)
  · unfold offBktHash at hlo; omega
  · have hbds := BpMetaLayout.OwnsMetaAddr.bounds hv.bp_valid.mp_valid hma
    have hobm : fl.bpL.mp.offBktMeta = offBktMeta fl.c w fl.N := by rw [hv.mp_eq]; rfl
    rcases hbds with (rfl | h10) | htab
    · unfold offBktHash at hlo; omega
    · unfold offBktHash at hlo; omega
    · rw [hobm] at htab; omega
  · exact hv.disjoint_seeds addr hlo hhi hia

/-- Construct `FeistelHashCtx` for `fl : FallbackLayout`. -/
@[expose] def FallbackLayout.feistelCtx (fl : FallbackLayout) : FeistelHashCtx :=
  let mb := fl.bpL.mp.metaBase
  let w := fl.bpL.mp.w
  let offBot_v := BitPackedDoubleTabulation.offBot w (cTabWhp fl.c) (dTabWhp fl.c) (bCharWhp fl.N)
  (((mb + offBktHash, offBot_v), (w, redWidthWhp fl.U)),
    ((redBitsWhp fl.c fl.N, cTabWhp fl.c), (dTabWhp fl.c, (bCharWhp fl.N, bWhp fl.N))))

/-- Dynamic state invariant of `FallbackPool` (`fallbackMode = 1`). -/
structure FallbackLayout.StateInv (fl : FallbackLayout) (slack : ℕ)
    (θ_bkt : BktSeed fl.c fl.U fl.N) (mem : ℕ → ℕ)
    (s_abs : Fin fl.U → Option (Fin fl.V)) : Prop where
  hdr_N : mem fl.bpL.mp.metaBase = fl.N
  mode_eq : mem (fl.bpL.mp.metaBase + 2) = 1
  seed_bkt : BitPackedDoubleTabulation.SeedRep (fl.bpL.mp.metaBase + offBktHash) fl.bpL.mp.w
    (redWidthWhp fl.U) (cTabWhp fl.c) (dTabWhp fl.c) (bCharWhp fl.N) (bWhp fl.N) θ_bkt mem
  fb_valid : (extractFallback fl.bpL.mp mem).Valid
  nSide_le : (extractFallback fl.bpL.mp mem).nSide ≤ fl.N
  io_inv : fl.bpL.io.StateInv (extractFallback fl.bpL.mp mem).nSide slack mem
  refines : PoolItemsRefines fl.U fl.V (bWhp fl.N) (bktHash fl.c fl.U fl.N θ_bkt)
    (extractFallback fl.bpL.mp mem).nSide (extractFallback fl.bpL.mp mem).owner
    (slotIoPairAt fl.bpL.io mem) s_abs

theorem FallbackLayout.StateInv.mono_slack {fl : FallbackLayout} {s₁ s₂ : ℕ}
    {θ_bkt : BktSeed fl.c fl.U fl.N} {mem : ℕ → ℕ} {s_abs : Fin fl.U → Option (Fin fl.V)}
    (h : fl.StateInv s₁ θ_bkt mem s_abs) (hle : s₁ ≤ s₂) (hs₂ : s₂ ≤ 24) :
    fl.StateInv s₂ θ_bkt mem s_abs :=
  { h with io_inv := h.io_inv.mono_slack hle hs₂ }

theorem FallbackLayout.congr_of_outside {fl : FallbackLayout} {w fr slack : ℕ}
    {θ_bkt : BktSeed fl.c fl.U fl.N} {mem₁ mem₂ : ℕ → ℕ}
    {s_abs : Fin fl.U → Option (Fin fl.V)}
    (hv : fl.Valid w fr) (hinv : fl.StateInv slack θ_bkt mem₁ s_abs)
    (hN_eq : mem₂ fl.bpL.mp.metaBase = mem₁ fl.bpL.mp.metaBase)
    (hseed : ∀ addr, fl.bpL.mp.metaBase + offBktHash ≤ addr →
      addr < fl.bpL.mp.metaBase + offFpHash fl.c w fl.N → mem₂ addr = mem₁ addr)
    (hout : ∀ addr, fl.OwnsAddr addr → mem₂ addr = mem₁ addr) :
    fl.StateInv slack θ_bkt mem₂ s_abs := by
  have hw := hv.bp_valid.mp_valid.w_pos
  have hw_eq : fl.bpL.mp.w = w := hv.bp_valid.mp_valid.w_eq.symm
  have hex : extractFallback fl.bpL.mp mem₂ = extractFallback fl.bpL.mp mem₁ :=
    extractFallback_congr hw (fun a ha => (hout a (Or.inr (Or.inl ha))).symm) |>.symm
  obtain ⟨hio₂, harr₂⟩ := fl.bpL.io.congr_of_outside hv.bp_valid.io_valid.w_pos hinv.io_inv
    (fun a ha => hout a (Or.inr (Or.inr ha)))
  refine
    { hdr_N := hN_eq.trans hinv.hdr_N
      mode_eq := (hout _ (Or.inl rfl)).trans hinv.mode_eq
      seed_bkt := hinv.seed_bkt.congr_on hw fun a h1 h2 => by
        rw [hw_eq] at h2
        exact hseed a h1 (by unfold offFpHash; omega)
      fb_valid := hex ▸ hinv.fb_valid
      nSide_le := hex ▸ hinv.nSide_le
      io_inv := hex ▸ hio₂
      refines := hex ▸ hinv.refines.congr (fun _ _ => rfl) harr₂ }

theorem feistelPre_of_fallbackValid {fl : FallbackLayout} {w : ℕ} {s : Memory.State}
    {θ_bkt : BktSeed fl.c fl.U fl.N}
    (hv : fl.Valid w s.frontier)
    (hseed : BitPackedDoubleTabulation.SeedRep (fl.bpL.mp.metaBase + offBktHash) fl.bpL.mp.w
      (redWidthWhp fl.U) (cTabWhp fl.c) (dTabWhp fl.c) (bCharWhp fl.N) (bWhp fl.N) θ_bkt s.mem) :
    (∀ u_val < fl.U, FeistelSplitPre w (fl.feistelCtx, u_val) s) ∧
    (∀ bkt q_val, q_val < 2 ^ quotBitsWhp fl.U fl.N →
      FeistelReconPre w (fl.feistelCtx, (bkt, q_val)) s) := by
  obtain ⟨_, _, _, hbc_w, hbw_w, _, _, _, _, htop_N, hbot_N, _, _, _, _, _, _, _, _, _⟩ :=
    largeEpoch_param_bounds hv.thresh_le hv.N_le_U hv.fits_U
  have hw : 0 < w := hv.bp_valid.mp_valid.w_mach_pos
  have hw_eq : w = fl.bpL.mp.w := hv.bp_valid.mp_valid.w_eq
  have hN_w : fl.N < 2 ^ w := lt_of_le_of_lt hv.N_le_U hv.fits_U
  have hw₀_pos := redWidthWhp_pos fl.U
  have hw₀_le := redWidthWhp_le_of_le_pow hw hv.fits_U.le
  have hα_lt : s.mem (fl.bpL.mp.metaBase + offBktHash) < 2 ^ (redWidthWhp fl.U - 1) := by
    rw [hseed.1]; exact θ_bkt.1.isLt
  have hbc_pos : 0 < bCharWhp fl.N := by
    have h1 := Dynamic.one_le_logLogFactor fl.N
    have h2 := (Nat.mul_le_mul_right _ (le_codeExpWhp fl.c)).trans
      (codeExpWhp_mul_ell_le_bCharWhp hv.thresh_le)
    nlinarith [le_codeExpWhp fl.c]
  have hd_pos : 0 < dTabWhp fl.c := by
    have := le_qTabWhp fl.c; have := le_cTabWhp fl.c; unfold dTabWhp; positivity
  have hd_lt : dTabWhp fl.c < 2 ^ w := by
    have h2 : 1 < 2 ^ bCharWhp fl.N := Nat.one_lt_two_pow hbc_pos.ne'
    exact (lt_mul_of_one_lt_right hd_pos h2).trans (lt_of_le_of_lt hbot_N hN_w)
  have hc1_lt : cTabWhp fl.c + 1 < 2 ^ w := by
    have hd_ge : 1 ≤ dTabWhp fl.c * 2 ^ bCharWhp fl.N :=
      Nat.mul_pos hd_pos (Nat.two_pow_pos _)
    have : cTabWhp fl.c + 1 ≤
        BitPackedDoubleTabulation.topEntries (cTabWhp fl.c) (dTabWhp fl.c) (bCharWhp fl.N) := by
      unfold BitPackedDoubleTabulation.topEntries
      rw [Nat.mul_assoc]; exact Nat.le_mul_of_pos_right _ hd_ge
    exact lt_of_le_of_lt (this.trans htop_N) hN_w
  have hsp_fr : fl.bpL.mp.metaBase + offBktHash +
      BitPackedDoubleTabulation.space w (cTabWhp fl.c) (dTabWhp fl.c) (bCharWhp fl.N)
        (bWhp fl.N) ≤ s.frontier := by
    have hobm : fl.bpL.mp.offBktMeta = offBktMeta fl.c fl.bpL.mp.w fl.N := by
      rw [← hw_eq, hv.mp_eq]; rfl
    have hfr := hv.bp_valid.mp_valid.frontier_ge
    have hd1 := hv.bp_valid.mp_valid.offSlabDir_ge
    have hd2 := hv.bp_valid.mp_valid.offTailDir_ge
    have hd3 := hv.bp_valid.mp_valid.offSlabOwner_ge
    have hd4 := hv.bp_valid.mp_valid.offTailOwner_ge
    have hob : offBktHash + BitPackedDoubleTabulation.space fl.bpL.mp.w (cTabWhp fl.c)
        (dTabWhp fl.c) (bCharWhp fl.N) (bWhp fl.N) ≤ offBktMeta fl.c fl.bpL.mp.w fl.N := by
      unfold offBktMeta offFpHash; omega
    rw [hw_eq]; omega
  have heval_pre : ∀ x_in < 2 ^ redWidthWhp fl.U,
      EvalSaltedBoundedPre w
        (((((fl.bpL.mp.metaBase + offBktHash,
            BitPackedDoubleTabulation.offBot fl.bpL.mp.w (cTabWhp fl.c) (dTabWhp fl.c)
              (bCharWhp fl.N)),
           (fl.bpL.mp.w, redWidthWhp fl.U)),
          ((redBitsWhp fl.c fl.N, cTabWhp fl.c),
           (dTabWhp fl.c, (bCharWhp fl.N, bWhp fl.N))))),
         (0, x_in)) s := fun x_in hx => by
    rw [← hw_eq]
    exact ⟨hw, rfl, hw₀_pos, hw₀_le, hbc_w, hbw_w.le, rfl, hα_lt, Nat.two_pow_pos (bCharWhp fl.N),
      hx, hd_lt, hc1_lt, lt_of_le_of_lt htop_N hN_w, lt_of_le_of_lt hbot_N hN_w, hsp_fr⟩
  refine ⟨fun u_val hu => ?_, fun bkt q_val hq => ?_⟩
  · have hu_w₀ : u_val < 2 ^ redWidthWhp fl.U := hu.trans_le (le_two_pow_redWidthWhp fl.U)
    have hsh : u_val >>> bWhp fl.N < 2 ^ redWidthWhp fl.U := by
      rw [Nat.shiftRight_eq_div_pow]
      exact (Nat.div_le_self _ _).trans_lt hu_w₀
    exact ⟨hbw_w, hu_w₀, heval_pre _ hsh⟩
  · have hqb_add : quotBitsWhp fl.U fl.N + bWhp fl.N ≤ w := by
      have hle : bWhp fl.N ≤ keyBits fl.U := by
        unfold bWhp keyBits
        exact (Nat.sub_le _ _).trans
          ((Nat.log_mono_right hv.N_le_U).trans (Nat.log_le_clog 2 fl.U))
      unfold quotBitsWhp
      rw [Nat.sub_add_cancel hle]
      exact Nat.clog_le_of_le_pow hv.fits_U.le
    exact ⟨quotBitsWhp fl.U fl.N, hbw_w, hqb_add, hq,
      heval_pre q_val (hq.trans_le (two_pow_quotBitsWhp_le_redWidthWhp fl.U fl.N))⟩

/-! ### `FallbackPool` Lookup, Promotion, Demotion, and `enterFallbackProg` -/

/-- Read `fb.owner p` in `O(1)` time (`¬ReadsWidth`). -/
def fbOwnerOfProg : BpMetaCtx × ℕ → Memory.Prog ℕ
  | (mctx, p) => do
    let mk ← bpGetMKFromCtxProg mctx
    let caps ← bpGetNcapFromCtxProg mctx
    let fb ← bpReadScalarProg (mctx, 10)
    let dm ← bpDivModKProg (mctx, p)
    if dm.1 < fb then
      bpReadSlabOwnerProg (mctx, (dm.1, 1))
    else if fb ≤ caps / mk.2 then
      if p ≥ fb * mk.2 then do
        let t ← pure (p - fb * mk.2)
        bpReadTailDirRawProg (mctx, t)
      else
        pure 0
    else
      pure 0
where
  bpGetMKFromCtxProg : BpMetaCtx → Memory.Prog (ℕ × ℕ)
    | (_, (((m, k), _), _)) => pure (m, k)
  bpGetNcapFromCtxProg : BpMetaCtx → Memory.Prog ℕ
    | (_, (_, (_, nc))) => pure nc

theorem state_fbOwnerOfProg (x : BpMetaCtx × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (fbOwnerOfProg x) = s := by
  rcases x with ⟨⟨_, ⟨⟨⟨_, _⟩, _⟩, ⟨_, _⟩⟩⟩, _⟩
  unfold fbOwnerOfProg fbOwnerOfProg.bpGetMKFromCtxProg fbOwnerOfProg.bpGetNcapFromCtxProg
  dsimp only
  simp only [pure_bind]
  rw [StateTransitionSpec.clientState_bind, clientState_bpReadScalarProg,
    StateTransitionSpec.clientState_bind, clientState_bpDivModKProg]
  split_ifs
  · exact clientState_bpReadSlabOwnerProg _ s
  · exact clientState_bpReadTailDirRawProg _ s
  · rfl
  · rfl

theorem realizesBounded_fbOwnerOf :
    RealizesBounded .exact fbOwnerOfProg
      (WordEncoding.encode (α := BpMetaCtx × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w (mctx, _) s => (BpMetaLayout.ofCtx mctx).Valid w s.frontier) (fun _ _ => 0) := by
  have hrs := realizesBounded_bpReadScalar
  have hdm := realizesBounded_bpDivModK
  have hrso := realizesBounded_bpReadSlabOwner
  have hrtd := realizesBounded_bpReadTailDirRaw
  have hmk : RealizesBounded .exact fbOwnerOfProg.bpGetMKFromCtxProg
      (WordEncoding.encode (α := BpMetaCtx)) (WordEncoding.encode (α := ℕ × ℕ))
      (fun _ _ _ => True) (fun _ _ => 0) := by realize
  have hnc : RealizesBounded .exact fbOwnerOfProg.bpGetNcapFromCtxProg
      (WordEncoding.encode (α := BpMetaCtx)) (WordEncoding.encode (α := ℕ))
      (fun _ _ _ => True) (fun _ _ => 0) := by realize
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨mb, obm⟩, ⟨osd, otd⟩⟩, ⟨⟨oso, oto⟩, ⟨pb, wv⟩⟩⟩,
      ⟨⟨⟨m, k⟩, ⟨ms, mbk⟩⟩, ⟨mt, nc⟩⟩⟩, p⟩
    have hv0 := h
    have hnc_w := hv0.nCap_lt_two_pow_w
    have hw := hv0.w_mach_pos
    have hw1 : 1 < 2 ^ w := Nat.one_lt_two_pow hw.ne'
    have hp_w : p < 2 ^ w := hwords 14
    have hpk_le : p / k ≤ p := Nat.div_le_self p k
    have hnck_le : nc / k ≤ nc := Nat.div_le_self nc k
    have hK_ge : 64 ≤ k := hv0.K_ge
    have h12K_le : 12 * k ≤ nc := hv0.twelve_K_le
    dsimp only [BpMetaLayout.ofCtx] at hnc_w hK_ge h12K_le
    have h10_w : 10 < 2 ^ w := by omega
    have hdm_r : ((Memory.spec 0).runClient s
        (bpDivModKProg (((((mb, obm), (osd, otd)), ((oso, oto), (pb, wv))),
          (((m, k), (ms, mbk)), (mt, nc))), p))).1 = (p / k, p % k) := rfl
    dsimp only at *
    dsimp only [BpMetaLayout.ofCtx, fbOwnerOfProg.bpGetMKFromCtxProg,
      fbOwnerOfProg.bpGetNcapFromCtxProg, Fits, StateTransitionSpec.clientState,
      StateTransitionSpec.clientResult] at *
    try simp only [prog_runClient_state_pure, prog_clientResult_pure,
      runClient_state_bpReadScalarProg, runClient_state_bpDivModKProg, hdm_r] at *
    set fb_v := ((Memory.spec 0).runClient s
      (bpReadScalarProg (((((mb, obm), (osd, otd)), ((oso, oto), (pb, wv))),
        (((m, k), (ms, mbk)), (mt, nc))), 10))).1
    first | trivial | omega | (
      have hfb_mul : fb_v * k ≤ nc := (Nat.le_div_iff_mul_le (by omega)).mp (by omega)
      omega))

theorem fbOwnerOfProg_spec {mp : BpMetaLayout} {w fr maxT p : ℕ} {s : Memory.State}
    (hv : mp.Valid w fr) (hfb : (extractFallback mp s.mem).ValidWith maxT)
    (hmaxT : maxT < 8 * mp.M * mp.K)
    (hns_le : (extractFallback mp s.mem).nSide ≤ mp.nCap)
    (hp : p < (extractFallback mp s.mem).nSide) :
    (Memory.spec 0).clientResult s (fbOwnerOfProg (mp.toCtx, p)) =
      (extractFallback mp s.mem).owner p := by
  set fb := extractFallback mp s.mem
  have hK : 0 < mp.K := by have := hv.K_ge; omega
  have hfb_div : fb.fullBlocks ≤ mp.nCap / mp.K :=
    (Nat.le_div_iff_mul_le hK).mpr (hfb.blocks_le.trans hns_le)
  have hfb_mb : fb.fullBlocks < mp.maxBlocks := by
    have := hv.div_K_add_two_le; omega
  unfold fbOwnerOfProg FallbackState.owner
  rw [prog_clientResult_bind]
  have hmk_r : (Memory.spec 0).clientResult s (fbOwnerOfProg.bpGetMKFromCtxProg mp.toCtx) =
      (mp.M, mp.K) := rfl
  have hmk_s : (Memory.spec 0).clientState s (fbOwnerOfProg.bpGetMKFromCtxProg mp.toCtx) = s := rfl
  have hnc_r : (Memory.spec 0).clientResult s (fbOwnerOfProg.bpGetNcapFromCtxProg mp.toCtx) =
      mp.nCap := rfl
  have hnc_s : (Memory.spec 0).clientState s (fbOwnerOfProg.bpGetNcapFromCtxProg mp.toCtx) = s :=
    rfl
  rw [hmk_s, hmk_r, prog_clientResult_bind, hnc_s, hnc_r, prog_clientResult_bind,
    clientState_bpReadScalarProg, clientResult_bpReadScalar s (Or.inr ⟨le_rfl, by omega⟩),
    prog_clientResult_bind, clientState_bpDivModKProg, clientResult_bpDivModK]
  dsimp only
  have hfb_K : fb.K = mp.K := rfl
  rw [hfb_K]
  change (Memory.spec 0).clientResult s
    (if p / mp.K < fb.fullBlocks then _
     else if fb.fullBlocks ≤ mp.nCap / mp.K then if p ≥ fb.fullBlocks * mp.K then _ else _
     else _) = _
  have hlt_iff : p / mp.K < fb.fullBlocks ↔ p < fb.fullBlocks * mp.K :=
    Nat.div_lt_iff_lt_mul hK
  by_cases hlt : p < fb.fullBlocks * mp.K
  · rw [ite_eq_left (hlt_iff.mpr hlt), ite_eq_left hlt]
    have hdm_mb : p / mp.K < mp.maxBlocks := (hlt_iff.mpr hlt).trans hfb_mb
    unfold bpReadSlabOwnerProg; dsimp only [BpMetaLayout.toCtx, fb, extractFallback]
    rw [ite_eq_left ⟨hdm_mb, by decide⟩, ite_eq_left hdm_mb]
    simp [pure_bind, clientResult_readPackedCompGenProg]
  · have hnlt : ¬(p / mp.K < fb.fullBlocks) := fun h => hlt (hlt_iff.mp h)
    have hge : p ≥ fb.fullBlocks * mp.K := Nat.le_of_not_lt hlt
    rw [ite_eq_right hnlt, ite_eq_right hlt, ite_eq_left hfb_div, ite_eq_left hge]
    have ht_lt : p - fb.fullBlocks * mp.K < 8 * mp.M * mp.K := by
      have : p - fb.fullBlocks * mp.K < fb.tailLen := by
        unfold FallbackState.tailLen; rw [hfb_K]; omega
      exact this.trans (lt_of_le_of_lt hfb.tail_le hmaxT)
    simp only [pure_bind]
    unfold bpReadTailDirRawProg; dsimp only [BpMetaLayout.toCtx, fb, extractFallback] at ht_lt ⊢
    rw [ite_eq_left ht_lt, ite_eq_left ht_lt, clientResult_readPackedCompGenProg]

/-- Linear scan over `[0, nSide)` in `FallbackPool` for `(bkt, q_u)`, returning
`(foundFlag, (hitP, hitVal))`. -/
def fbScanStepProg :
    ((BpMetaCtx × SlotIoCtx) × (ℕ × (ℕ × ℕ))) × ((ℕ × ℕ) × (ℕ × ℕ)) →
      Memory.Prog ((ℕ × ℕ) × (ℕ × ℕ))
  | (((mctx, ioctx), (nSide, (bkt, q_u))), ((cur, found), (hitP, hitVal))) =>
    if cur < nSide then do
      let b_cur ← fbOwnerOfProg (mctx, cur)
      let qv ← slotIoReadRawProg (ioctx, cur)
      if found = 0 ∧ b_cur = bkt ∧ qv.1 = q_u then
        pure ((cur + 1, 1), (cur, qv.2))
      else
        pure ((cur + 1, found), (hitP, hitVal))
    else do
      let _ ← bpReadScalarProg (mctx, 1)
      pure ((cur, found), (hitP, hitVal))

theorem memoryCost_fbScanStepProg_pos
    (x : ((BpMetaCtx × SlotIoCtx) × (ℕ × (ℕ × ℕ))) × ((ℕ × ℕ) × (ℕ × ℕ))) (s : Memory.State) :
    1 ≤ memoryCost (fbScanStepProg x) s := by
  rcases x with ⟨⟨⟨mctx, _⟩, ⟨_, ⟨_, _⟩⟩⟩, ⟨⟨cur, _⟩, ⟨_, _⟩⟩⟩
  unfold fbScanStepProg; dsimp only
  split_ifs
  · unfold fbOwnerOfProg
    rcases mctx with ⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨_, _⟩⟩⟩
    dsimp only [fbOwnerOfProg.bpGetMKFromCtxProg, fbOwnerOfProg.bpGetNcapFromCtxProg]
    simp only [Realization.memoryCost_bind', memoryCost_pure, bpReadScalarProg]
    split_ifs <;> simp <;> omega
  · rcases mctx with ⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨_, _⟩⟩⟩
    simp [bpReadScalarProg]

/-- Per-step safety invariant for `fbScanStepProg`. -/
def FbScanStepPre (w : ℕ) :
    ((BpMetaCtx × SlotIoCtx) × (ℕ × (ℕ × ℕ))) × ((ℕ × ℕ) × (ℕ × ℕ)) → Memory.State → Prop
  | (((mctx, ioctx), (nSide, _)), ((cur, _), _)), s =>
    cur ≤ nSide ∧ nSide ≤ (BpMetaLayout.ofCtx mctx).nCap ∧
    (BpMetaLayout.ofCtx mctx).Valid w s.frontier ∧
    (SlotIoLayout.ofCtx ioctx).Valid w s.frontier

theorem state_fbScanStepProg
    (x : ((BpMetaCtx × SlotIoCtx) × (ℕ × (ℕ × ℕ))) × ((ℕ × ℕ) × (ℕ × ℕ))) (s : Memory.State) :
    (Memory.spec 0).clientState s (fbScanStepProg x) = s := by
  rcases x with ⟨⟨⟨mctx, ioctx⟩, ⟨nSide, ⟨bkt, q_u⟩⟩⟩, ⟨⟨cur, found⟩, ⟨hitP, hitVal⟩⟩⟩
  have hsr : ∀ idx, (Memory.spec 0).clientState s (slotIoReadRawProg (ioctx, idx)) = s :=
    fun idx => clientState_slotIoReadRawProg (ioctx, idx) s
  unfold fbScanStepProg; dsimp only
  split_ifs
  · rw [StateTransitionSpec.clientState_bind, state_fbOwnerOfProg,
      StateTransitionSpec.clientState_bind, hsr cur]
    split_ifs <;> rfl
  · rw [StateTransitionSpec.clientState_bind, clientState_bpReadScalarProg]; rfl

theorem realizesBounded_fbScanStep :
    RealizesBounded .exact fbScanStepProg
      (WordEncoding.encode (α :=
        ((BpMetaCtx × SlotIoCtx) × (ℕ × (ℕ × ℕ))) × ((ℕ × ℕ) × (ℕ × ℕ))))
      (WordEncoding.encode (α := (ℕ × ℕ) × (ℕ × ℕ)))
      FbScanStepPre (fun _ _ => 0) := by
  have hfo := realizesBounded_fbOwnerOf
  have hsr := realizesBounded_slotIoReadRaw
  have hrs := realizesBounded_bpReadScalar
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨⟨⟨mb, obm⟩, ⟨osd, otd⟩⟩, ⟨⟨oso, oto⟩, ⟨pb, wv⟩⟩⟩,
      ⟨⟨⟨m, k⟩, ⟨ms, mbk⟩⟩, ⟨mt, nc⟩⟩⟩, ioctx⟩, ⟨nSide, ⟨bkt, q_u⟩⟩⟩,
      ⟨⟨cur, found⟩, ⟨hitP, hitVal⟩⟩⟩
    obtain ⟨hcur, hn, hmv, hiov⟩ := h
    have hnc_w := hmv.nCap_lt_two_pow_w
    have hw := hmv.w_mach_pos
    have hw1 : 1 < 2 ^ w := Nat.one_lt_two_pow hw.ne'
    have hwf : found < 2 ^ w := hwords 31
    have hwp : hitP < 2 ^ w := hwords 32
    have hwv_i : hitVal < 2 ^ w := hwords 33
    dsimp only [BpMetaLayout.ofCtx] at hn hnc_w
    have hfo_s : ((Memory.spec 0).runClient s
        (fbOwnerOfProg
          (((((mb, obm), (osd, otd)), ((oso, oto), (pb, wv))),
            (((m, k), (ms, mbk)), (mt, nc))), cur))).2.1 = s :=
      state_fbOwnerOfProg
        (((((mb, obm), (osd, otd)), ((oso, oto), (pb, wv))),
          (((m, k), (ms, mbk)), (mt, nc))), cur) s
    try dsimp only [Fits, StateTransitionSpec.clientState] at *
    try simp only [hfo_s]
    try (rw [hfo_s] at *)
    first | exact hmv | exact hiov | exact hw1 | omega)

/-- Bounded iteration loop executing `fbScanStepProg` across `nSide` slots. -/
def fbScanLoopProg :
    (((BpMetaCtx × SlotIoCtx) × (ℕ × (ℕ × ℕ))) × ((ℕ × ℕ) × (ℕ × ℕ))) × ℕ →
      Memory.Prog ((ℕ × ℕ) × (ℕ × ℕ))
  | ((d, acc), fuel) => iterate fbScanStepProg d fuel acc

theorem realizesBounded_fbScanLoop :
    RealizesBounded .exact fbScanLoopProg
      (WordEncoding.encode (α :=
        (((BpMetaCtx × SlotIoCtx) × (ℕ × (ℕ × ℕ))) × ((ℕ × ℕ) × (ℕ × ℕ))) × ℕ))
      (WordEncoding.encode (α := (ℕ × ℕ) × (ℕ × ℕ)))
      (fun w ((d, acc), fuel) s => iterationSafe fbScanStepProg FbScanStepPre w d fuel acc s)
      (fun _ _ => 0) :=
  RealizesBounded.iterate₀
    (WordEncoding.encode (α := (BpMetaCtx × SlotIoCtx) × (ℕ × (ℕ × ℕ))))
    (WordEncoding.encode (α := (ℕ × ℕ) × (ℕ × ℕ)))
    realizesBounded_fbScanStep
    memoryCost_fbScanStepProg_pos

private abbrev fbScanLoopFound (r : (ℕ × ℕ) × (ℕ × ℕ)) : ℕ := r.1.2

/-- Fallback linear scan over `nSide` slots matching `(bkt, q_u)` (`¬ReadsWidth`). -/
def fbScanProg : (BpMetaCtx × SlotIoCtx) × (ℕ × ℕ) → Memory.Prog (ℕ × (ℕ × ℕ))
  | ((mctx, ioctx), (bkt, q_u)) => do
    let nSide ← bpReadScalarProg (mctx, 1)
    let (_, (_, (_, nCap))) := mctx
    if nSide ≤ nCap then do
      let z0 ← pure 0
      let r ← fbScanLoopProg ((((mctx, ioctx), (nSide, (bkt, q_u))), ((z0, z0), (z0, z0))), nSide)
      pure (fbScanLoopFound r, r.2)
    else
      pure (0, (0, 0))

theorem fbScanLoop_safe_and_state {mp : BpMetaLayout} {io : SlotIoLayout}
    {w nSide bkt q_u : ℕ} {s : Memory.State}
    (hn : nSide ≤ mp.nCap) (hmv : mp.Valid w s.frontier) (hiov : io.Valid w s.frontier) :
    ∀ fuel cur found hP hV,
      cur + fuel ≤ nSide →
      iterationSafe fbScanStepProg FbScanStepPre w
        ((mp.toCtx, io.toCtx), (nSide, (bkt, q_u))) fuel ((cur, found), (hP, hV)) s ∧
      (Memory.spec 0).clientState s
        (iterate fbScanStepProg ((mp.toCtx, io.toCtx), (nSide, (bkt, q_u))) fuel
          ((cur, found), (hP, hV))) = s := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ _; exact ⟨trivial, rfl⟩
  | succ k ih =>
    intro cur found hP hV hle
    have hpre : FbScanStepPre w
        (((mp.toCtx, io.toCtx), (nSide, (bkt, q_u))), ((cur, found), (hP, hV))) s := by
      dsimp only [FbScanStepPre]
      rw [BpMetaLayout.ofCtx_toCtx, SlotIoLayout.ofCtx_toCtx]
      exact ⟨by omega, hn, hmv, hiov⟩
    have hst1 := state_fbScanStepProg
      (((mp.toCtx, io.toCtx), (nSide, (bkt, q_u))), ((cur, found), (hP, hV))) s
    have hlt : cur < nSide := by omega
    have hres_cur : ((Memory.spec 0).clientResult s
        (fbScanStepProg
          (((mp.toCtx, io.toCtx), (nSide, (bkt, q_u))), ((cur, found), (hP, hV))))).1.1 =
        cur + 1 := by
      unfold fbScanStepProg; dsimp only; rw [ite_eq_left hlt]
      rw [prog_clientResult_bind, state_fbOwnerOfProg, prog_clientResult_bind]
      have hsr : (Memory.spec 0).clientState s (slotIoReadRawProg (io.toCtx, cur)) = s :=
        clientState_slotIoReadRawProg _ s
      rw [hsr]; split_ifs <;> rfl
    set nxt := (Memory.spec 0).clientResult s
      (fbScanStepProg (((mp.toCtx, io.toCtx), (nSide, (bkt, q_u))), ((cur, found), (hP, hV))))
    rcases nxt_eq : nxt with ⟨⟨c1, f1⟩, ⟨p1, v1⟩⟩
    have hc1 : c1 = cur + 1 := by
      have : nxt.1.1 = cur + 1 := hres_cur; rw [nxt_eq] at this; exact this
    obtain ⟨hs_k, hst_k⟩ := ih c1 f1 p1 v1 (by omega)
    refine ⟨?_, ?_⟩
    · unfold iterationSafe; rw [hst1]; change _ ∧ iterationSafe _ _ _ _ k nxt s
      rw [nxt_eq]; exact ⟨hpre, hs_k⟩
    · unfold iterate; rw [StateTransitionSpec.clientState_bind, hst1]
      change (Memory.spec 0).clientState s (iterate _ _ k nxt) = s
      rw [nxt_eq]; exact hst_k

theorem state_fbScanProg (x : (BpMetaCtx × SlotIoCtx) × (ℕ × ℕ)) (s : Memory.State) :
    (Memory.spec 0).clientState s (fbScanProg x) = s := by
  rcases x with ⟨⟨⟨p1, ⟨p2, ⟨mt, nCap⟩⟩⟩, ioctx⟩, ⟨bkt, q_u⟩⟩
  unfold fbScanProg fbScanLoopProg
  rw [StateTransitionSpec.clientState_bind, clientState_bpReadScalarProg]
  dsimp only
  split_ifs with hle
  · simp only [pure_bind]; rw [StateTransitionSpec.clientState_bind]
    have hex : ∀ nv k c f p v,
        (Memory.spec 0).clientState s
          (iterate fbScanStepProg
            (((p1, (p2, (mt, nCap))), ioctx), (nv, (bkt, q_u))) k ((c, f), (p, v))) = s := by
      intro nv k; induction k with
      | zero => intros; rfl
      | succ k ih =>
        intro c f p v; unfold iterate
        rw [StateTransitionSpec.clientState_bind, state_fbScanStepProg]
        rcases (Memory.spec 0).clientResult s _ with ⟨⟨_, _⟩, ⟨_, _⟩⟩
        exact ih ..
    rw [hex _ _ 0 0 0 0]; rfl
  · rfl

theorem realizesBounded_fbScan :
    RealizesBounded .exact fbScanProg
      (WordEncoding.encode (α := (BpMetaCtx × SlotIoCtx) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      (fun w ((mctx, ioctx), _) s =>
        (BpMetaLayout.ofCtx mctx).Valid w s.frontier ∧
        (SlotIoLayout.ofCtx ioctx).Valid w s.frontier)
      (fun _ _ => 0) := by
  have hrs := realizesBounded_bpReadScalar
  have hsl := realizesBounded_fbScanLoop
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨⟨mb, obm⟩, ⟨osd, otd⟩⟩, ⟨⟨oso, oto⟩, ⟨pb, wv⟩⟩⟩,
      ⟨⟨⟨m, k⟩, ⟨ms, mbk⟩⟩, ⟨mt, nc⟩⟩⟩, ioctx⟩, ⟨bkt, q_u⟩⟩
    obtain ⟨hmv, hiov⟩ := h
    have hw := hmv.w_mach_pos
    have hw1 : 1 < 2 ^ w := Nat.one_lt_two_pow hw.ne'
    try dsimp only [Fits, StateTransitionSpec.clientState] at *
    try simp only [runClient_state_bpReadScalarProg] at *
    first | exact hmv | exact hw1 | omega | (
      set mctx : BpMetaCtx := ((((mb, obm), (osd, otd)), ((oso, oto), (pb, wv))),
        (((m, k), (ms, mbk)), (mt, nc)))
      set ns_v := (Memory.spec 0).clientResult s (bpReadScalarProg (mctx, 1))
      have hm_eq := BpMetaLayout.toCtx_ofCtx mctx
      have hio_eq := SlotIoLayout.toCtx_ofCtx ioctx
      have hns_nc : ns_v ≤ (BpMetaLayout.ofCtx mctx).nCap := by
        dsimp only [BpMetaLayout.ofCtx, mctx]; omega
      obtain ⟨hsafe, _⟩ := fbScanLoop_safe_and_state (mp := BpMetaLayout.ofCtx mctx)
        (io := SlotIoLayout.ofCtx ioctx) (nSide := ns_v) (bkt := bkt) (q_u := q_u)
        hns_nc hmv hiov ns_v 0 0 0 0 (by omega)
      rwa [hm_eq, hio_eq] at hsafe))

theorem fbScanProg_spec {fl : FallbackLayout} {w slack : ℕ}
    {θ_bkt : BktSeed fl.c fl.U fl.N} {s_abs : Fin fl.U → Option (Fin fl.V)} {s : Memory.State}
    (hv : fl.Valid w s.frontier) (hinv : fl.StateInv slack θ_bkt s.mem s_abs) (u : Fin fl.U) :
    let bkt := epochBucket fl.c fl.U fl.N θ_bkt u
    let q_u := keyQuotient (bWhp fl.N) u.val
    let res := (Memory.spec 0).clientResult s
      (fbScanProg ((fl.bpL.mp.toCtx, fl.bpL.io.toCtx), (bkt, q_u)))
    (Memory.spec 0).clientState s
      (fbScanProg ((fl.bpL.mp.toCtx, fl.bpL.io.toCtx), (bkt, q_u))) = s ∧
    (match s_abs u with
     | none => res = (0, (0, 0))
     | some v =>
       res.1 = 1 ∧ scanResSlot res < (extractFallback fl.bpL.mp s.mem).nSide ∧
       scanResVal res = v.val ∧
       (extractFallback fl.bpL.mp s.mem).owner (scanResSlot res) = bkt ∧
       slotIoPairAt fl.bpL.io s.mem (scanResSlot res) = (q_u, v.val)) := by
  dsimp only
  set bkt := epochBucket fl.c fl.U fl.N θ_bkt u
  set q_u := keyQuotient (bWhp fl.N) u.val
  set fb := extractFallback fl.bpL.mp s.mem
  have hst := state_fbScanProg ((fl.bpL.mp.toCtx, fl.bpL.io.toCtx), (bkt, q_u)) s
  have h6lt8 : 6 * fl.bpL.mp.M * fl.bpL.mp.K < 8 * fl.bpL.mp.M * fl.bpL.mp.K := by
    have := hv.bp_valid.mp_valid.M_ge; have := hv.bp_valid.mp_valid.K_ge; nlinarith
  have hloop : ∀ fuel cur found hP hV,
      cur + fuel = fb.nSide →
      (found = 0 → hP = 0 ∧ hV = 0 ∧
        ∀ p < cur, ¬(fb.owner p = bkt ∧ (slotIoPairAt fl.bpL.io s.mem p).1 = q_u)) →
      (found = 1 → hP < cur ∧ fb.owner hP = bkt ∧
        slotIoPairAt fl.bpL.io s.mem hP = (q_u, hV)) →
      found ≤ 1 →
      let r := (Memory.spec 0).clientResult s
        (iterate fbScanStepProg ((fl.bpL.mp.toCtx, fl.bpL.io.toCtx), (fb.nSide, (bkt, q_u)))
          fuel ((cur, found), (hP, hV)))
      (r.1.2 = 0 ∧ r.2 = (0, 0) ∧
        ∀ p < fb.nSide, ¬(fb.owner p = bkt ∧ (slotIoPairAt fl.bpL.io s.mem p).1 = q_u)) ∨
      (r.1.2 = 1 ∧ r.2.1 < fb.nSide ∧ fb.owner r.2.1 = bkt ∧
        slotIoPairAt fl.bpL.io s.mem r.2.1 = (q_u, r.2.2)) := by
    intro fuel
    induction fuel with
    | zero =>
      intro cur found hP hV hsum hf0 hf1 hfle
      have hcur : cur = fb.nSide := by omega
      subst hcur
      rcases (by omega : found = 0 ∨ found = 1) with rfl | rfl
      · obtain ⟨rfl, rfl, hall⟩ := hf0 rfl; exact Or.inl ⟨rfl, rfl, hall⟩
      · obtain ⟨hlt, how, hpr⟩ := hf1 rfl; exact Or.inr ⟨rfl, hlt, how, hpr⟩
    | succ k ih =>
      intro cur found hP hV hsum hf0 hf1 hfle
      have hlt : cur < fb.nSide := by omega
      have how_r := fbOwnerOfProg_spec hv.bp_valid.mp_valid hinv.fb_valid h6lt8 hinv.nSide_le hlt
      obtain ⟨hpr_r, hpr_s⟩ := slotIoReadProg_spec hinv.io_inv hlt
      unfold slotIoReadProg at hpr_r hpr_s
      have hst1 := state_fbScanStepProg
        (((fl.bpL.mp.toCtx, fl.bpL.io.toCtx), (fb.nSide, (bkt, q_u))),
          ((cur, found), (hP, hV))) s
      have hres1 : (Memory.spec 0).clientResult s
          (fbScanStepProg
            (((fl.bpL.mp.toCtx, fl.bpL.io.toCtx), (fb.nSide, (bkt, q_u))),
              ((cur, found), (hP, hV)))) =
          if found = 0 ∧ fb.owner cur = bkt ∧ (slotIoPairAt fl.bpL.io s.mem cur).1 = q_u then
            ((cur + 1, 1), (cur, (slotIoPairAt fl.bpL.io s.mem cur).2))
          else
            ((cur + 1, found), (hP, hV)) := by
        unfold fbScanStepProg; dsimp only; rw [ite_eq_left hlt]
        rw [prog_clientResult_bind, state_fbOwnerOfProg, how_r,
          prog_clientResult_bind, hpr_s, hpr_r]
        dsimp only [fb]; split_ifs <;> rfl
      unfold iterate; rw [prog_clientResult_bind, hst1, hres1]
      by_cases hhit : found = 0 ∧ fb.owner cur = bkt ∧ (slotIoPairAt fl.bpL.io s.mem cur).1 = q_u
      · rw [ite_eq_left hhit]
        exact ih (cur + 1) 1 cur (slotIoPairAt fl.bpL.io s.mem cur).2 (by omega)
          (fun hc => absurd hc Nat.one_ne_zero)
          (fun _ => ⟨Nat.lt_succ_self cur, hhit.2.1, Prod.ext hhit.2.2 rfl⟩) le_rfl
      · rw [ite_eq_right hhit]
        refine ih (cur + 1) found hP hV (by omega) (fun hf => ?_) (fun hf => ?_) hfle
        · obtain ⟨hp0, hv0, hall⟩ := hf0 hf
          refine ⟨hp0, hv0, fun p hp => ?_⟩
          rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hp) with rfl | hp_lt
          · exact fun ⟨h1, h2⟩ => hhit ⟨hf, h1, h2⟩
          · exact hall p hp_lt
        · obtain ⟨hp_lt, how, hpr⟩ := hf1 hf
          exact ⟨Nat.lt_succ_of_lt hp_lt, how, hpr⟩
  obtain ⟨_, hloop_st⟩ := fbScanLoop_safe_and_state (mp := fl.bpL.mp) (io := fl.bpL.io)
    (nSide := fb.nSide) (bkt := bkt) (q_u := q_u) hinv.nSide_le hv.bp_valid.mp_valid
    hv.bp_valid.io_valid fb.nSide 0 0 0 0 (Nat.zero_add fb.nSide).le
  have hres_tot : (Memory.spec 0).clientResult s
      (fbScanProg ((fl.bpL.mp.toCtx, fl.bpL.io.toCtx), (bkt, q_u))) =
      let r := (Memory.spec 0).clientResult s
        (iterate fbScanStepProg ((fl.bpL.mp.toCtx, fl.bpL.io.toCtx), (fb.nSide, (bkt, q_u)))
          fb.nSide ((0, 0), (0, 0)))
      (r.1.2, r.2) := by
    unfold fbScanProg fbScanLoopProg
    rw [prog_clientResult_bind, clientState_bpReadScalarProg,
      clientResult_bpReadScalar s (Or.inl rfl)]
    have hmatch : (match fl.bpL.mp.toCtx with
        | (_, _, _, nCap) =>
          if s.mem (fl.bpL.mp.metaBase + 1) ≤ nCap then do
            let z0 ← pure 0
            let r ← iterate fbScanStepProg
              ((fl.bpL.mp.toCtx, fl.bpL.io.toCtx), (s.mem (fl.bpL.mp.metaBase + 1), (bkt, q_u)))
              (s.mem (fl.bpL.mp.metaBase + 1)) ((z0, z0), (z0, z0))
            let r1 := r.1
            pure (r1.2, r.2)
          else pure (0, (0, 0))) =
        (if fb.nSide ≤ fl.bpL.mp.nCap then do
          let z0 ← pure 0
          let r ← iterate fbScanStepProg
            ((fl.bpL.mp.toCtx, fl.bpL.io.toCtx), (fb.nSide, (bkt, q_u)))
            fb.nSide ((z0, z0), (z0, z0))
          pure (r.1.2, r.2)
        else pure (0, (0, 0))) := rfl
    rw [hmatch, ite_eq_left hinv.nSide_le]
    simp only [pure_bind, prog_clientResult_bind]
    dsimp only [fb] at hloop_st ⊢
    rw [hloop_st]; rfl
  refine ⟨hst, ?_⟩
  rw [hres_tot]
  have hout := hloop fb.nSide 0 0 0 0 (Nat.zero_add _)
    (fun _ => ⟨rfl, rfl, fun _ hp => absurd hp (Nat.not_lt_zero _)⟩)
    (fun hc => absurd hc Nat.zero_ne_one) (Nat.zero_le 1)
  rcases hout with ⟨hf0, hp0, hall⟩ | ⟨hf1, hlt_p, how_p, hpr_p⟩
  · have hnone : s_abs u = none := hinv.refines.lookup_eq_none hall
    rw [hnone]; dsimp only; rw [hf0, hp0]
  · have hsome := hinv.refines.lookup_eq_some hlt_p how_p (by rw [hpr_p])
    rw [hsome]; dsimp only
    have hv_eq : (slotIoPairAt fl.bpL.io s.mem
        ((Memory.spec 0).clientResult s
          (iterate fbScanStepProg ((fl.bpL.mp.toCtx, fl.bpL.io.toCtx), (fb.nSide, (bkt, q_u)))
            fb.nSide ((0, 0), (0, 0)))).2.1).2 =
        ((Memory.spec 0).clientResult s
          (iterate fbScanStepProg ((fl.bpL.mp.toCtx, fl.bpL.io.toCtx), (fb.nSide, (bkt, q_u)))
            fb.nSide ((0, 0), (0, 0)))).2.2 := by rw [hpr_p]
    exact ⟨hf1, hlt_p, hv_eq.symm, how_p, hpr_p.trans (Prod.ext rfl hv_eq.symm)⟩

/-! ### Generic Frontier-Invariant Loop Combinator and Range-Swap Primitive -/

theorem iterationSafe_of_frontier {D A : Type}
    (step : D × A → Memory.Prog A)
    (P : ℕ → D → ℕ → Prop)
    {w : ℕ}
    (hfr : ∀ d a s, P w d s.frontier →
      ((Memory.spec 0).clientState s (step (d, a))).frontier = s.frontier)
    {d : D} {s : Memory.State} (h0 : P w d s.frontier) :
    ∀ fuel a,
      iterationSafe step (fun w' (d', _) s' => P w' d' s'.frontier) w d fuel a s ∧
      ((Memory.spec 0).clientState s (iterate step d fuel a)).frontier = s.frontier := by
  intro fuel
  induction fuel generalizing s with
  | zero => intro _; exact ⟨trivial, rfl⟩
  | succ k ih =>
    intro a
    set s₁ := (Memory.spec 0).clientState s (step (d, a))
    set a₁ := (Memory.spec 0).clientResult s (step (d, a))
    have hfr₁ : s₁.frontier = s.frontier := hfr d a s h0
    obtain ⟨hs_k, hfr_k⟩ := ih (hfr₁.symm ▸ h0) a₁
    refine ⟨⟨h0, ?_⟩, ?_⟩
    · dsimp only [iterationSafe]; exact hs_k
    · unfold iterate; rw [StateTransitionSpec.clientState_bind]; exact hfr_k.trans hfr₁

theorem PoolItemsRefines.comp_involution {U V bBits : ℕ} {hBkt : ℕ → ℕ} {nSide : ℕ}
    {ow ow' : ℕ → ℕ} {pr pr' : ℕ → ℕ × ℕ} {s_abs : Fin U → Option (Fin V)}
    (h : PoolItemsRefines U V bBits hBkt nSide ow pr s_abs)
    (σ : ℕ → ℕ) (hinv : ∀ p < nSide, σ (σ p) = p) (hlt : ∀ p < nSide, σ p < nSide)
    (how : ∀ p < nSide, ow' p = ow (σ p))
    (hpr : ∀ p < nSide, pr' p = pr (σ p)) :
    PoolItemsRefines U V bBits hBkt nSide ow' pr' s_abs where
  slot_valid p hp := by
    rw [how p hp, hpr p hp]; exact h.slot_valid _ (hlt p hp)
  slot_inj p₁ hp₁ p₂ hp₂ he1 he2 := by
    rw [how p₁ hp₁, how p₂ hp₂] at he1
    rw [hpr p₁ hp₁, hpr p₂ hp₂] at he2
    have hin := h.slot_inj _ (hlt p₁ hp₁) _ (hlt p₂ hp₂) he1 he2
    have hσ := congrArg σ hin
    rwa [hinv p₁ hp₁, hinv p₂ hp₂] at hσ
  models u v := by
    rw [h.models u v]
    constructor
    · rintro ⟨p, hp, h1, h2, h3⟩
      refine ⟨σ p, hlt p hp, ?_, ?_, ?_⟩
      · rw [how _ (hlt p hp), hinv p hp]; exact h1
      · rw [hpr _ (hlt p hp), hinv p hp]; exact h2
      · rw [hpr _ (hlt p hp), hinv p hp]; exact h3
    · rintro ⟨p, hp, h1, h2, h3⟩
      rw [how p hp] at h1; rw [hpr p hp] at h2 h3
      exact ⟨σ p, hlt p hp, h1, h2, h3⟩

/-- Index involution swapping `[b₁, b₁ + len)` with `[b₂, b₂ + len)` when equal or disjoint. -/
@[expose] def swapRangeIdx (b₁ b₂ len p : ℕ) : ℕ :=
  if b₁ ≤ p ∧ p < b₁ + len then
    b₂ + (p - b₁)
  else if b₂ ≤ p ∧ p < b₂ + len then
    b₁ + (p - b₂)
  else
    p

theorem swapRangeIdx_lt {b₁ b₂ len nSide p : ℕ}
    (h₁ : b₁ + len ≤ nSide) (h₂ : b₂ + len ≤ nSide) (hp : p < nSide) :
    swapRangeIdx b₁ b₂ len p < nSide := by
  unfold swapRangeIdx; split_ifs <;> omega

theorem swapRangeIdx_involutive {b₁ b₂ len p : ℕ}
    (hdisj : b₁ = b₂ ∨ b₁ + len ≤ b₂ ∨ b₂ + len ≤ b₁) :
    swapRangeIdx b₁ b₂ len (swapRangeIdx b₁ b₂ len p) = p := by
  unfold swapRangeIdx
  by_cases h1 : b₁ ≤ p ∧ p < b₁ + len
  · rw [ite_eq_left h1]
    rcases hdisj with rfl | hle12 | hle21
    · rw [ite_eq_left (by omega)]; omega
    · rw [ite_eq_right (by omega), ite_eq_left (by omega)]; omega
    · rw [ite_eq_right (by omega), ite_eq_left (by omega)]; omega
  · rw [ite_eq_right h1]
    by_cases h2 : b₂ ≤ p ∧ p < b₂ + len
    · rw [ite_eq_left h2, ite_eq_left (by omega)]; omega
    · rw [ite_eq_right h2, ite_eq_right h1, ite_eq_right h2]

theorem swapRangeIdx_step {b₁ b₂ k : ℕ} {arr : ℕ → ℕ × ℕ}
    (hdisj : b₁ = b₂ ∨ b₁ + (k + 1) ≤ b₂ ∨ b₂ + (k + 1) ≤ b₁) (p : ℕ) :
    (PhysSwap.mk (b₁ + k) (b₂ + k)).apply (fun q => arr (swapRangeIdx b₁ b₂ k q)) p =
      arr (swapRangeIdx b₁ b₂ (k + 1) p) := by
  have hfix₁ : swapRangeIdx b₁ b₂ k (b₁ + k) = b₁ + k := by
    unfold swapRangeIdx; rcases hdisj with rfl | _ | _ <;> (split_ifs <;> omega)
  have hfix₂ : swapRangeIdx b₁ b₂ k (b₂ + k) = b₂ + k := by
    unfold swapRangeIdx; rcases hdisj with rfl | _ | _ <;> (split_ifs <;> omega)
  let sw : PhysSwap := ⟨b₁ + k, b₂ + k⟩
  by_cases hp1 : p = b₁ + k
  · subst hp1
    rw [sw.apply_p₁, hfix₂]
    unfold swapRangeIdx; rw [ite_eq_left (by omega)]
    exact congrArg arr (by omega)
  · by_cases hp2 : p = b₂ + k
    · subst hp2
      rw [sw.apply_p₂, hfix₁]
      unfold swapRangeIdx
      rcases hdisj with rfl | _ | _
      · exact absurd rfl hp1
      · rw [ite_eq_right (by omega), ite_eq_left (by omega)]
        exact congrArg arr (by omega)
      · rw [ite_eq_right (by omega), ite_eq_left (by omega)]
        exact congrArg arr (by omega)
    · rw [sw.apply_of_ne _ hp1 hp2]
      unfold swapRangeIdx
      have hc1 : (b₁ ≤ p ∧ p < b₁ + (k + 1)) ↔ (b₁ ≤ p ∧ p < b₁ + k) := by omega
      have hc2 : (b₂ ≤ p ∧ p < b₂ + (k + 1)) ↔ (b₂ ≤ p ∧ p < b₂ + k) := by omega
      simp only [hc1, hc2]

/-- Single-slot swap step for `fbSwapRangeLoopProg` (`¬ReadsWidth`). -/
def fbSwapRangeStepProg : (BlockPoolCtx × (ℕ × ℕ)) × ℕ → Memory.Prog ℕ
  | (((mctx, ioctx), (b₁, b₂)), cur) => do
    let _ ← bpReadScalarProg (mctx, 1)
    let (_, (_, (_, nCap))) := mctx
    if cur < nCap then
      if b₁ < nCap - cur then
        if b₂ < nCap - cur then do
          let p₁ ← pure (b₁ + cur)
          let p₂ ← pure (b₂ + cur)
          slotIoSwapRawProg (ioctx, (p₁, p₂))
          pure (cur + 1)
        else
          pure cur
      else
        pure cur
    else
      pure cur

theorem memoryCost_fbSwapRangeStep_pos
    (x : (BlockPoolCtx × (ℕ × ℕ)) × ℕ) (s : Memory.State) :
    1 ≤ memoryCost (fbSwapRangeStepProg x) s := by
  rcases x with ⟨⟨⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨_, _⟩⟩⟩, _⟩,
    ⟨_, _⟩⟩, _⟩
  simp [fbSwapRangeStepProg, bpReadScalarProg]

theorem frontier_fbSwapRangeStep (d : BlockPoolCtx × (ℕ × ℕ)) (cur : ℕ) (s : Memory.State)
    (hw : 0 < (SlotIoLayout.ofCtx (bpCtxIo d)).pgL.w) :
    ((Memory.spec 0).clientState s (fbSwapRangeStepProg (d, cur))).frontier = s.frontier := by
  rcases d with ⟨⟨⟨p1, ⟨p2, ⟨mt, nCap⟩⟩⟩, ioctx⟩, ⟨b₁, b₂⟩⟩
  unfold fbSwapRangeStepProg
  rw [StateTransitionSpec.clientState_bind, clientState_bpReadScalarProg]; dsimp only
  split_ifs
  · simp only [pure_bind]; rw [StateTransitionSpec.clientState_bind]
    have hswf := (slotIoSwapProg_frame (io := SlotIoLayout.ofCtx ioctx) hw
      (b₁ + cur) (b₂ + cur)).frontier_eq s
    unfold slotIoSwapProg at hswf; rw [SlotIoLayout.toCtx_ofCtx] at hswf
    exact hswf
  all_goals rfl

theorem realizesBounded_fbSwapRangeStep :
    RealizesBounded .exact fbSwapRangeStepProg
      (WordEncoding.encode (α := (BlockPoolCtx × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w (((mctx, ioctx), _), _) s =>
        (BpMetaLayout.ofCtx mctx).Valid w s.frontier ∧
        (SlotIoLayout.ofCtx ioctx).Valid w s.frontier)
      (fun _ _ => 0) := by
  have hrs := realizesBounded_bpReadScalar
  have hsw := realizesBounded_slotIoSwapRaw
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨⟨⟨mb, obm⟩, ⟨osd, otd⟩⟩, ⟨⟨oso, oto⟩, ⟨pb, wv⟩⟩⟩,
      ⟨⟨⟨m, k⟩, ⟨ms, mbk⟩⟩, ⟨mt, nc⟩⟩⟩, ioctx⟩, ⟨b₁, b₂⟩⟩, cur⟩
    obtain ⟨hmv, hiov⟩ := h
    have hw := hmv.w_mach_pos
    have hw1 : 1 < 2 ^ w := Nat.one_lt_two_pow hw.ne'
    have hnc_w := hmv.nCap_lt_two_pow_w
    have hc_w : cur < 2 ^ w := hwords 29
    have hb1_w : b₁ < 2 ^ w := hwords 27
    have hb2_w : b₂ < 2 ^ w := hwords 28
    dsimp only [BpMetaLayout.ofCtx] at hnc_w
    dsimp only at *
    try dsimp only [Fits, StateTransitionSpec.clientState] at *
    try simp only [runClient_state_bpReadScalarProg] at *
    first | exact hmv | exact hiov | exact hw1 | omega)

/-- Bounded iteration loop swapping `fuel` consecutive slots starting at `cur`. -/
def fbSwapRangeLoopProg :
    ((BlockPoolCtx × (ℕ × ℕ)) × ℕ) × ℕ → Memory.Prog ℕ
  | ((d, cur), fuel) => iterate fbSwapRangeStepProg d fuel cur

theorem realizesBounded_fbSwapRangeLoop :
    RealizesBounded .exact fbSwapRangeLoopProg
      (WordEncoding.encode (α := ((BlockPoolCtx × (ℕ × ℕ)) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w ((d, cur), fuel) s =>
        iterationSafe fbSwapRangeStepProg
          (fun w' (((mctx, ioctx), _), _) s' =>
            (BpMetaLayout.ofCtx mctx).Valid w' s'.frontier ∧
            (SlotIoLayout.ofCtx ioctx).Valid w' s'.frontier) w d fuel cur s)
      (fun _ _ => 0) :=
  RealizesBounded.iterate₀
    (WordEncoding.encode (α := BlockPoolCtx × (ℕ × ℕ)))
    (WordEncoding.encode (α := ℕ))
    realizesBounded_fbSwapRangeStep
    memoryCost_fbSwapRangeStep_pos

/-- Swap `len` consecutive slots `[b₁, b₁ + len)` and `[b₂, b₂ + len)` in `ioctx` (`¬ReadsWidth`).
-/
def fbSwapRangeProg : (BlockPoolCtx × (ℕ × ℕ)) × ℕ → Memory.Prog Unit
  | (d, len) => do
    let z0 ← pure 0
    let _ ← fbSwapRangeLoopProg ((d, z0), len)
    pure ()

theorem frontier_fbSwapRangeProg (d : BlockPoolCtx × (ℕ × ℕ)) (len : ℕ) (s : Memory.State)
    (hw : 0 < (SlotIoLayout.ofCtx (bpCtxIo d)).pgL.w) :
    ((Memory.spec 0).clientState s (fbSwapRangeProg (d, len))).frontier = s.frontier := by
  unfold fbSwapRangeProg fbSwapRangeLoopProg
  simp only [pure_bind]
  rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_pure]
  exact (iterationSafe_of_frontier fbSwapRangeStepProg
    (fun _ d' _ => 0 < (SlotIoLayout.ofCtx d'.1.2).pgL.w) (w := 0)
    (fun d' a s' hw' => frontier_fbSwapRangeStep d' a s' hw')
    (d := d) (s := s) hw len 0).2

theorem realizesBounded_fbSwapRange :
    RealizesBounded .exact fbSwapRangeProg
      (WordEncoding.encode (α := (BlockPoolCtx × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (((mctx, ioctx), _), _) s =>
        (BpMetaLayout.ofCtx mctx).Valid w s.frontier ∧
        (SlotIoLayout.ofCtx ioctx).Valid w s.frontier)
      (fun _ _ => 0) := by
  have hrl := realizesBounded_fbSwapRangeLoop
  realize
  all_goals (
    rcases d with ⟨⟨⟨mctx, ioctx⟩, ⟨b₁, b₂⟩⟩, len⟩
    obtain ⟨hmv, hiov⟩ := h
    dsimp only [Fits] at *
    exact (iterationSafe_of_frontier fbSwapRangeStepProg
      (fun w' (d' : BlockPoolCtx × (ℕ × ℕ)) fr' =>
        (BpMetaLayout.ofCtx d'.1.1).Valid w' fr' ∧
        (SlotIoLayout.ofCtx d'.1.2).Valid w' fr')
      (fun d' a' s' hd' => frontier_fbSwapRangeStep d' a' s' hd'.2.w_pos)
      (d := ((mctx, ioctx), (b₁, b₂))) (s := s) ⟨hmv, hiov⟩ len 0).1)

theorem fbSwapRangeProg_spec {mp : BpMetaLayout} {io : SlotIoLayout}
    {w nSide slack b₁ b₂ len : ℕ} {s : Memory.State}
    (_hmv : mp.Valid w s.frontier) (hiov : io.Valid io.pgL.w s.frontier)
    (hinv : io.StateInv nSide slack s.mem)
    (hns_lt : nSide ≤ mp.nCap)
    (hb₁ : b₁ + len ≤ nSide) (hb₂ : b₂ + len ≤ nSide)
    (hdisj : b₁ = b₂ ∨ b₁ + len ≤ b₂ ∨ b₂ + len ≤ b₁) :
    let s' :=
      (Memory.spec 0).clientState s (fbSwapRangeProg (((mp.toCtx, io.toCtx), (b₁, b₂)), len))
    s'.frontier = s.frontier ∧
    io.StateInv nSide slack s'.mem ∧
    (∀ p < nSide, slotIoPairAt io s'.mem p = slotIoPairAt io s.mem (swapRangeIdx b₁ b₂ len p)) ∧
    (∀ addr, ¬io.OwnsAddr addr → s'.mem addr = s.mem addr) ∧
    (io.usePaged ≠ 0 →
      extractPageUnperm io.pgL s'.mem = extractPageUnperm io.pgL s.mem ∧
      ∀ idx < (extractPagePair io.pgL s.mem).virtLen io.partner.side,
        slotIoPairAt io.partner s'.mem idx = slotIoPairAt io.partner s.mem idx) := by
  dsimp only
  -- Prove by induction on `k ≤ len` starting from `cur = 0`? Wait: `iterate` peels from the
  -- FRONT (`cur = 0, 1, ...`), so we prove a generalized induction over `fuel` with offset `cur`:
  have hloop : ∀ fuel cur (st : Memory.State),
      st.frontier = s.frontier →
      cur + fuel = len →
      io.StateInv nSide slack st.mem →
      (∀ p < nSide, slotIoPairAt io st.mem p = slotIoPairAt io s.mem (swapRangeIdx b₁ b₂ cur p)) →
      (∀ addr, ¬io.OwnsAddr addr → st.mem addr = s.mem addr) →
      (io.usePaged ≠ 0 →
        extractPageUnperm io.pgL st.mem = extractPageUnperm io.pgL s.mem ∧
        ∀ idx < (extractPagePair io.pgL s.mem).virtLen io.partner.side,
          slotIoPairAt io.partner st.mem idx = slotIoPairAt io.partner s.mem idx) →
      let st' := (Memory.spec 0).clientState st
        (iterate fbSwapRangeStepProg ((mp.toCtx, io.toCtx), (b₁, b₂)) fuel cur)
      st'.frontier = s.frontier ∧
      io.StateInv nSide slack st'.mem ∧
      (∀ p < nSide, slotIoPairAt io st'.mem p = slotIoPairAt io s.mem (swapRangeIdx b₁ b₂ len p)) ∧
      (∀ addr, ¬io.OwnsAddr addr → st'.mem addr = s.mem addr) ∧
      (io.usePaged ≠ 0 →
        extractPageUnperm io.pgL st'.mem = extractPageUnperm io.pgL s.mem ∧
        ∀ idx < (extractPagePair io.pgL s.mem).virtLen io.partner.side,
          slotIoPairAt io.partner st'.mem idx = slotIoPairAt io.partner s.mem idx) := by
    intro fuel
    induction fuel with
    | zero =>
      intro cur st hfr hsum hio harr hout hpart
      have hcur : cur = len := by omega
      subst hcur
      exact ⟨hfr, hio, harr, hout, hpart⟩
    | succ f ih =>
      intro cur st hfr hsum hio harr hout hpart
      have hc_nc : cur < mp.nCap := by omega
      have hb1_nc : b₁ < mp.nCap - cur := by omega
      have hb2_nc : b₂ < mp.nCap - cur := by omega
      have hp1_ns : b₁ + cur < nSide := by omega
      have hp2_ns : b₂ + cur < nSide := by omega
      obtain ⟨hio₁, harr₁, hpart₁⟩ :=
        slotIoSwapProg_spec (hfr.symm ▸ hiov) hio hp1_ns hp2_ns
      have hswf := slotIoSwapProg_frame (io := io) hiov.w_pos (b₁ + cur) (b₂ + cur)
      unfold slotIoSwapProg at hio₁ harr₁ hpart₁ hswf
      set st₁ := (Memory.spec 0).clientState st (slotIoSwapRawProg (io.toCtx, (b₁ + cur, b₂ + cur)))
      have hstep_st : (Memory.spec 0).clientState st
          (fbSwapRangeStepProg (((mp.toCtx, io.toCtx), (b₁, b₂)), cur)) = st₁ := by
        unfold fbSwapRangeStepProg
        rw [StateTransitionSpec.clientState_bind, clientState_bpReadScalarProg]
        have hm : (match mp.toCtx with
            | (_, _, _, nCap) =>
              if cur < nCap then
                if b₁ < nCap - cur then
                  if b₂ < nCap - cur then do
                    let p₁ ← pure (b₁ + cur)
                    let p₂ ← pure (b₂ + cur)
                    slotIoSwapRawProg (io.toCtx, (p₁, p₂))
                    pure (cur + 1)
                  else pure cur
                else pure cur
              else pure cur) =
            (if cur < mp.nCap then
              if b₁ < mp.nCap - cur then
                if b₂ < mp.nCap - cur then do
                  slotIoSwapRawProg (io.toCtx, (b₁ + cur, b₂ + cur))
                  pure (cur + 1)
                else pure cur
              else pure cur
            else pure cur) := rfl
        rw [hm, ite_eq_left hc_nc, ite_eq_left hb1_nc, ite_eq_left hb2_nc,
          StateTransitionSpec.clientState_bind]
        rfl
      have hstep_res : (Memory.spec 0).clientResult st
          (fbSwapRangeStepProg (((mp.toCtx, io.toCtx), (b₁, b₂)), cur)) = cur + 1 := by
        unfold fbSwapRangeStepProg
        rw [prog_clientResult_bind, clientState_bpReadScalarProg]
        have hm : (match mp.toCtx with
            | (_, _, _, nCap) =>
              if cur < nCap then
                if b₁ < nCap - cur then
                  if b₂ < nCap - cur then do
                    let p₁ ← pure (b₁ + cur)
                    let p₂ ← pure (b₂ + cur)
                    slotIoSwapRawProg (io.toCtx, (p₁, p₂))
                    pure (cur + 1)
                  else pure cur
                else pure cur
              else pure cur) =
            (if cur < mp.nCap then
              if b₁ < mp.nCap - cur then
                if b₂ < mp.nCap - cur then do
                  slotIoSwapRawProg (io.toCtx, (b₁ + cur, b₂ + cur))
                  pure (cur + 1)
                else pure cur
              else pure cur
            else pure cur) := rfl
        rw [hm, ite_eq_left hc_nc, ite_eq_left hb1_nc, ite_eq_left hb2_nc,
          prog_clientResult_bind, prog_clientResult_pure]
      have hdisj_c : b₁ = b₂ ∨ b₁ + (cur + 1) ≤ b₂ ∨ b₂ + (cur + 1) ≤ b₁ := by
        rcases hdisj with rfl | h12 | h21 <;> [exact Or.inl rfl; exact Or.inr (Or.inl (by omega));
          exact Or.inr (Or.inr (by omega))]
      unfold iterate; dsimp only
      rw [StateTransitionSpec.clientState_bind, hstep_st, hstep_res]
      refine ih (cur + 1) st₁ ((hswf.frontier_eq st).trans hfr) (by omega) hio₁
        (fun p hp => ?_)
        (fun addr ha => (hswf.mem_outside st addr ha).trans (hout addr ha))
        (fun hnz => ?_)
      · rw [harr₁ p hp]
        have hcongr : (PhysSwap.mk (b₁ + cur) (b₂ + cur)).apply (slotIoPairAt io st.mem) p =
            (PhysSwap.mk (b₁ + cur) (b₂ + cur)).apply
              (fun q => slotIoPairAt io s.mem (swapRangeIdx b₁ b₂ cur q)) p := by
          let sw : PhysSwap := ⟨b₁ + cur, b₂ + cur⟩
          by_cases h1 : p = b₁ + cur
          · subst h1; rw [sw.apply_p₁, sw.apply_p₁]; exact harr _ hp2_ns
          · by_cases h2 : p = b₂ + cur
            · subst h2; rw [sw.apply_p₂, sw.apply_p₂]; exact harr _ hp1_ns
            · rw [sw.apply_of_ne _ h1 h2, sw.apply_of_ne _ h1 h2]; exact harr p hp
        exact hcongr.trans (swapRangeIdx_step hdisj_c p)
      · obtain ⟨hu₀, hp₀⟩ := hpart hnz
        obtain ⟨hu₁, hp₁⟩ := hpart₁ hnz
        have hvl₀ : (extractPagePair io.pgL st.mem).virtLen io.partner.side =
            (extractPagePair io.pgL s.mem).virtLen io.partner.side :=
          congrArg (fun u => u.st.virtLen io.partner.side) hu₀
        exact ⟨hu₁.trans hu₀, fun idx hidx => (hp₁ idx (hvl₀.symm ▸ hidx)).trans (hp₀ idx hidx)⟩
  unfold fbSwapRangeProg fbSwapRangeLoopProg
  simp only [pure_bind]
  rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_pure]
  exact hloop len 0 s rfl (Nat.zero_add len) hinv
    (fun p _ => congrArg (slotIoPairAt io s.mem) (by unfold swapRangeIdx; split_ifs <;> omega))
    (fun _ _ => rfl)
    (fun _ => ⟨rfl, fun _ _ => rfl⟩)

/-! ### `FallbackPool` Pigeonhole Promotion, Block Demotion, and Slot Deletion -/

/-- Transposition swapping indices `i` and `j` and fixing all other indices. -/
@[expose] def swapIdx (i j x : ℕ) : ℕ :=
  if x = i then j else if x = j then i else x

theorem swapIdx_involutive (i j x : ℕ) : swapIdx i j (swapIdx i j x) = x := by
  unfold swapIdx; by_cases h1 : x = i
  · subst h1; by_cases h2 : j = x <;> simp [h2]
  · by_cases h2 : x = j
    · subst h2; simp [h1]
    · simp [h1, h2]

theorem swapIdx_lt {i j n x : ℕ} (hi : i < n) (hj : j < n) (hx : x < n) :
    swapIdx i j x < n := by
  unfold swapIdx; split_ifs <;> assumption

theorem physSwap_apply_eq_swapIdx {α : Type*} (i j : ℕ) (f : ℕ → α) (x : ℕ) :
    (PhysSwap.mk i j).apply f x = f (swapIdx i j x) := by
  let sw : PhysSwap := ⟨i, j⟩
  by_cases h1 : x = i
  · subst h1; rw [sw.apply_p₁]; unfold swapIdx; dsimp only [sw]; simp
  · by_cases h2 : x = j
    · subst h2; rw [sw.apply_p₂]; unfold swapIdx; dsimp only [sw]; simp [h1]
    · rw [sw.apply_of_ne f h1 h2]; unfold swapIdx; simp [h1, h2]

theorem filter_card_comp_swapIdx {n i j b : ℕ} {ot : ℕ → ℕ} (hi : i < n) (hj : j < n) :
    ((Finset.range n).filter (fun t => ot (swapIdx i j t) = b)).card =
      ((Finset.range n).filter (fun t => ot t = b)).card :=
  Finset.card_bij (fun t _ => swapIdx i j t)
    (fun t ht => by
      obtain ⟨h1, h2⟩ := mem_filter.mp ht
      exact mem_filter.mpr ⟨mem_range.mpr (swapIdx_lt hi hj (mem_range.mp h1)), h2⟩)
    (fun t₁ _ t₂ _ heq => by
      have h := congrArg (swapIdx i j) heq
      rwa [swapIdx_involutive, swapIdx_involutive] at h)
    (fun t ht => by
      obtain ⟨h1, h2⟩ := mem_filter.mp ht
      refine ⟨swapIdx i j t, mem_filter.mpr ⟨mem_range.mpr (swapIdx_lt hi hj (mem_range.mp h1)),
        ?_⟩, swapIdx_involutive i j t⟩
      rwa [swapIdx_involutive])

/-- Read-only step counting occurrences of bucket `b` in `ownerTail[0 .. tailLen)`. -/
private def fbCountBktStepProg : (BpMetaCtx × (ℕ × ℕ)) × (ℕ × ℕ) → Memory.Prog (ℕ × ℕ)
  | ((mctx, (tailLen, b)), (t, cnt)) => do
    let _ ← bpReadScalarProg (mctx, 1)
    let (_, (_, (_, nCap))) := mctx
    if t < tailLen then
      if cnt < nCap then do
        let bt ← bpReadTailDirRawProg (mctx, t)
        if bt = b then pure (t + 1, cnt + 1) else pure (t + 1, cnt)
      else pure (t, cnt)
    else pure (t, cnt)

private theorem memoryCost_fbCountBktStep_pos
    (x : (BpMetaCtx × (ℕ × ℕ)) × (ℕ × ℕ)) (s : Memory.State) :
    1 ≤ memoryCost (fbCountBktStepProg x) s := by
  rcases x with ⟨⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨_, _⟩⟩⟩,
    ⟨_, _⟩⟩, ⟨_, _⟩⟩
  simp [fbCountBktStepProg, bpReadScalarProg]

private theorem state_fbCountBktStep (x : (BpMetaCtx × (ℕ × ℕ)) × (ℕ × ℕ)) (s : Memory.State) :
    (Memory.spec 0).clientState s (fbCountBktStepProg x) = s := by
  rcases x with ⟨⟨⟨p1, ⟨p2, ⟨mt, nCap⟩⟩⟩, ⟨tailLen, b⟩⟩, ⟨t, cnt⟩⟩
  unfold fbCountBktStepProg
  rw [StateTransitionSpec.clientState_bind, clientState_bpReadScalarProg]; dsimp only
  split_ifs
  · rw [StateTransitionSpec.clientState_bind, clientState_bpReadTailDirRawProg]
    split_ifs <;> rfl
  all_goals rfl

private theorem realizesBounded_fbCountBktStep :
    RealizesBounded .exact fbCountBktStepProg
      (WordEncoding.encode (α := (BpMetaCtx × (ℕ × ℕ)) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w ((mctx, _), _) s => (BpMetaLayout.ofCtx mctx).Valid w s.frontier)
      (fun _ _ => 0) := by
  have hrs := realizesBounded_bpReadScalar
  have hrtd := realizesBounded_bpReadTailDirRaw
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨⟨mb, obm⟩, ⟨osd, otd⟩⟩, ⟨⟨oso, oto⟩, ⟨pb, wv⟩⟩⟩,
      ⟨⟨⟨m, k⟩, ⟨ms, mbk⟩⟩, ⟨mt, nc⟩⟩⟩, ⟨tailLen, b⟩⟩, ⟨t, cnt⟩⟩
    have hmv := h
    have hw := hmv.w_mach_pos
    have hw1 : 1 < 2 ^ w := Nat.one_lt_two_pow hw.ne'
    have hnc_w := hmv.nCap_lt_two_pow_w
    have htl_w : tailLen < 2 ^ w := hwords 14
    have ht_w : t < 2 ^ w := hwords 16
    have hc_w : cnt < 2 ^ w := hwords 17
    dsimp only [BpMetaLayout.ofCtx] at hnc_w
    dsimp only at *
    try dsimp only [Fits, StateTransitionSpec.clientState] at *
    try simp only [runClient_state_bpReadScalarProg] at *
    first | exact hmv | exact hw1 | omega)

private def fbCountBktLoopProg :
    ((BpMetaCtx × (ℕ × ℕ)) × (ℕ × ℕ)) × ℕ → Memory.Prog (ℕ × ℕ)
  | ((d, acc), fuel) => iterate fbCountBktStepProg d fuel acc

private theorem realizesBounded_fbCountBktLoop :
    RealizesBounded .exact fbCountBktLoopProg
      (WordEncoding.encode (α := ((BpMetaCtx × (ℕ × ℕ)) × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w ((d, acc), fuel) s =>
        iterationSafe fbCountBktStepProg
          (fun w' ((mctx, _), _) s' => (BpMetaLayout.ofCtx mctx).Valid w' s'.frontier)
          w d fuel acc s)
      (fun _ _ => 0) :=
  RealizesBounded.iterate₀
    (WordEncoding.encode (α := BpMetaCtx × (ℕ × ℕ)))
    (WordEncoding.encode (α := ℕ × ℕ))
    realizesBounded_fbCountBktStep
    memoryCost_fbCountBktStep_pos

private theorem state_fbCountBktLoop (x : ((BpMetaCtx × (ℕ × ℕ)) × (ℕ × ℕ)) × ℕ)
    (s : Memory.State) :
    (Memory.spec 0).clientState s (fbCountBktLoopProg x) = s := by
  rcases x with ⟨⟨d, acc⟩, fuel⟩
  unfold fbCountBktLoopProg
  induction fuel generalizing acc with
  | zero => rfl
  | succ f ih =>
    unfold iterate; rw [StateTransitionSpec.clientState_bind, state_fbCountBktStep]
    exact ih _

private theorem fbCountBktLoop_spec {mp : BpMetaLayout} {tailLen b : ℕ} {s : Memory.State}
    (htl_nc : tailLen ≤ mp.nCap) (htl_8 : tailLen < 8 * mp.M * mp.K) :
    ((Memory.spec 0).clientResult s
      (fbCountBktLoopProg (((mp.toCtx, (tailLen, b)), (0, 0)), tailLen))).2 =
      ((Finset.range tailLen).filter
        (fun t => (extractFallback mp s.mem).ownerTail t = b)).card := by
  set ot := (extractFallback mp s.mem).ownerTail
  have hloop : ∀ fuel t cnt,
      t + fuel = tailLen →
      cnt = ((Finset.range t).filter (fun i => ot i = b)).card →
      ((Memory.spec 0).clientResult s
        (iterate fbCountBktStepProg (mp.toCtx, (tailLen, b)) fuel (t, cnt))).2 =
        ((Finset.range tailLen).filter (fun i => ot i = b)).card := by
    intro fuel; induction fuel with
    | zero =>
      intro t cnt hsum hcnt
      have ht : t = tailLen := by omega
      subst ht; exact hcnt
    | succ f ih =>
      intro t cnt hsum hcnt
      have ht_lt : t < tailLen := by omega
      have ht_8 : t < 8 * mp.M * mp.K := ht_lt.trans htl_8
      have hcnt_le : cnt ≤ t := by
        rw [hcnt]; exact (Finset.card_filter_le _ _).trans (by simp)
      have hc_nc : cnt < mp.nCap := by omega
      have hbt_r : (Memory.spec 0).clientResult s (bpReadTailDirRawProg (mp.toCtx, t)) = ot t := by
        unfold bpReadTailDirRawProg; dsimp only [BpMetaLayout.toCtx, ot, extractFallback]
        rw [ite_eq_left ht_8, ite_eq_left ht_8, clientResult_readPackedCompGenProg]
      have hres1 : (Memory.spec 0).clientResult s
          (fbCountBktStepProg ((mp.toCtx, (tailLen, b)), (t, cnt))) =
          if ot t = b then (t + 1, cnt + 1) else (t + 1, cnt) := by
        unfold fbCountBktStepProg
        rw [prog_clientResult_bind, clientState_bpReadScalarProg]
        have hm : (match mp.toCtx with
            | (_, _, _, nCap) =>
              if t < tailLen then
                if cnt < nCap then do
                  let bt ← bpReadTailDirRawProg (mp.toCtx, t)
                  if bt = b then pure (t + 1, cnt + 1) else pure (t + 1, cnt)
                else pure (t, cnt)
              else pure (t, cnt)) =
            (if t < tailLen then
              if cnt < mp.nCap then do
                let bt ← bpReadTailDirRawProg (mp.toCtx, t)
                if bt = b then pure (t + 1, cnt + 1) else pure (t + 1, cnt)
              else pure (t, cnt)
            else pure (t, cnt)) := rfl
        rw [hm, ite_eq_left ht_lt, ite_eq_left hc_nc, prog_clientResult_bind,
          clientState_bpReadTailDirRawProg, hbt_r]
        split_ifs <;> rfl
      unfold iterate
      rw [prog_clientResult_bind, state_fbCountBktStep, hres1]
      have hcard_succ : ((Finset.range (t + 1)).filter (fun i => ot i = b)).card =
          if ot t = b then cnt + 1 else cnt := by
        rw [Finset.range_add_one, Finset.filter_insert]
        split_ifs with heq
        · rw [Finset.card_insert_of_notMem (by simp), hcnt]
        · exact hcnt.symm
      by_cases heq : ot t = b
      · rw [ite_eq_left heq]
        exact ih (t + 1) (cnt + 1) (by omega) (by rw [hcard_succ, ite_eq_left heq])
      · rw [ite_eq_right heq]
        exact ih (t + 1) cnt (by omega) (by rw [hcard_succ, ite_eq_right heq])
  exact hloop tailLen 0 0 (Nat.zero_add _) (by simp)

/-- Read-only outer scan over `b = 0 .. M - 1` finding `bStar < M` with `≥ K` tail items. -/
private def fbFindHeavyBktStepProg : (BpMetaCtx × ℕ) × (ℕ × ℕ) → Memory.Prog (ℕ × ℕ)
  | ((mctx, tailLen), (b, bStar)) => do
    let _ ← bpReadScalarProg (mctx, 1)
    let (_, (((m, k), _), (_, nCap))) := mctx
    if b < m then
      if tailLen ≤ nCap then do
        let z0 ← pure 0
        let tc ← fbCountBktLoopProg ((((mctx, (tailLen, b)), (z0, z0))), tailLen)
        if k ≤ tc.2 then pure (b + 1, b) else pure (b + 1, bStar)
      else pure (b, bStar)
    else pure (b, bStar)

private theorem memoryCost_fbFindHeavyBktStep_pos
    (x : (BpMetaCtx × ℕ) × (ℕ × ℕ)) (s : Memory.State) :
    1 ≤ memoryCost (fbFindHeavyBktStepProg x) s := by
  rcases x with ⟨⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨_, _⟩⟩⟩, _⟩,
    ⟨_, _⟩⟩
  simp [fbFindHeavyBktStepProg, bpReadScalarProg]

private theorem state_fbFindHeavyBktStep (x : (BpMetaCtx × ℕ) × (ℕ × ℕ)) (s : Memory.State) :
    (Memory.spec 0).clientState s (fbFindHeavyBktStepProg x) = s := by
  rcases x with ⟨⟨⟨p1, ⟨⟨⟨m, k⟩, p2b⟩, ⟨mt, nCap⟩⟩⟩, tailLen⟩, ⟨b, bStar⟩⟩
  unfold fbFindHeavyBktStepProg
  rw [StateTransitionSpec.clientState_bind, clientState_bpReadScalarProg]; dsimp only
  split_ifs
  · simp only [pure_bind]; rw [StateTransitionSpec.clientState_bind, state_fbCountBktLoop]
    split_ifs <;> rfl
  all_goals rfl

private theorem realizesBounded_fbFindHeavyBktStep :
    RealizesBounded .exact fbFindHeavyBktStepProg
      (WordEncoding.encode (α := (BpMetaCtx × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w ((mctx, _), _) s => (BpMetaLayout.ofCtx mctx).Valid w s.frontier)
      (fun _ _ => 0) := by
  have hrs := realizesBounded_bpReadScalar
  have hcl := realizesBounded_fbCountBktLoop
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨⟨mb, obm⟩, ⟨osd, otd⟩⟩, ⟨⟨oso, oto⟩, ⟨pb, wv⟩⟩⟩,
      ⟨⟨⟨m, k⟩, ⟨ms, mbk⟩⟩, ⟨mt, nc⟩⟩⟩, tailLen⟩, ⟨b, bStar⟩⟩
    have hmv := h
    have hw := hmv.w_mach_pos
    have hw1 : 1 < 2 ^ w := Nat.one_lt_two_pow hw.ne'
    have hm_w : m < 2 ^ w := lt_of_le_of_lt
      (by have := hmv.sixteen_M_le; dsimp only [BpMetaLayout.ofCtx] at *; omega)
      hmv.nCap_lt_two_pow_w
    have hbs_w : bStar < 2 ^ w := hwords 16
    let mctx : BpMetaCtx := ((((mb, obm), (osd, otd)), ((oso, oto), (pb, wv))),
      (((m, k), (ms, mbk)), (mt, nc)))
    dsimp only at *
    try dsimp only [Fits, StateTransitionSpec.clientState] at *
    try simp only [runClient_state_bpReadScalarProg] at *
    first | exact hmv | exact hw1 | omega | (
      exact (iterationSafe_of_frontier fbCountBktStepProg
        (fun w' (d' : BpMetaCtx × (ℕ × ℕ)) fr' => (BpMetaLayout.ofCtx d'.1).Valid w' fr')
        (fun d' a' s' _ => congrArg Memory.State.frontier (state_fbCountBktStep (d', a') s'))
        (d := (mctx, (tailLen, b))) (s := s) hmv tailLen (0, 0)).1))

/-- Outer loop scanning buckets `0..M - 1` to find a tail-heavy bucket `bStar`. -/
def fbFindHeavyBktLoopProg :
    ((BpMetaCtx × ℕ) × (ℕ × ℕ)) × ℕ → Memory.Prog (ℕ × ℕ)
  | ((d, acc), fuel) => iterate fbFindHeavyBktStepProg d fuel acc

private theorem realizesBounded_fbFindHeavyBktLoop :
    RealizesBounded .exact fbFindHeavyBktLoopProg
      (WordEncoding.encode (α := ((BpMetaCtx × ℕ) × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w ((d, acc), fuel) s =>
        iterationSafe fbFindHeavyBktStepProg
          (fun w' ((mctx, _), _) s' => (BpMetaLayout.ofCtx mctx).Valid w' s'.frontier)
          w d fuel acc s)
      (fun _ _ => 0) :=
  RealizesBounded.iterate₀
    (WordEncoding.encode (α := BpMetaCtx × ℕ))
    (WordEncoding.encode (α := ℕ × ℕ))
    realizesBounded_fbFindHeavyBktStep
    memoryCost_fbFindHeavyBktStep_pos

theorem state_fbFindHeavyBktLoop (x : ((BpMetaCtx × ℕ) × (ℕ × ℕ)) × ℕ)
    (s : Memory.State) :
    (Memory.spec 0).clientState s (fbFindHeavyBktLoopProg x) = s := by
  rcases x with ⟨⟨d, acc⟩, fuel⟩
  unfold fbFindHeavyBktLoopProg
  induction fuel generalizing acc with
  | zero => rfl
  | succ f ih =>
    unfold iterate; rw [StateTransitionSpec.clientState_bind, state_fbFindHeavyBktStep]
    exact ih _

theorem fbFindHeavyBktLoop_spec {mp : BpMetaLayout} {tailLen : ℕ} {s : Memory.State}
    (hM : 1 ≤ mp.M) (hK : 1 ≤ mp.K)
    (htl_nc : tailLen ≤ mp.nCap) (htl_ge : mp.M * mp.K ≤ tailLen)
    (htl_8 : tailLen < 8 * mp.M * mp.K)
    (hown : ∀ t < tailLen, (extractFallback mp s.mem).ownerTail t < mp.M) :
    let bStar := ((Memory.spec 0).clientResult s
      (fbFindHeavyBktLoopProg (((mp.toCtx, tailLen), (0, 0)), mp.M))).2
    bStar < mp.M ∧
    mp.K ≤ ((Finset.range tailLen).filter
      (fun t => (extractFallback mp s.mem).ownerTail t = bStar)).card := by
  dsimp only
  set ot := (extractFallback mp s.mem).ownerTail
  obtain ⟨b₀, hb₀_lt, hb₀_cnt⟩ := FallbackState.exists_heavy_tail_bkt hM hK htl_ge hown
  have hloop : ∀ fuel b bStar,
      b + fuel = mp.M →
      ((bStar < mp.M ∧ mp.K ≤ ((Finset.range tailLen).filter (fun t => ot t = bStar)).card) ∨
        b ≤ b₀) →
      let r := (Memory.spec 0).clientResult s
        (iterate fbFindHeavyBktStepProg (mp.toCtx, tailLen) fuel (b, bStar))
      r.2 < mp.M ∧ mp.K ≤ ((Finset.range tailLen).filter (fun t => ot t = r.2)).card := by
    intro fuel; induction fuel with
    | zero =>
      intro b bStar hsum hor
      have hb : b = mp.M := by omega
      subst hb
      rcases hor with hok | hle
      · exact hok
      · omega
    | succ f ih =>
      intro b bStar hsum hor
      have hb_lt : b < mp.M := by omega
      have hcnt_b := fbCountBktLoop_spec (mp := mp) (b := b) (s := s) htl_nc htl_8
      have hres1 : (Memory.spec 0).clientResult s
          (fbFindHeavyBktStepProg ((mp.toCtx, tailLen), (b, bStar))) =
          if mp.K ≤ ((Finset.range tailLen).filter (fun t => ot t = b)).card then (b + 1, b)
          else (b + 1, bStar) := by
        unfold fbFindHeavyBktStepProg
        rw [prog_clientResult_bind, clientState_bpReadScalarProg]
        have hm : (match mp.toCtx with
            | (_, (((m, k), _), (_, nCap))) =>
              if b < m then
                if tailLen ≤ nCap then do
                  let z0 ← pure 0
                  let tc ← fbCountBktLoopProg ((((mp.toCtx, (tailLen, b)), (z0, z0))), tailLen)
                  if k ≤ tc.2 then pure (b + 1, b) else pure (b + 1, bStar)
                else pure (b, bStar)
              else pure (b, bStar)) =
            (if b < mp.M then
              if tailLen ≤ mp.nCap then do
                let z0 ← pure 0
                let tc ← fbCountBktLoopProg ((((mp.toCtx, (tailLen, b)), (z0, z0))), tailLen)
                if mp.K ≤ tc.2 then pure (b + 1, b) else pure (b + 1, bStar)
              else pure (b, bStar)
            else pure (b, bStar)) := rfl
        rw [hm, ite_eq_left hb_lt, ite_eq_left htl_nc]
        simp only [pure_bind, prog_clientResult_bind]
        rw [state_fbCountBktLoop, hcnt_b]; split_ifs <;> rfl
      unfold iterate
      rw [prog_clientResult_bind, state_fbFindHeavyBktStep, hres1]
      by_cases hge : mp.K ≤ ((Finset.range tailLen).filter (fun t => ot t = b)).card
      · rw [ite_eq_left hge]
        exact ih (b + 1) b (by omega) (Or.inl ⟨hb_lt, hge⟩)
      · rw [ite_eq_right hge]
        refine ih (b + 1) bStar (by omega) ?_
        rcases hor with hok | hle
        · exact Or.inl hok
        · have hne : b ≠ b₀ := fun heq => hge (heq ▸ hb₀_cnt)
          exact Or.inr (by omega)
  exact hloop mp.M 0 0 (Nat.zero_add _) (Or.inr (Nat.zero_le _))

/-- Read-only scan over `t ∈ [dst, tailLen)` finding `src ≥ dst` with `ownerTail src = bStar`. -/
private def fbFindMatchStepProg :
    (BpMetaCtx × (ℕ × ℕ)) × (ℕ × (ℕ × ℕ)) → Memory.Prog (ℕ × (ℕ × ℕ))
  | ((mctx, (tailLen, bStar)), (t, (found, src))) => do
    let _ ← bpReadScalarProg (mctx, 1)
    if t < tailLen then do
      let bt ← bpReadTailDirRawProg (mctx, t)
      if found = 0 ∧ bt = bStar then pure (t + 1, (1, t)) else pure (t + 1, (found, src))
    else pure (t, (found, src))

private theorem memoryCost_fbFindMatchStep_pos
    (x : (BpMetaCtx × (ℕ × ℕ)) × (ℕ × (ℕ × ℕ))) (s : Memory.State) :
    1 ≤ memoryCost (fbFindMatchStepProg x) s := by
  rcases x with ⟨⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨_, _⟩⟩⟩,
    ⟨_, _⟩⟩, ⟨_, ⟨_, _⟩⟩⟩
  simp [fbFindMatchStepProg, bpReadScalarProg]

private theorem state_fbFindMatchStep
    (x : (BpMetaCtx × (ℕ × ℕ)) × (ℕ × (ℕ × ℕ))) (s : Memory.State) :
    (Memory.spec 0).clientState s (fbFindMatchStepProg x) = s := by
  rcases x with ⟨⟨mctx, ⟨tailLen, bStar⟩⟩, ⟨t, ⟨found, src⟩⟩⟩
  unfold fbFindMatchStepProg
  rw [StateTransitionSpec.clientState_bind, clientState_bpReadScalarProg]
  split_ifs
  · rw [StateTransitionSpec.clientState_bind, clientState_bpReadTailDirRawProg]
    split_ifs <;> rfl
  · rfl

private theorem realizesBounded_fbFindMatchStep :
    RealizesBounded .exact fbFindMatchStepProg
      (WordEncoding.encode (α := (BpMetaCtx × (ℕ × ℕ)) × (ℕ × (ℕ × ℕ))))
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      (fun w ((mctx, _), _) s => (BpMetaLayout.ofCtx mctx).Valid w s.frontier)
      (fun _ _ => 0) := by
  have hrs := realizesBounded_bpReadScalar
  have hrtd := realizesBounded_bpReadTailDirRaw
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨⟨mb, obm⟩, ⟨osd, otd⟩⟩, ⟨⟨oso, oto⟩, ⟨pb, wv⟩⟩⟩,
      ⟨⟨⟨m, k⟩, ⟨ms, mbk⟩⟩, ⟨mt, nc⟩⟩⟩, ⟨tailLen, bStar⟩⟩, ⟨t, ⟨found, src⟩⟩⟩
    have hmv := h
    have hw := hmv.w_mach_pos
    have hw1 : 1 < 2 ^ w := Nat.one_lt_two_pow hw.ne'
    have htl_w : tailLen < 2 ^ w := hwords 14
    have ht_w : t < 2 ^ w := hwords 16
    have hf_w : found < 2 ^ w := hwords 17
    have hs_w : src < 2 ^ w := hwords 18
    dsimp only at *
    try dsimp only [Fits, StateTransitionSpec.clientState] at *
    try simp only [runClient_state_bpReadScalarProg] at *
    first | exact hmv | exact hw1 | omega)

/-- Bounded loop scanning `t ∈ [dst, tailLen)` for `ownerTail t = bStar`. -/
def fbFindMatchLoopProg :
    ((BpMetaCtx × (ℕ × ℕ)) × (ℕ × (ℕ × ℕ))) × ℕ → Memory.Prog (ℕ × (ℕ × ℕ))
  | ((d, acc), fuel) => iterate fbFindMatchStepProg d fuel acc

private theorem realizesBounded_fbFindMatchLoop :
    RealizesBounded .exact fbFindMatchLoopProg
      (WordEncoding.encode (α := ((BpMetaCtx × (ℕ × ℕ)) × (ℕ × (ℕ × ℕ))) × ℕ))
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      (fun w ((d, acc), fuel) s =>
        iterationSafe fbFindMatchStepProg
          (fun w' ((mctx, _), _) s' => (BpMetaLayout.ofCtx mctx).Valid w' s'.frontier)
          w d fuel acc s)
      (fun _ _ => 0) :=
  RealizesBounded.iterate₀
    (WordEncoding.encode (α := BpMetaCtx × (ℕ × ℕ)))
    (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
    realizesBounded_fbFindMatchStep
    memoryCost_fbFindMatchStep_pos

theorem state_fbFindMatchLoop
    (x : ((BpMetaCtx × (ℕ × ℕ)) × (ℕ × (ℕ × ℕ))) × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (fbFindMatchLoopProg x) = s := by
  rcases x with ⟨⟨d, acc⟩, fuel⟩
  unfold fbFindMatchLoopProg
  induction fuel generalizing acc with
  | zero => rfl
  | succ f ih =>
    unfold iterate; rw [StateTransitionSpec.clientState_bind, state_fbFindMatchStep]
    exact ih _

/-- Matched source slot `r.2.2` in an `fbFindMatchLoopProg` result `(cur, (found, src))`. -/
abbrev fbMatchResSrc (r : ℕ × (ℕ × ℕ)) : ℕ := r.2.2

theorem fbFindMatchLoop_spec {mp : BpMetaLayout} {tailLen bStar dst : ℕ} {s : Memory.State}
    (htl_8 : tailLen < 8 * mp.M * mp.K)
    (hdst_K : dst < mp.K) (hdst_tl : dst ≤ tailLen)
    (hcnt : mp.K ≤ ((Finset.range tailLen).filter
      (fun t => (extractFallback mp s.mem).ownerTail t = bStar)).card) :
    let res := (Memory.spec 0).clientResult s
      (fbFindMatchLoopProg (((mp.toCtx, (tailLen, bStar)), (dst, (0, dst))), tailLen - dst))
    let src := fbMatchResSrc res
    dst ≤ src ∧ src < tailLen ∧ (extractFallback mp s.mem).ownerTail src = bStar := by
  dsimp only
  set ot := (extractFallback mp s.mem).ownerTail
  have hex_match : ∃ j, dst ≤ j ∧ j < tailLen ∧ ot j = bStar := by
    by_contra hno
    push Not at hno
    have hsub : (Finset.range tailLen).filter (fun t => ot t = bStar) ⊆ Finset.range dst := by
      intro t ht
      obtain ⟨ht_lt, hot⟩ := mem_filter.mp ht
      rw [mem_range] at ht_lt ⊢
      by_contra hge
      exact hno t (Nat.le_of_not_lt hge) ht_lt hot
    have hle := (Finset.card_le_card hsub).trans (by simp : (Finset.range dst).card ≤ dst)
    omega
  obtain ⟨j₀, hj₀_ge, hj₀_lt, hj₀_eq⟩ := hex_match
  have hloop : ∀ fuel t found src,
      t + fuel = tailLen →
      dst ≤ t →
      found ≤ 1 →
      (found = 1 → dst ≤ src ∧ src < t ∧ ot src = bStar) →
      (found = 0 → t ≤ j₀) →
      let r := (Memory.spec 0).clientResult s
        (iterate fbFindMatchStepProg (mp.toCtx, (tailLen, bStar)) fuel (t, (found, src)))
      dst ≤ r.2.2 ∧ r.2.2 < tailLen ∧ ot r.2.2 = bStar := by
    intro fuel; induction fuel with
    | zero =>
      intro t found src hsum _ hfle hf1 hf0
      have ht : t = tailLen := by omega
      subst ht
      rcases (by omega : found = 0 ∨ found = 1) with rfl | rfl
      · have := hf0 rfl; omega
      · exact hf1 rfl
    | succ f ih =>
      intro t found src hsum ht_ge hfle hf1 hf0
      have ht_lt : t < tailLen := by omega
      have ht_8 : t < 8 * mp.M * mp.K := ht_lt.trans htl_8
      have hbt_r : (Memory.spec 0).clientResult s (bpReadTailDirRawProg (mp.toCtx, t)) = ot t := by
        unfold bpReadTailDirRawProg; dsimp only [BpMetaLayout.toCtx, ot, extractFallback]
        rw [ite_eq_left ht_8, ite_eq_left ht_8, clientResult_readPackedCompGenProg]
      have hres1 : (Memory.spec 0).clientResult s
          (fbFindMatchStepProg ((mp.toCtx, (tailLen, bStar)), (t, (found, src)))) =
          if found = 0 ∧ ot t = bStar then (t + 1, (1, t)) else (t + 1, (found, src)) := by
        unfold fbFindMatchStepProg
        rw [prog_clientResult_bind, clientState_bpReadScalarProg, ite_eq_left ht_lt,
          prog_clientResult_bind, clientState_bpReadTailDirRawProg, hbt_r]
        split_ifs <;> rfl
      unfold iterate; rw [prog_clientResult_bind, state_fbFindMatchStep, hres1]
      by_cases hhit : found = 0 ∧ ot t = bStar
      · rw [ite_eq_left hhit]
        exact ih (t + 1) 1 t (by omega) (by omega) le_rfl
          (fun _ => ⟨ht_ge, Nat.lt_succ_self t, hhit.2⟩) (fun hc => absurd hc Nat.one_ne_zero)
      · rw [ite_eq_right hhit]
        refine ih (t + 1) found src (by omega) (by omega) hfle
          (fun hf => by obtain ⟨h1, h2, h3⟩ := hf1 hf; exact ⟨h1, Nat.lt_succ_of_lt h2, h3⟩)
          (fun hf => ?_)
        have hle := hf0 hf
        have hne : t ≠ j₀ := fun heq => hhit ⟨hf, heq ▸ hj₀_eq⟩
        omega
  exact hloop (tailLen - dst) dst 0 dst (by omega) le_rfl (Nat.zero_le _)
    (fun hc => absurd hc Nat.zero_ne_one) (fun _ => hj₀_ge)

/-- Read `(ownerTail t₁, ownerTail t₂)` (`≤ 2` binds, instant `realize`). -/
private def fbReadTailPairProg : BpMetaCtx × (ℕ × ℕ) → Memory.Prog (ℕ × ℕ)
  | (mctx, (t₁, t₂)) => do
    let b₁ ← bpReadTailDirRawProg (mctx, t₁)
    let b₂ ← bpReadTailDirRawProg (mctx, t₂)
    pure (b₁, b₂)

private theorem state_fbReadTailPairProg (x : BpMetaCtx × (ℕ × ℕ)) (s : Memory.State) :
    (Memory.spec 0).clientState s (fbReadTailPairProg x) = s := by
  rcases x with ⟨mctx, ⟨t₁, t₂⟩⟩
  unfold fbReadTailPairProg
  rw [StateTransitionSpec.clientState_bind, clientState_bpReadTailDirRawProg,
    StateTransitionSpec.clientState_bind, clientState_bpReadTailDirRawProg]
  rfl

private theorem realizesBounded_fbReadTailPair :
    RealizesBounded .exact fbReadTailPairProg
      (WordEncoding.encode (α := BpMetaCtx × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w (mctx, _) s => (BpMetaLayout.ofCtx mctx).Valid w s.frontier)
      (fun _ _ => 0) := by
  have hrtd := realizesBounded_bpReadTailDirRaw
  realize
  all_goals (
    rcases d with ⟨mctx, ⟨t₁, t₂⟩⟩
    have hmv := h
    try dsimp only [Fits, StateTransitionSpec.clientState] at *
    try simp only [runClient_state_bpReadTailDirRawProg] at *
    exact hmv)

/-- Write `(b₂, b₁)` to `ownerTail[t₁]` and `ownerTail[t₂]` (`≤ 2` binds, instant `realize`). -/
private def fbWriteTailPairProg : (BpMetaCtx × (ℕ × ℕ)) × (ℕ × ℕ) → Memory.Prog Unit
  | ((mctx, (t₁, t₂)), (b₁, b₂)) => do
    bpWriteTailDirRawProg ((mctx, t₁), b₂)
    bpWriteTailDirRawProg ((mctx, t₂), b₁)

private theorem frontier_fbWriteTailPairProg
    (x : (BpMetaCtx × (ℕ × ℕ)) × (ℕ × ℕ)) (s : Memory.State) :
    ((Memory.spec 0).clientState s (fbWriteTailPairProg x)).frontier = s.frontier := by
  rcases x with ⟨⟨mctx, ⟨t₁, t₂⟩⟩, ⟨b₁, b₂⟩⟩
  unfold fbWriteTailPairProg
  rw [StateTransitionSpec.clientState_bind, frontier_bpWriteTailDirRawProg,
    frontier_bpWriteTailDirRawProg]

private theorem realizesBounded_fbWriteTailPair :
    RealizesBounded .exact fbWriteTailPairProg
      (WordEncoding.encode (α := (BpMetaCtx × (ℕ × ℕ)) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w ((mctx, _), _) s => (BpMetaLayout.ofCtx mctx).Valid w s.frontier)
      (fun _ _ => 0) := by
  have hwtd := realizesBounded_bpWriteTailDirRaw
  realize
  all_goals (
    rcases d with ⟨⟨mctx, ⟨t₁, t₂⟩⟩, ⟨b₁, b₂⟩⟩
    have hmv := h
    try dsimp only [Fits, StateTransitionSpec.clientState] at *
    try simp only [runClient_frontier_bpWriteTailDirRawProg] at *
    exact hmv)

/-- Swap two tail offsets `t₁, t₂` simultaneously in `ioctx` (at `fbBase + t₁`, `fbBase + t₂`)
and in `ownerTail` (`offTailDir[t₁]`, `offTailDir[t₂]`). -/
def fbSwapTailSlotsProg : (BlockPoolCtx × ℕ) × (ℕ × ℕ) → Memory.Prog Unit
  | (((mctx, ioctx), fbBase), (t₁, t₂)) => do
    let (_, (_, (_, nCap))) := mctx
    if t₁ < nCap then
      if t₂ < nCap then
        if fbBase < nCap - t₁ then
          if fbBase < nCap - t₂ then do
            let bs ← fbReadTailPairProg (mctx, (t₁, t₂))
            slotIoSwapRawProg (ioctx, (fbBase + t₁, fbBase + t₂))
            fbWriteTailPairProg ((mctx, (t₁, t₂)), bs)
          else pure ()
        else pure ()
      else pure ()
    else pure ()

theorem frontier_fbSwapTailSlotsProg (d : BlockPoolCtx × ℕ) (t₁ t₂ : ℕ) (s : Memory.State)
    (hw : 0 < (SlotIoLayout.ofCtx (bpCtxIo d)).pgL.w) :
    ((Memory.spec 0).clientState s (fbSwapTailSlotsProg (d, (t₁, t₂)))).frontier = s.frontier := by
  rcases d with ⟨⟨⟨p1, ⟨p2, ⟨mt, nCap⟩⟩⟩, ioctx⟩, fbBase⟩
  unfold fbSwapTailSlotsProg; dsimp only
  split_ifs
  · rw [StateTransitionSpec.clientState_bind, state_fbReadTailPairProg,
      StateTransitionSpec.clientState_bind, frontier_fbWriteTailPairProg]
    have hswf := (slotIoSwapProg_frame (io := SlotIoLayout.ofCtx ioctx) hw
      (fbBase + t₁) (fbBase + t₂)).frontier_eq s
    unfold slotIoSwapProg at hswf; rw [SlotIoLayout.toCtx_ofCtx] at hswf
    exact hswf
  all_goals rfl

theorem realizesBounded_fbSwapTailSlots :
    RealizesBounded .exact fbSwapTailSlotsProg
      (WordEncoding.encode (α := (BlockPoolCtx × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w (((mctx, ioctx), _), _) s =>
        (BpMetaLayout.ofCtx mctx).Valid w s.frontier ∧
        (SlotIoLayout.ofCtx ioctx).Valid w s.frontier)
      (fun _ _ => 0) := by
  have hrp := realizesBounded_fbReadTailPair
  have hsw := realizesBounded_slotIoSwapRaw
  have hwp := realizesBounded_fbWriteTailPair
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨⟨⟨mb, obm⟩, ⟨osd, otd⟩⟩, ⟨⟨oso, oto⟩, ⟨pb, wv⟩⟩⟩,
      ⟨⟨⟨m, k⟩, ⟨ms, mbk⟩⟩, ⟨mt, nc⟩⟩⟩, ioctx⟩, fbBase⟩, ⟨t₁, t₂⟩⟩
    obtain ⟨hmv, hiov⟩ := h
    have hnc_w := hmv.nCap_lt_two_pow_w
    have hfb_w : fbBase < 2 ^ w := hwords 27
    have ht1_w : t₁ < 2 ^ w := hwords 28
    have ht2_w : t₂ < 2 ^ w := hwords 29
    let mctx : BpMetaCtx := ((((mb, obm), (osd, otd)), ((oso, oto), (pb, wv))),
      (((m, k), (ms, mbk)), (mt, nc)))
    have hrp_s : ((Memory.spec 0).runClient s (fbReadTailPairProg (mctx, (t₁, t₂)))).2.1 = s :=
      state_fbReadTailPairProg _ s
    dsimp only [BpMetaLayout.ofCtx] at hnc_w
    dsimp only [mctx] at hrp_s
    try dsimp only at *
    try simp only [Prod.mk.eta] at *
    try dsimp only [Fits, StateTransitionSpec.clientState] at *
    try rw [hrp_s]
    first | exact hmv | exact hiov | omega | (
      have hswf := (slotIoSwapProg_frame (io := SlotIoLayout.ofCtx ioctx) hiov.w_pos
        (fbBase + t₁) (fbBase + t₂)).frontier_eq s
      unfold slotIoSwapProg at hswf; rw [SlotIoLayout.toCtx_ofCtx] at hswf
      dsimp only [StateTransitionSpec.clientState] at hswf
      rw [hswf]; exact hmv))

theorem fbSwapTailSlotsProg_spec {mp : BpMetaLayout} {io : SlotIoLayout}
    {w slack maxT t₁ t₂ : ℕ} {s : Memory.State}
    (hmv : mp.Valid w s.frontier) (hiov : io.Valid io.pgL.w s.frontier)
    (hdisj : ∀ addr, mp.OwnsMetaAddr addr → io.OwnsAddr addr → False)
    (hfb : (extractFallback mp s.mem).ValidWith maxT)
    (hmaxT : maxT < 8 * mp.M * mp.K)
    (hns_le : (extractFallback mp s.mem).nSide ≤ mp.nCap)
    (hio : io.StateInv (extractFallback mp s.mem).nSide slack s.mem)
    (ht₁ : t₁ < (extractFallback mp s.mem).tailLen)
    (ht₂ : t₂ < (extractFallback mp s.mem).tailLen) :
    let fb := extractFallback mp s.mem
    let fbBase := fb.fullBlocks * mp.K
    let s' := (Memory.spec 0).clientState s
      (fbSwapTailSlotsProg (((mp.toCtx, io.toCtx), fbBase), (t₁, t₂)))
    s'.frontier = s.frontier ∧
    extractFallback mp s'.mem =
      { fb with ownerTail := (PhysSwap.mk t₁ t₂).apply fb.ownerTail } ∧
    io.StateInv fb.nSide slack s'.mem ∧
    (∀ p < fb.nSide, slotIoPairAt io s'.mem p =
      (PhysSwap.mk (fbBase + t₁) (fbBase + t₂)).apply (slotIoPairAt io s.mem) p) ∧
    (∀ addr, ¬(mp.OwnsMetaAddr addr ∨ io.OwnsAddr addr) → s'.mem addr = s.mem addr) ∧
    (io.usePaged ≠ 0 →
      extractPageUnperm io.pgL s'.mem = extractPageUnperm io.pgL s.mem ∧
      ∀ idx < (extractPagePair io.pgL s.mem).virtLen io.partner.side,
        slotIoPairAt io.partner s'.mem idx = slotIoPairAt io.partner s.mem idx) := by
  dsimp only
  set fb := extractFallback mp s.mem
  set fbBase := fb.fullBlocks * mp.K
  have hfb_K : fb.K = mp.K := rfl
  have hfb_M : fb.M = mp.M := rfl
  have ht1_8 : t₁ < 8 * mp.M * mp.K := ht₁.trans (lt_of_le_of_lt hfb.tail_le hmaxT)
  have ht2_8 : t₂ < 8 * mp.M * mp.K := ht₂.trans (lt_of_le_of_lt hfb.tail_le hmaxT)
  have hp1_ns : fbBase + t₁ < fb.nSide := by
    unfold FallbackState.tailLen at ht₁; rw [hfb_K] at ht₁; omega
  have hp2_ns : fbBase + t₂ < fb.nSide := by
    unfold FallbackState.tailLen at ht₂; rw [hfb_K] at ht₂; omega
  have ht1_nc : t₁ < mp.nCap := by omega
  have ht2_nc : t₁ < mp.nCap ∧ t₂ < mp.nCap := ⟨ht1_nc, by omega⟩
  have hfb1_nc : fbBase < mp.nCap - t₁ := by omega
  have hfb2_nc : fbBase < mp.nCap - t₂ := by omega
  have hb1_lt_M : fb.ownerTail t₁ < mp.M := hfb_M ▸ hfb.tail_lt t₁ ht₁
  have hb2_lt_M : fb.ownerTail t₂ < mp.M := hfb_M ▸ hfb.tail_lt t₂ ht₂
  have hM_nc : mp.M ≤ mp.nCap := by have := hmv.sixteen_M_le; omega
  have hb1_nc : fb.ownerTail t₁ ≤ mp.nCap := hb1_lt_M.le.trans hM_nc
  have hb2_nc : fb.ownerTail t₂ ≤ mp.nCap := hb2_lt_M.le.trans hM_nc
  have hb1_pb : fb.ownerTail t₁ < 2 ^ mp.ptrB := lt_of_le_of_lt hb1_nc hmv.nCap_lt_ptrB
  have hb2_pb : fb.ownerTail t₂ < 2 ^ mp.ptrB := lt_of_le_of_lt hb2_nc hmv.nCap_lt_ptrB
  have hrp_res : (Memory.spec 0).clientResult s (fbReadTailPairProg (mp.toCtx, (t₁, t₂))) =
      (fb.ownerTail t₁, fb.ownerTail t₂) := by
    unfold fbReadTailPairProg
    rw [prog_clientResult_bind, clientState_bpReadTailDirRawProg]
    have hr1 : (Memory.spec 0).clientResult s (bpReadTailDirRawProg (mp.toCtx, t₁)) =
        fb.ownerTail t₁ := by
      unfold bpReadTailDirRawProg; dsimp only [BpMetaLayout.toCtx, fb, extractFallback]
      rw [ite_eq_left ht1_8, ite_eq_left ht1_8, clientResult_readPackedCompGenProg]
    have hr2 : (Memory.spec 0).clientResult s (bpReadTailDirRawProg (mp.toCtx, t₂)) =
        fb.ownerTail t₂ := by
      unfold bpReadTailDirRawProg; dsimp only [BpMetaLayout.toCtx, fb, extractFallback]
      rw [ite_eq_left ht2_8, ite_eq_left ht2_8, clientResult_readPackedCompGenProg]
    rw [hr1, prog_clientResult_bind, clientState_bpReadTailDirRawProg, hr2, prog_clientResult_pure]
  obtain ⟨hio₁, harr₁, hpart₁⟩ := slotIoSwapProg_spec hiov hio hp1_ns hp2_ns
  have hswf := slotIoSwapProg_frame (io := io) hiov.w_pos (fbBase + t₁) (fbBase + t₂)
  unfold slotIoSwapProg at hio₁ harr₁ hpart₁ hswf
  set s₁ := (Memory.spec 0).clientState s (slotIoSwapRawProg (io.toCtx, (fbBase + t₁, fbBase + t₂)))
  set s₂ := (Memory.spec 0).clientState s₁ (bpWriteTailDirRawProg ((mp.toCtx, t₁), fb.ownerTail t₂))
  set s₃ := (Memory.spec 0).clientState s₂ (bpWriteTailDirRawProg ((mp.toCtx, t₂), fb.ownerTail t₁))
  have hst_eq : (Memory.spec 0).clientState s
      (fbSwapTailSlotsProg (((mp.toCtx, io.toCtx), fbBase), (t₁, t₂))) = s₃ := by
    unfold fbSwapTailSlotsProg; dsimp only
    have hnc_eq : mp.toCtx.2.2.2 = mp.nCap := rfl
    rw [hnc_eq, ite_eq_left ht2_nc.1, ite_eq_left ht2_nc.2, ite_eq_left hfb1_nc,
      ite_eq_left hfb2_nc, StateTransitionSpec.clientState_bind, state_fbReadTailPairProg,
      hrp_res, StateTransitionSpec.clientState_bind]
    unfold fbWriteTailPairProg
    rw [StateTransitionSpec.clientState_bind]
  rw [hst_eq]
  have hotd_ge : mp.offBktMeta + packedWords (16 * mp.M) mp.ptrB mp.w ≤ mp.offTailDir := by
    have := hmv.offSlabDir_ge; have := hmv.offTailDir_ge; omega
  have hwf1 := bpWriteTailDirRawProg_frame hmv.w_pos hotd_ge t₁ (fb.ownerTail t₂)
  have hwf2 := bpWriteTailDirRawProg_frame hmv.w_pos hotd_ge t₂ (fb.ownerTail t₁)
  have hfb₁ : extractFallback mp s₁.mem = fb :=
    extractFallback_congr hmv.w_pos fun a hma =>
      hswf.mem_outside s a (fun hia => hdisj a hma hia)
  have hfb₂ := extractFallback_writeOwnerTail (hswf.frontier_eq s ▸ hmv) ht1_8 hb2_pb hb2_nc
    (s := s₁)
  have hfb₃ := extractFallback_writeOwnerTail
    ((hwf1.1.frontier_eq s₁).trans (hswf.frontier_eq s) ▸ hmv) ht2_8 hb1_pb hb1_nc (s := s₂)
  rw [hfb₁] at hfb₂; rw [hfb₂] at hfb₃
  have hot_eq : Function.update (Function.update fb.ownerTail t₁ (fb.ownerTail t₂)) t₂
      (fb.ownerTail t₁) = (PhysSwap.mk t₁ t₂).apply fb.ownerTail := by
    let sw : PhysSwap := ⟨t₁, t₂⟩
    ext x
    by_cases hx2 : x = t₂
    · subst hx2
      by_cases hx1 : x = t₁
      · subst hx1; rw [Function.update_self, sw.apply_p₁]
      · rw [Function.update_self, sw.apply_p₂]
    · rw [Function.update_of_ne hx2]
      by_cases hx1 : x = t₁
      · subst hx1; rw [Function.update_self, sw.apply_p₁]
      · rw [Function.update_of_ne hx1, sw.apply_of_ne _ hx1 hx2]
  have hio_out : ∀ addr, io.OwnsAddr addr → s₃.mem addr = s₁.mem addr := fun addr hia =>
    (hwf2.1.mem_outside s₂ addr (fun hma => hdisj addr hma hia)).trans
      (hwf1.1.mem_outside s₁ addr (fun hma => hdisj addr hma hia))
  obtain ⟨hio₃, harr₃⟩ := io.congr_of_outside hiov.w_pos hio₁ hio_out
  refine ⟨(hwf2.1.frontier_eq s₂).trans ((hwf1.1.frontier_eq s₁).trans (hswf.frontier_eq s)),
    by rw [hfb₃, hot_eq], hio₃, fun p hp => (harr₃ p hp).trans (harr₁ p hp),
    fun addr ha => ?_, fun hnz => ?_⟩
  · exact (hwf2.1.mem_outside s₂ addr (fun hma => ha (Or.inl hma))).trans
      ((hwf1.1.mem_outside s₁ addr (fun hma => ha (Or.inl hma))).trans
        (hswf.mem_outside s addr (fun hia => ha (Or.inr hia))))
  · obtain ⟨hu₁, hp₁⟩ := hpart₁ hnz
    have hown_pg : ∀ addr, io.pgL.OwnsAddr addr → s₃.mem addr = s₁.mem addr := fun addr ha => by
      apply hio_out addr; unfold SlotIoLayout.OwnsAddr; rwa [ite_eq_right hnz]
    have hu₃ : extractPageUnperm io.pgL s₃.mem = extractPageUnperm io.pgL s₁.mem :=
      extractPageUnperm_congr hiov.w_pos (fun a ha => hown_pg a (Or.inl ha))
    refine ⟨hu₃.trans hu₁, fun idx hidx => ?_⟩
    unfold SlotIoLayout.StateInv at hio₁; rw [ite_eq_right hnz] at hio₁
    have hidx₁ : idx < (extractPagePair io.pgL s₁.mem).virtLen io.partner.side := by
      have : extractPagePair io.pgL s₁.mem = extractPagePair io.pgL s.mem :=
        congrArg PageUnpermState.st hu₁
      rwa [this]
    have hp_lt₁ : (extractPageUnperm io.pgL s₁.mem).toPhys io.partner.side idx < io.pgL.nCap :=
      (hio₁.1.toPhys_lt hidx₁).trans_le hio₁.2.2.2.1
    have hp₃ : slotIoPairAt io.partner s₃.mem idx = slotIoPairAt io.partner s₁.mem idx := by
      unfold slotIoPairAt
      have hp_nz : io.partner.usePaged ≠ 0 := hnz
      rw [ite_eq_right hp_nz, ite_eq_right hp_nz, SlotIoLayout.partner_pgL, hu₃]
      exact arenaPairAt_congr hiov.w_pos (fun a ha => hown_pg a (Or.inr ha)) hp_lt₁
    exact hp₃.trans (hp₁ idx hidx)

/-- Outer step partitioning the `dst`-th occurrence of `bStar` to `ownerTail[dst]`. -/
def fbPartHeavyStepProg :
    (BlockPoolCtx × (ℕ × (ℕ × ℕ))) × ℕ → Memory.Prog ℕ
  | (((mctx, ioctx), (fbBase, (tailLen, bStar))), dst) => do
    let _ ← bpReadScalarProg (mctx, 1)
    if dst < tailLen then do
      let z0 ← pure 0
      let r ← fbFindMatchLoopProg ((((mctx, (tailLen, bStar)), (dst, (z0, dst)))), tailLen - dst)
      fbSwapTailSlotsProg (((mctx, ioctx), fbBase), (dst, fbMatchResSrc r))
      pure (dst + 1)
    else
      pure dst

private theorem memoryCost_fbPartHeavyStep_pos
    (x : (BlockPoolCtx × (ℕ × (ℕ × ℕ))) × ℕ) (s : Memory.State) :
    1 ≤ memoryCost (fbPartHeavyStepProg x) s := by
  rcases x with ⟨⟨⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨_, _⟩⟩⟩, _⟩,
    ⟨_, ⟨_, _⟩⟩⟩, _⟩
  simp [fbPartHeavyStepProg, bpReadScalarProg]

private theorem frontier_fbPartHeavyStep (d : BlockPoolCtx × (ℕ × (ℕ × ℕ))) (dst : ℕ)
    (s : Memory.State) (hw : 0 < (SlotIoLayout.ofCtx d.1.2).pgL.w) :
    ((Memory.spec 0).clientState s (fbPartHeavyStepProg (d, dst))).frontier = s.frontier := by
  rcases d with ⟨⟨mctx, ioctx⟩, ⟨fbBase, ⟨tailLen, bStar⟩⟩⟩
  unfold fbPartHeavyStepProg
  rw [StateTransitionSpec.clientState_bind, clientState_bpReadScalarProg]
  split_ifs
  · simp only [pure_bind]
    rw [StateTransitionSpec.clientState_bind, state_fbFindMatchLoop,
      StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_pure]
    exact frontier_fbSwapTailSlotsProg ((mctx, ioctx), fbBase) _ _ s hw
  · rfl

private theorem realizesBounded_fbPartHeavyStep :
    RealizesBounded .exact fbPartHeavyStepProg
      (WordEncoding.encode (α := (BlockPoolCtx × (ℕ × (ℕ × ℕ))) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w (((mctx, ioctx), _), _) s =>
        (BpMetaLayout.ofCtx mctx).Valid w s.frontier ∧
        (SlotIoLayout.ofCtx ioctx).Valid w s.frontier)
      (fun _ _ => 0) := by
  have hrs := realizesBounded_bpReadScalar
  have hfm := realizesBounded_fbFindMatchLoop
  have hsw := realizesBounded_fbSwapTailSlots
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨⟨⟨mb, obm⟩, ⟨osd, otd⟩⟩, ⟨⟨oso, oto⟩, ⟨pb, wv⟩⟩⟩,
      ⟨⟨⟨m, k⟩, ⟨ms, mbk⟩⟩, ⟨mt, nc⟩⟩⟩, ioctx⟩, ⟨fbBase, ⟨tailLen, bStar⟩⟩⟩, dst⟩
    obtain ⟨hmv, hiov⟩ := h
    have hw := hmv.w_mach_pos
    have hw1 : 1 < 2 ^ w := Nat.one_lt_two_pow hw.ne'
    have htl_w : tailLen < 2 ^ w := hwords 28
    have hd_w : dst < 2 ^ w := hwords 30
    let mctx : BpMetaCtx := ((((mb, obm), (osd, otd)), ((oso, oto), (pb, wv))),
      (((m, k), (ms, mbk)), (mt, nc)))
    have hfm_s : ((Memory.spec 0).runClient s
        (fbFindMatchLoopProg
          ((((mctx, (tailLen, bStar)), (dst, (0, dst)))), tailLen - dst))).2.1 = s :=
      state_fbFindMatchLoop _ s
    dsimp only [mctx] at hfm_s
    try dsimp only at *
    try simp only [runClient_state_bpReadScalarProg, Prod.mk.eta] at *
    try dsimp only [Fits, StateTransitionSpec.clientState] at *
    try rw [hfm_s]
    first | exact hmv | exact hiov | exact hw1 | omega | (
      exact (iterationSafe_of_frontier fbFindMatchStepProg
        (fun w' (d' : BpMetaCtx × (ℕ × ℕ)) fr' => (BpMetaLayout.ofCtx d'.1).Valid w' fr')
        (fun d' a' s' _ => congrArg Memory.State.frontier (state_fbFindMatchStep (d', a') s'))
        (d := (mctx, (tailLen, bStar))) (s := s) hmv (tailLen - dst) (dst, (0, dst))).1))

/-- Outer partition loop moving `K` tail occurrences of `bStar` to `0..K - 1`. -/
def fbPartHeavyLoopProg :
    ((BlockPoolCtx × (ℕ × (ℕ × ℕ))) × ℕ) × ℕ → Memory.Prog ℕ
  | ((d, dst), fuel) => iterate fbPartHeavyStepProg d fuel dst

private theorem realizesBounded_fbPartHeavyLoop :
    RealizesBounded .exact fbPartHeavyLoopProg
      (WordEncoding.encode (α := ((BlockPoolCtx × (ℕ × (ℕ × ℕ))) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w ((d, dst), fuel) s =>
        iterationSafe fbPartHeavyStepProg
          (fun w' (((mctx, ioctx), _), _) s' =>
            (BpMetaLayout.ofCtx mctx).Valid w' s'.frontier ∧
            (SlotIoLayout.ofCtx ioctx).Valid w' s'.frontier) w d fuel dst s)
      (fun _ _ => 0) :=
  RealizesBounded.iterate₀
    (WordEncoding.encode (α := BlockPoolCtx × (ℕ × (ℕ × ℕ))))
    (WordEncoding.encode (α := ℕ))
    realizesBounded_fbPartHeavyStep
    memoryCost_fbPartHeavyStep_pos

/-- Left-shift `ownerTail` by `k` slots (`ownerTail'[t] := ownerTail[t + k]`). -/
def fbShiftLeftStepProg : (BpMetaCtx × ℕ) × ℕ → Memory.Prog ℕ
  | ((mctx, k), t) => do
    let _ ← bpReadScalarProg (mctx, 1)
    let (_, (_, (_, nCap))) := mctx
    if t < nCap then
      if k ≤ nCap - t then do
        let v ← bpReadTailDirRawProg (mctx, t + k)
        bpWriteTailDirRawProg ((mctx, t), v)
        pure (t + 1)
      else pure t
    else pure t

private theorem memoryCost_fbShiftLeftStep_pos (x : (BpMetaCtx × ℕ) × ℕ) (s : Memory.State) :
    1 ≤ memoryCost (fbShiftLeftStepProg x) s := by
  rcases x with ⟨⟨⟨⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩, ⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨_, _⟩⟩⟩, _⟩, _⟩
  simp [fbShiftLeftStepProg, bpReadScalarProg]

private theorem frontier_fbShiftLeftStep (d : BpMetaCtx × ℕ) (t : ℕ) (s : Memory.State) :
    ((Memory.spec 0).clientState s (fbShiftLeftStepProg (d, t))).frontier = s.frontier := by
  rcases d with ⟨⟨p1, ⟨p2, ⟨mt, nCap⟩⟩⟩, k⟩
  unfold fbShiftLeftStepProg
  rw [StateTransitionSpec.clientState_bind, clientState_bpReadScalarProg]; dsimp only
  split_ifs
  · rw [StateTransitionSpec.clientState_bind, clientState_bpReadTailDirRawProg,
      StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_pure,
      frontier_bpWriteTailDirRawProg]
  all_goals rfl

private theorem realizesBounded_fbShiftLeftStep :
    RealizesBounded .exact fbShiftLeftStepProg
      (WordEncoding.encode (α := (BpMetaCtx × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w ((mctx, _), _) s => (BpMetaLayout.ofCtx mctx).Valid w s.frontier)
      (fun _ _ => 0) := by
  have hrs := realizesBounded_bpReadScalar
  have hrtd := realizesBounded_bpReadTailDirRaw
  have hwtd := realizesBounded_bpWriteTailDirRaw
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨⟨mb, obm⟩, ⟨osd, otd⟩⟩, ⟨⟨oso, oto⟩, ⟨pb, wv⟩⟩⟩,
      ⟨⟨⟨m, k⟩, ⟨ms, mbk⟩⟩, ⟨mt, nc⟩⟩⟩, k_sh⟩, t⟩
    have hmv := h
    have hw := hmv.w_mach_pos
    have hw1 : 1 < 2 ^ w := Nat.one_lt_two_pow hw.ne'
    have hnc_w := hmv.nCap_lt_two_pow_w
    have hk_w : k_sh < 2 ^ w := hwords 14
    have ht_w : t < 2 ^ w := hwords 15
    dsimp only [BpMetaLayout.ofCtx] at hnc_w
    dsimp only at *
    try dsimp only [Fits, StateTransitionSpec.clientState] at *
    try simp only [runClient_state_bpReadScalarProg, runClient_state_bpReadTailDirRawProg] at *
    first | exact hmv | exact hw1 | omega)

/-- Bounded loop shifting `ownerTail` left by `K` positions after promotion. -/
def fbShiftLeftLoopProg : ((BpMetaCtx × ℕ) × ℕ) × ℕ → Memory.Prog ℕ
  | ((d, t), fuel) => iterate fbShiftLeftStepProg d fuel t

private theorem realizesBounded_fbShiftLeftLoop :
    RealizesBounded .exact fbShiftLeftLoopProg
      (WordEncoding.encode (α := ((BpMetaCtx × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w ((d, t), fuel) s =>
        iterationSafe fbShiftLeftStepProg
          (fun w' ((mctx, _), _) s' => (BpMetaLayout.ofCtx mctx).Valid w' s'.frontier)
          w d fuel t s)
      (fun _ _ => 0) :=
  RealizesBounded.iterate₀
    (WordEncoding.encode (α := BpMetaCtx × ℕ))
    (WordEncoding.encode (α := ℕ))
    realizesBounded_fbShiftLeftStep
    memoryCost_fbShiftLeftStep_pos

/-- Finish promotion after partitioning `bStar`: write `ownerBlk[fb0] := bStar`, shift left by `K`,
and set `fullBlocks := fb0 + 1` (`≤ 3` binds). -/
def fbPromoteFinishProg : (BpMetaCtx × (ℕ × ℕ)) × ℕ → Memory.Prog Unit
  | ((mctx, (fb0, tailLen)), bStar) => do
    let (_, (((_, k), _), (_, nCap))) := mctx
    if fb0 < nCap then
      if k ≤ tailLen then do
        bpWriteSlabOwnerProg ((mctx, (fb0, 1)), bStar)
        let z0 ← pure 0
        let _ ← fbShiftLeftLoopProg ((((mctx, k), z0)), tailLen - k)
        bpWriteScalarProg ((mctx, 10), fb0 + 1)
      else pure ()
    else pure ()

private theorem frontier_fbPromoteFinishProg
    (x : (BpMetaCtx × (ℕ × ℕ)) × ℕ) (s : Memory.State) :
    ((Memory.spec 0).clientState s (fbPromoteFinishProg x)).frontier = s.frontier := by
  rcases x with ⟨⟨⟨p1, ⟨⟨⟨m, k⟩, p2b⟩, ⟨mt, nCap⟩⟩⟩, ⟨fb0, tailLen⟩⟩, bStar⟩
  set mctx : BpMetaCtx := (p1, (((m, k), p2b), (mt, nCap)))
  unfold fbPromoteFinishProg; dsimp only
  split_ifs
  · simp only [pure_bind]
    rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
      frontier_bpWriteScalarProg]
    set s_so := (Memory.spec 0).clientState s (bpWriteSlabOwnerProg ((mctx, (fb0, 1)), bStar))
    have hfr_sh := (iterationSafe_of_frontier fbShiftLeftStepProg
      (fun _ _ _ => True) (w := 0) (fun d' a' st _ => frontier_fbShiftLeftStep d' a' st)
      (d := (mctx, k)) (s := s_so) trivial (tailLen - k) 0).2
    exact hfr_sh.trans (frontier_bpWriteSlabOwnerProg _ s)
  all_goals rfl

private theorem realizesBounded_fbPromoteFinish :
    RealizesBounded .exact fbPromoteFinishProg
      (WordEncoding.encode (α := (BpMetaCtx × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((mctx, _), _) s => (BpMetaLayout.ofCtx mctx).Valid w s.frontier)
      (fun _ _ => 0) := by
  have hwso := realizesBounded_bpWriteSlabOwner
  have hshl := realizesBounded_fbShiftLeftLoop
  have hws := realizesBounded_bpWriteScalar
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨⟨mb, obm⟩, ⟨osd, otd⟩⟩, ⟨⟨oso, oto⟩, ⟨pb, wv⟩⟩⟩,
      ⟨⟨⟨m, k⟩, ⟨ms, mbk⟩⟩, ⟨mt, nc⟩⟩⟩, ⟨fb0, tailLen⟩⟩, bStar⟩
    have hmv := h
    have hw := hmv.w_mach_pos
    have hw1 : 1 < 2 ^ w := Nat.one_lt_two_pow hw.ne'
    have hnc_w := hmv.nCap_lt_two_pow_w
    have h10_w : 10 < 2 ^ w := lt_of_le_of_lt
      (by have := hmv.K_ge; have := hmv.twelve_K_le; dsimp only [BpMetaLayout.ofCtx] at *; omega)
      hnc_w
    have htl_w : tailLen < 2 ^ w := hwords 15
    let mctx : BpMetaCtx := ((((mb, obm), (osd, otd)), ((oso, oto), (pb, wv))),
      (((m, k), (ms, mbk)), (mt, nc)))
    dsimp only [BpMetaLayout.ofCtx] at hnc_w
    dsimp only at *
    try dsimp only [Fits, StateTransitionSpec.clientState] at *
    first | exact hmv | exact hw1 | exact h10_w | omega | (
      set s_so := ((Memory.spec 0).runClient s
        (bpWriteSlabOwnerProg ((mctx, (fb0, 1)), bStar))).2.1
      have hfr_so : s_so.frontier = s.frontier :=
        runClient_frontier_bpWriteSlabOwnerProg _ s
      exact (iterationSafe_of_frontier fbShiftLeftStepProg
        (fun w' (d' : BpMetaCtx × ℕ) fr' => (BpMetaLayout.ofCtx d'.1).Valid w' fr')
        (fun d' a' st _ => frontier_fbShiftLeftStep d' a' st)
        (d := (mctx, k)) (s := s_so) (hfr_so.symm ▸ hmv) (tailLen - k) 0).1) | (
      set s_so := ((Memory.spec 0).runClient s
        (bpWriteSlabOwnerProg ((mctx, (fb0, 1)), bStar))).2.1
      have hfr_so : s_so.frontier = s.frontier :=
        runClient_frontier_bpWriteSlabOwnerProg _ s
      have hfr_sh := (iterationSafe_of_frontier fbShiftLeftStepProg
        (fun _ _ _ => True) (w := 0) (fun d' a' st _ => frontier_fbShiftLeftStep d' a' st)
        (d := (mctx, k)) (s := s_so) trivial (tailLen - k) 0).2
      unfold fbShiftLeftLoopProg; dsimp only [StateTransitionSpec.clientState] at hfr_sh ⊢
      rw [hfr_sh, hfr_so]; exact hmv))

/-- Core promotion body given `(fb0, fbBase, tailLen)` (`3` binds). -/
def fbPromoteBodyProg : (BlockPoolCtx × (ℕ × ℕ)) × ℕ → Memory.Prog Unit
  | (((mctx, ioctx), (fb0, fbBase)), tailLen) => do
    let (_, (((m, k), _), _)) := mctx
    let z0 ← pure 0
    let hb ← fbFindHeavyBktLoopProg ((((mctx, tailLen), (z0, z0))), m)
    let _ ← fbPartHeavyLoopProg (((((mctx, ioctx), (fbBase, (tailLen, hb.2))), z0)), k)
    fbPromoteFinishProg ((mctx, (fb0, tailLen)), hb.2)

theorem frontier_fbPromoteBodyProg
    (x : (BlockPoolCtx × (ℕ × ℕ)) × ℕ) (s : Memory.State)
    (hw : 0 < (SlotIoLayout.ofCtx (bpNestedIo x)).pgL.w) :
    ((Memory.spec 0).clientState s (fbPromoteBodyProg x)).frontier = s.frontier := by
  rcases x with ⟨⟨⟨⟨p1, ⟨⟨⟨m, k⟩, p2b⟩, p2c⟩⟩, ioctx⟩, ⟨fb0, fbBase⟩⟩, tailLen⟩
  set mctx : BpMetaCtx := (p1, (((m, k), p2b), p2c))
  unfold fbPromoteBodyProg; dsimp only; simp only [pure_bind]
  rw [StateTransitionSpec.clientState_bind, state_fbFindHeavyBktLoop,
    StateTransitionSpec.clientState_bind, frontier_fbPromoteFinishProg]
  set bStar := ((Memory.spec 0).clientResult s
    (fbFindHeavyBktLoopProg ((((mctx, tailLen), (0, 0))), m))).2
  exact (iterationSafe_of_frontier fbPartHeavyStepProg
    (fun _ d' _ => 0 < (SlotIoLayout.ofCtx d'.1.2).pgL.w) (w := 0)
    (fun d' a' st hw' => frontier_fbPartHeavyStep d' a' st hw')
    (d := ((mctx, ioctx), (fbBase, (tailLen, bStar)))) (s := s) hw k 0).2

private theorem realizesBounded_fbPromoteBody :
    RealizesBounded .exact fbPromoteBodyProg
      (WordEncoding.encode (α := (BlockPoolCtx × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((((mctx, ioctx), _), _)) s =>
        (BpMetaLayout.ofCtx mctx).Valid w s.frontier ∧
        (SlotIoLayout.ofCtx ioctx).Valid w s.frontier)
      (fun _ _ => 0) := by
  have hfhb := realizesBounded_fbFindHeavyBktLoop
  have hphl := realizesBounded_fbPartHeavyLoop
  have hfin := realizesBounded_fbPromoteFinish
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨⟨⟨mb, obm⟩, ⟨osd, otd⟩⟩, ⟨⟨oso, oto⟩, ⟨pb, wv⟩⟩⟩,
      ⟨⟨⟨m, k⟩, ⟨ms, mbk⟩⟩, ⟨mt, nc⟩⟩⟩, ioctx⟩, ⟨fb0, fbBase⟩⟩, tailLen⟩
    obtain ⟨hmv, hiov⟩ := h
    have hw := hmv.w_mach_pos
    let mctx : BpMetaCtx := ((((mb, obm), (osd, otd)), ((oso, oto), (pb, wv))),
      (((m, k), (ms, mbk)), (mt, nc)))
    have hfhb_s : ((Memory.spec 0).runClient s
        (fbFindHeavyBktLoopProg ((((mctx, tailLen), (0, 0))), m))).2.1 = s :=
      state_fbFindHeavyBktLoop _ s
    dsimp only [mctx] at hfhb_s
    try dsimp only at *
    try simp only [Prod.mk.eta] at *
    try dsimp only [Fits, StateTransitionSpec.clientState] at *
    try rw [hfhb_s]
    first | omega | (
      exact (iterationSafe_of_frontier fbFindHeavyBktStepProg
        (fun w' (d' : BpMetaCtx × ℕ) fr' => (BpMetaLayout.ofCtx d'.1).Valid w' fr')
        (fun d' a' st _ => congrArg Memory.State.frontier (state_fbFindHeavyBktStep (d', a') st))
        (d := (mctx, tailLen)) (s := s) hmv m (0, 0)).1) | (
      let bStar := ((Memory.spec 0).clientResult s
        (fbFindHeavyBktLoopProg ((((mctx, tailLen), (0, 0))), m))).2
      exact (iterationSafe_of_frontier fbPartHeavyStepProg
        (fun w' (d' : BlockPoolCtx × (ℕ × (ℕ × ℕ))) fr' =>
          (BpMetaLayout.ofCtx d'.1.1).Valid w' fr' ∧
          (SlotIoLayout.ofCtx d'.1.2).Valid w' fr')
        (fun d' a' st hd' => frontier_fbPartHeavyStep d' a' st hd'.2.w_pos)
        (d := ((mctx, ioctx), (fbBase, (tailLen, bStar)))) (s := s) ⟨hmv, hiov⟩ k 0).1) | (
      let bStar := ((Memory.spec 0).clientResult s
        (fbFindHeavyBktLoopProg ((((mctx, tailLen), (0, 0))), m))).2
      have hfr_p := (iterationSafe_of_frontier fbPartHeavyStepProg
        (fun _ d' _ => 0 < (SlotIoLayout.ofCtx d'.1.2).pgL.w) (w := 0)
        (fun d' a' st hw' => frontier_fbPartHeavyStep d' a' st hw')
        (d := ((mctx, ioctx), (fbBase, (tailLen, bStar)))) (s := s) hiov.w_pos k 0).2
      dsimp only [mctx, bStar] at hfr_p
      try unfold fbPartHeavyLoopProg
      dsimp only [StateTransitionSpec.clientState] at hfr_p ⊢
      rw [hfr_p]; exact hmv))

/-- Guarded tail-length check dispatching `fbPromoteBodyProg` when `M * K ≤ tailLen`. -/
def fbPromoteInnerCheckProg : (BlockPoolCtx × ℕ) × (ℕ × ℕ) → Memory.Prog Unit
  | (((mctx, ioctx), fb0), (nSide, fbBase)) => do
    let (_, (((m, k), _), _)) := mctx
    if fbBase ≤ nSide then
      if m * k ≤ nSide - fbBase then do
        let tailLen ← pure (nSide - fbBase)
        fbPromoteBodyProg (((mctx, ioctx), (fb0, fbBase)), tailLen)
      else pure ()
    else pure ()

private theorem realizesBounded_fbPromoteInnerCheck :
    RealizesBounded .exact fbPromoteInnerCheckProg
      (WordEncoding.encode (α := (BlockPoolCtx × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w (((mctx, ioctx), _), _) s =>
        (BpMetaLayout.ofCtx mctx).Valid w s.frontier ∧
        (SlotIoLayout.ofCtx ioctx).Valid w s.frontier)
      (fun _ _ => 0) := by
  have hbd := realizesBounded_fbPromoteBody
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨⟨⟨mb, obm⟩, ⟨osd, otd⟩⟩, ⟨⟨oso, oto⟩, ⟨pb, wv⟩⟩⟩,
      ⟨⟨⟨m, k⟩, ⟨ms, mbk⟩⟩, ⟨mt, nc⟩⟩⟩, ioctx⟩, fb0⟩, ⟨nSide, fbBase⟩⟩
    obtain ⟨hmv, hiov⟩ := h
    have hnc_w := hmv.nCap_lt_two_pow_w
    have h8mk := hmv.eight_MK_le
    have hns_w : nSide < 2 ^ w := hwords 28
    dsimp only [BpMetaLayout.ofCtx] at hnc_w h8mk
    have hmk_le : m * k ≤ 8 * m * k := by nlinarith
    try dsimp only at *
    try simp only [Prod.mk.eta] at *
    try dsimp only [Fits] at *
    first | exact hmv | exact hiov | omega)

/-- Guarded check-and-run wrapper for `fbPromoteBodyProg` (`2` `if`s). -/
def fbPromoteCheckProg : BlockPoolCtx × (ℕ × ℕ) → Memory.Prog Unit
  | ((mctx, ioctx), (nSide, fb0)) => do
    let (_, (((_, k), _), (_, nCap))) := mctx
    if nSide ≤ nCap then
      if fb0 ≤ nCap / k then do
        let fbBase ← pure (fb0 * k)
        fbPromoteInnerCheckProg (((mctx, ioctx), fb0), (nSide, fbBase))
      else pure ()
    else pure ()

private theorem realizesBounded_fbPromoteCheck :
    RealizesBounded .exact fbPromoteCheckProg
      (WordEncoding.encode (α := BlockPoolCtx × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w ((mctx, ioctx), _) s =>
        (BpMetaLayout.ofCtx mctx).Valid w s.frontier ∧
        (SlotIoLayout.ofCtx ioctx).Valid w s.frontier)
      (fun _ _ => 0) := by
  have hin := realizesBounded_fbPromoteInnerCheck
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨⟨mb, obm⟩, ⟨osd, otd⟩⟩, ⟨⟨oso, oto⟩, ⟨pb, wv⟩⟩⟩,
      ⟨⟨⟨m, k⟩, ⟨ms, mbk⟩⟩, ⟨mt, nc⟩⟩⟩, ioctx⟩, ⟨nSide, fb0⟩⟩
    obtain ⟨hmv, hiov⟩ := h
    have hnc_w := hmv.nCap_lt_two_pow_w
    have hK_ge := hmv.K_ge
    dsimp only [BpMetaLayout.ofCtx] at hnc_w hK_ge
    try dsimp only at *
    try simp only [Prod.mk.eta] at *
    try dsimp only [Fits] at *
    first | exact hmv | exact hiov | omega | (
      have hfb_mul : fb0 * k ≤ nc := (Nat.le_div_iff_mul_le (by omega)).mp (by omega)
      omega))

/-- Promote one heavy bucket `bStar` (`≥ K` occurrences in `ownerTail`) into `ownerBlk[fullBlocks]`
and shift `ownerTail` left by `K` (`¬ReadsWidth`). -/
def fbPromoteOneBlockProg : BlockPoolCtx → Memory.Prog Unit
  | (mctx, ioctx) => do
    let nSide ← bpReadScalarProg (mctx, 1)
    let fb0 ← bpReadScalarProg (mctx, 10)
    fbPromoteCheckProg ((mctx, ioctx), (nSide, fb0))

theorem realizesBounded_fbPromoteOneBlock :
    RealizesBounded .exact fbPromoteOneBlockProg
      (WordEncoding.encode (α := BlockPoolCtx))
      (WordEncoding.encode (α := Unit))
      (fun w (mctx, ioctx) s =>
        (BpMetaLayout.ofCtx mctx).Valid w s.frontier ∧
        (SlotIoLayout.ofCtx ioctx).Valid w s.frontier)
      (fun _ _ => 0) := by
  have hrs := realizesBounded_bpReadScalar
  have hchk := realizesBounded_fbPromoteCheck
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨⟨mb, obm⟩, ⟨osd, otd⟩⟩, ⟨⟨oso, oto⟩, ⟨pb, wv⟩⟩⟩,
      ⟨⟨⟨m, k⟩, ⟨ms, mbk⟩⟩, ⟨mt, nc⟩⟩⟩, ioctx⟩
    obtain ⟨hmv, hiov⟩ := h
    have hw := hmv.w_mach_pos
    have hw1 : 1 < 2 ^ w := Nat.one_lt_two_pow hw.ne'
    have hnc_w := hmv.nCap_lt_two_pow_w
    have hK_ge := hmv.K_ge
    dsimp only [BpMetaLayout.ofCtx] at hnc_w hK_ge
    have h10_w : 10 < 2 ^ w := lt_of_le_of_lt
      (by have := hmv.twelve_K_le; dsimp only [BpMetaLayout.ofCtx] at *; omega) hnc_w
    try dsimp only at *
    try simp only [runClient_state_bpReadScalarProg, Prod.mk.eta] at *
    try dsimp only [Fits, StateTransitionSpec.clientState] at *
    first | exact hmv | exact hiov | exact hw1 | exact h10_w)

theorem frontier_fbPromoteOneBlockProg (ctx : BlockPoolCtx) (s : Memory.State)
    (hw : 0 < (SlotIoLayout.ofCtx ctx.2).pgL.w) :
    ((Memory.spec 0).clientState s (fbPromoteOneBlockProg ctx)).frontier = s.frontier := by
  rcases ctx with ⟨⟨p1, ⟨⟨⟨m, k⟩, p2b⟩, ⟨mt, nCap⟩⟩⟩, ioctx⟩
  unfold fbPromoteOneBlockProg
  rw [StateTransitionSpec.clientState_bind, clientState_bpReadScalarProg,
    StateTransitionSpec.clientState_bind, clientState_bpReadScalarProg]
  unfold fbPromoteCheckProg fbPromoteInnerCheckProg; dsimp only
  split_ifs
  · simp only [pure_bind]
    split_ifs
    · exact frontier_fbPromoteBodyProg _ s hw
    all_goals rfl
  all_goals rfl

theorem fbPromoteOneBlockProg_spec {mp : BpMetaLayout} {io : SlotIoLayout}
    {U V bBits w slack : ℕ} {hBkt : ℕ → ℕ} {s_abs : Fin U → Option (Fin V)} {s : Memory.State}
    (hmv : mp.Valid w s.frontier) (hiov : io.Valid io.pgL.w s.frontier)
    (hdisj : ∀ addr, mp.OwnsMetaAddr addr → io.OwnsAddr addr → False)
    (hfb : (extractFallback mp s.mem).Valid)
    (hns_le : (extractFallback mp s.mem).nSide ≤ mp.nCap)
    (hio : io.StateInv (extractFallback mp s.mem).nSide slack s.mem)
    (href : PoolItemsRefines U V bBits hBkt (extractFallback mp s.mem).nSide
      (extractFallback mp s.mem).owner (slotIoPairAt io s.mem) s_abs)
    (htl_ge : mp.M * mp.K ≤ (extractFallback mp s.mem).tailLen) :
    let fb := extractFallback mp s.mem
    let s' := (Memory.spec 0).clientState s (fbPromoteOneBlockProg (mp.toCtx, io.toCtx))
    let fb' := extractFallback mp s'.mem
    s'.frontier = s.frontier ∧
    fb'.nSide = fb.nSide ∧
    fb'.fullBlocks = fb.fullBlocks + 1 ∧
    fb'.tailLen = fb.tailLen - mp.K ∧
    fb'.Valid ∧
    io.StateInv fb.nSide slack s'.mem ∧
    PoolItemsRefines U V bBits hBkt fb.nSide fb'.owner (slotIoPairAt io s'.mem) s_abs ∧
    (∀ p < fb.fullBlocks * mp.K,
      slotIoPairAt io s'.mem p = slotIoPairAt io s.mem p ∧ fb'.owner p = fb.owner p) ∧
    (∀ addr, ¬(mp.OwnsMetaAddr addr ∨ io.OwnsAddr addr) → s'.mem addr = s.mem addr) ∧
    (io.usePaged ≠ 0 →
      extractPageUnperm io.pgL s'.mem = extractPageUnperm io.pgL s.mem ∧
      ∀ idx < (extractPagePair io.pgL s.mem).virtLen io.partner.side,
        slotIoPairAt io.partner s'.mem idx = slotIoPairAt io.partner s.mem idx) := by
  dsimp only
  set fb := extractFallback mp s.mem
  set fb0 := fb.fullBlocks
  set fbBase := fb0 * mp.K
  set tailLen := fb.nSide - fbBase
  have hfb_K : fb.K = mp.K := rfl
  have hfb_M : fb.M = mp.M := rfl
  have htl_def : fb.tailLen = tailLen := rfl
  have hbl_le : fbBase ≤ fb.nSide := by
    dsimp only [fbBase, fb0]; rw [← hfb_K]; exact hfb.blocks_le
  have htl_le6 : tailLen ≤ 6 * mp.M * mp.K := by
    have h := hfb.tail_le; rw [htl_def, hfb_M, hfb_K] at h; exact h
  have htl_ge' : mp.M * mp.K ≤ tailLen := htl_def ▸ htl_ge
  have hK : 0 < mp.K := by have := hmv.K_ge; omega
  have hM1 : 1 ≤ mp.M := by have := hmv.M_ge; omega
  have hK1 : 1 ≤ mp.K := by omega
  have h6lt8 : 6 * mp.M * mp.K < 8 * mp.M * mp.K := by
    have := hmv.M_ge; have := hmv.K_ge; nlinarith
  have htl_8 : tailLen < 8 * mp.M * mp.K := lt_of_le_of_lt htl_le6 h6lt8
  have hfb_div : fb0 ≤ mp.nCap / mp.K :=
    (Nat.le_div_iff_mul_le hK).mpr (hbl_le.trans hns_le)
  have hfb_mb : fb0 < mp.maxBlocks := by have := hmv.div_K_add_two_le; omega
  have htl_nc : tailLen ≤ mp.nCap := by omega
  have hotd_ge : mp.offBktMeta + packedWords (16 * mp.M) mp.ptrB mp.w ≤ mp.offTailDir := by
    have := hmv.offSlabDir_ge; have := hmv.offTailDir_ge; omega
  have hoso_ge : mp.offBktMeta + packedWords (16 * mp.M) mp.ptrB mp.w ≤ mp.offSlabOwner := by
    have := hmv.offSlabOwner_ge; omega
  have hnc_eq : mp.toCtx.2.2.2 = mp.nCap := rfl
  have hk_eq : mp.toCtx.2.1.1.2 = mp.K := rfl
  have hm_eq : mp.toCtx.2.1.1.1 = mp.M := rfl
  obtain ⟨hbStar_lt, hbStar_cnt⟩ := fbFindHeavyBktLoop_spec (mp := mp) (tailLen := tailLen)
    (s := s) hM1 hK1 htl_nc htl_ge' htl_8 (fun t ht => hfb_M ▸ hfb.tail_lt t (htl_def.symm ▸ ht))
  set bStar := ((Memory.spec 0).clientResult s
    (fbFindHeavyBktLoopProg (((mp.toCtx, tailLen), (0, 0)), mp.M))).2
  have hbStar_nc : bStar ≤ mp.nCap := by have := hmv.sixteen_M_le; omega
  have hbStar_pb : bStar < 2 ^ mp.ptrB := lt_of_le_of_lt hbStar_nc hmv.nCap_lt_ptrB
  have hpart_loop : ∀ fuel dst (st : Memory.State),
      st.frontier = s.frontier →
      dst + fuel = mp.K →
      (extractFallback mp st.mem).nSide = fb.nSide →
      (extractFallback mp st.mem).fullBlocks = fb0 →
      (extractFallback mp st.mem).ownerBlk = fb.ownerBlk →
      (extractFallback mp st.mem).Valid →
      mp.K ≤ ((Finset.range tailLen).filter
        (fun t => (extractFallback mp st.mem).ownerTail t = bStar)).card →
      (∀ i < dst, (extractFallback mp st.mem).ownerTail i = bStar) →
      io.StateInv fb.nSide slack st.mem →
      PoolItemsRefines U V bBits hBkt fb.nSide (extractFallback mp st.mem).owner
        (slotIoPairAt io st.mem) s_abs →
      (∀ p < fbBase, slotIoPairAt io st.mem p = slotIoPairAt io s.mem p) →
      (∀ addr, ¬(mp.OwnsMetaAddr addr ∨ io.OwnsAddr addr) → st.mem addr = s.mem addr) →
      (io.usePaged ≠ 0 →
        extractPageUnperm io.pgL st.mem = extractPageUnperm io.pgL s.mem ∧
        ∀ idx < (extractPagePair io.pgL s.mem).virtLen io.partner.side,
          slotIoPairAt io.partner st.mem idx = slotIoPairAt io.partner s.mem idx) →
      let st' := (Memory.spec 0).clientState st
        (iterate fbPartHeavyStepProg ((mp.toCtx, io.toCtx), (fbBase, (tailLen, bStar))) fuel dst)
      st'.frontier = s.frontier ∧
      (extractFallback mp st'.mem).nSide = fb.nSide ∧
      (extractFallback mp st'.mem).fullBlocks = fb0 ∧
      (extractFallback mp st'.mem).ownerBlk = fb.ownerBlk ∧
      (extractFallback mp st'.mem).Valid ∧
      (∀ i < mp.K, (extractFallback mp st'.mem).ownerTail i = bStar) ∧
      io.StateInv fb.nSide slack st'.mem ∧
      PoolItemsRefines U V bBits hBkt fb.nSide (extractFallback mp st'.mem).owner
        (slotIoPairAt io st'.mem) s_abs ∧
      (∀ p < fbBase, slotIoPairAt io st'.mem p = slotIoPairAt io s.mem p) ∧
      (∀ addr, ¬(mp.OwnsMetaAddr addr ∨ io.OwnsAddr addr) → st'.mem addr = s.mem addr) ∧
      (io.usePaged ≠ 0 →
        extractPageUnperm io.pgL st'.mem = extractPageUnperm io.pgL s.mem ∧
        ∀ idx < (extractPagePair io.pgL s.mem).virtLen io.partner.side,
          slotIoPairAt io.partner st'.mem idx = slotIoPairAt io.partner s.mem idx) := by
    intro fuel; induction fuel with
    | zero =>
      intro dst st hfr hsum hns hfb_eq hob hval _ hpref hio_s href_s hlow hout hpart
      have hdst : dst = mp.K := by omega
      subst hdst
      exact ⟨hfr, hns, hfb_eq, hob, hval, hpref, hio_s, href_s, hlow, hout, hpart⟩
    | succ f ih =>
      intro dst st hfr hsum hns hfb_eq hob hval hcnt hpref hio_s href_s hlow hout hpart
      have hdst_K : dst < mp.K := by omega
      have hdst_tl : dst < tailLen := by
        have : mp.K ≤ mp.M * mp.K := Nat.le_mul_of_pos_left _ hM1; omega
      have htl_st : (extractFallback mp st.mem).tailLen = tailLen := by
        unfold FallbackState.tailLen; rw [hns, hfb_eq]; rfl
      obtain ⟨hsrc_ge, hsrc_lt, hsrc_eq⟩ := fbFindMatchLoop_spec (mp := mp) (s := st)
        htl_8 hdst_K hdst_tl.le hcnt
      set src := ((Memory.spec 0).clientResult st
        (fbFindMatchLoopProg (((mp.toCtx, (tailLen, bStar)), (dst, (0, dst))), tailLen - dst))).2.2
      have hsw_spec := fbSwapTailSlotsProg_spec (hfr.symm ▸ hmv) (hfr.symm ▸ hiov) hdisj
        hval h6lt8 (hns.symm ▸ hns_le) (hns.symm ▸ hio_s)
        (htl_st.symm ▸ hdst_tl) (htl_st.symm ▸ hsrc_lt)
      dsimp only at hsw_spec
      rw [hfb_eq] at hsw_spec
      obtain ⟨hfr₁, hfb₁, hio₁_raw, harr₁_raw, hout₁, hpart₁⟩ := hsw_spec
      have hio₁ : io.StateInv fb.nSide slack _ := hns ▸ hio₁_raw
      set st₁ := (Memory.spec 0).clientState st
        (fbSwapTailSlotsProg (((mp.toCtx, io.toCtx), fbBase), (dst, src)))
      have hstep_st : (Memory.spec 0).clientState st
          (fbPartHeavyStepProg (((mp.toCtx, io.toCtx), (fbBase, (tailLen, bStar))), dst)) =
          st₁ := by
        unfold fbPartHeavyStepProg
        rw [StateTransitionSpec.clientState_bind, clientState_bpReadScalarProg, ite_eq_left hdst_tl]
        simp only [pure_bind]
        rw [StateTransitionSpec.clientState_bind, state_fbFindMatchLoop,
          StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_pure]
      have hstep_res : (Memory.spec 0).clientResult st
          (fbPartHeavyStepProg (((mp.toCtx, io.toCtx), (fbBase, (tailLen, bStar))), dst)) =
          dst + 1 := by
        unfold fbPartHeavyStepProg
        rw [prog_clientResult_bind, clientState_bpReadScalarProg, ite_eq_left hdst_tl]
        simp only [pure_bind, prog_clientResult_bind]
        rw [state_fbFindMatchLoop, prog_clientResult_pure]
      unfold iterate; dsimp only
      rw [StateTransitionSpec.clientState_bind, hstep_st, hstep_res]
      have hns₁ : (extractFallback mp st₁.mem).nSide = fb.nSide := by
        rw [hfb₁]; simp only; exact hns
      have hfb_eq₁ : (extractFallback mp st₁.mem).fullBlocks = fb0 := by
        rw [hfb₁]
      have hob₁ : (extractFallback mp st₁.mem).ownerBlk = fb.ownerBlk := by
        rw [hfb₁]; simp only; exact hob
      have hot₁ : (extractFallback mp st₁.mem).ownerTail =
          (PhysSwap.mk dst src).apply (extractFallback mp st.mem).ownerTail := by
        rw [hfb₁]
      have htl_st₁ : (extractFallback mp st₁.mem).tailLen = tailLen := by
        unfold FallbackState.tailLen; rw [hns₁, hfb_eq₁]; rfl
      have hval₁ : (extractFallback mp st₁.mem).Valid :=
        { M_ge := hval.M_ge
          K_ge := hval.K_ge
          blocks_le := by rw [hns₁, hfb_eq₁]; exact hbl_le
          tail_le := by rw [htl_st₁, ← htl_st]; exact hval.tail_le
          blk_lt := by rw [hfb_eq₁, hob₁]; exact hfb.blk_lt
          tail_lt := fun t ht => by
            rw [htl_st₁] at ht
            rw [hot₁, physSwap_apply_eq_swapIdx]
            exact hval.tail_lt _ (htl_st.symm ▸ swapIdx_lt hdst_tl hsrc_lt ht) }
      have hcnt₁ : mp.K ≤ ((Finset.range tailLen).filter
          (fun t => (extractFallback mp st₁.mem).ownerTail t = bStar)).card := by
        rw [hot₁]
        simp only [physSwap_apply_eq_swapIdx]
        rwa [filter_card_comp_swapIdx hdst_tl hsrc_lt]
      have hpref₁ : ∀ i < dst + 1, (extractFallback mp st₁.mem).ownerTail i = bStar := by
        intro i hi
        rw [hot₁]
        rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hi) with hi_eq | hi_lt
        · subst hi_eq; rw [(PhysSwap.mk i src).apply_p₁]; exact hsrc_eq
        · rw [(PhysSwap.mk dst src).apply_of_ne _ (by dsimp only; omega) (by dsimp only; omega)]
          exact hpref i hi_lt
      have hp1_ns : fbBase + dst < fb.nSide := by omega
      have hp2_ns : fbBase + src < fb.nSide := by omega
      have how_sw : ∀ p < fb.nSide, (extractFallback mp st₁.mem).owner p =
          (PhysSwap.mk (fbBase + dst) (fbBase + src)).apply
            (extractFallback mp st.mem).owner p := by
        intro p hp
        unfold FallbackState.owner
        have hK_eq : (extractFallback mp st₁.mem).K = mp.K := rfl
        have hK_eq0 : (extractFallback mp st.mem).K = mp.K := rfl
        rw [hfb_eq₁, hK_eq]
        by_cases hlt : p < fbBase
        · rw [ite_eq_left hlt, hob₁, ← hob,
            (PhysSwap.mk (fbBase + dst) (fbBase + src)).apply_of_ne _
              (by dsimp only; omega) (by dsimp only; omega),
            hfb_eq, hK_eq0, ite_eq_left hlt]
        · rw [ite_eq_right hlt, hot₁]
          by_cases h1 : p = fbBase + dst
          · subst h1
            have hsub1 : fbBase + dst - fbBase = dst := Nat.add_sub_cancel_left _ _
            have hn2 : ¬(fbBase + src < fbBase) := by omega
            have hsub2 : fbBase + src - fbBase = src := Nat.add_sub_cancel_left _ _
            rw [hsub1, (PhysSwap.mk dst src).apply_p₁,
              (PhysSwap.mk (fbBase + dst) (fbBase + src)).apply_p₁,
              hfb_eq, hK_eq0, ite_eq_right hn2, hsub2]
          · by_cases h2 : p = fbBase + src
            · subst h2
              have hsub2 : fbBase + src - fbBase = src := Nat.add_sub_cancel_left _ _
              have hn1 : ¬(fbBase + dst < fbBase) := by omega
              have hsub1 : fbBase + dst - fbBase = dst := Nat.add_sub_cancel_left _ _
              rw [hsub2, (PhysSwap.mk dst src).apply_p₂,
                (PhysSwap.mk (fbBase + dst) (fbBase + src)).apply_p₂,
                hfb_eq, hK_eq0, ite_eq_right hn1, hsub1]
            · rw [(PhysSwap.mk dst src).apply_of_ne _
                  (by dsimp only; omega) (by dsimp only; omega),
                (PhysSwap.mk (fbBase + dst) (fbBase + src)).apply_of_ne _ h1 h2,
                hfb_eq, hK_eq0, ite_eq_right hlt]
      have href₁ := (href_s.apply_swap (sw := ⟨fbBase + dst, fbBase + src⟩) hp1_ns hp2_ns).congr
        how_sw (fun p hp => harr₁_raw p (hns.symm ▸ hp))
      refine ih (dst + 1) st₁ (hfr₁.trans hfr) (by omega) hns₁ hfb_eq₁ hob₁ hval₁ hcnt₁ hpref₁
        hio₁ href₁ (fun p hp => ?_)
        (fun a ha => (hout₁ a ha).trans (hout a ha))
        (fun hnz => ?_)
      · rw [harr₁_raw p (hns.symm ▸ hp.trans_le hbl_le),
          (PhysSwap.mk (fbBase + dst) (fbBase + src)).apply_of_ne _
            (by dsimp only; omega) (by dsimp only; omega)]
        exact hlow p hp
      · obtain ⟨hu₀, hp₀⟩ := hpart hnz
        obtain ⟨hu₁, hp₁⟩ := hpart₁ hnz
        have hvl₀ : (extractPagePair io.pgL st.mem).virtLen io.partner.side =
            (extractPagePair io.pgL s.mem).virtLen io.partner.side :=
          congrArg (fun u => u.st.virtLen io.partner.side) hu₀
        exact ⟨hu₁.trans hu₀, fun idx hidx => (hp₁ idx (hvl₀.symm ▸ hidx)).trans (hp₀ idx hidx)⟩
  set s_part := (Memory.spec 0).clientState s
    (iterate fbPartHeavyStepProg ((mp.toCtx, io.toCtx), (fbBase, (tailLen, bStar))) mp.K 0)
  obtain ⟨hfr_p, hns_p, hfb_p, hob_p, hval_p, hpref_p, hio_p, href_p, hlow_p, hout_p, hpg_p⟩ :=
    hpart_loop mp.K 0 s rfl (Nat.zero_add _) rfl rfl rfl hfb hbStar_cnt
      (fun _ h => absurd h (Nat.not_lt_zero _)) hio href (fun _ _ => rfl)
      (fun _ _ => rfl) (fun _ => ⟨rfl, fun _ _ => rfl⟩)
  set s_so :=
    (Memory.spec 0).clientState s_part (bpWriteSlabOwnerProg ((mp.toCtx, (fb0, 1)), bStar))
  have hwf_so := bpWriteSlabOwnerProg_frame hmv.w_pos hoso_ge fb0 1 bStar
  have hfb_so := extractFallback_writeOwnerBlk (hfr_p.symm ▸ hmv) hfb_mb hbStar_pb hbStar_nc
    (s := s_part)
  have hfr_so : s_so.frontier = s.frontier := (hwf_so.1.frontier_eq s_part).trans hfr_p
  have htl_p : (extractFallback mp s_part.mem).tailLen = tailLen := by
    unfold FallbackState.tailLen; rw [hns_p, hfb_p]; rfl
  have hshift_loop : ∀ fuel t (ot₀ ob₀ : ℕ → ℕ) (st : Memory.State),
      st.frontier = s.frontier →
      t + fuel = tailLen - mp.K →
      (extractFallback mp st.mem).nSide = fb.nSide →
      (extractFallback mp st.mem).fullBlocks = fb0 →
      (extractFallback mp st.mem).ownerBlk = ob₀ →
      (∀ i < tailLen, ot₀ i < mp.M) →
      (∀ i < t, (extractFallback mp st.mem).ownerTail i = ot₀ (i + mp.K)) →
      (∀ j, t ≤ j → j < tailLen → (extractFallback mp st.mem).ownerTail j = ot₀ j) →
      (∀ addr, ¬mp.OwnsMetaAddr addr → st.mem addr = s_so.mem addr) →
      let st' :=
        (Memory.spec 0).clientState st (iterate fbShiftLeftStepProg (mp.toCtx, mp.K) fuel t)
      st'.frontier = s.frontier ∧
      (extractFallback mp st'.mem).nSide = fb.nSide ∧
      (extractFallback mp st'.mem).fullBlocks = fb0 ∧
      (extractFallback mp st'.mem).ownerBlk = ob₀ ∧
      (∀ i < tailLen - mp.K, (extractFallback mp st'.mem).ownerTail i = ot₀ (i + mp.K)) ∧
      (∀ addr, ¬mp.OwnsMetaAddr addr → st'.mem addr = s_so.mem addr) := by
    intro fuel; induction fuel with
    | zero =>
      intro t ot₀ ob₀ st hfr hsum hns hfb_eq hob _ hlo _ hout
      have ht : t = tailLen - mp.K := by omega
      subst ht; exact ⟨hfr, hns, hfb_eq, hob, hlo, hout⟩
    | succ f ih =>
      intro t ot₀ ob₀ st hfr hsum hns hfb_eq hob hot_M hlo hhi hout
      have ht_lt : t < tailLen - mp.K := by omega
      have htk_tl : t + mp.K < tailLen := by omega
      have ht_8 : t < 8 * mp.M * mp.K := by omega
      have htk_8 : t + mp.K < 8 * mp.M * mp.K := htk_tl.trans htl_8
      have ht_nc : t < mp.nCap := by omega
      have hk_sub : mp.K ≤ mp.nCap - t := by omega
      have hv_eq : (extractFallback mp st.mem).ownerTail (t + mp.K) = ot₀ (t + mp.K) :=
        hhi (t + mp.K) (by omega) htk_tl
      have hv_M : ot₀ (t + mp.K) < mp.M := hot_M _ htk_tl
      have hv_nc : ot₀ (t + mp.K) ≤ mp.nCap := by have := hmv.sixteen_M_le; omega
      have hv_pb : ot₀ (t + mp.K) < 2 ^ mp.ptrB := lt_of_le_of_lt hv_nc hmv.nCap_lt_ptrB
      have hr_tk : (Memory.spec 0).clientResult st (bpReadTailDirRawProg (mp.toCtx, t + mp.K)) =
          ot₀ (t + mp.K) := by
        unfold bpReadTailDirRawProg; dsimp only [BpMetaLayout.toCtx]
        rw [ite_eq_left htk_8, clientResult_readPackedCompGenProg]
        have : (extractFallback mp st.mem).ownerTail (t + mp.K) =
            readPacked (mp.metaBase + mp.offTailDir) mp.ptrB mp.w st.mem (t + mp.K) := by
          unfold extractFallback; dsimp only; rw [ite_eq_left htk_8]
        exact this.symm.trans hv_eq
      set st₁ := (Memory.spec 0).clientState st
        (bpWriteTailDirRawProg ((mp.toCtx, t), ot₀ (t + mp.K)))
      have hstep_st : (Memory.spec 0).clientState st
          (fbShiftLeftStepProg ((mp.toCtx, mp.K), t)) = st₁ := by
        unfold fbShiftLeftStepProg
        rw [StateTransitionSpec.clientState_bind, clientState_bpReadScalarProg]; dsimp only
        rw [hnc_eq, ite_eq_left ht_nc, ite_eq_left hk_sub, StateTransitionSpec.clientState_bind,
          clientState_bpReadTailDirRawProg, hr_tk, StateTransitionSpec.clientState_bind,
          StateTransitionSpec.clientState_pure]
      have hstep_res : (Memory.spec 0).clientResult st
          (fbShiftLeftStepProg ((mp.toCtx, mp.K), t)) = t + 1 := by
        unfold fbShiftLeftStepProg
        rw [prog_clientResult_bind, clientState_bpReadScalarProg]; dsimp only
        rw [hnc_eq, ite_eq_left ht_nc, ite_eq_left hk_sub, prog_clientResult_bind,
          clientState_bpReadTailDirRawProg, hr_tk, prog_clientResult_bind, prog_clientResult_pure]
      have hwf := bpWriteTailDirRawProg_frame hmv.w_pos hotd_ge t (ot₀ (t + mp.K))
      have hfb₁ := extractFallback_writeOwnerTail (hfr.symm ▸ hmv) ht_8 hv_pb hv_nc (s := st)
      unfold iterate; dsimp only
      rw [StateTransitionSpec.clientState_bind, hstep_st, hstep_res]
      refine ih (t + 1) ot₀ ob₀ st₁ ((hwf.1.frontier_eq st).trans hfr) (by omega)
        (by rw [hfb₁]; simp only; exact hns)
        (by rw [hfb₁]; simp only; exact hfb_eq)
        (by rw [hfb₁]; simp only; exact hob) hot_M
        (fun i hi => ?_) (fun j hj1 hj2 => ?_)
        (fun a ha => (hwf.1.mem_outside st a ha).trans (hout a ha))
      · rw [hfb₁]; simp only
        rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hi) with rfl | hi_lt
        · exact Function.update_self ..
        · rw [Function.update_of_ne (by omega)]; exact hlo i hi_lt
      · rw [hfb₁]; simp only
        rw [Function.update_of_ne (by omega)]; exact hhi j (by omega) hj2
  set s_sh := (Memory.spec 0).clientState s_so
    (iterate fbShiftLeftStepProg (mp.toCtx, mp.K) (tailLen - mp.K) 0)
  obtain ⟨hfr_sh, hns_sh, hfb_sh, hob_sh, hot_sh, hout_sh⟩ :=
    hshift_loop (tailLen - mp.K) 0 (extractFallback mp s_part.mem).ownerTail
      (Function.update fb.ownerBlk fb0 bStar) s_so hfr_so (Nat.zero_add _)
      (by rw [hfb_so]; simp only; exact hns_p)
      (by rw [hfb_so]; simp only; exact hfb_p)
      (by rw [hfb_so]; simp only; rw [hob_p])
      (fun i hi => hfb_M ▸ hval_p.tail_lt i (htl_p.symm ▸ hi))
      (fun _ h => absurd h (Nat.not_lt_zero _))
      (fun j _ _ => by rw [hfb_so])
      (fun _ _ => rfl)
  set s_fin := (Memory.spec 0).clientState s_sh (bpWriteScalarProg ((mp.toCtx, 10), fb0 + 1))
  have hbl_mk : fbBase + mp.M * mp.K ≤ fb.nSide := by omega
  have hfb1_nc : fb0 + 1 ≤ mp.nCap := by
    have : (fb0 + 1) * mp.K ≤ fbBase + mp.M * mp.K := by
      rw [Nat.add_one_mul]; exact Nat.add_le_add_left (Nat.le_mul_of_pos_left _ hM1) _
    have := this.trans (hbl_mk.trans hns_le)
    exact (le_mul_of_one_le_right (Nat.zero_le _) hK1).trans this
  have hfb0_nc : fb0 < mp.nCap := by omega
  have hk_tl : mp.K ≤ tailLen := by
    have : mp.K ≤ mp.M * mp.K := Nat.le_mul_of_pos_left _ hM1; omega
  have hwf_sc := bpWriteScalarProg_frame hmv.w_pos hmv.offBktMeta_ge 10 (fb0 + 1)
  have hfb_fin := extractFallback_writeScalar_10 (hfr_sh.symm ▸ hmv) hfb1_nc (s := s_sh)
  have hst_tot : (Memory.spec 0).clientState s (fbPromoteOneBlockProg (mp.toCtx, io.toCtx)) =
      s_fin := by
    unfold fbPromoteOneBlockProg
    rw [StateTransitionSpec.clientState_bind, clientState_bpReadScalarProg,
      clientResult_bpReadScalar s (Or.inl rfl),
      StateTransitionSpec.clientState_bind, clientState_bpReadScalarProg,
      clientResult_bpReadScalar s (Or.inr ⟨le_rfl, by omega⟩)]
    unfold fbPromoteCheckProg; dsimp only
    have hns_mem : s.mem (mp.metaBase + 1) = fb.nSide := rfl
    have hfb_mem : s.mem (mp.metaBase + 10) = fb0 := rfl
    rw [hns_mem, hfb_mem, hnc_eq, hk_eq, ite_eq_left hns_le, ite_eq_left hfb_div]
    simp only [pure_bind]
    unfold fbPromoteInnerCheckProg; dsimp only
    rw [hm_eq, hk_eq, ite_eq_left hbl_le, ite_eq_left htl_ge']
    simp only [pure_bind]
    unfold fbPromoteBodyProg fbPartHeavyLoopProg; dsimp only [BpMetaLayout.toCtx]
    simp only [pure_bind]
    rw [StateTransitionSpec.clientState_bind]
    change (Memory.spec 0).clientState
      ((Memory.spec 0).clientState s
        (fbFindHeavyBktLoopProg ((((mp.toCtx, tailLen), (0, 0))), mp.M))) _ = _
    rw [state_fbFindHeavyBktLoop, StateTransitionSpec.clientState_bind]
    change (Memory.spec 0).clientState s_part
      (fbPromoteFinishProg ((mp.toCtx, (fb0, tailLen)), bStar)) = s_fin
    unfold fbPromoteFinishProg fbShiftLeftLoopProg; dsimp only
    rw [hnc_eq, hk_eq, ite_eq_left hfb0_nc, ite_eq_left hk_tl]
    simp only [pure_bind]
    rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind]
  rw [hst_tot]
  have hio_out : ∀ addr, io.OwnsAddr addr → s_fin.mem addr = s_part.mem addr := fun a hia => by
    have hma : ¬mp.OwnsMetaAddr a := fun hma => hdisj a hma hia
    exact (hwf_sc.1.mem_outside s_sh a hma).trans
      ((hout_sh a hma).trans (hwf_so.1.mem_outside s_part a hma))
  obtain ⟨hio_fin, harr_fin⟩ := io.congr_of_outside hiov.w_pos hio_p hio_out
  have hns_fin : (extractFallback mp s_fin.mem).nSide = fb.nSide := by
    rw [hfb_fin]; simp only; exact hns_sh
  have hfb_fin_blk : (extractFallback mp s_fin.mem).fullBlocks = fb0 + 1 := by
    rw [hfb_fin]
  have hob_fin : (extractFallback mp s_fin.mem).ownerBlk = Function.update fb.ownerBlk fb0 bStar :=
    by rw [hfb_fin]; simp only; exact hob_sh
  have hot_fin :
      (extractFallback mp s_fin.mem).ownerTail = (extractFallback mp s_sh.mem).ownerTail :=
    by rw [hfb_fin]
  have htl_fin : (extractFallback mp s_fin.mem).tailLen = tailLen - mp.K := by
    unfold FallbackState.tailLen; rw [hns_fin, hfb_fin_blk]
    have : (fb0 + 1) * mp.K = fbBase + mp.K := Nat.add_one_mul fb0 mp.K
    have hK_eq : (extractFallback mp s_fin.mem).K = mp.K := rfl
    rw [hK_eq, this]; omega
  have how_fin : ∀ p < fb.nSide,
      (extractFallback mp s_fin.mem).owner p = (extractFallback mp s_part.mem).owner p := by
    intro p hp
    unfold FallbackState.owner
    have hK_f : (extractFallback mp s_fin.mem).K = mp.K := rfl
    have hK_p : (extractFallback mp s_part.mem).K = mp.K := rfl
    rw [hfb_fin_blk, hfb_p, hK_f, hK_p]
    by_cases hp1 : p < fbBase
    · have hp2 : p < (fb0 + 1) * mp.K := hp1.trans_le (by rw [Nat.add_one_mul]; omega)
      rw [ite_eq_left hp2, ite_eq_left hp1, hob_fin, hob_p,
        Function.update_of_ne (ne_of_lt ((Nat.div_lt_iff_lt_mul hK).mpr hp1))]
    · rw [ite_eq_right hp1]
      by_cases hp2 : p < (fb0 + 1) * mp.K
      · rw [ite_eq_left hp2, hob_fin]
        have hdiv : p / mp.K = fb0 := by
          have hge : fb0 ≤ p / mp.K := (Nat.le_div_iff_mul_le hK).mpr (Nat.le_of_not_lt hp1)
          have hlt : p / mp.K < fb0 + 1 := (Nat.div_lt_iff_lt_mul hK).mpr hp2
          omega
        rw [hdiv, Function.update_self]
        exact (hpref_p (p - fbBase) (by rw [Nat.add_one_mul] at hp2; omega)).symm
      · rw [ite_eq_right hp2, hot_fin]
        have ht_lt : p - (fb0 + 1) * mp.K < tailLen - mp.K := by
          rw [Nat.add_one_mul] at hp2 ⊢; omega
        rw [hot_sh _ ht_lt]
        exact congrArg (extractFallback mp s_part.mem).ownerTail
          (by rw [Nat.add_one_mul] at hp2 ⊢; omega)
  have hval_fin : (extractFallback mp s_fin.mem).Valid :=
    { M_ge := hfb.M_ge
      K_ge := hfb.K_ge
      blocks_le := by
        rw [hns_fin, hfb_fin_blk]
        have hK_f : (extractFallback mp s_fin.mem).K = mp.K := rfl
        rw [hK_f, Nat.add_one_mul]
        exact (Nat.add_le_add_left (Nat.le_mul_of_pos_left _ hM1) _).trans hbl_mk
      tail_le := by
        have hM_f : (extractFallback mp s_fin.mem).M = mp.M := rfl
        have hK_f : (extractFallback mp s_fin.mem).K = mp.K := rfl
        rw [htl_fin, hM_f, hK_f]; omega
      blk_lt := fun blk hblk => by
        rw [hfb_fin_blk] at hblk
        rw [hob_fin]
        rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hblk) with rfl | hlt
        · rw [Function.update_self]; exact hbStar_lt
        · rw [Function.update_of_ne (ne_of_lt hlt)]; exact hfb.blk_lt blk hlt
      tail_lt := fun t ht => by
        rw [htl_fin] at ht
        rw [hot_fin, hot_sh t ht]
        exact hval_p.tail_lt (t + mp.K) (by rw [htl_p]; omega) }
  have href_fin := href_p.congr how_fin harr_fin
  refine ⟨(hwf_sc.1.frontier_eq s_sh).trans hfr_sh, hns_fin, hfb_fin_blk, htl_fin, hval_fin,
    hio_fin, href_fin, fun p hp => ?_, fun addr ha => ?_, fun hnz => ?_⟩
  · refine ⟨(harr_fin p (hp.trans_le hbl_le)).trans (hlow_p p hp), ?_⟩
    rw [how_fin p (hp.trans_le hbl_le)]
    unfold FallbackState.owner
    have hK_p : (extractFallback mp s_part.mem).K = mp.K := rfl
    rw [hfb_p, hK_p, ite_eq_left hp, hob_p, hfb_K, ite_eq_left hp]
  · have hma : ¬mp.OwnsMetaAddr addr := fun h => ha (Or.inl h)
    exact (hwf_sc.1.mem_outside s_sh addr hma).trans
      ((hout_sh addr hma).trans ((hwf_so.1.mem_outside s_part addr hma).trans (hout_p addr ha)))
  · obtain ⟨hu_p, hp_p⟩ := hpg_p hnz
    have hown_pg : ∀ addr, io.pgL.OwnsAddr addr → s_fin.mem addr = s_part.mem addr := fun a ha => by
      apply hio_out a; unfold SlotIoLayout.OwnsAddr; rwa [ite_eq_right hnz]
    have hu_fin : extractPageUnperm io.pgL s_fin.mem = extractPageUnperm io.pgL s_part.mem :=
      extractPageUnperm_congr hiov.w_pos (fun a ha => hown_pg a (Or.inl ha))
    refine ⟨hu_fin.trans hu_p, fun idx hidx => ?_⟩
    unfold SlotIoLayout.StateInv at hio_p; rw [ite_eq_right hnz] at hio_p
    have hidx_p : idx < (extractPagePair io.pgL s_part.mem).virtLen io.partner.side := by
      have : extractPagePair io.pgL s_part.mem = extractPagePair io.pgL s.mem :=
        congrArg PageUnpermState.st hu_p
      rwa [this]
    have hp_lt_p :
        (extractPageUnperm io.pgL s_part.mem).toPhys io.partner.side idx < io.pgL.nCap :=
      (hio_p.1.toPhys_lt hidx_p).trans_le hio_p.2.2.2.1
    have hp_fin : slotIoPairAt io.partner s_fin.mem idx = slotIoPairAt io.partner s_part.mem idx :=
      by
        unfold slotIoPairAt
        have hp_nz : io.partner.usePaged ≠ 0 := hnz
        rw [ite_eq_right hp_nz, ite_eq_right hp_nz, SlotIoLayout.partner_pgL, hu_fin]
        exact arenaPairAt_congr hiov.w_pos (fun a ha => hown_pg a (Or.inr ha)) hp_lt_p
    exact hp_fin.trans (hp_p idx hidx)

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp

end
