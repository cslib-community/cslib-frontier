/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpHashProg
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpFastBaseProg.Frame
import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpBTreeProg
import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpFastBaseProg.SliceBuf
import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpFastBaseProg.HeaderBkt
import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpFastBaseProg.SlotArrays
import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpFastBaseProg.LocPoolArrays
import CslibFrontier.Tactic.Realize

/-!
# Per-Bucket Overmars Shadow B+-Tree Rebuild (`overmarsStepGenProg`)

This module implements the compact `BktMetaRt` descriptor and the worst-case `O_c(1)` per-bucket
Overmars shadow B+-tree rebuild subroutine (`overmarsStepGenProg`) on `FastMemRep`, certified
over `Basis.exact` with zero local work via `realize` and `Realizes.iterate₀`:

1. `BktMetaRt`, `mkBktMetaRt`, `mkBktMetaRtProg`, `BktMetaBucketEnv`, `setOvermarsActRtProg`:
   4-word runtime descriptor for packed `bktMeta` multi-field updates.
2. Activation, 16-coordinate bounded-fuel shadow-tree scan (`overmarsScanLoopGenProg`), and
   role-swap completion combined in `overmarsStepGenProg`.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.BktMetaRt`, `mkBktMetaRt`,
  `mkBktMetaRtProg`, `BktMetaBucketEnv`, `setOvermarsActRtProg`, `OvermarsBucketStepBounds`,
  `OvermarsStepPre`, `overmarsStepGenProg`.

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.realizes_mkBktMetaRt`,
  `mkBktMetaRtProg_spec`, `realizes_setOvermarsActRt`, `setOvermarsActRtProg_fastStep`,
  `OvermarsBucketStepBounds.of_core_and_pre`, `realizes_overmarsStepGen`,
  `overmarsStepGenProg_fastStep`.
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

open Cslib.WordRAM Cslib.WordRAM.Realization
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.StateTransitionSpec (clientState_bind clientResult_bind)
open Cslib.DataStructure.WordRAM
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.Dynamic
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.SuccinctWhp
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM.Succinct

attribute [local simp] clientResult_pure_whp clientState_pure_whp

/-! ### Bundled read-only and fast-step specifications -/

/-- From `s`, `p` leaves the state unchanged, returns `r`, issues exactly `C` memory operations,
and is valid below frontier `F`. -/
private structure ReadSpec {α : Type} (w F : ℕ) (s : Memory.State) (p : Memory.Prog α) (r : α)
    (C : ℕ) : Prop where
  state : (Memory.spec 0).clientState s p = s
  result : (Memory.spec 0).clientResult s p = r
  cost : memoryCost p s = C
  valid : ValidProg w F s p

private theorem ReadSpec.of {α : Type} {w F C : ℕ} {s : Memory.State} {p : Memory.Prog α}
    {r : α} (h : (Memory.spec 0).clientState s p = s ∧ (Memory.spec 0).clientResult s p = r ∧
      memoryCost p s = C ∧ ValidProg w F s p) : ReadSpec w F s p r C :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩

private theorem ReadSpec.toAnd {α : Type} {w F C C' : ℕ} {s : Memory.State}
    {p : Memory.Prog α} {r r' : α} (h : ReadSpec w F s p r C) (hr : r = r') (hC : C = C') :
    (Memory.spec 0).clientState s p = s ∧ (Memory.spec 0).clientResult s p = r' ∧
      memoryCost p s = C' ∧ ValidProg w F s p :=
  ⟨h.state, hr ▸ h.result, hC ▸ h.cost, h.valid⟩

private theorem ReadSpec.pure {α : Type} {w F : ℕ} {s : Memory.State} (a : α) :
    ReadSpec w F s (pure a) a 0 :=
  ⟨rfl, rfl, rfl, validProg_pure a⟩

private theorem ReadSpec.bind {α β : Type} {w F C₁ C₂ : ℕ} {s : Memory.State}
    {m : Memory.Prog α} {k : α → Memory.Prog β} {a : α} {b : β}
    (hm : ReadSpec w F s m a C₁) (hk : ReadSpec w F s (k a) b C₂) :
    ReadSpec w F s (m >>= k) b (C₁ + C₂) where
  state := by rw [clientState_bind, hm.state, hm.result, hk.state]
  result := by rw [clientResult_bind, hm.state, hm.result, hk.result]
  cost := by rw [memoryCost_bind', hm.state, hm.result, hm.cost, hk.cost]
  valid := validProg_bind hm.valid (by rw [hm.state, hm.result]; exact hk.valid)

/-- From `s`, `p` issues exactly `C` memory operations, is valid below the large-mode frontier,
and is a `FastStateStep` to `fs'`. -/
private structure StepSpec {α : Type} (base c U V w n_max : ℕ) (θ : SeedWhp c U n_max)
    (fs' : FastState) (s : Memory.State) (p : Memory.Prog α) (C : ℕ) : Prop where
  cost : memoryCost p s = C
  valid : ValidProg w (base + largeSpaceWhp c U V w n_max) s p
  step : FastStateStep base c U V w n_max θ fs' s ((Memory.spec 0).clientState s p)

private theorem StepSpec.of {α : Type} {base c U V w n_max C : ℕ} {θ : SeedWhp c U n_max}
    {fs' : FastState} {s : Memory.State} {p : Memory.Prog α}
    (h : memoryCost p s = C ∧ ValidProg w (base + largeSpaceWhp c U V w n_max) s p ∧
      FastStateStep base c U V w n_max θ fs' s ((Memory.spec 0).clientState s p)) :
    StepSpec base c U V w n_max θ fs' s p C :=
  ⟨h.1, h.2.1, h.2.2⟩

/-- Record the exact cost of a step known only to be bounded; the bound stays with the caller. -/
private theorem StepSpec.of_le {α : Type} {base c U V w n_max C : ℕ} {θ : SeedWhp c U n_max}
    {fs' : FastState} {s : Memory.State} {p : Memory.Prog α}
    (h : memoryCost p s ≤ C ∧ ValidProg w (base + largeSpaceWhp c U V w n_max) s p ∧
      FastStateStep base c U V w n_max θ fs' s ((Memory.spec 0).clientState s p)) :
    StepSpec base c U V w n_max θ fs' s p (memoryCost p s) :=
  ⟨rfl, h.2.1, h.2.2⟩

private theorem StepSpec.toAnd {α : Type} {base c U V w n_max C C' : ℕ}
    {θ : SeedWhp c U n_max} {fs' : FastState} {s : Memory.State} {p : Memory.Prog α}
    (h : StepSpec base c U V w n_max θ fs' s p C) (hC : C = C') :
    memoryCost p s = C' ∧ ValidProg w (base + largeSpaceWhp c U V w n_max) s p ∧
      FastStateStep base c U V w n_max θ fs' s ((Memory.spec 0).clientState s p) :=
  ⟨hC ▸ h.cost, h.valid, h.step⟩

private theorem StepSpec.toAnd_le {α : Type} {base c U V w n_max C C' : ℕ}
    {θ : SeedWhp c U n_max} {fs' : FastState} {s : Memory.State} {p : Memory.Prog α}
    (h : StepSpec base c U V w n_max θ fs' s p C) (hC : C ≤ C') :
    memoryCost p s ≤ C' ∧ ValidProg w (base + largeSpaceWhp c U V w n_max) s p ∧
      FastStateStep base c U V w n_max θ fs' s ((Memory.spec 0).clientState s p) :=
  ⟨h.cost ▸ hC, h.valid, h.step⟩

private theorem StepSpec.toAnd_le_and {α : Type} {base c U V w n_max C C' : ℕ}
    {θ : SeedWhp c U n_max} {fs' : FastState} {s : Memory.State} {p : Memory.Prog α} {P : Prop}
    (h : StepSpec base c U V w n_max θ fs' s p C) (hC : C ≤ C') (hP : P) :
    memoryCost p s ≤ C' ∧ ValidProg w (base + largeSpaceWhp c U V w n_max) s p ∧
      FastStateStep base c U V w n_max θ fs' s ((Memory.spec 0).clientState s p) ∧ P :=
  ⟨h.cost ▸ hC, h.valid, h.step, hP⟩

private theorem StepSpec.pure {α : Type} {base c U V w n_max : ℕ} {θ : SeedWhp c U n_max}
    {fs : FastState} {s : Memory.State} (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) (a : α) :
    StepSpec base c U V w n_max θ fs s (pure a) 0 :=
  ⟨rfl, validProg_pure a, FastStateStep.refl hseed hrep⟩

private theorem StepSpec.bind {α β : Type} {base c U V w n_max C₁ C₂ : ℕ}
    {θ : SeedWhp c U n_max} {fs₁ fs₂ : FastState} {s : Memory.State}
    {m : Memory.Prog α} {k : α → Memory.Prog β}
    (hm : StepSpec base c U V w n_max θ fs₁ s m C₁)
    (hk : StepSpec base c U V w n_max θ fs₂ ((Memory.spec 0).clientState s m)
      (k ((Memory.spec 0).clientResult s m)) C₂) :
    StepSpec base c U V w n_max θ fs₂ s (m >>= k) (C₁ + C₂) where
  cost := by rw [memoryCost_bind', hm.cost, hk.cost]
  valid := validProg_bind hm.valid hk.valid
  step := by rw [clientState_bind]; exact hm.step.trans hk.step

private theorem ReadSpec.thenStep {α β : Type} {base c U V w n_max C₁ C₂ : ℕ}
    {θ : SeedWhp c U n_max} {fs' : FastState} {s : Memory.State}
    {m : Memory.Prog α} {k : α → Memory.Prog β} {a : α}
    (hm : ReadSpec w (base + largeSpaceWhp c U V w n_max) s m a C₁)
    (hk : StepSpec base c U V w n_max θ fs' s (k a) C₂) :
    StepSpec base c U V w n_max θ fs' s (m >>= k) (C₁ + C₂) where
  cost := by rw [memoryCost_bind', hm.state, hm.result, hk.cost, hm.cost]
  valid := validProg_bind hm.valid (by rw [hm.state, hm.result]; exact hk.valid)
  step := by rw [clientState_bind, hm.state, hm.result]; exact hk.step

private theorem StepSpec.if_pos {α : Type} {base c U V w n_max C : ℕ} {θ : SeedWhp c U n_max}
    {fs' : FastState} {s : Memory.State} {q : Prop} [Decidable q] {p₁ p₂ : Memory.Prog α}
    (hq : q) (h : StepSpec base c U V w n_max θ fs' s p₁ C) :
    StepSpec base c U V w n_max θ fs' s (if q then p₁ else p₂) C := by
  rwa [ite_eq_left hq]

private theorem StepSpec.if_neg {α : Type} {base c U V w n_max C : ℕ} {θ : SeedWhp c U n_max}
    {fs' : FastState} {s : Memory.State} {q : Prop} [Decidable q] {p₁ p₂ : Memory.Prog α}
    (hq : ¬q) (h : StepSpec base c U V w n_max θ fs' s p₂ C) :
    StepSpec base c U V w n_max θ fs' s (if q then p₁ else p₂) C := by
  rwa [ite_eq_right hq]

/-! ## Section 1: `BktMetaRt` Descriptor and Role/Activation Substeps -/

/-- Compact 4-word runtime descriptor `((base, offBktMeta), (globalPtrBits, w))` for `bktMeta`
packed-array accesses, keeping `realize` elaboration independent of `WhpCoreParams` width. -/
abbrev BktMetaRt : Type := (ℕ × ℕ) × (ℕ × ℕ)

/-- Construct the 4-word `BktMetaRt` descriptor for `(c, U, V, w, n_max, base)`. -/
@[expose] def mkBktMetaRt (c U V w n_max base : ℕ) : BktMetaRt :=
  ((base, offBktMeta c U V w n_max), (globalPtrBits n_max, w))

/-- Project `BktMetaRt` from `(cp, base)` in zero memory steps. -/
@[irreducible] def mkBktMetaRtProg : WhpCoreParams × ℕ → Memory.Prog BktMetaRt
  | (cp, base) => do
    let off ← pure (wpOffBktMeta cp)
    let g ← pure (wpGlobalPtrBits cp)
    let ww ← pure (wpW cp)
    pure ((base, off), (g, ww))

theorem realizes_mkBktMetaRt :
    Realizes .exact mkBktMetaRtProg
      (WordEncoding.encode (α := WhpCoreParams × ℕ))
      (WordEncoding.encode (α := BktMetaRt))
      (fun _ _ _ => True)
      (fun _ _ => 0) := by
  unfold mkBktMetaRtProg
  realize

theorem mkBktMetaRtProg_spec {c U V w n_max base : ℕ}
    (hth : whpThreshold c ≤ n_max) (s : Memory.State) :
    let prog := mkBktMetaRtProg (mkWhpCoreParams c U V w n_max, base)
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog = mkBktMetaRt c U V w n_max base ∧
    memoryCost prog s = 0 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  unfold mkBktMetaRtProg
  simp only [wp_large_offBktMeta hth, wp_large_globalPtrBits hth, wp_large_w hth, pure_bind]
  exact ⟨rfl, rfl, rfl, validProg_pure _⟩

/-- Existential admissibility predicate for `(bm, b)` on `bktMeta`. -/
@[expose] def BktMetaBucketEnv (w : ℕ) (bm : BktMetaRt) (b : ℕ) : Prop :=
  ∃ c U V w₀ n_max base,
    WhpLargeEnv c U V w₀ n_max w base ∧
    bm = mkBktMetaRt c U V w₀ n_max base ∧
    b < numBucketsWhp n_max

private theorem readPacked_mkBktMetaRt_eq {c U V w n_max base b : ℕ}
    (hth : whpThreshold c ≤ n_max) (f : ℕ) :
    readPackedGenProg (mkBktMetaRt c U V w n_max base, 16 * b + f) =
      readBktFieldGenProg (((mkWhpCoreParams c U V w n_max, base), b), f) := by
  unfold readBktFieldGenProg
  simp only [pure_bind, wp_large_offBktMeta hth, wp_large_globalPtrBits hth, wp_large_w hth,
    mkBktMetaRt]

private theorem writePacked_mkBktMetaRt_eq {c U V w n_max base b : ℕ}
    (hth : whpThreshold c ≤ n_max) (f v : ℕ) :
    writePackedGenProg ((mkBktMetaRt c U V w n_max base, 16 * b + f), v) =
      writeBktFieldGenProg ((((mkWhpCoreParams c U V w n_max, base), b), f), v) := by
  unfold writeBktFieldGenProg
  simp only [pure_bind, wp_large_offBktMeta hth, wp_large_globalPtrBits hth, wp_large_w hth,
    mkBktMetaRt]

/-- Shared `FastStateStep` combinator for reading two bucket fields and branching into an action
or a no-op `pure ()`. -/
private theorem readTwoBktFields_if_fastStep {c U V w n_max base b f1 f2 C : ℕ}
    {θ : SeedWhp c U n_max} {fs fsTrue : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hb : b < numBucketsWhp n_max) (hf1 : f1 < 10) (hf2 : f2 < 10)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem)
    (P : ℕ → ℕ → Prop) [∀ a b, Decidable (P a b)]
    (body : Memory.Prog Unit)
    (hbody : P (getBktField fs b f1) (getBktField fs b f2) →
      memoryCost body s ≤ C ∧
      ValidProg w (base + largeSpaceWhp c U V w n_max) s body ∧
      FastStateStep base c U V w n_max θ fsTrue s ((Memory.spec 0).clientState s body)) :
    let cp := mkWhpCoreParams c U V w n_max
    let prog : Memory.Prog Unit :=
      readBktFieldGenProg (((cp, base), b), f1) >>= fun v1 =>
        readBktFieldGenProg (((cp, base), b), f2) >>= fun v2 =>
          if P v1 v2 then body else pure ()
    let s' := (Memory.spec 0).clientState s prog
    let fs' := if P (getBktField fs b f1) (getBktField fs b f2) then fsTrue else fs
    memoryCost prog s ≤ C + 4 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ fs' s s' := by
  have h1 := ReadSpec.of (readBktFieldGenProg_spec henv hb hf1 hrep (s := s))
  have h2 := ReadSpec.of (readBktFieldGenProg_spec henv hb hf2 hrep (s := s))
  dsimp only
  by_cases hcond : P (getBktField fs b f1) (getBktField fs b f2)
  · have hbd := hbody hcond
    rw [ite_eq_left hcond]
    exact StepSpec.toAnd_le (h1.thenStep <| h2.thenStep <| .if_pos hcond (.of_le hbd))
      (by have := hbd.1; omega)
  · rw [ite_eq_right hcond]
    exact StepSpec.toAnd_le (h1.thenStep <| h2.thenStep <| .if_neg hcond (.pure hseed hrep ()))
      (by omega)

/-- Set `(overmarsActive b, overmarsCursor b, overmarsInsCount b) := (actVal, 0, 0)` on `BktMetaRt`
(`d = ((bm, b), actVal)`). -/
@[irreducible] def setOvermarsActRtProg : (BktMetaRt × ℕ) × ℕ → Memory.Prog Unit
  | ((bm, b), actVal) => do
    let z0 ← pure 0
    let i5 ← pure (16 * b + 5)
    let i6 ← pure (16 * b + 6)
    let i7 ← pure (16 * b + 7)
    writePackedGenProg ((bm, i5), actVal)
    writePackedGenProg ((bm, i6), z0)
    writePackedGenProg ((bm, i7), z0)

theorem realizes_setOvermarsActRt :
    Realizes .exact setOvermarsActRtProg
      (WordEncoding.encode (α := (BktMetaRt × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((bm, b), _) _ => BktMetaBucketEnv w bm b)
      (fun _ _ => 0) := by
  unfold setOvermarsActRtProg
  have hwp := realizes_writePackedGen
  realize
  all_goals (
    rcases d with ⟨⟨bm, b⟩, actVal⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, base, henv, rfl, hb⟩ := h
    obtain rfl := henv.2.2.1
    have h16M := sixteen_mul_numBuckets_le_n_max henv.2.2.2.1
    dsimp only [mkBktMetaRt] at *
    first
    | exact henv.fits_const (by decide)
    | exact henv.fits_of_le_n_max (by omega)
    | exact henv.bktMeta_safe (by omega)
  )

theorem setOvermarsActRtProg_fastStep {c U V w n_max base b actVal : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hb : b < numBucketsWhp n_max) (hact_le : actVal ≤ n_max)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := setOvermarsActRtProg ((mkBktMetaRt c U V w n_max base, b), actVal)
    let s' := (Memory.spec 0).clientState s prog
    memoryCost prog s = 12 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ
      { fs with
        overmarsActive := Function.update fs.overmarsActive b actVal
        overmarsCursor := Function.update fs.overmarsCursor b 0
        overmarsInsCount := Function.update fs.overmarsInsCount b 0 } s s' := by
  have h1 := StepSpec.of
    (writeBktFieldGenProg_fastStep henv hb (by decide : 5 < 10) hact_le hseed hrep (s := s))
  have h2 := StepSpec.of (writeBktFieldGenProg_fastStep henv hb (by decide : 6 < 10)
    (Nat.zero_le n_max) h1.step.2.1 h1.step.2.2.1)
  have h3 := StepSpec.of (writeBktFieldGenProg_fastStep henv hb (by decide : 7 < 10)
    (Nat.zero_le n_max) h2.step.2.1 h2.step.2.2.1)
  dsimp only
  unfold setOvermarsActRtProg
  simp only [pure_bind, writePacked_mkBktMetaRt_eq henv.2.2.2.1]
  exact StepSpec.toAnd (h1.bind (h2.bind h3)) rfl

/-- Swap `liveRole b` and `overmarsRole b` and set `liveInsCount b := overmarsInsCount b` on
`BktMetaRt` (`d = (bm, b)`). -/
@[irreducible] private def overmarsSwapRolesRtProg : BktMetaRt × ℕ → Memory.Prog Unit
  | (bm, b) => do
    let i2 ← pure (16 * b + 2)
    let i3 ← pure (16 * b + 3)
    let i4 ← pure (16 * b + 4)
    let i7 ← pure (16 * b + 7)
    let oldLive ← readPackedGenProg (bm, i2)
    let oldOm ← readPackedGenProg (bm, i4)
    let omIns ← readPackedGenProg (bm, i7)
    writePackedGenProg ((bm, i2), oldOm)
    writePackedGenProg ((bm, i4), oldLive)
    writePackedGenProg ((bm, i3), omIns)

private theorem realizes_overmarsSwapRolesRt :
    Realizes .exact overmarsSwapRolesRtProg
      (WordEncoding.encode (α := BktMetaRt × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (bm, b) _ => BktMetaBucketEnv w bm b)
      (fun _ _ => 0) := by
  unfold overmarsSwapRolesRtProg
  have hrp := realizes_readPackedGen
  have hwp := realizes_writePackedGen
  realize
  all_goals (
    rcases d with ⟨bm, b⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, base, henv, rfl, hb⟩ := h
    obtain rfl := henv.2.2.1
    have h16M := sixteen_mul_numBuckets_le_n_max henv.2.2.2.1
    dsimp only [mkBktMetaRt] at *
    first
    | exact henv.fits_const (by decide)
    | exact henv.fits_of_le_n_max (by omega)
    | exact henv.bktMeta_safe (by omega)
  )

private theorem overmarsSwapRolesRtProg_fastStep {c U V w n_max base b : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hb : b < numBucketsWhp n_max)
    (hlr : fs.liveRole b ≤ n_max) (hor : fs.overmarsRole b ≤ n_max)
    (hins : fs.overmarsInsCount b ≤ n_max)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := overmarsSwapRolesRtProg (mkBktMetaRt c U V w n_max base, b)
    let s' := (Memory.spec 0).clientState s prog
    memoryCost prog s = 18 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ
      { fs with
        liveRole := Function.update fs.liveRole b (fs.overmarsRole b)
        overmarsRole := Function.update fs.overmarsRole b (fs.liveRole b)
        liveInsCount := Function.update fs.liveInsCount b (fs.overmarsInsCount b) } s s' := by
  have hw1 := StepSpec.of
    (writeBktFieldGenProg_fastStep henv hb (by decide : 2 < 10) hor hseed hrep (s := s))
  have hw2 := StepSpec.of (writeBktFieldGenProg_fastStep henv hb (by decide : 4 < 10) hlr
    hw1.step.2.1 hw1.step.2.2.1)
  have hw3 := StepSpec.of (writeBktFieldGenProg_fastStep henv hb (by decide : 3 < 10) hins
    hw2.step.2.1 hw2.step.2.2.1)
  dsimp only
  unfold overmarsSwapRolesRtProg
  simp only [pure_bind, readPacked_mkBktMetaRt_eq henv.2.2.2.1,
    writePacked_mkBktMetaRt_eq henv.2.2.2.1]
  exact StepSpec.toAnd
    (ReadSpec.thenStep (.of (readBktFieldGenProg_spec henv hb (by decide : 2 < 10) hrep)) <|
      ReadSpec.thenStep (.of (readBktFieldGenProg_spec henv hb (by decide : 4 < 10) hrep)) <|
      ReadSpec.thenStep (.of (readBktFieldGenProg_spec henv hb (by decide : 7 < 10) hrep)) <|
      hw1.bind (hw2.bind hw3)) rfl

/-- Inner activation action of `overmarsStep` (`d = ((cp, base), b)`). -/
@[irreducible] private def overmarsDoActivateGenProg : (WhpCoreParams × ℕ) × ℕ → Memory.Prog Unit
  | ((cp, base), b) => do
    let z1 ← pure 1
    let omRole ← readBktFieldGenProg (((cp, base), b), 4)
    let omIdx ← pure (3 * b + omRole)
    let bm ← mkBktMetaRtProg (cp, base)
    setOvermarsActRtProg ((bm, b), z1)
    resetBTreeSliceGenProg ((cp, base), omIdx)

private theorem realizes_overmarsDoActivateGen :
    Realizes .exact overmarsDoActivateGenProg
      (WordEncoding.encode (α := (WhpCoreParams × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((cp, base), b) s =>
        ∃ (c U V w₀ n_max : ℕ) (fs : FastState),
          WhpLargeEnv c U V w₀ n_max w base ∧
          cp = mkWhpCoreParams c U V w₀ n_max ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          b < numBucketsWhp n_max ∧
          fs.overmarsRole b < 3)
      (fun _ _ => 0) := by
  unfold overmarsDoActivateGenProg
  have hrb := realizes_readBktFieldGen
  have hmb := realizes_mkBktMetaRt
  have hsa := realizes_setOvermarsActRt
  have hrs := realizes_resetBTreeSliceGen
  realize
  all_goals (
    rcases d with ⟨⟨cp, base⟩, b⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, fs, henv, rfl, hrep, hb, hor⟩ := h
    obtain rfl := henv.2.2.1
    have hth := henv.2.2.2.1
    have h3M := (large_index_bounds hth).2.2.2.2.1
    obtain ⟨h4_st, h4_res, _, _⟩ :=
      readBktFieldGenProg_spec henv hb (by decide : 4 < 10) hrep (s := s)
    simp only [getBktField] at h4_res
    obtain ⟨hmb_st, hmb_res, _, _⟩ := mkBktMetaRtProg_spec (c := c) (U := U) (V := V)
      (w := w) (n_max := n_max) (base := base) hth s
    simp only [h4_st, h4_res, hmb_st, hmb_res] at *
    try simp only [wp_large_M hth] at *
    first
    | decide
    | trivial
    | exact henv.fits_const (by decide)
    | exact henv.fits_of_le_n_max (by omega)
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | exact ⟨c, U, V, w, n_max, base, henv, rfl, hb⟩
    | omega
  )

/-- Activation substep of `overmarsStep` on bucket `b` (`d = ((cp, base), b)`). -/
@[irreducible] private def overmarsActivateGenProg : (WhpCoreParams × ℕ) × ℕ → Memory.Prog Unit
  | ((cp, base), b) => do
    let z0 ← pure 0
    let act ← readBktFieldGenProg (((cp, base), b), 5)
    let lic ← readBktFieldGenProg (((cp, base), b), 3)
    if act = z0 ∧ wpOvermarsThresh cp ≤ lic then
      overmarsDoActivateGenProg ((cp, base), b)
    else
      pure ()

private theorem realizes_overmarsActivateGen :
    Realizes .exact overmarsActivateGenProg
      (WordEncoding.encode (α := (WhpCoreParams × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((cp, base), b) s =>
        ∃ (c U V w₀ n_max : ℕ) (fs : FastState),
          WhpLargeEnv c U V w₀ n_max w base ∧
          cp = mkWhpCoreParams c U V w₀ n_max ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          b < numBucketsWhp n_max ∧
          fs.overmarsRole b < 3)
      (fun _ _ => 0) := by
  unfold overmarsActivateGenProg
  have hrb := realizes_readBktFieldGen
  have hda := realizes_overmarsDoActivateGen
  realize
  all_goals (
    rcases d with ⟨⟨cp, base⟩, b⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, fs, henv, rfl, hrep, hb, hor⟩ := h
    obtain rfl := henv.2.2.1
    have hth := henv.2.2.2.1
    obtain ⟨h5_st, _, _, _⟩ :=
      readBktFieldGenProg_spec henv hb (by decide : 5 < 10) hrep (s := s)
    obtain ⟨h3_st, _, _, _⟩ :=
      readBktFieldGenProg_spec henv hb (by decide : 3 < 10) hrep (s := s)
    simp only [h5_st, h3_st] at *
    try simp only [wp_large_M hth] at *
    first
    | decide
    | exact henv.fits_const (by decide)
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | exact hb
    | exact ⟨c, U, V, w, n_max, fs, henv, rfl, hrep, hb, hor⟩
  )

private theorem overmarsActivateGenProg_fastStep {c U V w n_max base b : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hb : b < numBucketsWhp n_max) (hor : fs.overmarsRole b < 3)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := overmarsActivateGenProg ((mkWhpCoreParams c U V w n_max, base), b)
    let s' := (Memory.spec 0).clientState s prog
    let fs0 : FastState :=
      if fs.overmarsActive b = 0 ∧ 5 * (slabScale n_max) ^ 12 ≤ fs.liveInsCount b then
        let omIdx := fs.overmarsSliceIdx b
        { fs with
          overmarsActive := Function.update fs.overmarsActive b 1
          overmarsCursor := Function.update fs.overmarsCursor b 0
          overmarsInsCount := Function.update fs.overmarsInsCount b 0
          slices := Function.update fs.slices omIdx (resetBTreeSlice (fs.slices omIdx)) }
      else fs
    memoryCost prog s ≤ 26 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ fs0 s s' := by
  have hth := henv.2.2.2.1
  have hn1 : 1 ≤ n_max := by have := four_le_of_whpThreshold_le hth; omega
  have homIdx : fs.overmarsSliceIdx b < 3 * numBucketsWhp n_max := by
    unfold FastState.overmarsSliceIdx; omega
  unfold overmarsActivateGenProg
  simp only [wp_large_overmarsThresh hth, pure_bind]
  refine readTwoBktFields_if_fastStep henv hb (by decide : 5 < 10) (by decide : 3 < 10)
    hseed hrep (fun act lic => act = 0 ∧ 5 * (slabScale n_max) ^ 12 ≤ lic)
    (overmarsDoActivateGenProg ((mkWhpCoreParams c U V w n_max, base), b)) fun _ => ?_
  have hsa := StepSpec.of (setOvermarsActRtProg_fastStep henv hb hn1 hseed hrep (s := s))
  have hrs := StepSpec.of
    (resetBTreeSliceGenProg_fastStep henv homIdx hsa.step.2.1 hsa.step.2.2.1)
  unfold overmarsDoActivateGenProg
  simp only [pure_bind]
  exact StepSpec.toAnd_le
    (ReadSpec.thenStep (.of (readBktFieldGenProg_spec henv hb (by decide : 4 < 10) hrep)) <|
      ReadSpec.thenStep
        (.of (mkBktMetaRtProg_spec (U := U) (V := V) (w := w) (base := base) hth s)) <|
      hsa.bind hrs) (by omega)

/-! ## Section 2: Coordinate Scan Step and Bounded-Fuel Scan Loop -/

/-- Evaluate `inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) (fs.locState b loc)`
(`d = (((cp, base), b), loc)`), returning `1` or `0` without mutating memory. -/
@[irreducible] private def checkCoordInLiveGenProg :
    ((WhpCoreParams × ℕ) × ℕ) × ℕ → Memory.Prog ℕ
  | (((cp, base), b), loc) => do
    let stg ← readHdrProg (base, hdrRebStage)
    let oldEp ← readOldEpProg base
    let doneB ← readBktFieldGenProg (((cp, base), b), 8)
    let st ← readFastLocGenProg (((cp, base), b), loc)
    inLiveTreeProg ((stg, oldEp), (doneB, st))

private theorem realizes_checkCoordInLiveGen :
    Realizes .exact checkCoordInLiveGenProg
      (WordEncoding.encode (α := ((WhpCoreParams × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w (((cp, base), b), loc) s =>
        ∃ (c U V w₀ n_max : ℕ) (fs : FastState),
          WhpLargeEnv c U V w₀ n_max w base ∧
          cp = mkWhpCoreParams c U V w₀ n_max ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          (fs.curEp = 0 ∨ fs.curEp = 1) ∧
          b < numBucketsWhp n_max ∧
          loc < totalLocalCoordsWhp n_max)
      (fun _ _ => 0) := by
  unfold checkCoordInLiveGenProg
  have hrh := realizes_readHdr
  have hro := realizes_readOldEp
  have hrb := realizes_readBktFieldGen
  have hrl := realizes_readFastLocGen
  have hil := realizes_inLiveTree
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, base⟩, b⟩, loc⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, fs, henv, rfl, hrep, hce_or, hb, hloc⟩ := h
    obtain rfl := henv.2.2.1
    have hth := henv.2.2.2.1
    have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
    have hw2 : 2 ≤ w := by linarith [le_bMinWhp c, bMinWhp_le_log hth, henv.log_lt_w]
    obtain ⟨hst_st, _, _, _⟩ := readHdrProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrRebStage) (s := s)
      (by dsimp only [hdrRebStage]; omega)
    obtain ⟨hro_st, hro_res, _, _⟩ := readOldEpProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max)
      (by dsimp [hdrCurEp]; omega) hce_or hrep.2.2.2.1 (s := s)
    obtain ⟨hd8_st, _, _, _⟩ :=
      readBktFieldGenProg_spec henv hb (by decide : 8 < 10) hrep (s := s)
    obtain ⟨hlc_st, _, _, _⟩ := readFastLocGenProg_spec henv hb hloc hrep (s := s)
    have hold_le1 : fs.oldEp ≤ 1 := by
      rcases hce_or with h0 | h1 <;> simp [FastState.oldEp, *]
    simp only [hst_st, hro_st, hro_res, hd8_st, hlc_st] at *
    try simp only [wp_large_M hth, wp_large_totalLoc hth] at *
    first
    | decide
    | exact henv.fits_const (by decide)
    | exact henv.fits_hdr_addr (by decide)
    | exact hw2
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | exact hb
    | exact hloc
    | exact hold_le1
  )

private theorem checkCoordInLiveGenProg_spec {c U V w n_max base b loc : ℕ}
    {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hrep : FastMemRep base c U V w n_max fs s.mem)
    (hce_or : fs.curEp = 0 ∨ fs.curEp = 1)
    (hb : b < numBucketsWhp n_max) (hloc : loc < totalLocalCoordsWhp n_max) :
    let prog := checkCoordInLiveGenProg (((mkWhpCoreParams c U V w n_max, base), b), loc)
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog =
      (if inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) (fs.locState b loc) then 1 else 0) ∧
    memoryCost prog s = 6 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  have hst := readHdrProg_spec (w := w) (F := base + largeSpaceWhp c U V w n_max) (base := base)
    (hdrOff := hdrRebStage) (s := s) (by dsimp only [largeSpaceWhp, hdrRebStage]; omega)
  rw [hrep.2.2.2.2.2.1] at hst
  dsimp only
  unfold checkCoordInLiveGenProg
  exact ReadSpec.toAnd ((ReadSpec.of hst).bind <|
    .bind (.of (readOldEpProg_spec (by dsimp only [largeSpaceWhp, hdrCurEp]; omega) hce_or
      hrep.2.2.2.1)) <|
    .bind (.of (readBktFieldGenProg_spec henv hb (by decide : 8 < 10) hrep)) <|
    .bind (.of (readFastLocGenProg_spec henv hb hloc hrep)) <| .of inLiveTreeProg_spec) rfl rfl

/-- Read `(bktSalt b, (3 * b + overmarsRole b, overmarsInsCount b))` (`d = ((cp, base), b)`). -/
@[irreducible] private def overmarsReadScanInfoGenProg :
    (WhpCoreParams × ℕ) × ℕ → Memory.Prog (ℕ × (ℕ × ℕ))
  | ((cp, base), b) => do
    let f1 ← pure 1
    let f4 ← pure 4
    let f7 ← pure 7
    let salt ← readBktFieldGenProg (((cp, base), b), f1)
    let omRole ← readBktFieldGenProg (((cp, base), b), f4)
    let omIns ← readBktFieldGenProg (((cp, base), b), f7)
    let omIdx ← pure (3 * b + omRole)
    pure (salt, (omIdx, omIns))

private theorem realizes_overmarsReadScanInfoGen :
    Realizes .exact overmarsReadScanInfoGenProg
      (WordEncoding.encode (α := (WhpCoreParams × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      (fun w ((cp, base), b) s =>
        ∃ (c U V w₀ n_max : ℕ) (fs : FastState),
          WhpLargeEnv c U V w₀ n_max w base ∧
          cp = mkWhpCoreParams c U V w₀ n_max ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          b < numBucketsWhp n_max ∧
          fs.overmarsRole b < 3)
      (fun _ _ => 0) := by
  unfold overmarsReadScanInfoGenProg
  have hrb := realizes_readBktFieldGen
  realize
  all_goals (
    rcases d with ⟨⟨cp, base⟩, b⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, fs, henv, rfl, hrep, hb, hor⟩ := h
    obtain rfl := henv.2.2.1
    have hth := henv.2.2.2.1
    have h3M := (large_index_bounds hth).2.2.2.2.1
    obtain ⟨h1_st, _, _, _⟩ := readBktFieldGenProg_spec henv hb (by decide : 1 < 10) hrep (s := s)
    obtain ⟨h4_st, h4_res, _, _⟩ :=
      readBktFieldGenProg_spec henv hb (by decide : 4 < 10) hrep (s := s)
    obtain ⟨h7_st, _, _, _⟩ := readBktFieldGenProg_spec henv hb (by decide : 7 < 10) hrep (s := s)
    simp only [getBktField] at h4_res
    simp only [h1_st, h4_st, h4_res, h7_st, wp_large_M hth] at *
    first
    | decide
    | assumption
    | exact henv.fits_const (by decide)
    | exact henv.fits_of_le_n_max (by omega)
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
  )

private theorem overmarsReadScanInfoGenProg_spec {c U V w n_max base b : ℕ}
    {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hb : b < numBucketsWhp n_max)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := overmarsReadScanInfoGenProg ((mkWhpCoreParams c U V w n_max, base), b)
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog =
      (fs.bktSalt b, (fs.overmarsSliceIdx b, fs.overmarsInsCount b)) ∧
    memoryCost prog s = 6 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  dsimp only
  unfold overmarsReadScanInfoGenProg
  simp only [pure_bind]
  exact ReadSpec.toAnd
    (ReadSpec.bind (.of (readBktFieldGenProg_spec henv hb (by decide : 1 < 10) hrep)) <|
      .bind (.of (readBktFieldGenProg_spec henv hb (by decide : 4 < 10) hrep)) <|
      .bind (.of (readBktFieldGenProg_spec henv hb (by decide : 7 < 10) hrep)) <| .pure _) rfl rfl

/-- Write `(overmarsCursor b, overmarsInsCount b) := (cur1, omIns1)` via `BktMetaRt`. -/
@[irreducible] private def overmarsWriteCurInsRtProg :
    ((BktMetaRt × ℕ) × ℕ) × ℕ → Memory.Prog Unit
  | (((bm, b), cur1), omIns1) => do
    let i6 ← pure (16 * b + 6)
    let i7 ← pure (16 * b + 7)
    writePackedGenProg ((bm, i6), cur1)
    writePackedGenProg ((bm, i7), omIns1)

private theorem realizes_overmarsWriteCurInsRt :
    Realizes .exact overmarsWriteCurInsRtProg
      (WordEncoding.encode (α := ((BktMetaRt × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (((bm, b), _), _) _ => BktMetaBucketEnv w bm b)
      (fun _ _ => 0) := by
  unfold overmarsWriteCurInsRtProg
  have hwp := realizes_writePackedGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨bm, b⟩, cur1⟩, omIns1⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, base, henv, rfl, hb⟩ := h
    obtain rfl := henv.2.2.1
    have h16M := sixteen_mul_numBuckets_le_n_max henv.2.2.2.1
    dsimp only [mkBktMetaRt] at *
    first
    | exact henv.fits_const (by decide)
    | exact henv.fits_of_le_n_max (by omega)
    | exact henv.bktMeta_safe (by omega)
  )

private theorem overmarsWriteCurInsRtProg_fastStep {c U V w n_max base b cur1 omIns1 : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hb : b < numBucketsWhp n_max) (hcur_le : cur1 ≤ n_max) (hins_le : omIns1 ≤ n_max)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := overmarsWriteCurInsRtProg (((mkBktMetaRt c U V w n_max base, b), cur1), omIns1)
    let s' := (Memory.spec 0).clientState s prog
    memoryCost prog s = 8 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ
      { fs with
        overmarsCursor := Function.update fs.overmarsCursor b cur1
        overmarsInsCount := Function.update fs.overmarsInsCount b omIns1 } s s' := by
  have h1 := StepSpec.of
    (writeBktFieldGenProg_fastStep henv hb (by decide : 6 < 10) hcur_le hseed hrep (s := s))
  have h2 := StepSpec.of (writeBktFieldGenProg_fastStep henv hb (by decide : 7 < 10) hins_le
    h1.step.2.1 h1.step.2.2.1)
  dsimp only
  unfold overmarsWriteCurInsRtProg
  simp only [pure_bind, writePacked_mkBktMetaRt_eq henv.2.2.2.1]
  exact StepSpec.toAnd (h1.bind h2) rfl

/-- Precondition for one Overmars scan step (`p = (((wp, base), b), ())`). -/
private def OvermarsScanOnePre (w : ℕ) (p : ((WhpParams × ℕ) × ℕ) × Unit)
    (s : Memory.State) : Prop :=
  let ((wp, base), b) := p.1
  ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState) (omMap : ℕ → Option ℕ),
    WhpLargeEnv c U V w₀ n_max w base ∧
    wp = mkWhpParams c U V w₀ n_max ∧
    SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
    FastMemRep base c U V w₀ n_max fs s.mem ∧
    b < numBucketsWhp n_max ∧
    (fs.curEp = 0 ∨ fs.curEp = 1) ∧
    fs.overmarsRole b < 3 ∧
    fs.bktCount b ≤ totalLocalCoordsWhp n_max ∧
    fs.overmarsCursor b < n_max ∧
    fs.overmarsInsCount b < 8 * (slabScale n_max) ^ 12 ∧
    (∀ i < n_max, fs.quotArr i < 2 ^ quotBitsWhp U n_max) ∧
    (∀ k < fs.bktCount b - capFrontWhp n_max, fs.backPtr b k < poolSizeWhp n_max) ∧
    ValidWhpSlice n_max (fs.overmarsInsCount b) (fs.slices (fs.overmarsSliceIdx b)) omMap

/-- Insert `(fpAt salt b cur, cur)` into `overmarsSlice` and advance
`(overmarsCursor, overmarsInsCount)`. -/
@[irreducible] private def overmarsInsertCoordGenProg :
    ((WhpParams × ℕ) × ℕ) × ℕ → Memory.Prog Unit
  | (((wp, base), b), cur) => do
    let info ← overmarsReadScanInfoGenProg ((wp.1, base), b)
    let fp ← fpAtGenProg ((((wp, base), info.1), b), cur)
    btreeInsertGenProg ((((wp.1, base), info.2.1), fp), cur)
    let bm ← mkBktMetaRtProg (wp.1, base)
    let cur1 ← pure (cur + 1)
    let omIns1 ← pure (info.2.2 + 1)
    overmarsWriteCurInsRtProg (((bm, b), cur1), omIns1)

private theorem realizes_overmarsInsertCoordGen :
    Realizes .exact overmarsInsertCoordGenProg
      (WordEncoding.encode (α := ((WhpParams × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (((wp, base), b), cur) s =>
        OvermarsScanOnePre w (((wp, base), b), ()) s ∧
        cur = readPacked (base + wpOffBktMeta wp.1) (wpGlobalPtrBits wp.1) (wpW wp.1)
          s.mem (16 * b + 6) ∧
        cur < readPacked (base + wpOffBktMeta wp.1) (wpGlobalPtrBits wp.1) (wpW wp.1)
          s.mem (16 * b + 0))
      (fun _ _ => 0) := by
  unfold overmarsInsertCoordGenProg
  have hri := realizes_overmarsReadScanInfoGen
  have hfp := realizes_fpAtGen
  have hbi := realizes_btreeInsertGen
  have hmb := realizes_mkBktMetaRt
  have hwc := realizes_overmarsWriteCurInsRt
  realize
  all_goals (
    rcases d with ⟨⟨⟨wp, base⟩, b⟩, cur⟩
    dsimp only at *
    simp only [Prod.mk.eta] at *
    obtain ⟨⟨c, U, V, w₀, n_max, θ, fs, omMap, henv, rfl, hseed, hrep, hb, _, hor,
      hcnt_le, hcur_n, hins_lt, hq_all, hbp_v, hv_om⟩, hcur_eq0, hcur_lt0⟩ := h
    obtain rfl := henv.2.2.1
    have hth := henv.2.2.2.1
    have hcp_eq : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
      simp [mkWhpParams, Nat.not_lt.mpr hth]
    have hbm := hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 b hb
    simp only [hcp_eq, wp_large_offBktMeta hth, wp_large_globalPtrBits hth, wp_large_w hth,
      hbm.2.2.2.2.2.2.1, hbm.1] at hcur_eq0 hcur_lt0
    have hcur_tot : cur < totalLocalCoordsWhp n_max := hcur_lt0.trans_le hcnt_le
    have hcur_val : cur < 2 ^ valLaneBitsWhp n_max := by
      have htl3 := totalLocalCoordsWhp_le_three_mul (n_max := n_max)
      rw [two_pow_valLaneBitsWhp]; omega
    have h8L12_n : 8 * (slabScale n_max) ^ 12 ≤ n_max :=
      (Nat.mul_le_mul_right _ (by linarith [(large_bounds_lt_n_max hth).1])).trans
        (numBucketsWhp_mul_scale_pow12_le hth)
    have h3M := (large_index_bounds hth).2.2.2.2.1
    obtain ⟨hri_st, hri_res, _, _⟩ := overmarsReadScanInfoGenProg_spec henv hb hrep (s := s)
    have hbp_cur : capFrontWhp n_max ≤ cur → fs.backPtr b (cur - capFrontWhp n_max) <
        poolSizeWhp n_max := fun hcf => hbp_v _ (by omega)
    obtain ⟨hfp_st, hfp_res, _, _⟩ :=
      fpAtGenProg_spec henv hseed hrep hb hcur_tot hbp_cur (salt := fs.bktSalt b) (s := s)
    have homIdx : fs.overmarsSliceIdx b < 3 * numBucketsWhp n_max := by
      unfold FastState.overmarsSliceIdx; omega
    obtain ⟨hbi_mc, _, hbi_step⟩ :=
      btreeInsertGenProg_fastStep henv homIdx hins_lt.le hseed hrep hv_om
        (fpAt_lt θ fs (fs.bktSalt b) b cur) hcur_val (s := s)
    obtain ⟨hmb_st, hmb_res, _, _⟩ := mkBktMetaRtProg_spec (c := c) (U := U) (V := V)
      (w := w) (n_max := n_max) (base := base) hth
      ((Memory.spec 0).clientState s
        (btreeInsertGenProg ((((mkWhpCoreParams c U V w n_max, base), fs.overmarsSliceIdx b),
          fs.fpAt c U n_max θ (fs.bktSalt b) b cur), cur)))
    simp only [hcp_eq, hri_st, hri_res, hfp_st, hfp_res, hmb_st, hmb_res] at *
    first
    | exact henv.fits_of_le_n_max (by omega)
    | exact ⟨c, U, V, w, n_max, θ, fs, henv, rfl, hseed, hrep, hq_all, hb, hcur_tot, hbp_cur⟩
    | exact ⟨c, U, V, w, n_max, fs, henv, rfl, hrep, hb, hor⟩
    | exact ⟨c, U, V, w, n_max, fs.overmarsInsCount b, fs.slices (fs.overmarsSliceIdx b), omMap,
        henv, rfl, homIdx, hins_lt.le, hrep.slice_rep homIdx, hv_om,
        fpAt_lt θ fs (fs.bktSalt b) b cur, hcur_val⟩
    | exact ⟨c, U, V, w, n_max, base, henv, rfl, hb⟩
  )

/-- Increment `overmarsCursor b` to `cur + 1` (`d = (((cp, base), b), cur)`). -/
@[irreducible] private def overmarsIncCurGenProg :
    ((WhpCoreParams × ℕ) × ℕ) × ℕ → Memory.Prog Unit
  | (((cp, base), b), cur) => do
    let f6 ← pure 6
    let cur1 ← pure (cur + 1)
    writeBktFieldGenProg ((((cp, base), b), f6), cur1)

private theorem realizes_overmarsIncCurGen :
    Realizes .exact overmarsIncCurGenProg
      (WordEncoding.encode (α := ((WhpCoreParams × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (((cp, base), b), cur) _ =>
        WhpLargeEnvGen w cp base ∧ b < wpM cp ∧ cur < wpNMax cp)
      (fun _ _ => 0) := by
  unfold overmarsIncCurGenProg
  have hwb := realizes_writeBktFieldGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, base⟩, b⟩, cur⟩
    dsimp only at *
    obtain ⟨⟨c, U, V, w₀, n_max, henv, rfl⟩, hb, hcur⟩ := h
    obtain rfl := henv.2.2.1
    have hth := henv.2.2.2.1
    simp only [wp_large_M hth, wp_large_nMax hth] at *
    first
    | decide
    | exact henv.fits_const (by decide)
    | exact henv.fits_of_le_n_max (by omega)
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | exact hb
  )

/-- Read `(overmarsCursor b, bktCount b)` (`d = ((cp, base), b)`). -/
@[irreducible] private def overmarsReadCurCntGenProg :
    (WhpCoreParams × ℕ) × ℕ → Memory.Prog (ℕ × ℕ)
  | ((cp, base), b) => do
    let f6 ← pure 6
    let f0 ← pure 0
    let cur ← readBktFieldGenProg (((cp, base), b), f6)
    let cnt ← readBktFieldGenProg (((cp, base), b), f0)
    pure (cur, cnt)

private theorem clientState_readBktFieldGenProg (x : ((WhpCoreParams × ℕ) × ℕ) × ℕ)
    (s : Memory.State) :
    (Memory.spec 0).clientState s (readBktFieldGenProg x) = s := by
  rcases x with ⟨⟨⟨_, _⟩, _⟩, _⟩
  unfold readBktFieldGenProg
  simp only [pure_bind]
  rfl

private theorem realizes_overmarsReadCurCntGen :
    Realizes .exact overmarsReadCurCntGenProg
      (WordEncoding.encode (α := (WhpCoreParams × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w ((cp, base), b) _ => WhpLargeEnvGen w cp base ∧ b < wpM cp)
      (fun _ _ => 0) := by
  unfold overmarsReadCurCntGenProg
  have hrb := realizes_readBktFieldGen
  have hcs_r := clientState_readBktFieldGenProg
  realize
  all_goals (
    rcases d with ⟨⟨cp, base⟩, b⟩
    dsimp only at *
    obtain ⟨⟨c, U, V, w₀, n_max, henv, rfl⟩, hb⟩ := h
    obtain rfl := henv.2.2.1
    have hth := henv.2.2.2.1
    rw [wp_large_M hth] at hb
    simp only [hcs_r, wp_large_M hth] at *
    first
    | decide
    | exact henv.fits_const (by decide)
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | exact hb
  )

private theorem overmarsReadCurCntGenProg_spec {c U V w n_max base b : ℕ}
    {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hb : b < numBucketsWhp n_max)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := overmarsReadCurCntGenProg ((mkWhpCoreParams c U V w n_max, base), b)
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog = (fs.overmarsCursor b, fs.bktCount b) ∧
    memoryCost prog s = 4 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  dsimp only
  unfold overmarsReadCurCntGenProg
  simp only [pure_bind]
  exact ReadSpec.toAnd
    (ReadSpec.bind (.of (readBktFieldGenProg_spec henv hb (by decide : 6 < 10) hrep)) <|
      .bind (.of (readBktFieldGenProg_spec henv hb (by decide : 0 < 10) hrep)) <| .pure _) rfl rfl

/-- In-bounds coordinate helper for `overmarsScanOneProg` (`d = (((wp, base), b), cur)`). -/
@[irreducible] private def overmarsScanInBoundsProg :
    ((WhpParams × ℕ) × ℕ) × ℕ → Memory.Prog Unit
  | (((wp, base), b), cur) => do
    let z1 ← pure 1
    let inL ← checkCoordInLiveGenProg (((wp.1, base), b), cur)
    if inL = z1 then
      overmarsInsertCoordGenProg (((wp, base), b), cur)
    else
      overmarsIncCurGenProg (((wp.1, base), b), cur)

private theorem realizes_overmarsScanInBounds :
    Realizes .exact overmarsScanInBoundsProg
      (WordEncoding.encode (α := ((WhpParams × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (((wp, base), b), cur) s =>
        OvermarsScanOnePre w (((wp, base), b), ()) s ∧
        cur = readPacked (base + wpOffBktMeta wp.1) (wpGlobalPtrBits wp.1) (wpW wp.1)
          s.mem (16 * b + 6) ∧
        cur < readPacked (base + wpOffBktMeta wp.1) (wpGlobalPtrBits wp.1) (wpW wp.1)
          s.mem (16 * b + 0))
      (fun _ _ => 0) := by
  unfold overmarsScanInBoundsProg
  have hcl := realizes_checkCoordInLiveGen
  have hic := realizes_overmarsInsertCoordGen
  have hinc := realizes_overmarsIncCurGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨wp, base⟩, b⟩, cur⟩
    dsimp only at *
    simp only [Prod.mk.eta] at *
    obtain ⟨⟨c, U, V, w₀, n_max, θ, fs, omMap, henv, rfl, hseed, hrep, hb, hce_or, hor,
      hcnt_le, hcur_n, hins_lt, hq_all, hbp_v, hv_om⟩, hcur_eq0, hcur_lt0⟩ := h
    obtain rfl := henv.2.2.1
    have hth := henv.2.2.2.1
    have hcp_eq : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
      simp [mkWhpParams, Nat.not_lt.mpr hth]
    have hbm := hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 b hb
    simp only [hcp_eq, wp_large_offBktMeta hth, wp_large_globalPtrBits hth, wp_large_w hth,
      hbm.2.2.2.2.2.2.1, hbm.1] at hcur_eq0 hcur_lt0
    have hcur_tot : cur < totalLocalCoordsWhp n_max := hcur_lt0.trans_le hcnt_le
    obtain ⟨hcl_st, _, _, _⟩ :=
      checkCoordInLiveGenProg_spec henv hrep hce_or hb hcur_tot (s := s)
    simp only [hcp_eq, hcl_st] at *
    try simp only [wp_large_M hth, wp_large_nMax hth, wp_large_offBktMeta hth,
      wp_large_globalPtrBits hth, wp_large_w hth] at *
    first
    | exact henv.fits_const (by decide)
    | exact ⟨c, U, V, w, n_max, fs, henv, rfl, hrep, hce_or, hb, hcur_tot⟩
    | exact ⟨c, U, V, w, n_max, θ, fs, omMap, henv, rfl, hseed, hrep, hb, hce_or, hor,
        hcnt_le, hcur_n, hins_lt, hq_all, hbp_v, hv_om⟩
    | exact hbm.2.2.2.2.2.2.1.symm ▸ hcur_eq0
    | exact hbm.1.symm ▸ hcur_lt0
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | exact hb
    | omega
  )

/-- Single coordinate scan step `overmarsScanOneProg` (`p = (((wp, base), b), ())`). -/
private def overmarsScanOneProg : ((WhpParams × ℕ) × ℕ) × Unit → Memory.Prog Unit
  | (((wp, base), b), _) => do
    let cc ← overmarsReadCurCntGenProg ((wp.1, base), b)
    if cc.1 < cc.2 then
      overmarsScanInBoundsProg (((wp, base), b), cc.1)
    else
      overmarsIncCurGenProg (((wp.1, base), b), cc.1)

private theorem memoryCost_overmarsScanOneProg_pos (p : ((WhpParams × ℕ) × ℕ) × Unit)
    (s : Memory.State) :
    1 ≤ memoryCost (overmarsScanOneProg p) s := by
  rcases p with ⟨⟨⟨wp, base⟩, b⟩, ⟨⟩⟩
  unfold overmarsScanOneProg overmarsReadCurCntGenProg readBktFieldGenProg
  simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind,
    memoryCost_readPackedGen]
  omega

private theorem realizes_overmarsScanOne :
    Realizes .exact overmarsScanOneProg
      (WordEncoding.encode (α := ((WhpParams × ℕ) × ℕ) × Unit))
      (WordEncoding.encode (α := Unit))
      OvermarsScanOnePre
      (fun _ _ => 0) := by
  unfold overmarsScanOneProg
  have hrc := realizes_overmarsReadCurCntGen
  have hib := realizes_overmarsScanInBounds
  have hinc := realizes_overmarsIncCurGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨wp, base⟩, b⟩, ⟨⟩⟩
    dsimp only at *
    simp only [Prod.mk.eta] at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, omMap, henv, rfl, hseed, hrep, hb, hce_or, hor,
      hcnt_le, hcur_n, hins_lt, hq_all, hbp_v, hv_om⟩ := h
    obtain rfl := henv.2.2.1
    have hth := henv.2.2.2.1
    have hcp_eq : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
      simp [mkWhpParams, Nat.not_lt.mpr hth]
    obtain ⟨hcc_st, hcc_res, _, _⟩ := overmarsReadCurCntGenProg_spec henv hb hrep (s := s)
    have hbm := hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 b hb
    simp only [hcp_eq, hcc_st, hcc_res] at *
    try simp only [wp_large_M hth, wp_large_nMax hth, wp_large_offBktMeta hth,
      wp_large_globalPtrBits hth, wp_large_w hth] at *
    first
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | exact hb
    | exact ⟨c, U, V, w, n_max, θ, fs, omMap, henv, rfl, hseed, hrep, hb, hce_or, hor,
        hcnt_le, hcur_n, hins_lt, hq_all, hbp_v, hv_om⟩
    | exact hbm.2.2.2.2.2.2.1.symm
    | exact hbm.1.symm ▸ (by omega)
    | exact hcur_n
  )

private theorem overmarsScanOneProg_fastStep {c U V w n_max base b : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {omMap : ℕ → Option ℕ} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hb : b < numBucketsWhp n_max)
    (hce_or : fs.curEp = 0 ∨ fs.curEp = 1)
    (hor : fs.overmarsRole b < 3)
    (hcnt_le : fs.bktCount b ≤ totalLocalCoordsWhp n_max)
    (hcur_n : fs.overmarsCursor b < n_max)
    (hins_lt : fs.overmarsInsCount b < 8 * (slabScale n_max) ^ 12)
    (hbp_v : ∀ k < fs.bktCount b - capFrontWhp n_max, fs.backPtr b k < poolSizeWhp n_max)
    (hv_om : ValidWhpSlice n_max (fs.overmarsInsCount b) (fs.slices (fs.overmarsSliceIdx b)) omMap)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := overmarsScanOneProg (((mkWhpParams c U V w n_max, base), b), ())
    let s' := (Memory.spec 0).clientState s prog
    let fs1 := overmarsScanSteps c U n_max θ b 1 fs
    memoryCost prog s ≤ 2 * hashEvalCostWhp c + 2454 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ fs1 s s' ∧
    fs1.curEp = fs.curEp ∧
    fs1.overmarsRole b = fs.overmarsRole b ∧
    fs1.bktCount b = fs.bktCount b ∧
    fs1.quotArr = fs.quotArr ∧
    fs1.backPtr = fs.backPtr ∧
    fs1.overmarsCursor b = fs.overmarsCursor b + 1 ∧
    fs1.overmarsInsCount b ≤ fs.overmarsInsCount b + 1 ∧
    ∃ omMap1, ValidWhpSlice n_max (fs1.overmarsInsCount b)
      (fs1.slices (fs1.overmarsSliceIdx b)) omMap1 := by
  have hth := henv.2.2.2.1
  have hwp1 : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
    simp [mkWhpParams, Nat.not_lt.mpr hth]
  have hML12 := numBucketsWhp_mul_scale_pow12_le hth
  have hM_ge := (large_bounds_lt_n_max hth).1
  have h8L12_n : 8 * (slabScale n_max) ^ 12 ≤ n_max :=
    (Nat.mul_le_mul_right _ (by omega : 8 ≤ numBucketsWhp n_max)).trans hML12
  have hcc := ReadSpec.of (overmarsReadCurCntGenProg_spec henv hb hrep (s := s))
  set cur := fs.overmarsCursor b
  have hw6 := StepSpec.of (writeBktFieldGenProg_fastStep henv hb (by decide : 6 < 10)
    (by omega : cur + 1 ≤ n_max) hseed hrep (s := s))
  dsimp only
  unfold overmarsScanOneProg overmarsScanInBoundsProg overmarsInsertCoordGenProg
    overmarsIncCurGenProg
  simp only [hwp1, pure_bind]
  dsimp only [overmarsScanSteps]
  by_cases hcur_lt : cur < fs.bktCount b
  · have hcur_tot : cur < totalLocalCoordsWhp n_max := hcur_lt.trans_le hcnt_le
    have hcl := ReadSpec.of (checkCoordInLiveGenProg_spec henv hrep hce_or hb hcur_tot (s := s))
    by_cases hinL : inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) (fs.locState b cur) = true
    · rw [ite_eq_left (⟨hcur_lt, hinL⟩ : _ ∧ _)]
      have hcur_val : cur < 2 ^ valLaneBitsWhp n_max := by
        have htl3 := totalLocalCoordsWhp_le_three_mul (n_max := n_max)
        rw [two_pow_valLaneBitsWhp]; omega
      have hfp := fpAtGenProg_spec henv hseed hrep hb hcur_tot
        (fun hcf => hbp_v _ (by omega)) (salt := fs.bktSalt b) (s := s)
      have homIdx : fs.overmarsSliceIdx b < 3 * numBucketsWhp n_max := by
        unfold FastState.overmarsSliceIdx; omega
      have hbi := btreeInsertGenProg_fastStep henv homIdx hins_lt.le hseed hrep hv_om
        (fpAt_lt θ fs (fs.bktSalt b) b cur) hcur_val (s := s)
      have hbi' := StepSpec.of_le hbi
      have hwc := StepSpec.of (overmarsWriteCurInsRtProg_fastStep henv hb
        (by omega : cur + 1 ≤ n_max) (by omega : fs.overmarsInsCount b + 1 ≤ n_max)
        hbi'.step.2.1 hbi'.step.2.2.1)
      have hv_om1 := (hv_om.insert_spec hth hins_lt.le
        (fpAt_lt θ fs (fs.bktSalt b) b cur) hcur_val).2
      exact StepSpec.toAnd_le_and (hcc.thenStep <| .if_pos hcur_lt <| hcl.thenStep <|
        .if_pos (ite_eq_left hinL) <|
        ReadSpec.thenStep (.of (overmarsReadScanInfoGenProg_spec henv hb hrep)) <|
        ReadSpec.thenStep ⟨hfp.1, hfp.2.1, rfl, hfp.2.2.2⟩ <| hbi'.bind <|
        ReadSpec.thenStep
          (.of (mkBktMetaRtProg_spec (U := U) (V := V) (w := w) (base := base) hth _)) hwc)
        (by dsimp only; have := hfp.2.2.1; have := hbi.1; omega)
        ⟨rfl, rfl, rfl, rfl, rfl, Function.update_self _ _ _, (Function.update_self _ _ _).le,
          _, by simpa only [FastState.overmarsSliceIdx, Function.update_self] using hv_om1⟩
    · rw [ite_eq_right (fun h : _ ∧ _ => hinL h.2)]
      exact StepSpec.toAnd_le_and (hcc.thenStep <| .if_pos hcur_lt <| hcl.thenStep <|
        .if_neg (by rw [ite_eq_right hinL]; decide) hw6) (by omega)
        ⟨rfl, rfl, rfl, rfl, rfl, Function.update_self _ _ _, Nat.le_succ _, omMap, hv_om⟩
  · rw [ite_eq_right (fun h : _ ∧ _ => hcur_lt h.1)]
    exact StepSpec.toAnd_le_and (hcc.thenStep <| .if_neg hcur_lt hw6) (by omega)
      ⟨rfl, rfl, rfl, rfl, rfl, Function.update_self _ _ _, Nat.le_succ _, omMap, hv_om⟩

/-- Bounded-fuel Overmars scan loop via `Realizes.iterate₀`. -/
@[irreducible] private def overmarsScanLoopGenProg (p : (((WhpParams × ℕ) × ℕ) × Unit) × ℕ) :
    Memory.Prog Unit :=
  iterate overmarsScanOneProg p.1.1 p.2 p.1.2

private theorem realizes_overmarsScanLoopGen :
    Realizes .exact overmarsScanLoopGenProg
      (WordEncoding.encode (α := (((WhpParams × ℕ) × ℕ) × Unit) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w p s => iterationSafe overmarsScanOneProg OvermarsScanOnePre w p.1.1 p.2 p.1.2 s)
      (fun _ _ => 0) := by
  unfold overmarsScanLoopGenProg
  exact Realizes.iterate₀
    (WordEncoding.encode (α := (WhpParams × ℕ) × ℕ))
    (WordEncoding.encode (α := Unit))
    realizes_overmarsScanOne
    memoryCost_overmarsScanOneProg_pos

private theorem overmarsScanLoopGenProg_spec {c U V w n_max base b : ℕ}
    {θ : SeedWhp c U n_max}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hb : b < numBucketsWhp n_max) :
    let d0 := ((mkWhpParams c U V w n_max, base), b)
    ∀ rem (fs : FastState) (omMap : ℕ → Option ℕ) (s : Memory.State),
      (fs.curEp = 0 ∨ fs.curEp = 1) →
      fs.overmarsRole b < 3 →
      fs.bktCount b ≤ totalLocalCoordsWhp n_max →
      fs.overmarsCursor b + rem ≤ n_max →
      fs.overmarsInsCount b + rem ≤ 8 * (slabScale n_max) ^ 12 →
      (∀ i < n_max, fs.quotArr i < 2 ^ quotBitsWhp U n_max) →
      (∀ k < fs.bktCount b - capFrontWhp n_max, fs.backPtr b k < poolSizeWhp n_max) →
      ValidWhpSlice n_max (fs.overmarsInsCount b) (fs.slices (fs.overmarsSliceIdx b)) omMap →
      SeedWhpMemRep base c U w n_max θ s.mem →
      FastMemRep base c U V w n_max fs s.mem →
      let prog := overmarsScanLoopGenProg ((d0, ()), rem)
      let s' := (Memory.spec 0).clientState s prog
      let fs' := overmarsScanSteps c U n_max θ b rem fs
      iterationSafe overmarsScanOneProg OvermarsScanOnePre w d0 rem () s ∧
      memoryCost prog s ≤ rem * (2 * hashEvalCostWhp c + 2454) ∧
      ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
      FastStateStep base c U V w n_max θ fs' s s' := by
  intro d0 rem
  induction rem with
  | zero =>
    intro fs omMap s _ _ _ _ _ _ _ _ hseed hrep
    unfold overmarsScanLoopGenProg
    exact ⟨trivial, Nat.zero_le _, validProg_pure _, FastStateStep.refl hseed hrep⟩
  | succ rem ih =>
    intro fs omMap s hce hor hcnt hcur_n hins_ub hq_all hbp_v hv_om hseed hrep
    have hpre1 : OvermarsScanOnePre w (d0, ()) s :=
      ⟨c, U, V, w, n_max, θ, fs, omMap, henv, rfl, hseed, hrep, hb, hce, hor,
        hcnt, by omega, by omega, hq_all, hbp_v, hv_om⟩
    obtain ⟨hmc1, hvp1, hstep1, hce1, hor1, hcnt1, hq1, hbp1, hcur1, hins1, omMap1, hv_om1⟩ :=
      overmarsScanOneProg_fastStep henv hb hce hor hcnt (by omega) (by omega) hbp_v hv_om
        hseed hrep (s := s)
    set s1 := (Memory.spec 0).clientState s (overmarsScanOneProg (d0, ()))
    set fs1 := overmarsScanSteps c U n_max θ b 1 fs
    obtain ⟨hsafe_r, hmc_r, hvp_r, hstep_r⟩ :=
      ih fs1 omMap1 s1 (hce1 ▸ hce) (hor1 ▸ hor) (hcnt1 ▸ hcnt)
        (by omega) (by omega) (fun i hi => hq1 ▸ hq_all i hi)
        (fun k hk => hbp1 ▸ hbp_v k (hcnt1 ▸ hk)) hv_om1 hstep1.2.1 hstep1.2.2.1
    dsimp only
    unfold overmarsScanLoopGenProg at hmc_r hvp_r hstep_r ⊢
    dsimp only [iterate] at hmc_r hvp_r hstep_r ⊢
    rw [clientState_bind]
    refine ⟨⟨hpre1, ?_⟩, ?_, validProg_bind hvp1 hvp_r, hstep1.trans hstep_r⟩
    · rw [clientState_width, clientResult_width]; exact hsafe_r
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      calc memoryCost (overmarsScanOneProg (d0, ())) s +
            memoryCost (iterate overmarsScanOneProg d0 rem ()) s1
          ≤ (2 * hashEvalCostWhp c + 2454) + rem * (2 * hashEvalCostWhp c + 2454) :=
            Nat.add_le_add hmc1 hmc_r
        _ = (rem + 1) * (2 * hashEvalCostWhp c + 2454) := by ring

private theorem overmarsScanLoopGenProg_safe {c U V w n_max base b rem : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {omMap : ℕ → Option ℕ} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hb : b < numBucketsWhp n_max)
    (hce : fs.curEp = 0 ∨ fs.curEp = 1)
    (hor : fs.overmarsRole b < 3)
    (hcnt : fs.bktCount b ≤ totalLocalCoordsWhp n_max)
    (hcur : fs.overmarsCursor b + rem ≤ n_max)
    (hins : fs.overmarsInsCount b + rem ≤ 8 * (slabScale n_max) ^ 12)
    (hq : ∀ i < n_max, fs.quotArr i < 2 ^ quotBitsWhp U n_max)
    (hbp : ∀ k < fs.bktCount b - capFrontWhp n_max, fs.backPtr b k < poolSizeWhp n_max)
    (hv_om : ValidWhpSlice n_max (fs.overmarsInsCount b) (fs.slices (fs.overmarsSliceIdx b)) omMap)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    iterationSafe overmarsScanOneProg OvermarsScanOnePre w
      ((mkWhpParams c U V w n_max, base), b) rem () s :=
  (overmarsScanLoopGenProg_spec henv hb rem fs omMap s hce hor hcnt hcur hins hq hbp hv_om
    hseed hrep).1

/-! ## Section 3: Role-Swap Completion and Full `overmarsStepGenProg` -/

/-- Inner swap action of `overmarsFinishSwapGenProg` (`d = ((cp, base), b)`). -/
@[irreducible] private def overmarsDoSwapGenProg : (WhpCoreParams × ℕ) × ℕ → Memory.Prog Unit
  | ((cp, base), b) => do
    let z0 ← pure 0
    let bm ← mkBktMetaRtProg (cp, base)
    overmarsSwapRolesRtProg (bm, b)
    setOvermarsActRtProg ((bm, b), z0)

private theorem realizes_overmarsDoSwapGen :
    Realizes .exact overmarsDoSwapGenProg
      (WordEncoding.encode (α := (WhpCoreParams × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((cp, base), b) _ => WhpLargeEnvGen w cp base ∧ b < wpM cp)
      (fun _ _ => 0) := by
  unfold overmarsDoSwapGenProg
  have hmb := realizes_mkBktMetaRt
  have hsr := realizes_overmarsSwapRolesRt
  have hsa := realizes_setOvermarsActRt
  realize
  rcases d with ⟨⟨cp, base⟩, b⟩
  obtain ⟨⟨c, U, V, w₀, n_max, henv, rfl⟩, hb⟩ := h
  obtain rfl := henv.2.2.1
  have hth := henv.2.2.2.1
  obtain ⟨hmb_st, hmb_res, _, _⟩ := mkBktMetaRtProg_spec (c := c) (U := U) (V := V)
    (w := w) (n_max := n_max) (base := base) hth s
  rw [wp_large_M hth] at hb
  simp only [hmb_st, hmb_res] at *
  exact ⟨c, U, V, w, n_max, base, henv, rfl, hb⟩

/-- Role-swap completion substep of `overmarsStep` (`d = ((cp, base), b)`). -/
@[irreducible] private def overmarsFinishSwapGenProg : (WhpCoreParams × ℕ) × ℕ → Memory.Prog Unit
  | ((cp, base), b) => do
    let cnt ← readBktFieldGenProg (((cp, base), b), 0)
    let cur ← readBktFieldGenProg (((cp, base), b), 6)
    if cnt ≤ cur then
      overmarsDoSwapGenProg ((cp, base), b)
    else
      pure ()

private theorem realizes_overmarsFinishSwapGen :
    Realizes .exact overmarsFinishSwapGenProg
      (WordEncoding.encode (α := (WhpCoreParams × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((cp, base), b) _ => WhpLargeEnvGen w cp base ∧ b < wpM cp)
      (fun _ _ => 0) := by
  unfold overmarsFinishSwapGenProg
  have hrb := realizes_readBktFieldGen
  have hds := realizes_overmarsDoSwapGen
  have hcs_r := clientState_readBktFieldGenProg
  realize
  all_goals (
    rcases d with ⟨⟨cp, base⟩, b⟩
    dsimp only at *
    obtain ⟨⟨c, U, V, w₀, n_max, henv, rfl⟩, hb⟩ := h
    obtain rfl := henv.2.2.1
    have hth := henv.2.2.2.1
    simp only [hcs_r, wp_large_M hth] at *
    first
    | decide
    | exact henv.fits_const (by decide)
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | exact hb
  )

private theorem overmarsFinishSwapGenProg_fastStep {c U V w n_max base b : ℕ}
    {θ : SeedWhp c U n_max} {fs1 : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hb : b < numBucketsWhp n_max)
    (hlr : fs1.liveRole b ≤ n_max) (hor : fs1.overmarsRole b ≤ n_max)
    (hins : fs1.overmarsInsCount b ≤ n_max)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs1 s.mem) :
    let prog := overmarsFinishSwapGenProg ((mkWhpCoreParams c U V w n_max, base), b)
    let s' := (Memory.spec 0).clientState s prog
    let fs2 : FastState :=
      if fs1.bktCount b ≤ fs1.overmarsCursor b then
        let oldLive := fs1.liveRole b
        let oldOm := fs1.overmarsRole b
        { fs1 with
          liveRole := Function.update fs1.liveRole b oldOm
          overmarsRole := Function.update fs1.overmarsRole b oldLive
          liveInsCount := Function.update fs1.liveInsCount b (fs1.overmarsInsCount b)
          overmarsActive := Function.update fs1.overmarsActive b 0
          overmarsCursor := Function.update fs1.overmarsCursor b 0
          overmarsInsCount := Function.update fs1.overmarsInsCount b 0 }
      else fs1
    memoryCost prog s ≤ 34 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ fs2 s s' := by
  unfold overmarsFinishSwapGenProg
  refine readTwoBktFields_if_fastStep henv hb (by decide : 0 < 10) (by decide : 6 < 10)
    hseed hrep (fun cnt cur => cnt ≤ cur)
    (overmarsDoSwapGenProg ((mkWhpCoreParams c U V w n_max, base), b)) fun _ => ?_
  have hsr := StepSpec.of
    (overmarsSwapRolesRtProg_fastStep henv hb hlr hor hins hseed hrep (s := s))
  have hsa := StepSpec.of (setOvermarsActRtProg_fastStep henv hb (Nat.zero_le n_max)
    hsr.step.2.1 hsr.step.2.2.1)
  unfold overmarsDoSwapGenProg
  simp only [pure_bind]
  exact StepSpec.toAnd_le (ReadSpec.thenStep
    (.of (mkBktMetaRtProg_spec (U := U) (V := V) (w := w) (base := base) henv.2.2.2.1 s)) <|
    hsr.bind hsa) (by omega)

/-- Complete `overmarsStep` `Memory.Prog` subroutine (`d = ((wp, base), b)`). -/
@[irreducible] def overmarsStepGenProg : (WhpParams × ℕ) × ℕ → Memory.Prog Unit
  | ((wp, base), b) => do
    let z1 ← pure 1
    let n16 ← pure 16
    overmarsActivateGenProg ((wp.1, base), b)
    let act ← readBktFieldGenProg (((wp.1, base), b), 5)
    if act = z1 then do
      overmarsScanLoopGenProg ((((wp, base), b), ()), n16)
      overmarsFinishSwapGenProg ((wp.1, base), b)
    else
      pure ()

/-- Minimal structural bounds on `fs` sufficient to execute `overmarsStepGenProg` safely on
bucket `b`. -/
@[expose] def OvermarsBucketStepBounds (U n_max b : ℕ) (fs : FastState) : Prop :=
  b < numBucketsWhp n_max ∧
  (fs.curEp = 0 ∨ fs.curEp = 1) ∧
  fs.liveRole b < 3 ∧
  fs.overmarsRole b < 3 ∧
  fs.bktCount b ≤ totalLocalCoordsWhp n_max ∧
  (∀ i < n_max, fs.quotArr i < 2 ^ quotBitsWhp U n_max) ∧
  (∀ k < fs.bktCount b - capFrontWhp n_max, fs.backPtr b k < poolSizeWhp n_max) ∧
  ((overmarsAfterActivate n_max b fs).overmarsActive b = 1 →
    (overmarsAfterActivate n_max b fs).overmarsCursor b + 16 ≤ n_max ∧
    (overmarsAfterActivate n_max b fs).overmarsInsCount b + 16 ≤ 8 * (slabScale n_max) ^ 12 ∧
    ∃ omMap0, ValidWhpSlice n_max ((overmarsAfterActivate n_max b fs).overmarsInsCount b)
      ((overmarsAfterActivate n_max b fs).slices
        ((overmarsAfterActivate n_max b fs).overmarsSliceIdx b)) omMap0)

/-- `CoreFastInv` + `PreOvermarsBucketInv` immediately yield `OvermarsBucketStepBounds`. -/
theorem OvermarsBucketStepBounds.of_core_and_pre {c U V n_max b : ℕ} {θ : SeedWhp c U n_max}
    {fs : FastState} {dict : State U}
    (hc : CoreFastInv c U V n_max θ fs dict) (hb : b < numBucketsWhp n_max)
    (hom : PreOvermarsBucketInv c U n_max θ fs b) :
    OvermarsBucketStepBounds U n_max b fs := by
  have h2tl := (large_index_bounds hc.hth).2.2.1
  have hL2 := two_le_slabScale n_max
  have hL12 : 4096 ≤ (slabScale n_max) ^ 12 := by
    calc 4096 = 2 ^ 12 := by decide
      _ ≤ (slabScale n_max) ^ 12 := Nat.pow_le_pow_left hL2 12
  have hcnt_tl := hc.bktCount_le b hb
  have hcnt_3L : fs.bktCount b ≤ 3 * (slabScale n_max) ^ 12 :=
    hcnt_tl.trans totalLocalCoordsWhp_le_three_mul
  refine ⟨hb, hc.curEp_or, (hc.roles_valid b hb).1, (hc.roles_valid b hb).2.1,
    hcnt_tl, fun i _ => (hc.qv_global i).1,
    fun k hk => (hc.backPtr_valid b hb k hk).1, ?_⟩
  unfold overmarsAfterActivate
  intro ha1
  rcases hom with ⟨ha0, _⟩ | ⟨ha_act, _, hcur_le, _, hins_le, omMap0, hv0, _⟩
  · by_cases htrig : 5 * (slabScale n_max) ^ 12 ≤ fs.liveInsCount b
    · simp only [ha0, htrig, and_self, ↓reduceIte, FastState.overmarsSliceIdx,
        Function.update_self]
      exact ⟨by omega, by omega, ⟨fun _ => none, validWhpSlice_zero _ 0 _⟩⟩
    · rw [ite_eq_right fun ⟨_, h⟩ => htrig h] at ha1
      omega
  · rw [ite_eq_right (by omega)]
    exact ⟨by omega, by omega, ⟨omMap0, hv0⟩⟩

/-- Precondition for `overmarsStepGenProg`. -/
@[expose] def OvermarsStepPre (w : ℕ) : (WhpParams × ℕ) × ℕ → Memory.State → Prop
  | ((wp, base), b), s =>
    ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState),
      WhpLargeEnv c U V w₀ n_max w base ∧
      wp = mkWhpParams c U V w₀ n_max ∧
      SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
      FastMemRep base c U V w₀ n_max fs s.mem ∧
      OvermarsBucketStepBounds U n_max b fs

private theorem overmarsAfterActivate_preserves (n_max b : ℕ) (fs : FastState) :
    let fs0 := overmarsAfterActivate n_max b fs
    fs0.curEp = fs.curEp ∧
    fs0.overmarsRole b = fs.overmarsRole b ∧
    fs0.liveRole b = fs.liveRole b ∧
    fs0.bktCount b = fs.bktCount b ∧
    fs0.quotArr = fs.quotArr ∧
    fs0.backPtr = fs.backPtr := by
  unfold overmarsAfterActivate
  split_ifs <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem overmarsScanSteps_roles_and_ins (c U n_max : ℕ) (θ : SeedWhp c U n_max) (b : ℕ) :
    ∀ k (st : FastState),
      (overmarsScanSteps c U n_max θ b k st).liveRole b = st.liveRole b ∧
      (overmarsScanSteps c U n_max θ b k st).overmarsRole b = st.overmarsRole b ∧
      (overmarsScanSteps c U n_max θ b k st).overmarsInsCount b ≤ st.overmarsInsCount b + k := by
  intro k
  induction k with
  | zero => exact fun st => ⟨rfl, rfl, Nat.le_add_right _ _⟩
  | succ k ih =>
    intro st
    dsimp only [overmarsScanSteps]
    split <;> obtain ⟨r1, r2, r3⟩ := ih _ <;> refine ⟨r1, r2, ?_⟩ <;> dsimp only at r3
    · rw [Function.update_self] at r3
      omega
    · omega

theorem realizes_overmarsStepGen :
    Realizes .exact overmarsStepGenProg
      (WordEncoding.encode (α := (WhpParams × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      OvermarsStepPre
      (fun _ _ => 0) := by
  unfold overmarsStepGenProg
  have hoa := realizes_overmarsActivateGen
  have hrb := realizes_readBktFieldGen
  have hsl := realizes_overmarsScanLoopGen
  have hfs := realizes_overmarsFinishSwapGen
  realize
  all_goals (
    rcases d with ⟨⟨wp, base⟩, b⟩
    dsimp only at *
    try simp only [Prod.mk.eta] at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, henv, rfl, hseed, hrep,
      ⟨hb, hce_or, _, hor, hcnt_le, hq_all, hbp_v, hscan16⟩⟩ := h
    obtain rfl := henv.2.2.1
    have hth := henv.2.2.2.1
    have hcp_eq : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
      simp [mkWhpParams, Nat.not_lt.mpr hth]
    obtain ⟨_, _, hoa_step⟩ := overmarsActivateGenProg_fastStep henv hb hor hseed hrep (s := s)
    have hrep0 := hoa_step.2.2.1
    obtain ⟨h5_st, h5_res, _, _⟩ :=
      readBktFieldGenProg_spec henv hb (by decide : 5 < 10) hrep0
    simp only [getBktField] at h5_res
    simp only [hcp_eq, h5_st, h5_res] at *
    try simp only [wp_large_M hth] at *
    first
    | decide
    | exact henv.fits_const (by decide)
    | exact ⟨c, U, V, w, n_max, fs, henv, rfl, hrep, hb, hor⟩
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | exact hb
    | (obtain ⟨hcur16, hins16, omMap0, hv0⟩ := hscan16 (by assumption)
       obtain ⟨hce0, hor0, _, hcnt0, hq0, hbp0⟩ := overmarsAfterActivate_preserves n_max b fs
       exact overmarsScanLoopGenProg_safe henv hb
         (hce0 ▸ hce_or) (hor0 ▸ hor) (hcnt0 ▸ hcnt_le)
         hcur16 hins16 (fun i hi => hq0 ▸ hq_all i hi)
         (fun k hk => hbp0 ▸ hbp_v k (hcnt0 ▸ hk))
         hv0 hoa_step.2.1 hrep0)
  )

private theorem overmarsStep_eq (c U n_max : ℕ) (θ : SeedWhp c U n_max) (b : ℕ)
    (fs : FastState) :
    overmarsStep c U n_max θ b fs =
      let fs0 := overmarsAfterActivate n_max b fs
      if fs0.overmarsActive b = 1 then
        let fs1 := overmarsScanSteps c U n_max θ b 16 fs0
        if fs1.bktCount b ≤ fs1.overmarsCursor b then
          { fs1 with
            liveRole := Function.update fs1.liveRole b (fs1.overmarsRole b)
            overmarsRole := Function.update fs1.overmarsRole b (fs1.liveRole b)
            liveInsCount := Function.update fs1.liveInsCount b (fs1.overmarsInsCount b)
            overmarsActive := Function.update fs1.overmarsActive b 0
            overmarsCursor := Function.update fs1.overmarsCursor b 0
            overmarsInsCount := Function.update fs1.overmarsInsCount b 0 }
        else fs1
      else fs0 := by
  unfold overmarsStep overmarsAfterActivate
  rfl

theorem overmarsStepGenProg_fastStep {c U V w n_max base b : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hbnds : OvermarsBucketStepBounds U n_max b fs)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := overmarsStepGenProg ((mkWhpParams c U V w n_max, base), b)
    let s' := (Memory.spec 0).clientState s prog
    memoryCost prog s ≤ 32 * hashEvalCostWhp c + 39326 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ (overmarsStep c U n_max θ b fs) s s' := by
  have hth := henv.2.2.2.1
  have hwp1 : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
    simp [mkWhpParams, Nat.not_lt.mpr hth]
  have hn4 := four_le_of_whpThreshold_le hth
  have hML12 := numBucketsWhp_mul_scale_pow12_le hth
  have hM_ge := (large_bounds_lt_n_max hth).1
  have h8L12_n : 8 * (slabScale n_max) ^ 12 ≤ n_max :=
    (Nat.mul_le_mul_right _ (by omega : 8 ≤ numBucketsWhp n_max)).trans hML12
  rcases hbnds with ⟨hb, hce_or, hlr, hor, hcnt_le, hq_all, hbp_v, hscan16⟩
  obtain ⟨hoa_mc, hoa_vp, hoa_step⟩ :=
    overmarsActivateGenProg_fastStep henv hb hor hseed hrep (s := s)
  have hoa := StepSpec.of_le ⟨hoa_mc, hoa_vp, hoa_step⟩
  have hrep0 := hoa.step.2.2.1
  have h5 := ReadSpec.of (readBktFieldGenProg_spec henv hb (by decide : 5 < 10) hrep0)
  dsimp only
  unfold overmarsStepGenProg
  rw [overmarsStep_eq]
  generalize hk16_eq : (16 : ℕ) = k16
  have hk16 : k16 ≤ 16 := hk16_eq ▸ le_rfl
  clear hk16_eq
  dsimp only
  simp only [hwp1, pure_bind]
  by_cases ha1 : (overmarsAfterActivate n_max b fs).overmarsActive b = 1
  · rw [ite_eq_left ha1]
    obtain ⟨hcur16, hins16, omMap0, hv0⟩ := hscan16 ha1
    obtain ⟨hce0, hor0, hlr0, hcnt0, hq0, hbp0⟩ := overmarsAfterActivate_preserves n_max b fs
    obtain ⟨_, hsl_mc, hsl_vp, hsl_step⟩ :=
      overmarsScanLoopGenProg_spec henv hb k16 (overmarsAfterActivate n_max b fs) omMap0 _
        (hce0 ▸ hce_or) (hor0 ▸ hor) (hcnt0 ▸ hcnt_le)
        (by omega) (by omega) (fun i hi => hq0 ▸ hq_all i hi)
        (fun k' hk' => hbp0 ▸ hbp_v k' (hcnt0 ▸ hk'))
        hv0 hoa.step.2.1 hrep0
    obtain ⟨r1, r2, r3⟩ :=
      overmarsScanSteps_roles_and_ins c U n_max θ b k16 (overmarsAfterActivate n_max b fs)
    have hfs := overmarsFinishSwapGenProg_fastStep henv hb (by rw [r1]; omega)
      (by rw [r2]; omega) (by omega) hsl_step.2.1 hsl_step.2.2.1
    exact StepSpec.toAnd_le (hoa.bind <| h5.thenStep <| .if_pos ha1 <|
      (StepSpec.of_le ⟨hsl_mc, hsl_vp, hsl_step⟩).bind (.of_le hfs)) (by
        have := Nat.mul_le_mul_right (2 * hashEvalCostWhp c + 2454) hk16
        have := hfs.1; omega)
  · rw [ite_eq_right ha1]
    exact StepSpec.toAnd_le (hoa.bind <| h5.thenStep <| .if_neg ha1 <|
      .pure hoa.step.2.1 hrep0 ()) (by omega)

end Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

end
