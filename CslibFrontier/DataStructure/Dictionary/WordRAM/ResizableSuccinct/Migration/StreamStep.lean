/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Migration.ParamsCompute
public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Dispatch.BucketOps
-- Unfolds `recoverOwnerBucketGenProg` in `MetaSync` for read-only state and cost lemmas.
import all CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.MetaSync
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import CslibFrontier.DataStructure.StateTransition.ClientMap

/-!
# Single-Tape Block Copy, New-Epoch Metadata Initialization, and Streaming Rebuild (`Memory.Prog`)

This module implements the deterministic `Memory.Prog` subroutines (`¬ReadsWidth`, certified via
`RealizesBounded .exact`) for single-tape `1 · OPT` epoch capacity migration:
1. **Overlapping-Safe Block Copy (`copyRightwardProg`, `copyLeftwardProg`)**:
   * `copyRightwardProg` copies `[srcBase, +len)` rightward to `[dstBase, +len)`
     (`srcBase ≤ dstBase`) in reverse index order `len - 1 .. 0` so overlapping ranges never
     clobber unread words;
   * `copyLeftwardProg` copies `[srcBase, +len)` leftward to `[dstBase, +len)` (`dstBase ≤ srcBase`)
     in forward index order `0 .. len - 1`.
2. **New-Epoch Table & Zeroed Metadata Initialization (`initNewEpochMetaProg`)**:
   * builds the Four-Russians carryless multiplication table via `initTableGenProg` and zeros
     `[newMetaBase + offCompLM, newMetaBase + offCompItems)`, establishing `ReducedKWise.Rep`,
     `DictStateInv ... (Dictionary.empty U)`, `FixedCoupled`, and `slotPotential = 0`.
3. **Old-Item Key/Value Reconstruction & Fresh-Key Streaming Append (`readOldItemKeyValGenProg`,
   `streamInsertFreshGenProg`, `streamAllItemsProg`)**:
   * reconstructs `(u_i, v_i)` from dense slot `i < n` of the right-aligned old item suffix via
     `recoverOwnerBucketGenProg`, `evalHashGenProg`, and Feistel inversion;
   * appends `(u_i, v_i)` into `[0, i + 1)` at `(newMetaBase, arenaBase)` without duplicate search
     (valid by injectivity of `reconstructKeyAt_spec`), preserving all unread old items `d > i` by
     `newItemEnd_le_oldItemNextWord`.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.copyRightwardProg`,
  `copyLeftwardProg`: overlapping-safe rightward and leftward word-block copy programs.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.initNewEpochMetaProg`:
  Four-Russians table and zeroed compacted metadata initializer.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.readOldItemKeyValGenProg`,
  `streamInsertFreshGenProg`, `streamAllItemsProg`: single-tape streaming rebuild programs.

## Main results

* `copyRightwardProg_spec`, `realizesBounded_copyRightward`,
  `copyLeftwardProg_spec`, `realizesBounded_copyLeftward`: correctness and `RealizesBounded`
  certificates for overlapping-safe word-block shifts.
* `initNewEpochMetaProg_spec`, `realizesBounded_initNewEpochMeta`: empty new-epoch invariant and
  `RealizesBounded` certificate.
* `streamInsertFreshGenProg_spec`, `realizesBounded_streamInsertFreshGen`: fresh-key append
  correctness (`≤ 45360` amortized memory operations) and `RealizesBounded` certificate.
* `streamAllItemsProg_spec`, `realizesBounded_streamAllItems`: full `n`-item single-tape streaming
  rebuild establishing `DictStateInv` and `FixedCoupled` for `s_abs` in `O(n)` deterministic steps.
* `compactedSplitRep_of_reloc`: transports `CompactedSplitRep` after leftward relocation to `base`.

## References

* [M. A. Bender, M. Farach-Colton, J. Kuszmaul, and W. Kuszmaul, *Modern Hashing Made Simple*,
  Sections 3–4 and 6][BenderFarachColtonKuszmaulKuszmaul2024]
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.WordRAM.Resizable
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM.Succinct
open Cslib.DataStructure.HashFamily.WordRAM
open Cslib.DataStructure.HashFamily.WordRAM.ReducedKWise
open Cslib.DataStructure.HashFamily.WordRAM.RuntimeReducedKWise
open Cslib.Probability

attribute [local simp] Realization.memoryCost_bind'
attribute [local simp] prog_clientResult_bind prog_runClient_state_bind prog_clientResult_pure
attribute [local simp] prog_runClient_state_pure StateTransitionSpec.clientResult_map
  StateTransitionSpec.fst_snd_runClient_map
attribute [local simp] Realization.memoryCost_map prog_clientResult_read prog_runClient_state_read
attribute [local simp] prog_memoryCost_read prog_clientResult_write prog_runClient_state_write
attribute [local simp] prog_memoryCost_write

/-! ## Section 1: Overlapping-Safe Rightward and Leftward Block Copy (`Memory.Prog`) -/

private def copyRightStepProg : (ℕ × (ℕ × ℕ)) × ℕ → Memory.Prog ℕ
  | ((srcBase, (dstBase, len)), k) => do
    let idx ← pure (len - 1 - k)
    let val ← Memory.read (srcBase + idx)
    Memory.write (dstBase + idx) val
    pure (k + 1)

private def CopyRightStepPre (w : ℕ) : (ℕ × (ℕ × ℕ)) × ℕ → Memory.State → Prop
  | ((srcBase, (dstBase, len)), k), s =>
    srcBase ≤ dstBase ∧ k < len ∧ dstBase + len ≤ s.frontier ∧ Fits w 1

private theorem realizesBounded_copyRightStep :
    RealizesBounded .exact copyRightStepProg
      (WordEncoding.encode (α := (ℕ × (ℕ × ℕ)) × ℕ)) (WordEncoding.encode (α := ℕ))
      CopyRightStepPre (fun _ _ => 0) := by
  realize
  all_goals (
    rcases d with ⟨⟨srcBase, ⟨dstBase, len⟩⟩, k⟩
    obtain ⟨hle, hk, hfr, hfit1⟩ := h
    dsimp only at *
    have hfit_fr : Fits w s.frontier := hmem.1)
  all_goals (
    first
    | omega
    | (refine hfit_fr.of_le ?_; omega))

private theorem memoryCost_copyRightStep_ge_one (x : (ℕ × (ℕ × ℕ)) × ℕ) (s : Memory.State) :
    1 ≤ memoryCost (copyRightStepProg x) s := by
  rcases x with ⟨⟨srcBase, ⟨dstBase, len⟩⟩, k⟩
  dsimp only [copyRightStepProg]; simp only [pure_bind, Realization.memoryCost_bind',
    prog_memoryCost_read, prog_runClient_state_read, prog_memoryCost_write,
    prog_runClient_state_write, memoryCost_pure]; omega

private theorem copyRightLoop_spec {w srcBase dstBase len : ℕ} {s₀ : Memory.State}
    (hwf : ∀ a < s₀.frontier, Fits w (s₀.mem a))
    (hle : srcBase ≤ dstBase) (hfr : dstBase + len ≤ s₀.frontier) (hfit1 : Fits w 1) :
    let env := (srcBase, (dstBase, len))
    let prog := iterate copyRightStepProg env len 0
    let s' := (Memory.spec 0).clientState s₀ prog
    iterationSafe copyRightStepProg CopyRightStepPre w env len 0 s₀ ∧
    (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ prog) ∧
    memoryCost prog s₀ ≤ 2 * len ∧
    s'.frontier = s₀.frontier ∧
    (∀ j < len, s'.mem (dstBase + j) = s₀.mem (srcBase + j)) ∧
    (∀ a, ¬(dstBase ≤ a ∧ a < dstBase + len) → s'.mem a = s₀.mem a) := by
  intro env prog s'
  let inv (k : ℕ) (acc : ℕ) (s : Memory.State) : Prop :=
    acc = k ∧ s.frontier = s₀.frontier ∧
    (∀ j, len - k ≤ j → j < len → s.mem (dstBase + j) = s₀.mem (srcBase + j)) ∧
    (∀ a, a < dstBase + (len - k) ∨ dstBase + len ≤ a → s.mem a = s₀.mem a)
  obtain ⟨hsafe, hv, hcost, hfr', hmod, _, _, hcopied, _⟩ :=
    iterate_spec copyRightStepProg CopyRightStepPre w env 2 len inv
      (fun a => dstBase ≤ a ∧ a < dstBase + len)
      (fun k hk acc s ⟨hacc, hfr_s, hhi, hlo⟩ => by
        subst acc
        set idx := len - 1 - k
        have hsrc_lt : srcBase + idx < s₀.frontier := by omega
        have hdst_lt : dstBase + idx < s.frontier := by omega
        have hsrc_eq : s.mem (srcBase + idx) = s₀.mem (srcBase + idx) :=
          hlo (srcBase + idx) (Or.inl (by omega))
        have hval_fit : Fits w (s.mem (srcBase + idx)) := hsrc_eq ▸ hwf (srcBase + idx) hsrc_lt
        refine ⟨⟨hle, hk, by omega, hfit1⟩, ?_, ?_, rfl, ?_, rfl, hfr_s, ?_, ?_⟩
        · dsimp only [copyRightStepProg, env]; simp only [pure_bind]
          exact ⟨show srcBase + idx < s.frontier by omega, ⟨hdst_lt, hval_fit⟩, trivial⟩
        · dsimp only [copyRightStepProg, env]; simp only [pure_bind, Realization.memoryCost_bind',
            prog_memoryCost_read, prog_runClient_state_read, prog_memoryCost_write,
            prog_runClient_state_write, memoryCost_pure]; omega
        · intro x hx
          dsimp only [copyRightStepProg, env]
          simp only [pure_bind, StateTransitionSpec.clientState,
            prog_runClient_state_bind, prog_runClient_state_read, prog_clientResult_read,
            prog_runClient_state_write, prog_runClient_state_pure]
          exact Function.update_of_ne (by omega) _ _
        · intro j hj_lo hj_hi
          change Function.update s.mem (dstBase + idx) (s.mem (srcBase + idx)) (dstBase + j) = _
          rcases eq_or_ne j idx with rfl | hne
          · rw [Function.update_self]; exact hsrc_eq
          · rw [Function.update_of_ne (by omega)]; exact hhi j (by omega) hj_hi
        · intro a ha
          change Function.update s.mem (dstBase + idx) (s.mem (srcBase + idx)) a = s₀.mem a
          rw [Function.update_of_ne (by omega)]
          exact hlo a (by omega))
      0 s₀ ⟨rfl, rfl, fun j h1 h2 => absurd h2 (by omega), fun _ _ => rfl⟩
  refine ⟨hsafe, hv, hcost, hfr', fun j hj => hcopied j (by omega) hj,
    fun a ha => hmod a ha⟩

/-- Copy `len` words rightward from `[srcBase, +len)` to `[dstBase, +len)` (`srcBase ≤ dstBase`)
in reverse order (`¬ReadsWidth`). -/
def copyRightwardProg : (ℕ × ℕ) × ℕ → Memory.Prog Unit
  | ((srcBase, dstBase), len) => do
    let _ ← iterate copyRightStepProg (srcBase, (dstBase, len)) len 0
    pure ()

/-- Entry precondition for `copyRightwardProg`. -/
@[expose] def CopyRightwardPre (w : ℕ) : (ℕ × ℕ) × ℕ → Memory.State → Prop
  | ((srcBase, dstBase), len), s =>
    srcBase ≤ dstBase ∧ dstBase + len ≤ s.frontier ∧ Fits w 1

theorem realizesBounded_copyRightward :
    RealizesBounded .exact copyRightwardProg
      (WordEncoding.encode (α := (ℕ × ℕ) × ℕ)) (WordEncoding.encode (α := Unit))
      CopyRightwardPre (fun _ _ => 0) := by
  have hcr := RealizesBounded.iterate₀ (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
    (WordEncoding.encode (α := ℕ)) realizesBounded_copyRightStep memoryCost_copyRightStep_ge_one
  realize
  rcases d with ⟨⟨srcBase, dstBase⟩, len⟩
  obtain ⟨hle, hfr, hfit1⟩ := h
  exact (copyRightLoop_spec (fun a _ => hmem.2 a) hle hfr hfit1).1

theorem copyRightwardProg_spec {w srcBase dstBase len : ℕ} {s₀ : Memory.State}
    (hwf : ∀ a < s₀.frontier, Fits w (s₀.mem a))
    (hle : srcBase ≤ dstBase) (hfr : dstBase + len ≤ s₀.frontier) (hfit1 : Fits w 1) :
    let d := ((srcBase, dstBase), len)
    let prog := copyRightwardProg d
    let s' := (Memory.spec 0).clientState s₀ prog
    CopyRightwardPre w d s₀ ∧
    (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ prog) ∧
    memoryCost prog s₀ ≤ 2 * len ∧
    s'.frontier = s₀.frontier ∧
    (∀ j < len, s'.mem (dstBase + j) = s₀.mem (srcBase + j)) ∧
    (∀ a, ¬(dstBase ≤ a ∧ a < dstBase + len) → s'.mem a = s₀.mem a) := by
  intro d prog s'
  obtain ⟨_, hv, hc, hfr', hcp, hout⟩ := copyRightLoop_spec hwf hle hfr hfit1
  have hs'_eq : s' = (Memory.spec 0).clientState s₀
      (iterate copyRightStepProg (srcBase, (dstBase, len)) len 0) := by
    dsimp only [s', prog, d, copyRightwardProg]
    rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_pure]
  refine ⟨⟨hle, hfr, hfit1⟩, ?_, ?_, hs'_eq ▸ hfr',
    fun j hj => hs'_eq ▸ hcp j hj, fun a ha => hs'_eq ▸ hout a ha⟩
  · dsimp only [prog, d, copyRightwardProg]
    rw [validHistory_bind']; exact ⟨hv, trivial⟩
  · dsimp only [prog, d, copyRightwardProg]
    rw [Realization.memoryCost_bind', memoryCost_pure]; omega

private def copyLeftStepProg : (ℕ × ℕ) × ℕ → Memory.Prog ℕ
  | ((srcBase, dstBase), k) => do
    let val ← Memory.read (srcBase + k)
    Memory.write (dstBase + k) val
    pure (k + 1)

private def CopyLeftStepPre (w : ℕ) : (ℕ × ℕ) × ℕ → Memory.State → Prop
  | ((srcBase, dstBase), k), s =>
    dstBase ≤ srcBase ∧ srcBase + k < s.frontier ∧ Fits w 1

private theorem realizesBounded_copyLeftStep :
    RealizesBounded .exact copyLeftStepProg
      (WordEncoding.encode (α := (ℕ × ℕ) × ℕ)) (WordEncoding.encode (α := ℕ))
      CopyLeftStepPre (fun _ _ => 0) := by
  realize
  all_goals (
    rcases d with ⟨⟨srcBase, dstBase⟩, k⟩
    obtain ⟨hle, hlt, hfit1⟩ := h
    dsimp only at *
    have hfit_fr : Fits w s.frontier := hmem.1)
  all_goals (refine hfit_fr.of_le ?_; omega)

private theorem memoryCost_copyLeftStep_ge_one (x : (ℕ × ℕ) × ℕ) (s : Memory.State) :
    1 ≤ memoryCost (copyLeftStepProg x) s := by
  rcases x with ⟨⟨srcBase, dstBase⟩, k⟩
  dsimp only [copyLeftStepProg]; simp only [Realization.memoryCost_bind',
    prog_memoryCost_read, prog_runClient_state_read, prog_memoryCost_write,
    prog_runClient_state_write, memoryCost_pure]; omega

private theorem copyLeftLoop_spec {w srcBase dstBase len : ℕ} {s₀ : Memory.State}
    (hwf : ∀ a < s₀.frontier, Fits w (s₀.mem a))
    (hle : dstBase ≤ srcBase) (hfr : srcBase + len ≤ s₀.frontier) (hfit1 : Fits w 1) :
    let env := (srcBase, dstBase)
    let prog := iterate copyLeftStepProg env len 0
    let s' := (Memory.spec 0).clientState s₀ prog
    iterationSafe copyLeftStepProg CopyLeftStepPre w env len 0 s₀ ∧
    (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ prog) ∧
    memoryCost prog s₀ ≤ 2 * len ∧
    s'.frontier = s₀.frontier ∧
    (∀ j < len, s'.mem (dstBase + j) = s₀.mem (srcBase + j)) ∧
    (∀ a, ¬(dstBase ≤ a ∧ a < dstBase + len) → s'.mem a = s₀.mem a) := by
  intro env prog s'
  let inv (k : ℕ) (acc : ℕ) (s : Memory.State) : Prop :=
    acc = k ∧ s.frontier = s₀.frontier ∧
    (∀ j < k, s.mem (dstBase + j) = s₀.mem (srcBase + j)) ∧
    (∀ a, a < dstBase ∨ dstBase + k ≤ a → s.mem a = s₀.mem a)
  obtain ⟨hsafe, hv, hcost, hfr', hmod, _, _, hcopied, _⟩ :=
    iterate_spec copyLeftStepProg CopyLeftStepPre w env 2 len inv
      (fun a => dstBase ≤ a ∧ a < dstBase + len)
      (fun k hk acc s ⟨hacc, hfr_s, hlo, hhi⟩ => by
        subst acc
        have hsrc_lt : srcBase + k < s₀.frontier := by omega
        have hdst_lt : dstBase + k < s.frontier := by omega
        have hsrc_eq : s.mem (srcBase + k) = s₀.mem (srcBase + k) :=
          hhi (srcBase + k) (Or.inr (by omega))
        have hval_fit : Fits w (s.mem (srcBase + k)) := hsrc_eq ▸ hwf (srcBase + k) hsrc_lt
        refine ⟨⟨hle, by omega, hfit1⟩, ?_, ?_, rfl, ?_, rfl, hfr_s, ?_, ?_⟩
        · dsimp only [copyLeftStepProg, env]
          exact ⟨show srcBase + k < s.frontier by omega, ⟨hdst_lt, hval_fit⟩, trivial⟩
        · dsimp only [copyLeftStepProg, env]; simp only [Realization.memoryCost_bind',
            prog_memoryCost_read, prog_runClient_state_read, prog_memoryCost_write,
            prog_runClient_state_write, memoryCost_pure]; omega
        · intro x hx
          dsimp only [copyLeftStepProg, env]; simp only [StateTransitionSpec.clientState,
            prog_runClient_state_bind, prog_runClient_state_read, prog_clientResult_read,
            prog_runClient_state_write, prog_runClient_state_pure]
          exact Function.update_of_ne (by omega) _ _
        · intro j hj
          change Function.update s.mem (dstBase + k) (s.mem (srcBase + k)) (dstBase + j) = _
          rcases eq_or_ne j k with rfl | hne
          · rw [Function.update_self]; exact hsrc_eq
          · rw [Function.update_of_ne (by omega)]; exact hlo j (by omega)
        · intro a ha
          change Function.update s.mem (dstBase + k) (s.mem (srcBase + k)) a = s₀.mem a
          rw [Function.update_of_ne (by omega)]
          exact hhi a (by omega))
      0 s₀ ⟨rfl, rfl, fun _ hj => (Nat.not_lt_zero _ hj).elim, fun _ _ => rfl⟩
  exact ⟨hsafe, hv, hcost, hfr', hcopied, fun a ha => hmod a ha⟩

/-- Copy `len` words leftward from `[srcBase, +len)` to `[dstBase, +len)` (`dstBase ≤ srcBase`)
in forward order (`¬ReadsWidth`). -/
def copyLeftwardProg : (ℕ × ℕ) × ℕ → Memory.Prog Unit
  | ((srcBase, dstBase), len) => do
    let _ ← iterate copyLeftStepProg (srcBase, dstBase) len 0
    pure ()

/-- Entry precondition for `copyLeftwardProg`. -/
@[expose] def CopyLeftwardPre (w : ℕ) : (ℕ × ℕ) × ℕ → Memory.State → Prop
  | ((srcBase, dstBase), len), s =>
    dstBase ≤ srcBase ∧ srcBase + len ≤ s.frontier ∧ Fits w 1

theorem realizesBounded_copyLeftward :
    RealizesBounded .exact copyLeftwardProg
      (WordEncoding.encode (α := (ℕ × ℕ) × ℕ)) (WordEncoding.encode (α := Unit))
      CopyLeftwardPre (fun _ _ => 0) := by
  have hcl := RealizesBounded.iterate₀ (WordEncoding.encode (α := ℕ × ℕ))
    (WordEncoding.encode (α := ℕ)) realizesBounded_copyLeftStep memoryCost_copyLeftStep_ge_one
  realize
  rcases d with ⟨⟨srcBase, dstBase⟩, len⟩
  obtain ⟨hle, hfr, hfit1⟩ := h
  exact (copyLeftLoop_spec (fun a _ => hmem.2 a) hle hfr hfit1).1

theorem copyLeftwardProg_spec {w srcBase dstBase len : ℕ} {s₀ : Memory.State}
    (hwf : ∀ a < s₀.frontier, Fits w (s₀.mem a))
    (hle : dstBase ≤ srcBase) (hfr : srcBase + len ≤ s₀.frontier) (hfit1 : Fits w 1) :
    let d := ((srcBase, dstBase), len)
    let prog := copyLeftwardProg d
    let s' := (Memory.spec 0).clientState s₀ prog
    CopyLeftwardPre w d s₀ ∧
    (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ prog) ∧
    memoryCost prog s₀ ≤ 2 * len ∧
    s'.frontier = s₀.frontier ∧
    (∀ j < len, s'.mem (dstBase + j) = s₀.mem (srcBase + j)) ∧
    (∀ a, ¬(dstBase ≤ a ∧ a < dstBase + len) → s'.mem a = s₀.mem a) := by
  intro d prog s'
  obtain ⟨_, hv, hc, hfr', hcp, hout⟩ := copyLeftLoop_spec hwf hle hfr hfit1
  have hs'_eq : s' = (Memory.spec 0).clientState s₀
      (iterate copyLeftStepProg (srcBase, dstBase) len 0) := by
    dsimp only [s', prog, d, copyLeftwardProg]
    rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_pure]
  refine ⟨⟨hle, hfr, hfit1⟩, ?_, ?_, hs'_eq ▸ hfr',
    fun j hj => hs'_eq ▸ hcp j hj, fun a ha => hs'_eq ▸ hout a ha⟩
  · dsimp only [prog, d, copyLeftwardProg]
    rw [validHistory_bind']; exact ⟨hv, trivial⟩
  · dsimp only [prog, d, copyLeftwardProg]
    rw [Realization.memoryCost_bind', memoryCost_pure]; omega

/-! ## Section 2: New-Epoch Four-Russians Table and Zeroed Metadata Initializer -/

private theorem memoryCost_zeroWordsStep_ge_one (x : ℕ × ℕ) (s : Memory.State) :
    1 ≤ memoryCost (zeroWordsStepProg x) s := by
  rcases x with ⟨baseAddr, i⟩
  dsimp only [zeroWordsStepProg]
  rw [Realization.memoryCost_bind', prog_memoryCost_write]; omega

/-- Build the Four-Russians table at `newMetaBase + 225` and zero compacted metadata
`[newMetaBase + offCompLM, newMetaBase + offCompItems)` (`¬ReadsWidth`). -/
def initNewEpochMetaProg : (HashParams × CompParams) × ℕ → Memory.Prog Unit
  | ((newHp, newCp), newMetaBase) => do
    let _ ← initTableGenProg (newHp, newMetaBase + 225)
    let offLM ← pure (225 + cpHashSpace newCp)
    let metaWords ← pure (cpOffItems newCp - offLM)
    let _ ← iterate zeroWordsStepProg (newMetaBase + offLM) metaWords 0
    pure ()

/-- Entry precondition for `initNewEpochMetaProg`. -/
@[expose] def InitNewEpochMetaPre (w : ℕ) :
    (HashParams × CompParams) × ℕ → Memory.State → Prop
  | ((newHp, newCp), newMetaBase), s =>
    ∃ U V N,
      0 < w ∧ 1 ≤ N ∧ N ≤ U ∧ Fits w U ∧ V ≤ 2 ^ w ∧
      newHp = mkHashParams w (qBits U N) (hashB N) (totalMicroBits N) 3 ∧
      newCp = mkCompParams U V w N ∧
      newMetaBase + offCompItems U w N ≤ s.frontier ∧
      Fits w (newMetaBase + offCompItems U w N)

theorem realizesBounded_initNewEpochMeta :
    RealizesBounded .exact initNewEpochMetaProg
      (WordEncoding.encode (α := (HashParams × CompParams) × ℕ))
      (WordEncoding.encode (α := Unit))
      InitNewEpochMetaPre (fun _ _ => 0) := by
  have htab := realizesBounded_initTableGen
  have hzw := RealizesBounded.iterate₀ (WordEncoding.encode (α := ℕ))
    (WordEncoding.encode (α := ℕ)) realizesBounded_zeroWordsStep memoryCost_zeroWordsStep_ge_one
  realize
  all_goals (
    rcases d with ⟨⟨newHp, newCp⟩, newMetaBase⟩
    obtain ⟨U, V, N, hw, hN, hNU, hU, _hV, rfl, rfl, hfr, hfit⟩ := h
    dsimp only at *
    try simp only [cpHashSpace_mk, cpOffItems_mk] at *
    have h225 : Fits w 225 := fits_const_of_offCompItems hfit le_rfl
    have hw2 : 2 ≤ w := by
      by_contra hlt2
      have hw1 : w ≤ 1 := by omega
      have := Nat.pow_le_pow_right two_pos hw1
      change 225 < 2 ^ w at h225; omega
    have hlm_le : offCompLM U w N ≤ offCompItems U w N := by
      unfold offCompItems offDenseToTail offTailToDense offCompGM; omega
    have hfr_h : (newMetaBase + 225) +
        ReducedKWise.space w (qBits U N) (hashB N) (totalMicroBits N) 3 ≤ s.frontier := by
      dsimp only [offCompLM, epochHdrWords, epochHashSpace, epochQBits, epochHashB, qBits,
        hashB] at hlm_le ⊢
      omega
    have hfit_h : Fits w ((newMetaBase + 225) +
        ReducedKWise.space w (qBits U N) (hashB N) (totalMicroBits N) 3) := hfit.of_le (by
      dsimp only [offCompLM, epochHdrWords, epochHashSpace, epochQBits, epochHashB, qBits,
        hashB] at hlm_le ⊢
      omega)
    have hc_lt : 2 * reducedChunkBits
        (reducedTrinomialStep (qBits U N) (hashB N) (totalMicroBits N)) < w :=
      ReducedKWise.two_mul_reducedChunkBits_lt_of_fits_space
        (two_mul_reducedChunkBits_hash_le hw2 hNU hU.le) hfit_h)
  all_goals try (dsimp only [offCompLM, epochHdrWords] at hlm_le; omega)
  all_goals try (refine hfit.of_le ?_; dsimp only [offCompLM, epochHdrWords] at hlm_le; omega)
  · exact (initTableGenProg_spec (k := 3) hc_lt hfr_h hfit_h).1
  · obtain ⟨_, _, _, hfr_tab, _, _⟩ := initTableGenProg_spec (k := 3) hc_lt hfr_h hfit_h
    refine (zeroWordsLoop_spec (w := w) ?_).1
    rw [hfr_tab]
    dsimp only [offCompLM, epochHdrWords] at hlm_le
    omega

theorem initNewEpochMetaProg_spec {w U V N newMetaBase arenaBase : ℕ}
    {θ_new : QuotHashSeed U N} {s₀ : Memory.State}
    (hw : 0 < w) (hN : 1 ≤ N) (hNU : N ≤ U) (hU : Fits w U) (hV : V ≤ 2 ^ w)
    (hfr : newMetaBase + offCompItems U w N ≤ s₀.frontier)
    (hfit : Fits w (newMetaBase + offCompItems U w N))
    (hseed : ReducedKWise.SeedRep (newMetaBase + epochHdrWords)
      (qBits U N) (hashB N) (totalMicroBits N) 3 θ_new s₀.mem) :
    let d := ((mkHashParams w (qBits U N) (hashB N) (totalMicroBits N) 3,
      mkCompParams U V w N), newMetaBase)
    let prog := initNewEpochMetaProg d
    let s' := (Memory.spec 0).clientState s₀ prog
    InitNewEpochMetaPre w d s₀ ∧
    (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ prog) ∧
    memoryCost prog s₀ ≤ 256 * N + 475 ∧
    s'.frontier = s₀.frontier ∧
    ReducedKWise.Rep (newMetaBase + epochHdrWords) w
      (qBits U N) (hashB N) (totalMicroBits N) 3 θ_new s'.mem ∧
    totalSlots N (compGmAt newMetaBase U w N s'.mem) = 0 ∧
    slotPotential N (compGmAt newMetaBase U w N s'.mem) = 0 ∧
    (∃ s_fix₀ : Memory.State,
      DictStateInv U V (ghostW w) N 0 θ_new (Dictionary.empty U) s_fix₀ ∧
      FixedCoupled newMetaBase arenaBase U V w N s_fix₀ s') ∧
    (∀ a, ¬(newMetaBase + epochHdrWords ≤ a ∧ a < newMetaBase + offCompItems U w N) →
      s'.mem a = s₀.mem a) := by
  intro d prog s'
  have h225 : Fits w 225 := fits_const_of_offCompItems hfit le_rfl
  have hw2 : 2 ≤ w := by
    by_contra hlt2
    have hw1 : w ≤ 1 := by omega
    have := Nat.pow_le_pow_right two_pos hw1
    change 225 < 2 ^ w at h225; omega
  have hlm_le : offCompLM U w N ≤ offCompItems U w N := by
    unfold offCompItems offDenseToTail offTailToDense offCompGM; omega
  have hfr_h : (newMetaBase + 225) +
      ReducedKWise.space w (qBits U N) (hashB N) (totalMicroBits N) 3 ≤ s₀.frontier := by
    dsimp only [offCompLM, epochHdrWords, epochHashSpace, epochQBits, epochHashB, qBits,
      hashB] at hlm_le ⊢; omega
  have hfit_h : Fits w ((newMetaBase + 225) +
      ReducedKWise.space w (qBits U N) (hashB N) (totalMicroBits N) 3) := hfit.of_le (by
    dsimp only [offCompLM, epochHdrWords, epochHashSpace, epochQBits, epochHashB, qBits,
      hashB] at hlm_le ⊢; omega)
  have hc_lt : 2 * reducedChunkBits
      (reducedTrinomialStep (qBits U N) (hashB N) (totalMicroBits N)) < w :=
    ReducedKWise.two_mul_reducedChunkBits_lt_of_fits_space
      (two_mul_reducedChunkBits_hash_le hw2 hNU hU.le) hfit_h
  obtain ⟨_, hv_tab, hc_tab, hfr_tab, htab_rep, hframe_tab⟩ :=
    initTableGenProg_spec (k := 3) (s₀ := s₀) hc_lt hfr_h hfit_h
  set s₁ := (Memory.spec 0).clientState s₀
    (initTableGenProg (mkHashParams w (qBits U N) (hashB N) (totalMicroBits N) 3,
      newMetaBase + 225))
  set offLM := offCompLM U w N
  set metaWords := offCompItems U w N - offLM
  have hfr_zw : (newMetaBase + offLM) + metaWords ≤ s₁.frontier := by
    rw [hfr_tab]; dsimp only [metaWords]; omega
  obtain ⟨_, hv_zw, hc_zw, hfr_zw', hz_mem, hframe_zw⟩ :=
    zeroWordsLoop_spec (w := w) (baseAddr := newMetaBase + offLM) (n := metaWords) (s₀ := s₁)
      hfr_zw
  have hs'_eq : s' = (Memory.spec 0).clientState s₁
      (iterate zeroWordsStepProg (newMetaBase + offLM) metaWords 0) := by
    dsimp only [s', prog, d, initNewEpochMetaProg, s₁, offLM, metaWords, offCompLM, epochHdrWords]
    simp only [pure_bind, cpHashSpace_mk, cpOffItems_mk]
    rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
      StateTransitionSpec.clientState_pure]
  have htab_le : 2 ^ (2 * reducedChunkBits
      (reducedTrinomialStep (qBits U N) (hashB N) (totalMicroBits N))) ≤ 8 + N :=
    two_pow_two_mul_reducedChunkBits_hash_le U N
  have hoff_lin := offCompItems_le_linear hw hNU hU
  have hz_range : ∀ a, newMetaBase + offCompLM U w N ≤ a ∧ a < newMetaBase + offCompItems U w N →
      s'.mem a = 0 := fun a ha => by
    rw [hs'_eq]
    have hd_lt : a - (newMetaBase + offLM) < metaWords := by dsimp only [offLM, metaWords]; omega
    have hadd : newMetaBase + offLM + (a - (newMetaBase + offLM)) = a := by
      dsimp only [offLM]; omega
    rw [← hadd]; exact hz_mem _ hd_lt
  have h0_off : offCompLM U w N ≤ offCompGM U w N := Nat.le_add_right _ _
  have h1_off : offCompGM U w N ≤ offTailToDense U w N := Nat.le_add_right _ _
  have h2_off : offTailToDense U w N ≤ offDenseToTail U w N := Nat.le_add_right _ _
  have h3_off : offDenseToTail U w N ≤ offCompItems U w N := Nat.le_add_right _ _
  have hlm_z : compLmAt newMetaBase U w N s'.mem = fun _ => 0 := by
    rw [compLmAt_congr hw (fun a ha => hz_range a ⟨ha.1, by omega⟩)]
    funext ⟨c, idx⟩; unfold compLmAt; dsimp only
    split_ifs with hc
    · exact BitPackedArray.readPacked_zero rfl rfl
    · rfl
  have hgm_z : compGmAt newMetaBase U w N s'.mem = fun _ => 0 := by
    rw [compGmAt_congr hw (fun a ha => hz_range a ⟨by omega, by omega⟩)]
    funext idx; unfold compGmAt
    split_ifs with hidx
    · exact BitPackedArray.readPacked_zero rfl rfl
    · rfl
  have htd_z : compTDAt newMetaBase U w N s'.mem = fun _ => 0 := by
    rw [compTDAt_congr hw (fun a ha => hz_range a ⟨by omega, by omega⟩)]
    funext t; unfold compTDAt
    split_ifs with ht
    · exact BitPackedArray.readPacked_zero rfl rfl
    · rfl
  have hdt_z : compDTAt newMetaBase U w N s'.mem = fun _ => 0 := by
    rw [compDTAt_congr hw (fun a ha => hz_range a ⟨by omega, ha.2⟩)]
    funext r; unfold compDTAt
    split_ifs with hr
    · exact BitPackedArray.readPacked_zero rfl rfl
    · rfl
  let s_fix₀ : Memory.State := ⟨fun _ => 0, 0⟩
  have hgm_fix₀ : gmAt 0 U V (ghostW w) N (hashSpace U (ghostW w) N) s_fix₀.mem = fun _ => 0 := by
    funext i; unfold gmAt
    split_ifs <;> first | exact BitPackedArray.readPacked_zero (mem := s_fix₀.mem) rfl rfl | rfl
  have hlm_fix₀ : lmAt 0 U V (ghostW w) N (hashSpace U (ghostW w) N) s_fix₀.mem = fun _ => 0 := by
    funext ⟨c, idx⟩; unfold lmAt; dsimp only
    split_ifs <;> first | exact BitPackedArray.readPacked_zero (mem := s_fix₀.mem) rfl rfl | rfl
  obtain ⟨hinv₀, hpot₀⟩ := dictStateInv_of_zero (U := U) (V := V) (w₀ := ghostW w)
    (n_max := N) (base := 0) θ_new (s := s_fix₀)
    (fun i => congrFun hgm_fix₀ i) (fun p => congrFun hlm_fix₀ p)
  have htot₀ : totalSlots N (compGmAt newMetaBase U w N s'.mem) = 0 := by
    rw [hgm_z, ← hgm_fix₀, hinv₀.htot]; simp [Dictionary.dom_empty]
  have hpot₀' : slotPotential N (compGmAt newMetaBase U w N s'.mem) = 0 := by
    rw [hgm_z, ← hgm_fix₀]; exact hpot₀
  have hcpl₀ : FixedCoupled newMetaBase arenaBase U V w N s_fix₀ s' := by
    refine ⟨by rw [hgm_z]; exact hgm_fix₀.symm,
      by rw [hlm_z]; exact hlm_fix₀.symm,
      ?_, fun i => by rw [htd_z]; positivity, fun i => by rw [hdt_z]; positivity,
      fun i hi => ?_, fun i hi => ?_⟩
    · have hn0 : (if bucketBits N = 0 then 0 else compGmAt newMetaBase U w N s'.mem 1) = 0 := by
        rw [hgm_z]; split_ifs <;> rfl
      rw [hn0]; exact windowInv_zero _ _ _ _
    · exfalso; change i < totalSlots N (compGmAt newMetaBase U w N s'.mem) at hi; omega
    · exfalso; change i < totalSlots N (compGmAt newMetaBase U w N s'.mem) at hi; omega
  have hrep_hash : ReducedKWise.Rep (newMetaBase + epochHdrWords) w
      (qBits U N) (hashB N) (totalMicroBits N) 3 θ_new s'.mem := by
    have hpres_h : ∀ a, a < newMetaBase + offCompLM U w N → s'.mem a = s₁.mem a := fun a ha => by
      rw [hs'_eq]; exact hframe_zw a (Or.inl ha)
    have htab' : ReducedKWise.TableRep (newMetaBase + epochHdrWords) w
        (qBits U N) (hashB N) (totalMicroBits N) 3 s'.mem :=
      ReducedKWise.tableRep_congr htab_rep (fun a _ hhi => by
        refine (hpres_h a ?_).symm
        dsimp only [offCompLM, epochHdrWords, epochHashSpace, epochQBits, epochHashB, qBits,
          hashB] at hhi ⊢
        omega)
    have hseed₁ : ReducedKWise.SeedRep (newMetaBase + epochHdrWords)
        (qBits U N) (hashB N) (totalMicroBits N) 3 θ_new s₁.mem := by
      refine ⟨?_, fun j m => ?_⟩
      · refine (hframe_tab (newMetaBase + epochHdrWords) (Or.inl ?_)).trans hseed.1
        unfold ReducedKWise.tabBase ReducedKWise.seedWords epochHdrWords; omega
      · have hlt_sw : m.val +
            reducedLimbCount (reducedTrinomialStep (qBits U N) (hashB N) (totalMicroBits N)) *
              j.val <
            3 * reducedLimbCount
              (reducedTrinomialStep (qBits U N) (hashB N) (totalMicroBits N)) := by
          calc m.val + _ * j.val
              < reducedLimbCount _ + reducedLimbCount _ * j.val := Nat.add_lt_add_right m.isLt _
            _ = (j.val + 1) * reducedLimbCount _ := by ring
            _ ≤ 3 * reducedLimbCount _ := Nat.mul_le_mul_right _ j.isLt
        refine (hframe_tab _ (Or.inl ?_)).trans (hseed.2 j m)
        unfold ReducedKWise.tabBase ReducedKWise.seedWords epochHdrWords; omega
    have hseed' : ReducedKWise.SeedRep (newMetaBase + epochHdrWords)
        (qBits U N) (hashB N) (totalMicroBits N) 3 θ_new s'.mem :=
      ReducedKWise.seedRep_congr (w := w) hseed₁ (fun a _ hhi => by
        refine (hpres_h a ?_).symm
        dsimp only [offCompLM, epochHdrWords, epochHashSpace, epochQBits, epochHashB, qBits,
          hashB] at hhi ⊢
        omega)
    exact ⟨htab', hseed'⟩
  refine ⟨⟨U, V, N, hw, hN, hNU, hU, hV, rfl, rfl, hfr, hfit⟩,
    ?_, ?_, by rw [hs'_eq, hfr_zw', hfr_tab], hrep_hash, htot₀, hpot₀',
    ⟨s_fix₀, hinv₀, hcpl₀⟩, fun a ha => ?_⟩
  · dsimp only [prog, d, initNewEpochMetaProg, offCompLM, epochHdrWords]
    simp only [pure_bind, cpHashSpace_mk, cpOffItems_mk]
    rw [validHistory_bind']; refine ⟨hv_tab, ?_⟩
    rw [validHistory_bind']; exact ⟨hv_zw, trivial⟩
  · dsimp only [prog, d, initNewEpochMetaProg, offCompLM, epochHdrWords]
    simp only [pure_bind, cpHashSpace_mk, cpOffItems_mk]
    rw [Realization.memoryCost_bind', Realization.memoryCost_bind', memoryCost_pure]
    change memoryCost (initTableGenProg _) s₀ +
      (memoryCost (iterate zeroWordsStepProg (newMetaBase + offLM) metaWords 0) s₁ + 0) ≤ _
    dsimp only [metaWords, offLM] at hc_zw ⊢
    omega
  · rw [hs'_eq]
    have hzw_out :
        ((Memory.spec 0).clientState s₁
          (iterate zeroWordsStepProg (newMetaBase + offLM) metaWords 0)).mem a = s₁.mem a :=
      hframe_zw a (by dsimp only [offLM, metaWords]; unfold offCompLM at *; omega)
    rw [hzw_out]
    rcases lt_or_ge a (newMetaBase + 225) with hlt | hge
    · exact hframe_tab a (Or.inl (by unfold ReducedKWise.tabBase; omega))
    · have ha_hi : newMetaBase + offCompItems U w N ≤ a := by
        unfold epochHdrWords at ha; omega
      refine hframe_tab a (Or.inr ?_)
      have hsp_le : 225 + ReducedKWise.space w (qBits U N) (hashB N) (totalMicroBits N) 3 ≤
          offCompItems U w N := by
        have hlm' : offCompLM U w N ≤ offCompItems U w N := by
          unfold offCompItems offDenseToTail offTailToDense offCompGM; omega
        dsimp only [offCompLM, epochHdrWords, epochHashSpace, epochQBits, epochHashB] at hlm'
        dsimp only [qBits, hashB]
        exact hlm'
      omega

/-! ## Section 3: Old-Item `(u_i, v_i)` Reconstruction (`readOldItemKeyValGenProg`) -/

private def feistelReconstructProg : CompParams × ((ℕ × ℕ) × ℕ) → Memory.Prog ℕ
  | (cp, ((b, q), hq)) => do
    let b_bits ← pure (cpBucketBits cp)
    let b_mask ← pure (cpBucketMask cp)
    let low ← pure ((hq &&& b_mask) ^^^ (b &&& b_mask))
    pure ((q <<< b_bits) + low)

private def FeistelReconstructPre (w : ℕ) : CompParams × ((ℕ × ℕ) × ℕ) → Memory.State → Prop
  | (cp, ((b, q), hq)), _s =>
    Fits w b ∧ Fits w q ∧ Fits w hq ∧ Fits w (cpBucketBits cp) ∧ Fits w (cpBucketMask cp) ∧
    cpBucketMask cp = 2 ^ cpBucketBits cp - 1 ∧
    Fits w (feistelReconstruct (cpBucketBits cp) (fun _ => hq) b q)

private theorem clientResult_feistelReconstructProg (cp : CompParams) (b q hq : ℕ)
    (hmask : cpBucketMask cp = 2 ^ cpBucketBits cp - 1) (s : Memory.State) :
    (Memory.spec 0).clientResult s (feistelReconstructProg (cp, ((b, q), hq))) =
      feistelReconstruct (cpBucketBits cp) (fun _ => hq) b q := by
  dsimp only [feistelReconstructProg, feistelReconstruct]
  simp only [pure_bind, prog_clientResult_pure, hmask, Nat.shiftLeft_eq,
    Nat.and_two_pow_sub_one_eq_mod]

private theorem clientState_feistelReconstructProg (d : CompParams × ((ℕ × ℕ) × ℕ))
    (s : Memory.State) :
    (Memory.spec 0).clientState s (feistelReconstructProg d) = s := by
  rcases d with ⟨cp, ⟨⟨b, q⟩, hq⟩⟩; rfl

private theorem memoryCost_feistelReconstructProg (d : CompParams × ((ℕ × ℕ) × ℕ))
    (s : Memory.State) :
    memoryCost (feistelReconstructProg d) s = 0 := by
  rcases d with ⟨cp, ⟨⟨b, q⟩, hq⟩⟩; rfl

private theorem realizesBounded_feistelReconstruct :
    RealizesBounded .exact feistelReconstructProg
      (WordEncoding.encode (α := CompParams × ((ℕ × ℕ) × ℕ)))
      (WordEncoding.encode (α := ℕ))
      FeistelReconstructPre (fun _ _ => 0) := by
  realize
  all_goals (
    rcases d with ⟨cp, ⟨⟨b, q⟩, hq⟩⟩
    obtain ⟨hb, hq_fit, hhq, hbb, hbm, hmask, hrec⟩ := h
    dsimp only at *)
  all_goals
    first
    | (refine Nat.xor_lt_two_pow ?_ ?_ <;> exact lt_of_le_of_lt Nat.and_le_right hbm)
    | (rw [Nat.shiftLeft_eq, hmask, Nat.and_two_pow_sub_one_eq_mod,
         Nat.and_two_pow_sub_one_eq_mod]; exact hrec)

private theorem clientState_recoverOwnerBucketGenProg (d : (CompParams × ℕ) × ℕ)
    (s : Memory.State) :
    (Memory.spec 0).clientState s (recoverOwnerBucketGenProg d) = s := by
  rcases d with ⟨⟨cp, metaBase⟩, idx_d⟩
  dsimp only [recoverOwnerBucketGenProg, recoverOwnerTailProg]
  simp only [pure_bind]
  split_ifs with hb0
  · rfl
  · rw [StateTransitionSpec.clientState_bind, clientState_readCompGMGenProg]
    split_ifs with hd_slab
    · exact clientState_readCompGMGenProg _ s
    · rw [StateTransitionSpec.clientState_bind, clientState_readCompDTGenProg,
        StateTransitionSpec.clientState_bind, clientState_readCompGMGenProg,
        StateTransitionSpec.clientState_pure]

private theorem memoryCost_recoverOwnerBucketGenProg_le (d : (CompParams × ℕ) × ℕ)
    (s : Memory.State) :
    memoryCost (recoverOwnerBucketGenProg d) s ≤ 6 := by
  rcases d with ⟨⟨cp, metaBase⟩, idx_d⟩
  dsimp only [recoverOwnerBucketGenProg, recoverOwnerTailProg]
  simp only [pure_bind]
  split_ifs with hb0
  · simp only [memoryCost_pure]; omega
  · rw [Realization.memoryCost_bind', memoryCost_readCompGMGenProg,
      clientState_readCompGMGenProg]
    split_ifs with hd_slab
    · rw [memoryCost_readCompGMGenProg]; omega
    · rw [Realization.memoryCost_bind', memoryCost_readCompDTGenProg,
        clientState_readCompDTGenProg, Realization.memoryCost_bind',
        memoryCost_readCompGMGenProg, clientState_readCompGMGenProg, memoryCost_pure]

/-- Shared quotient-hash evaluation certificate at `(metaBase + 225, metaBase + 63)`. -/
private theorem evalHashAtQuot_spec {w U N metaBase q : ℕ} {θ : QuotHashSeed U N}
    {s₀ : Memory.State}
    (hw : 0 < w) (hNU : N ≤ U) (hU : Fits w U)
    (hfr : metaBase + offCompItems U w N ≤ s₀.frontier)
    (hfit : Fits w (metaBase + offCompItems U w N))
    (hrep : ReducedKWise.Rep (metaBase + epochHdrWords) w (qBits U N) (hashB N)
      (totalMicroBits N) 3 θ s₀.mem)
    (hq_lt : q < 2 ^ quotientBits U N) :
    let hp := mkHashParams w (qBits U N) (hashB N) (totalMicroBits N) 3
    let d := (hp, metaBase + 225, metaBase + 63, q)
    let prog := evalHashGenProg d
    let s' := (Memory.spec 0).clientState s₀ prog
    EvalHashGenPre w d s₀ ∧
    (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ prog) ∧
    memoryCost prog s₀ ≤ 45151 ∧
    (Memory.spec 0).clientResult s₀ prog = hValOfSeed U N θ q ∧
    s'.frontier = s₀.frontier ∧
    (∀ a, ¬(metaBase + 63 ≤ a ∧ a < metaBase + 225) → s'.mem a = s₀.mem a) := by
  intro hp d prog s'
  have h225 : Fits w 225 := fits_const_of_offCompItems hfit le_rfl
  have hw2 : 2 ≤ w := by
    by_contra hlt2
    have hw1 : w ≤ 1 := by omega
    have := Nat.pow_le_pow_right two_pos hw1
    change 225 < 2 ^ w at h225; omega
  have hlm_le : offCompLM U w N ≤ offCompItems U w N := by
    unfold offCompItems offDenseToTail offTailToDense offCompGM; omega
  have hfr_h : (metaBase + 225) +
      ReducedKWise.space w (qBits U N) (hashB N) (totalMicroBits N) 3 ≤ s₀.frontier := by
    dsimp only [offCompLM, epochHdrWords, epochHashSpace, epochQBits, epochHashB, qBits,
      hashB] at hlm_le ⊢; omega
  have hfit_h : Fits w ((metaBase + 225) +
      ReducedKWise.space w (qBits U N) (hashB N) (totalMicroBits N) 3) := hfit.of_le (by
    dsimp only [offCompLM, epochHdrWords, epochHashSpace, epochQBits, epochHashB, qBits,
      hashB] at hlm_le ⊢; omega)
  have hc_lt : 2 * reducedChunkBits
      (reducedTrinomialStep (qBits U N) (hashB N) (totalMicroBits N)) < w :=
    ReducedKWise.two_mul_reducedChunkBits_lt_of_fits_space
      (two_mul_reducedChunkBits_hash_le hw2 hNU hU.le) hfit_h
  have hfr_s : (metaBase + 63) + scratchWords ≤ s₀.frontier := by
    dsimp only [scratchWords]; unfold offCompLM epochHdrWords at hlm_le; omega
  have hfit_s : Fits w ((metaBase + 63) + scratchWords) := hfit.of_le (by
    dsimp only [scratchWords]; unfold offCompLM epochHdrWords at hlm_le; omega)
  have hdisj : (metaBase + 225) +
      ReducedKWise.space w (qBits U N) (hashB N) (totalMicroBits N) 3 ≤ metaBase + 63 ∨
      (metaBase + 63) + scratchWords ≤ metaBase + 225 :=
    Or.inr (by dsimp only [scratchWords]; omega)
  let u_q : Fin (2 ^ quotientBits U N) := ⟨q, hq_lt⟩
  obtain ⟨hpre, hv, hcost, hres, hfr', hout⟩ :=
    evalHashGenProg_spec (w := w) (U := 2 ^ quotientBits U N)
      (w₀ := qBits U N) (b := hashB N) (b' := totalMicroBits N) (k := 3)
      (hashBase := metaBase + 225) (scratchBase := metaBase + 63)
      (θ := θ) (u := u_q) (s₀ := s₀)
      (qBits_pos U N) (qBits_le_of_le_pow hw hU.le)
      (two_pow_quotientBits_le_two_pow_qBits U N)
      (totalMicroBits_le_of_le_pow hNU hU.le) (by decide) hc_lt
      hfr_h hfit_h hfr_s hfit_s hdisj hrep
  have heval_eq : evalMemBound 3 = 45151 := by decide
  have hres_eq : (Memory.spec 0).clientResult s₀ prog = hValOfSeed U N θ q := by
    rw [hres]
    unfold hValOfSeed evalQuotHash
    have hu_eq : u_q = ⟨q % 2 ^ quotientBits U N, Nat.mod_lt _ (Nat.two_pow_pos _)⟩ :=
      Fin.ext (Nat.mod_eq_of_lt hq_lt).symm
    rw [hu_eq]
  exact ⟨hpre, hv, hcost.trans_eq heval_eq, hres_eq, hfr',
    fun a ha => hout a (by dsimp only [scratchWords]; omega)⟩

/-- Reconstruct `(u_d, v_d)` at dense slot `idx_d` of the old epoch (`¬ReadsWidth`). -/
def readOldItemKeyValGenProg :
    ((HashParams × CompParams) × (ℕ × ℕ)) × ℕ → Memory.Prog (ℕ × ℕ)
  | (((oldHp, oldCp), (oldMetaBase, oldItemBase)), idx_d) => do
    let q ← readCompQuotGenProg ((oldCp, oldItemBase), idx_d)
    let v ← readCompValGenProg ((oldCp, oldItemBase), idx_d)
    let b ← recoverOwnerBucketGenProg ((oldCp, oldMetaBase), idx_d)
    let hq ← evalHashGenProg (oldHp, oldMetaBase + 225, oldMetaBase + 63, q)
    let u ← feistelReconstructProg (oldCp, ((b, q), hq))
    pure (u, v)

/-- Entry precondition for `readOldItemKeyValGenProg`. -/
@[expose] def ReadOldItemKeyValPre (w : ℕ) :
    ((HashParams × CompParams) × (ℕ × ℕ)) × ℕ → Memory.State → Prop
  | (((oldHp, oldCp), (oldMetaBase, oldItemBase)), idx_d), s =>
    ∃ U V N n, ∃ θ : QuotHashSeed U N,
      0 < w ∧ 1 ≤ N ∧ N ≤ U ∧ Fits w U ∧ V ≤ 2 ^ w ∧
      oldHp = mkHashParams w (qBits U N) (hashB N) (totalMicroBits N) 3 ∧
      oldCp = mkCompParams U V w N ∧
      oldMetaBase + offCompItems U w N ≤ oldItemBase ∧
      oldItemBase + compactedItemWords U V w N n ≤ s.frontier ∧
      Fits w (oldMetaBase + offCompItems U w N) ∧
      ReducedKWise.Rep (oldMetaBase + epochHdrWords) w (qBits U N) (hashB N)
        (totalMicroBits N) 3 θ s.mem ∧
      SlotStoreInv N (compGmAt oldMetaBase U w N s.mem) ∧
      (0 < bucketBits N →
        TailDenseInv N (compGmAt oldMetaBase U w N s.mem 0) (compGmAt oldMetaBase U w N s.mem 1)
          (compTDAt oldMetaBase U w N s.mem) (compDTAt oldMetaBase U w N s.mem)) ∧
      epochTotalSlots N (compGmAt oldMetaBase U w N s.mem) = n ∧
      idx_d < n ∧
      reconstructKeyAt oldMetaBase oldItemBase U V w N n θ s.mem idx_d < U

theorem readOldItemKeyValGenProg_spec {w U V N n oldMetaBase oldItemBase idx_d : ℕ}
    {θ : QuotHashSeed U N} {s₀ : Memory.State}
    (hw : 0 < w) (hN : 1 ≤ N) (hNU : N ≤ U) (hU : Fits w U) (hV : V ≤ 2 ^ w)
    (hitem : oldMetaBase + offCompItems U w N ≤ oldItemBase)
    (hfr : oldItemBase + compactedItemWords U V w N n ≤ s₀.frontier)
    (hfit : Fits w (oldMetaBase + offCompItems U w N))
    (hrep : ReducedKWise.Rep (oldMetaBase + epochHdrWords) w (qBits U N) (hashB N)
      (totalMicroBits N) 3 θ s₀.mem)
    (hslot : SlotStoreInv N (compGmAt oldMetaBase U w N s₀.mem))
    (htd : 0 < bucketBits N →
      TailDenseInv N (compGmAt oldMetaBase U w N s₀.mem 0) (compGmAt oldMetaBase U w N s₀.mem 1)
        (compTDAt oldMetaBase U w N s₀.mem) (compDTAt oldMetaBase U w N s₀.mem))
    (htot : epochTotalSlots N (compGmAt oldMetaBase U w N s₀.mem) = n)
    (hd : idx_d < n)
    (hrec_lt : reconstructKeyAt oldMetaBase oldItemBase U V w N n θ s₀.mem idx_d < U) :
    let oldHp := mkHashParams w (qBits U N) (hashB N) (totalMicroBits N) 3
    let oldCp := mkCompParams U V w N
    let d := (((oldHp, oldCp), (oldMetaBase, oldItemBase)), idx_d)
    let prog := readOldItemKeyValGenProg d
    let s' := (Memory.spec 0).clientState s₀ prog
    ReadOldItemKeyValPre w d s₀ ∧
    ValidProg w 0 s₀ prog ∧
    memoryCost prog s₀ ≤ 45180 ∧
    (Memory.spec 0).clientResult s₀ prog =
      (reconstructKeyAt oldMetaBase oldItemBase U V w N n θ s₀.mem idx_d,
        compValAt oldItemBase U V w N n s₀.mem idx_d) ∧
    s'.frontier = s₀.frontier ∧
    (∀ a, ¬(oldMetaBase + 63 ≤ a ∧ a < oldMetaBase + 225) → s'.mem a = s₀.mem a) := by
  intro oldHp oldCp d prog s'
  have hmeta_fr : oldMetaBase + offCompItems U w N ≤ s₀.frontier :=
    hitem.trans (le_trans (Nat.le_add_right _ _) hfr)
  have hitem_env : CompItemEnv w oldCp oldItemBase n s₀ :=
    ⟨U, V, N, hw, hN, hNU, hU, hV, rfl, hfr⟩
  have hq_pre : ReadCompQuotPre w ((oldCp, oldItemBase), idx_d) s₀ := ⟨n, hitem_env, hd⟩
  have hv_pre : ReadCompValPre w ((oldCp, oldItemBase), idx_d) s₀ := ⟨n, hitem_env, hd⟩
  have hb_pre : RecoverOwnerBucketPre w ((oldCp, oldMetaBase), idx_d) s₀ :=
    ⟨U, V, N, hw, hN, hNU, hU, hV, rfl, hmeta_fr, hslot, htd, htot.symm ▸ hd⟩
  set q := compQuotAt oldItemBase U V w N n s₀.mem idx_d
  set v := compValAt oldItemBase U V w N n s₀.mem idx_d
  set b := ownerBucketOfDense N (compGmAt oldMetaBase U w N s₀.mem)
    (compDTAt oldMetaBase U w N s₀.mem) idx_d
  have hq_lt : q < 2 ^ quotientBits U N := compQuotAt_lt oldItemBase U V w N n s₀.mem idx_d
  obtain ⟨_, hv_eh, hcost_eh, hres_eh, hfr_eh, hout_eh⟩ :=
    evalHashAtQuot_spec hw hNU hU hmeta_fr hfit hrep hq_lt
  set s₁ := (Memory.spec 0).clientState s₀
    (evalHashGenProg (oldHp, oldMetaBase + 225, oldMetaBase + 63, q))
  have hres_q :=
    clientResult_readCompQuotGenProg (U := U) (V := V) (w := w) (N := N)
      (itemBase := oldItemBase) hd s₀
  have hres_v :=
    clientResult_readCompValGenProg (U := U) (V := V) (w := w) (N := N)
      (itemBase := oldItemBase) hd s₀
  have hres_b := clientResult_recoverOwnerBucketGenProg (V := V) hslot htd (htot.symm ▸ hd)
  have hres_rec : (Memory.spec 0).clientResult s₁
      (feistelReconstructProg (oldCp, ((b, q), hValOfSeed U N θ q))) =
      reconstructKeyAt oldMetaBase oldItemBase U V w N n θ s₀.mem idx_d := by
    rw [clientResult_feistelReconstructProg oldCp b q _ (cpBucketMask_mk U V w N) s₁,
      cpBucketBits_mk]
    unfold reconstructKeyAt
    dsimp only [b, q, feistelReconstruct]
  have hs'_eq : s' = s₁ := by
    dsimp only [s', prog, d, readOldItemKeyValGenProg, oldHp, oldCp, s₁, q, b]
    rw [StateTransitionSpec.clientState_bind, clientState_readCompQuotGenProg, hres_q,
      StateTransitionSpec.clientState_bind, clientState_readCompValGenProg, hres_v,
      StateTransitionSpec.clientState_bind, clientState_recoverOwnerBucketGenProg, hres_b,
      StateTransitionSpec.clientState_bind, hres_eh,
      StateTransitionSpec.clientState_bind, clientState_feistelReconstructProg,
      StateTransitionSpec.clientState_pure]
  refine ⟨⟨U, V, N, n, θ, hw, hN, hNU, hU, hV, rfl, rfl, hitem, hfr, hfit, hrep,
      hslot, htd, htot, hd, hrec_lt⟩,
    ?_, ?_, ?_, hs'_eq ▸ hfr_eh, fun a ha => hs'_eq ▸ hout_eh a ha⟩
  · dsimp only [prog, d, readOldItemKeyValGenProg]
    refine validProg_bind (validProg_readCompQuotGen hq_pre) ?_
    rw [clientState_readCompQuotGenProg, hres_q]
    refine validProg_bind (validProg_readCompValGen hv_pre) ?_
    rw [clientState_readCompValGenProg, hres_v]
    refine validProg_bind (validProg_recoverOwnerBucketGen hb_pre) ?_
    rw [clientState_recoverOwnerBucketGenProg, hres_b]
    refine validProg_bind (fun _ => hv_eh) ?_
    rw [hres_eh]
    refine validProg_bind (fun _ => trivial) ?_
    exact validProg_pure _
  · dsimp only [prog, d, readOldItemKeyValGenProg]
    rw [memoryCost_bind_of_clientState_eq (clientState_readCompQuotGenProg _ s₀) _,
      memoryCost_readCompQuotGenProg, hres_q,
      memoryCost_bind_of_clientState_eq (clientState_readCompValGenProg _ s₀) _,
      memoryCost_readCompValGenProg, hres_v,
      memoryCost_bind_of_clientState_eq (clientState_recoverOwnerBucketGenProg _ s₀) _,
      hres_b, Realization.memoryCost_bind', hres_eh,
      memoryCost_bind_of_clientState_eq (clientState_feistelReconstructProg _ s₁) _,
      memoryCost_feistelReconstructProg, memoryCost_pure]
    have hcb := memoryCost_recoverOwnerBucketGenProg_le ((oldCp, oldMetaBase), idx_d) s₀
    dsimp only [oldHp, oldCp, s₁, q, b] at hcb hcost_eh ⊢
    omega
  · dsimp only [prog, d, readOldItemKeyValGenProg, oldHp, oldCp]
    rw [prog_clientResult_bind, clientState_readCompQuotGenProg, hres_q,
      prog_clientResult_bind, clientState_readCompValGenProg, hres_v,
      prog_clientResult_bind, clientState_recoverOwnerBucketGenProg, hres_b,
      prog_clientResult_bind, hres_eh,
      prog_clientResult_bind, clientState_feistelReconstructProg, hres_rec,
      prog_clientResult_pure]

theorem realizesBounded_readOldItemKeyValGen :
    RealizesBounded .exact readOldItemKeyValGenProg
      (WordEncoding.encode (α := ((HashParams × CompParams) × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      ReadOldItemKeyValPre (fun _ _ => 0) := by
  have hrq := realizesBounded_readCompQuotGen
  have hrv := realizesBounded_readCompValGen
  have hrb := realizesBounded_recoverOwnerBucketGen
  have heh := realizesBounded_evalHashGen
  have hfr_rec := realizesBounded_feistelReconstruct
  realize
  all_goals (
    rcases d with ⟨⟨⟨oldHp, oldCp⟩, ⟨oldMetaBase, oldItemBase⟩⟩, idx_d⟩
    obtain ⟨U, V, N, n, θ, hw, hN, hNU, hU, hV, rfl, rfl, hitem, hfr, hfit, hrep,
      hslot, htd, htot, hd, hrec_lt⟩ := h
    dsimp only at *
    have hmeta_fr : oldMetaBase + offCompItems U w N ≤ s.frontier :=
      hitem.trans (le_trans (Nat.le_add_right _ _) hfr)
    have h225 : Fits w 225 := fits_const_of_offCompItems hfit le_rfl
    have hcp_fit := fits_mkCompParams (U := U) (V := V) (w := w) (N := N) hw hNU hU hV hfit
    have hq_lt : compQuotAt oldItemBase U V w N n s.mem idx_d < 2 ^ quotientBits U N :=
      compQuotAt_lt oldItemBase U V w N n s.mem idx_d)
  all_goals try (
    refine hfit.of_le ?_
    unfold offCompItems offDenseToTail offTailToDense offCompGM offCompLM epochHdrWords
    omega)
  · exact ⟨n, ⟨U, V, N, hw, hN, hNU, hU, hV, rfl, hfr⟩, hd⟩
  · rw [clientState_readCompQuotGenProg]
    exact ⟨n, ⟨U, V, N, hw, hN, hNU, hU, hV, rfl, hfr⟩, hd⟩
  · rw [clientState_readCompValGenProg, clientState_readCompQuotGenProg]
    exact ⟨U, V, N, hw, hN, hNU, hU, hV, rfl, hmeta_fr, hslot, htd, htot.symm ▸ hd⟩
  · rw [clientState_recoverOwnerBucketGenProg, clientState_readCompValGenProg,
      clientState_readCompQuotGenProg,
      clientResult_readCompQuotGenProg (U := U) (V := V) (w := w) (N := N)
        (itemBase := oldItemBase) hd]
    exact (evalHashAtQuot_spec hw hNU hU hmeta_fr hfit hrep hq_lt).1
  · rw [clientState_recoverOwnerBucketGenProg, clientState_readCompValGenProg,
      clientState_readCompQuotGenProg,
      clientResult_readCompQuotGenProg (U := U) (V := V) (w := w) (N := N)
        (itemBase := oldItemBase) hd,
      clientResult_recoverOwnerBucketGenProg (V := V) hslot htd (htot.symm ▸ hd)]
    obtain ⟨_, _, _, hres_eh, _, _⟩ :=
      evalHashAtQuot_spec hw hNU hU hmeta_fr hfit hrep hq_lt
    rw [hres_eh]
    have hb_lt := (ownerBucketOfDense_lt_and_slotOf hslot htd (htot.symm ▸ hd)).1
    have hnb_le : numBuckets N ≤ max N 1 := by
      unfold numBuckets bucketBits
      rcases Nat.eq_zero_or_pos N with rfl | hN_pos
      · decide
      · exact (Nat.pow_le_pow_right two_pos (Nat.sub_le _ _)).trans
          ((Nat.pow_log_le_self 2 hN_pos.ne').trans (le_max_left N 1))
    have hb_fit : Fits w (ownerBucketOfDense N (compGmAt oldMetaBase U w N s.mem)
        (compDTAt oldMetaBase U w N s.mem) idx_d) :=
      lt_of_lt_of_le hb_lt (hnb_le.trans (max_n_one_lt_two_pow_w hw hNU hU).le)
    have hq_fit : Fits w (compQuotAt oldItemBase U V w N n s.mem idx_d) :=
      lt_of_lt_of_le hq_lt (Nat.pow_le_pow_right two_pos (quotientBits_le_of_le_pow hU.le))
    have hhq_fit : Fits w (hValOfSeed U N θ (compQuotAt oldItemBase U V w N n s.mem idx_d)) :=
      (fits_compFeistelCoords (V := V) (s := s) hw hNU hU hV hfit (Nat.two_pow_pos w)
        (hValOfSeed_lt U N θ _)).2.1
    refine ⟨hb_fit, hq_fit, hhq_fit, hcp_fit ⟨20, by decide⟩, hcp_fit ⟨21, by decide⟩,
      cpBucketMask_mk U V w N, ?_⟩
    rw [cpBucketBits_mk]
    exact lt_of_lt_of_le hrec_lt hU.le

/-! ## Section 4: Fresh-Key Streaming Insertion (`streamInsertFreshGenProg`) -/

/-- Insert a fresh `(u, v)` pair (`¬(s_abs ⟨u, hu⟩).isSome`) into `(newMetaBase, arenaBase)`
without duplicate bucket search (`¬ReadsWidth`). -/
def streamInsertFreshGenProg :
    ((HashParams × CompParams) × (ℕ × ℕ)) × (ℕ × ℕ) → Memory.Prog Unit
  | (((newHp, newCp), (newMetaBase, arenaBase)), (u, v)) => do
    let q ← compExtractQuotGenProg (newCp, u)
    let h_q ← evalHashGenProg (newHp, newMetaBase + 225, newMetaBase + 63, q)
    let c ← compFeistelCoordsProg (newCp, (u, h_q))
    let bq ← pure c.1
    compInsertAppendNewGenProg (((newCp, (newMetaBase, arenaBase)), (bq.1, c.2)), (u, v))

/-- Entry precondition for `streamInsertFreshGenProg`. -/
@[expose] def StreamInsertFreshPre (w : ℕ) :
    ((HashParams × CompParams) × (ℕ × ℕ)) × (ℕ × ℕ) → Memory.State → Prop
  | (((newHp, newCp), (newMetaBase, arenaBase)), (u, v)), s =>
    ∃ U V N m_cap, ∃ θ : QuotHashSeed U N, ∃ s_abs : Dictionary.State U, ∃ s_fix : Memory.State,
      ∃ hu : u < U,
        CompEpochEnv U V w N newMetaBase arenaBase m_cap s ∧
        Fits w (newMetaBase + offCompItems U w N) ∧
        newHp = mkHashParams w (qBits U N) (hashB N) (totalMicroBits N) 3 ∧
        newCp = mkCompParams U V w N ∧
        ReducedKWise.Rep (newMetaBase + epochHdrWords) w (qBits U N) (hashB N)
          (totalMicroBits N) 3 θ s.mem ∧
        DictStateInv U V (ghostW w) N 0 θ s_abs s_fix ∧
        FixedCoupled newMetaBase arenaBase U V w N s_fix s ∧
        totalSlots N (compGmAt newMetaBase U w N s.mem) < N ∧
        totalSlots N (compGmAt newMetaBase U w N s.mem) + 1 ≤ m_cap ∧
        v < V ∧
        ¬(s_abs ⟨u, hu⟩).isSome

private theorem fixedCoupled_of_above_lm {metaBase itemBase U V w N : ℕ}
    {s_fix s₀ s₁ : Memory.State} (hw : 0 < w)
    (hitem : metaBase + offCompItems U w N ≤ itemBase)
    (hcpl : FixedCoupled metaBase itemBase U V w N s_fix s₀)
    (habove : ∀ a, metaBase + offCompLM U w N ≤ a → s₁.mem a = s₀.mem a) :
    compGmAt metaBase U w N s₁.mem = compGmAt metaBase U w N s₀.mem ∧
    FixedCoupled metaBase itemBase U V w N s_fix s₁ := by
  have h0_off : offCompLM U w N ≤ offCompGM U w N := Nat.le_add_right _ _
  have h1_off : offCompGM U w N ≤ offTailToDense U w N := Nat.le_add_right _ _
  have h2_off : offTailToDense U w N ≤ offDenseToTail U w N := Nat.le_add_right _ _
  have h3_off : offDenseToTail U w N ≤ offCompItems U w N := Nat.le_add_right _ _
  have hlm_eq := compLmAt_congr (metaBase := metaBase) (U := U) (N := N) hw
    fun a ha => habove a ha.1
  have hgm_eq := compGmAt_congr (metaBase := metaBase) (U := U) (N := N) hw
    fun a ha => habove a (by omega)
  have htd_eq := compTDAt_congr (metaBase := metaBase) (U := U) (N := N) hw
    fun a ha => habove a (by omega)
  have hdt_eq := compDTAt_congr (metaBase := metaBase) (U := U) (N := N) hw
    fun a ha => habove a (by omega)
  have hq_eq : ∀ m, compQuotAt itemBase U V w N m s₁.mem = compQuotAt itemBase U V w N m s₀.mem :=
    fun _ => compQuotAt_congr hw fun a ha => habove a (by omega)
  have hv_eq : ∀ m, compValAt itemBase U V w N m s₁.mem = compValAt itemBase U V w N m s₀.mem :=
    fun _ => compValAt_congr hw fun a ha => habove a (by omega)
  refine ⟨hgm_eq,
    ⟨hgm_eq.trans hcpl.gm_eq, hlm_eq.trans hcpl.lm_eq,
      by rw [hgm_eq, htd_eq, hdt_eq]; exact hcpl.win_inv,
      fun i => by rw [htd_eq]; exact hcpl.td_lt i,
      fun i => by rw [hdt_eq]; exact hcpl.dt_lt i,
      fun d hd => by
        rw [hgm_eq, hq_eq, hdt_eq]
        exact hcpl.quot_eq d (by simpa only [epochTotalSlots, hgm_eq] using hd),
      fun d hd => by
        rw [hgm_eq, hv_eq, hdt_eq]
        exact hcpl.val_eq d (by simpa only [epochTotalSlots, hgm_eq] using hd)⟩⟩

theorem streamInsertFreshGenProg_spec {w U V N m_cap newMetaBase arenaBase u v : ℕ}
    {θ : QuotHashSeed U N} {s_abs : Dictionary.State U} {s_fix s₀ : Memory.State}
    (hu : u < U)
    (henv : CompEpochEnv U V w N newMetaBase arenaBase m_cap s₀)
    (hfit : Fits w (newMetaBase + offCompItems U w N))
    (hrep : ReducedKWise.Rep (newMetaBase + epochHdrWords) w (qBits U N) (hashB N)
      (totalMicroBits N) 3 θ s₀.mem)
    (hinv : DictStateInv U V (ghostW w) N 0 θ s_abs s_fix)
    (hcpl : FixedCoupled newMetaBase arenaBase U V w N s_fix s₀)
    (htot_lt : totalSlots N (compGmAt newMetaBase U w N s₀.mem) < N)
    (hm_cap : totalSlots N (compGmAt newMetaBase U w N s₀.mem) + 1 ≤ m_cap)
    (hv : v < V)
    (hfresh : ¬(s_abs ⟨u, hu⟩).isSome) :
    let newHp := mkHashParams w (qBits U N) (hashB N) (totalMicroBits N) 3
    let newCp := mkCompParams U V w N
    let d := (((newHp, newCp), (newMetaBase, arenaBase)), (u, v))
    let prog := streamInsertFreshGenProg d
    let s' := (Memory.spec 0).clientState s₀ prog
    StreamInsertFreshPre w d s₀ ∧
    ValidProg w 0 s₀ prog ∧
    memoryCost prog s₀ + 98 * slotPotential N (compGmAt newMetaBase U w N s'.mem) ≤
      98 * slotPotential N (compGmAt newMetaBase U w N s₀.mem) + 45360 ∧
    s'.frontier = s₀.frontier ∧
    ReducedKWise.Rep (newMetaBase + epochHdrWords) w (qBits U N) (hashB N)
      (totalMicroBits N) 3 θ s'.mem ∧
    (∃ s_fix' : Memory.State,
      DictStateInv U V (ghostW w) N 0 θ (Function.update s_abs ⟨u, hu⟩ (some v)) s_fix' ∧
      FixedCoupled newMetaBase arenaBase U V w N s_fix' s') ∧
    (∀ a,
      ¬(newMetaBase + 63 ≤ a ∧ a < newMetaBase + 225) →
      ¬(newMetaBase + offCompLM U w N ≤ a ∧ a < newMetaBase + offCompItems U w N) →
      ¬(arenaBase ≤ a ∧ a < arenaBase + compactedItemWords U V w N m_cap) →
      s'.mem a = s₀.mem a) := by
  intro newHp newCp d prog s'
  have hw := henv.pos_w
  have hNU := henv.le_U
  have hU : Fits w U := henv.lt_pow_U
  have hV := henv.le_pow_V
  have hmeta_fr : newMetaBase + offCompItems U w N ≤ s₀.frontier :=
    henv.meta_le_item.trans (le_trans (Nat.le_add_right _ _) henv.item_le_frontier)
  set q := keyQuotient (bucketBits N) u
  have hq_lt : q < 2 ^ quotientBits U N := keyQuotient_lt_two_pow_quotientBits hNU hu
  have hq_res : (Memory.spec 0).clientResult s₀ (compExtractQuotGenProg (newCp, u)) = q :=
    clientResult_compExtractQuotGenProg U V w N u s₀
  obtain ⟨_, hv_eh, hcost_eh, hres_eh, hfr_eh, hout_eh⟩ :=
    evalHashAtQuot_spec hw hNU hU hmeta_fr hfit hrep hq_lt
  set s₁ := (Memory.spec 0).clientState s₀
    (evalHashGenProg (newHp, newMetaBase + 225, newMetaBase + 63, q))
  have henv₁ : CompEpochEnv U V w N newMetaBase arenaBase m_cap s₁ :=
    henv.of_mem_eq (hfr_eh.symm.le)
  have heh_val : epochHdrWords = 225 := rfl
  have h0_off : epochHdrWords ≤ offCompLM U w N := Nat.le_add_right _ _
  obtain ⟨hgm₁, hcpl₁⟩ := fixedCoupled_of_above_lm hw henv.meta_le_item hcpl
    (fun a ha => hout_eh a (by omega))
  have hrep₁ : ReducedKWise.Rep (newMetaBase + epochHdrWords) w (qBits U N) (hashB N)
      (totalMicroBits N) 3 θ s₁.mem :=
    ⟨ReducedKWise.tableRep_congr hrep.1 (fun a h1 _ => (hout_eh a (by omega)).symm),
     ReducedKWise.seedRep_congr (w := w) hrep.2 (fun a h1 _ => (hout_eh a (by omega)).symm)⟩
  have htot₁ : totalSlots N (compGmAt newMetaBase U w N s₁.mem) < N := hgm₁.symm ▸ htot_lt
  have hm_cap₁ : totalSlots N (compGmAt newMetaBase U w N s₁.mem) + 1 ≤ m_cap :=
    hgm₁.symm ▸ hm_cap
  obtain ⟨_, _, _, hfound_iff, _, _⟩ :=
    compInsertSearchWithHashGenProg_dict_spec henv₁ hfit hinv hcpl₁ (by omega) ⟨u, hu⟩
  have hmiss : sbFound ((Memory.spec 0).clientResult s_fix
      (searchBucketProg U V (ghostW w) N (epochHashSpace U (ghostW w) N)
        (((0, feistelBucket (bucketBits N) (hValOfSeed U N θ) u), q),
          mOfSeed U N θ q))) ≠ 1 :=
    mt hfound_iff.mp hfresh
  obtain ⟨hpre_app, hfr_app, hcost_app, s_fix', hinv', hcpl'⟩ :=
    compInsertMiss_dict_spec henv₁ rfl hinv hcpl₁ htot₁ hm_cap₁ ⟨u, hu⟩ v hv hmiss
  set b := feistelBucket (bucketBits N) (hValOfSeed U N θ) u
  set m := mOfSeed U N θ q
  set d_app := (((newCp, (newMetaBase, arenaBase)), (b, m)), (u, v))
  have hc_res : (Memory.spec 0).clientResult s₁
      (compFeistelCoordsProg (newCp, (u, hValOfSeed U N θ q))) = ((b, q), m) :=
    clientResult_compFeistelCoordsProg U V w N u (hValOfSeed U N θ q) s₁
  have hs'_eq : s' = (Memory.spec 0).clientState s₁ (compInsertAppendNewGenProg d_app) := by
    dsimp only [s', prog, d, streamInsertFreshGenProg, newHp, newCp, s₁, d_app]
    rw [StateTransitionSpec.clientState_bind, clientState_compExtractQuotGenProg, hq_res,
      StateTransitionSpec.clientState_bind, hres_eh,
      StateTransitionSpec.clientState_bind, clientState_compFeistelCoordsProg, hc_res]
    simp only [pure_bind]
  have hlm_le : offCompLM U w N ≤ offCompItems U w N := by
    unfold offCompItems offDenseToTail offTailToDense offCompGM; omega
  have hrep' : ReducedKWise.Rep (newMetaBase + epochHdrWords) w (qBits U N) (hashB N)
      (totalMicroBits N) 3 θ s'.mem := by
    have hpres_h : ∀ a, newMetaBase + epochHdrWords ≤ a → a < newMetaBase + offCompLM U w N →
        s'.mem a = s₁.mem a := fun a _ hhi => by
      rw [hs'_eq]
      exact hfr_app.outside_eq a (by omega)
        (by have := henv.meta_le_item; omega)
    exact ⟨ReducedKWise.tableRep_congr hrep₁.1 (fun a h1 h2 =>
        (hpres_h a h1
          (by dsimp only [offCompLM, epochHdrWords, epochHashSpace, epochQBits, epochHashB, qBits,
                hashB] at h2 ⊢; omega)).symm),
      ReducedKWise.seedRep_congr (w := w) hrep₁.2 (fun a h1 h2 =>
        (hpres_h a h1
          (by unfold offCompLM epochHdrWords epochHashSpace ReducedKWise.space at *;
              dsimp only [epochQBits, epochHashB, qBits, hashB] at *; omega)).symm)⟩
  refine ⟨⟨U, V, N, m_cap, θ, s_abs, s_fix, hu, henv, hfit, rfl, rfl, hrep, hinv, hcpl,
      htot_lt, hm_cap, hv, hfresh⟩,
    ?_, ?_, by rw [hs'_eq, hfr_app.frontier_eq, hfr_eh], hrep',
    ⟨s_fix', hinv', hs'_eq ▸ hcpl'⟩, fun a hscr hlm hit => ?_⟩
  · dsimp only [prog, d, streamInsertFreshGenProg]
    refine validProg_bind (validProg_compExtractQuotGen _ _) ?_
    rw [clientState_compExtractQuotGenProg, hq_res]
    refine validProg_bind (fun _ => hv_eh) ?_
    rw [hres_eh]
    refine validProg_bind (validProg_compFeistelCoords _ _) ?_
    rw [clientState_compFeistelCoordsProg, hc_res]
    simp only [pure_bind]
    exact validProg_compInsertAppendNewGen hpre_app
  · dsimp only [prog, d, streamInsertFreshGenProg]
    rw [memoryCost_bind_of_clientState_eq (clientState_compExtractQuotGenProg _ s₀) _,
      memoryCost_compExtractQuotGenProg, hq_res, zero_add,
      Realization.memoryCost_bind', hres_eh,
      memoryCost_bind_of_clientState_eq (clientState_compFeistelCoordsProg _ s₁) _,
      memoryCost_compFeistelCoordsProg, hc_res, zero_add]
    simp only [pure_bind]
    rw [hs'_eq]
    rw [hgm₁] at hcost_app
    dsimp only [newHp, newCp, s₁, d_app] at hcost_eh hcost_app ⊢
    omega
  · rw [hs'_eq, hfr_app.outside_eq a hlm hit, hout_eh a hscr]

theorem realizesBounded_streamInsertFreshGen :
    RealizesBounded .exact streamInsertFreshGenProg
      (WordEncoding.encode (α := ((HashParams × CompParams) × (ℕ × ℕ)) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      StreamInsertFreshPre (fun _ _ => 0) := by
  have heq := realizesBounded_compExtractQuotGen
  have heh := realizesBounded_evalHashGen
  have hfc := realizesBounded_compFeistelCoords
  have hap := realizesBounded_compInsertAppendNewGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨newHp, newCp⟩, ⟨newMetaBase, arenaBase⟩⟩, ⟨u, v⟩⟩
    obtain ⟨U, V, N, m_cap, θ, s_abs, s_fix, hu, henv, hfit, rfl, rfl, hrep, hinv, hcpl,
      htot_lt, hm_cap, hv, hfresh⟩ := h
    dsimp only at *
    have hw := henv.pos_w
    have hNU := henv.le_U
    have hU : Fits w U := henv.lt_pow_U
    have hV := henv.le_pow_V
    have hmeta_fr : newMetaBase + offCompItems U w N ≤ s.frontier :=
      henv.meta_le_item.trans (le_trans (Nat.le_add_right _ _) henv.item_le_frontier)
    have h225 : Fits w 225 := fits_const_of_offCompItems hfit le_rfl
    have hcp_fit := fits_mkCompParams (U := U) (V := V) (w := w) (N := N) hw hNU hU hV hfit
    have hq_lt : keyQuotient (bucketBits N) u < 2 ^ quotientBits U N :=
      keyQuotient_lt_two_pow_quotientBits hNU hu
    have hq_res : (Memory.spec 0).clientResult s
        (compExtractQuotGenProg (mkCompParams U V w N, u)) = keyQuotient (bucketBits N) u :=
      clientResult_compExtractQuotGenProg U V w N u s)
  all_goals try (
    refine hfit.of_le ?_
    unfold offCompItems offDenseToTail offTailToDense offCompGM offCompLM epochHdrWords
    omega)
  · exact ⟨hu.trans hU, hcp_fit ⟨20, by decide⟩⟩
  · rw [clientState_compExtractQuotGenProg, hq_res]
    exact (evalHashAtQuot_spec hw hNU hU hmeta_fr hfit hrep hq_lt).1
  · rw [clientState_compExtractQuotGenProg, hq_res]
    obtain ⟨_, _, _, hres_eh, _, _⟩ := evalHashAtQuot_spec hw hNU hU hmeta_fr hfit hrep hq_lt
    rw [hres_eh]
    exact fits_compFeistelCoords hw hNU hU hV hfit (hu.trans hU) (hValOfSeed_lt U N θ _)
  · rw [clientState_compExtractQuotGenProg, hq_res]
    obtain ⟨_, _, _, hres_eh, hfr_eh, hout_eh⟩ :=
      evalHashAtQuot_spec hw hNU hU hmeta_fr hfit hrep hq_lt
    set s₁ := (Memory.spec 0).clientState s
      (evalHashGenProg (mkHashParams w (qBits U N) (hashB N) (totalMicroBits N) 3,
        newMetaBase + 225, newMetaBase + 63, keyQuotient (bucketBits N) u))
    rw [hres_eh, clientState_compFeistelCoordsProg,
      clientResult_compFeistelCoordsProg U V w N u _ s₁]
    dsimp only
    have henv₁ : CompEpochEnv U V w N newMetaBase arenaBase m_cap s₁ :=
      henv.of_mem_eq hfr_eh.symm.le
    have heh_val : epochHdrWords = 225 := rfl
    have h0_off : epochHdrWords ≤ offCompLM U w N := Nat.le_add_right _ _
    obtain ⟨hgm₁, hcpl₁⟩ := fixedCoupled_of_above_lm hw henv.meta_le_item hcpl
      (fun a ha => hout_eh a (by omega))
    obtain ⟨_, _, _, hfound_iff, _, _⟩ :=
      compInsertSearchWithHashGenProg_dict_spec henv₁ hfit hinv hcpl₁
        (by rw [hgm₁]; omega) ⟨u, hu⟩
    have hmiss := mt hfound_iff.mp hfresh
    exact (compInsertMiss_dict_spec henv₁ rfl hinv hcpl₁ (hgm₁.symm ▸ htot_lt)
      (hgm₁.symm ▸ hm_cap) ⟨u, hu⟩ v hv hmiss).1

/-! ## Section 5: Full `n`-Item Single-Tape Streaming Loop and Relocation -/

/-- Partial dictionary formed by inserting the first `k` reconstructed items of `(s_abs, keyAt)`
into `Dictionary.empty U`. -/
private def streamPartialDict {U : ℕ} (s_abs : Dictionary.State U) (keyAt : ℕ → ℕ) :
    ℕ → Dictionary.State U
  | 0 => Dictionary.empty U
  | k + 1 =>
    let s_prev := streamPartialDict s_abs keyAt k
    if h : keyAt k < U then
      Function.update s_prev ⟨keyAt k, h⟩ (s_abs ⟨keyAt k, h⟩)
    else s_prev

private theorem streamPartialDict_apply {U n k : ℕ} {s_abs : Dictionary.State U} {keyAt : ℕ → ℕ}
    (hkey_lt : ∀ d < n, keyAt d < U) (hk : k ≤ n) (u : Fin U) :
    streamPartialDict s_abs keyAt k u =
      if ∃ d < k, keyAt d = u.val then s_abs u else none := by
  induction k with
  | zero => simp [streamPartialDict, Dictionary.empty]
  | succ k ih =>
    have hku : keyAt k < U := hkey_lt k (by omega)
    dsimp only [streamPartialDict]
    simp only [hku, ↓reduceDIte]
    by_cases heq : u = ⟨keyAt k, hku⟩
    · subst heq
      rw [Function.update_self, ite_eq_left ⟨k, Nat.lt_succ_self k, rfl⟩]
    · rw [Function.update_of_ne heq, ih (by omega)]
      have hne_val : keyAt k ≠ u.val := fun hv => heq (Fin.ext hv.symm)
      have hiff : (∃ d < k + 1, keyAt d = u.val) ↔ (∃ d < k, keyAt d = u.val) :=
        ⟨fun ⟨d, hd, hdu⟩ =>
          ⟨d, by
            rcases eq_or_ne d k with rfl | hne
            · exact absurd hdu hne_val
            · omega, hdu⟩,
         fun ⟨d, hd, hdu⟩ => ⟨d, Nat.lt_succ_of_lt hd, hdu⟩⟩
      simp only [hiff]

private theorem streamPartialDict_not_isSome {U n k : ℕ} {s_abs : Dictionary.State U}
    {keyAt : ℕ → ℕ} (hkey_lt : ∀ d < n, keyAt d < U)
    (hinj : ∀ d₁ < n, ∀ d₂ < n, keyAt d₁ = keyAt d₂ → d₁ = d₂)
    (hk : k < n) (hku : keyAt k < U) :
    ¬(streamPartialDict s_abs keyAt k ⟨keyAt k, hku⟩).isSome := by
  rw [streamPartialDict_apply hkey_lt hk.le]
  have hnot : ¬∃ d < k, keyAt d = keyAt k := fun ⟨d, hd, heq⟩ => by
    have := hinj d (hd.trans hk) k hk heq; omega
  rw [ite_eq_right hnot]; simp

private theorem streamPartialDict_succ {U k v : ℕ} {s_abs : Dictionary.State U} {keyAt : ℕ → ℕ}
    (hku : keyAt k < U) (hv_eq : s_abs ⟨keyAt k, hku⟩ = some v) :
    Function.update (streamPartialDict s_abs keyAt k) ⟨keyAt k, hku⟩ (some v) =
      streamPartialDict s_abs keyAt (k + 1) := by
  dsimp only [streamPartialDict]
  simp only [hku, ↓reduceDIte, hv_eq]

private theorem card_dom_streamPartialDict {U n k : ℕ} {s_abs : Dictionary.State U}
    {keyAt : ℕ → ℕ} (hkey_some : ∀ d < n, ∃ hu : keyAt d < U, (s_abs ⟨keyAt d, hu⟩).isSome)
    (hinj : ∀ d₁ < n, ∀ d₂ < n, keyAt d₁ = keyAt d₂ → d₁ = d₂)
    (hk : k ≤ n) :
    (Dictionary.dom (streamPartialDict s_abs keyAt k)).card = k := by
  have hkey_lt : ∀ d < n, keyAt d < U := fun d hd => (hkey_some d hd).1
  induction k with
  | zero => exact Dictionary.card_dom_empty U
  | succ k ih =>
    obtain ⟨hku, hsome⟩ := hkey_some k (by omega)
    obtain ⟨v, hv_eq⟩ := Option.isSome_iff_exists.mp hsome
    rw [← streamPartialDict_succ hku hv_eq, Dictionary.dom_insert,
      Finset.card_insert_of_notMem, ih (by omega)]
    rw [Dictionary.mem_dom_iff_isSome]
    exact streamPartialDict_not_isSome hkey_lt hinj (by omega) hku

private theorem streamPartialDict_full {U n : ℕ} {s_abs : Dictionary.State U} {keyAt : ℕ → ℕ}
    (hkey_lt : ∀ d < n, keyAt d < U)
    (hsurj : ∀ u : Fin U, (s_abs u).isSome → ∃ d < n, keyAt d = u.val) :
    streamPartialDict s_abs keyAt n = s_abs := by
  funext u
  rw [streamPartialDict_apply hkey_lt le_rfl]
  split_ifs with hex
  · rfl
  · cases hs : s_abs u with
    | none => rfl
    | some v => exact absurd (hsurj u (by simp [hs])) hex

/-- Single step of `streamAllItemsProg` at dense slot `k`. -/
private def streamStepProg :
    (((HashParams × CompParams) × (ℕ × ℕ)) × ((HashParams × CompParams) × (ℕ × ℕ))) × ℕ →
      Memory.Prog ℕ
  | ((oldCtx, newCtx), k) => do
    let uv ← readOldItemKeyValGenProg (oldCtx, k)
    streamInsertFreshGenProg (newCtx, uv)
    pure (k + 1)

/-- Entry precondition for `streamStepProg`. -/
private def StreamStepPre (w : ℕ) :
    (((HashParams × CompParams) × (ℕ × ℕ)) × ((HashParams × CompParams) × (ℕ × ℕ))) × ℕ →
      Memory.State → Prop
  | ((oldCtx, newCtx), k), s =>
    Fits w 1 ∧ Fits w (k + 1) ∧
    ReadOldItemKeyValPre w (oldCtx, k) s ∧
    StreamInsertFreshPre w
      (newCtx, (Memory.spec 0).clientResult s (readOldItemKeyValGenProg (oldCtx, k)))
      ((Memory.spec 0).clientState s (readOldItemKeyValGenProg (oldCtx, k)))

private theorem realizesBounded_streamStep :
    RealizesBounded .exact streamStepProg
      (WordEncoding.encode
        (α := (((HashParams × CompParams) × (ℕ × ℕ)) × ((HashParams × CompParams) × (ℕ × ℕ))) × ℕ))
      (WordEncoding.encode (α := ℕ))
      StreamStepPre (fun _ _ => 0) := by
  have hro := realizesBounded_readOldItemKeyValGen
  have hsi := realizesBounded_streamInsertFreshGen
  realize
  all_goals (
    rcases d with ⟨⟨oldCtx, newCtx⟩, k⟩
    obtain ⟨h1, hk1, hro_pre, hsi_pre⟩ := h
    assumption)

private theorem memoryCost_streamStep_ge_one
    (x : (((HashParams × CompParams) × (ℕ × ℕ)) × ((HashParams × CompParams) × (ℕ × ℕ))) × ℕ)
    (s : Memory.State) :
    1 ≤ memoryCost (streamStepProg x) s := by
  rcases x with ⟨⟨⟨⟨oldHp, oldCp⟩, ⟨oldMetaBase, oldItemBase⟩⟩, newCtx⟩, k⟩
  dsimp only [streamStepProg, readOldItemKeyValGenProg]
  rw [Realization.memoryCost_bind',
    memoryCost_bind_of_clientState_eq (clientState_readCompQuotGenProg _ s) _,
    memoryCost_readCompQuotGenProg]
  omega

/-- Stream `n` items starting from index `a` (`0` for a full epoch migration) from
`(oldMetaBase, oldItemBase)` into `(newMetaBase, arenaBase)` (`¬ReadsWidth`). -/
def streamAllItemsProg :
    ((((HashParams × CompParams) × (ℕ × ℕ)) × ((HashParams × CompParams) × (ℕ × ℕ))) × ℕ) × ℕ →
      Memory.Prog ℕ
  | ((env, a), n) => iterate streamStepProg env n a

/-- Entry precondition for `streamAllItemsProg`. -/
def StreamAllItemsPre (w : ℕ) :
    ((((HashParams × CompParams) × (ℕ × ℕ)) × ((HashParams × CompParams) × (ℕ × ℕ))) × ℕ) × ℕ →
      Memory.State → Prop
  | ((env, a), n), s =>
    iterationSafe streamStepProg StreamStepPre w env n a s

theorem realizesBounded_streamAllItems :
    RealizesBounded .exact streamAllItemsProg
      (WordEncoding.encode
        (α := ((((HashParams × CompParams) × (ℕ × ℕ)) ×
          ((HashParams × CompParams) × (ℕ × ℕ))) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      StreamAllItemsPre (fun _ _ => 0) :=
  RealizesBounded.iterate₀
    (WordEncoding.encode
      (α := ((HashParams × CompParams) × (ℕ × ℕ)) × ((HashParams × CompParams) × (ℕ × ℕ))))
    (WordEncoding.encode (α := ℕ))
    realizesBounded_streamStep memoryCost_streamStep_ge_one

/-- Single-tape zone and epoch-invariant bundle for `streamAllItemsProg_spec`. -/
structure StreamRebuildEnv (U V w N_old N_new n oldMetaBase newMetaBase arenaBase : ℕ)
    (θ_old : QuotHashSeed U N_old) (θ_new : QuotHashSeed U N_new)
    (s_abs : Dictionary.State U) (s₀ : Memory.State) : Prop where
  pos_w : 0 < w
  pos_n : 1 ≤ n
  le_old : n ≤ N_old
  old_le_U : N_old ≤ U
  le_new : n ≤ N_new
  new_le_U : N_new ≤ U
  fits_U : Fits w U
  le_pow_V : V ≤ 2 ^ w
  vals_lt : Dictionary.ValuesBounded V s_abs
  old_le_newMeta : oldMetaBase + offCompItems U w N_old ≤ newMetaBase
  new_le_arena : newMetaBase + offCompItems U w N_new ≤ arenaBase
  arena_le_fr : arenaBase + migrateArenaWords U V w N_old N_new n ≤ s₀.frontier
  fits_new_meta : Fits w (newMetaBase + offCompItems U w N_new)
  old_hash_rep : ReducedKWise.Rep (oldMetaBase + epochHdrWords) w (qBits U N_old) (hashB N_old)
    (totalMicroBits N_old) 3 θ_old s₀.mem
  old_coupled : ∃ s_fix_old : Memory.State,
    DictStateInv U V (ghostW w) N_old 0 θ_old s_abs s_fix_old ∧
    totalSlots N_old (compGmAt oldMetaBase U w N_old s₀.mem) = n ∧
    FixedCoupled oldMetaBase
      (arenaBase + (migrateArenaWords U V w N_old N_new n - compactedItemWords U V w N_old n))
      U V w N_old s_fix_old s₀
  new_hash_rep : ReducedKWise.Rep (newMetaBase + epochHdrWords) w (qBits U N_new) (hashB N_new)
    (totalMicroBits N_new) 3 θ_new s₀.mem
  new_pot_zero : slotPotential N_new (compGmAt newMetaBase U w N_new s₀.mem) = 0
  new_empty_coupled : ∃ s_fix₀ : Memory.State,
    DictStateInv U V (ghostW w) N_new 0 θ_new (Dictionary.empty U) s_fix₀ ∧
    FixedCoupled newMetaBase arenaBase U V w N_new s_fix₀ s₀

private theorem unread_old_quot_val_eq {U V w N_old n oldItemBase d : ℕ}
    {mem₀ mem : ℕ → ℕ} (hw : 0 < w) (hd : d < n)
    (habove : ∀ a, oldItemBase + wOffQ (quotientBits U N_old) (valBits V) w d ≤ a →
      a < oldItemBase + compactedItemWords U V w N_old n → mem a = mem₀ a) :
    compQuotAt oldItemBase U V w N_old n mem d = compQuotAt oldItemBase U V w N_old n mem₀ d ∧
    compValAt oldItemBase U V w N_old n mem d = compValAt oldItemBase U V w N_old n mem₀ d := by
  have hq_lt := wOffQ_add_one_lt_compactedItemWords (U := U) (V := V) (N := N_old) hw hd
  have hv_lt := wOffV_add_one_lt_compactedItemWords (U := U) (V := V) (N := N_old) hw hd
  have hqv_ge : wOffQ (quotientBits U N_old) (valBits V) w d ≤
      wOffV (quotientBits U N_old) (valBits V) w d := Nat.le_add_right _ _
  refine ⟨?_, ?_⟩
  · unfold compQuotAt readBitSlice
    simp only [hd, ↓reduceIte]
    rw [habove _ (by omega) (by omega), habove _ (by omega) (by omega)]
  · unfold compValAt readBitSlice
    simp only [hd, ↓reduceIte]
    rw [habove _ (by omega) (by omega), habove _ (by omega) (by omega)]

theorem streamAllItemsProg_spec {U V w N_old N_new n oldMetaBase newMetaBase arenaBase : ℕ}
    {θ_old : QuotHashSeed U N_old} {θ_new : QuotHashSeed U N_new}
    {s_abs : Dictionary.State U} {s₀ : Memory.State}
    (henv : StreamRebuildEnv U V w N_old N_new n oldMetaBase newMetaBase arenaBase
      θ_old θ_new s_abs s₀) :
    let oldItemBase :=
      arenaBase + (migrateArenaWords U V w N_old N_new n - compactedItemWords U V w N_old n)
    let oldHp := mkHashParams w (qBits U N_old) (hashB N_old) (totalMicroBits N_old) 3
    let oldCp := mkCompParams U V w N_old
    let newHp := mkHashParams w (qBits U N_new) (hashB N_new) (totalMicroBits N_new) 3
    let newCp := mkCompParams U V w N_new
    let d := (((((oldHp, oldCp), (oldMetaBase, oldItemBase)),
      ((newHp, newCp), (newMetaBase, arenaBase))), 0), n)
    let prog := streamAllItemsProg d
    let s' := (Memory.spec 0).clientState s₀ prog
    StreamAllItemsPre w d s₀ ∧
    ValidProg w 0 s₀ prog ∧
    memoryCost prog s₀ + 98 * slotPotential N_new (compGmAt newMetaBase U w N_new s'.mem) ≤
      90540 * n ∧
    s'.frontier = s₀.frontier ∧
    ReducedKWise.Rep (newMetaBase + epochHdrWords) w (qBits U N_new) (hashB N_new)
      (totalMicroBits N_new) 3 θ_new s'.mem ∧
    totalSlots N_new (compGmAt newMetaBase U w N_new s'.mem) = n ∧
    (∃ s_fix' : Memory.State,
      DictStateInv U V (ghostW w) N_new 0 θ_new s_abs s_fix' ∧
      FixedCoupled newMetaBase arenaBase U V w N_new s_fix' s') ∧
    (∀ a, a < oldMetaBase + 63 → s'.mem a = s₀.mem a) ∧
    (∀ a, newMetaBase ≤ a ∧ a < newMetaBase + 63 → s'.mem a = s₀.mem a) := by
  intro oldItemBase oldHp oldCp newHp newCp d prog s'
  have hw := henv.pos_w
  have hU := henv.fits_U
  have hV := henv.le_pow_V
  have hN_old : 1 ≤ N_old := henv.pos_n.trans henv.le_old
  have hN_new : 1 ≤ N_new := henv.pos_n.trans henv.le_new
  have hfit_old : Fits w (oldMetaBase + offCompItems U w N_old) :=
    henv.fits_new_meta.of_le (henv.old_le_newMeta.trans (Nat.le_add_right _ _))
  have hfit1 : Fits w 1 := fits_const_of_offCompItems henv.fits_new_meta (by decide)
  obtain ⟨s_fix_old, hinv_old, htot_old, hcpl_old⟩ := henv.old_coupled
  obtain ⟨L_old, hb_old⟩ := hinv_old.hbucket
  have hslot_old₀ : SlotStoreInv N_old (compGmAt oldMetaBase U w N_old s₀.mem) := by
    rw [hcpl_old.gm_eq]; exact hb_old.hslot
  have htd_old₀ : 0 < bucketBits N_old →
      TailDenseInv N_old (compGmAt oldMetaBase U w N_old s₀.mem 0)
        (compGmAt oldMetaBase U w N_old s₀.mem 1)
        (compTDAt oldMetaBase U w N_old s₀.mem) (compDTAt oldMetaBase U w N_old s₀.mem) :=
    fun hb => hcpl_old.tailDenseInv hb
  obtain ⟨hrec_val, hrec_inj, hrec_surj⟩ :=
    reconstructKeyAt_spec henv.vals_lt henv.old_le_U hinv_old hcpl_old htot_old
  set keyAt := reconstructKeyAt oldMetaBase oldItemBase U V w N_old n θ_old s₀.mem
  have hkey_some : ∀ idx < n, ∃ hu : keyAt idx < U, (s_abs ⟨keyAt idx, hu⟩).isSome :=
    fun idx hidx =>
      let ⟨hu, hs, _⟩ := hrec_val idx hidx
      ⟨hu, by rw [hs]; simp⟩
  have hkey_lt : ∀ idx < n, keyAt idx < U := fun idx hidx => (hkey_some idx hidx).1
  set env := (((oldHp, oldCp), (oldMetaBase, oldItemBase)),
    ((newHp, newCp), (newMetaBase, arenaBase)))
  have hold_iw_le : compactedItemWords U V w N_old n ≤ migrateArenaWords U V w N_old N_new n :=
    (le_max_left _ _).trans (Nat.le_add_right _ 6)
  have hnew_iw_le : compactedItemWords U V w N_new n ≤ migrateArenaWords U V w N_old N_new n :=
    (le_max_right _ _).trans (Nat.le_add_right _ 6)
  have hold_fr₀ : oldItemBase + compactedItemWords U V w N_old n ≤ s₀.frontier := by
    dsimp only [oldItemBase]; have := henv.arena_le_fr; omega
  have hold_meta_le_item : oldMetaBase + offCompItems U w N_old ≤ oldItemBase := by
    dsimp only [oldItemBase]; have := henv.old_le_newMeta; have := henv.new_le_arena; omega
  -- State invariant at step `k ≤ n`
  let loopInv (k : ℕ) (s_k : Memory.State) : Prop :=
    s_k.frontier = s₀.frontier ∧
    ReducedKWise.Rep (newMetaBase + epochHdrWords) w (qBits U N_new) (hashB N_new)
      (totalMicroBits N_new) 3 θ_new s_k.mem ∧
    (∃ s_fix_k : Memory.State,
      DictStateInv U V (ghostW w) N_new 0 θ_new (streamPartialDict s_abs keyAt k) s_fix_k ∧
      FixedCoupled newMetaBase arenaBase U V w N_new s_fix_k s_k) ∧
    (∀ a, a < oldMetaBase + 63 → s_k.mem a = s₀.mem a) ∧
    (∀ a, oldMetaBase + 225 ≤ a ∧ a < newMetaBase + 63 → s_k.mem a = s₀.mem a) ∧
    (∀ a, arenaBase + compactedItemWords U V w N_new k ≤ a → s_k.mem a = s₀.mem a)
  have hloop : ∀ (rem k : ℕ) (s_k : Memory.State), k + rem = n → loopInv k s_k →
      let p_rem := iterate streamStepProg env rem k
      let s_end := (Memory.spec 0).clientState s_k p_rem
      iterationSafe streamStepProg StreamStepPre w env rem k s_k ∧
      ValidProg w 0 s_k p_rem ∧
      memoryCost p_rem s_k + 98 * slotPotential N_new (compGmAt newMetaBase U w N_new s_end.mem) ≤
        98 * slotPotential N_new (compGmAt newMetaBase U w N_new s_k.mem) + 90540 * rem ∧
      loopInv n s_end := by
    intro rem
    induction rem with
    | zero =>
      intro k s_k hsum hinv_k
      have hkn : k = n := by omega
      subst hkn
      dsimp only [iterate]
      refine ⟨trivial, validProg_pure k, ?_, hinv_k⟩
      rw [memoryCost_pure, StateTransitionSpec.clientState_pure]; omega
    | succ rem ih =>
      intro k s_k hsum ⟨hfr_k, hrep_new_k, ⟨s_fix_k, hinv_k, hcpl_k⟩, hlo_k, hmid_k, hhi_k⟩
      have hk_lt : k < n := by omega
      have h0_old : epochHdrWords ≤ offCompLM U w N_old := Nat.le_add_right _ _
      have h1_old : offCompLM U w N_old ≤ offCompGM U w N_old := Nat.le_add_right _ _
      have h2_old : offCompGM U w N_old ≤ offTailToDense U w N_old := Nat.le_add_right _ _
      have h3_old : offTailToDense U w N_old ≤ offDenseToTail U w N_old := Nat.le_add_right _ _
      have h4_old : offDenseToTail U w N_old ≤ offCompItems U w N_old := Nat.le_add_right _ _
      have heh_val : epochHdrWords = 225 := rfl
      have hold_pres : ∀ a, oldMetaBase + 225 ≤ a ∧ a < oldMetaBase + offCompItems U w N_old →
          s_k.mem a = s₀.mem a := fun a ha =>
        hmid_k a ⟨ha.1, lt_of_lt_of_le ha.2 (henv.old_le_newMeta.trans (Nat.le_add_right _ _))⟩
      have hsp_le_old :
          225 + ReducedKWise.space w (qBits U N_old) (hashB N_old) (totalMicroBits N_old) 3 ≤
            offCompItems U w N_old := by
        have hlm_old : offCompLM U w N_old ≤ offCompItems U w N_old := by omega
        dsimp only [offCompLM, epochHdrWords, epochHashSpace, epochQBits, epochHashB] at hlm_old
        dsimp only [qBits, hashB]
        exact hlm_old
      have hrep_old_k : ReducedKWise.Rep (oldMetaBase + epochHdrWords) w (qBits U N_old)
          (hashB N_old) (totalMicroBits N_old) 3 θ_old s_k.mem :=
        ⟨ReducedKWise.tableRep_congr henv.old_hash_rep.1 (fun a h1 h2 =>
            (hold_pres a ⟨by omega, by omega⟩).symm),
         ReducedKWise.seedRep_congr (w := w) henv.old_hash_rep.2 (fun a h1 h2 =>
            (hold_pres a ⟨by omega, by omega⟩).symm)⟩
      have hgm_old_k : compGmAt oldMetaBase U w N_old s_k.mem =
          compGmAt oldMetaBase U w N_old s₀.mem :=
        compGmAt_congr hw fun a ha => hold_pres a ⟨by omega, by omega⟩
      have htd_old_k : compTDAt oldMetaBase U w N_old s_k.mem =
          compTDAt oldMetaBase U w N_old s₀.mem :=
        compTDAt_congr hw fun a ha => hold_pres a ⟨by omega, by omega⟩
      have hdt_old_k : compDTAt oldMetaBase U w N_old s_k.mem =
          compDTAt oldMetaBase U w N_old s₀.mem :=
        compDTAt_congr hw fun a ha => hold_pres a ⟨by omega, ha.2⟩
      have hnonov := newItemEnd_le_oldItemNextWord (U := U) (V := V) (N_old := N_old)
        (N_new := N_new) (n := n) (j := k) hw hk_lt.le
      obtain ⟨hq_old_k, hv_old_k⟩ := unread_old_quot_val_eq (U := U) (V := V) (N_old := N_old)
        (n := n) (oldItemBase := oldItemBase) hw hk_lt
        (fun a ha _ => hhi_k a (by dsimp only [oldItemBase] at ha; omega))
      have hrec_eq_k : reconstructKeyAt oldMetaBase oldItemBase U V w N_old n θ_old s_k.mem k =
          keyAt k := by
        dsimp only [keyAt]
        unfold reconstructKeyAt
        rw [hgm_old_k, hdt_old_k, hq_old_k]
      obtain ⟨hku, hs_val, hv_lt_V⟩ := hrec_val k hk_lt
      change keyAt k < U at hku
      have htot_old_k : epochTotalSlots N_old (compGmAt oldMetaBase U w N_old s_k.mem) = n := by
        rw [hgm_old_k]; exact htot_old
      obtain ⟨hro_pre, hvp_ro, hc_ro, hres_ro, hfr_ro, hout_ro⟩ :=
        readOldItemKeyValGenProg_spec hw hN_old henv.old_le_U hU hV hold_meta_le_item
          (hfr_k.symm ▸ hold_fr₀) hfit_old hrep_old_k
          (hgm_old_k.symm ▸ hslot_old₀)
          (fun hb => by rw [hgm_old_k, htd_old_k, hdt_old_k]; exact htd_old₀ hb)
          htot_old_k hk_lt (hrec_eq_k.symm ▸ hku)
      rw [hrec_eq_k, hv_old_k] at hres_ro
      set s_mid := (Memory.spec 0).clientState s_k
        (readOldItemKeyValGenProg (((oldHp, oldCp), (oldMetaBase, oldItemBase)), k))
      have hnew_ge_old225 : oldMetaBase + 225 ≤ newMetaBase := by
        have := le_offCompItems_225 U w N_old
        have := henv.old_le_newMeta; omega
      have habove_mid : ∀ a, newMetaBase ≤ a → s_mid.mem a = s_k.mem a := fun a ha =>
        hout_ro a (by omega)
      have hrep_new_mid : ReducedKWise.Rep (newMetaBase + epochHdrWords) w (qBits U N_new)
          (hashB N_new) (totalMicroBits N_new) 3 θ_new s_mid.mem :=
        ⟨ReducedKWise.tableRep_congr hrep_new_k.1 (fun a h1 _ =>
            (habove_mid a (by omega)).symm),
         ReducedKWise.seedRep_congr (w := w) hrep_new_k.2 (fun a h1 _ =>
            (habove_mid a (by omega)).symm)⟩
      obtain ⟨hgm_new_mid, hcpl_mid⟩ := fixedCoupled_of_above_lm hw henv.new_le_arena hcpl_k
        (fun a ha => habove_mid a (by omega))
      have hcard_k : (Dictionary.dom (streamPartialDict s_abs keyAt k)).card = k :=
        card_dom_streamPartialDict hkey_some hrec_inj hk_lt.le
      have htot_new_k : totalSlots N_new (compGmAt newMetaBase U w N_new s_k.mem) = k := by
        rw [hcpl_k.gm_eq]
        exact hinv_k.htot.trans hcard_k
      have htot_new_mid : totalSlots N_new (compGmAt newMetaBase U w N_new s_mid.mem) = k :=
        (congrArg (totalSlots N_new) hgm_new_mid).trans htot_new_k
      have henv_ins : CompEpochEnv U V w N_new newMetaBase arenaBase (k + 1) s_mid :=
        ⟨hw, hN_new, henv.new_le_U, hU, hV, henv.new_le_arena, by
          rw [hfr_ro, hfr_k]
          have hcw_le : compactedItemWords U V w N_new (k + 1) ≤
              compactedItemWords U V w N_new n := compactedItemWords_mono hk_lt
          have := henv.arena_le_fr; omega⟩
      have hfresh_k : ¬(streamPartialDict s_abs keyAt k ⟨keyAt k, hku⟩).isSome :=
        streamPartialDict_not_isSome hkey_lt hrec_inj hk_lt hku
      obtain ⟨hsi_pre, hvp_si, hc_si, hfr_si, hrep_new_next, ⟨s_fix_next, hinv_next, hcpl_next⟩,
          hout_si⟩ :=
        streamInsertFreshGenProg_spec hku henv_ins henv.fits_new_meta hrep_new_mid hinv_k hcpl_mid
          (by rw [htot_new_mid]; exact lt_of_lt_of_le hk_lt henv.le_new)
          (by rw [htot_new_mid]) hv_lt_V hfresh_k
      rw [streamPartialDict_succ hku hs_val] at hinv_next
      set s_next := (Memory.spec 0).clientState s_k (streamStepProg (env, k))
      have hs_next_eq : s_next = (Memory.spec 0).clientState s_mid
          (streamInsertFreshGenProg
            (((newHp, newCp), (newMetaBase, arenaBase)),
              (keyAt k, compValAt oldItemBase U V w N_old n s₀.mem k))) := by
        dsimp only [s_next, streamStepProg, env, s_mid]
        rw [StateTransitionSpec.clientState_bind, hres_ro,
          StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_pure]
      have hres_step : (Memory.spec 0).clientResult s_k (streamStepProg (env, k)) = k + 1 := by
        dsimp only [streamStepProg, env]
        rw [prog_clientResult_bind, hres_ro, prog_clientResult_bind, prog_clientResult_pure]
      have hvp_step : ValidProg w 0 s_k (streamStepProg (env, k)) := by
        dsimp only [streamStepProg, env]
        refine validProg_bind hvp_ro ?_
        rw [hres_ro]
        refine validProg_bind hvp_si ?_
        exact validProg_pure _
      have hcost_step : memoryCost (streamStepProg (env, k)) s_k +
          98 * slotPotential N_new (compGmAt newMetaBase U w N_new s_next.mem) ≤
          98 * slotPotential N_new (compGmAt newMetaBase U w N_new s_k.mem) + 90540 := by
        dsimp only [streamStepProg, env]
        rw [Realization.memoryCost_bind', hres_ro, Realization.memoryCost_bind', memoryCost_pure,
          hs_next_eq]
        rw [hgm_new_mid] at hc_si
        dsimp only [oldHp, oldCp, newHp, newCp, oldItemBase, s_mid] at hc_ro hc_si ⊢
        omega
      have h225_new_lm : 225 ≤ offCompLM U w N_new := by
        unfold offCompLM epochHdrWords; omega
      have hlm_le_new : offCompLM U w N_new ≤ offCompItems U w N_new := by
        unfold offCompItems offDenseToTail offTailToDense offCompGM; omega
      have hinv_loop_next : loopInv (k + 1) s_next := by
        refine ⟨by rw [hs_next_eq, hfr_si, hfr_ro, hfr_k],
          hs_next_eq ▸ hrep_new_next,
          ⟨s_fix_next, hinv_next, hs_next_eq ▸ hcpl_next⟩,
          fun a ha => ?_, fun a ha => ?_, fun a ha => ?_⟩
        · rw [hs_next_eq, hout_si a (by omega) (by omega)
            (by have := henv.new_le_arena; omega),
            hout_ro a (by omega)]
          exact hlo_k a ha
        · rw [hs_next_eq, hout_si a (by omega) (by omega)
            (by have := henv.new_le_arena; omega),
            hout_ro a (by omega)]
          exact hmid_k a ha
        · rw [hs_next_eq, hout_si a (by have := henv.new_le_arena; omega)
            (by have := henv.new_le_arena; omega) (by omega),
            hout_ro a (by have := henv.new_le_arena; omega)]
          exact hhi_k a ((Nat.add_le_add_left (compactedItemWords_mono (Nat.le_succ k))
            arenaBase).trans ha)
      obtain ⟨hsafe_rem, hvp_rem, hc_rem, hinv_end⟩ :=
        ih (k + 1) s_next (by omega) hinv_loop_next
      have hk1_fit : Fits w (k + 1) := hU.of_le (hk_lt.trans_le (henv.le_old.trans henv.old_le_U))
      have hstep_pre : StreamStepPre w (env, k) s_k := by
        refine ⟨hfit1, hk1_fit, hro_pre, ?_⟩
        rw [hres_ro]; exact hsi_pre
      dsimp only [iterate]
      have hs_end_eq : (Memory.spec 0).clientState s_k
          (streamStepProg (env, k) >>= iterate streamStepProg env rem) =
          (Memory.spec 0).clientState s_next (iterate streamStepProg env rem (k + 1)) := by
        rw [StateTransitionSpec.clientState_bind, hres_step]
      refine ⟨⟨hstep_pre, by rw [hres_step]; exact hsafe_rem⟩,
        validProg_bind hvp_step (by rw [hres_step]; exact hvp_rem), ?_,
        by rw [hs_end_eq]; exact hinv_end⟩
      rw [Realization.memoryCost_bind', hres_step, hs_end_eq]
      dsimp only [s_next] at hcost_step hc_rem ⊢
      omega
  obtain ⟨s_fix₀, hinv₀, hcpl₀⟩ := henv.new_empty_coupled
  have hinv_0 : loopInv 0 s₀ :=
    ⟨rfl, henv.new_hash_rep, ⟨s_fix₀, hinv₀, hcpl₀⟩, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
  obtain ⟨hsafe_all, hvp_all, hc_all, hfr_end, hrep_end, ⟨s_fix_end, hinv_end, hcpl_end⟩,
      hlo_end, hmid_end, _⟩ :=
    hloop n 0 s₀ (Nat.zero_add n) hinv_0
  rw [henv.new_pot_zero, Nat.mul_zero, Nat.zero_add] at hc_all
  rw [streamPartialDict_full hkey_lt hrec_surj] at hinv_end
  have hs'_eq : s' = (Memory.spec 0).clientState s₀ (iterate streamStepProg env n 0) := rfl
  have htot_end : totalSlots N_new (compGmAt newMetaBase U w N_new s'.mem) = n := by
    have hcard_n := card_dom_streamPartialDict hkey_some hrec_inj le_rfl
    rw [streamPartialDict_full hkey_lt hrec_surj] at hcard_n
    exact (congrArg (totalSlots N_new) hcpl_end.gm_eq).trans (hinv_end.htot.trans hcard_n)
  refine ⟨hsafe_all, hvp_all, hc_all, hfr_end, hrep_end, htot_end,
    ⟨s_fix_end, hinv_end, hcpl_end⟩,
    fun a ha => hlo_end a ha,
    fun a ha => hmid_end a ⟨by
      have := le_offCompItems_225 U w N_old
      have := henv.old_le_newMeta; omega, ha.2⟩⟩

/-- Relocate an active compacted epoch representation from `(srcMetaBase, srcItemBase)` to
`(base, base + offCompItems U w N)` after leftward block copy. -/
theorem compactedSplitRep_of_reloc {U V w N n n_init srcMetaBase srcItemBase base : ℕ}
    {θ : QuotHashSeed U N} {s_abs : Dictionary.State U} {s_src s_dst : Memory.State}
    (hw : 0 < w)
    (hhdr : RootHeaderValid U V w N n n_init srcMetaBase s_src.mem)
    (hpar : EpochParamsStored U V w N srcMetaBase s_src.mem)
    (hhash : ReducedKWise.Rep (srcMetaBase + epochHdrWords) w (qBits U N) (hashB N)
      (totalMicroBits N) 3 θ s_src.mem)
    (hcard : (Dictionary.dom s_abs).card = n)
    (hvals : Dictionary.ValuesBounded V s_abs)
    (hinv_cpl : ∃ s_fix : Memory.State,
      DictStateInv U V (ghostW w) N 0 θ s_abs s_fix ∧
      FixedCoupled srcMetaBase srcItemBase U V w N s_fix s_src)
    (hmeta_eq : ∀ j < offCompItems U w N, s_dst.mem (base + j) = s_src.mem (srcMetaBase + j))
    (hitem_eq : ∀ j < compactedItemWords U V w N n,
      s_dst.mem (base + offCompItems U w N + j) = s_src.mem (srcItemBase + j)) :
    CompactedSplitRep base (base + offCompItems U w N) U V w N n n_init θ s_abs s_dst ∧
    compGmAt base U w N s_dst.mem = compGmAt srcMetaBase U w N s_src.mem := by
  have heh : epochHdrWords = 225 := rfl
  have h0_off : epochHdrWords ≤ offCompLM U w N := Nat.le_add_right _ _
  have h1_off : offCompLM U w N ≤ offCompGM U w N := Nat.le_add_right _ _
  have h2_off : offCompGM U w N ≤ offTailToDense U w N := Nat.le_add_right _ _
  have h3_off : offTailToDense U w N ≤ offDenseToTail U w N := Nat.le_add_right _ _
  have h4_off : offDenseToTail U w N ≤ offCompItems U w N := Nat.le_add_right _ _
  have h225_le : 225 ≤ offCompItems U w N := by omega
  let mem_meta (a : ℕ) : ℕ := s_dst.mem (base + (a - srcMetaBase))
  let mem_item (a : ℕ) : ℕ := s_dst.mem (base + offCompItems U w N + (a - srcItemBase))
  have hmeta_congr : ∀ a, srcMetaBase ≤ a ∧ a < srcMetaBase + offCompItems U w N →
      mem_meta a = s_src.mem a := fun a ha => by
    dsimp only [mem_meta]
    have hj : a - srcMetaBase < offCompItems U w N := by omega
    rw [hmeta_eq _ hj, Nat.add_sub_of_le ha.1]
  have hitem_congr : ∀ a, srcItemBase ≤ a ∧ a < srcItemBase + compactedItemWords U V w N n →
      mem_item a = s_src.mem a := fun a ha => by
    dsimp only [mem_item]
    have hj : a - srcItemBase < compactedItemWords U V w N n := by omega
    rw [hitem_eq _ hj, Nat.add_sub_of_le ha.1]
  have hhdr_dst : RootHeaderValid U V w N n n_init base s_dst.mem :=
    ⟨hhdr.fits_U, hhdr.pos_U, hhdr.pos_V,
      by simpa using (hmeta_eq 0 (by omega)).trans (by simpa using hhdr.hdr_U),
      (hmeta_eq 1 (by omega)).trans hhdr.hdr_V,
      (hmeta_eq 2 (by omega)).trans hhdr.hdr_w,
      (hmeta_eq 3 (by omega)).trans hhdr.hdr_keyBits,
      (hmeta_eq 4 (by omega)).trans hhdr.hdr_valBits,
      (hmeta_eq 5 (by omega)).trans hhdr.hdr_N,
      (hmeta_eq 6 (by omega)).trans hhdr.hdr_n,
      (hmeta_eq 7 (by omega)).trans hhdr.hdr_n_init⟩
  have hpar_dst : EpochParamsStored U V w N base s_dst.mem :=
    ⟨fun i => by
      have hj : offHashParams + i.val < offCompItems U w N := by unfold offHashParams; omega
      have h1 := hmeta_eq (offHashParams + i.val) hj
      rw [← Nat.add_assoc, ← Nat.add_assoc] at h1
      exact h1.trans (hpar.hp_eq i),
     fun i => by
      have hj : offCompParams + i.val < offCompItems U w N := by unfold offCompParams; omega
      have h1 := hmeta_eq (offCompParams + i.val) hj
      rw [← Nat.add_assoc, ← Nat.add_assoc] at h1
      exact h1.trans (hpar.cp_eq i)⟩
  have hsp_le : 225 + ReducedKWise.space w (qBits U N) (hashB N) (totalMicroBits N) 3 ≤
      offCompItems U w N := by
    have hlm : offCompLM U w N ≤ offCompItems U w N := by omega
    dsimp only [offCompLM, epochHdrWords, epochHashSpace, epochQBits, epochHashB] at hlm
    dsimp only [qBits, hashB]
    exact hlm
  have htab_mid : ReducedKWise.TableRep (srcMetaBase + epochHdrWords) w (qBits U N) (hashB N)
      (totalMicroBits N) 3 mem_meta :=
    ReducedKWise.tableRep_congr hhash.1 fun a h1 h2 =>
      (hmeta_congr a ⟨by omega, by omega⟩).symm
  have hseed_mid : ReducedKWise.SeedRep (srcMetaBase + epochHdrWords) (qBits U N) (hashB N)
      (totalMicroBits N) 3 θ mem_meta :=
    ReducedKWise.seedRep_congr (w := w) hhash.2 fun a h1 h2 =>
      (hmeta_congr a ⟨by omega, by omega⟩).symm
  have hmem_meta_add : ∀ off, mem_meta (srcMetaBase + off) = s_dst.mem (base + off) :=
    fun off => by dsimp only [mem_meta]; rw [Nat.add_sub_cancel_left]
  have hmem_item_add : ∀ off,
      mem_item (srcItemBase + off) = s_dst.mem (base + offCompItems U w N + off) :=
    fun off => by dsimp only [mem_item]; rw [Nat.add_sub_cancel_left]
  have hhash_dst : ReducedKWise.Rep (base + epochHdrWords) w (qBits U N) (hashB N)
      (totalMicroBits N) 3 θ s_dst.mem := by
    refine ⟨⟨fun wIdx hw_lt => ?_, fun idx hidx_lt => ?_⟩, ⟨?_, fun j m => ?_⟩⟩
    · have h := htab_mid.1 wIdx hw_lt
      dsimp only [ReducedKWise.tabBase] at h ⊢
      simpa only [Nat.add_assoc, hmem_meta_add] using h
    · have h := htab_mid.2 idx hidx_lt
      dsimp only [ReducedKWise.tabBase] at h ⊢
      simpa only [Nat.add_assoc, hmem_meta_add] using h
    · have h := hseed_mid.1
      simpa only [Nat.add_assoc, hmem_meta_add] using h
    · have h := hseed_mid.2 j m
      simpa only [Nat.add_assoc, hmem_meta_add] using h
  have hlm_eq : compLmAt base U w N s_dst.mem = compLmAt srcMetaBase U w N s_src.mem := by
    have hmid := compLmAt_congr (metaBase := srcMetaBase) (U := U) (N := N) hw
      fun a ha => hmeta_congr a ⟨by omega, by omega⟩
    rw [← hmid]; funext ⟨c, idx⟩; unfold compLmAt readPacked readBitSlice; dsimp only
    split_ifs with hc
    · simp only [Nat.add_assoc, hmem_meta_add]
    · rfl
  have hgm_eq : compGmAt base U w N s_dst.mem = compGmAt srcMetaBase U w N s_src.mem := by
    have hmid := compGmAt_congr (metaBase := srcMetaBase) (U := U) (N := N) hw
      fun a ha => hmeta_congr a ⟨by omega, by omega⟩
    rw [← hmid]; funext idx; unfold compGmAt readPacked readBitSlice; dsimp only
    split_ifs with hidx
    · simp only [Nat.add_assoc, hmem_meta_add]
    · rfl
  have htd_eq : compTDAt base U w N s_dst.mem = compTDAt srcMetaBase U w N s_src.mem := by
    have hmid := compTDAt_congr (metaBase := srcMetaBase) (U := U) (N := N) hw
      fun a ha => hmeta_congr a ⟨by omega, by omega⟩
    rw [← hmid]; funext idx; unfold compTDAt readPacked readBitSlice; dsimp only
    split_ifs with hidx
    · simp only [Nat.add_assoc, hmem_meta_add]
    · rfl
  have hdt_eq : compDTAt base U w N s_dst.mem = compDTAt srcMetaBase U w N s_src.mem := by
    have hmid := compDTAt_congr (metaBase := srcMetaBase) (U := U) (N := N) hw
      fun a ha => hmeta_congr a ⟨by omega, ha.2⟩
    rw [← hmid]; funext idx; unfold compDTAt readPacked readBitSlice; dsimp only
    split_ifs with hidx
    · simp only [Nat.add_assoc, hmem_meta_add]
    · rfl
  have hq_eq : compQuotAt (base + offCompItems U w N) U V w N n s_dst.mem =
      compQuotAt srcItemBase U V w N n s_src.mem := by
    have hmid := compQuotAt_congr (itemBase := srcItemBase) (U := U) (V := V) (N := N) (n := n) hw
      hitem_congr
    rw [← hmid]; funext idx; unfold compQuotAt readBitSlice; dsimp only
    split_ifs with hidx
    · simp only [Nat.add_assoc, hmem_item_add]
    · rfl
  have hv_eq : compValAt (base + offCompItems U w N) U V w N n s_dst.mem =
      compValAt srcItemBase U V w N n s_src.mem := by
    have hmid := compValAt_congr (itemBase := srcItemBase) (U := U) (V := V) (N := N) (n := n) hw
      hitem_congr
    rw [← hmid]; funext idx; unfold compValAt readBitSlice; dsimp only
    split_ifs with hidx
    · simp only [Nat.add_assoc, hmem_item_add]
    · rfl
  obtain ⟨s_fix, hinv, hcpl⟩ := hinv_cpl
  have htot_src : totalSlots N (compGmAt srcMetaBase U w N s_src.mem) = n :=
    (congrArg (totalSlots N) hcpl.gm_eq).trans (hinv.htot.trans hcard)
  have htot_dst : totalSlots N (compGmAt base U w N s_dst.mem) = n :=
    (congrArg (totalSlots N) hgm_eq).trans htot_src
  refine ⟨⟨hhdr_dst, hpar_dst, hhash_dst, hcard, hvals, s_fix, hinv, htot_dst,
    ⟨hgm_eq.trans hcpl.gm_eq, hlm_eq.trans hcpl.lm_eq,
      by rw [hgm_eq, htd_eq, hdt_eq]; exact hcpl.win_inv,
      fun i => by rw [htd_eq]; exact hcpl.td_lt i,
      fun i => by rw [hdt_eq]; exact hcpl.dt_lt i,
      fun d hd => by
        have hd_n : d < n := by change d < totalSlots N _ at hd; omega
        have hd_src : d < epochTotalSlots N (compGmAt srcMetaBase U w N s_src.mem) := by
          change d < totalSlots N (compGmAt srcMetaBase U w N s_src.mem); omega
        have hq0 := hcpl.quot_eq d hd_src
        rw [compQuotAt_of_lt s_dst.mem hd (n₂ := n) hd_n, hq_eq,
          compQuotAt_of_lt s_src.mem hd_n hd_src, hgm_eq, hdt_eq]
        exact hq0,
      fun d hd => by
        have hd_n : d < n := by change d < totalSlots N _ at hd; omega
        have hd_src : d < epochTotalSlots N (compGmAt srcMetaBase U w N s_src.mem) := by
          change d < totalSlots N (compGmAt srcMetaBase U w N s_src.mem); omega
        have hv0 := hcpl.val_eq d hd_src
        rw [compValAt_of_lt s_dst.mem hd (n₂ := n) hd_n, hv_eq,
          compValAt_of_lt s_src.mem hd_n hd_src, hgm_eq, hdt_eq]
        exact hv0⟩⟩,
    hgm_eq⟩

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct
