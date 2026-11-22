/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Accessors
import CslibFrontier.Tactic.WramOmega

/-!
# Metadata and Circular-Window `Memory.Prog` Primitives

This module builds on `Accessors.lean` to provide `RealizesBounded .exact` (`¬ReadsWidth`)
`Memory.Prog` primitives for:
* dense item copy/clear (`copyCompItemGenProg`, `clearCompItemGenProg`);
* compacted metadata arrays (`readCompLMGenProg`, `writeCompLMGenProg`, `readCompGMGenProg`,
  `writeCompGMGenProg`, `readCompTDGenProg`, `writeCompTDGenProg`, `readCompDTGenProg`,
  `writeCompDTGenProg`);
* circular tail-to-dense window transitions (`denseOfCircGenProg`, `denseOfPhysGenProg`,
  `winGrowRightGenProg`, `winGrowLeftGenProg`, `winShrinkRightGenProg`, `winShrinkLeftGenProg`).

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.readCompLMGenProg`,
  `writeCompLMGenProg`, `readCompGMGenProg`, `writeCompGMGenProg`, `readCompTDGenProg`,
  `writeCompTDGenProg`, `readCompDTGenProg`, `writeCompDTGenProg`: metadata accessors.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.denseOfCircGenProg`,
  `denseOfPhysGenProg`, `winGrowRightGenProg`, `winGrowLeftGenProg`, `winShrinkRightGenProg`,
  `winShrinkLeftGenProg`: circular window `Memory.Prog` operations.

## Main results

* `realizesBounded_denseOfPhysGen`, `realizesBounded_winGrowRightGen`,
  `realizesBounded_winGrowLeftGen`, `realizesBounded_winShrinkRightGen`,
  `realizesBounded_winShrinkLeftGen`: parameter-free `RealizesBounded .exact` certificates.
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

attribute [local simp] Realization.memoryCost_bind'
attribute [local simp] prog_clientResult_bind prog_runClient_state_bind prog_clientResult_pure
attribute [local simp] prog_runClient_state_pure prog_clientResult_map prog_runClient_state_map
attribute [local simp] prog_memoryCost_map prog_clientResult_read prog_runClient_state_read
attribute [local simp] prog_memoryCost_read prog_clientResult_write prog_runClient_state_write
attribute [local simp] prog_memoryCost_write

/-! ## Section 1: Item Copy/Clear and Metadata Array Accessors -/

private theorem encode_fst {α β : Type} [WordEncoding α] [WordEncoding β]
    (a : α) (b : β) (i : Fin (WordEncoding.width α)) :
    WordEncoding.encode (a, b) (Fin.castAdd (WordEncoding.width β) i) =
      WordEncoding.encode a i :=
  Fin.append_left _ _ i

private class HasCompEnv (δ : Type) [WordEncoding δ] where
  eb : δ → CompParams × ℕ
  ix : Fin 37 → Fin (WordEncoding.width δ)
  eq : ∀ d i, WordEncoding.encode (eb d) i = WordEncoding.encode d (ix i)

private instance : HasCompEnv (CompParams × ℕ) := ⟨id, id, fun _ _ => rfl⟩

private instance {δ β : Type} [WordEncoding δ] [WordEncoding β] [h : HasCompEnv δ] :
    HasCompEnv (δ × β) where
  eb x := h.eb x.1
  ix i := Fin.castAdd _ (h.ix i)
  eq x i := (h.eq x.1 i).trans (encode_fst x.1 x.2 (h.ix i)).symm

@[simp] private theorem hasCompEnv_eb_base (e : CompParams × ℕ) : HasCompEnv.eb e = e := rfl
@[simp] private theorem hasCompEnv_eb_prod {δ β : Type} [WordEncoding δ] [WordEncoding β]
    [HasCompEnv δ] (x : δ × β) : HasCompEnv.eb x = HasCompEnv.eb x.1 := rfl

private theorem liftComp1 {δ γ : Type} [WordEncoding δ] [WordEncoding γ] [hE : HasCompEnv δ]
    {p : (CompParams × ℕ) × ℕ → Memory.Prog γ}
    {safe : ℕ → (CompParams × ℕ) × ℕ → Memory.State → Prop}
    (h : RealizesBounded .exact p (WordEncoding.encode (α := (CompParams × ℕ) × ℕ))
      (WordEncoding.encode (α := γ)) safe (fun _ _ => 0))
    (xOf : δ → ℕ) (ix_x : Fin (WordEncoding.width δ))
    (hx : ∀ d, xOf d = WordEncoding.encode d ix_x) :
    RealizesBounded .exact (fun d => p (hE.eb d, xOf d))
      (WordEncoding.encode (α := δ)) (WordEncoding.encode (α := γ))
      (fun w d s => safe w (hE.eb d, xOf d) s) (fun _ _ => 0) :=
  h.reindex (fun d => (hE.eb d, xOf d)) _ (Fin.addCases hE.ix fun _ => ix_x) fun d i => by
    refine Fin.addCases (fun i₀ => ?_) (fun j => ?_) i
    · rw [Fin.addCases_left]; exact (encode_fst _ _ i₀).trans (hE.eq d i₀)
    · fin_cases j; exact hx d

private theorem liftComp2 {δ γ : Type} [WordEncoding δ] [WordEncoding γ] [hE : HasCompEnv δ]
    {p : ((CompParams × ℕ) × ℕ) × ℕ → Memory.Prog γ}
    {safe : ℕ → ((CompParams × ℕ) × ℕ) × ℕ → Memory.State → Prop}
    (h : RealizesBounded .exact p (WordEncoding.encode (α := ((CompParams × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := γ)) safe (fun _ _ => 0))
    (xOf yOf : δ → ℕ) (ix_x ix_y : Fin (WordEncoding.width δ))
    (hx : ∀ d, xOf d = WordEncoding.encode d ix_x)
    (hy : ∀ d, yOf d = WordEncoding.encode d ix_y) :
    RealizesBounded .exact (fun d => p ((hE.eb d, xOf d), yOf d))
      (WordEncoding.encode (α := δ)) (WordEncoding.encode (α := γ))
      (fun w d s => safe w ((hE.eb d, xOf d), yOf d) s) (fun _ _ => 0) :=
  h.reindex (fun d => ((hE.eb d, xOf d), yOf d)) _
    (Fin.addCases (Fin.addCases hE.ix fun _ => ix_x) fun _ => ix_y) fun d i => by
    refine Fin.addCases (fun i₁ => ?_) (fun j₁ => ?_) i
    · rw [Fin.addCases_left, encode_fst]
      refine Fin.addCases (fun i₀ => ?_) (fun j₀ => ?_) i₁
      · rw [Fin.addCases_left]; exact (encode_fst _ _ i₀).trans (hE.eq d i₀)
      · fin_cases j₀; exact hx d
    · fin_cases j₁; exact hy d

/-- Copy `(quot, val)` from dense slot `src` to `dst` at `itemBase`. -/
def copyCompItemGenProg : (CompParams × ℕ) × (ℕ × ℕ) → Memory.Prog Unit
  | ((cp, itemBase), (src, dst)) => do
    let q ← readCompQuotGenProg ((cp, itemBase), src)
    let v ← readCompValGenProg ((cp, itemBase), src)
    writeCompQuotGenProg (((cp, itemBase), dst), q)
    writeCompValGenProg (((cp, itemBase), dst), v)

@[simp] theorem clientResult_copyCompItemGenProg
    (d : (CompParams × ℕ) × (ℕ × ℕ)) (s : Memory.State) :
    (Memory.spec 0).clientResult s (copyCompItemGenProg d) = () := by
  rcases d with ⟨⟨cp, itemBase⟩, ⟨src, dst⟩⟩; simp [copyCompItemGenProg]
theorem clientState_copyCompItemGenProg {U V w N m_items itemBase src dst : ℕ}
    (hsrc : src < m_items) (s : Memory.State) :
    (Memory.spec 0).clientState s
        (copyCompItemGenProg ((mkCompParams U V w N, itemBase), (src, dst))) =
      { mem := writeCompVal itemBase U V w N
          (writeCompQuot itemBase U V w N s.mem dst (compQuotAt itemBase U V w N m_items s.mem src))
          dst (compValAt itemBase U V w N m_items s.mem src),
        frontier := s.frontier } := by
  unfold StateTransitionSpec.clientState
  simp only [copyCompItemGenProg, prog_runClient_state_bind, StateTransitionSpec.clientState,
    clientResult_readCompQuotGenProg hsrc, runClient_state_readCompQuotGenProg,
    clientResult_readCompValGenProg hsrc, runClient_state_readCompValGenProg,
    runClient_state_writeCompQuotGenProg, runClient_state_writeCompValGenProg]
@[simp] theorem memoryCost_copyCompItemGenProg
    (d : (CompParams × ℕ) × (ℕ × ℕ)) (s : Memory.State) :
    memoryCost (copyCompItemGenProg d) s = 12 := by
  rcases d with ⟨⟨cp, itemBase⟩, ⟨src, dst⟩⟩; simp [copyCompItemGenProg]
/-- Precondition for copying an item between two compacted item slots. -/
@[expose] def CopyCompItemPre (w : ℕ) : (CompParams × ℕ) × (ℕ × ℕ) → Memory.State → Prop
  | ((cp, itemBase), (src, dst)), s =>
    ∃ m_items, CompItemEnv w cp itemBase m_items s ∧ src < m_items ∧ dst < m_items
theorem realizesBounded_copyCompItemGen :
    RealizesBounded .exact copyCompItemGenProg
      (WordEncoding.encode (α := (CompParams × ℕ) × (ℕ × ℕ))) (WordEncoding.encode (α := Unit))
      CopyCompItemPre (fun _ _ => 0) := by
  have hrq := liftComp1 (δ := (CompParams × ℕ) × (ℕ × ℕ)) realizesBounded_readCompQuotGen
    (fun d => d.2.1) ⟨37, by decide⟩ fun ⟨_, _, _⟩ => rfl
  have hrv := liftComp1 (δ := ((CompParams × ℕ) × (ℕ × ℕ)) × ℕ) realizesBounded_readCompValGen
    (fun d => d.1.2.1) ⟨37, by decide⟩ fun ⟨⟨_, _, _⟩, _⟩ => rfl
  have hwq := liftComp2 (δ := (((CompParams × ℕ) × (ℕ × ℕ)) × ℕ) × ℕ)
    realizesBounded_writeCompQuotGen (fun d => d.1.1.2.2) (fun d => d.1.2)
    ⟨38, by decide⟩ ⟨39, by decide⟩ (fun ⟨⟨⟨_, _, _⟩, _⟩, _⟩ => rfl)
    fun ⟨⟨⟨_, _, _⟩, _⟩, _⟩ => rfl
  have hwv := liftComp2 (δ := ((((CompParams × ℕ) × (ℕ × ℕ)) × ℕ) × ℕ) × Unit)
    realizesBounded_writeCompValGen (fun d => d.1.1.1.2.2) (fun d => d.1.2)
    ⟨38, by decide⟩ ⟨40, by decide⟩ (fun ⟨⟨⟨⟨_, _, _⟩, _⟩, _⟩, _⟩ => rfl)
    fun ⟨⟨⟨⟨_, _, _⟩, _⟩, _⟩, _⟩ => rfl
  refine ((hrq.bind₀ (hrv.bind₀ (hwq.bind₀ hwv))).congr
    fun ⟨⟨_, _⟩, _, _⟩ => rfl).consequence (fun w ⟨⟨_, itemBase⟩, src, dst⟩ s _ _ h => ?_)
    (fun _ _ => le_rfl)
  obtain ⟨m_items, ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, hsrc, hdst⟩ := h
  have henv : CompItemEnv w (mkCompParams U V w N) itemBase m_items s :=
    ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩
  simp only [hasCompEnv_eb_prod, hasCompEnv_eb_base, StateTransitionSpec.clientState,
    runClient_state_readCompQuotGenProg, runClient_state_readCompValGenProg,
    runClient_state_writeCompQuotGenProg]
  exact ⟨⟨m_items, henv, hsrc⟩, ⟨m_items, henv, hsrc⟩, ⟨m_items, henv, hdst⟩,
    by dsimp only [WriteCompValPre, CompItemEnv] at henv ⊢; exact ⟨m_items, henv, hdst⟩⟩

/-- Clear `(quot, val)` to `(0, 0)` at dense index `d` before shrinking trailing words. -/
def clearCompItemGenProg : (CompParams × ℕ) × ℕ → Memory.Prog Unit
  | ((cp, itemBase), d) => do
    let z ← pure 0
    writeCompQuotGenProg (((cp, itemBase), d), z)
    writeCompValGenProg (((cp, itemBase), d), z)

@[simp] theorem clientResult_clearCompItemGenProg
    (d : (CompParams × ℕ) × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (clearCompItemGenProg d) = () := by
  rcases d with ⟨⟨cp, itemBase⟩, idx⟩; simp [clearCompItemGenProg]

theorem clientState_clearCompItemGenProg (U V w N itemBase d : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s
        (clearCompItemGenProg ((mkCompParams U V w N, itemBase), d)) =
      { mem := writeCompVal itemBase U V w N (writeCompQuot itemBase U V w N s.mem d 0) d 0,
        frontier := s.frontier } := by
  unfold StateTransitionSpec.clientState
  simp [clearCompItemGenProg]

@[simp] theorem memoryCost_clearCompItemGenProg
    (d : (CompParams × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (clearCompItemGenProg d) s = 8 := by
  rcases d with ⟨⟨cp, itemBase⟩, idx⟩; simp [clearCompItemGenProg]

private theorem realizesBounded_zeroUnit :
    RealizesBounded .exact (fun _ : Unit => pure 0)
      (WordEncoding.encode (α := Unit)) (WordEncoding.encode (α := ℕ))
      (fun _ _ _ => True) (fun _ _ => 0) := by
  realize

theorem realizesBounded_clearCompItemGen :
    RealizesBounded .exact clearCompItemGenProg
      (WordEncoding.encode (α := (CompParams × ℕ) × ℕ)) (WordEncoding.encode (α := Unit))
      ReadCompQuotPre (fun _ _ => 0) := by
  have h0 := realizesBounded_zeroUnit.reindex (fun _ : (CompParams × ℕ) × ℕ => ())
    (WordEncoding.encode (α := (CompParams × ℕ) × ℕ)) Fin.elim0 fun _ i => Fin.elim0 i
  have hwv := liftComp2 (δ := (((CompParams × ℕ) × ℕ) × ℕ) × Unit) realizesBounded_writeCompValGen
    (fun d => d.1.1.2) (fun d => d.1.2) ⟨37, by decide⟩ ⟨38, by decide⟩
    (fun ⟨⟨⟨_, _⟩, _⟩, _⟩ => rfl) fun ⟨⟨⟨_, _⟩, _⟩, _⟩ => rfl
  refine ((h0.bind₀ (realizesBounded_writeCompQuotGen.bind₀ hwv)).congr
    fun ⟨⟨_, _⟩, _⟩ => rfl).consequence (fun w ⟨⟨_, itemBase⟩, idx⟩ s _ _ h => ?_)
    (fun _ _ => le_rfl)
  obtain ⟨m_items, ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, hidx⟩ := h
  refine ⟨trivial, ⟨m_items, ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, hidx⟩, ?_⟩
  change WriteCompValPre w _ ((Memory.spec 0).clientState s (writeCompQuotGenProg (_, 0)))
  rw [clientState_writeCompQuotGenProg]
  exact ⟨m_items, ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, hidx⟩

private theorem realizesBounded_readCompPacked (offIdx kIdx : Fin 36) :
    RealizesBounded .exact
      (fun ((cp, metaBase), idx) =>
        readPackedCompGenProg (((metaBase, cp offIdx), (cp kIdx, cpW cp)), idx))
      (WordEncoding.encode (α := (CompParams × ℕ) × ℕ)) (WordEncoding.encode (α := ℕ))
      (fun w ((cp, metaBase), idx) s =>
        ReadPackedCompPre w (((metaBase, cp offIdx), (cp kIdx, cpW cp)), idx) s)
      (fun _ _ => 0) :=
  realizesBounded_readPackedCompGen.reindex _ _
    ![⟨36, by decide⟩, Fin.castAdd 1 (Fin.castAdd 1 offIdx),
      Fin.castAdd 1 (Fin.castAdd 1 kIdx), ⟨0, by decide⟩, ⟨37, by decide⟩]
    fun ⟨⟨cp, metaBase⟩, idx⟩ i => by
      fin_cases i
      all_goals first
        | rfl
        | exact ((encode_fst (cp, metaBase) idx _).trans (encode_fst cp metaBase _)).symm

private theorem realizesBounded_writeCompPacked (offIdx kIdx : Fin 36) :
    RealizesBounded .exact
      (fun (((cp, metaBase), idx), val) =>
        writePackedCompGenProg ((((metaBase, cp offIdx), (cp kIdx, cpW cp)), idx), val))
      (WordEncoding.encode (α := ((CompParams × ℕ) × ℕ) × ℕ)) (WordEncoding.encode (α := Unit))
      (fun w (((cp, metaBase), idx), val) s =>
        WritePackedCompPre w ((((metaBase, cp offIdx), (cp kIdx, cpW cp)), idx), val) s)
      (fun _ _ => 0) :=
  realizesBounded_writePackedCompGen.reindex _ _
    ![⟨36, by decide⟩, Fin.castAdd 1 (Fin.castAdd 1 (Fin.castAdd 1 offIdx)),
      Fin.castAdd 1 (Fin.castAdd 1 (Fin.castAdd 1 kIdx)),
      ⟨0, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩]
    fun ⟨⟨⟨cp, metaBase⟩, idx⟩, val⟩ i => by
      fin_cases i
      all_goals first
        | rfl
        | exact (((encode_fst ((cp, metaBase), idx) val _).trans
            (encode_fst (cp, metaBase) idx _)).trans (encode_fst cp metaBase _)).symm

/-- Read `LocalMeta[c, idx]` at `metaBase` in `Memory.Prog`. -/
def readCompLMGenProg (c : Fin 9) : (CompParams × ℕ) × ℕ → Memory.Prog ℕ
  | ((cp, metaBase), idx) => do
    let off ← pure (cpOffLMSub c cp)
    let k ← pure (cpLmBits cp)
    let wVal ← pure (cpW cp)
    readPackedCompGenProg (((metaBase, off), (k, wVal)), idx)

@[simp] theorem clientResult_readCompLMGenProg (c : Fin 9) {U V w N metaBase idx : ℕ}
    (hidx : idx < totalMicroBuckets N) (s : Memory.State) :
    (Memory.spec 0).clientResult s
        (readCompLMGenProg c ((mkCompParams U V w N, metaBase), idx)) =
      compLmAt metaBase U w N s.mem (c.val, idx) := by
  simp [readCompLMGenProg, cpOffLMSub_mk, compLmAt, c.isLt, hidx]

theorem clientState_readCompLMGenProg (c : Fin 9) (d : (CompParams × ℕ) × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (readCompLMGenProg c d) = s := by
  rcases d with ⟨⟨cp, metaBase⟩, idx⟩; unfold StateTransitionSpec.clientState
  simp [readCompLMGenProg]
@[simp] theorem runClient_state_readCompLMGenProg
    (c : Fin 9) (d : (CompParams × ℕ) × ℕ) (s : Memory.State) :
    Prod.fst (Prod.snd ((Memory.spec 0).runClient s (readCompLMGenProg c d))) = s :=
  clientState_readCompLMGenProg c d s
@[simp] theorem memoryCost_readCompLMGenProg
    (c : Fin 9) (d : (CompParams × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (readCompLMGenProg c d) s = 2 := by
  rcases d with ⟨⟨cp, metaBase⟩, idx⟩; simp [readCompLMGenProg]

/-- Precondition for reading from local metadata array `LM`. -/
@[expose] def CompLMPre (w : ℕ) : (CompParams × ℕ) × ℕ → Memory.State → Prop
  | ((cp, metaBase), idx), s => CompMetaEnv w cp metaBase s ∧ idx < totalMicroBuckets (cpN cp)

private theorem readPackedCompPre_lm (c : Fin 9) {w metaBase idx : ℕ} {cp : CompParams}
    {s : Memory.State} (h : CompMetaEnv w cp metaBase s ∧ idx < totalMicroBuckets (cpN cp)) :
    ReadPackedCompPre w (((metaBase, cp ⟨5 + c.val, by omega⟩), (cp 14, cpW cp)), idx) s := by
  obtain ⟨⟨U, V, N, hw, _, hnU, hU, _, rfl, hfr⟩, hidx⟩ := h
  have hidx' : idx < totalMicroBuckets N := hidx
  have hsub : mkCompParams U V w N ⟨5 + c.val, by omega⟩ = offCompLMSub U w N c.val := by
    fin_cases c <;> rfl
  change ReadPackedCompPre w
    (((metaBase, mkCompParams U V w N ⟨5 + c.val, by omega⟩), (effBucketPosBits N, w)), idx) s
  rw [hsub]
  refine ⟨totalMicroBuckets N, hw, rfl, effBucketPosBits_le_of_lt_pow hnU hU, hidx', ?_⟩
  have hle := Nat.mul_le_mul_right (lmSubWords N w) c.isLt
  rw [Nat.add_one_mul] at hle
  unfold offCompItems offDenseToTail offTailToDense offCompGM offCompLMSub offCompLM at *
  change _ + lmSubWords N w ≤ s.frontier
  omega

theorem realizesBounded_readCompLMGen (c : Fin 9) :
    RealizesBounded .exact (readCompLMGenProg c)
      (WordEncoding.encode (α := (CompParams × ℕ) × ℕ)) (WordEncoding.encode (α := ℕ))
      CompLMPre (fun _ _ => 0) :=
  ((realizesBounded_readCompPacked ⟨5 + c.val, by omega⟩ 14).congr
    fun ⟨⟨_, _⟩, _⟩ => by fin_cases c <;> rfl).consequence
    (fun _ ⟨⟨_, _⟩, _⟩ _ _ _ h => readPackedCompPre_lm c h) (fun _ _ => le_rfl)

/-- Write `val` into `LocalMeta[c, idx]` at `metaBase` in `Memory.Prog`. -/
def writeCompLMGenProg (c : Fin 9) : ((CompParams × ℕ) × ℕ) × ℕ → Memory.Prog Unit
  | (((cp, metaBase), idx), val) => do
    let off ← pure (cpOffLMSub c cp)
    let k ← pure (cpLmBits cp)
    let wVal ← pure (cpW cp)
    writePackedCompGenProg ((((metaBase, off), (k, wVal)), idx), val)

@[simp] theorem clientResult_writeCompLMGenProg
    (c : Fin 9) (d : ((CompParams × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (writeCompLMGenProg c d) = () := by
  rcases d with ⟨⟨⟨cp, metaBase⟩, idx⟩, val⟩; simp [writeCompLMGenProg]
theorem clientState_writeCompLMGenProg
    (c : Fin 9) (U V w N metaBase idx val : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s
        (writeCompLMGenProg c (((mkCompParams U V w N, metaBase), idx), val)) =
      { mem := writePacked (metaBase + offCompLMSub U w N c.val)
          (effBucketPosBits N) w s.mem idx val,
        frontier := s.frontier } := by
  unfold StateTransitionSpec.clientState; simp [writeCompLMGenProg, cpOffLMSub_mk]
@[simp] theorem runClient_state_writeCompLMGenProg
    (c : Fin 9) (U V w N metaBase idx val : ℕ) (s : Memory.State) :
    Prod.fst (Prod.snd ((Memory.spec 0).runClient s
        (writeCompLMGenProg c (((mkCompParams U V w N, metaBase), idx), val)))) =
      { mem := writePacked (metaBase + offCompLMSub U w N c.val)
          (effBucketPosBits N) w s.mem idx val,
        frontier := s.frontier } :=
  clientState_writeCompLMGenProg c U V w N metaBase idx val s
@[simp] theorem memoryCost_writeCompLMGenProg
    (c : Fin 9) (d : ((CompParams × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (writeCompLMGenProg c d) s = 4 := by
  rcases d with ⟨⟨⟨cp, metaBase⟩, idx⟩, val⟩; simp [writeCompLMGenProg]

/-- Precondition for writing to local metadata array `LM`. -/
@[expose] def WriteCompLMPre (w : ℕ) : ((CompParams × ℕ) × ℕ) × ℕ → Memory.State → Prop
  | (((cp, metaBase), idx), _val), s =>
    CompMetaEnv w cp metaBase s ∧ idx < totalMicroBuckets (cpN cp)

theorem realizesBounded_writeCompLMGen (c : Fin 9) :
    RealizesBounded .exact (writeCompLMGenProg c)
      (WordEncoding.encode (α := ((CompParams × ℕ) × ℕ) × ℕ)) (WordEncoding.encode (α := Unit))
      WriteCompLMPre (fun _ _ => 0) :=
  ((realizesBounded_writeCompPacked ⟨5 + c.val, by omega⟩ 14).congr
    fun ⟨⟨⟨_, _⟩, _⟩, _⟩ => by fin_cases c <;> rfl).consequence
    (fun _ ⟨⟨⟨_, _⟩, _⟩, _⟩ _ _ _ h => readPackedCompPre_lm c h) (fun _ _ => le_rfl)

/-- Read `GlobalMeta[idx]` at `metaBase` in `Memory.Prog`. -/
def readCompGMGenProg : (CompParams × ℕ) × ℕ → Memory.Prog ℕ
  | ((cp, metaBase), idx) => do
    let off ← pure (cpOffGM cp)
    let k ← pure (cpGmBits cp)
    let wVal ← pure (cpW cp)
    readPackedCompGenProg (((metaBase, off), (k, wVal)), idx)

@[simp] theorem clientResult_readCompGMGenProg {U V w N metaBase idx : ℕ}
    (hidx : idx < globalMetaLen N) (s : Memory.State) :
    (Memory.spec 0).clientResult s
        (readCompGMGenProg ((mkCompParams U V w N, metaBase), idx)) =
      compGmAt metaBase U w N s.mem idx := by
  simp [readCompGMGenProg, compGmAt, hidx]

theorem clientState_readCompGMGenProg (d : (CompParams × ℕ) × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (readCompGMGenProg d) = s := by
  rcases d with ⟨⟨cp, metaBase⟩, idx⟩; unfold StateTransitionSpec.clientState
  simp [readCompGMGenProg]
@[simp] theorem runClient_state_readCompGMGenProg (d : (CompParams × ℕ) × ℕ) (s : Memory.State) :
    Prod.fst (Prod.snd ((Memory.spec 0).runClient s (readCompGMGenProg d))) = s :=
  clientState_readCompGMGenProg d s
@[simp] theorem memoryCost_readCompGMGenProg (d : (CompParams × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (readCompGMGenProg d) s = 2 := by
  rcases d with ⟨⟨cp, metaBase⟩, idx⟩; simp [readCompGMGenProg]

/-- Precondition for reading from global metadata array `GM`. -/
@[expose] def CompGMPre (w : ℕ) : (CompParams × ℕ) × ℕ → Memory.State → Prop
  | ((cp, metaBase), idx), s => CompMetaEnv w cp metaBase s ∧ idx < globalMetaLen (cpN cp)

private theorem readPackedCompPre_gm {w metaBase idx : ℕ} {cp : CompParams} {s : Memory.State}
    (h : CompMetaEnv w cp metaBase s ∧ idx < globalMetaLen (cpN cp)) :
    ReadPackedCompPre w (((metaBase, cp 15), (cp 16, cpW cp)), idx) s := by
  obtain ⟨⟨U, V, N, hw, _, hnU, hU, _, rfl, hfr⟩, hidx⟩ := h
  exact ⟨globalMetaLen N, hw, rfl, globalPtrBits_le_of_lt_pow hnU hU, hidx, by
    change _ + offCompGM _ _ N + packedWords (globalMetaLen N) (globalPtrBits N) w ≤ _
    wram_omega⟩

theorem realizesBounded_readCompGMGen :
    RealizesBounded .exact readCompGMGenProg
      (WordEncoding.encode (α := (CompParams × ℕ) × ℕ)) (WordEncoding.encode (α := ℕ))
      CompGMPre (fun _ _ => 0) :=
  ((realizesBounded_readCompPacked 15 16).congr fun ⟨⟨_, _⟩, _⟩ => rfl).consequence
    (fun _ ⟨⟨_, _⟩, _⟩ _ _ _ h => readPackedCompPre_gm h) (fun _ _ => le_rfl)

/-- Write `val` into `GlobalMeta[idx]` at `metaBase` in `Memory.Prog`. -/
def writeCompGMGenProg : ((CompParams × ℕ) × ℕ) × ℕ → Memory.Prog Unit
  | (((cp, metaBase), idx), val) => do
    let off ← pure (cpOffGM cp)
    let k ← pure (cpGmBits cp)
    let wVal ← pure (cpW cp)
    writePackedCompGenProg ((((metaBase, off), (k, wVal)), idx), val)

@[simp] theorem clientResult_writeCompGMGenProg
    (d : ((CompParams × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (writeCompGMGenProg d) = () := by
  rcases d with ⟨⟨⟨cp, metaBase⟩, idx⟩, val⟩; simp [writeCompGMGenProg]
theorem clientState_writeCompGMGenProg (U V w N metaBase idx val : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s
        (writeCompGMGenProg (((mkCompParams U V w N, metaBase), idx), val)) =
      { mem := writePacked (metaBase + offCompGM U w N) (globalPtrBits N) w s.mem idx val,
        frontier := s.frontier } := by
  unfold StateTransitionSpec.clientState; simp [writeCompGMGenProg]
@[simp] theorem runClient_state_writeCompGMGenProg
    (U V w N metaBase idx val : ℕ) (s : Memory.State) :
    Prod.fst (Prod.snd ((Memory.spec 0).runClient s
        (writeCompGMGenProg (((mkCompParams U V w N, metaBase), idx), val)))) =
      { mem := writePacked (metaBase + offCompGM U w N) (globalPtrBits N) w s.mem idx val,
        frontier := s.frontier } :=
  clientState_writeCompGMGenProg U V w N metaBase idx val s
@[simp] theorem memoryCost_writeCompGMGenProg
    (d : ((CompParams × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (writeCompGMGenProg d) s = 4 := by
  rcases d with ⟨⟨⟨cp, metaBase⟩, idx⟩, val⟩; simp [writeCompGMGenProg]

/-- Precondition for writing to global metadata array `GM`. -/
@[expose] def WriteCompGMPre (w : ℕ) : ((CompParams × ℕ) × ℕ) × ℕ → Memory.State → Prop
  | (((cp, metaBase), idx), _val), s =>
    CompMetaEnv w cp metaBase s ∧ idx < globalMetaLen (cpN cp)

theorem realizesBounded_writeCompGMGen :
    RealizesBounded .exact writeCompGMGenProg
      (WordEncoding.encode (α := ((CompParams × ℕ) × ℕ) × ℕ)) (WordEncoding.encode (α := Unit))
      WriteCompGMPre (fun _ _ => 0) :=
  ((realizesBounded_writeCompPacked 15 16).congr fun ⟨⟨⟨_, _⟩, _⟩, _⟩ => rfl).consequence
    (fun _ ⟨⟨⟨_, _⟩, _⟩, _⟩ _ _ _ h => readPackedCompPre_gm h) (fun _ _ => le_rfl)

/-- Read `TailToDense[t]` at `metaBase` in `Memory.Prog`. -/
def readCompTDGenProg : (CompParams × ℕ) × ℕ → Memory.Prog ℕ
  | ((cp, metaBase), t) => do
    let off ← pure (cpOffTD cp)
    let k ← pure (cpGmBits cp)
    let wVal ← pure (cpW cp)
    readPackedCompGenProg (((metaBase, off), (k, wVal)), t)

@[simp] theorem clientResult_readCompTDGenProg {U V w N metaBase t : ℕ}
    (ht : t < maxTailItems N) (s : Memory.State) :
    (Memory.spec 0).clientResult s
        (readCompTDGenProg ((mkCompParams U V w N, metaBase), t)) =
      compTDAt metaBase U w N s.mem t := by
  simp [readCompTDGenProg, compTDAt, ht]

theorem clientState_readCompTDGenProg (d : (CompParams × ℕ) × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (readCompTDGenProg d) = s := by
  rcases d with ⟨⟨cp, metaBase⟩, t⟩; unfold StateTransitionSpec.clientState
  simp [readCompTDGenProg]
@[simp] theorem runClient_state_readCompTDGenProg (d : (CompParams × ℕ) × ℕ) (s : Memory.State) :
    Prod.fst (Prod.snd ((Memory.spec 0).runClient s (readCompTDGenProg d))) = s :=
  clientState_readCompTDGenProg d s
@[simp] theorem memoryCost_readCompTDGenProg (d : (CompParams × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (readCompTDGenProg d) s = 2 := by
  rcases d with ⟨⟨cp, metaBase⟩, t⟩; simp [readCompTDGenProg]

/-- Precondition for reading from tail map `TailToDense`. -/
@[expose] def CompTailMapPre (w : ℕ) : (CompParams × ℕ) × ℕ → Memory.State → Prop
  | ((cp, metaBase), idx), s => CompMetaEnv w cp metaBase s ∧ idx < cpMaxTail cp

private theorem readPackedCompPre_tail (isDT : Bool) {w metaBase idx : ℕ} {cp : CompParams}
    {s : Memory.State} (h : CompMetaEnv w cp metaBase s ∧ idx < cpMaxTail cp) :
    ReadPackedCompPre w (((metaBase, cp (isDT.casesOn 17 18)), (cp 16, cpW cp)), idx) s := by
  obtain ⟨⟨U, V, N, hw, _, hnU, hU, _, rfl, hfr⟩, hidx⟩ := h
  cases isDT
  · exact ⟨maxTailItems N, hw, rfl, globalPtrBits_le_of_lt_pow hnU hU, hidx, by
      change metaBase + offTailToDense U w N + packedWords (maxTailItems N) (globalPtrBits N) w ≤ _
      wram_omega⟩
  · exact ⟨maxTailItems N, hw, rfl, globalPtrBits_le_of_lt_pow hnU hU, hidx, by
      change metaBase + offDenseToTail U w N + packedWords (maxTailItems N) (globalPtrBits N) w ≤ _
      wram_omega⟩

theorem realizesBounded_readCompTDGen :
    RealizesBounded .exact readCompTDGenProg
      (WordEncoding.encode (α := (CompParams × ℕ) × ℕ)) (WordEncoding.encode (α := ℕ))
      CompTailMapPre (fun _ _ => 0) :=
  ((realizesBounded_readCompPacked 17 16).congr fun ⟨⟨_, _⟩, _⟩ => rfl).consequence
    (fun _ ⟨⟨_, _⟩, _⟩ _ _ _ h => readPackedCompPre_tail false h) (fun _ _ => le_rfl)

/-- Write `val` into `TailToDense[t]` at `metaBase` in `Memory.Prog`. -/
def writeCompTDGenProg : ((CompParams × ℕ) × ℕ) × ℕ → Memory.Prog Unit
  | (((cp, metaBase), t), val) => do
    let off ← pure (cpOffTD cp)
    let k ← pure (cpGmBits cp)
    let wVal ← pure (cpW cp)
    writePackedCompGenProg ((((metaBase, off), (k, wVal)), t), val)

@[simp] theorem clientResult_writeCompTDGenProg
    (d : ((CompParams × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (writeCompTDGenProg d) = () := by
  rcases d with ⟨⟨⟨cp, metaBase⟩, t⟩, val⟩; simp [writeCompTDGenProg]
theorem clientState_writeCompTDGenProg (U V w N metaBase t val : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s
        (writeCompTDGenProg (((mkCompParams U V w N, metaBase), t), val)) =
      { mem := writePacked (metaBase + offTailToDense U w N) (globalPtrBits N) w s.mem t val,
        frontier := s.frontier } := by
  unfold StateTransitionSpec.clientState; simp [writeCompTDGenProg]
@[simp] theorem runClient_state_writeCompTDGenProg
    (U V w N metaBase t val : ℕ) (s : Memory.State) :
    Prod.fst (Prod.snd ((Memory.spec 0).runClient s
        (writeCompTDGenProg (((mkCompParams U V w N, metaBase), t), val)))) =
      { mem := writePacked (metaBase + offTailToDense U w N) (globalPtrBits N) w s.mem t val,
        frontier := s.frontier } :=
  clientState_writeCompTDGenProg U V w N metaBase t val s
@[simp] theorem memoryCost_writeCompTDGenProg
    (d : ((CompParams × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (writeCompTDGenProg d) s = 4 := by
  rcases d with ⟨⟨⟨cp, metaBase⟩, t⟩, val⟩; simp [writeCompTDGenProg]

/-- Precondition for writing to tail map `TailToDense`. -/
@[expose] def WriteCompTailMapPre (w : ℕ) : ((CompParams × ℕ) × ℕ) × ℕ → Memory.State → Prop
  | (((cp, metaBase), idx), _val), s => CompMetaEnv w cp metaBase s ∧ idx < cpMaxTail cp

theorem realizesBounded_writeCompTDGen :
    RealizesBounded .exact writeCompTDGenProg
      (WordEncoding.encode (α := ((CompParams × ℕ) × ℕ) × ℕ)) (WordEncoding.encode (α := Unit))
      WriteCompTailMapPre (fun _ _ => 0) :=
  ((realizesBounded_writeCompPacked 17 16).congr fun ⟨⟨⟨_, _⟩, _⟩, _⟩ => rfl).consequence
    (fun _ ⟨⟨⟨_, _⟩, _⟩, _⟩ _ _ _ h => readPackedCompPre_tail false h) (fun _ _ => le_rfl)

/-- Read `DenseToTail[r]` at `metaBase` in `Memory.Prog`. -/
def readCompDTGenProg : (CompParams × ℕ) × ℕ → Memory.Prog ℕ
  | ((cp, metaBase), r) => do
    let off ← pure (cpOffDT cp)
    let k ← pure (cpGmBits cp)
    let wVal ← pure (cpW cp)
    readPackedCompGenProg (((metaBase, off), (k, wVal)), r)

@[simp] theorem clientResult_readCompDTGenProg {U V w N metaBase r : ℕ}
    (hr : r < maxTailItems N) (s : Memory.State) :
    (Memory.spec 0).clientResult s
        (readCompDTGenProg ((mkCompParams U V w N, metaBase), r)) =
      compDTAt metaBase U w N s.mem r := by
  simp [readCompDTGenProg, compDTAt, hr]

theorem clientState_readCompDTGenProg (d : (CompParams × ℕ) × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (readCompDTGenProg d) = s := by
  rcases d with ⟨⟨cp, metaBase⟩, r⟩; unfold StateTransitionSpec.clientState
  simp [readCompDTGenProg]
@[simp] theorem runClient_state_readCompDTGenProg (d : (CompParams × ℕ) × ℕ) (s : Memory.State) :
    Prod.fst (Prod.snd ((Memory.spec 0).runClient s (readCompDTGenProg d))) = s :=
  clientState_readCompDTGenProg d s
@[simp] theorem memoryCost_readCompDTGenProg (d : (CompParams × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (readCompDTGenProg d) s = 2 := by
  rcases d with ⟨⟨cp, metaBase⟩, r⟩; simp [readCompDTGenProg]

theorem realizesBounded_readCompDTGen :
    RealizesBounded .exact readCompDTGenProg
      (WordEncoding.encode (α := (CompParams × ℕ) × ℕ)) (WordEncoding.encode (α := ℕ))
      CompTailMapPre (fun _ _ => 0) :=
  ((realizesBounded_readCompPacked 18 16).congr fun ⟨⟨_, _⟩, _⟩ => rfl).consequence
    (fun _ ⟨⟨_, _⟩, _⟩ _ _ _ h => readPackedCompPre_tail true h) (fun _ _ => le_rfl)

/-- Write `val` into `DenseToTail[r]` at `metaBase` in `Memory.Prog`. -/
def writeCompDTGenProg : ((CompParams × ℕ) × ℕ) × ℕ → Memory.Prog Unit
  | (((cp, metaBase), r), val) => do
    let off ← pure (cpOffDT cp)
    let k ← pure (cpGmBits cp)
    let wVal ← pure (cpW cp)
    writePackedCompGenProg ((((metaBase, off), (k, wVal)), r), val)

@[simp] theorem clientResult_writeCompDTGenProg
    (d : ((CompParams × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (writeCompDTGenProg d) = () := by
  rcases d with ⟨⟨⟨cp, metaBase⟩, r⟩, val⟩; simp [writeCompDTGenProg]
theorem clientState_writeCompDTGenProg (U V w N metaBase r val : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s
        (writeCompDTGenProg (((mkCompParams U V w N, metaBase), r), val)) =
      { mem := writePacked (metaBase + offDenseToTail U w N) (globalPtrBits N) w s.mem r val,
        frontier := s.frontier } := by
  unfold StateTransitionSpec.clientState; simp [writeCompDTGenProg]
@[simp] theorem runClient_state_writeCompDTGenProg
    (U V w N metaBase r val : ℕ) (s : Memory.State) :
    Prod.fst (Prod.snd ((Memory.spec 0).runClient s
        (writeCompDTGenProg (((mkCompParams U V w N, metaBase), r), val)))) =
      { mem := writePacked (metaBase + offDenseToTail U w N) (globalPtrBits N) w s.mem r val,
        frontier := s.frontier } :=
  clientState_writeCompDTGenProg U V w N metaBase r val s
@[simp] theorem memoryCost_writeCompDTGenProg
    (d : ((CompParams × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (writeCompDTGenProg d) s = 4 := by
  rcases d with ⟨⟨⟨cp, metaBase⟩, r⟩, val⟩; simp [writeCompDTGenProg]

theorem realizesBounded_writeCompDTGen :
    RealizesBounded .exact writeCompDTGenProg
      (WordEncoding.encode (α := ((CompParams × ℕ) × ℕ) × ℕ)) (WordEncoding.encode (α := Unit))
      WriteCompTailMapPre (fun _ _ => 0) :=
  ((realizesBounded_writeCompPacked 18 16).congr fun ⟨⟨⟨_, _⟩, _⟩, _⟩ => rfl).consequence
    (fun _ ⟨⟨⟨_, _⟩, _⟩, _⟩ _ _ _ h => readPackedCompPre_tail true h) (fun _ _ => le_rfl)

/-! ## Section 2: Circular-Window Transitions, Owner-Bucket Recovery, and `fits_mkCompParams` -/

theorem maxTailItems_le_of_pos {N : ℕ} (hM : 0 < maxTailItems N) : maxTailItems N ≤ N := by
  have hb_pos : 0 < bucketBits N := by
    rcases Nat.eq_zero_or_pos (bucketBits N) with hb0 | hb
    · simp [maxTailItems, tailCapPerBucket, hb0] at hM
    · exact hb
  have h1 := gmSlabMetaBase_add_eq_globalMetaLen hb_pos
  have h2 := globalMetaLen_le_of_bucketBits_pos hb_pos
  wram_omega [h1]

/-- Overflow-free evaluation of `denseOfCirc (cpMaxTail cp) b_win c` in `Memory.Prog`. -/
def denseOfCircGenProg : CompParams × (ℕ × ℕ) → Memory.Prog ℕ
  | (cp, (b_win, c)) => do
    let z ← pure 0
    if cpMaxTail cp = z then pure b_win
    else do
      let M ← pure (cpMaxTail cp)
      let rem ← pure (b_win % M)
      if c < rem then
        pure (b_win + (c + (M - rem)))
      else
        pure (b_win + (c - rem))

theorem clientResult_denseOfCircGenProg {U V w N b_win c : ℕ}
    (hc : 0 < maxTailItems N → c < maxTailItems N) (s : Memory.State) :
    (Memory.spec 0).clientResult s
        (denseOfCircGenProg (mkCompParams U V w N, (b_win, c))) =
      denseOfCirc (maxTailItems N) b_win c := by
  dsimp only [denseOfCircGenProg, denseOfCirc]
  simp only [pure_bind, cpMaxTail_mk]
  by_cases hM0 : maxTailItems N = 0
  · rw [ite_eq_left hM0, ite_eq_left hM0]; rfl
  · rw [ite_eq_right hM0, ite_eq_right hM0]
    have hM_pos : 0 < maxTailItems N := Nat.pos_of_ne_zero hM0
    have hc_lt : c < maxTailItems N := hc hM_pos
    have hrem_lt : b_win % maxTailItems N < maxTailItems N := Nat.mod_lt _ hM_pos
    by_cases hlt : c < b_win % maxTailItems N
    · rw [ite_eq_left hlt, prog_clientResult_pure]
      have heq : c + maxTailItems N - b_win % maxTailItems N =
          c + (maxTailItems N - b_win % maxTailItems N) := by omega
      rw [heq, Nat.mod_eq_of_lt (a := c + (maxTailItems N - b_win % maxTailItems N)) (by omega)]
    · rw [ite_eq_right hlt, prog_clientResult_pure]
      have heq : c + maxTailItems N - b_win % maxTailItems N =
          (c - b_win % maxTailItems N) + 1 * maxTailItems N := by omega
      rw [heq, Nat.add_mul_mod_self_right,
        Nat.mod_eq_of_lt (a := c - b_win % maxTailItems N) (by omega)]

theorem clientState_denseOfCircGenProg (d : CompParams × (ℕ × ℕ)) (s : Memory.State) :
    (Memory.spec 0).clientState s (denseOfCircGenProg d) = s := by
  rcases d with ⟨cp, ⟨b_win, c⟩⟩
  unfold StateTransitionSpec.clientState; dsimp only [denseOfCircGenProg]
  simp only [pure_bind]; split_ifs <;> rfl

@[simp] theorem runClient_state_denseOfCircGenProg
    (d : CompParams × (ℕ × ℕ)) (s : Memory.State) :
    Prod.fst (Prod.snd ((Memory.spec 0).runClient s (denseOfCircGenProg d))) = s :=
  clientState_denseOfCircGenProg d s

@[simp] theorem memoryCost_denseOfCircGenProg (d : CompParams × (ℕ × ℕ)) (s : Memory.State) :
    memoryCost (denseOfCircGenProg d) s = 0 := by
  rcases d with ⟨cp, ⟨b_win, c⟩⟩
  dsimp only [denseOfCircGenProg]; simp only [pure_bind]; split_ifs <;> rfl

/-- Precondition for circular tail offset mapping `denseOfCirc`. -/
@[expose] def DenseOfCircPre (w : ℕ) : CompParams × (ℕ × ℕ) → Memory.State → Prop
  | (cp, (b_win, c)), _s =>
    ∃ U V N,
      0 < w ∧ 0 < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧ b_win ≤ N ∧
      (0 < maxTailItems N →
        c < maxTailItems N ∧ denseOfCirc (maxTailItems N) b_win c ≤ N)

private def denseOfCircCoreProg : ℕ × (ℕ × ℕ) → Memory.Prog ℕ
  | (M, (b_win, c)) => do
    let z ← pure 0
    if M = z then pure b_win
    else do
      let rem ← pure (b_win % M)
      if c < rem then
        pure (b_win + (c + (M - rem)))
      else
        pure (b_win + (c - rem))

private def DenseOfCircCorePre (w : ℕ) : ℕ × (ℕ × ℕ) → Memory.State → Prop
  | (M, (b_win, c)), _s =>
    0 < M → c < M ∧ denseOfCirc M b_win c < 2 ^ w

private theorem realizesBounded_denseOfCircCore :
    RealizesBounded .exact denseOfCircCoreProg
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ))) (WordEncoding.encode (α := ℕ))
      DenseOfCircCorePre (fun _ _ => 0) := by
  realize
  all_goals (
    rcases d with ⟨M, ⟨b_win, c⟩⟩
    dsimp only [Fits] at *
    have hM_pos : 0 < M := by omega
    obtain ⟨hc_lt, hd_lt⟩ := h hM_pos
    have hrem_lt : b_win % M < M := Nat.mod_lt _ hM_pos
    unfold denseOfCirc at hd_lt
    rw [ite_eq_right hM_pos.ne'] at hd_lt)
  all_goals try omega
  · have heq : c + M - b_win % M = c + (M - b_win % M) := by omega
    rw [heq, Nat.mod_eq_of_lt (by omega)] at hd_lt
    omega
  · have heq : c + M - b_win % M = (c - b_win % M) + 1 * M := by omega
    rw [heq, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)] at hd_lt
    omega

theorem realizesBounded_denseOfCircGen :
    RealizesBounded .exact denseOfCircGenProg
      (WordEncoding.encode (α := CompParams × (ℕ × ℕ))) (WordEncoding.encode (α := ℕ))
      DenseOfCircPre (fun _ _ => 0) := by
  refine ((realizesBounded_denseOfCircCore.reindex
    (fun (cp, bc) => (cpMaxTail cp, bc))
    (WordEncoding.encode (α := CompParams × (ℕ × ℕ))) ![19, 36, 37]
    fun ⟨_, _, _⟩ i => by fin_cases i <;> rfl).congr fun ⟨_, _, _⟩ => rfl).consequence
    (fun _ ⟨_, _, _⟩ _ _ _ h hM => ?_) (fun _ _ => le_rfl)
  obtain ⟨_, _, _, _, _, hnU, hU, _, rfl, _, hM_cond⟩ := h
  obtain ⟨hc, hd⟩ := hM_cond hM
  exact ⟨hc, lt_of_le_of_lt (hd.trans hnU) hU⟩

/-- Map physical slot `g < N` to dense index `denseOfPhys N gm td g` in `Memory.Prog`. -/
def denseOfPhysGenProg : (CompParams × ℕ) × ℕ → Memory.Prog ℕ
  | ((cp, metaBase), g) => do
    let z ← pure 0
    if cpBucketBits cp = z then pure g
    else do
      let n_slabs ← readCompGMGenProg ((cp, metaBase), z)
      let b_tail ← pure (n_slabs * cpSlabSize cp)
      if g < b_tail then pure g
      else do
        let t ← pure (cpNSubOne cp - g)
        let c ← readCompTDGenProg ((cp, metaBase), t)
        denseOfCircGenProg (cp, (b_tail, c))

theorem clientResult_denseOfPhysGenProg {U V w N metaBase g : ℕ} {s : Memory.State}
    (ht_lt : 0 < bucketBits N → ¬(g < compGmAt metaBase U w N s.mem 0 * slabSize N) →
      N - 1 - g < maxTailItems N ∧
      compTDAt metaBase U w N s.mem (N - 1 - g) < maxTailItems N) :
    (Memory.spec 0).clientResult s
        (denseOfPhysGenProg ((mkCompParams U V w N, metaBase), g)) =
      denseOfPhys N (compGmAt metaBase U w N s.mem) (compTDAt metaBase U w N s.mem) g := by
  dsimp only [denseOfPhysGenProg, denseOfPhys, cpBucketBits_mk, cpSlabSize_mk, cpNSubOne_mk]
  simp only [pure_bind]
  by_cases hb0 : bucketBits N = 0
  · rw [ite_eq_left hb0, ite_eq_left hb0]; rfl
  · rw [ite_eq_right hb0, ite_eq_right hb0]
    have hb_pos : 0 < bucketBits N := Nat.pos_of_ne_zero hb0
    have h0_lt : 0 < globalMetaLen N := by wram_omega
    rw [prog_clientResult_bind, clientResult_readCompGMGenProg h0_lt,
      clientState_readCompGMGenProg]
    by_cases hg_lt : g < compGmAt metaBase U w N s.mem 0 * slabSize N
    · rw [ite_eq_left hg_lt, ite_eq_left hg_lt]; rfl
    · rw [ite_eq_right hg_lt, ite_eq_right hg_lt]
      obtain ⟨ht1, ht2⟩ := ht_lt hb_pos hg_lt
      rw [prog_clientResult_bind, clientResult_readCompTDGenProg ht1,
        clientState_readCompTDGenProg]
      exact clientResult_denseOfCircGenProg (fun _ => ht2) s

theorem clientState_denseOfPhysGenProg (d : (CompParams × ℕ) × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (denseOfPhysGenProg d) = s := by
  rcases d with ⟨⟨cp, metaBase⟩, g⟩
  unfold StateTransitionSpec.clientState; dsimp only [denseOfPhysGenProg]
  simp only [pure_bind]
  by_cases hb0 : cpBucketBits cp = 0
  · rw [ite_eq_left hb0]; rfl
  · rw [ite_eq_right hb0, prog_runClient_state_bind]
    simp only [StateTransitionSpec.clientState, runClient_state_readCompGMGenProg]
    split_ifs <;> simp

@[simp] theorem runClient_state_denseOfPhysGenProg
    (d : (CompParams × ℕ) × ℕ) (s : Memory.State) :
    Prod.fst (Prod.snd ((Memory.spec 0).runClient s (denseOfPhysGenProg d))) = s :=
  clientState_denseOfPhysGenProg d s

/-- Precondition for mapping physical slot index to dense index `denseOfPhys`. -/
@[expose] def DenseOfPhysPre (w : ℕ) : (CompParams × ℕ) × ℕ → Memory.State → Prop
  | ((cp, metaBase), g), s =>
    ∃ U V N,
      0 < w ∧ 0 < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧
      metaBase + offCompItems U w N ≤ s.frontier ∧ g < N ∧
      (0 < bucketBits N →
        compGmAt metaBase U w N s.mem 0 * slabSize N ≤ N ∧
        (¬(g < compGmAt metaBase U w N s.mem 0 * slabSize N) →
          N - 1 - g < maxTailItems N ∧
          compTDAt metaBase U w N s.mem (N - 1 - g) < maxTailItems N ∧
          denseOfCirc (maxTailItems N) (compGmAt metaBase U w N s.mem 0 * slabSize N)
            (compTDAt metaBase U w N s.mem (N - 1 - g)) ≤ N))

private abbrev DenseOfPhysCoreArg :=
  (((ℕ × (ℕ × ℕ)) × (ℕ × ℕ)) × ((ℕ × ℕ) × (ℕ × ℕ))) × ℕ

private def denseOfPhysCoreProg : DenseOfPhysCoreArg → Memory.Prog ℕ
  | ((((metaBase, (offGM, offTD)), (gmBits, wVal)),
      ((bBits, sSize), (nSubOne, maxTail))), g) => do
    let z ← pure 0
    if bBits = z then pure g
    else do
      let n_slabs ← readPackedCompGenProg (((metaBase, offGM), (gmBits, wVal)), z)
      let b_tail ← pure (n_slabs * sSize)
      if g < b_tail then pure g
      else do
        let t ← pure (nSubOne - g)
        let c ← readPackedCompGenProg (((metaBase, offTD), (gmBits, wVal)), t)
        denseOfCircCoreProg (maxTail, (b_tail, c))

private def DenseOfPhysCorePre (w : ℕ) : DenseOfPhysCoreArg → Memory.State → Prop
  | ((((metaBase, (offGM, offTD)), (gmBits, wVal)),
      ((bBits, sSize), (nSubOne, maxTail))), g), s =>
    0 < bBits →
      let b_tail := readPacked (metaBase + offGM) gmBits wVal s.mem 0 * sSize
      ReadPackedCompPre w (((metaBase, offGM), (gmBits, wVal)), 0) s ∧
      b_tail < 2 ^ w ∧
      (¬(g < b_tail) →
        g ≤ nSubOne ∧
        ReadPackedCompPre w (((metaBase, offTD), (gmBits, wVal)), nSubOne - g) s ∧
        DenseOfCircCorePre w
          (maxTail, (b_tail, readPacked (metaBase + offTD) gmBits wVal s.mem (nSubOne - g))) s)

private theorem realizesBounded_denseOfPhysCore :
    RealizesBounded .exact denseOfPhysCoreProg
      (WordEncoding.encode (α := DenseOfPhysCoreArg)) (WordEncoding.encode (α := ℕ))
      DenseOfPhysCorePre (fun _ _ => 0) := by
  have hrp := realizesBounded_readPackedCompGen
  have hdoc := realizesBounded_denseOfCircCore
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨metaBase, ⟨offGM, offTD⟩⟩, ⟨gmBits, wVal⟩⟩,
      ⟨⟨bBits, sSize⟩, ⟨nSubOne, maxTail⟩⟩⟩, g⟩
    obtain ⟨hgm, hbt, htail⟩ := h (Nat.pos_of_ne_zero (by assumption))
    obtain ⟨_, _, hw_eq, _, _, _⟩ := id hgm
    subst hw_eq
    dsimp only [Fits] at *)
  · exact hgm
  all_goals (
    simp only [StateTransitionSpec.clientState, clientResult_readPackedCompGenProg,
      runClient_state_readPackedCompGenProg] at *)
  · exact hbt
  all_goals obtain ⟨hgle, htd, hcirc⟩ := htail (by assumption)
  · exact hgle
  · exact htd
  · dsimp only [DenseOfCircCorePre] at hcirc ⊢
    exact hcirc

theorem realizesBounded_denseOfPhysGen :
    RealizesBounded .exact denseOfPhysGenProg
      (WordEncoding.encode (α := (CompParams × ℕ) × ℕ)) (WordEncoding.encode (α := ℕ))
      DenseOfPhysPre (fun _ _ => 0) := by
  refine ((realizesBounded_denseOfPhysCore.reindex
    (fun ((cp, metaBase), g) =>
      ((((metaBase, (cpOffGM cp, cpOffTD cp)), (cpGmBits cp, cpW cp)),
        ((cpBucketBits cp, cpSlabSize cp), (cpNSubOne cp, cpMaxTail cp))), g))
    (WordEncoding.encode (α := (CompParams × ℕ) × ℕ))
    ![36, 15, 17, 16, 0, 20, 22, 2, 19, 37]
    fun ⟨⟨_, _⟩, _⟩ i => by fin_cases i <;> rfl).congr fun ⟨⟨_, _⟩, _⟩ => rfl).consequence
    (fun w ⟨⟨cp, metaBase⟩, g⟩ s _ _ h => ?_) (fun _ _ => le_rfl)
  obtain ⟨U, V, N, hw, _, hnU, hU, _, rfl, hfr, hg_lt, hb_cond⟩ := h
  intro hb_pos
  have hb_pos' : 0 < bucketBits N := hb_pos
  have h0_lt : 0 < globalMetaLen N := by wram_omega
  have hgptr := globalPtrBits_le_of_lt_pow hnU hU
  obtain ⟨hb_tail_le, htail_cond⟩ := hb_cond hb_pos'
  have hgm_eq : readPacked (metaBase + offCompGM U w N) (globalPtrBits N) w s.mem 0 =
      compGmAt metaBase U w N s.mem 0 := by simp [compGmAt, h0_lt]
  refine ⟨⟨globalMetaLen N, hw, rfl, hgptr, h0_lt, by
    change metaBase + offCompGM U w N + packedWords (globalMetaLen N) (globalPtrBits N) w ≤ _
    wram_omega⟩, ?_, fun hg_ge => ?_⟩
  · change readPacked (metaBase + offCompGM U w N) (globalPtrBits N) w s.mem 0 * slabSize N < 2 ^ w
    rw [hgm_eq]
    exact lt_of_le_of_lt (hb_tail_le.trans hnU) hU
  · change ¬(g < readPacked (metaBase + offCompGM U w N) (globalPtrBits N) w s.mem 0 * slabSize N)
      at hg_ge
    rw [hgm_eq] at hg_ge
    obtain ⟨ht_lt, hc_lt, hd_le⟩ := htail_cond hg_ge
    have htd_eq : readPacked (metaBase + offTailToDense U w N) (globalPtrBits N) w s.mem
        (N - 1 - g) = compTDAt metaBase U w N s.mem (N - 1 - g) := by simp [compTDAt, ht_lt]
    refine ⟨by change g ≤ N - 1; omega,
      ⟨maxTailItems N, hw, rfl, hgptr, ht_lt, by
        change metaBase + offTailToDense U w N +
          packedWords (maxTailItems N) (globalPtrBits N) w ≤ _
        wram_omega⟩, fun _ => ?_⟩
    simp only [cpOffTD_mk, cpGmBits_mk, cpW_mk, cpNSubOne_mk, cpMaxTail_mk,
      cpOffGM_mk, cpSlabSize_mk]
    rw [hgm_eq, htd_eq]
    exact ⟨hc_lt, lt_of_le_of_lt (hd_le.trans hnU) hU⟩

private theorem realizesBounded_winMod (addN : Bool) :
    RealizesBounded .exact
      (fun ((cp, _), (b, n)) =>
        pure (addN.casesOn b (b + n) % cpMaxTail cp) : (CompParams × ℕ) × (ℕ × ℕ) → Memory.Prog ℕ)
      (WordEncoding.encode (α := (CompParams × ℕ) × (ℕ × ℕ))) (WordEncoding.encode (α := ℕ))
      (fun w ((cp, _), (b, n)) _ => 0 < cpMaxTail cp ∧ addN.casesOn b (b + n) < 2 ^ w)
      (fun _ _ => 0) := by
  have hcore : RealizesBounded .exact
      (fun (M, (b, n)) => pure (addN.casesOn b (b + n) % M) : ℕ × (ℕ × ℕ) → Memory.Prog ℕ)
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ))) (WordEncoding.encode (α := ℕ))
      (fun w (M, (b, n)) _ => 0 < M ∧ addN.casesOn b (b + n) < 2 ^ w) (fun _ _ => 0) := by
    cases addN <;>
    · realize
      all_goals (rcases d with ⟨M, ⟨b, n⟩⟩; obtain ⟨hM, hlt⟩ := h; dsimp only [Fits] at *)
      all_goals first | exact hM.ne' | exact hlt
  exact hcore.reindex (fun d : (CompParams × ℕ) × (ℕ × ℕ) => (cpMaxTail d.1.1, d.2)) _
    ![19, 37, 38] fun ⟨⟨_, _⟩, _, _⟩ i => by fin_cases i <;> rfl

private theorem realizesBounded_winGrow (addN : Bool) :
    RealizesBounded .exact
      (fun ((cp, metaBase), (b_win, n_win)) => do
        let c ← pure (addN.casesOn b_win (b_win + n_win) % cpMaxTail cp)
        writeCompTDGenProg (((cp, metaBase), n_win), c)
        writeCompDTGenProg (((cp, metaBase), c), n_win))
      (WordEncoding.encode (α := (CompParams × ℕ) × (ℕ × ℕ))) (WordEncoding.encode (α := Unit))
      (fun w ((cp, metaBase), (b_win, n_win)) s =>
        CompMetaEnv w cp metaBase s ∧ n_win < cpMaxTail cp ∧
          addN.casesOn b_win (b_win + n_win) ≤ cpN cp)
      (fun _ _ => 0) := by
  have hwtd := liftComp2 (δ := ((CompParams × ℕ) × (ℕ × ℕ)) × ℕ) realizesBounded_writeCompTDGen
    (fun d => d.1.2.2) (fun d => d.2) ⟨38, by decide⟩ ⟨39, by decide⟩
    (fun ⟨⟨_, _, _⟩, _⟩ => rfl) fun ⟨⟨_, _, _⟩, _⟩ => rfl
  have hwdt := liftComp2 (δ := (((CompParams × ℕ) × (ℕ × ℕ)) × ℕ) × Unit)
    realizesBounded_writeCompDTGen (fun d => d.1.2) (fun d => d.1.1.2.2)
    ⟨39, by decide⟩ ⟨38, by decide⟩ (fun ⟨⟨⟨_, _, _⟩, _⟩, _⟩ => rfl)
    fun ⟨⟨⟨_, _, _⟩, _⟩, _⟩ => rfl
  refine (((realizesBounded_winMod addN).bind₀ (hwtd.bind₀ hwdt)).congr
    fun ⟨⟨_, _⟩, _, _⟩ => rfl).consequence (fun w ⟨⟨_, metaBase⟩, b_win, n_win⟩ s _ _ h => ?_)
    (fun _ _ => le_rfl)
  obtain ⟨⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩, hn_lt, hnum_le⟩ := h
  have hM_pos : 0 < maxTailItems N := by change _ < maxTailItems N at hn_lt; omega
  have hnum_le' : addN.casesOn b_win (b_win + n_win) ≤ N := hnum_le
  have henv : CompMetaEnv w (mkCompParams U V w N) metaBase s :=
    ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩
  simp only [hasCompEnv_eb_prod, hasCompEnv_eb_base, cpMaxTail_mk, StateTransitionSpec.clientState,
    prog_clientResult_pure, prog_runClient_state_pure, runClient_state_writeCompTDGenProg]
  exact ⟨⟨hM_pos, lt_of_le_of_lt (hnum_le'.trans hnU) hU⟩, ⟨henv, hn_lt⟩,
    by dsimp only [WriteCompTailMapPre, CompMetaEnv] at henv ⊢; exact ⟨henv, Nat.mod_lt _ hM_pos⟩⟩

/-- Grow circular window `[b_win, b_win + n_win)` on the right by 1 (`winGrowRight`). -/
def winGrowRightGenProg : (CompParams × ℕ) × (ℕ × ℕ) → Memory.Prog Unit
  | ((cp, metaBase), (b_win, n_win)) => do
    let c ← pure ((b_win + n_win) % cpMaxTail cp)
    writeCompTDGenProg (((cp, metaBase), n_win), c)
    writeCompDTGenProg (((cp, metaBase), c), n_win)

@[simp] theorem memoryCost_winGrowRightGenProg
    (d : (CompParams × ℕ) × (ℕ × ℕ)) (s : Memory.State) :
    memoryCost (winGrowRightGenProg d) s = 8 := by
  rcases d with ⟨⟨cp, metaBase⟩, ⟨b_win, n_win⟩⟩; simp [winGrowRightGenProg]

/-- Precondition for growing the circular window on the right. -/
@[expose] def WinGrowRightPre (w : ℕ) : (CompParams × ℕ) × (ℕ × ℕ) → Memory.State → Prop
  | ((cp, metaBase), (b_win, n_win)), s =>
    CompMetaEnv w cp metaBase s ∧ n_win < cpMaxTail cp ∧ b_win + n_win ≤ cpN cp

theorem realizesBounded_winGrowRightGen :
    RealizesBounded .exact winGrowRightGenProg
      (WordEncoding.encode (α := (CompParams × ℕ) × (ℕ × ℕ))) (WordEncoding.encode (α := Unit))
      WinGrowRightPre (fun _ _ => 0) :=
  (realizesBounded_winGrow true).congr fun ⟨⟨_, _⟩, _, _⟩ => rfl

theorem clientState_winGrowRightGenProg (U V w N metaBase b_win n_win : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s
        (winGrowRightGenProg ((mkCompParams U V w N, metaBase), (b_win, n_win))) =
      { mem := writePacked (metaBase + offDenseToTail U w N) (globalPtrBits N) w
          (writePacked (metaBase + offTailToDense U w N) (globalPtrBits N) w s.mem n_win
            ((b_win + n_win) % maxTailItems N))
          ((b_win + n_win) % maxTailItems N) n_win,
        frontier := s.frontier } := by
  unfold StateTransitionSpec.clientState; simp [winGrowRightGenProg]

/-- Grow circular window `[b_win + 1, b_win + 1 + n_win)` on the left by 1 (`winGrowLeft`). -/
def winGrowLeftGenProg : (CompParams × ℕ) × (ℕ × ℕ) → Memory.Prog Unit
  | ((cp, metaBase), (b_win, n_win)) => do
    let c ← pure (b_win % cpMaxTail cp)
    writeCompTDGenProg (((cp, metaBase), n_win), c)
    writeCompDTGenProg (((cp, metaBase), c), n_win)

@[simp] theorem memoryCost_winGrowLeftGenProg
    (d : (CompParams × ℕ) × (ℕ × ℕ)) (s : Memory.State) :
    memoryCost (winGrowLeftGenProg d) s = 8 := by
  rcases d with ⟨⟨cp, metaBase⟩, ⟨b_win, n_win⟩⟩; simp [winGrowLeftGenProg]

/-- Precondition for growing the circular window on the left. -/
@[expose] def WinGrowLeftPre (w : ℕ) : (CompParams × ℕ) × (ℕ × ℕ) → Memory.State → Prop
  | ((cp, metaBase), (b_win, n_win)), s =>
    CompMetaEnv w cp metaBase s ∧ n_win < cpMaxTail cp ∧ b_win ≤ cpN cp

theorem realizesBounded_winGrowLeftGen :
    RealizesBounded .exact winGrowLeftGenProg
      (WordEncoding.encode (α := (CompParams × ℕ) × (ℕ × ℕ))) (WordEncoding.encode (α := Unit))
      WinGrowLeftPre (fun _ _ => 0) :=
  (realizesBounded_winGrow false).congr fun ⟨⟨_, _⟩, _, _⟩ => rfl

theorem clientState_winGrowLeftGenProg (U V w N metaBase b_win n_win : ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s
        (winGrowLeftGenProg ((mkCompParams U V w N, metaBase), (b_win, n_win))) =
      { mem := writePacked (metaBase + offDenseToTail U w N) (globalPtrBits N) w
          (writePacked (metaBase + offTailToDense U w N) (globalPtrBits N) w s.mem n_win
            (b_win % maxTailItems N))
          (b_win % maxTailItems N) n_win,
        frontier := s.frontier } := by
  unfold StateTransitionSpec.clientState; simp [winGrowLeftGenProg]

private theorem realizesBounded_winShrink (addN : Bool) :
    RealizesBounded .exact
      (fun ((cp, metaBase), (b_win, n_win)) => do
        let c_rem ← pure (addN.casesOn b_win (b_win + n_win) % cpMaxTail cp)
        let t_rem ← readCompDTGenProg ((cp, metaBase), c_rem)
        let c_last ← readCompTDGenProg ((cp, metaBase), n_win)
        writeCompTDGenProg (((cp, metaBase), t_rem), c_last)
        writeCompDTGenProg (((cp, metaBase), c_last), t_rem))
      (WordEncoding.encode (α := (CompParams × ℕ) × (ℕ × ℕ))) (WordEncoding.encode (α := Unit))
      (fun w ((cp, metaBase), (b_win, n_win)) s =>
        ∃ U V N,
          0 < w ∧ 0 < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
          cp = mkCompParams U V w N ∧
          metaBase + offCompItems U w N ≤ s.frontier ∧
          n_win < maxTailItems N ∧ addN.casesOn b_win (b_win + n_win) ≤ N ∧
          compDTAt metaBase U w N s.mem
            (addN.casesOn b_win (b_win + n_win) % maxTailItems N) < maxTailItems N ∧
          compTDAt metaBase U w N s.mem n_win < maxTailItems N)
      (fun _ _ => 0) := by
  have hrdt := liftComp1 (δ := ((CompParams × ℕ) × (ℕ × ℕ)) × ℕ) realizesBounded_readCompDTGen
    (fun d => d.2) ⟨39, by decide⟩ fun ⟨⟨_, _, _⟩, _⟩ => rfl
  have hrtd := liftComp1 (δ := (((CompParams × ℕ) × (ℕ × ℕ)) × ℕ) × ℕ)
    realizesBounded_readCompTDGen (fun d => d.1.1.2.2) ⟨38, by decide⟩
    fun ⟨⟨⟨_, _, _⟩, _⟩, _⟩ => rfl
  have hwtd := liftComp2 (δ := ((((CompParams × ℕ) × (ℕ × ℕ)) × ℕ) × ℕ) × ℕ)
    realizesBounded_writeCompTDGen (fun d => d.1.2) (fun d => d.2)
    ⟨40, by decide⟩ ⟨41, by decide⟩ (fun ⟨⟨⟨⟨_, _, _⟩, _⟩, _⟩, _⟩ => rfl)
    fun ⟨⟨⟨⟨_, _, _⟩, _⟩, _⟩, _⟩ => rfl
  have hwdt := liftComp2 (δ := (((((CompParams × ℕ) × (ℕ × ℕ)) × ℕ) × ℕ) × ℕ) × Unit)
    realizesBounded_writeCompDTGen (fun d => d.1.2) (fun d => d.1.1.2)
    ⟨41, by decide⟩ ⟨40, by decide⟩ (fun ⟨⟨⟨⟨⟨_, _, _⟩, _⟩, _⟩, _⟩, _⟩ => rfl)
    fun ⟨⟨⟨⟨⟨_, _, _⟩, _⟩, _⟩, _⟩, _⟩ => rfl
  refine (((realizesBounded_winMod addN).bind₀
    (hrdt.bind₀ (hrtd.bind₀ (hwtd.bind₀ hwdt)))).congr
    fun ⟨⟨_, _⟩, _, _⟩ => rfl).consequence (fun w ⟨⟨_, metaBase⟩, b_win, n_win⟩ s _ _ h => ?_)
    (fun _ _ => le_rfl)
  obtain ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr, hn_lt, hnum_le, hdt_lt, htd_lt⟩ := h
  have hM_pos : 0 < maxTailItems N := by omega
  have hcrem_lt := Nat.mod_lt (addN.casesOn b_win (b_win + n_win)) hM_pos
  have henv : CompMetaEnv w (mkCompParams U V w N) metaBase s :=
    ⟨U, V, N, hw, hN, hnU, hU, hV, rfl, hfr⟩
  simp only [hasCompEnv_eb_prod, hasCompEnv_eb_base, cpMaxTail_mk, StateTransitionSpec.clientState,
    prog_clientResult_pure, prog_runClient_state_pure,
    clientResult_readCompDTGenProg hcrem_lt, runClient_state_readCompDTGenProg,
    clientResult_readCompTDGenProg hn_lt, runClient_state_readCompTDGenProg,
    runClient_state_writeCompTDGenProg]
  exact ⟨⟨hM_pos, lt_of_le_of_lt (hnum_le.trans hnU) hU⟩, ⟨henv, hcrem_lt⟩,
    ⟨henv, hn_lt⟩, ⟨henv, hdt_lt⟩,
    by dsimp only [WriteCompTailMapPre, CompMetaEnv] at henv ⊢; exact ⟨henv, htd_lt⟩⟩

/-- Shrink circular window `[b_win, b_win + n_win + 1)` on the right by 1 (`winShrinkRight`). -/
def winShrinkRightGenProg : (CompParams × ℕ) × (ℕ × ℕ) → Memory.Prog Unit
  | ((cp, metaBase), (b_win, n_win)) => do
    let c_rem ← pure ((b_win + n_win) % cpMaxTail cp)
    let t_rem ← readCompDTGenProg ((cp, metaBase), c_rem)
    let c_last ← readCompTDGenProg ((cp, metaBase), n_win)
    writeCompTDGenProg (((cp, metaBase), t_rem), c_last)
    writeCompDTGenProg (((cp, metaBase), c_last), t_rem)

@[simp] theorem memoryCost_winShrinkRightGenProg
    (d : (CompParams × ℕ) × (ℕ × ℕ)) (s : Memory.State) :
    memoryCost (winShrinkRightGenProg d) s = 12 := by
  rcases d with ⟨⟨cp, metaBase⟩, ⟨b_win, n_win⟩⟩; simp [winShrinkRightGenProg]

/-- Precondition for shrinking the circular window on the right. -/
@[expose] def WinShrinkRightPre (w : ℕ) : (CompParams × ℕ) × (ℕ × ℕ) → Memory.State → Prop
  | ((cp, metaBase), (b_win, n_win)), s =>
    ∃ U V N,
      0 < w ∧ 0 < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧
      metaBase + offCompItems U w N ≤ s.frontier ∧
      n_win < maxTailItems N ∧ b_win + n_win ≤ N ∧
      compDTAt metaBase U w N s.mem ((b_win + n_win) % maxTailItems N) < maxTailItems N ∧
      compTDAt metaBase U w N s.mem n_win < maxTailItems N

theorem realizesBounded_winShrinkRightGen :
    RealizesBounded .exact winShrinkRightGenProg
      (WordEncoding.encode (α := (CompParams × ℕ) × (ℕ × ℕ))) (WordEncoding.encode (α := Unit))
      WinShrinkRightPre (fun _ _ => 0) :=
  (realizesBounded_winShrink true).congr fun ⟨⟨_, _⟩, _, _⟩ => rfl

/-- Shrink circular window `[b_win, b_win + n_win + 1)` on the left by 1 (`winShrinkLeft`). -/
def winShrinkLeftGenProg : (CompParams × ℕ) × (ℕ × ℕ) → Memory.Prog Unit
  | ((cp, metaBase), (b_win, n_win)) => do
    let c_rem ← pure (b_win % cpMaxTail cp)
    let t_rem ← readCompDTGenProg ((cp, metaBase), c_rem)
    let c_last ← readCompTDGenProg ((cp, metaBase), n_win)
    writeCompTDGenProg (((cp, metaBase), t_rem), c_last)
    writeCompDTGenProg (((cp, metaBase), c_last), t_rem)

@[simp] theorem memoryCost_winShrinkLeftGenProg
    (d : (CompParams × ℕ) × (ℕ × ℕ)) (s : Memory.State) :
    memoryCost (winShrinkLeftGenProg d) s = 12 := by
  rcases d with ⟨⟨cp, metaBase⟩, ⟨b_win, n_win⟩⟩; simp [winShrinkLeftGenProg]

/-- Precondition for shrinking the circular window on the left. -/
@[expose] def WinShrinkLeftPre (w : ℕ) : (CompParams × ℕ) × (ℕ × ℕ) → Memory.State → Prop
  | ((cp, metaBase), (b_win, n_win)), s =>
    ∃ U V N,
      0 < w ∧ 0 < N ∧ N ≤ U ∧ U < 2 ^ w ∧ V ≤ 2 ^ w ∧
      cp = mkCompParams U V w N ∧
      metaBase + offCompItems U w N ≤ s.frontier ∧
      n_win < maxTailItems N ∧ b_win ≤ N ∧
      compDTAt metaBase U w N s.mem (b_win % maxTailItems N) < maxTailItems N ∧
      compTDAt metaBase U w N s.mem n_win < maxTailItems N

theorem realizesBounded_winShrinkLeftGen :
    RealizesBounded .exact winShrinkLeftGenProg
      (WordEncoding.encode (α := (CompParams × ℕ) × (ℕ × ℕ))) (WordEncoding.encode (α := Unit))
      WinShrinkLeftPre (fun _ _ => 0) :=
  (realizesBounded_winShrink false).congr fun ⟨⟨_, _⟩, _, _⟩ => rfl

theorem clientState_winShrinkRightGenProg {U V w N metaBase b_win n_win : ℕ} {s : Memory.State}
    (hc : (b_win + n_win) % maxTailItems N < maxTailItems N) (hn : n_win < maxTailItems N) :
    (Memory.spec 0).clientState s
        (winShrinkRightGenProg ((mkCompParams U V w N, metaBase), (b_win, n_win))) =
      { mem := writePacked (metaBase + offDenseToTail U w N) (globalPtrBits N) w
          (writePacked (metaBase + offTailToDense U w N) (globalPtrBits N) w s.mem
            (compDTAt metaBase U w N s.mem ((b_win + n_win) % maxTailItems N))
            (compTDAt metaBase U w N s.mem n_win))
          (compTDAt metaBase U w N s.mem n_win)
          (compDTAt metaBase U w N s.mem ((b_win + n_win) % maxTailItems N)),
        frontier := s.frontier } := by
  unfold StateTransitionSpec.clientState
  simp [winShrinkRightGenProg, hc, hn]

theorem clientState_winShrinkLeftGenProg {U V w N metaBase b_win n_win : ℕ} {s : Memory.State}
    (hc : b_win % maxTailItems N < maxTailItems N) (hn : n_win < maxTailItems N) :
    (Memory.spec 0).clientState s
        (winShrinkLeftGenProg ((mkCompParams U V w N, metaBase), (b_win, n_win))) =
      { mem := writePacked (metaBase + offDenseToTail U w N) (globalPtrBits N) w
          (writePacked (metaBase + offTailToDense U w N) (globalPtrBits N) w s.mem
            (compDTAt metaBase U w N s.mem (b_win % maxTailItems N))
            (compTDAt metaBase U w N s.mem n_win))
          (compTDAt metaBase U w N s.mem n_win)
          (compDTAt metaBase U w N s.mem (b_win % maxTailItems N)),
        frontier := s.frontier } := by
  unfold StateTransitionSpec.clientState
  simp [winShrinkLeftGenProg, hc, hn]

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct
