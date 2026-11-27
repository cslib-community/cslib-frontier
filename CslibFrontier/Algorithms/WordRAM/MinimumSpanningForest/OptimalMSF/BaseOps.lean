/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MinimumSpanningForest.GraphOps.IndexedEdges
import CslibFrontier.Tactic.Fits
import CslibFrontier.Tactic.Realize
import CslibFrontier.Tactic.UpdateSimp
import CslibFrontier.Tactic.ValidProg

/-!
# Word-RAM Edge Subroutines for Optimal MSF

Word-RAM base subroutines toward Section 2.1 (p. 18), Section 5 (pp. 23–24), and Theorem 5.8
(Section 5.1, p. 27) of [PettieRamachandran2002] (#8624):

- Six faithfully word-encoded argument bundles (`AppendSelIdsArgs`, `RetagEdgesArgs`,
  `CopyStride4Args`, `ConcatThreeArgs`, `LiftEdgesArgs`, `LiftHRemArgs`).
- Six `Memory.Prog` subroutines with `Realizes .exact` (`work = 0`) and `Memory.FramedTriple`
  specifications: `appendSelIdsProg`, `retagIndexedProg`, `copyStride4Prog` (via
  `Memory.copy` / `HoldsRecords.copy`), `concatThreeProg` (via `RecordOps.concatRecordsProg`),
  `liftEdgesProg`, and `liftHRemProg`.

## Main definitions

* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.AppendSelIdsArgs`,
  `Cslib.Algorithms.WordRAM.MinimumSpanningForest.encAppendSelIdsArgs`: argument bundle and
  encoding for `appendSelIdsProg`.
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.RetagEdgesArgs`,
  `Cslib.Algorithms.WordRAM.MinimumSpanningForest.encRetagEdgesArgs`: argument bundle and
  encoding for `retagIndexedProg`.
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.CopyStride4Args`,
  `Cslib.Algorithms.WordRAM.MinimumSpanningForest.encCopyStride4Args`: argument bundle and
  encoding for `copyStride4Prog`.
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.ConcatThreeArgs`,
  `Cslib.Algorithms.WordRAM.MinimumSpanningForest.encConcatThreeArgs`: argument bundle and
  encoding for `concatThreeProg`.
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.LiftEdgesArgs`,
  `Cslib.Algorithms.WordRAM.MinimumSpanningForest.encLiftEdgesArgs`: argument bundle and
  encoding for `liftEdgesProg`.
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.LiftHRemArgs`,
  `Cslib.Algorithms.WordRAM.MinimumSpanningForest.encLiftHRemArgs`: argument bundle and
  encoding for `liftHRemProg`.
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.appendSelIdsProg`,
  `Cslib.Algorithms.WordRAM.MinimumSpanningForest.appendSelIdsProgSafe`: append selected edge IDs.
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.retagIndexedProg`,
  `Cslib.Algorithms.WordRAM.MinimumSpanningForest.retagIndexedProgSafe`: retag edge IDs `0..m-1`.
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.copyStride4Prog`,
  `Cslib.Algorithms.WordRAM.MinimumSpanningForest.copyStride4ProgSafe`: stride-4 edge array copy.
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.concatThreeProg`,
  `Cslib.Algorithms.WordRAM.MinimumSpanningForest.concatThreeProgSafe`: 3-way stride-4 concat.
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.liftEdgesProg`,
  `Cslib.Algorithms.WordRAM.MinimumSpanningForest.liftEdgesProgSafe`: lift local edges to global.
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.liftHRemProg`,
  `Cslib.Algorithms.WordRAM.MinimumSpanningForest.liftHRemProgSafe`: gather `H_rem` edges by ID.

## Main results

* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.realizes_appendSelIdsProg`,
  `Cslib.Algorithms.WordRAM.MinimumSpanningForest.appendSelIdsProg_spec`: certificates for
  `appendSelIdsProg`.
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.realizes_retagIndexedProg`,
  `Cslib.Algorithms.WordRAM.MinimumSpanningForest.retagIndexedProg_spec`: certificates for
  `retagIndexedProg`.
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.realizes_copyStride4Prog`,
  `Cslib.Algorithms.WordRAM.MinimumSpanningForest.copyStride4Prog_spec`: certificates for
  `copyStride4Prog`.
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.realizes_concatThreeProg`,
  `Cslib.Algorithms.WordRAM.MinimumSpanningForest.concatThreeProg_spec`: certificates for
  `concatThreeProg`.
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.realizes_liftEdgesProg`,
  `Cslib.Algorithms.WordRAM.MinimumSpanningForest.liftEdgesProg_spec`: certificates for
  `liftEdgesProg`.
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.realizes_liftHRemProg`,
  `Cslib.Algorithms.WordRAM.MinimumSpanningForest.liftHRemProg_spec`: certificates for
  `liftHRemProg`.

## References

* [Pettie and Ramachandran, *An Optimal Minimum Spanning Tree Algorithm*,
  Journal of the ACM 49(1), 2002][PettieRamachandran2002], Section 2.1 (p. 18),
  Section 5 (pp. 23–24), and Section 5.1 (pp. 25–27)
-/

public section

namespace Cslib.Algorithms.WordRAM.MinimumSpanningForest

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.DataStructure Cslib.DataStructure.Memory

/-! ## Section 1: Argument Structures and Encodings -/

/-- Input arguments for `appendSelIdsProg`: source edge array, destination ID array, destination
offset, and edge count. -/
structure AppendSelIdsArgs where
  /-- Base address of stride-4 source edges. -/
  srcBase : ℕ
  /-- Base address of destination edge-ID array. -/
  dstBase : ℕ
  /-- Starting element offset in destination array. -/
  dstOff : ℕ
  /-- Number of edge IDs to append. -/
  count : ℕ
  deriving DecidableEq

/-- Faithful 4-word encoding of `AppendSelIdsArgs` as `[srcBase, dstBase, dstOff, count]`. -/
word_enc_structure encAppendSelIdsArgs : AppendSelIdsArgs where
  srcBase : wordWords,
  dstBase : wordWords,
  dstOff : wordWords,
  count : wordWords

instance : WordEncoding AppendSelIdsArgs := ⟨4, encAppendSelIdsArgs⟩

/-- Input arguments for `retagIndexedProg`: source stride-4 edge array base and edge count. -/
structure RetagEdgesArgs where
  /-- Base address of stride-4 source edges. -/
  srcBase : ℕ
  /-- Number of edges to retag. -/
  count : ℕ
  deriving DecidableEq

/-- Faithful 2-word encoding of `RetagEdgesArgs` as `[srcBase, count]`. -/
word_enc_structure encRetagEdgesArgs : RetagEdgesArgs where
  srcBase : wordWords,
  count : wordWords

instance : WordEncoding RetagEdgesArgs := ⟨2, encRetagEdgesArgs⟩

/-- Input arguments for `copyStride4Prog`: source base, destination base, destination edge offset,
and edge count. -/
structure CopyStride4Args where
  /-- Base address of stride-4 source edges. -/
  srcBase : ℕ
  /-- Base address of stride-4 destination array. -/
  dstBase : ℕ
  /-- Starting edge offset in destination array. -/
  dstOff : ℕ
  /-- Number of stride-4 edges to copy. -/
  count : ℕ
  deriving DecidableEq

/-- Faithful 4-word encoding of `CopyStride4Args` as `[srcBase, dstBase, dstOff, count]`. -/
word_enc_structure encCopyStride4Args : CopyStride4Args where
  srcBase : wordWords,
  dstBase : wordWords,
  dstOff : wordWords,
  count : wordWords

instance : WordEncoding CopyStride4Args := ⟨4, encCopyStride4Args⟩

/-- Input arguments for `concatThreeProg`: base addresses and lengths of three stride-4 edge
arrays. -/
structure ConcatThreeArgs where
  /-- Base of first stride-4 array. -/
  base1 : ℕ
  /-- Length of first array. -/
  len1 : ℕ
  /-- Base of second stride-4 array. -/
  base2 : ℕ
  /-- Length of second array. -/
  len2 : ℕ
  /-- Base of third stride-4 array. -/
  base3 : ℕ
  /-- Length of third array. -/
  len3 : ℕ
  deriving DecidableEq

/-- Faithful 6-word encoding of `ConcatThreeArgs` as
`[base1, len1, base2, len2, base3, len3]`. -/
word_enc_structure encConcatThreeArgs : ConcatThreeArgs where
  base1 : wordWords,
  len1 : wordWords,
  base2 : wordWords,
  len2 : wordWords,
  base3 : wordWords,
  len3 : wordWords

instance : WordEncoding ConcatThreeArgs := ⟨6, encConcatThreeArgs⟩

/-- Input arguments for `liftEdgesProg`: local edge base, vertex lift map, global destination
array base, destination edge offset, and edge count. -/
structure LiftEdgesArgs where
  /-- Base address of local stride-4 edges. -/
  srcBase : ℕ
  /-- Base address of vertex lift table. -/
  liftBase : ℕ
  /-- Base address of global destination stride-4 array. -/
  dstBase : ℕ
  /-- Starting edge offset in destination array. -/
  dstOff : ℕ
  /-- Number of edges to lift. -/
  count : ℕ
  deriving DecidableEq

/-- Faithful 5-word encoding of `LiftEdgesArgs` as
`[srcBase, liftBase, dstBase, dstOff, count]`. -/
word_enc_structure encLiftEdgesArgs : LiftEdgesArgs where
  srcBase : wordWords,
  liftBase : wordWords,
  dstBase : wordWords,
  dstOff : wordWords,
  count : wordWords

instance : WordEncoding LiftEdgesArgs := ⟨5, encLiftEdgesArgs⟩

/-- Input arguments for `liftHRemProg`: original edge array base, MSF edge array base, and MSF
edge count. -/
structure LiftHRemArgs where
  /-- Base address of stride-4 original edges `H_rem`. -/
  hRemBase : ℕ
  /-- Base address of stride-4 MSF edges. -/
  msfBase : ℕ
  /-- Number of MSF edges to gather. -/
  count : ℕ
  deriving DecidableEq

/-- Faithful 3-word encoding of `LiftHRemArgs` as `[hRemBase, msfBase, count]`. -/
word_enc_structure encLiftHRemArgs : LiftHRemArgs where
  hRemBase : wordWords,
  msfBase : wordWords,
  count : wordWords

instance : WordEncoding LiftHRemArgs := ⟨3, encLiftHRemArgs⟩

private structure AppendSelEnv where
  srcBase : ℕ
  dstBase : ℕ
  deriving DecidableEq

private word_enc_structure encAppendSelEnv : AppendSelEnv where
  srcBase : wordWords,
  dstBase : wordWords

private instance : WordEncoding AppendSelEnv := ⟨2, encAppendSelEnv⟩

private structure RetagEnv where
  srcBase : ℕ
  outBase : ℕ
  deriving DecidableEq

private word_enc_structure encRetagEnv : RetagEnv where
  srcBase : wordWords,
  outBase : wordWords

private instance : WordEncoding RetagEnv := ⟨2, encRetagEnv⟩

private structure LiftEdgesEnv where
  srcBase : ℕ
  liftBase : ℕ
  dstBase : ℕ
  deriving DecidableEq

private word_enc_structure encLiftEdgesEnv : LiftEdgesEnv where
  srcBase : wordWords,
  liftBase : wordWords,
  dstBase : wordWords

private instance : WordEncoding LiftEdgesEnv := ⟨3, encLiftEdgesEnv⟩

private structure LiftHRemEnv where
  hRemBase : ℕ
  msfBase : ℕ
  outBase : ℕ
  deriving DecidableEq

private word_enc_structure encLiftHRemEnv : LiftHRemEnv where
  hRemBase : wordWords,
  msfBase : wordWords,
  outBase : wordWords

private instance : WordEncoding LiftHRemEnv := ⟨3, encLiftHRemEnv⟩

private structure Stride4Words where
  u : ℕ
  v : ℕ
  wt : ℕ
  eid : ℕ

private word_enc_structure encStride4Words : Stride4Words where
  u : wordWords,
  v : wordWords,
  wt : wordWords,
  eid : wordWords

private instance : WordEncoding Stride4Words := ⟨4, encStride4Words⟩

/-! ## Section 2: Word-RAM Edge Subroutines and Specifications -/

private theorem iterate_bind_snd_ft {w C : ℕ} {S : Set ℕ} {s : Memory.State}
    {p : Memory.Prog (ℕ × ℕ)}
    (hv : (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s p))
    (hm : memoryCost p s ≤ C)
    (hmod : Memory.Modifies S s ((Memory.spec 0).clientState s p))
    {Q : ℕ → Memory.State → Prop}
    (hq : Q ((Memory.spec 0).clientResult s p).2 ((Memory.spec 0).clientState s p)) :
    Memory.FramedTriple w s (p >>= fun st => pure st.2) C S Q := by
  refine framedTriple_iff_realization.mpr ⟨validHistory_bind_step hv (validHistory_pure w _ _),
    ?_, ?_, ?_⟩
  · rw [memoryCost_bind', memoryCost_pure, Nat.add_zero]; exact hm
  · rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_pure]; exact hmod
  · rw [StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientResult_pure,
      StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_pure]; exact hq

private theorem allocDirty4_bind_pure_ft {w count C : ℕ} {S : Set ℕ} {s : Memory.State}
    {f : ℕ → Memory.Prog ℕ}
    (hfit : Fits w (s.frontier + 4 * count)) (hS : ∀ a ∈ S, s.frontier ≤ a)
    (hv : (Memory.spec w).ValidHistory ⟨s.mem, s.frontier + 4 * count⟩
      ((Memory.spec w).clientHistory ⟨s.mem, s.frontier + 4 * count⟩ (f s.frontier)))
    (hm : memoryCost (f s.frontier) ⟨s.mem, s.frontier + 4 * count⟩ ≤ C)
    (hmod : Memory.Modifies S ⟨s.mem, s.frontier + 4 * count⟩
      ((Memory.spec 0).clientState ⟨s.mem, s.frontier + 4 * count⟩ (f s.frontier)))
    {Q : ℕ → Memory.State → Prop}
    (hq : Q s.frontier
      ((Memory.spec 0).clientState ⟨s.mem, s.frontier + 4 * count⟩ (f s.frontier))) :
    Memory.FramedTriple w s (Memory.allocDirty (4 * count) >>= fun ob =>
      f ob >>= fun _ => pure ob) (C + 1) ∅ Q := by
  have hft : Memory.FramedTriple w ⟨s.mem, s.frontier + 4 * count⟩ (f s.frontier) C S
      fun _ s' => Memory.FramedTriple w s' (pure s.frontier) 0 S Q :=
    framedTriple_iff_realization.mpr ⟨hv, hm, hmod, Memory.FramedTriple.pure hq⟩
  exact ((Memory.FramedTriple.allocDirty_bind hfit
    ((Memory.FramedTriple.bind_same hft).mono (Nat.add_zero _).le
      fun _ _ h => h)).frame_empty_of_ge_frontier hS).mono (by omega : C + 0 + 1 ≤ C + 1)
    fun _ _ h => h

/-! ### `appendSelIdsProg`: Append Edge IDs from Stride-4 Array -/

private def appendSelIdStep (d : AppendSelEnv × (ℕ × ℕ)) : Memory.Prog (ℕ × ℕ) := do
  let eid ← Memory.read (d.1.srcBase + 4 * d.2.1 + 3)
  Memory.write (d.1.dstBase + d.2.2) eid
  pure (d.2.1 + 1, d.2.2 + 1)

private def appendSelIdStepSafe (w : ℕ) (d : AppendSelEnv × (ℕ × ℕ)) (s : Memory.State) : Prop :=
  Fits w 16 ∧ Fits w (d.2.1 + 1) ∧ Fits w (d.2.2 + 1) ∧
    d.1.srcBase + 4 * d.2.1 + 3 < s.frontier ∧ d.1.dstBase + d.2.2 < s.frontier

private theorem realizes_appendSelIdStep_history : Realizes .exact
    appendSelIdStep
    (appendWords (WordEncoding.encode (α := AppendSelEnv)) (WordEncoding.encode (α := ℕ × ℕ)))
    (WordEncoding.encode (α := ℕ × ℕ))
    (fun w d s => appendSelIdStepSafe w d s ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (appendSelIdStep d)))
    (fun _ _ => 0) := by
  unfold appendSelIdStep
  realize
  all_goals
    obtain ⟨⟨h16, hfit1, hfit2, h1, h2⟩, hv⟩ := h
    have hfront := hmem.frontier_fits
    dsimp only [StateTransitionSpec.clientHistory] at hv
    simp_all only [StateTransitionSpec.runClient_lift_bind',
      StateTransitionSpec.validHistory_cons, StateTransitionSpec.stepFn, Memory.read,
      Memory.write, Memory.step_read, Memory.step_write, Memory.valid]
  all_goals fits

private theorem realizes_appendSelIdStep : Realizes .exact
    appendSelIdStep
    (appendWords (WordEncoding.encode (α := AppendSelEnv)) (WordEncoding.encode (α := ℕ × ℕ)))
    (WordEncoding.encode (α := ℕ × ℕ)) appendSelIdStepSafe (fun _ _ => 0) :=
  realizes_appendSelIdStep_history.consequence_valid fun _ _ _ _ _ hv h => ⟨h, hv⟩

/-- Append `a.count` original edge IDs (`e.id`) from stride-4 source array `a.srcBase` into
`a.dstBase` starting at offset `a.dstOff`, returning `a.dstOff + a.count`. -/
def appendSelIdsProg (a : AppendSelIdsArgs) : Memory.Prog ℕ := do
  let st ← iterate appendSelIdStep ⟨a.srcBase, a.dstBase⟩ a.count (0, a.dstOff)
  pure st.2

/-- Safety domain for `appendSelIdsProg`. -/
@[expose] def appendSelIdsProgSafe (w : ℕ) (a : AppendSelIdsArgs) (s : Memory.State) : Prop :=
  Fits w 16 ∧ a.srcBase + 4 * a.count ≤ s.frontier ∧
    a.dstBase + a.dstOff + a.count ≤ s.frontier

private theorem appendSelIdsProg_word_spec {w srcBase dstBase dstOff count : ℕ}
    {s : Memory.State} (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hsrc_lt : srcBase + 4 * count ≤ s.frontier)
    (hdst_lt : dstBase + dstOff + count ≤ s.frontier) :
    let e : AppendSelEnv := ⟨srcBase, dstBase⟩
    let S := Set.Ico (dstBase + dstOff) (dstBase + dstOff + count)
    iterationSafe appendSelIdStep appendSelIdStepSafe w e count (0, dstOff) s ∧
    Memory.FramedTriple w s (appendSelIdsProg ⟨srcBase, dstBase, dstOff, count⟩) (2 * count) S
      fun res s' =>
        res = dstOff + count ∧ s'.frontier = s.frontier ∧ Memory.WellFormed w s' ∧
        ((srcBase + 4 * count ≤ dstBase + dstOff ∨ dstBase + dstOff + count ≤ srcBase) →
          ∀ j < count, s'.mem (dstBase + dstOff + j) = s.mem (srcBase + 4 * j + 3)) := by
  let e : AppendSelEnv := ⟨srcBase, dstBase⟩
  let S : Set ℕ := Set.Ico (dstBase + dstOff) (dstBase + dstOff + count)
  let inv (k : ℕ) (a : ℕ × ℕ) (t : Memory.State) : Prop :=
    a = (k, dstOff + k) ∧ t.frontier = s.frontier ∧ Memory.WellFormed w t ∧
    (∀ x, x ∉ S → t.mem x = s.mem x) ∧
    ((srcBase + 4 * count ≤ dstBase + dstOff ∨ dstBase + dstOff + count ≤ srcBase) →
      ∀ j < k, t.mem (dstBase + dstOff + j) = s.mem (srcBase + 4 * j + 3))
  have hstep : ∀ k < count, ∀ a t, inv k a t →
      appendSelIdStepSafe w (e, a) t ∧
      (Memory.spec w).ValidHistory t ((Memory.spec w).clientHistory t (appendSelIdStep (e, a))) ∧
      let a' := (Memory.spec 0).clientResult t (appendSelIdStep (e, a))
      let t' := (Memory.spec 0).clientState t (appendSelIdStep (e, a))
      memoryCost (appendSelIdStep (e, a)) t + 0 ≤ 0 + 2 ∧
      Memory.Modifies S t t' ∧
      inv (k + 1) a' t' := by
    intro k hk a t ⟨ha, htfr, hwt, hframe, hpref⟩
    subst a
    have hfit_k1 : Fits w (k + 1) := hwf.frontier_fits.of_le (by omega)
    have hfit_ok1 : Fits w (dstOff + k + 1) := hwf.frontier_fits.of_le (by omega)
    have hmem_t : ∀ x, Fits w (t.mem x) := hwt.mem_fits
    have hvh : (Memory.spec w).ValidHistory t
        ((Memory.spec w).clientHistory t (appendSelIdStep (e, (k, dstOff + k)))) := by
      dsimp only [appendSelIdStep, e]
      valid_prog
      all_goals first | exact hmem_t _ | omega
    have hcost : memoryCost (appendSelIdStep (e, (k, dstOff + k))) t ≤ 2 := by
      dsimp only [appendSelIdStep, e]
      prog_cost
    have hres : (Memory.spec 0).clientResult t (appendSelIdStep (e, (k, dstOff + k))) =
        (k + 1, dstOff + (k + 1)) := by
      dsimp only [appendSelIdStep, e]
      simp only [clientResult_bind_read, clientResult_bind_write,
        StateTransitionSpec.clientResult_pure, Nat.add_assoc]
    have hst : (Memory.spec 0).clientState t (appendSelIdStep (e, (k, dstOff + k))) =
        ⟨Function.update t.mem (dstBase + (dstOff + k)) (t.mem (srcBase + 4 * k + 3)),
          t.frontier⟩ := by
      dsimp only [appendSelIdStep, e]
      rw [clientState_bind_read, clientState_bind_write, StateTransitionSpec.clientState_pure]
    have hupd_out : ∀ x, x ∉ S →
        ((Memory.spec 0).clientState t (appendSelIdStep (e, (k, dstOff + k)))).mem x =
          t.mem x := by
      intro x hx
      rw [hst]
      simp only [S, Set.mem_Ico, not_and_or, not_le, not_lt] at hx
      update_simp
    refine ⟨⟨h16, hfit_k1, hfit_ok1, by dsimp only [e]; omega, by dsimp only [e]; omega⟩,
      hvh, by omega, ⟨by rw [hst], fun x _ hx => hupd_out x hx⟩,
      hres, by rw [hst]; exact htfr, wellFormed_clientState hwt hvh,
      fun x hx => (hupd_out x hx).trans (hframe x hx), fun hd j hj => ?_⟩
    rw [hst]; dsimp only
    by_cases hjk : j = k
    · subst j
      have hin_src : t.mem (srcBase + 4 * k + 3) = s.mem (srcBase + 4 * k + 3) :=
        hframe _ (by simp only [S, Set.mem_Ico]; rcases hd with hdl | hdr <;> omega)
      rw [show dstBase + (dstOff + k) = dstBase + dstOff + k by omega, Function.update_self,
        hin_src]
    · update_simp; exact hpref hd j (by omega)
  obtain ⟨hsafe_it, hv_it, hm_it, hmod_it, hres_it, hfr_it, hwf_it, _, hvals_it⟩ :=
    iterate_potential_spec appendSelIdStep appendSelIdStepSafe w e 2 count inv (fun _ _ _ => 0)
      S hstep (0, dstOff) s
      ⟨rfl, rfl, hwf, fun _ _ => rfl, fun _ _ h => absurd h (Nat.not_lt_zero _)⟩
  exact ⟨hsafe_it, iterate_bind_snd_ft hv_it (by simpa using hm_it) hmod_it
    ⟨congrArg Prod.snd hres_it, hfr_it, hwf_it, hvals_it⟩⟩

/-- Uniform `Realizes .exact` certificate (`work = 0`) for `appendSelIdsProg`. -/
theorem realizes_appendSelIdsProg : Realizes .exact
    appendSelIdsProg
    (WordEncoding.encode (α := AppendSelIdsArgs)) (WordEncoding.encode (α := ℕ))
    appendSelIdsProgSafe (fun _ _ => 0) := by
  have hraw : Realizes .exact
      (fun a : AppendSelIdsArgs => do
        let st ← iterate appendSelIdStep ⟨a.srcBase, a.dstBase⟩ a.count (0, a.dstOff)
        pure st.2)
      (WordEncoding.encode (α := AppendSelIdsArgs)) (WordEncoding.encode (α := ℕ))
      (fun w a s => Fits w 16 ∧
        iterationSafe appendSelIdStep appendSelIdStepSafe w ⟨a.srcBase, a.dstBase⟩ a.count
          (0, a.dstOff) s)
      (fun _ _ => 0) := by
    realize [realizes_appendSelIdStep]
    exact iterationSafe_imp h.2 (fun _ => rfl) (fun _ _ hs => hs)
  refine hraw.consequence (fun w a s _ hmem ⟨h16, hsrc, hdst⟩ => ?_) (fun _ _ => le_rfl)
  exact ⟨h16, (appendSelIdsProg_word_spec h16 hmem hsrc hdst).1⟩

/-- Framed specification for `appendSelIdsProg`: copies `srcEs[j].id` into
`dstBase + dstOff + j` for `j < srcEs.length`, modifying only
`Set.Ico (dstBase + dstOff) (dstBase + dstOff + srcEs.length)`, in at most `2 * srcEs.length`
memory operations. -/
theorem appendSelIdsProg_spec {w n srcBase dstBase dstOff : ℕ}
    {srcEs : List (IndexedEdge n)} {s : Memory.State}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hin : HoldsIndexedEdges srcBase srcEs s.mem)
    (hin_lt : srcBase + 4 * srcEs.length ≤ s.frontier)
    (hdst_lt : dstBase + dstOff + srcEs.length ≤ s.frontier)
    (hdisj : srcBase + 4 * srcEs.length ≤ dstBase + dstOff ∨
      dstBase + dstOff + srcEs.length ≤ srcBase) :
    Memory.FramedTriple w s (appendSelIdsProg ⟨srcBase, dstBase, dstOff, srcEs.length⟩)
      (2 * srcEs.length) (Set.Ico (dstBase + dstOff) (dstBase + dstOff + srcEs.length))
      fun res s' =>
        res = dstOff + srcEs.length ∧
        s'.frontier = s.frontier ∧
        Memory.WellFormed w s' ∧
        ∀ j (hj : j < srcEs.length), s'.mem (dstBase + dstOff + j) = srcEs[j].id := by
  refine (appendSelIdsProg_word_spec h16 hwf hin_lt hdst_lt).2.mono le_rfl
    fun res s' ⟨hres, hfr, hwf', hvals⟩ =>
      ⟨hres, hfr, hwf', fun j hj => (hvals hdisj j hj).trans (hin j hj).2.2.2⟩

/-! ### Private Stride-4 Read/Write Helpers -/

private def stride4At (base idx : ℕ) (ew : Stride4Words) (mem : ℕ → ℕ) : Prop :=
  mem (base + 4 * idx) = ew.u ∧ mem (base + 4 * idx + 1) = ew.v ∧
    mem (base + 4 * idx + 2) = ew.wt ∧ mem (base + 4 * idx + 3) = ew.eid

private theorem stride4At_congr {base idx : ℕ} {ew : Stride4Words} {m₁ m₂ : ℕ → ℕ}
    (heq : ∀ q < 4, m₂ (base + 4 * idx + q) = m₁ (base + 4 * idx + q))
    (h : stride4At base idx ew m₁) : stride4At base idx ew m₂ :=
  ⟨(heq 0 (by decide)).trans h.1, (heq 1 (by decide)).trans h.2.1,
    (heq 2 (by decide)).trans h.2.2.1, (heq 3 (by decide)).trans h.2.2.2⟩

private def writeStride4 (d : (ℕ × ℕ) × Stride4Words) : Memory.Prog ℕ := do
  Memory.write (d.1.1 + 4 * d.1.2) d.2.u
  Memory.write (d.1.1 + 4 * d.1.2 + 1) d.2.v
  Memory.write (d.1.1 + 4 * d.1.2 + 2) d.2.wt
  Memory.write (d.1.1 + 4 * d.1.2 + 3) d.2.eid
  pure (d.1.2 + 1)

private def writeStride4Safe (w : ℕ) (d : (ℕ × ℕ) × Stride4Words) (s : Memory.State) : Prop :=
  Fits w 16 ∧ Fits w (d.1.2 + 1) ∧ Fits w d.2.u ∧ Fits w d.2.v ∧ Fits w d.2.wt ∧
    Fits w d.2.eid ∧ d.1.1 + 4 * d.1.2 + 3 < s.frontier

private theorem realizes_writeStride4_history : Realizes .exact
    writeStride4
    (appendWords (WordEncoding.encode (α := ℕ × ℕ)) (WordEncoding.encode (α := Stride4Words)))
    (WordEncoding.encode (α := ℕ))
    (fun w d s => writeStride4Safe w d s ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (writeStride4 d)))
    (fun _ _ => 0) := by
  unfold writeStride4
  realize
  all_goals
    obtain ⟨⟨h16, hfit, hu, hv1, hw1, hid, hlt⟩, hv⟩ := h
    have hfront := hmem.frontier_fits
    dsimp only [StateTransitionSpec.clientHistory] at hv
    simp_all only [StateTransitionSpec.runClient_lift_bind',
      StateTransitionSpec.validHistory_cons, StateTransitionSpec.stepFn, Memory.write,
      Memory.step_write, Memory.valid]
  all_goals fits

private theorem realizes_writeStride4 : Realizes .exact
    writeStride4
    (appendWords (WordEncoding.encode (α := ℕ × ℕ)) (WordEncoding.encode (α := Stride4Words)))
    (WordEncoding.encode (α := ℕ)) writeStride4Safe (fun _ _ => 0) :=
  realizes_writeStride4_history.consequence_valid fun _ _ _ _ _ hv h => ⟨h, hv⟩

private theorem writeStride4_spec {w dst idx : ℕ} {ew : Stride4Words} {s : Memory.State}
    (hwf : Memory.WellFormed w s)
    (hu : Fits w ew.u) (hv : Fits w ew.v) (hwt : Fits w ew.wt) (heid : Fits w ew.eid)
    (hlt : dst + 4 * idx + 3 < s.frontier) :
    let S := Set.Ico (dst + 4 * idx) (dst + 4 * idx + 4)
    Memory.FramedTriple w s (writeStride4 ((dst, idx), ew)) 4 S fun res s' =>
      res = idx + 1 ∧ s'.frontier = s.frontier ∧ Memory.WellFormed w s' ∧
      stride4At dst idx ew s'.mem := by
  have hprog : writeStride4 ((dst, idx), ew) =
      (Memory.write (dst + 4 * idx) ew.u >>= fun _ =>
        Memory.write (dst + 4 * idx + 1) ew.v >>= fun _ =>
          Memory.write (dst + 4 * idx + 2) ew.wt >>= fun _ =>
            Memory.write (dst + 4 * idx + 3) ew.eid >>= fun _ => pure (idx + 1)) := rfl
  have hvh : (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (writeStride4 ((dst, idx), ew))) := by
    rw [hprog]; valid_prog; all_goals (try dsimp only); omega
  have hst : (Memory.spec 0).clientState s (writeStride4 ((dst, idx), ew)) =
      ⟨Function.update (Function.update (Function.update (Function.update s.mem
        (dst + 4 * idx) ew.u) (dst + 4 * idx + 1) ew.v) (dst + 4 * idx + 2) ew.wt)
        (dst + 4 * idx + 3) ew.eid, s.frontier⟩ := by
    rw [hprog]; repeat rw [clientState_bind_write]; rfl
  have hmod : Memory.Modifies (Set.Ico (dst + 4 * idx) (dst + 4 * idx + 4)) s
      ((Memory.spec 0).clientState s (writeStride4 ((dst, idx), ew))) := by
    refine ⟨by rw [hst], fun x _ hx => ?_⟩
    rw [hst]
    simp only [Set.mem_Ico, not_and_or, not_le, not_lt] at hx
    update_simp
  refine framedTriple_iff_realization.mpr ⟨hvh, ?_, hmod, ?_, by rw [hst],
    wellFormed_clientState hwf hvh, ?_⟩
  · rw [hprog]; prog_cost
  · rw [hprog]; simp only [clientResult_bind_write, StateTransitionSpec.clientResult_pure]
  · rw [hst]; dsimp only [stride4At]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> update_simp

private def readStride4 (d : ℕ × ℕ) : Memory.Prog Stride4Words := do
  let u ← Memory.read (d.1 + 4 * d.2)
  let v ← Memory.read (d.1 + 4 * d.2 + 1)
  let wt ← Memory.read (d.1 + 4 * d.2 + 2)
  let eid ← Memory.read (d.1 + 4 * d.2 + 3)
  pure ⟨u, v, wt, eid⟩

private def readStride4Safe (w : ℕ) (d : ℕ × ℕ) (s : Memory.State) : Prop :=
  Fits w 16 ∧ d.1 + 4 * d.2 + 3 < s.frontier

private theorem realizes_readStride4_history : Realizes .exact
    readStride4 (WordEncoding.encode (α := ℕ × ℕ)) (WordEncoding.encode (α := Stride4Words))
    (fun w d s => readStride4Safe w d s ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (readStride4 d)))
    (fun _ _ => 0) := by
  unfold readStride4
  realize
  all_goals
    obtain ⟨⟨h16, hlt⟩, hv⟩ := h
    have hfront := hmem.frontier_fits
    dsimp only [StateTransitionSpec.clientHistory] at hv
    simp_all only [StateTransitionSpec.runClient_lift_bind',
      StateTransitionSpec.validHistory_cons, StateTransitionSpec.stepFn, Memory.read,
      Memory.step_read, Memory.valid]
  all_goals fits

private theorem realizes_readStride4 : Realizes .exact
    readStride4 (WordEncoding.encode (α := ℕ × ℕ)) (WordEncoding.encode (α := Stride4Words))
    readStride4Safe (fun _ _ => 0) :=
  realizes_readStride4_history.consequence_valid fun _ _ _ _ _ hv h => ⟨h, hv⟩

private theorem readStride4_spec {w base idx : ℕ} {s : Memory.State}
    (hlt : base + 4 * idx + 3 < s.frontier) :
    Memory.FramedTriple w s (readStride4 (base, idx)) 4 ∅ fun res s' =>
      res = ⟨s.mem (base + 4 * idx), s.mem (base + 4 * idx + 1),
        s.mem (base + 4 * idx + 2), s.mem (base + 4 * idx + 3)⟩ ∧ s' = s :=
  Memory.FramedTriple.read_bind (by omega) <|
    Memory.FramedTriple.read_bind (by omega) <|
      Memory.FramedTriple.read_bind (by omega) <|
        Memory.FramedTriple.read_bind hlt <|
          Memory.FramedTriple.pure ⟨rfl, rfl⟩

private theorem stride4WriteAfterRead_ft {w cRead outBase k frEnd : ℕ} {t : Memory.State}
    {rd : Memory.Prog Stride4Words} {adj : Stride4Words → Stride4Words}
    {ewRead ewGoal : Stride4Words}
    (hwt : Memory.WellFormed w t) (hfr : t.frontier = frEnd) (hlt : outBase + 4 * k + 3 < frEnd)
    (hr : Memory.FramedTriple w t rd cRead ∅ fun ew t₁ => ew = ewRead ∧ t₁ = t)
    (hadj : adj ewRead = ewGoal)
    (hu : Fits w ewGoal.u) (hv : Fits w ewGoal.v) (hwtF : Fits w ewGoal.wt)
    (heid : Fits w ewGoal.eid) :
    let Sk := Set.Ico (outBase + 4 * k) (outBase + 4 * k + 4)
    Memory.FramedTriple w t (rd >>= fun ew => writeStride4 ((outBase, k), adj ew))
      (cRead + 4) Sk fun a' t' =>
        a' = k + 1 ∧ t'.frontier = frEnd ∧ Memory.WellFormed w t' ∧
        stride4At outBase k ewGoal t'.mem := by
  intro Sk
  have hsub : Memory.FramedTriple w t rd cRead Sk fun ew t₁ =>
      Memory.FramedTriple w t₁ (writeStride4 ((outBase, k), adj ew)) 4 Sk fun a' t' =>
        a' = k + 1 ∧ t'.frontier = frEnd ∧ Memory.WellFormed w t' ∧
        stride4At outBase k ewGoal t'.mem := by
    refine (hr.frame_mono (Set.empty_subset Sk)).mono le_rfl fun ew t₁ ⟨hew, ht₁⟩ => ?_
    rw [ht₁, hew, hadj]
    have hw := writeStride4_spec (w := w) (dst := outBase) (idx := k) (ew := ewGoal)
      hwt hu hv hwtF heid (by rw [hfr]; exact hlt)
    exact hw.mono le_rfl fun res t' ⟨hres, hfr', hwt', hstr⟩ =>
      ⟨hres, hfr'.trans hfr, hwt', hstr⟩
  exact hsub.bind_same

private theorem allocDirty_stride4_loop_spec {w count stepCost : ℕ} {Γ : Type} {s : Memory.State}
    (ctx : ℕ → Γ) (step : Γ × ℕ → Memory.Prog ℕ)
    (stepSafe : ℕ → Γ × ℕ → Memory.State → Prop)
    (target : ℕ → Stride4Words)
    (hwf : Memory.WellFormed w s) (hfit : Fits w (s.frontier + 4 * count))
    (hstep_spec : ∀ k < count, ∀ t : Memory.State,
      t.frontier = s.frontier + 4 * count → Memory.WellFormed w t →
      (∀ x < s.frontier, t.mem x = s.mem x) →
      stepSafe w (ctx s.frontier, k) t ∧
      Memory.FramedTriple w t (step (ctx s.frontier, k)) stepCost
        (Set.Ico (s.frontier + 4 * k) (s.frontier + 4 * k + 4)) fun a' t' =>
          a' = k + 1 ∧ t'.frontier = s.frontier + 4 * count ∧ Memory.WellFormed w t' ∧
          stride4At s.frontier k (target k) t'.mem) :
    iterationSafe step stepSafe w (ctx s.frontier) count 0 ⟨s.mem, s.frontier + 4 * count⟩ ∧
    Memory.FramedTriple w s
      (Memory.allocDirty (4 * count) >>= fun ob =>
        iterate step (ctx ob) count 0 >>= fun _ => pure ob)
      (stepCost * count + 1) ∅ fun outBase s' =>
        outBase = s.frontier ∧ s'.frontier = s.frontier + 4 * count ∧ Memory.WellFormed w s' ∧
        ∀ i < count, stride4At outBase i (target i) s'.mem := by
  let s₀ : Memory.State := ⟨s.mem, s.frontier + 4 * count⟩
  let S : Set ℕ := Set.Ico s.frontier (s.frontier + 4 * count)
  have hwf₀ : Memory.WellFormed w s₀ := ⟨hfit, hwf.mem_fits⟩
  let inv (k a : ℕ) (t : Memory.State) : Prop :=
    a = k ∧ t.frontier = s₀.frontier ∧ Memory.WellFormed w t ∧
    (∀ x < s.frontier, t.mem x = s.mem x) ∧
    ∀ i < k, stride4At s.frontier i (target i) t.mem
  have hstep : ∀ k < count, ∀ a t, inv k a t →
      stepSafe w (ctx s.frontier, a) t ∧
      (Memory.spec w).ValidHistory t
        ((Memory.spec w).clientHistory t (step (ctx s.frontier, a))) ∧
      let a' := (Memory.spec 0).clientResult t (step (ctx s.frontier, a))
      let t' := (Memory.spec 0).clientState t (step (ctx s.frontier, a))
      memoryCost (step (ctx s.frontier, a)) t + 0 ≤ 0 + stepCost ∧
      Memory.Modifies S t t' ∧
      inv (k + 1) a' t' := by
    intro k hk a t ⟨ha, htfr, hwt, hframe, hpref⟩
    subst a
    obtain ⟨hsafe_s, hft_s⟩ := hstep_spec k hk t htfr hwt hframe
    obtain ⟨hv_s, hc_s, hmod_s, hres_s, ht'_fr, hwt', hstr_k⟩ :=
      framedTriple_iff_realization.mp hft_s
    have hmod_S : Memory.Modifies S t
        ((Memory.spec 0).clientState t (step (ctx s.frontier, k))) :=
      hmod_s.mono fun x hx => by simp only [S, Set.mem_Ico] at hx ⊢; omega
    have hmem_keep : ∀ x < s.frontier,
        ((Memory.spec 0).clientState t (step (ctx s.frontier, k))).mem x = t.mem x :=
      fun x hx => hmod_s.mem_eq_of_not_mem (by rw [htfr]; change x < s.frontier + 4 * count; omega)
        (by simp only [Set.mem_Ico]; omega)
    refine ⟨hsafe_s, hv_s, by omega, hmod_S,
      hres_s, ht'_fr, hwt', fun x hx => (hmem_keep x hx).trans (hframe x hx), fun i hi => ?_⟩
    by_cases hik : i = k
    · subst i; exact hstr_k
    · exact stride4At_congr (fun q hq => hmod_s.mem_eq_of_not_mem
        (by rw [htfr]; change s.frontier + 4 * i + q < s.frontier + 4 * count; omega)
        (by simp only [Set.mem_Ico]; omega)) (hpref i (by omega))
  obtain ⟨hsafe_it, hv_it, hm_it, hmod_it, _, hfr_it, hwf_it, _, hvals_it⟩ :=
    iterate_potential_spec step stepSafe w (ctx s.frontier) stepCost count
      inv (fun _ _ _ => 0) S hstep 0 s₀
      ⟨rfl, rfl, hwf₀, fun _ _ => rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  exact ⟨hsafe_it, allocDirty4_bind_pure_ft (S := S)
    (f := fun ob => iterate step (ctx ob) count 0)
    hfit (fun _ ha => ha.1) hv_it (by simpa using hm_it) hmod_it ⟨rfl, hfr_it, hwf_it, hvals_it⟩⟩

/-! ### `retagIndexedProg`: Retag Edge IDs `0..m-1` -/

private def retagStep (d : RetagEnv × ℕ) : Memory.Prog ℕ := do
  let ew ← readStride4 (d.1.srcBase, d.2)
  writeStride4 ((d.1.outBase, d.2), ⟨ew.u, ew.v, ew.wt, d.2⟩)

private def retagStepSafe (w : ℕ) (d : RetagEnv × ℕ) (s : Memory.State) : Prop :=
  Fits w 16 ∧ readStride4Safe w (d.1.srcBase, d.2) s ∧
    let ew := (Memory.spec 0).clientResult s (readStride4 (d.1.srcBase, d.2))
    let s1 := (Memory.spec 0).clientState s (readStride4 (d.1.srcBase, d.2))
    writeStride4Safe w ((d.1.outBase, d.2), ⟨ew.u, ew.v, ew.wt, d.2⟩) s1

private theorem realizes_retagStep : Realizes .exact
    retagStep
    (appendWords (WordEncoding.encode (α := RetagEnv)) (WordEncoding.encode (α := ℕ)))
    (WordEncoding.encode (α := ℕ)) retagStepSafe (fun _ _ => 0) := by
  unfold retagStep
  realize [realizes_readStride4, realizes_writeStride4]
  · exact h.2.1
  · exact h.2.2

/-- Copy `a.count` stride-4 edges from `a.srcBase` into a newly allocated dirty block while
rewriting each edge's identifier to its array index `0 .. a.count - 1`, returning the allocated base
address. -/
def retagIndexedProg (a : RetagEdgesArgs) : Memory.Prog ℕ := do
  let outBase ← Memory.allocDirty (4 * a.count)
  let _ ← iterate retagStep ⟨a.srcBase, outBase⟩ a.count 0
  pure outBase

/-- Safety domain for `retagIndexedProg`. -/
@[expose] def retagIndexedProgSafe (w : ℕ) (a : RetagEdgesArgs) (s : Memory.State) : Prop :=
  Fits w 16 ∧ a.srcBase + 4 * a.count ≤ s.frontier ∧ Fits w (s.frontier + 4 * a.count)

private theorem retagIndexedProg_word_spec {w srcBase count : ℕ} {s : Memory.State}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hin_lt : srcBase + 4 * count ≤ s.frontier) (hfit : Fits w (s.frontier + 4 * count)) :
    iterationSafe retagStep retagStepSafe w ⟨srcBase, s.frontier⟩ count 0
      ⟨s.mem, s.frontier + 4 * count⟩ ∧
    Memory.FramedTriple w s (retagIndexedProg ⟨srcBase, count⟩) (8 * count + 1) ∅
      fun outBase s' =>
        outBase = s.frontier ∧ s'.frontier = s.frontier + 4 * count ∧ Memory.WellFormed w s' ∧
        ∀ i < count, stride4At outBase i
          ⟨s.mem (srcBase + 4 * i), s.mem (srcBase + 4 * i + 1),
            s.mem (srcBase + 4 * i + 2), i⟩ s'.mem := by
  refine allocDirty_stride4_loop_spec (ctx := fun ob => RetagEnv.mk srcBase ob)
    retagStep retagStepSafe
    (fun i => ⟨s.mem (srcBase + 4 * i), s.mem (srcBase + 4 * i + 1),
      s.mem (srcBase + 4 * i + 2), i⟩)
    hwf hfit fun k hk t htfr hwt hframe => ?_
  have hr := readStride4_spec (w := w) (base := srcBase) (idx := k) (s := t) (by rw [htfr]; omega)
  have hsrc_mem : ∀ q < 4, t.mem (srcBase + 4 * k + q) = s.mem (srcBase + 4 * k + q) :=
    fun q hq => hframe _ (by omega)
  have hfit_k1 : Fits w (k + 1) := hfit.of_le (by omega)
  let ewGoal : Stride4Words := ⟨s.mem (srcBase + 4 * k), s.mem (srcBase + 4 * k + 1),
    s.mem (srcBase + 4 * k + 2), k⟩
  have hft_s := stride4WriteAfterRead_ft (w := w) (cRead := 4) (outBase := s.frontier) (k := k)
    (frEnd := s.frontier + 4 * count) (adj := fun ew => ⟨ew.u, ew.v, ew.wt, k⟩) (ewGoal := ewGoal)
    hwt htfr (by omega) hr
    (by
      have h0 : t.mem (srcBase + 4 * k) = s.mem (srcBase + 4 * k) := by
        simpa using hsrc_mem 0 (by decide)
      dsimp only [ewGoal]
      rw [h0, hsrc_mem 1 (by decide), hsrc_mem 2 (by decide)])
    (hwf.mem_fits _) (hwf.mem_fits _) (hwf.mem_fits _) (hfit_k1.of_le (Nat.le_succ k))
  obtain ⟨hr_ew, hr_st⟩ := (framedTriple_iff_realization.mp hr).2.2.2
  have hmem_t := hwt.mem_fits
  refine ⟨⟨h16, ⟨h16, by dsimp only; rw [htfr]; omega⟩, ?_⟩, hft_s⟩
  dsimp only
  rw [hr_st, hr_ew]
  exact ⟨h16, hfit_k1, hmem_t _, hmem_t _, hmem_t _, hfit_k1.of_le (Nat.le_succ k),
    by dsimp only; rw [htfr]; omega⟩

/-- Uniform `Realizes .exact` certificate (`work = 0`) for `retagIndexedProg`. -/
theorem realizes_retagIndexedProg : Realizes .exact
    retagIndexedProg (WordEncoding.encode (α := RetagEdgesArgs)) (WordEncoding.encode (α := ℕ))
    retagIndexedProgSafe (fun _ _ => 0) := by
  have hraw : Realizes .exact retagIndexedProg (WordEncoding.encode (α := RetagEdgesArgs))
      (WordEncoding.encode (α := ℕ))
      (fun w a s => Fits w 16 ∧ Fits w (s.frontier + 4 * a.count) ∧
        iterationSafe retagStep retagStepSafe w ⟨a.srcBase, s.frontier⟩ a.count 0
          ⟨s.mem, s.frontier + 4 * a.count⟩)
      (fun _ _ => 0) := by
    unfold retagIndexedProg
    realize [realizes_retagStep]
    all_goals first
      | exact iterationSafe_imp h.2.2 (fun _ => rfl) (fun _ _ hs => hs)
      | (have h16 := h.1; have hf := h.2.1; have hfront := hmem.frontier_fits; fits)
  refine hraw.consequence (fun w a s _ hmem ⟨h16, hsrc, hfit⟩ => ?_) (fun _ _ => le_rfl)
  exact ⟨h16, hfit, (retagIndexedProg_word_spec h16 hmem hsrc hfit).1⟩

/-- Framed specification for `retagIndexedProg`: allocates `4 * es.length` dirty words at
`s.frontier`, copies `es` with edge IDs retagged `0 .. es.length - 1`, leaving all cells below
`s.frontier` untouched (`Modifies ∅`), in at most `8 * es.length + 1` memory operations. -/
theorem retagIndexedProg_spec {w n srcBase : ℕ} {es : List (IndexedEdge n)}
    {s : Memory.State} (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hin : HoldsIndexedEdges srcBase es s.mem)
    (hin_lt : srcBase + 4 * es.length ≤ s.frontier)
    (hfit : Fits w (s.frontier + 4 * es.length)) :
    Memory.FramedTriple w s (retagIndexedProg ⟨srcBase, es.length⟩) (8 * es.length + 1) ∅
      fun outBase s' =>
        outBase = s.frontier ∧
        s'.frontier = s.frontier + 4 * es.length ∧
        Memory.WellFormed w s' ∧
        HoldsIndexedEdges outBase (es.mapIdx fun i e => ⟨e.u, e.v, e.weight, i⟩) s'.mem := by
  refine (retagIndexedProg_word_spec h16 hwf hin_lt hfit).2.mono le_rfl
    fun outBase s' ⟨hout, hfr, hwf', hvals⟩ => ⟨hout, hfr, hwf', fun i hi => ?_⟩
  have hi_len : i < es.length := by simpa using hi
  obtain ⟨hu, hv, hw, _⟩ := hin i hi_len
  obtain ⟨h0, h1, h2, h3⟩ := hvals i hi_len
  simp only [List.getElem_mapIdx]
  exact ⟨h0.trans hu, h1.trans hv, h2.trans hw, h3⟩

/-! ### `copyStride4Prog` & `concatThreeProg` via `ArrayOps` / `RecordOps` -/

private def edgeToRecord {n : ℕ} (e : IndexedEdge n) : Fin 4 → ℕ
  | 0 => e.u.val
  | 1 => e.v.val
  | 2 => e.weight
  | 3 => e.id

private theorem holdsIndexedEdges_iff_holdsRecords {n : ℕ} (base : ℕ)
    (es : List (IndexedEdge n)) (mem : ℕ → ℕ) :
    HoldsIndexedEdges base es mem ↔ HoldsRecords 4 base (es.map edgeToRecord) mem := by
  constructor
  · intro h i hi j
    have hi' : i < es.length := by simpa using hi
    obtain ⟨hu, hv, hw, hid⟩ := h i hi'
    rcases j with ⟨_ | _ | _ | _ | k, hj⟩
    · simp only [List.getElem_map, edgeToRecord, Nat.add_zero]; exact hu
    · simp only [List.getElem_map, edgeToRecord]; exact hv
    · simp only [List.getElem_map, edgeToRecord]; exact hw
    · simp only [List.getElem_map, edgeToRecord]; exact hid
    · omega
  · intro h i hi
    have hi' : i < (es.map edgeToRecord).length := by simpa using hi
    have h0 := h i hi' 0
    have h1 := h i hi' 1
    have h2 := h i hi' 2
    have h3 := h i hi' 3
    simp only [List.getElem_map, edgeToRecord] at h0 h1 h2 h3
    exact ⟨h0, h1, h2, h3⟩

/-- Copy `a.count` stride-4 edges from `a.srcBase` to `a.dstBase` starting at edge offset
`a.dstOff` via `Memory.copy`, returning `a.dstOff + a.count`. -/
def copyStride4Prog (a : CopyStride4Args) : Memory.Prog ℕ := do
  Memory.copy a.srcBase (a.dstBase + 4 * a.dstOff) (4 * a.count)
  pure (a.dstOff + a.count)

/-- Safety domain for `copyStride4Prog`. -/
@[expose] def copyStride4ProgSafe (w : ℕ) (a : CopyStride4Args) (s : Memory.State) : Prop :=
  Fits w 16 ∧ a.srcBase + 4 * a.count ≤ s.frontier ∧
    a.dstBase + 4 * (a.dstOff + a.count) ≤ s.frontier

/-- Uniform `Realizes .exact` certificate (`work = 0`) for `copyStride4Prog`. -/
theorem realizes_copyStride4Prog : Realizes .exact
    copyStride4Prog (WordEncoding.encode (α := CopyStride4Args)) (WordEncoding.encode (α := ℕ))
    copyStride4ProgSafe (fun _ _ => 0) := by
  unfold copyStride4Prog
  realize [realizes_copy]
  all_goals
    obtain ⟨h16, hsrc, hdst⟩ := h
    have hfront := hmem.frontier_fits
    first | fits | omega

/-- Framed specification for `copyStride4Prog`: copies `srcEs` into `dstBase + 4 * dstOff`,
modifying only `Set.Ico (dstBase + 4 * dstOff) (dstBase + 4 * (dstOff + srcEs.length))`, in at
most `8 * srcEs.length` memory operations. -/
theorem copyStride4Prog_spec {w n srcBase dstBase dstOff : ℕ}
    {srcEs : List (IndexedEdge n)} {s : Memory.State}
    (hwf : Memory.WellFormed w s)
    (hin : HoldsIndexedEdges srcBase srcEs s.mem)
    (hin_lt : srcBase + 4 * srcEs.length ≤ s.frontier)
    (hdst_lt : dstBase + 4 * (dstOff + srcEs.length) ≤ s.frontier)
    (hdisj : srcBase + 4 * srcEs.length ≤ dstBase + 4 * dstOff ∨
      dstBase + 4 * (dstOff + srcEs.length) ≤ srcBase) :
    Memory.FramedTriple w s (copyStride4Prog ⟨srcBase, dstBase, dstOff, srcEs.length⟩)
      (8 * srcEs.length) (Set.Ico (dstBase + 4 * dstOff) (dstBase + 4 * (dstOff + srcEs.length)))
      fun res s' =>
        res = dstOff + srcEs.length ∧
        s'.frontier = s.frontier ∧
        Memory.WellFormed w s' ∧
        HoldsIndexedEdges (dstBase + 4 * dstOff) srcEs s'.mem := by
  have hrows := (holdsIndexedEdges_iff_holdsRecords srcBase srcEs s.mem).mp hin
  have hc := HoldsRecords.copy (w := w) (stride := 4) (src := srcBase)
    (dst := dstBase + 4 * dstOff) (rows := srcEs.map edgeToRecord) (s := s)
    (by simp only [List.length_map]; rcases hdisj with h | h <;> [left; right] <;> omega)
    (by simp only [List.length_map]; exact hin_lt)
    (by simp only [List.length_map]; omega)
    hwf hrows
  simp only [List.length_map] at hc
  have hprog : copyStride4Prog ⟨srcBase, dstBase, dstOff, srcEs.length⟩ =
      (Memory.copy srcBase (dstBase + 4 * dstOff) (4 * srcEs.length) >>= fun _ =>
        pure (dstOff + srcEs.length)) := rfl
  rw [hprog]
  refine (Memory.FramedTriple.bind_same (hc.mono le_rfl fun _ s' ⟨hfr, hwf', hrows'⟩ =>
    Memory.FramedTriple.pure (c := 0) (a := dstOff + srcEs.length)
      ⟨rfl, hfr, hwf', (holdsIndexedEdges_iff_holdsRecords _ _ _).mpr hrows'⟩)).frame_mono
    (fun x hx => by simp only [Set.mem_Ico] at hx ⊢; omega) |>.mono (by omega) fun _ _ h => h

/-- Concatenate three stride-4 edge arrays into a newly dirty-allocated `Block` via
`RecordOps.concatRecordsProg`. -/
def concatThreeProg (a : ConcatThreeArgs) : Memory.Prog Block :=
  concatRecordsProg ⟨4, a.base1, a.len1, a.base2, a.len2, a.base3, a.len3⟩

/-- Safety domain for `concatThreeProg`. -/
@[expose] def concatThreeProgSafe (w : ℕ) (a : ConcatThreeArgs) (s : Memory.State) : Prop :=
  Fits w 16 ∧ Fits w (s.frontier + 4 * (a.len1 + a.len2 + a.len3)) ∧
    a.base1 + 4 * a.len1 ≤ s.frontier ∧ a.base2 + 4 * a.len2 ≤ s.frontier ∧
    a.base3 + 4 * a.len3 ≤ s.frontier

/-- Uniform `Realizes .exact` certificate (`work = 0`) for `concatThreeProg`. -/
theorem realizes_concatThreeProg : Realizes .exact
    concatThreeProg (WordEncoding.encode (α := ConcatThreeArgs)) (WordEncoding.encode (α := Block))
    concatThreeProgSafe (fun _ _ => 0) := by
  unfold concatThreeProg
  realize [realizes_concatRecordsProg]
  all_goals first
    | exact h.2.2.1
    | exact h.2.2.2.1
    | exact h.2.2.2.2
    | (have h16 := h.1; have hfit := h.2.1; fits)

/-- Framed specification for `concatThreeProg`: concatenates `L1`, `L2`, and `L3` into a freshly
dirty-allocated stride-4 `Block` at `s.frontier`, leaving all cells below `s.frontier` untouched
(`Modifies ∅`), in at most `8 * (L1.length + L2.length + L3.length) + 1` memory operations. -/
theorem concatThreeProg_spec {w n base1 base2 base3 : ℕ}
    {L1 L2 L3 : List (IndexedEdge n)} {s : Memory.State}
    (hwf : Memory.WellFormed w s)
    (h1 : HoldsIndexedEdges base1 L1 s.mem) (h1_lt : base1 + 4 * L1.length ≤ s.frontier)
    (h2 : HoldsIndexedEdges base2 L2 s.mem) (h2_lt : base2 + 4 * L2.length ≤ s.frontier)
    (h3 : HoldsIndexedEdges base3 L3 s.mem) (h3_lt : base3 + 4 * L3.length ≤ s.frontier)
    (hfit : Fits w (s.frontier + 4 * (L1.length + L2.length + L3.length))) :
    let tot := L1.length + L2.length + L3.length
    Memory.FramedTriple w s
      (concatThreeProg ⟨base1, L1.length, base2, L2.length, base3, L3.length⟩)
      (8 * tot + 1) ∅ fun blk s' =>
        blk = ⟨s.frontier, 4 * tot⟩ ∧
        blk.Allocated s' ∧
        s'.frontier = s.frontier + 4 * tot ∧
        Memory.WellFormed w s' ∧
        HoldsIndexedEdges blk.base (L1 ++ L2 ++ L3) s'.mem := by
  have hR1 := (holdsIndexedEdges_iff_holdsRecords base1 L1 s.mem).mp h1
  have hR2 := (holdsIndexedEdges_iff_holdsRecords base2 L2 s.mem).mp h2
  have hR3 := (holdsIndexedEdges_iff_holdsRecords base3 L3 s.mem).mp h3
  have hc := concatRecordsProg_spec (w := w) (stride := 4)
    (srcA := base1) (srcB := base2) (srcC := base3)
    (rowsA := L1.map edgeToRecord) (rowsB := L2.map edgeToRecord)
    (rowsC := L3.map edgeToRecord) hwf
    hR1 (by simpa using h1_lt) hR2 (by simpa using h2_lt) hR3 (by simpa using h3_lt)
    (by simpa using hfit)
  simp only [List.length_map] at hc
  refine hc.mono (by omega) fun blk s' ⟨hblk, hal, hfr, hwf', hrows⟩ =>
    ⟨hblk, hal, hfr, hwf', ?_⟩
  rw [holdsIndexedEdges_iff_holdsRecords, List.map_append, List.map_append]
  exact hrows

/-! ### `liftEdgesProg`: Lift Local Stride-4 Edges to Global Vertices -/

private def liftEdgeRead (d : LiftEdgesEnv × ℕ) : Memory.Prog Stride4Words := do
  let u ← Memory.read (d.1.srcBase + 4 * d.2)
  let v ← Memory.read (d.1.srcBase + 4 * d.2 + 1)
  let u' ← Memory.read (d.1.liftBase + u)
  let v' ← Memory.read (d.1.liftBase + v)
  let wt ← Memory.read (d.1.srcBase + 4 * d.2 + 2)
  let eid ← Memory.read (d.1.srcBase + 4 * d.2 + 3)
  pure ⟨u', v', wt, eid⟩

private def liftEdgeReadSafe (w : ℕ) (d : LiftEdgesEnv × ℕ) (s : Memory.State) : Prop :=
  Fits w 16 ∧ d.1.srcBase + 4 * d.2 + 3 < s.frontier ∧
    let u := s.mem (d.1.srcBase + 4 * d.2)
    let v := s.mem (d.1.srcBase + 4 * d.2 + 1)
    d.1.liftBase + u < s.frontier ∧ d.1.liftBase + v < s.frontier

private theorem realizes_liftEdgeRead_history : Realizes .exact
    liftEdgeRead
    (appendWords (WordEncoding.encode (α := LiftEdgesEnv)) (WordEncoding.encode (α := ℕ)))
    (WordEncoding.encode (α := Stride4Words))
    (fun w d s => liftEdgeReadSafe w d s ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (liftEdgeRead d)))
    (fun _ _ => 0) := by
  unfold liftEdgeRead
  realize
  all_goals
    obtain ⟨⟨h16, h1, h2, h3⟩, hv⟩ := h
    have hfront := hmem.frontier_fits
    dsimp only [StateTransitionSpec.clientHistory] at hv
    simp_all only [StateTransitionSpec.runClient_lift_bind',
      StateTransitionSpec.validHistory_cons, StateTransitionSpec.stepFn, Memory.read,
      Memory.step_read, Memory.valid]
  all_goals fits

private theorem realizes_liftEdgeRead : Realizes .exact
    liftEdgeRead
    (appendWords (WordEncoding.encode (α := LiftEdgesEnv)) (WordEncoding.encode (α := ℕ)))
    (WordEncoding.encode (α := Stride4Words)) liftEdgeReadSafe (fun _ _ => 0) :=
  realizes_liftEdgeRead_history.consequence_valid fun _ _ _ _ _ hv h => ⟨h, hv⟩

private theorem liftEdgeRead_spec {w srcBase liftBase dstBase idx : ℕ} {s : Memory.State}
    (hlt : srcBase + 4 * idx + 3 < s.frontier)
    (hu_lt : liftBase + s.mem (srcBase + 4 * idx) < s.frontier)
    (hv_lt : liftBase + s.mem (srcBase + 4 * idx + 1) < s.frontier) :
    let e : LiftEdgesEnv := ⟨srcBase, liftBase, dstBase⟩
    Memory.FramedTriple w s (liftEdgeRead (e, idx)) 6 ∅ fun res s' =>
      res = ⟨s.mem (liftBase + s.mem (srcBase + 4 * idx)),
        s.mem (liftBase + s.mem (srcBase + 4 * idx + 1)),
        s.mem (srcBase + 4 * idx + 2), s.mem (srcBase + 4 * idx + 3)⟩ ∧ s' = s := by
  dsimp only [liftEdgeRead]
  exact Memory.FramedTriple.read_bind (by omega) <|
    Memory.FramedTriple.read_bind (by omega) <|
      Memory.FramedTriple.read_bind hu_lt <|
        Memory.FramedTriple.read_bind hv_lt <|
          Memory.FramedTriple.read_bind (by omega) <|
            Memory.FramedTriple.read_bind hlt <|
              Memory.FramedTriple.pure ⟨rfl, rfl⟩

private def liftEdgeStep (d : LiftEdgesEnv × (ℕ × ℕ)) : Memory.Prog (ℕ × ℕ) := do
  let ew ← liftEdgeRead (d.1, d.2.1)
  let nextOff ← writeStride4 ((d.1.dstBase, d.2.2), ew)
  pure (d.2.1 + 1, nextOff)

private def liftEdgeStepSafe (w : ℕ) (d : LiftEdgesEnv × (ℕ × ℕ)) (s : Memory.State) : Prop :=
  Fits w 16 ∧ Fits w (d.2.1 + 1) ∧ liftEdgeReadSafe w (d.1, d.2.1) s ∧
    let ew := (Memory.spec 0).clientResult s (liftEdgeRead (d.1, d.2.1))
    let s1 := (Memory.spec 0).clientState s (liftEdgeRead (d.1, d.2.1))
    writeStride4Safe w ((d.1.dstBase, d.2.2), ew) s1

private theorem realizes_liftEdgeStep : Realizes .exact
    liftEdgeStep
    (appendWords (WordEncoding.encode (α := LiftEdgesEnv)) (WordEncoding.encode (α := ℕ × ℕ)))
    (WordEncoding.encode (α := ℕ × ℕ)) liftEdgeStepSafe (fun _ _ => 0) := by
  unfold liftEdgeStep
  realize [realizes_liftEdgeRead, realizes_writeStride4]
  all_goals first
    | exact h.2.2.1
    | exact h.2.2.2
    | (have h16 := h.1; have hfit1 := h.2.1; fits)

/-- Lift `a.count` local stride-4 edges at `a.srcBase` through vertex table `a.liftBase` into
`a.dstBase` starting at offset `a.dstOff`, returning `a.dstOff + a.count`. -/
def liftEdgesProg (a : LiftEdgesArgs) : Memory.Prog ℕ := do
  let st ← iterate liftEdgeStep ⟨a.srcBase, a.liftBase, a.dstBase⟩ a.count (0, a.dstOff)
  pure st.2

/-- Safety domain for `liftEdgesProg`. -/
@[expose] def liftEdgesProgSafe (w : ℕ) (a : LiftEdgesArgs) (s : Memory.State) : Prop :=
  Fits w 16 ∧ a.srcBase + 4 * a.count ≤ s.frontier ∧
    (a.srcBase + 4 * a.count ≤ a.dstBase + 4 * a.dstOff ∨
      a.dstBase + 4 * (a.dstOff + a.count) ≤ a.srcBase) ∧
    (∀ k < a.count,
      a.liftBase + s.mem (a.srcBase + 4 * k) < s.frontier ∧
      a.liftBase + s.mem (a.srcBase + 4 * k + 1) < s.frontier) ∧
    a.dstBase + 4 * (a.dstOff + a.count) ≤ s.frontier

private theorem liftEdgesProg_word_spec {w srcBase liftBase dstBase dstOff count : ℕ}
    {s : Memory.State} (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hsrc_lt : srcBase + 4 * count ≤ s.frontier)
    (hdisj_e : srcBase + 4 * count ≤ dstBase + 4 * dstOff ∨
      dstBase + 4 * (dstOff + count) ≤ srcBase)
    (hlb : ∀ k < count, liftBase + s.mem (srcBase + 4 * k) < s.frontier ∧
      liftBase + s.mem (srcBase + 4 * k + 1) < s.frontier)
    (hdst_lt : dstBase + 4 * (dstOff + count) ≤ s.frontier) :
    let e : LiftEdgesEnv := ⟨srcBase, liftBase, dstBase⟩
    let S := Set.Ico (dstBase + 4 * dstOff) (dstBase + 4 * (dstOff + count))
    iterationSafe liftEdgeStep liftEdgeStepSafe w e count (0, dstOff) s ∧
    Memory.FramedTriple w s (liftEdgesProg ⟨srcBase, liftBase, dstBase, dstOff, count⟩)
      (10 * count) S fun res s' =>
        res = dstOff + count ∧ s'.frontier = s.frontier ∧ Memory.WellFormed w s' ∧
        ((∀ k < count, liftBase + s.mem (srcBase + 4 * k) ∉ S ∧
          liftBase + s.mem (srcBase + 4 * k + 1) ∉ S) →
          ∀ i < count, stride4At (dstBase + 4 * dstOff) i
            ⟨s.mem (liftBase + s.mem (srcBase + 4 * i)),
              s.mem (liftBase + s.mem (srcBase + 4 * i + 1)),
              s.mem (srcBase + 4 * i + 2), s.mem (srcBase + 4 * i + 3)⟩ s'.mem) := by
  let e : LiftEdgesEnv := ⟨srcBase, liftBase, dstBase⟩
  let S : Set ℕ := Set.Ico (dstBase + 4 * dstOff) (dstBase + 4 * (dstOff + count))
  let inv (k : ℕ) (a : ℕ × ℕ) (t : Memory.State) : Prop :=
    a = (k, dstOff + k) ∧ t.frontier = s.frontier ∧ Memory.WellFormed w t ∧
    (∀ x, x ∉ S → t.mem x = s.mem x) ∧
    ((∀ j < count, liftBase + s.mem (srcBase + 4 * j) ∉ S ∧
      liftBase + s.mem (srcBase + 4 * j + 1) ∉ S) →
      ∀ i < k, stride4At (dstBase + 4 * dstOff) i
        ⟨s.mem (liftBase + s.mem (srcBase + 4 * i)),
          s.mem (liftBase + s.mem (srcBase + 4 * i + 1)),
          s.mem (srcBase + 4 * i + 2), s.mem (srcBase + 4 * i + 3)⟩ t.mem)
  have hstep : ∀ k < count, ∀ a t, inv k a t →
      liftEdgeStepSafe w (e, a) t ∧
      (Memory.spec w).ValidHistory t ((Memory.spec w).clientHistory t (liftEdgeStep (e, a))) ∧
      let a' := (Memory.spec 0).clientResult t (liftEdgeStep (e, a))
      let t' := (Memory.spec 0).clientState t (liftEdgeStep (e, a))
      memoryCost (liftEdgeStep (e, a)) t + 0 ≤ 0 + 10 ∧
      Memory.Modifies S t t' ∧
      inv (k + 1) a' t' := by
    intro k hk a t ⟨ha, htfr, hwt, hframe, hpref⟩
    subst a
    have hsrc_mem : ∀ q < 4, t.mem (srcBase + 4 * k + q) = s.mem (srcBase + 4 * k + q) :=
      fun q hq => hframe _ (by simp only [S, Set.mem_Ico]; rcases hdisj_e with hd | hd <;> omega)
    have hlu_eq : t.mem (srcBase + 4 * k) = s.mem (srcBase + 4 * k) := by
      simpa using hsrc_mem 0 (by decide)
    have hlv_eq : t.mem (srcBase + 4 * k + 1) = s.mem (srcBase + 4 * k + 1) :=
      hsrc_mem 1 (by decide)
    have hu_lt : liftBase + t.mem (srcBase + 4 * k) < t.frontier := by
      rw [hlu_eq, htfr]; exact (hlb k hk).1
    have hv_lt : liftBase + t.mem (srcBase + 4 * k + 1) < t.frontier := by
      rw [hlv_eq, htfr]; exact (hlb k hk).2
    have hr := liftEdgeRead_spec (w := w) (srcBase := srcBase) (liftBase := liftBase)
      (dstBase := dstBase) (idx := k) (s := t) (by omega) hu_lt hv_lt
    have hmem_t := hwt.mem_fits
    have hfit_k1 : Fits w (k + 1) := hwf.frontier_fits.of_le (by omega)
    have hfit_ok1 : Fits w (dstOff + k + 1) := hwf.frontier_fits.of_le (by omega)
    let ew_t : Stride4Words :=
      ⟨t.mem (liftBase + t.mem (srcBase + 4 * k)),
        t.mem (liftBase + t.mem (srcBase + 4 * k + 1)),
        t.mem (srcBase + 4 * k + 2), t.mem (srcBase + 4 * k + 3)⟩
    let Sk := Set.Ico (dstBase + 4 * (dstOff + k)) (dstBase + 4 * (dstOff + k) + 4)
    have hft_s : Memory.FramedTriple w t (liftEdgeStep (e, (k, dstOff + k))) 10 Sk fun a' t' =>
        a' = (k + 1, dstOff + (k + 1)) ∧ t'.frontier = s.frontier ∧ Memory.WellFormed w t' ∧
        stride4At dstBase (dstOff + k) ew_t t'.mem := by
      have hsub : Memory.FramedTriple w t (liftEdgeRead (e, k)) 6 Sk fun ew t₁ =>
          Memory.FramedTriple w t₁ (writeStride4 ((dstBase, dstOff + k), ew) >>= fun nextOff =>
            pure (k + 1, nextOff)) 4 Sk fun a' t' =>
              a' = (k + 1, dstOff + (k + 1)) ∧ t'.frontier = s.frontier ∧ Memory.WellFormed w t' ∧
              stride4At dstBase (dstOff + k) ew_t t'.mem := by
        refine (hr.frame_mono (Set.empty_subset Sk)).mono le_rfl fun ew t₁ ⟨hew, ht₁⟩ => ?_
        subst ht₁; rw [hew]
        have hw := writeStride4_spec (w := w) (dst := dstBase) (idx := dstOff + k) (ew := ew_t)
          hwt (hmem_t _) (hmem_t _) (hmem_t _) (hmem_t _) (by rw [htfr]; omega)
        exact ((hw.mono le_rfl fun nextOff t' ⟨hnext, hfr', hwt', hstr⟩ =>
          Memory.FramedTriple.pure (c := 0) (a := (k + 1, nextOff))
            ⟨by rw [hnext, Nat.add_assoc], hfr'.trans htfr, hwt', hstr⟩).bind_same).mono
          (Nat.add_zero 4).le fun _ _ h => h
      exact hsub.bind_same.mono (by omega) fun _ _ h => h
    obtain ⟨hv_s, hc_s, hmod_s, hres_s, ht'_fr, hwt', hstr_k⟩ :=
      framedTriple_iff_realization.mp hft_s
    have hr_spec := framedTriple_iff_realization.mp hr
    obtain ⟨hr_ew, hr_st⟩ := hr_spec.2.2.2
    have hsafe_s : liftEdgeStepSafe w (e, (k, dstOff + k)) t := by
      refine ⟨h16, hfit_k1, ⟨h16, by rw [htfr]; dsimp only [e]; omega, hu_lt, hv_lt⟩, ?_⟩
      rw [hr_st, hr_ew]
      exact ⟨h16, hfit_ok1, hmem_t _, hmem_t _, hmem_t _, hmem_t _,
        by rw [htfr]; dsimp only [e]; omega⟩
    have hmod_S : Memory.Modifies S t
        ((Memory.spec 0).clientState t (liftEdgeStep (e, (k, dstOff + k)))) :=
      hmod_s.mono fun x hx => by simp only [Sk, S, Set.mem_Ico] at hx ⊢; omega
    have hmem_keep : ∀ x, x ∉ S →
        ((Memory.spec 0).clientState t (liftEdgeStep (e, (k, dstOff + k)))).mem x = t.mem x :=
      fun x hx => hft_s.mem_eq_of_frontier_eq (ht'_fr.trans htfr.symm) x fun hxk => by
        simp only [Sk, S, Set.mem_Ico] at hx hxk; omega
    refine ⟨hsafe_s, hv_s, by omega, hmod_S, ?_⟩
    dsimp only [inv]
    refine ⟨hres_s, ht'_fr, hwt', fun x hx => (hmem_keep x hx).trans (hframe x hx),
      fun hl i hi => ?_⟩
    by_cases hik : i = k
    · subst i
      have ha0 : dstBase + 4 * (dstOff + k) = dstBase + 4 * dstOff + 4 * k := by omega
      have hl0 : t.mem (liftBase + s.mem (srcBase + 4 * k)) =
          s.mem (liftBase + s.mem (srcBase + 4 * k)) := hframe _ (hl k hk).1
      have hl1 : t.mem (liftBase + s.mem (srcBase + 4 * k + 1)) =
          s.mem (liftBase + s.mem (srcBase + 4 * k + 1)) := hframe _ (hl k hk).2
      dsimp only [stride4At, ew_t] at hstr_k ⊢
      rw [ha0, hlu_eq, hlv_eq, hl0, hl1, hsrc_mem 2 (by decide),
        hsrc_mem 3 (by decide)] at hstr_k
      exact hstr_k
    · exact stride4At_congr (fun q hq => hft_s.mem_eq_of_frontier_eq (ht'_fr.trans htfr.symm) _
        (by simp only [Sk, Set.mem_Ico]; omega)) (hpref hl i (by omega))
  obtain ⟨hsafe_it, hv_it, hm_it, hmod_it, hres_it, hfr_it, hwf_it, _, hvals_it⟩ :=
    iterate_potential_spec liftEdgeStep liftEdgeStepSafe w e 10 count inv (fun _ _ _ => 0)
      S hstep (0, dstOff) s
      ⟨rfl, rfl, hwf, fun _ _ => rfl, fun _ _ h => absurd h (Nat.not_lt_zero _)⟩
  exact ⟨hsafe_it, iterate_bind_snd_ft hv_it (by simpa using hm_it) hmod_it
    ⟨congrArg Prod.snd hres_it, hfr_it, hwf_it, hvals_it⟩⟩

/-- Uniform `Realizes .exact` certificate (`work = 0`) for `liftEdgesProg`. -/
theorem realizes_liftEdgesProg : Realizes .exact
    liftEdgesProg (WordEncoding.encode (α := LiftEdgesArgs)) (WordEncoding.encode (α := ℕ))
    liftEdgesProgSafe (fun _ _ => 0) := by
  have hraw : Realizes .exact
      (fun a : LiftEdgesArgs => do
        let st ← iterate liftEdgeStep ⟨a.srcBase, a.liftBase, a.dstBase⟩ a.count (0, a.dstOff)
        pure st.2)
      (WordEncoding.encode (α := LiftEdgesArgs)) (WordEncoding.encode (α := ℕ))
      (fun w a s => Fits w 16 ∧
        iterationSafe liftEdgeStep liftEdgeStepSafe w ⟨a.srcBase, a.liftBase, a.dstBase⟩ a.count
          (0, a.dstOff) s)
      (fun _ _ => 0) := by
    realize [realizes_liftEdgeStep]
    exact iterationSafe_imp h.2 (fun _ => rfl) (fun _ _ hs => hs)
  refine hraw.consequence (fun w a s _ hmem ⟨h16, hsrc, hde, hlb, hdst⟩ => ?_)
    (fun _ _ => le_rfl)
  exact ⟨h16, (liftEdgesProg_word_spec h16 hmem hsrc hde hlb hdst).1⟩

/-- Framed specification for `liftEdgesProg`: writes `C` with endpoints lifted through `lift`
into `dstBase + 4 * dstOff`, modifying only
`Set.Ico (dstBase + 4 * dstOff) (dstBase + 4 * (dstOff + C.length))`, in at most `10 * C.length`
memory operations. -/
theorem liftEdgesProg_spec {w nLoc nGlob srcBase liftBase dstBase dstOff : ℕ}
    {C : List (IndexedEdge nLoc)} {lift : Fin nLoc → Fin nGlob} {s : Memory.State}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hin : HoldsIndexedEdges srcBase C s.mem)
    (hin_lt : srcBase + 4 * C.length ≤ s.frontier)
    (hlift : ∀ k : Fin nLoc, s.mem (liftBase + k.val) = (lift k).val)
    (hlift_lt : liftBase + nLoc ≤ s.frontier)
    (hdst_lt : dstBase + 4 * (dstOff + C.length) ≤ s.frontier)
    (hdisj_e : srcBase + 4 * C.length ≤ dstBase + 4 * dstOff ∨
      dstBase + 4 * (dstOff + C.length) ≤ srcBase)
    (hdisj_l : liftBase + nLoc ≤ dstBase + 4 * dstOff ∨
      dstBase + 4 * (dstOff + C.length) ≤ liftBase) :
    Memory.FramedTriple w s
      (liftEdgesProg ⟨srcBase, liftBase, dstBase, dstOff, C.length⟩)
      (10 * C.length) (Set.Ico (dstBase + 4 * dstOff) (dstBase + 4 * (dstOff + C.length)))
      fun res s' =>
        res = dstOff + C.length ∧
        s'.frontier = s.frontier ∧
        Memory.WellFormed w s' ∧
        HoldsIndexedEdges (dstBase + 4 * dstOff)
          (C.map fun x => (⟨lift x.u, lift x.v, x.weight, x.id⟩ : IndexedEdge nGlob)) s'.mem := by
  have hlb : ∀ k < C.length, liftBase + s.mem (srcBase + 4 * k) < s.frontier ∧
      liftBase + s.mem (srcBase + 4 * k + 1) < s.frontier := fun k hk => by
    obtain ⟨hu, hv, _, _⟩ := hin k hk
    rw [hu, hv]
    exact ⟨by have := C[k].u.isLt; omega, by have := C[k].v.isLt; omega⟩
  have hnl : ∀ k < C.length,
      liftBase + s.mem (srcBase + 4 * k) ∉
        Set.Ico (dstBase + 4 * dstOff) (dstBase + 4 * (dstOff + C.length)) ∧
      liftBase + s.mem (srcBase + 4 * k + 1) ∉
        Set.Ico (dstBase + 4 * dstOff) (dstBase + 4 * (dstOff + C.length)) := fun k hk => by
    obtain ⟨hu, hv, _, _⟩ := hin k hk
    rw [hu, hv]
    simp only [Set.mem_Ico]
    have h1 := C[k].u.isLt
    have h2 := C[k].v.isLt
    rcases hdisj_l with hdl | hdr <;> exact ⟨by omega, by omega⟩
  refine (liftEdgesProg_word_spec h16 hwf hin_lt hdisj_e hlb hdst_lt).2.mono le_rfl
    fun res s' ⟨hres, hfr, hwf', hvals⟩ => ⟨hres, hfr, hwf', fun i hi => ?_⟩
  have hi' : i < C.length := by simpa using hi
  obtain ⟨hu, hv, hw, hid⟩ := hin i hi'
  obtain ⟨h0, h1, h2, h3⟩ := hvals hnl i hi'
  simp only [List.getElem_map]
  rw [hu, hlift C[i].u] at h0
  rw [hv, hlift C[i].v] at h1
  exact ⟨h0, h1, h2.trans hw, h3.trans hid⟩

/-! ### `liftHRemProg`: Gather Selected `H_rem` Edges by Original Identifier -/

private def liftHRemRead (d : (ℕ × ℕ) × ℕ) : Memory.Prog Stride4Words := do
  let idx ← Memory.read (d.1.2 + 4 * d.2 + 3)
  readStride4 (d.1.1, idx)

private def liftHRemReadSafe (w : ℕ) (d : (ℕ × ℕ) × ℕ) (s : Memory.State) : Prop :=
  Fits w 16 ∧ d.1.2 + 4 * d.2 + 3 < s.frontier ∧
    readStride4Safe w (d.1.1, s.mem (d.1.2 + 4 * d.2 + 3)) s

private theorem realizes_liftHRemRead : Realizes .exact
    liftHRemRead
    (appendWords (WordEncoding.encode (α := ℕ × ℕ)) (WordEncoding.encode (α := ℕ)))
    (WordEncoding.encode (α := Stride4Words)) liftHRemReadSafe (fun _ _ => 0) := by
  unfold liftHRemRead
  realize [realizes_readStride4]
  all_goals first
    | exact h.2.2
    | (have h16 := h.1; have hlt := h.2.1; have hfront := hmem.frontier_fits; fits)

private theorem liftHRemRead_spec {w hRemBase msfBase idx : ℕ} {s : Memory.State}
    (hmsf_lt : msfBase + 4 * idx + 3 < s.frontier)
    (hrem_lt : hRemBase + 4 * s.mem (msfBase + 4 * idx + 3) + 3 < s.frontier) :
    let eIdx := s.mem (msfBase + 4 * idx + 3)
    Memory.FramedTriple w s (liftHRemRead ((hRemBase, msfBase), idx)) 5 ∅ fun res s' =>
      res = ⟨s.mem (hRemBase + 4 * eIdx), s.mem (hRemBase + 4 * eIdx + 1),
        s.mem (hRemBase + 4 * eIdx + 2), s.mem (hRemBase + 4 * eIdx + 3)⟩ ∧ s' = s :=
  Memory.FramedTriple.read_bind hmsf_lt (readStride4_spec hrem_lt)

private def liftHRemStep (d : LiftHRemEnv × ℕ) : Memory.Prog ℕ := do
  let ew ← liftHRemRead ((d.1.hRemBase, d.1.msfBase), d.2)
  writeStride4 ((d.1.outBase, d.2), ew)

private def liftHRemStepSafe (w : ℕ) (d : LiftHRemEnv × ℕ) (s : Memory.State) : Prop :=
  Fits w 16 ∧ Fits w (d.2 + 1) ∧ liftHRemReadSafe w ((d.1.hRemBase, d.1.msfBase), d.2) s ∧
    let ew := (Memory.spec 0).clientResult s (liftHRemRead ((d.1.hRemBase, d.1.msfBase), d.2))
    let s1 := (Memory.spec 0).clientState s (liftHRemRead ((d.1.hRemBase, d.1.msfBase), d.2))
    writeStride4Safe w ((d.1.outBase, d.2), ew) s1

private theorem realizes_liftHRemStep : Realizes .exact
    liftHRemStep
    (appendWords (WordEncoding.encode (α := LiftHRemEnv)) (WordEncoding.encode (α := ℕ)))
    (WordEncoding.encode (α := ℕ)) liftHRemStepSafe (fun _ _ => 0) := by
  unfold liftHRemStep
  realize [realizes_liftHRemRead, realizes_writeStride4]
  · exact h.2.2.1
  · exact h.2.2.2

/-- Gather `a.count` edges from `a.hRemBase` indexed by the `.id` fields of stride-4 records at
`a.msfBase`, returning the base address of a newly allocated dirty stride-4 edge array. -/
def liftHRemProg (a : LiftHRemArgs) : Memory.Prog ℕ := do
  let outBase ← Memory.allocDirty (4 * a.count)
  let _ ← iterate liftHRemStep ⟨a.hRemBase, a.msfBase, outBase⟩ a.count 0
  pure outBase

/-- Safety domain for `liftHRemProg`. -/
@[expose] def liftHRemProgSafe (w : ℕ) (a : LiftHRemArgs) (s : Memory.State) : Prop :=
  Fits w 16 ∧ a.msfBase + 4 * a.count ≤ s.frontier ∧
    (∀ k < a.count, a.hRemBase + 4 * s.mem (a.msfBase + 4 * k + 3) + 4 ≤ s.frontier) ∧
    Fits w (s.frontier + 4 * a.count)

private theorem liftHRemProg_word_spec {w hRemBase msfBase count : ℕ} {s : Memory.State}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hmsf_lt : msfBase + 4 * count ≤ s.frontier)
    (hids_lt : ∀ k < count, hRemBase + 4 * s.mem (msfBase + 4 * k + 3) + 4 ≤ s.frontier)
    (hfit : Fits w (s.frontier + 4 * count)) :
    iterationSafe liftHRemStep liftHRemStepSafe w ⟨hRemBase, msfBase, s.frontier⟩ count 0
      ⟨s.mem, s.frontier + 4 * count⟩ ∧
    Memory.FramedTriple w s (liftHRemProg ⟨hRemBase, msfBase, count⟩) (9 * count + 1) ∅
      fun outBase s' =>
        outBase = s.frontier ∧ s'.frontier = s.frontier + 4 * count ∧ Memory.WellFormed w s' ∧
        ∀ i < count,
          let eIdx := s.mem (msfBase + 4 * i + 3)
          stride4At outBase i ⟨s.mem (hRemBase + 4 * eIdx), s.mem (hRemBase + 4 * eIdx + 1),
            s.mem (hRemBase + 4 * eIdx + 2), s.mem (hRemBase + 4 * eIdx + 3)⟩ s'.mem := by
  refine allocDirty_stride4_loop_spec (ctx := fun ob => LiftHRemEnv.mk hRemBase msfBase ob)
    liftHRemStep liftHRemStepSafe
    (fun i =>
      let eIdx := s.mem (msfBase + 4 * i + 3)
      ⟨s.mem (hRemBase + 4 * eIdx), s.mem (hRemBase + 4 * eIdx + 1),
        s.mem (hRemBase + 4 * eIdx + 2), s.mem (hRemBase + 4 * eIdx + 3)⟩)
    hwf hfit fun k hk t htfr hwt hframe => ?_
  have hidx_eq : t.mem (msfBase + 4 * k + 3) = s.mem (msfBase + 4 * k + 3) :=
    hframe _ (by omega)
  have hrem_bound := hids_lt k hk
  have hrem_mem : ∀ q < 4, t.mem (hRemBase + 4 * s.mem (msfBase + 4 * k + 3) + q) =
      s.mem (hRemBase + 4 * s.mem (msfBase + 4 * k + 3) + q) := fun q hq =>
    hframe _ (by omega)
  have hr := liftHRemRead_spec (w := w) (hRemBase := hRemBase) (msfBase := msfBase)
    (idx := k) (s := t) (by rw [htfr]; omega) (by rw [htfr, hidx_eq]; omega)
  have hfit_k1 : Fits w (k + 1) := hfit.of_le (by omega)
  let ewGoal : Stride4Words :=
    ⟨s.mem (hRemBase + 4 * s.mem (msfBase + 4 * k + 3)),
      s.mem (hRemBase + 4 * s.mem (msfBase + 4 * k + 3) + 1),
      s.mem (hRemBase + 4 * s.mem (msfBase + 4 * k + 3) + 2),
      s.mem (hRemBase + 4 * s.mem (msfBase + 4 * k + 3) + 3)⟩
  have hft_s := stride4WriteAfterRead_ft (w := w) (cRead := 5) (outBase := s.frontier) (k := k)
    (frEnd := s.frontier + 4 * count) (adj := id) (ewGoal := ewGoal)
    hwt htfr (by omega) hr
    (by
      have hrem0 : t.mem (hRemBase + 4 * s.mem (msfBase + 4 * k + 3)) =
          s.mem (hRemBase + 4 * s.mem (msfBase + 4 * k + 3)) := by
        simpa using hrem_mem 0 (by decide)
      dsimp only [id, ewGoal]
      rw [hidx_eq, hrem0, hrem_mem 1 (by decide), hrem_mem 2 (by decide), hrem_mem 3 (by decide)])
    (hwf.mem_fits _) (hwf.mem_fits _) (hwf.mem_fits _) (hwf.mem_fits _)
  obtain ⟨hr_ew, hr_st⟩ := (framedTriple_iff_realization.mp hr).2.2.2
  have hmem_t := hwt.mem_fits
  refine ⟨⟨h16, hfit_k1, ⟨h16, by dsimp only; rw [htfr]; omega,
    ⟨h16, by dsimp only; rw [htfr, hidx_eq]; omega⟩⟩, ?_⟩, hft_s⟩
  dsimp only
  rw [hr_st, hr_ew]
  exact ⟨h16, hfit_k1, hmem_t _, hmem_t _, hmem_t _, hmem_t _, by dsimp only; rw [htfr]; omega⟩

/-- Uniform `Realizes .exact` certificate (`work = 0`) for `liftHRemProg`. -/
theorem realizes_liftHRemProg : Realizes .exact
    liftHRemProg (WordEncoding.encode (α := LiftHRemArgs)) (WordEncoding.encode (α := ℕ))
    liftHRemProgSafe (fun _ _ => 0) := by
  have hraw : Realizes .exact liftHRemProg (WordEncoding.encode (α := LiftHRemArgs))
      (WordEncoding.encode (α := ℕ))
      (fun w a s => Fits w 16 ∧ Fits w (s.frontier + 4 * a.count) ∧
        iterationSafe liftHRemStep liftHRemStepSafe w ⟨a.hRemBase, a.msfBase, s.frontier⟩ a.count
          0 ⟨s.mem, s.frontier + 4 * a.count⟩)
      (fun _ _ => 0) := by
    unfold liftHRemProg
    realize [realizes_liftHRemStep]
    all_goals first
      | exact iterationSafe_imp h.2.2 (fun _ => rfl) (fun _ _ hs => hs)
      | (have h16 := h.1; have hf := h.2.1; have hfront := hmem.frontier_fits; fits)
  refine hraw.consequence (fun w a s _ hmem ⟨h16, hmsf, hids, hfit⟩ => ?_) (fun _ _ => le_rfl)
  exact ⟨h16, hfit, (liftHRemProg_word_spec h16 hmem hmsf hids hfit).1⟩

/-- Framed specification for `liftHRemProg`: allocates `4 * H_msf.length` dirty words at
`s.frontier` and gathers `H_rem[e.id]` for each `e ∈ H_msf`, leaving all cells below `s.frontier`
untouched (`Modifies ∅`), in at most `9 * H_msf.length + 1` memory operations. -/
theorem liftHRemProg_spec {w n nA hRemBase msfBase : ℕ}
    {H_rem : List (IndexedEdge n)} {H_msf : List (IndexedEdge nA)} {s : Memory.State}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hrem : HoldsIndexedEdges hRemBase H_rem s.mem)
    (hrem_lt : hRemBase + 4 * H_rem.length ≤ s.frontier)
    (hmsf : HoldsIndexedEdges msfBase H_msf s.mem)
    (hmsf_lt : msfBase + 4 * H_msf.length ≤ s.frontier)
    (hids : ∀ e ∈ H_msf, e.id < H_rem.length)
    (hfit : Fits w (s.frontier + 4 * H_msf.length)) :
    Memory.FramedTriple w s (liftHRemProg ⟨hRemBase, msfBase, H_msf.length⟩)
      (9 * H_msf.length + 1) ∅ fun outBase s' =>
        outBase = s.frontier ∧
        s'.frontier = s.frontier + 4 * H_msf.length ∧
        Memory.WellFormed w s' ∧
        HoldsIndexedEdges outBase
          (H_msf.pmap (fun e he => H_rem[e.id]'(hids e he)) (fun _ he => he)) s'.mem := by
  have hids_lt : ∀ k < H_msf.length,
      hRemBase + 4 * s.mem (msfBase + 4 * k + 3) + 4 ≤ s.frontier := fun k hk => by
    have hid_eq := (hmsf k hk).2.2.2
    have hlt := hids H_msf[k] (List.getElem_mem hk)
    omega
  refine (liftHRemProg_word_spec h16 hwf hmsf_lt hids_lt hfit).2.mono le_rfl
    fun outBase s' ⟨hout, hfr, hwf', hvals⟩ => ⟨hout, hfr, hwf', fun i hi => ?_⟩
  have hi_len : i < H_msf.length := by simpa using hi
  have hid_eq := (hmsf i hi_len).2.2.2
  have hlt := hids H_msf[i] (List.getElem_mem hi_len)
  obtain ⟨hu, hv, hw, hid⟩ := hrem H_msf[i].id hlt
  obtain ⟨h0, h1, h2, h3⟩ := hvals i hi_len
  simp only [List.getElem_pmap]
  rw [hid_eq] at h0 h1 h2 h3
  exact ⟨h0.trans hu, h1.trans hv, h2.trans hw, h3.trans hid⟩

end Cslib.Algorithms.WordRAM.MinimumSpanningForest
