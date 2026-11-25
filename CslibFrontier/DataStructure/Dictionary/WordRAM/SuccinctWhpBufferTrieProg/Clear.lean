/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpSwarProg
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpBufferTrieProg.Rt
import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpBufferTrieProg.Helpers
import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpBufferTrieProg.ClearLoop
import CslibFrontier.Tactic.Realize

/-!
# Parameter-Free `bufClearStepsGenProg` Subroutine

Certified `O(k)` `bufClearSteps` incremental trie reset subroutine preserving `BufEpFrame` and
opposite-buffer invariants.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.BufClearStepsGenPre`
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.bufClearStepsGenProg`

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.bufClearStepsGenProg_spec`
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.realizes_bufClearStepsGen`
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

open Finset
open scoped BigOperators
open Cslib.WordRAM Cslib.WordRAM.Realization
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.StateTransitionSpec (clientState_bind clientResult_bind)
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.SuccinctWhp
open Cslib.DataStructure.Dictionary.Dynamic (logLogFactor one_le_logLogFactor)
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM.Succinct

attribute [local simp] clientResult_pure_whp clientState_pure_whp

/-- Precondition for `bufClearStepsGenProg` (`d = (((cp, base), ep), k)`). -/
@[expose] def BufClearStepsGenPre (w : ℕ) :
    ((WhpCoreParams × ℕ) × ℕ) × ℕ → Memory.State → Prop
  | (((cp, base), ep), _), s =>
    ∃ c U V w₀ n_max tr,
      WhpLargeEnv c U V w₀ n_max w base ∧
      cp = mkWhpCoreParams c U V w₀ n_max ∧
      (ep = 0 ∨ ep = 1) ∧
      BufTrieMemRep base c U V w₀ n_max ep tr s.mem ∧
      ClearableBufTrie tr

/-- Parameter-free `bufClearSteps` (`d = (((cp, base), ep), k)`). -/
@[irreducible] def bufClearStepsGenProg (d : ((WhpCoreParams × ℕ) × ℕ) × ℕ) : Memory.Prog Unit := do
  let rt ← mkBufRtGenProg d.1
  bufClearLoopGenProg ((rt, ()), d.2)

theorem bufClearStepsGenProg_spec {c U V w n_max base ep k : ℕ}
    {tr : BufTrie} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base) (hep : ep = 0 ∨ ep = 1)
    (hrep : BufTrieMemRep base c U V w n_max ep tr s.mem)
    (hclr : ClearableBufTrie tr) :
    let prog := bufClearStepsGenProg (((mkWhpCoreParams c U V w n_max, base), ep), k)
    let s' := (Memory.spec 0).clientState s prog
    let tr' := bufClearSteps k tr
    s'.frontier = s.frontier ∧
    memoryCost prog s ≤ 15 * k ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    BufTrieMemRep base c U V w n_max ep tr' s'.mem ∧
    BufEpFrame base c U V w n_max ep s.mem s'.mem := by
  obtain ⟨hrt_st, hrt_res, hrt_mc, hrt_vp⟩ := mkBufRtGenProg_spec (c := c) (U := U) (V := V)
    (w := w) (n_max := n_max) (base := base) (ep := ep) henv.2.2.2.1 s
  set rt := mkBufRt c U V w n_max base ep
  obtain ⟨_, hfr_l, hmc_l, hvp_l, hrep_l, hbfr_l⟩ := bufClearLoop_spec henv hep k tr s hrep hclr
  dsimp only
  unfold bufClearStepsGenProg
  have hs'_eq : (Memory.spec 0).clientState s
      (mkBufRtGenProg ((mkWhpCoreParams c U V w n_max, base), ep) >>= fun rt' =>
        bufClearLoopGenProg ((rt', ()), k)) =
      (Memory.spec 0).clientState s (bufClearLoopGenProg ((rt, ()), k)) := by
    rw [clientState_bind, hrt_st, hrt_res]
  rw [hs'_eq]
  refine ⟨hfr_l, ?_, validProg_bind hrt_vp (by rwa [hrt_st, hrt_res]), hrep_l, hbfr_l⟩
  simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
  rw [hrt_st, hrt_res, hrt_mc]
  dsimp only [rt] at hmc_l ⊢
  omega

theorem realizes_bufClearStepsGen :
    Realizes .exact bufClearStepsGenProg
      (WordEncoding.encode (α := ((WhpCoreParams × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      BufClearStepsGenPre
      (fun _ _ => 0) := by
  unfold bufClearStepsGenProg
  have hmrt := realizes_mkBufRtGen
  have hcl := realizes_bufClearLoopGen
  realize
  all_goals
    rcases d with ⟨⟨⟨cp, base⟩, ep⟩, k⟩
    obtain ⟨c, U, V, _, n_max, tr, henv, rfl, hep, hrep, hclr⟩ := h
    cases henv.2.2.1
    obtain ⟨hrt_st, hrt_res, _, _⟩ := mkBufRtGenProg_spec (c := c) (U := U) (V := V)
      (w := w) (n_max := n_max) (base := base) (ep := ep) henv.2.2.2.1 s
    obtain ⟨hsafe, _, _, _, _, _⟩ := bufClearLoop_spec henv hep k tr s hrep hclr
    simp only [hrt_st, hrt_res] at *
  · exact ⟨c, U, V, w, n_max, henv, rfl⟩
  · exact hsafe

end Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

end
