/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.HopcroftKarp.Internal
import CslibFrontier.Algorithms.WordRAM.HopcroftKarp.DFSStep
import CslibFrontier.Computability.WordRAM.CountingLoop
import CslibFrontier.Computability.WordRAM.Notation
import CslibFrontier.Computability.WordRAM.SymbolicExec
import Mathlib.Algebra.BigOperators.Fin

/-!
# Hopcroft–Karp iterative DFS augmentation phase on the word RAM

Implements the `O(m + r + |E|)` word-RAM depth-first augmentation phase `Internal.dfsPhaseCode`
used by `CslibFrontier.Algorithms.WordRAM.HopcroftKarp`, matching
`Cslib.Algorithms.Lean.MaxFlow.hkPhase` ([HopcroftKarp1973]; [CLRS2009], Problem 26-6).

## Main definitions

* `Cslib.Algorithms.WordRAM.HopcroftKarp.Internal.dfsPhaseCode`: clears `vis`, runs explicit-stack
  DFS from every layer-`0` root, and rematches `colMate` along the collected disjoint augmenting
  paths.

## Main results

* `Cslib.Algorithms.WordRAM.HopcroftKarp.Internal.exec_dfsPhaseCode`: `O(m + r + |E|)` instruction
  bound and exact agreement with `hkPhase`.

## References

* [J. E. Hopcroft and R. M. Karp, *An n^{5/2} Algorithm for Maximum Matchings in Bipartite
  Graphs*][HopcroftKarp1973]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest, and C. Stein,
  *Introduction to Algorithms*][CLRS2009]
-/

public section

namespace Cslib.Algorithms.WordRAM.HopcroftKarp.Internal

open Cslib.WordRAM
open Cslib.Algorithms.Lean
open Cslib.Algorithms.Lean.MaxFlow
open Cslib.Algorithms.WordRAM.HopcroftKarp.Reg

/-- Postcondition of executing `dfsLoop` from stack depth `d` over remaining neighbours `vs`. -/
private def DfsLevelPost (w bOff k f d : ℕ) (inst : SparseInstance)
    (mate : Vector (Option (Fin inst.m)) inst.r) (dist : Vector (Option ℕ) inst.m)
    (augPairs path : List (Fin inst.m × Fin inst.r)) (u : Fin inst.m)
    (vs : List (Fin inst.r)) (vis : Vector Bool inst.r) (x : Data 34) : Prop :=
  let res := hkDfsLevel inst.graph mate dist (decide (f = 0)) d
    (dfsNext inst.graph inst.adj mate dist f d) u vs vis []
  match res.2 with
  | some q =>
    ∃ z, ExecWithin w dfsLoop x z
        (38 * vs.length + (dfsPot inst mate vis - dfsPot inst mate res.1) + 12 * (k + 1) + 33) ∧
      (∀ i : Fin 34, i.val < 25 → z.regs i = x.regs i) ∧
      z.regs augLen = (augPairs ++ (path ++ q)).length ∧
      VisMem inst bOff res.1 z.mem ∧
      AugMem inst bOff (augPairs ++ (path ++ q)) z.mem ∧
      (∀ a, ¬(bOff + inst.m + 1 + inst.numEdges + inst.r + 3 * inst.m ≤ a ∧
          a < bOff + inst.m + 1 + inst.numEdges + 4 * inst.r + 6 * inst.m + 6) →
        z.mem a = x.mem a)
  | none =>
    ∃ y,
      (∀ z T_after, ExecWithin w dfsLoop y z T_after →
        ExecWithin w dfsLoop x z
          (38 * vs.length + 14 + (dfsPot inst mate vis - dfsPot inst mate res.1) + T_after)) ∧
      (∀ i : Fin 34, i.val < 25 → y.regs i = x.regs i) ∧
      y.regs augLen = augPairs.length ∧
      (if d = 0 then y.regs active = 0 else y.regs active = 1 ∧ y.regs rd = d - 1) ∧
      VisMem inst bOff res.1 y.mem ∧
      (∀ a, DfsSubtreeOutside inst bOff d a → y.mem a = x.mem a)

private theorem exec_dfsLevel_nil {w bOff k f d : ℕ} {inst : SparseInstance}
    {mate : Vector (Option (Fin inst.m)) inst.r} {dist : Vector (Option ℕ) inst.m}
    {augPairs path : List (Fin inst.m × Fin inst.r)} {u : Fin inst.m}
    {pre : List (Fin inst.r)} {vis : Vector Bool inst.r} {x : Data 34}
    (hd_le : d ≤ k) (hk_le : k ≤ inst.m + 1)
    (hsplit : inst.adj u = pre ++ [])
    (hfr : DfsFrame inst bOff k mate dist augPairs d path u pre vis x)
    (hfit : Fits w (bOff + 7 * inst.m + 5 * inst.r + inst.numEdges + 8)) :
    DfsLevelPost w bOff k f d inst mate dist augPairs path u [] vis x := by
  have hc_loop : (Cond.eq active one).Holds x := by
    rw [Cond.holds_eq, hfr.hact, hfr.hb.hone]
  obtain ⟨y, he_pop, hr_y, hal_y, hact_y, hmem_y⟩ :=
    exec_dfsStep_pop hd_le hk_le (by simpa using hsplit) hfr hfit
  dsimp only [DfsLevelPost, hkDfsLevel]
  exact ⟨y, fun z T_after he_after =>
    (ExecWithin.loop_iter hc_loop he_pop he_after).mono (by omega),
    hr_y, hal_y, hact_y, hmem_y ▸ hfr.hvisM, fun a _ => congrFun hmem_y a⟩

private theorem exec_dfsLevel_skip {w bOff k f d : ℕ} {inst : SparseInstance}
    {mate : Vector (Option (Fin inst.m)) inst.r} {dist : Vector (Option ℕ) inst.m}
    {augPairs path : List (Fin inst.m × Fin inst.r)} {u : Fin inst.m}
    {pre vs : List (Fin inst.r)} {v : Fin inst.r}
    {vis : Vector Bool inst.r} {x : Data 34}
    (hd_le : d ≤ k) (hk_le : k ≤ inst.m + 1)
    (hsplit : inst.adj u = pre ++ v :: vs)
    (hfr : DfsFrame inst bOff k mate dist augPairs d path u pre vis x)
    (hcond : vget vis v = true ∨
      (vget vis v = false ∧ vget mate v = none ∧ d ≠ k) ∨
      (vget vis v = false ∧ ∃ w₀, vget mate v = some w₀ ∧
        ¬(d < k ∧ vget dist w₀ = some (d + 1))))
    (hfit : Fits w (bOff + 7 * inst.m + 5 * inst.r + inst.numEdges + 8))
    (heq_R : hkDfsLevel inst.graph mate dist (decide (f = 0)) d
        (dfsNext inst.graph inst.adj mate dist f d) u (v :: vs) vis [] =
      hkDfsLevel inst.graph mate dist (decide (f = 0)) d
        (dfsNext inst.graph inst.adj mate dist f d) u vs vis [])
    (ih_step : ∀ x₁, DfsFrame inst bOff k mate dist augPairs d path u (pre ++ [v]) vis x₁ →
      DfsLevelPost w bOff k f d inst mate dist augPairs path u vs vis x₁) :
    DfsLevelPost w bOff k f d inst mate dist augPairs path u (v :: vs) vis x := by
  have hc_loop : (Cond.eq active one).Holds x := by
    rw [Cond.holds_eq, hfr.hact, hfr.hb.hone]
  obtain ⟨x₁, he_skip, hr₁, hfr₁, hf_sub₁, hf_all₁⟩ :=
    exec_dfsStep_skip hd_le hk_le hsplit hfr hcond hfit
  have hrec := ih_step x₁ hfr₁
  dsimp only [DfsLevelPost] at hrec ⊢
  rw [heq_R]
  cases hr2 : (hkDfsLevel inst.graph mate dist (decide (f = 0)) d
      (dfsNext inst.graph inst.adj mate dist f d) u vs vis []).2 with
  | some q =>
    rw [hr2] at hrec
    obtain ⟨z, he_rest, hr_z, hal_z, hvis_z, haug_z, hf_z⟩ := hrec
    exact ⟨z, (ExecWithin.loop_iter hc_loop he_skip he_rest).mono
      (by simp only [List.length_cons]; omega),
      fun i hi => (hr_z i hi).trans (hr₁ i hi), hal_z, hvis_z, haug_z,
      fun a ha => (hf_z a ha).trans (hf_all₁ a ha)⟩
  | none =>
    rw [hr2] at hrec
    obtain ⟨y, htrans, hr_y, hal_y, hact_y, hvis_y, hf_y⟩ := hrec
    exact ⟨y, fun z T_after he_after =>
      (ExecWithin.loop_iter hc_loop he_skip (htrans z T_after he_after)).mono
        (by simp only [List.length_cons]; omega),
      fun i hi => (hr_y i hi).trans (hr₁ i hi), hal_y, hact_y, hvis_y,
      fun a ha => (hf_y a ha).trans (hf_sub₁ a ha)⟩

private theorem exec_dfsLevel_cons_unvisited {w bOff k f d : ℕ} {inst : SparseInstance}
    {mate : Vector (Option (Fin inst.m)) inst.r} {dist : Vector (Option ℕ) inst.m}
    {augPairs path : List (Fin inst.m × Fin inst.r)} {u : Fin inst.m}
    {pre vs : List (Fin inst.r)} {v : Fin inst.r}
    {vis : Vector Bool inst.r} {x : Data 34}
    (hd_le : d ≤ k) (hk_le : k ≤ inst.m + 1)
    (hsplit : inst.adj u = pre ++ v :: vs)
    (hfr : DfsFrame inst bOff k mate dist augPairs d path u pre vis x)
    (hfit : Fits w (bOff + 7 * inst.m + 5 * inst.r + inst.numEdges + 8))
    (ih_step : ∀ x₁, DfsFrame inst bOff k mate dist augPairs d path u (pre ++ [v]) vis x₁ →
      DfsLevelPost w bOff k f d inst mate dist augPairs path u vs vis x₁)
    (hunvis : inst.graph (u, v) = true → inst.adj u = (pre ++ [v]) ++ vs → vget vis v = false →
      DfsLevelPost w bOff k f d inst mate dist augPairs path u (v :: vs) vis x) :
    DfsLevelPost w bOff k f d inst mate dist augPairs path u (v :: vs) vis x := by
  have hGu : inst.graph (u, v) = true := decide_eq_true (by rw [hsplit]; simp)
  have hsplit' : inst.adj u = (pre ++ [v]) ++ vs := by simp [hsplit]
  by_cases hvv : vget vis v = false
  · exact hunvis hGu hsplit' hvv
  · have hvv_t : vget vis v = true := Bool.eq_true_of_not_eq_false hvv
    exact exec_dfsLevel_skip hd_le hk_le hsplit hfr (Or.inl hvv_t) hfit
      (by simp [hkDfsLevel, hvv_t]) ih_step

private theorem exec_dfsLevel {w bOff k : ℕ} {inst : SparseInstance}
    {mate : Vector (Option (Fin inst.m)) inst.r} {dist : Vector (Option ℕ) inst.m}
    (hk_le : k ≤ inst.m + 1) (augPairs : List (Fin inst.m × Fin inst.r)) :
    ∀ (f d : ℕ), f + d = k →
      ∀ (path : List (Fin inst.m × Fin inst.r)) (u : Fin inst.m)
        (pre vs : List (Fin inst.r)) (vis : Vector Bool inst.r) (x : Data 34),
        inst.adj u = pre ++ vs →
        DfsFrame inst bOff k mate dist augPairs d path u pre vis x →
        Fits w (bOff + 7 * inst.m + 5 * inst.r + inst.numEdges + 8) →
        DfsLevelPost w bOff k f d inst mate dist augPairs path u vs vis x := by
  intro f
  induction f with
  | zero =>
    intro d hfd path u pre vs vis x hsplit hfr hfit
    obtain rfl : d = k := by omega
    induction vs generalizing pre vis x with
    | nil => exact exec_dfsLevel_nil (le_refl d) hk_le hsplit hfr hfit
    | cons v vs ih =>
      refine exec_dfsLevel_cons_unvisited (le_refl d) hk_le hsplit hfr hfit
        (fun x₁ hfr₁ => ih (pre ++ [v]) vis x₁ (by simp [hsplit]) hfr₁) fun hGu hsplit' hvv => ?_
      cases hmv : vget mate v with
      | none =>
        obtain ⟨z, he_acc, hr_z, hal_z, hvis_z, haug_z, hf_z⟩ :=
          exec_dfsStep_accept hk_le hsplit hfr hvv hmv hfit
        have heq_R : hkDfsLevel inst.graph mate dist (decide (0 = 0)) d
            (dfsNext inst.graph inst.adj mate dist 0 d) u (v :: vs) vis [] =
            (vset vis v true, some [(u, v)]) := by
          simp [hkDfsLevel, hGu, hvv, hmv]
        dsimp only [DfsLevelPost]
        rw [heq_R]
        exact ⟨z, he_acc.mono (by omega), hr_z, hal_z, hvis_z, haug_z, hf_z⟩
      | some w₀ =>
        exact exec_dfsLevel_skip (le_refl d) hk_le hsplit hfr
          (Or.inr (Or.inr ⟨hvv, w₀, hmv, fun h => Nat.lt_irrefl d h.1⟩)) hfit
          (by simp [hkDfsLevel, hGu, hvv, hmv])
          (fun x₁ hfr₁ => ih (pre ++ [v]) vis x₁ hsplit' hfr₁)
  | succ f ih_f =>
    intro d hfd path u pre vs vis x hsplit hfr hfit
    have hd_lt_k : d < k := by omega
    have hd_le_k : d ≤ k := by omega
    have hd_ne_k : d ≠ k := by omega
    induction vs generalizing pre vis x with
    | nil => exact exec_dfsLevel_nil hd_le_k hk_le hsplit hfr hfit
    | cons v vs ih =>
      refine exec_dfsLevel_cons_unvisited hd_le_k hk_le hsplit hfr hfit
        (fun x₁ hfr₁ => ih (pre ++ [v]) vis x₁ (by simp [hsplit]) hfr₁) fun hGu hsplit' hvv => ?_
      have hc_loop : (Cond.eq active one).Holds x := by
        rw [Cond.holds_eq, hfr.hact, hfr.hb.hone]
      cases hmv : vget mate v with
      | none =>
        exact exec_dfsLevel_skip hd_le_k hk_le hsplit hfr
          (Or.inr (Or.inl ⟨hvv, hmv, hd_ne_k⟩)) hfit
          (by simp [hkDfsLevel, hGu, hvv, hmv])
          (fun x₁ hfr₁ => ih (pre ++ [v]) vis x₁ hsplit' hfr₁)
      | some w₀ =>
        by_cases hdw : vget dist w₀ = some (d + 1)
        · obtain ⟨x_push, he_push, hr_p, hfr_p, hspd_p, hf_sub_p, hf_all_p⟩ :=
            exec_dfsStep_push hd_lt_k hk_le hsplit hfr hvv hmv hdw hfit
          have hpot_v : dfsPot inst mate (vset vis v true) +
              (38 * (inst.adj w₀).length + 14) = dfsPot inst mate vis := by
            simpa [dfsVertWeight, hkDfsCost, hmv] using
              dfsPot_vset_true (inst := inst) (mate := mate) hvv
          have hchild := ih_f (d + 1) (by omega) (path ++ [(u, v)]) w₀ [] (inst.adj w₀)
            (vset vis v true) x_push rfl hfr_p hfit
          dsimp only [DfsLevelPost] at hchild ⊢
          rw [← hkDfs_eq_dfsLevel] at hchild
          obtain ⟨_, hpot_child, hcov_child⟩ :=
            hkDfs_pure_props (inst := inst) (mate := mate) (dist := dist) f (d + 1) w₀
              (vset vis v true) (augPairs ++ (path ++ [(u, v)])) hfr_p.hcovers
          have heq_step : hkDfsLevel inst.graph mate dist (decide (f + 1 = 0)) d
              (dfsNext inst.graph inst.adj mate dist (f + 1) d) u (v :: vs) vis [] =
            let res := hkDfs inst.graph inst.adj mate dist f (d + 1) w₀ (vset vis v true) []
            match res.2 with
            | some qw => (res.1, some ((u, v) :: qw))
            | none => hkDfsLevel inst.graph mate dist (decide (f + 1 = 0)) d
                (dfsNext inst.graph inst.adj mate dist (f + 1) d) u vs res.1 [] := by
            simp only [hkDfsLevel, hGu, hvv, hmv, hdw, dfsNext]
            cases (hkDfs inst.graph inst.adj mate dist f (d + 1) w₀ (vset vis v true) []).2 <;>
              simp
          rw [heq_step]
          dsimp only
          cases hrw : (hkDfs inst.graph inst.adj mate dist f (d + 1) w₀
              (vset vis v true) []).2 with
          | some qw =>
            rw [hrw] at hchild hcov_child
            dsimp only
            obtain ⟨z, he_child, hr_z, hal_z, hvis_z, haug_z, hf_z⟩ := hchild
            have hpath_assoc :
                augPairs ++ ((path ++ [(u, v)]) ++ qw) =
                  augPairs ++ (path ++ ((u, v) :: qw)) := by
              simp [List.append_assoc]
            rw [hpath_assoc] at hal_z haug_z
            exact ⟨z, (ExecWithin.loop_iter hc_loop he_push he_child).mono
              (by simp only [List.length_cons]; omega),
              fun i hi => (hr_z i hi).trans (hr_p i hi), hal_z, hvis_z, haug_z,
              fun a ha => (hf_z a ha).trans (hf_all_p a ha)⟩
          | none =>
            rw [hrw] at hchild hcov_child
            dsimp only
            obtain ⟨y_pop, htrans_c, hr_c, hal_c, hact_c, hvis_c, hf_c⟩ := hchild
            rw [ite_eq_right (Nat.succ_ne_zero d)] at hact_c
            have hcov_back : VisCovers
                (hkDfs inst.graph inst.adj mate dist f (d + 1) w₀ (vset vis v true) []).1
                (augPairs ++ path) :=
              ⟨hfr.hcovers.1, fun e he => hcov_child.2 e (by
                simp only [List.mem_append] at he ⊢
                exact he.elim Or.inl (Or.inr ∘ Or.inl))⟩
            have haug_le : augPairs.length ≤ inst.r := by
              have := hfr.hcovers.length_le
              simp only [List.length_append] at this
              omega
            have hc_d {a} (ha : DfsSubtreeOutside inst bOff d a) : y_pop.mem a = x.mem a :=
              (hf_c a (by simp only [DfsSubtreeOutside] at ha ⊢; omega)).trans (hf_sub_p a ha)
            have hfr_pop : DfsFrame inst bOff k mate dist augPairs d path u (pre ++ [v])
                (hkDfs inst.graph inst.adj mate dist f (d + 1) w₀ (vset vis v true) []).1
                y_pop :=
              { hplen := hfr.hplen
                hcovers := hcov_back
                hb := hfr_p.hb.of_eq fun i hi => hr_c i (by omega)
                hcsr := hfr.hcsr.of_outside fun a ha =>
                  hc_d (by simp only [DfsSubtreeOutside]; omega)
                hmate := hfr.hmate.of_outside fun a ha =>
                  hc_d (by simp only [DfsSubtreeOutside]; omega)
                hdM := hfr.hdM.of_outside fun a ha => hc_d (by simp only [DfsSubtreeOutside]; omega)
                hvisM := hvis_c
                haugM := hfr.haugM.of_outside haug_le fun a ha =>
                  hc_d (by simp only [DfsSubtreeOutside]; omega)
                hstack := fun i hi => by
                  rw [hc_d (by simp only [DfsSubtreeOutside]; omega),
                    hc_d (by simp only [DfsSubtreeOutside]; omega)]
                  exact hfr.hstack i hi
                hsu := by rw [hc_d (by simp only [DfsSubtreeOutside]; omega)]; exact hfr.hsu
                hsp := by rw [hf_c _ (by simp only [DfsSubtreeOutside]; omega)]; exact hspd_p
                hrk := (hr_c rk (by decide)).trans hfr_p.hrk
                hrd := by simpa using hact_c.2
                hal := hal_c
                hact := hact_c.1 }
            have hpot_rem := (hkDfsLevel_pure_props (mate := mate) (dist := dist) (f + 1) d
              (fun w' vis₀ ps₀ hc => hkDfs_pure_props f (d + 1) w' vis₀ ps₀ hc)
              u vs _ (augPairs ++ path) hcov_back).2.1
            have hrem := ih (pre ++ [v]) _ y_pop hsplit' hfr_pop
            dsimp only [DfsLevelPost] at hrem
            cases hr2 : (hkDfsLevel inst.graph mate dist (decide (f + 1 = 0)) d
                (dfsNext inst.graph inst.adj mate dist (f + 1) d) u vs
                (hkDfs inst.graph inst.adj mate dist f (d + 1) w₀
                  (vset vis v true) []).1 []).2 with
            | some q =>
              rw [hr2] at hrem
              obtain ⟨z, he_rem, hr_z, hal_z, hvis_z, haug_z, hf_z⟩ := hrem
              exact ⟨z, (ExecWithin.loop_iter hc_loop he_push (htrans_c z _ he_rem)).mono
                (by simp only [List.length_cons]; omega),
                fun i hi => (hr_z i hi).trans ((hr_c i hi).trans (hr_p i hi)),
                hal_z, hvis_z, haug_z, fun a ha =>
                  (hf_z a ha).trans ((hf_c a (by simp only [DfsSubtreeOutside]; omega)).trans
                    (hf_all_p a ha))⟩
            | none =>
              rw [hr2] at hrem
              obtain ⟨y_end, htrans_rem, hr_end, hal_end, hact_end, hvis_end, hf_end⟩ := hrem
              exact ⟨y_end, fun z T_after he_after =>
                (ExecWithin.loop_iter hc_loop he_push
                  (htrans_c z _ (htrans_rem z T_after he_after))).mono
                  (by simp only [List.length_cons]; omega),
                fun i hi => (hr_end i hi).trans ((hr_c i hi).trans (hr_p i hi)),
                hal_end, hact_end, hvis_end, fun a ha => (hf_end a ha).trans (hc_d ha)⟩
        · exact exec_dfsLevel_skip hd_le_k hk_le hsplit hfr
            (Or.inr (Or.inr ⟨hvv, w₀, hmv, fun h => hdw h.2⟩)) hfit
            (by simp [hkDfsLevel, hGu, hvv, hmv, hdw])
            (fun x₁ hfr₁ => ih (pre ++ [v]) vis x₁ hsplit' hfr₁)

private def dfsRootSetup : Code .standard 34 := ram[
  rd ← #0;
  addr ← bStackUReg; *addr ← qHead;
  addr ← bOffReg + qHead; val ← *addr;
  addr ← bStackPosReg; *addr ← val;
  active ← one ]

private def dfsRootBody : Code .standard 34 :=
  .seq (ram[ addr ← bDistReg + qHead; val ← *addr ])
    (.seq (.branch (.eq val one) (.seq dfsRootSetup dfsLoop) (ram[ tmp ← zero ]))
      (ram[ qHead ← qHead + one ]))

private def applyAugBody : Code .standard 34 := ram[
  addr ← bAugUReg + idx; val ← *addr;
  addr ← bAugVReg + idx; val2 ← *addr;
  addr ← bColMateReg + val2; *addr ← val;
  idx ← idx + one ]

private def applyAugCode : Code .standard 34 :=
  .seq (ram[ idx ← #0 ]) (.loop (.lt idx augLen) applyAugBody)

/-- Explicit-stack DFS augmentation phase (`O(m + r + |E|)` instructions per phase). -/
def dfsPhaseCode : Code .standard 34 :=
  .seq (clearAt bVisReg rr)
    (.seq (ram[ augLen ← #0; qHead ← #0 ])
      (.seq (.loop (.lt qHead rm) dfsRootBody) applyAugCode))

private theorem exec_dfsRootsLoop {w bOff k : ℕ} {inst : SparseInstance}
    {mate : Vector (Option (Fin inst.m)) inst.r} {dist : Vector (Option ℕ) inst.m}
    (hk_le : k ≤ inst.m + 1)
    (pre us : List (Fin inst.m)) (hsplit : List.finRange inst.m = pre ++ us)
    (vis : Vector Bool inst.r)
    (augPairs pureAcc : List (Fin inst.m × Fin inst.r))
    (hcovers : VisCovers vis augPairs)
    (hfin_eq : augPairs.toFinset = pureAcc.toFinset)
    (x : Data 34) (hb : BaseRegs inst bOff x) (hcsr : CSRMem inst bOff x.mem)
    (hmate : MateMem inst bOff mate x.mem)
    (hdM : DistMem inst bOff dist x.mem)
    (hvisM : VisMem inst bOff vis x.mem)
    (haugM : AugMem inst bOff augPairs x.mem)
    (hrk : x.regs rk = k)
    (hqh : x.regs qHead = pre.length)
    (hal : x.regs augLen = augPairs.length)
    (hfit : Fits w (bOff + 7 * inst.m + 5 * inst.r + inst.numEdges + 8)) :
    ∃ y augPairs',
      ExecWithin w (.loop (.lt qHead rm) dfsRootBody) x y
        ((us.map (fun u => 38 * (inst.adj u).length + 49)).sum +
          dfsPot inst mate vis + 12 * (augPairs'.length - augPairs.length) + 2) ∧
      augPairs.length ≤ augPairs'.length ∧
      (∀ i : Fin 34, i.val < 20 → y.regs i = x.regs i) ∧
      y.regs augLen = augPairs'.length ∧
      VisCovers (Vector.replicate inst.r true) augPairs' ∧
      augPairs'.toFinset = (hkDfsRoots inst.graph inst.adj mate dist k us vis pureAcc).toFinset ∧
      AugMem inst bOff augPairs' y.mem ∧
      (∀ a, ¬(bOff + inst.m + 1 + inst.numEdges + inst.r + 3 * inst.m ≤ a ∧
          a < bOff + inst.m + 1 + inst.numEdges + 4 * inst.r + 6 * inst.m + 6) →
        y.mem a = x.mem a) := by
  induction us generalizing pre vis augPairs pureAcc x with
  | nil =>
    simp only [List.append_nil] at hsplit
    have hpre_m : pre.length = inst.m := by
      have := congrArg List.length hsplit; simpa using this.symm
    have hc : ¬(Cond.lt qHead rm).Holds x := by
      simp [Cond.holds_lt, hqh, hb.hrm, hpre_m]
    exact ⟨x, augPairs, (ExecWithin.loop_exit hc).mono (by omega), le_refl _,
      fun _ _ => rfl, hal, ⟨hcovers.1, fun _ _ => by simp [vget_replicate]⟩,
      hfin_eq, haugM, fun _ _ => rfl⟩
  | cons u us ih =>
    have hpre_lt : pre.length < inst.m := by
      have := congrArg List.length hsplit
      simp only [List.length_finRange, List.length_append, List.length_cons] at this
      omega
    have hu_val : u.val = pre.length := by
      have hget : (List.finRange inst.m)[pre.length]'(by simp [hpre_lt]) = u := by
        simp [hsplit]
      simpa using (congrArg Fin.val hget).symm
    have hc_loop : (Cond.lt qHead rm).Holds x := by
      simp [Cond.holds_lt, hqh, hb.hrm, hpre_lt]
    have hsplit' : List.finRange inst.m = (pre ++ [u]) ++ us := by simp [hsplit]
    have hdist_u :
        x.mem (bOff + inst.m + 1 + inst.numEdges + inst.r + inst.m + pre.length) =
          encodeDist (vget dist u) := by
      rw [← hu_val]
      exact hdM u
    have hchk : ∃ x_chk, ExecWithin w
        (ram[ addr ← bDistReg + qHead; val ← *addr ] : Code .standard 34) x x_chk 2 ∧
        x_chk = (x.set addr
          (bOff + inst.m + 1 + inst.numEdges + inst.r + inst.m + pre.length)).set val
          (encodeDist (vget dist u)) := by
      refine WP.exists_execWithin ?_
      wram_exec [hb.hbDist, hqh, hdist_u]
      rfl
    obtain ⟨x_chk, he_chk, rfl⟩ := hchk
    let x_chk := (x.set addr
      (bOff + inst.m + 1 + inst.numEdges + inst.r + inst.m + pre.length)).set val
      (encodeDist (vget dist u))
    have hb_chk : BaseRegs inst bOff x_chk :=
      hb.of_eq fun i hi => by dsimp only [x_chk]; wram_simp
    by_cases hdu0 : vget dist u = some 0
    · have henc_1 : encodeDist (vget dist u) = 1 := by simp [hdu0, encodeDist]
      have hc_val1 : (Cond.eq val one).Holds x_chk := by
        rw [Cond.holds_eq, hb_chk.hone]
        dsimp only [x_chk]
        wram_simp [henc_1]
      have hoff_u : x_chk.mem (bOff + pre.length) = inst.offset u.val := by
        dsimp only [x_chk]
        rw [← hu_val]
        exact hcsr.hoff (le_of_lt u.isLt)
      have hqh_chk : x_chk.regs qHead = pre.length := by dsimp only [x_chk]; wram_simp [hqh]
      have hal_chk : x_chk.regs augLen = augPairs.length := by dsimp only [x_chk]; wram_simp [hal]
      have hset : ∃ x_in, ExecWithin w dfsRootSetup x_chk x_in 8 ∧
          (∀ i : Fin 34, i.val < 25 → x_in.regs i = x.regs i) ∧
          x_in.regs rd = 0 ∧ x_in.regs augLen = augPairs.length ∧ x_in.regs active = 1 ∧
          x_in.mem = Function.update
            (Function.update x.mem
              (bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 3 * inst.m) u.val)
            (bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 5 * inst.m + 4)
            (inst.offset u.val) := by
        refine WP.exists_execWithin ?_
        unfold dfsRootSetup
        wram_exec [hb_chk.hbStackU, hb_chk.hbOff, hb_chk.hbStackPos, hb_chk.hone,
          hqh_chk, hoff_u]
        refine ⟨fun i hi => by dsimp only [x_chk]; wram_simp, by wram_simp,
          by wram_simp [hal_chk], by wram_simp, ?_⟩
        rw [← hu_val]
        rfl
      obtain ⟨x_in, he_in, hr_in, hrd_in, hal_in, hact_in, hmem_in⟩ := hset
      have hin_out {a} (ha : ¬(bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 3 * inst.m ≤ a ∧
          a < bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 5 * inst.m + 5)) :
          x_in.mem a = x.mem a := by
        rw [hmem_in, Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      have hfr_in : DfsFrame inst bOff k mate dist augPairs 0 [] u [] vis x_in :=
        { hplen := rfl
          hcovers := by simpa using hcovers
          hb := hb.of_eq fun i hi => hr_in i (by omega)
          hcsr := hcsr.of_outside fun a ha => hin_out (by omega)
          hmate := hmate.of_outside fun a ha => hin_out (by omega)
          hdM := hdM.of_outside fun a ha => hin_out (by omega)
          hvisM := hvisM.of_outside fun a ha => hin_out (by omega)
          haugM := haugM.of_outside hcovers.length_le fun a ha => hin_out (by omega)
          hstack := fun _ hi => absurd hi (Nat.not_lt_zero _)
          hsu := by
            simp only [Nat.add_zero, hmem_in]
            rw [Function.update_of_ne (by omega), Function.update_self]
          hsp := by
            simp only [Nat.add_zero, List.length_nil, hmem_in]
            exact Function.update_self _ _ _
          hrk := (hr_in rk (by decide)).trans hrk
          hrd := hrd_in
          hal := hal_in
          hact := hact_in }
      have hdfs := exec_dfsLevel hk_le augPairs k 0 (by omega) [] u [] (inst.adj u)
        vis x_in rfl hfr_in hfit
      dsimp only [DfsLevelPost] at hdfs
      rw [← hkDfs_eq_dfsLevel] at hdfs
      obtain ⟨_, hpot_R, hcov_R⟩ :=
        hkDfs_pure_props (inst := inst) (mate := mate) (dist := dist) k 0 u vis augPairs hcovers
      have hacc_eq := hkDfs_acc inst.graph inst.adj mate dist k 0 u vis pureAcc
      have hbody_exec : ∃ x₁ aug₁,
          ExecWithin w dfsRootBody x x₁
            (38 * (inst.adj u).length + 47 +
              (dfsPot inst mate vis -
                dfsPot inst mate (hkDfs inst.graph inst.adj mate dist k 0 u vis []).1) +
              12 * (aug₁.length - augPairs.length)) ∧
          augPairs.length ≤ aug₁.length ∧
          (∀ i : Fin 34, i.val < 22 → x₁.regs i = x.regs i) ∧
          x₁.regs qHead = pre.length + 1 ∧
          x₁.regs augLen = aug₁.length ∧
          VisCovers (hkDfs inst.graph inst.adj mate dist k 0 u vis []).1 aug₁ ∧
          aug₁.toFinset = ((hkDfs inst.graph inst.adj mate dist k 0 u vis pureAcc).2.getD
            pureAcc).toFinset ∧
          VisMem inst bOff (hkDfs inst.graph inst.adj mate dist k 0 u vis []).1 x₁.mem ∧
          AugMem inst bOff aug₁ x₁.mem ∧
          (∀ a, ¬(bOff + inst.m + 1 + inst.numEdges + inst.r + 3 * inst.m ≤ a ∧
              a < bOff + inst.m + 1 + inst.numEdges + 4 * inst.r + 6 * inst.m + 6) →
            x₁.mem a = x.mem a) := by
        have wrap_root (s_mid : Data 34) {t_dfs : ℕ}
            (he_dfs : ExecWithin w (.loop (.eq active one) dfsStepBody) x_in s_mid t_dfs)
            (hr_mid : ∀ i : Fin 34, i.val < 25 → s_mid.regs i = x_in.regs i) :
            ExecWithin w dfsRootBody x (s_mid.set qHead (pre.length + 1))
              (2 + ((8 + t_dfs + 1) + 1)) := by
          have hqh_mid : s_mid.regs qHead = pre.length :=
            (hr_mid qHead (by decide)).trans ((hr_in qHead (by decide)).trans hqh)
          have hone_mid : s_mid.regs one = 1 :=
            (hr_mid one (by decide)).trans hfr_in.hb.hone
          have hinc : ExecWithin w (ram[ qHead ← qHead + one ] : Code .standard 34)
              s_mid (s_mid.set qHead (pre.length + 1)) 1 :=
            WP.execWithin (by wram_exec [hqh_mid, hone_mid]; rfl)
          exact he_chk.seq
            (((he_in.seq he_dfs).branch_pos (neg := (ram[ tmp ← zero ] : Code .standard 34))
              hc_val1).seq hinc)
        cases hr2 : (hkDfs inst.graph inst.adj mate dist k 0 u vis []).2 with
        | some q =>
          rw [hr2] at hdfs hcov_R hacc_eq
          obtain ⟨z_mid, he_dfs, hr_mid, hal_mid, hvis_mid, haug_mid, hf_mid⟩ := hdfs
          simp only [List.nil_append] at hal_mid haug_mid
          refine ⟨z_mid.set qHead (pre.length + 1), augPairs ++ q,
            (wrap_root z_mid he_dfs hr_mid).mono (by rw [List.length_append, hcov_R.2]; omega),
            by simp, fun i hi => by wram_simp [(hr_mid i (by omega)).trans (hr_in i (by omega))],
            by wram_simp, by wram_simp [hal_mid], hcov_R.1,
            by rw [hacc_eq]; simp [hfin_eq, Finset.union_comm], hvis_mid, haug_mid,
            fun a ha => (hf_mid a ha).trans (hin_out (by omega))⟩
        | none =>
          rw [hr2] at hdfs hcov_R hacc_eq
          obtain ⟨y_mid, htrans, hr_mid, hal_mid, hact_mid, hvis_mid, hf_mid⟩ := hdfs
          simp only [↓reduceIte] at hact_mid
          have hc_exit : ¬(Cond.eq active one).Holds y_mid := by
            rw [Cond.holds_eq, hact_mid, (hr_mid one (by decide)).trans hfr_in.hb.hone]; simp
          have haug_ymid : AugMem inst bOff augPairs y_mid.mem :=
            hfr_in.haugM.of_outside hcovers.length_le fun a ha =>
              hf_mid a (by simp only [DfsSubtreeOutside]; omega)
          refine ⟨y_mid.set qHead (pre.length + 1), augPairs,
            (wrap_root y_mid (htrans y_mid 2 (ExecWithin.loop_exit hc_exit)) hr_mid).mono
              (by omega),
            le_refl _, fun i hi => by wram_simp [(hr_mid i (by omega)).trans (hr_in i (by omega))],
            by wram_simp, by wram_simp [hal_mid], hcov_R, by rw [hacc_eq]; simp [hfin_eq],
            hvis_mid, haug_ymid,
            fun a ha => (hf_mid a (by simp only [DfsSubtreeOutside]; omega)).trans
              (hin_out (by omega))⟩
      obtain ⟨x₁, aug₁, he_body, hlen_le₁, hr₁, hqh₁, hal₁, hcov₁, hfin₁, hvis₁, haug₁, hf₁⟩ :=
        hbody_exec
      have hb₁ : BaseRegs inst bOff x₁ := hb.of_eq fun i hi => hr₁ i (by omega)
      have hcsr₁ : CSRMem inst bOff x₁.mem := hcsr.of_outside fun a ha => hf₁ a (by omega)
      have hmate₁ : MateMem inst bOff mate x₁.mem := hmate.of_outside fun a ha => hf₁ a (by omega)
      have hdM₁ : DistMem inst bOff dist x₁.mem := hdM.of_outside fun a ha => hf₁ a (by omega)
      obtain ⟨y, augPairs', he_rest, hlen_le₂, hr₂, hal₂, hcov₂, hfin₂, haug₂, hf₂⟩ :=
        ih (pre ++ [u]) hsplit' (hkDfs inst.graph inst.adj mate dist k 0 u vis []).1 aug₁
          ((hkDfs inst.graph inst.adj mate dist k 0 u vis pureAcc).2.getD pureAcc)
          hcov₁ hfin₁ x₁ hb₁ hcsr₁ hmate₁ hdM₁ hvis₁ haug₁
          ((hr₁ rk (by decide)).trans hrk) (by simpa using hqh₁) hal₁
      have heq_roots : hkDfsRoots inst.graph inst.adj mate dist k (u :: us) vis pureAcc =
          hkDfsRoots inst.graph inst.adj mate dist k us
            (hkDfs inst.graph inst.adj mate dist k 0 u vis []).1
            ((hkDfs inst.graph inst.adj mate dist k 0 u vis pureAcc).2.getD pureAcc) := by
        have h1 : (hkDfs inst.graph inst.adj mate dist k 0 u vis pureAcc).1 =
            (hkDfs inst.graph inst.adj mate dist k 0 u vis []).1 := by
          rw [hkDfs_acc]
        simp only [hkDfsRoots, ite_eq_left hdu0, h1]
      refine ⟨y, augPairs', (ExecWithin.loop_iter hc_loop he_body he_rest).mono ?_,
        hlen_le₁.trans hlen_le₂,
        fun i hi => (hr₂ i hi).trans (hr₁ i (by omega)),
        hal₂, hcov₂, by rw [heq_roots]; exact hfin₂, haug₂,
        fun a ha => (hf₂ a ha).trans (hf₁ a ha)⟩
      simp only [List.map_cons, List.sum_cons]
      omega
    · have henc_ne1 : encodeDist (vget dist u) ≠ 1 := by
        cases h : vget dist u with
        | none => simp [encodeDist]
        | some j =>
          simp only [encodeDist]
          intro heq
          exact hdu0 (by rw [h]; congr 1; omega)
      have hc_nval1 : ¬(Cond.eq val one).Holds x_chk := by
        rw [Cond.holds_eq, hb_chk.hone]
        dsimp only [x_chk]
        wram_simp
        exact henc_ne1
      have hnop : ExecWithin w (ram[ tmp ← zero ] : Code .standard 34) x_chk (x_chk.set tmp 0) 1 :=
        WP.execWithin (by wram_exec [hb_chk.hzero]; rfl)
      have hqh_chk : x_chk.regs qHead = pre.length := by dsimp only [x_chk]; wram_simp [hqh]
      have hinc : ExecWithin w (ram[ qHead ← qHead + one ] : Code .standard 34)
          (x_chk.set tmp 0) ((x_chk.set tmp 0).set qHead (pre.length + 1)) 1 :=
        WP.execWithin (by wram_exec [hqh_chk, hb_chk.hone]; rfl)
      let x₁ := (x_chk.set tmp 0).set qHead (pre.length + 1)
      have hb₁ : BaseRegs inst bOff x₁ :=
        hb.of_eq fun i hi => by dsimp only [x₁, x_chk]; wram_simp
      obtain ⟨y, augPairs', he_rest, hlen_le₂, hr₂, hal₂, hcov₂, hfin₂, haug₂, hf₂⟩ :=
        ih (pre ++ [u]) hsplit' vis augPairs pureAcc hcovers hfin_eq x₁ hb₁
          hcsr hmate hdM hvisM haugM
          (by dsimp only [x₁, x_chk]; wram_simp [hrk])
          (by dsimp only [x₁, x_chk]; wram_simp; simp)
          (by dsimp only [x₁, x_chk]; wram_simp [hal])
      refine ⟨y, augPairs',
        (ExecWithin.loop_iter hc_loop (he_chk.seq ((hnop.branch_neg hc_nval1).seq hinc))
          he_rest).mono ?_,
        hlen_le₂, fun i hi => (hr₂ i hi).trans (by dsimp only [x₁, x_chk]; wram_simp),
        hal₂, hcov₂, by simpa [hkDfsRoots, hdu0] using hfin₂, haug₂, hf₂⟩
      simp only [List.map_cons, List.sum_cons]; omega

private theorem exec_applyAugCode {w bOff : ℕ} {inst : SparseInstance}
    {mate : Vector (Option (Fin inst.m)) inst.r}
    (augPairs : List (Fin inst.m × Fin inst.r))
    (hlen_le : augPairs.length ≤ inst.r)
    (x : Data 34) (hb : BaseRegs inst bOff x)
    (hmate : MateMem inst bOff mate x.mem)
    (haugM : AugMem inst bOff augPairs x.mem)
    (hal : x.regs augLen = augPairs.length)
    (hfit : Fits w (bOff + 7 * inst.m + 5 * inst.r + inst.numEdges + 8)) :
    ∃ y, ExecWithin w applyAugCode x y (9 * augPairs.length + 3) ∧
      (∀ i : Fin 34, i.val < 20 → y.regs i = x.regs i) ∧
      MateMem inst bOff (hkApplyEdges mate augPairs) y.mem ∧
      (∀ a, ¬(bOff + inst.m + 1 + inst.numEdges ≤ a ∧
          a < bOff + inst.m + 1 + inst.numEdges + inst.r) → y.mem a = x.mem a) := by
  have hs₀ : ∃ s₀, ExecWithin w (ram[ idx ← #0 ] : Code .standard 34) x s₀ 1 ∧
      s₀ = x.set idx 0 := by
    refine WP.exists_execWithin ?_
    wram_exec
    rfl
  obtain ⟨s₀, he₀, rfl⟩ := hs₀
  let P (t : ℕ) (y : Data 34) : Prop :=
    t ≤ augPairs.length ∧
      (∀ i : Fin 34, i.val < 20 → y.regs i = x.regs i) ∧
      y.regs augLen = augPairs.length ∧
      MateMem inst bOff (hkApplyEdges mate (augPairs.take t)) y.mem ∧
      (∀ a, ¬(bOff + inst.m + 1 + inst.numEdges ≤ a ∧
          a < bOff + inst.m + 1 + inst.numEdges + inst.r) → y.mem a = x.mem a)
  have hP₀ : P 0 (x.set idx 0) := by
    refine ⟨Nat.zero_le _, fun i hi => by wram_simp, by wram_simp [hal], ?_, fun _ _ => rfl⟩
    simpa [hkApplyEdges] using hmate
  have hbody (y : Data 34) (hy : P (y.regs idx) y) (hlt : y.regs idx < augPairs.length) :
      ∃ z, ExecWithin w applyAugBody y z 7 ∧ P (y.regs idx + 1) z ∧
        z.regs idx = y.regs idx + 1 := by
    obtain ⟨_, hr, hal_y, hmate_y, hf_y⟩ := hy
    have hby : BaseRegs inst bOff y := hb.of_eq fun i hi => hr i (by omega)
    have hv_lt := (augPairs[y.regs idx]'hlt).2.isLt
    have hau : y.mem (bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 6 * inst.m + 6 +
        y.regs idx) = (augPairs[y.regs idx]'hlt).1.val := by
      rw [hf_y _ (by omega)]
      exact (haugM (y.regs idx) hlt).1
    have hav : y.mem (bOff + inst.m + 1 + inst.numEdges + 3 * inst.r + 6 * inst.m + 6 +
        y.regs idx) = (augPairs[y.regs idx]'hlt).2.val := by
      rw [hf_y _ (by omega)]
      exact (haugM (y.regs idx) hlt).2
    refine WP.exists_execWithin ?_
    unfold applyAugBody
    wram_exec [hby.hbAugU, hby.hbAugV, hby.hbColMate, hby.hone, hau, hav]
    have htake_eq : hkApplyEdges mate (augPairs.take (y.regs idx + 1)) =
        vset (hkApplyEdges mate (augPairs.take (y.regs idx)))
          (augPairs[y.regs idx]'hlt).2 (some (augPairs[y.regs idx]'hlt).1) := by
      rw [List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some]
      simp only [hkApplyEdges, List.foldl_append, List.foldl_cons, List.foldl_nil]
    refine ⟨⟨by omega, fun i hi => by wram_simp [hr i hi], by wram_simp [hal_y], ?_,
      fun a ha => ?_⟩, by wram_simp⟩
    · intro v₀
      have := v₀.isLt
      rw [htake_eq]
      rcases eq_or_ne v₀ (augPairs[y.regs idx]'hlt).2 with rfl | hne
      · wram_simp
        simp [encodeOptFin]
      · have hne_val : v₀.val ≠ (augPairs[y.regs idx]'hlt).2.val := fun h => hne (Fin.ext h)
        wram_simp
        rw [vget_vset_ne _ _ hne.symm]
        exact hmate_y v₀
    · wram_simp
      exact hf_y a ha
  obtain ⟨y, hl, hPend, _⟩ := ExecWithin.loop_count P (fun y hy => hy.2.2.1) hbody
    (x := x.set idx 0) (by simp) (by simpa using hP₀)
  obtain ⟨_, hr, _, hmate', hf'⟩ := hPend
  rw [List.take_of_length_le (le_refl _)] at hmate'
  exact ⟨y, (he₀.seq hl).mono (by simp; omega), hr, hmate', hf'⟩

/-- `O(m + r + |E|)` execution of `dfsPhaseCode`, agreeing with `hkPhase`. -/
theorem exec_dfsPhaseCode {w bOff k : ℕ} {inst : SparseInstance}
    {mate : Vector (Option (Fin inst.m)) inst.r} {dist : Vector (Option ℕ) inst.m}
    (hM : IsMatching inst.graph (mateMatching mate))
    (hk_le : k ≤ inst.m + 1)
    (x : Data 34) (hb : BaseRegs inst bOff x) (hcsr : CSRMem inst bOff x.mem)
    (hmate : MateMem inst bOff mate x.mem)
    (hdM : DistMem inst bOff dist x.mem)
    (hrk : x.regs rk = k)
    (hfit : Fits w (bOff + 7 * inst.m + 5 * inst.r + inst.numEdges + 8)) :
    ∃ y, ExecWithin w dfsPhaseCode x y (49 * inst.m + 39 * inst.r + 76 * inst.numEdges + 11) ∧
      (∀ i : Fin 34, i.val < 20 → y.regs i = x.regs i) ∧
      MateMem inst bOff (hkPhase inst.graph inst.adj mate dist k) y.mem ∧
      (∀ a, ¬(bOff + inst.m + 1 + inst.numEdges ≤ a ∧
          a < bOff + inst.m + 1 + inst.numEdges + 4 * inst.r + 6 * inst.m + 6) →
        y.mem a = x.mem a) := by
  obtain ⟨y₁, he₁, hr₁, hzero₁, hkeep₁⟩ := exec_clearAt bVisReg rr (by decide) (by decide) x
    hb.hzero hb.hone hb.hbVis hb.hrr (hfit.of_le (by omega))
  have hs₀ : ∃ y₂, ExecWithin w
      (ram[ augLen ← #0; qHead ← #0 ] : Code .standard 34) y₁ y₂ 2 ∧
      y₂ = (y₁.set augLen 0).set qHead 0 := by
    refine WP.exists_execWithin ?_
    wram_exec
    rfl
  obtain ⟨y₂, he₂, rfl⟩ := hs₀
  let y₂ := (y₁.set augLen 0).set qHead 0
  have hb₂ : BaseRegs inst bOff y₂ :=
    hb.of_eq fun i hi => by dsimp only [y₂]; wram_simp [hr₁ i (by omega)]
  have hclear_out : ∀ a, ¬(bOff + inst.m + 1 + inst.numEdges + inst.r + 3 * inst.m ≤ a ∧
      a < bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 3 * inst.m) → y₂.mem a = x.mem a :=
    fun a ha => hkeep₁ a (by omega)
  have hcsr₂ : CSRMem inst bOff y₂.mem := hcsr.of_outside fun a ha => hclear_out a (by omega)
  have hmate₂ : MateMem inst bOff mate y₂.mem :=
    hmate.of_outside fun a ha => hclear_out a (by omega)
  have hdM₂ : DistMem inst bOff dist y₂.mem := hdM.of_outside fun a ha => hclear_out a (by omega)
  have hvis₂ : VisMem inst bOff (Vector.replicate inst.r false) y₂.mem := fun v' => by
    simpa only [y₂, Data.set, vget_replicate, Bool.false_eq_true, ↓reduceIte] using
      hzero₁ v'.val v'.isLt
  have hcov₀ : VisCovers (Vector.replicate inst.r false) ([] : List (Fin inst.m × Fin inst.r)) :=
    ⟨List.nodup_nil, fun _ h => nomatch h⟩
  obtain ⟨y₃, augPairs', he₃, _, hr₃, hal₃, hcov₃, hfin₃, haug₃, hf₃⟩ :=
    exec_dfsRootsLoop hk_le [] (List.finRange inst.m) rfl (Vector.replicate inst.r false)
      [] [] hcov₀ rfl y₂ hb₂ hcsr₂ hmate₂ hdM₂ hvis₂ (fun _ hi => nomatch hi)
      (by dsimp only [y₂]; wram_simp [hr₁ rk (by decide), hrk])
      (by dsimp only [y₂]; wram_simp; rfl) (by dsimp only [y₂]; wram_simp; rfl) hfit
  have hlen_aug : augPairs'.length ≤ inst.r := hcov₃.length_le
  have hb₃ : BaseRegs inst bOff y₃ := hb₂.of_eq fun i hi => hr₃ i (by omega)
  have hmate₃ : MateMem inst bOff mate y₃.mem := hmate₂.of_outside fun a ha => hf₃ a (by omega)
  obtain ⟨y₄, he₄, hr₄, hmate₄, hf₄⟩ :=
    exec_applyAugCode augPairs' hlen_aug y₃ hb₃ hmate₃ haug₃ hal₃ hfit
  have hnd_es :
      ((hkDfsRoots inst.graph inst.adj mate dist k (List.finRange inst.m)
        (Vector.replicate inst.r false) []).map Prod.snd).Nodup :=
    hkDfsRoots_nodup_snd mate dist k (List.finRange inst.m)
      (Vector.replicate inst.r false) [] hcov₀
  have heq_apply :
      hkApplyEdges mate augPairs' = hkPhase inst.graph inst.adj mate dist k :=
    hkApplyEdges_eq_of_toFinset_eq mate hcov₃.1 hnd_es hfin₃
  rw [heq_apply] at hmate₄
  have hsum_roots :
      ((List.finRange inst.m).map (fun u => 38 * (inst.adj u).length + 49)).sum =
        38 * inst.numEdges + 49 * inst.m := by
    rw [← Fin.sum_univ_def]
    simp [SparseInstance.numEdges, bipAdjSteps, Finset.sum_add_distrib,
      ← Finset.mul_sum, Finset.sum_const, Nat.mul_comm]
  have hpot_init := dfsPot_replicate_le hM
  refine ⟨y₄, (he₁.seq (he₂.seq (he₃.seq he₄))).mono ?_,
    fun i hi => (hr₄ i hi).trans ((hr₃ i hi).trans
      (by dsimp only [y₂]; wram_simp [hr₁ i (by omega)])),
    hmate₄, fun a ha => ?_⟩
  · simp only [List.length_nil, Nat.sub_zero] at he₃
    omega
  · rw [hf₄ a (by omega), hf₃ a (by omega)]
    exact hclear_out a (by omega)

end Cslib.Algorithms.WordRAM.HopcroftKarp.Internal
