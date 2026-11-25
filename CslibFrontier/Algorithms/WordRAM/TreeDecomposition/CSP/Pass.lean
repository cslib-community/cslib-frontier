/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.TreeDecomposition.CSP.Model
public import CslibFrontier.Computability.WordRAM.Realization.ProgFrame
public import CslibFrontier.Computability.WordRAM.Realization.WordEncoding.Equiv
import CslibFrontier.Algorithms.WordRAM.TreeDecomposition.CSP.NodeStep
import CslibFrontier.Foundations.Data.List.FoldMax
import CslibFrontier.Tactic.Realize
import Mathlib.Tactic.Ring

/-!
# Bottom-up nice-tree DP pass and `runTreeCSPProg` correctness

This module proves the four structural-induction cases (`subtree_leaf`, `subtree_introduce`,
`subtree_forget`, `subtree_join`) verifying `SubtreeFullSpec` for `iterate nodeStep`, assembles the
top-level `Memory.Prog` entry point `runTreeCSPProg`, and proves its exact-basis Word-RAM
realization certificate.

## Main definitions

* `Cslib.Algorithms.WordRAM.TreeDecomposition.runTreeCSPProg`: top-level Word-RAM dynamic program.

## Main results

* `Cslib.Algorithms.WordRAM.TreeDecomposition.inputFits_encode`: input word-width fit lemma.
* `Cslib.Algorithms.WordRAM.TreeDecomposition.runTreeCSPProg_spec`: end-to-end validity, output
  equality with `TreeCSPInstance.result`, and step-cost bound `inst.stepBound`.
* `Cslib.Algorithms.WordRAM.TreeDecomposition.runTreeCSPProg_realizes`: exact-basis Word-RAM
  realization certificate.
-/

public section

namespace Cslib.Algorithms.WordRAM.TreeDecomposition

open SimpleGraph
open Cslib.Algorithms.Lean.TreeDecomposition
open Cslib.DataStructure
open Cslib.WordRAM
open Cslib.WordRAM.Realization

private theorem subtree_forget {w : ℕ} (inst : TreeCSPInstance) (hw : Fits w inst.wordBound)
    (v : ℕ) (child : NiceTree ℕ) (ih : ∀ offset s, SubtreeFullSpec w inst child offset s) :
    ∀ offset s, SubtreeFullSpec w inst (.forget v child) offset s := by
  let env := subtreeEnv inst
  let F_lo := env.descBase + 4 * inst.tree.size
  have hq : 0 < inst.domainSize := inst.domainSize_pos
  let E := maxTableExp inst.tree
  let perSpace := E + 2 + inst.domainSize ^ E
  let perCost := 16 + 4 * E + inst.vars.length + inst.domainSize ^ E *
    (E ^ 2 + E + 4 + 3 * inst.constraints.length + inst.totalArity * (2 * E + 3))
  obtain ⟨hpow_ge1, hfit_4, hfit_q, hfit_tree, hfit_total, _, hvars_lt_desc, _,
    _, hperSpace_le_total, hc_ge, hfit_tree_vert⟩ := subtree_setup inst hw
  have hfit_total' : Fits w (F_lo + inst.tree.size * perSpace) := hfit_total
  intro offset s hsz hexp hmv hwf hs_fr hfit_bud hvars htree hcons
  have hsz_ch_pos := NiceTree.size_pos child
  have hsz_ch : offset + child.size ≤ inst.tree.size := by
    simp only [NiceTree.size_forget] at hsz; omega
  have hexp_ch : maxTableExp child ≤ E := (maxTableExp_le_forget v child).trans hexp
  have hmv_ch : maxTreeVert child ≤ maxTreeVert inst.tree :=
    (maxTreeVert_le_forget v child).trans hmv
  have hfit_bud_ch : s.frontier + child.size * perSpace ≤ F_lo + inst.tree.size * perSpace := by
    have hmul_le : child.size * perSpace ≤ (NiceTree.forget v child).size * perSpace :=
      Nat.mul_le_mul_right _ (by simp [NiceTree.size_forget])
    exact le_trans (Nat.add_le_add_left hmul_le _) hfit_bud
  have htree_app := htree
  rw [encodeNiceTreeAux, HoldsIn.append_iff, length_encodeNiceTreeAux] at htree_app
  obtain ⟨htree_ch, hroot_hold⟩ := htree_app
  obtain ⟨hsafe_ch, hv_ch, hres_ch, hfr_ch, hframe_ch, hdesc_ch, hc_ch⟩ :=
    ih offset s hsz_ch hexp_ch hmv_ch hwf hs_fr hfit_bud_ch hvars htree_ch hcons
  let cur := offset + child.size
  obtain ⟨s₁, hs₁_def⟩ :
      ∃ s₁, (Memory.spec 0).clientState s (iterate nodeStep env child.size offset) = s₁ := ⟨_, rfl⟩
  rw [hs₁_def] at hfr_ch hframe_ch hdesc_ch
  have hFlo₁ : F_lo ≤ s₁.frontier := hs_fr.trans hframe_ch.1
  have hout_vars : env.varsPtr + env.varsLen ≤ env.descBase + 4 * offset :=
    hvars_lt_desc.trans (Nat.le_add_right _ _)
  have hout_root : env.treePtr + 4 * cur + [2, v, cur - 1, 0].length ≤
      env.descBase + 4 * offset := by
    simp only [List.length_cons, List.length_nil]
    change env.treePtr + 4 * (offset + child.size) + 4 ≤ env.descBase + 4 * offset
    simp only [NiceTree.size_forget] at hsz
    dsimp only [env, subtreeEnv] at *
    omega
  have hvars₁ : HoldsIn env.varsPtr inst.vars s₁ :=
    hvars.frame_outsideRange (.inl hout_vars) hframe_ch
  have hroot₁ : HoldsIn (env.treePtr + 4 * cur) [2, v, cur - 1, 0] s₁ := by
    rw [show env.treePtr + 4 * offset + 4 * child.size = env.treePtr + 4 * cur from by
      dsimp only [cur]; omega] at hroot_hold
    simpa only [cur, Nat.add_sub_cancel] using
      hroot_hold.frame_outsideRange (.inl hout_root) hframe_ch
  have hr_root := hroot₁
  rw [HoldsIn.cons_iff, HoldsIn.cons_iff, HoldsIn.cons_iff, HoldsIn.cons_iff] at hr_root
  obtain ⟨_, htag2, _, harg_v, _, hch1_eq, _, _, _⟩ := hr_root
  have hdCur_hi : env.descBase + 4 * cur + 4 ≤ F_lo := by
    simp only [NiceTree.size_forget] at hsz; dsimp only [cur, F_lo, env, subtreeEnv] at *; omega
  let LB := (bagList child).erase v
  have hLB_succ_le : LB.length + 1 ≤ E := by
    have h1 : LB.length + 1 ≤ maxTableExp (.forget v child) := le_max_left _ _
    exact h1.trans hexp
  have hcbag_len_le : (bagList child).length ≤ E :=
    (bagList_length_le_maxTableExp child).trans hexp_ch
  have hpow_ch_le : inst.domainSize ^ (bagList child).length ≤ inst.domainSize ^ E :=
    Nat.pow_le_pow_right hq hcbag_len_le
  have hpow_LB1_le : inst.domainSize ^ (LB.length + 1) ≤ inst.domainSize ^ E :=
    Nat.pow_le_pow_right hq hLB_succ_le
  have hpow_LB_le : inst.domainSize ^ LB.length ≤ inst.domainSize ^ E :=
    Nat.pow_le_pow_right hq (by omega)
  have hfit_cPow : Fits w (inst.domainSize ^ (bagList child).length) := by
    have hc_le_sp : inst.domainSize ^ (bagList child).length ≤ perSpace := by
      dsimp only [perSpace]; omega
    exact hfit_total.of_le (le_trans hc_le_sp (le_trans hperSpace_le_total (Nat.le_add_left _ _)))
  have hs₁_peak : Fits w (s₁.frontier +
      max (bagList child).length (LB.length + inst.domainSize ^ LB.length)) :=
    hfit_total'.of_le (by
      change s.frontier + (NiceTree.forget v child).size * perSpace ≤
        F_lo + inst.tree.size * perSpace at hfit_bud
      simp only [NiceTree.size_forget] at hfit_bud
      have hmx : max (bagList child).length (LB.length + inst.domainSize ^ LB.length) ≤
          perSpace :=
        max_le (by dsimp only [perSpace]; omega) (by dsimp only [perSpace]; omega)
      have hmul_bud : (child.size + 1) * perSpace = child.size * perSpace + perSpace := by ring
      change s₁.frontier ≤ s.frontier + child.size * perSpace at hfr_ch
      omega)
  have hfit_cap : Fits w
      (if inst.counting then inst.domainSize ^ (NiceTree.forget v child).size else 1) :=
    hw.of_le (by
      have hsz_le : (NiceTree.forget v child).size ≤ inst.tree.size :=
        Nat.le_trans (Nat.le_add_left _ offset) hsz
      have hpow_s := Nat.pow_le_pow_right hq hsz_le
      unfold TreeCSPInstance.wordBound TreeCSPInstance.maxEntryBound
      dsimp only
      by_cases hcnt : inst.counting = true
      · rw [ite_eq_left hcnt, ite_eq_left hcnt]; omega
      · rw [ite_eq_right hcnt, ite_eq_right hcnt]; omega)
  have hfit_bag_el := hfit_tree_vert child hmv_ch
  let fgArgs : ForgetNodeArgs :=
    ⟨env.mode, env.q, v, env.varsPtr, env.varsLen, env.descBase + 4 * (cur - 1),
      env.descBase + 4 * cur⟩
  obtain ⟨hv_fg, hfr_fg, hframe_fg, hdesc_fg, hc_fg⟩ :=
    forgetNodeProg_spec (w := w) inst.counting fgArgs hq rfl hvars₁ rfl
      hfit_bag_el hdesc_ch hdCur_hi hFlo₁ hs₁_peak hfit_cap
  have htree_lt : env.treePtr + 4 * cur + 3 < s₁.frontier := by
    have := hroot₁.1; simp only [List.length_cons, List.length_nil] at this; omega
  have hfit_vars : Fits w (env.varsPtr + env.varsLen) :=
    hfit_total.of_le (by dsimp only [F_lo, env, subtreeEnv, perSpace, E] at *; omega)
  have ht2_ne0 : s₁.mem (env.treePtr + 4 * cur) ≠ 0 := by omega
  have ht2_ne1 : s₁.mem (env.treePtr + 4 * cur) ≠ 1 := by omega
  have hsafe_root : nodeStepSafe w (env, cur) s₁ :=
    ⟨hfit_4, hfit_tree.of_le (by simp only [NiceTree.size_forget] at hsz; omega),
      hfit_total.of_le (by dsimp only [F_lo, env, subtreeEnv, perSpace, E] at *; omega),
      hfit_total.of_le (by dsimp only [F_lo, env, subtreeEnv, perSpace, E] at *; omega),
      Or.inr (Or.inr (Or.inl ⟨htag2, hq, hfit_q, hfit_vars,
        hfit_total.of_le (by
          rw [hch1_eq]; dsimp only [F_lo, env, subtreeEnv, perSpace, E] at *; omega),
        F_lo, inst.counting, child, inst.constraints, inst.vars,
        rfl, hfit_bag_el, by rw [hch1_eq]; exact hdesc_ch, hFlo₁,
        hfit_cPow, by rw [harg_v]; exact hs₁_peak, by rw [harg_v]; exact hfit_cap⟩))⟩
  have hr_s (x : ℕ) : (Memory.spec 0).clientState s₁ (Memory.read x) = s₁ := rfl
  have hr_r (x : ℕ) : (Memory.spec 0).clientResult s₁ (Memory.read x) = s₁.mem x := rfl
  have hst_root : (Memory.spec 0).clientState s₁ (nodeStep (env, cur)) =
      (Memory.spec 0).clientState s₁ (forgetNodeProg fgArgs) := by
    unfold nodeStep; dsimp only
    iterate 4 rw [StateTransitionSpec.clientState_bind, hr_s, hr_r]
    rw [ite_eq_right ht2_ne0, ite_eq_right ht2_ne1, ite_eq_left htag2,
      harg_v, hch1_eq, StateTransitionSpec.clientState_bind]
    rfl
  have hres_root : (Memory.spec 0).clientResult s₁ (nodeStep (env, cur)) = cur + 1 := by
    unfold nodeStep; dsimp only
    iterate 4 rw [StateTransitionSpec.clientResult_bind, hr_s, hr_r]
    rw [ite_eq_right ht2_ne0, ite_eq_right ht2_ne1, ite_eq_left htag2,
      StateTransitionSpec.clientResult_bind]
    rfl
  have hv_root : (Memory.spec w).ValidHistory s₁
      ((Memory.spec w).clientHistory s₁ (nodeStep (env, cur))) := by
    have hlt0 : env.treePtr + 4 * cur < s₁.frontier := lt_of_le_of_lt (by omega) htree_lt
    have hlt1 : env.treePtr + 4 * cur + 1 < s₁.frontier := lt_of_le_of_lt (by omega) htree_lt
    have hlt2 : env.treePtr + 4 * cur + 2 < s₁.frontier := lt_of_le_of_lt (by omega) htree_lt
    unfold nodeStep; dsimp only
    refine validHistory_read_bind hlt0 ?_
    refine validHistory_read_bind hlt1 ?_
    refine validHistory_read_bind hlt2 ?_
    refine validHistory_read_bind htree_lt ?_
    rw [ite_eq_right ht2_ne0, ite_eq_right ht2_ne1, ite_eq_left htag2,
      harg_v, hch1_eq]
    exact validHistory_bind_step hv_fg (validHistory_pure w _ _)
  have hcost_root : memoryCost (nodeStep (env, cur)) s₁ ≤ perCost := by
    unfold nodeStep; dsimp only
    iterate 4 rw [memoryCost_bind', memoryCost_read, hr_s, hr_r]
    rw [ite_eq_right ht2_ne0, ite_eq_right ht2_ne1, ite_eq_left htag2,
      harg_v, hch1_eq, memoryCost_bind', memoryCost_pure, Nat.add_zero]
    have hfg_mul :
        inst.domainSize ^ LB.length *
            (inst.domainSize * ((bagList child).length * (LB.length + 1) + 1) + 1) ≤
          inst.domainSize ^ E * (E ^ 2 + 2) := by
      calc inst.domainSize ^ LB.length *
            (inst.domainSize * ((bagList child).length * (LB.length + 1) + 1) + 1)
          = inst.domainSize ^ (LB.length + 1) *
              ((bagList child).length * (LB.length + 1) + 1) +
              inst.domainSize ^ LB.length := by
            rw [Nat.pow_succ]; ring
        _ ≤ inst.domainSize ^ E * (E * E + 1) + inst.domainSize ^ E := by
            refine Nat.add_le_add (Nat.mul_le_mul hpow_LB1_le ?_) hpow_LB_le
            exact Nat.add_le_add_right (Nat.mul_le_mul hcbag_len_le hLB_succ_le) 1
        _ = inst.domainSize ^ E * (E ^ 2 + 2) := by ring
    have h2_pow : 2 ≤ 2 * inst.domainSize ^ E := by
      dsimp only [E] at hpow_ge1 ⊢; omega
    have hfg_sum :
        18 + 3 * (bagList child).length + LB.length +
            inst.domainSize ^ LB.length *
              (inst.domainSize * ((bagList child).length * (LB.length + 1) + 1) + 1) ≤
          16 + 4 * E + inst.domainSize ^ E * (E ^ 2 + E + 4) := by
      have hqE_mul : inst.domainSize ^ E * (E ^ 2 + 2) + 2 * inst.domainSize ^ E ≤
          inst.domainSize ^ E * (E ^ 2 + E + 4) := by
        have : inst.domainSize ^ E * (E ^ 2 + 2) + 2 * inst.domainSize ^ E =
            inst.domainSize ^ E * (E ^ 2 + 4) := by ring
        rw [this]
        exact Nat.mul_le_mul_left _ (by omega)
      omega
    have hmul_c := hc_ge (E ^ 2 + E + 4) (by dsimp only [E]; omega)
    dsimp only [fgArgs, env, subtreeEnv, LB, perCost, E] at hc_fg hfg_sum hmul_c ⊢
    omega
  have hit_root_st : (Memory.spec 0).clientState s₁ (iterate nodeStep env 1 cur) =
      (Memory.spec 0).clientState s₁ (nodeStep (env, cur)) := by
    have hpure_st : ∀ t (x : ℕ), (Memory.spec 0).clientState t (pure x) = t := fun _ _ => rfl
    change (Memory.spec 0).clientState s₁ (nodeStep (env, cur) >>= iterate nodeStep env 0) = _
    rw [StateTransitionSpec.clientState_bind]
    exact hpure_st _ _
  have hit_root_res : (Memory.spec 0).clientResult s₁ (iterate nodeStep env 1 cur) = cur + 1 := by
    have hpure_res : ∀ t (x : ℕ), (Memory.spec 0).clientResult t (pure x) = x := fun _ _ => rfl
    change (Memory.spec 0).clientResult s₁ (nodeStep (env, cur) >>= iterate nodeStep env 0) = _
    rw [StateTransitionSpec.clientResult_bind, hres_root]
    exact hpure_res _ _
  have hv_it_root : (Memory.spec w).ValidHistory s₁
      ((Memory.spec w).clientHistory s₁ (iterate nodeStep env 1 cur)) := by
    change (Memory.spec w).ValidHistory s₁
      ((Memory.spec w).clientHistory s₁ (nodeStep (env, cur) >>= iterate nodeStep env 0))
    exact validHistory_bind_step hv_root (validHistory_pure w _ _)
  have hc_it_root : memoryCost (iterate nodeStep env 1 cur) s₁ ≤ perCost := by
    change memoryCost (nodeStep (env, cur) >>= iterate nodeStep env 0) s₁ ≤ _
    rw [memoryCost_bind', show memoryCost (iterate nodeStep env 0 _) _ = 0 from rfl, Nat.add_zero]
    exact hcost_root
  simp only [NiceTree.size_forget]
  refine ⟨iterationSafe_add nodeStep nodeStepSafe w env child.size 1 offset s hsafe_ch
      (by rw [hres_ch, hs₁_def]; exact ⟨hsafe_root, trivial⟩),
    validHistory_iterate_add nodeStep env child.size 1 offset s hv_ch
      (by dsimp only [cur]; rw [hres_ch, hs₁_def]; exact hv_it_root),
    by rw [clientResult_iterate_add, hres_ch, hs₁_def]; exact hit_root_res,
    ?_, ?_, ?_, ?_⟩
  · rw [clientState_iterate_add, hres_ch, hs₁_def, hit_root_st, hst_root]
    have hfr_le : LB.length + inst.domainSize ^ LB.length ≤ perSpace := by
      dsimp only [perSpace]; omega
    have hmul_bud : (child.size + 1) * perSpace = child.size * perSpace + perSpace := by ring
    change s₁.frontier ≤ s.frontier + child.size * perSpace at hfr_ch
    change _ ≤ s.frontier + (child.size + 1) * perSpace
    dsimp only [fgArgs, env, subtreeEnv, LB] at hfr_fg hfr_le hfr_ch ⊢
    omega
  · rw [clientState_iterate_add, hres_ch, hs₁_def]
    change FrameOutsideRange (env.descBase + 4 * offset)
      (env.descBase + 4 * (offset + (child.size + 1))) s
      ((Memory.spec 0).clientState s₁ (iterate nodeStep env 1 cur))
    rw [hit_root_st, hst_root]
    have hfr_fg' : FrameOutsideRange (env.descBase + 4 * cur)
        (env.descBase + 4 * (cur + 1)) s₁
        ((Memory.spec 0).clientState s₁ (forgetNodeProg fgArgs)) := by
      dsimp only [fgArgs] at hframe_fg
      simpa only [Nat.mul_add, Nat.mul_one, Nat.add_assoc] using hframe_fg
    simpa only [cur, env, subtreeEnv, Nat.add_assoc] using
      FrameOutsideRange.trans
        (hframe_ch.mono_range le_rfl (by dsimp only [cur, env, subtreeEnv]; omega))
        (hfr_fg'.mono_range (by dsimp only [cur, env, subtreeEnv]; omega) le_rfl)
  · rw [clientState_iterate_add, hres_ch, hs₁_def]
    change NodeDescAt F_lo inst.counting inst.domainSize inst.constraints inst.vars
      (.forget v child) (env.descBase + 4 * (offset + (child.size + 1) - 1))
      ((Memory.spec 0).clientState s₁ (iterate nodeStep env 1 cur))
    rw [hit_root_st, hst_root, show offset + (child.size + 1) - 1 = cur from by omega]
    exact hdesc_fg
  · rw [memoryCost_iterate_add, hres_ch, hs₁_def]
    change memoryCost (iterate nodeStep env child.size offset) s +
        memoryCost (iterate nodeStep env 1 cur) s₁ ≤ (child.size + 1) * perCost
    have : (child.size + 1) * perCost = child.size * perCost + perCost := by ring
    change memoryCost (iterate nodeStep env child.size offset) s ≤ child.size * perCost at hc_ch
    omega

private theorem nodeStep_join_branch {w : ℕ} (env : NodeEnv) (cur ch1 ch2 : ℕ)
    (s : Memory.State)
    (htree_lt : env.treePtr + 4 * cur + 3 < s.frontier)
    (hne0 : s.mem (env.treePtr + 4 * cur) ≠ 0)
    (hne1 : s.mem (env.treePtr + 4 * cur) ≠ 1)
    (hne2 : s.mem (env.treePtr + 4 * cur) ≠ 2)
    (hch1_eq : s.mem (env.treePtr + 4 * cur + 2) = ch1)
    (hch2_eq : s.mem (env.treePtr + 4 * cur + 3) = ch2)
    (jnArgs : JoinNodeArgs)
    (hjn : jnArgs = ⟨env.q, env.descBase + 4 * ch1, env.descBase + 4 * ch2,
      env.descBase + 4 * cur⟩)
    (hv_jn : (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (joinNodeProg jnArgs))) :
    (Memory.spec 0).clientState s (iterate nodeStep env 1 cur) =
      (Memory.spec 0).clientState s (joinNodeProg jnArgs) ∧
    (Memory.spec 0).clientResult s (iterate nodeStep env 1 cur) = cur + 1 ∧
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (iterate nodeStep env 1 cur)) ∧
    memoryCost (iterate nodeStep env 1 cur) s ≤ 4 + memoryCost (joinNodeProg jnArgs) s := by
  subst hjn
  have hr_s (x : ℕ) : (Memory.spec 0).clientState s (Memory.read x) = s := rfl
  have hr_r (x : ℕ) : (Memory.spec 0).clientResult s (Memory.read x) = s.mem x := rfl
  have hlt0 : env.treePtr + 4 * cur < s.frontier := lt_of_le_of_lt (by omega) htree_lt
  have hlt1 : env.treePtr + 4 * cur + 1 < s.frontier := lt_of_le_of_lt (by omega) htree_lt
  have hlt2 : env.treePtr + 4 * cur + 2 < s.frontier := lt_of_le_of_lt (by omega) htree_lt
  have hst : (Memory.spec 0).clientState s (nodeStep (env, cur)) =
      (Memory.spec 0).clientState s (joinNodeProg ⟨env.q, env.descBase + 4 * ch1,
        env.descBase + 4 * ch2, env.descBase + 4 * cur⟩) := by
    unfold nodeStep; dsimp only
    iterate 4 rw [StateTransitionSpec.clientState_bind, hr_s, hr_r]
    rw [ite_eq_right hne0, ite_eq_right hne1, ite_eq_right hne2,
      hch1_eq, hch2_eq, StateTransitionSpec.clientState_bind]
    rfl
  have hres : (Memory.spec 0).clientResult s (nodeStep (env, cur)) = cur + 1 := by
    unfold nodeStep; dsimp only
    iterate 4 rw [StateTransitionSpec.clientResult_bind, hr_s, hr_r]
    rw [ite_eq_right hne0, ite_eq_right hne1, ite_eq_right hne2,
      StateTransitionSpec.clientResult_bind]
    rfl
  have hv : (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (nodeStep (env, cur))) := by
    unfold nodeStep; dsimp only
    refine validHistory_read_bind hlt0 ?_
    refine validHistory_read_bind hlt1 ?_
    refine validHistory_read_bind hlt2 ?_
    refine validHistory_read_bind htree_lt ?_
    rw [ite_eq_right hne0, ite_eq_right hne1, ite_eq_right hne2, hch1_eq, hch2_eq]
    exact validHistory_bind_step hv_jn (validHistory_pure w _ _)
  have hcost : memoryCost (nodeStep (env, cur)) s ≤
      4 + memoryCost (joinNodeProg ⟨env.q, env.descBase + 4 * ch1,
        env.descBase + 4 * ch2, env.descBase + 4 * cur⟩) s := by
    unfold nodeStep; dsimp only
    iterate 4 rw [memoryCost_bind', memoryCost_read, hr_s, hr_r]
    rw [ite_eq_right hne0, ite_eq_right hne1, ite_eq_right hne2,
      hch1_eq, hch2_eq, memoryCost_bind', memoryCost_pure, Nat.add_zero]
    omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · change (Memory.spec 0).clientState s (nodeStep (env, cur) >>= iterate nodeStep env 0) = _
    rw [StateTransitionSpec.clientState_bind]; exact hst
  · change (Memory.spec 0).clientResult s (nodeStep (env, cur) >>= iterate nodeStep env 0) = _
    rw [StateTransitionSpec.clientResult_bind, hres]; rfl
  · change (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (nodeStep (env, cur) >>= iterate nodeStep env 0))
    exact validHistory_bind_step hv (validHistory_pure w _ _)
  · change memoryCost (nodeStep (env, cur) >>= iterate nodeStep env 0) s ≤ _
    rw [memoryCost_bind', show memoryCost (iterate nodeStep env 0 _) _ = 0 from rfl, Nat.add_zero]
    exact hcost

private theorem subtree_join_step {w : ℕ} (inst : TreeCSPInstance) (hw : Fits w inst.wordBound)
    (left right : NiceTree ℕ) (offset mid cur : ℕ) (s₂ : Memory.State)
    (hsz : offset + (NiceTree.join left right).size ≤ inst.tree.size)
    (hexp_l : maxTableExp left ≤ maxTableExp inst.tree)
    (hexp_r : maxTableExp right ≤ maxTableExp inst.tree)
    (hmid : mid = offset + left.size)
    (hcur : cur = mid + right.size)
    (hFlo₂ : (subtreeEnv inst).descBase + 4 * inst.tree.size ≤ s₂.frontier)
    (hfr_bound : s₂.frontier + inst.domainSize ^ (bagList left).length ≤
      (subtreeEnv inst).descBase + 4 * inst.tree.size +
        inst.tree.size * (maxTableExp inst.tree + 2 + inst.domainSize ^ maxTableExp inst.tree))
    (hroot₂ : HoldsIn ((subtreeEnv inst).treePtr + 4 * cur) [3, 0, mid - 1, cur - 1] s₂)
    (hdesc_l₂ : NodeDescAt ((subtreeEnv inst).descBase + 4 * inst.tree.size)
      inst.counting inst.domainSize inst.constraints inst.vars left
      ((subtreeEnv inst).descBase + 4 * (mid - 1)) s₂)
    (hdesc_r : NodeDescAt ((subtreeEnv inst).descBase + 4 * inst.tree.size)
      inst.counting inst.domainSize inst.constraints inst.vars right
      ((subtreeEnv inst).descBase + 4 * (cur - 1)) s₂) :
    nodeStepSafe w (subtreeEnv inst, cur) s₂ ∧
    (Memory.spec w).ValidHistory s₂
      ((Memory.spec w).clientHistory s₂ (iterate nodeStep (subtreeEnv inst) 1 cur)) ∧
    (Memory.spec 0).clientResult s₂ (iterate nodeStep (subtreeEnv inst) 1 cur) = cur + 1 ∧
    ((Memory.spec 0).clientState s₂ (iterate nodeStep (subtreeEnv inst) 1 cur)).frontier ≤
      s₂.frontier + inst.domainSize ^ (bagList left).length ∧
    FrameOutsideRange ((subtreeEnv inst).descBase + 4 * cur)
      ((subtreeEnv inst).descBase + 4 * (cur + 1)) s₂
      ((Memory.spec 0).clientState s₂ (iterate nodeStep (subtreeEnv inst) 1 cur)) ∧
    NodeDescAt ((subtreeEnv inst).descBase + 4 * inst.tree.size)
      inst.counting inst.domainSize inst.constraints inst.vars (.join left right)
      ((subtreeEnv inst).descBase + 4 * cur)
      ((Memory.spec 0).clientState s₂ (iterate nodeStep (subtreeEnv inst) 1 cur)) ∧
    memoryCost (iterate nodeStep (subtreeEnv inst) 1 cur) s₂ ≤
      16 + 4 * maxTableExp inst.tree + inst.vars.length +
        inst.domainSize ^ maxTableExp inst.tree *
          (maxTableExp inst.tree ^ 2 + maxTableExp inst.tree + 4 +
            3 * inst.constraints.length + inst.totalArity * (2 * maxTableExp inst.tree + 3)) := by
  let env := subtreeEnv inst
  let F_lo := env.descBase + 4 * inst.tree.size
  have hq : 0 < inst.domainSize := inst.domainSize_pos
  let E := maxTableExp inst.tree
  let perSpace := E + 2 + inst.domainSize ^ E
  let perCost := 16 + 4 * E + inst.vars.length + inst.domainSize ^ E *
    (E ^ 2 + E + 4 + 3 * inst.constraints.length + inst.totalArity * (2 * E + 3))
  obtain ⟨_, hfit_4, hfit_q, hfit_tree, hfit_total, _, _, _,
    _, hperSpace_le_total, hc_ge, _⟩ := subtree_setup inst hw
  have hsz_l_pos := NiceTree.size_pos left
  have hsz_r_pos := NiceTree.size_pos right
  have hr_root := hroot₂
  change HoldsIn (env.treePtr + 4 * cur) [3, 0, mid - 1, cur - 1] s₂ at hr_root
  rw [HoldsIn.cons_iff, HoldsIn.cons_iff, HoldsIn.cons_iff, HoldsIn.cons_iff] at hr_root
  obtain ⟨_, htag3, _, _, _, hch1_eq, _, hch2_eq, _⟩ := hr_root
  have hdCur_hi : env.descBase + 4 * cur + 4 ≤ F_lo := by
    simp only [NiceTree.size_join] at hsz; dsimp only [F_lo, env, subtreeEnv] at *; omega
  have hllen_le : (bagList left).length ≤ E :=
    (bagList_length_le_maxTableExp left).trans hexp_l
  have hrlen_le : (bagList right).length ≤ E :=
    (bagList_length_le_maxTableExp right).trans hexp_r
  have hpow_l_le : inst.domainSize ^ (bagList left).length ≤ inst.domainSize ^ E :=
    Nat.pow_le_pow_right hq hllen_le
  have hfit_rPow : Fits w (inst.domainSize ^ (bagList right).length) := by
    have hpow_r_le : inst.domainSize ^ (bagList right).length ≤ inst.domainSize ^ E :=
      Nat.pow_le_pow_right hq hrlen_le
    have hr_le_sp : inst.domainSize ^ (bagList right).length ≤ perSpace := by
      dsimp only [perSpace]; omega
    exact hfit_total.of_le (le_trans hr_le_sp (le_trans hperSpace_le_total (Nat.le_add_left _ _)))
  have hs₂_peak : Fits w (s₂.frontier + inst.domainSize ^ (bagList left).length) :=
    hfit_total.of_le hfr_bound
  have hfit_cap : Fits w
      (if inst.counting then inst.domainSize ^ (NiceTree.join left right).size else 1) :=
    hw.of_le (by
      have hsz_le : (NiceTree.join left right).size ≤ inst.tree.size :=
        Nat.le_trans (Nat.le_add_left _ offset) hsz
      have hpow_s := Nat.pow_le_pow_right hq hsz_le
      unfold TreeCSPInstance.wordBound TreeCSPInstance.maxEntryBound
      dsimp only
      by_cases hcnt : inst.counting = true
      · rw [ite_eq_left hcnt, ite_eq_left hcnt]; omega
      · rw [ite_eq_right hcnt, ite_eq_right hcnt]; omega)
  let jnArgs : JoinNodeArgs :=
    ⟨env.q, env.descBase + 4 * (mid - 1), env.descBase + 4 * (cur - 1), env.descBase + 4 * cur⟩
  obtain ⟨hv_jn, hfr_jn, hframe_jn, hdesc_jn, hc_jn⟩ :=
    joinNodeProg_spec (w := w) inst.counting jnArgs hq hdesc_l₂ hdesc_r hdCur_hi hFlo₂
      hs₂_peak hfit_cap
  have htree_lt : env.treePtr + 4 * cur + 3 < s₂.frontier := by
    have := hroot₂.1; simp only [List.length_cons, List.length_nil] at this; omega
  have hne0 : s₂.mem (env.treePtr + 4 * cur) ≠ 0 := by omega
  have hne1 : s₂.mem (env.treePtr + 4 * cur) ≠ 1 := by omega
  have hne2 : s₂.mem (env.treePtr + 4 * cur) ≠ 2 := by omega
  have hsafe_root : nodeStepSafe w (env, cur) s₂ :=
    ⟨hfit_4, hfit_tree.of_le (by simp only [NiceTree.size_join] at hsz; omega),
      hfit_total.of_le (by dsimp only [F_lo, env, subtreeEnv, perSpace, E] at *; omega),
      hfit_total.of_le (by dsimp only [F_lo, env, subtreeEnv, perSpace, E] at *; omega),
      Or.inr (Or.inr (Or.inr ⟨hne0, hne1, hne2, hq, hfit_q,
        hfit_total.of_le (by
          rw [hch1_eq]; dsimp only [F_lo, env, subtreeEnv, perSpace, E] at *; omega),
        hfit_total.of_le (by
          rw [hch2_eq]; dsimp only [F_lo, env, subtreeEnv, perSpace, E] at *; omega),
        F_lo, inst.counting, left, right, inst.constraints, inst.vars,
        by rw [hch1_eq]; exact hdesc_l₂, by rw [hch2_eq]; exact hdesc_r,
        hfit_rPow, hs₂_peak, hfit_cap⟩))⟩
  obtain ⟨hit_root_st, hit_root_res, hv_it_root, hcost_br⟩ :=
    nodeStep_join_branch env cur (mid - 1) (cur - 1) s₂ htree_lt hne0 hne1 hne2
      hch1_eq hch2_eq jnArgs rfl hv_jn
  have hc_it_root : memoryCost (iterate nodeStep env 1 cur) s₂ ≤ perCost := by
    have hjn_mul :
        inst.domainSize ^ (bagList left).length *
            ((bagList right).length * ((bagList left).length + 1) + 3) ≤
          inst.domainSize ^ E * (E ^ 2 + E + 4) := by
      refine Nat.mul_le_mul hpow_l_le ?_
      have hmul_lr : (bagList right).length * ((bagList left).length + 1) ≤ E * (E + 1) :=
        Nat.mul_le_mul hrlen_le (Nat.add_le_add_right hllen_le 1)
      have hsq : E * (E + 1) = E ^ 2 + E := by ring
      omega
    have hmul_c := hc_ge (E ^ 2 + E + 4) (by dsimp only [E]; omega)
    dsimp only [jnArgs, env, subtreeEnv, perCost, E] at hc_jn hcost_br hjn_mul hmul_c ⊢
    omega
  have hfr_jn' : FrameOutsideRange (env.descBase + 4 * cur) (env.descBase + 4 * (cur + 1)) s₂
      ((Memory.spec 0).clientState s₂ (joinNodeProg jnArgs)) := by
    dsimp only [jnArgs] at hframe_jn
    simpa only [Nat.mul_add, Nat.mul_one, Nat.add_assoc] using hframe_jn
  refine ⟨hsafe_root, hv_it_root, hit_root_res, ?_, ?_, ?_, hc_it_root⟩
  · rw [hit_root_st]; exact hfr_jn
  · rw [hit_root_st]; exact hfr_jn'
  · rw [hit_root_st]; exact hdesc_jn

private theorem subtree_join {w : ℕ} (inst : TreeCSPInstance) (hw : Fits w inst.wordBound)
    (left right : NiceTree ℕ)
    (ihl : ∀ offset s, SubtreeFullSpec w inst left offset s)
    (ihr : ∀ offset s, SubtreeFullSpec w inst right offset s) :
    ∀ offset s, SubtreeFullSpec w inst (.join left right) offset s := by
  let env := subtreeEnv inst
  let F_lo := env.descBase + 4 * inst.tree.size
  have hq : 0 < inst.domainSize := inst.domainSize_pos
  let E := maxTableExp inst.tree
  let perSpace := E + 2 + inst.domainSize ^ E
  let perCost := 16 + 4 * E + inst.vars.length + inst.domainSize ^ E *
    (E ^ 2 + E + 4 + 3 * inst.constraints.length + inst.totalArity * (2 * E + 3))
  obtain ⟨_, _, _, _, _, _, hvars_lt_desc, hcons_lt_desc, _, _, _, _⟩ := subtree_setup inst hw
  intro offset s hsz hexp hmv hwf hs_fr hfit_bud hvars htree hcons
  have hsz_l_pos := NiceTree.size_pos left
  have hsz_r_pos := NiceTree.size_pos right
  have hsz_l : offset + left.size ≤ inst.tree.size := by
    simp only [NiceTree.size_join] at hsz; omega
  have hsz_r : (offset + left.size) + right.size ≤ inst.tree.size := by
    simp only [NiceTree.size_join] at hsz; omega
  have hexp_l : maxTableExp left ≤ E := (maxTableExp_le_join_left left right).trans hexp
  have hexp_r : maxTableExp right ≤ E := (maxTableExp_le_join_right left right).trans hexp
  have hmv_l : maxTreeVert left ≤ maxTreeVert inst.tree :=
    (maxTreeVert_le_join_left left right).trans hmv
  have hmv_r : maxTreeVert right ≤ maxTreeVert inst.tree :=
    (maxTreeVert_le_join_right left right).trans hmv
  have hfit_bud_l : s.frontier + left.size * perSpace ≤ F_lo + inst.tree.size * perSpace := by
    have hmul_le : left.size * perSpace ≤ (NiceTree.join left right).size * perSpace :=
      Nat.mul_le_mul_right _ (by simp [NiceTree.size_join]; omega)
    exact le_trans (Nat.add_le_add_left hmul_le _) hfit_bud
  have htree_app := htree
  rw [encodeNiceTreeAux, List.append_assoc, HoldsIn.append_iff, length_encodeNiceTreeAux,
    HoldsIn.append_iff, length_encodeNiceTreeAux] at htree_app
  obtain ⟨htree_l, htree_r0, hroot_hold⟩ := htree_app
  obtain ⟨hsafe_l, hv_l, hres_l, hfr_l, hframe_l, hdesc_l, hc_l⟩ :=
    ihl offset s hsz_l hexp_l hmv_l hwf hs_fr hfit_bud_l hvars htree_l hcons
  let mid := offset + left.size
  obtain ⟨s₁, hs₁_def⟩ : ∃ s₁,
      (Memory.spec 0).clientState s (iterate nodeStep env left.size offset) = s₁ := ⟨_, rfl⟩
  rw [hs₁_def] at hfr_l hframe_l hdesc_l
  have hwf₁ : Memory.WellFormed w s₁ := by
    rw [← hs₁_def]
    exact wellFormed_clientState hwf hv_l
  have hFlo₁ : F_lo ≤ s₁.frontier := hs_fr.trans hframe_l.1
  have hout_vars₁ : env.varsPtr + env.varsLen ≤ env.descBase + 4 * offset :=
    hvars_lt_desc.trans (Nat.le_add_right _ _)
  have hout_cons₁ : env.consRawPtr + (inst.constraints.flatMap ConstraintTable.encode).length ≤
      env.descBase + 4 * offset :=
    hcons_lt_desc.trans (Nat.le_add_right _ _)
  have hout_tr₁ : env.treePtr + 4 * mid + (encodeNiceTreeAux mid right).length ≤
      env.descBase + 4 * offset := by
    rw [length_encodeNiceTreeAux]
    simp only [NiceTree.size_join] at hsz
    dsimp only [mid, env, subtreeEnv] at *
    omega
  have hout_root₁ : env.treePtr + 4 * (mid + right.size) +
      [3, 0, mid - 1, mid + right.size - 1].length ≤ env.descBase + 4 * offset := by
    simp only [List.length_cons, List.length_nil]
    simp only [NiceTree.size_join] at hsz
    dsimp only [mid, env, subtreeEnv] at *
    omega
  have hvars₁ : HoldsIn env.varsPtr inst.vars s₁ :=
    hvars.frame_outsideRange (.inl hout_vars₁) hframe_l
  have hcons₁ : HoldsIn env.consRawPtr (inst.constraints.flatMap ConstraintTable.encode) s₁ :=
    hcons.frame_outsideRange (.inl hout_cons₁) hframe_l
  have htree_r₁ : HoldsIn (env.treePtr + 4 * mid) (encodeNiceTreeAux mid right) s₁ := by
    rw [show env.treePtr + 4 * offset + 4 * left.size = env.treePtr + 4 * mid from by
      dsimp only [mid]; omega] at htree_r0
    exact htree_r0.frame_outsideRange (.inl hout_tr₁) hframe_l
  have hroot₁ : HoldsIn (env.treePtr + 4 * (mid + right.size))
      [3, 0, mid - 1, mid + right.size - 1] s₁ := by
    rw [show env.treePtr + 4 * offset + 4 * left.size + 4 * right.size =
      env.treePtr + 4 * (mid + right.size) from by dsimp only [mid]; omega] at hroot_hold
    exact hroot_hold.frame_outsideRange (.inl hout_root₁) hframe_l
  have hfit_bud_r : s₁.frontier + right.size * perSpace ≤ F_lo + inst.tree.size * perSpace := by
    change s.frontier + (NiceTree.join left right).size * perSpace ≤
      F_lo + inst.tree.size * perSpace at hfit_bud
    simp only [NiceTree.size_join] at hfit_bud
    have hmul_sum : (left.size + right.size + 1) * perSpace =
        left.size * perSpace + right.size * perSpace + perSpace := by ring
    change s₁.frontier ≤ s.frontier + left.size * perSpace at hfr_l
    omega
  obtain ⟨hsafe_r, hv_r, hres_r, hfr_r, hframe_r, hdesc_r, hc_r⟩ :=
    ihr mid s₁ hsz_r hexp_r hmv_r hwf₁ hFlo₁ hfit_bud_r hvars₁ htree_r₁ hcons₁
  let cur := mid + right.size
  obtain ⟨s₂, hs₂_def⟩ : ∃ s₂,
      (Memory.spec 0).clientState s₁ (iterate nodeStep env right.size mid) = s₂ := ⟨_, rfl⟩
  rw [hs₂_def] at hfr_r hframe_r hdesc_r
  have hFlo₂ : F_lo ≤ s₂.frontier := hFlo₁.trans hframe_r.1
  have hout_root₂ : env.treePtr + 4 * cur + [3, 0, mid - 1, cur - 1].length ≤
      env.descBase + 4 * mid := by
    simp only [List.length_cons, List.length_nil]
    simp only [NiceTree.size_join] at hsz
    dsimp only [cur, mid, env, subtreeEnv] at *
    omega
  have hroot₂ : HoldsIn (env.treePtr + 4 * cur) [3, 0, mid - 1, cur - 1] s₂ :=
    hroot₁.frame_outsideRange (.inl hout_root₂) hframe_r
  have hdesc_l₂ : NodeDescAt F_lo inst.counting inst.domainSize inst.constraints inst.vars left
      (env.descBase + 4 * (mid - 1)) s₂ :=
    hdesc_l.frame (.inl (by dsimp only [mid]; omega))
      (by
        dsimp only [F_lo, mid, env, subtreeEnv] at *
        simp only [NiceTree.size_join] at hsz; omega)
      hframe_r
  have hllen_le : (bagList left).length ≤ E :=
    (bagList_length_le_maxTableExp left).trans hexp_l
  have hpow_l_le : inst.domainSize ^ (bagList left).length ≤ inst.domainSize ^ E :=
    Nat.pow_le_pow_right hq hllen_le
  have hfr_bound : s₂.frontier + inst.domainSize ^ (bagList left).length ≤
      F_lo + inst.tree.size * perSpace := by
    change s.frontier + (NiceTree.join left right).size * perSpace ≤
      F_lo + inst.tree.size * perSpace at hfit_bud
    simp only [NiceTree.size_join] at hfit_bud
    have hmul_sum : (left.size + right.size + 1) * perSpace =
        left.size * perSpace + right.size * perSpace + perSpace := by ring
    have : inst.domainSize ^ (bagList left).length ≤ perSpace := by
      dsimp only [perSpace]; omega
    change s₁.frontier ≤ s.frontier + left.size * perSpace at hfr_l
    change s₂.frontier ≤ s₁.frontier + right.size * perSpace at hfr_r
    omega
  obtain ⟨hsafe_root, hv_it_root, hit_root_res, hfr_root, hframe_root, hdesc_root, hc_it_root⟩ :=
    subtree_join_step inst hw left right offset mid cur s₂ hsz hexp_l hexp_r rfl rfl
      hFlo₂ hfr_bound hroot₂ hdesc_l₂ hdesc_r
  have hsafe_lr : iterationSafe nodeStep nodeStepSafe w env (left.size + right.size) offset s :=
    iterationSafe_add nodeStep nodeStepSafe w env left.size right.size offset s hsafe_l
      (by rw [hres_l, hs₁_def]; exact hsafe_r)
  have hv_lr : (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (iterate nodeStep env (left.size + right.size) offset)) :=
    validHistory_iterate_add nodeStep env left.size right.size offset s hv_l
      (by dsimp only; rw [hs₁_def, hres_l]; exact hv_r)
  have hres_lr : (Memory.spec 0).clientResult s
      (iterate nodeStep env (left.size + right.size) offset) = cur := by
    rw [clientResult_iterate_add, hres_l, hs₁_def]; exact hres_r
  have hst_lr : (Memory.spec 0).clientState s
      (iterate nodeStep env (left.size + right.size) offset) = s₂ := by
    rw [clientState_iterate_add, hres_l, hs₁_def, hs₂_def]
  simp only [NiceTree.size_join]
  refine ⟨iterationSafe_add nodeStep nodeStepSafe w env (left.size + right.size) 1 offset s
      hsafe_lr (by
        rw [hst_lr, hres_lr, show env = subtreeEnv inst from rfl]
        exact ⟨hsafe_root, trivial⟩),
    validHistory_iterate_add nodeStep env (left.size + right.size) 1 offset s hv_lr
      (by
        dsimp only
        rw [hst_lr, hres_lr, show env = subtreeEnv inst from rfl]
        exact hv_it_root),
    by
      rw [clientResult_iterate_add, hres_lr, hst_lr, hit_root_res]
      dsimp only [cur, mid]
      omega,
    ?_, ?_, ?_, ?_⟩
  · rw [clientState_iterate_add, hres_lr, hst_lr]
    have hfr_le : inst.domainSize ^ (bagList left).length ≤ perSpace := by
      dsimp only [perSpace]; omega
    have hsum_sp : (left.size + right.size + 1) * perSpace =
        left.size * perSpace + right.size * perSpace + perSpace := by ring
    dsimp only [perSpace, E] at hfr_le hsum_sp
    omega
  · rw [clientState_iterate_add, hres_lr, hst_lr]
    change FrameOutsideRange (env.descBase + 4 * offset)
      (env.descBase + 4 * (offset + (left.size + right.size + 1))) s
      ((Memory.spec 0).clientState s₂ (iterate nodeStep env 1 cur))
    rw [show env = subtreeEnv inst from rfl]
    have hfr_lr : FrameOutsideRange ((subtreeEnv inst).descBase + 4 * offset)
        ((subtreeEnv inst).descBase + 4 * cur) s s₂ :=
      FrameOutsideRange.trans
        (hframe_l.mono_range le_rfl (by dsimp only [mid, cur, env, subtreeEnv]; omega))
        (hframe_r.mono_range (by dsimp only [mid, env, subtreeEnv]; omega) le_rfl)
    rw [show (subtreeEnv inst).descBase + 4 * (offset + (left.size + right.size + 1)) =
        (subtreeEnv inst).descBase + 4 * (cur + 1) from by dsimp only [cur, mid]; omega]
    exact FrameOutsideRange.trans
      (hfr_lr.mono_range le_rfl (by dsimp only [cur, mid]; omega))
      (hframe_root.mono_range (by dsimp only [cur, mid]; omega) le_rfl)
  · rw [clientState_iterate_add, hres_lr, hst_lr]
    rw [show offset + (left.size + right.size + 1) - 1 = cur from by dsimp only [cur, mid]; omega]
    exact hdesc_root
  · rw [memoryCost_iterate_add, hres_lr, hst_lr]
    have hs₁_def' : (Memory.spec 0).clientState s
        (iterate nodeStep (subtreeEnv inst) left.size offset) = s₁ := hs₁_def
    have hc_lr :
        memoryCost (iterate nodeStep (subtreeEnv inst) (left.size + right.size) offset) s =
          memoryCost (iterate nodeStep (subtreeEnv inst) left.size offset) s +
            memoryCost (iterate nodeStep (subtreeEnv inst) right.size mid) s₁ := by
      rw [memoryCost_iterate_add, hres_l, hs₁_def']
    rw [hc_lr]
    have hsum_c : (left.size + right.size + 1) * perCost =
        left.size * perCost + right.size * perCost + perCost := by ring
    dsimp only [perCost, E] at hc_it_root hsum_c ⊢
    omega

private theorem subtree_leaf {w : ℕ} (inst : TreeCSPInstance) (hw : Fits w inst.wordBound) :
    ∀ offset s, SubtreeFullSpec w inst .leaf offset s := by
  let env := subtreeEnv inst
  let F_lo := env.descBase + 4 * inst.tree.size
  have hq : 0 < inst.domainSize := inst.domainSize_pos
  let E := maxTableExp inst.tree
  let perSpace := E + 2 + inst.domainSize ^ E
  let perCost := 16 + 4 * E + inst.vars.length + inst.domainSize ^ E *
    (E ^ 2 + E + 4 + 3 * inst.constraints.length + inst.totalArity * (2 * E + 3))
  obtain ⟨hpow_ge1, hfit_4, hfit_q, hfit_tree, hfit_total, hcons_len_bound, _, _,
    _, _, hc_ge, _⟩ := subtree_setup inst hw
  have hfit_total' : Fits w (F_lo + inst.tree.size * perSpace) := hfit_total
  intro offset s hsz _ _ _ hs_fr hfit_bud _ htree hcons
  have ht_eq := htree
  rw [encodeNiceTreeAux, HoldsIn.cons_iff, HoldsIn.cons_iff, HoldsIn.cons_iff,
    HoldsIn.cons_iff] at ht_eq
  obtain ⟨_, htag0, _, _, _, _, _, _, _⟩ := ht_eq
  have hdCur_hi : env.descBase + 4 * offset + 4 ≤ F_lo := by
    simp only [NiceTree.size_leaf] at hsz; dsimp only [F_lo, env, subtreeEnv] at *; omega
  have hs_fr1 : Fits w (s.frontier + 1) := hfit_total'.of_le (by
    have : 1 ≤ perSpace := by dsimp only [perSpace]; omega
    change s.frontier + NiceTree.size .leaf * perSpace ≤
      F_lo + inst.tree.size * perSpace at hfit_bud
    simp only [NiceTree.size_leaf, Nat.one_mul] at hfit_bud
    omega)
  have htree_lt : env.treePtr + 4 * offset + 3 < s.frontier := by
    have := htree.1; simp only [length_encodeNiceTreeAux, NiceTree.size_leaf] at this
    dsimp only [env, subtreeEnv] at this ⊢; omega
  let leafArgs : LeafNodeArgs := ⟨env.consRawPtr, env.numCons, env.descBase + 4 * offset⟩
  obtain ⟨hv_lf, hfr_lf, hframe_lf, hdesc_lf, hc_lf⟩ :=
    leafNodeProg_spec (w := w) inst.counting hq leafArgs (vars := inst.vars) hcons rfl hdCur_hi
      hs_fr hs_fr1
  have hcons_fit : Fits w (env.consRawPtr +
      (inst.constraints.flatMap ConstraintTable.encode).length) :=
    hw.of_le (by
      rw [hcons_len_bound]; dsimp only [env, subtreeEnv]
      unfold TreeCSPInstance.wordBound; dsimp only; omega)
  have hsafe0 : nodeStepSafe w (env, offset) s := by
    refine ⟨hfit_4, hfit_tree.of_le (by simp only [NiceTree.size_leaf] at hsz; exact hsz),
      hfit_total.of_le (by dsimp only [F_lo, env, subtreeEnv, perSpace, E] at *; omega),
      hfit_total.of_le (by dsimp only [F_lo, env, subtreeEnv, perSpace, E] at *; omega),
      Or.inl ⟨htag0, inst.domainSize, inst.constraints, hq, rfl, hcons, hcons_fit⟩⟩
  have hr_s (x : ℕ) : (Memory.spec 0).clientState s (Memory.read x) = s := rfl
  have hr_r (x : ℕ) : (Memory.spec 0).clientResult s (Memory.read x) = s.mem x := rfl
  have hst1 : (Memory.spec 0).clientState s (nodeStep (env, offset)) =
      (Memory.spec 0).clientState s (leafNodeProg leafArgs) := by
    unfold nodeStep; dsimp only
    iterate 4 rw [StateTransitionSpec.clientState_bind, hr_s, hr_r]
    rw [ite_eq_left htag0, StateTransitionSpec.clientState_bind]
    rfl
  have hres1 : (Memory.spec 0).clientResult s (nodeStep (env, offset)) = offset + 1 := by
    unfold nodeStep; dsimp only
    iterate 4 rw [StateTransitionSpec.clientResult_bind, hr_s, hr_r]
    rw [ite_eq_left htag0, StateTransitionSpec.clientResult_bind]
    rfl
  have hv1 : (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (nodeStep (env, offset))) := by
    unfold nodeStep; dsimp only
    refine validHistory_read_bind (by omega) ?_
    refine validHistory_read_bind (by omega) ?_
    refine validHistory_read_bind (by omega) ?_
    refine validHistory_read_bind (by omega) ?_
    rw [ite_eq_left htag0]
    exact validHistory_bind_step hv_lf (validHistory_pure w _ _)
  have hcost1 : memoryCost (nodeStep (env, offset)) s ≤ 1 * perCost := by
    unfold nodeStep; dsimp only
    iterate 4 rw [memoryCost_bind', memoryCost_read, hr_s, hr_r]
    rw [ite_eq_left htag0, memoryCost_bind', memoryCost_pure, Nat.add_zero]
    have hmul_nc : 3 * inst.constraints.length ≤
        inst.domainSize ^ E *
          (E ^ 2 + E + 4 + 3 * inst.constraints.length + inst.totalArity * (2 * E + 3)) :=
      (Nat.le_mul_of_pos_left _ hpow_ge1).trans
        (hc_ge (3 * inst.constraints.length) (by omega))
    dsimp only [leafArgs, env, subtreeEnv, perCost] at hc_lf ⊢
    omega
  have hfr1' : ((Memory.spec 0).clientState s (nodeStep (env, offset))).frontier ≤
      s.frontier + 1 * perSpace := by
    rw [hst1]
    exact hfr_lf.trans (by dsimp only [perSpace]; omega)
  have hit1 : (Memory.spec 0).clientState s (iterate nodeStep env 1 offset) =
      (Memory.spec 0).clientState s (nodeStep (env, offset)) := by
    change (Memory.spec 0).clientState s (nodeStep (env, offset) >>= iterate nodeStep env 0) = _
    rw [StateTransitionSpec.clientState_bind]; rfl
  have hres_it1 : (Memory.spec 0).clientResult s (iterate nodeStep env 1 offset) = offset + 1 := by
    change (Memory.spec 0).clientResult s (nodeStep (env, offset) >>= iterate nodeStep env 0) = _
    rw [StateTransitionSpec.clientResult_bind, hres1]; rfl
  have hv_it1 : (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (iterate nodeStep env 1 offset)) := by
    change (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (nodeStep (env, offset) >>= iterate nodeStep env 0))
    exact validHistory_bind_step hv1 (validHistory_pure w _ _)
  have hc_it1 : memoryCost (iterate nodeStep env 1 offset) s ≤ 1 * perCost := by
    change memoryCost (nodeStep (env, offset) >>= iterate nodeStep env 0) s ≤ _
    rw [memoryCost_bind', show memoryCost (iterate nodeStep env 0 _) _ = 0 from rfl, Nat.add_zero]
    exact hcost1
  simp only [NiceTree.size_leaf]
  refine ⟨⟨hsafe0, trivial⟩, hv_it1, hres_it1, by rw [hit1]; exact hfr1', ?_, ?_, hc_it1⟩
  · rw [hit1, hst1]
    dsimp only [leafArgs, env, subtreeEnv] at hframe_lf ⊢
    simpa only [Nat.mul_add, Nat.mul_one, Nat.add_assoc] using hframe_lf
  · rw [hit1, hst1, Nat.add_sub_cancel]
    exact hdesc_lf

private theorem subtree_introduce {w : ℕ} (inst : TreeCSPInstance) (hw : Fits w inst.wordBound)
    (v : ℕ) (child : NiceTree ℕ) (ih : ∀ offset s, SubtreeFullSpec w inst child offset s) :
    ∀ offset s, SubtreeFullSpec w inst (.introduce v child) offset s := by
  let env := subtreeEnv inst
  let F_lo := env.descBase + 4 * inst.tree.size
  have hq : 0 < inst.domainSize := inst.domainSize_pos
  let E := maxTableExp inst.tree
  let perSpace := E + 2 + inst.domainSize ^ E
  let perCost := 16 + 4 * E + inst.vars.length + inst.domainSize ^ E *
    (E ^ 2 + E + 4 + 3 * inst.constraints.length + inst.totalArity * (2 * E + 3))
  obtain ⟨_, hfit_4, hfit_q, hfit_tree, hfit_total, _, hvars_lt_desc, hcons_lt_desc,
    _, _, _, _⟩ := subtree_setup inst hw
  have hfit_total' : Fits w (F_lo + inst.tree.size * perSpace) := hfit_total
  intro offset s hsz hexp hmv hwf hs_fr hfit_bud hvars htree hcons
  have hsz_ch_pos := NiceTree.size_pos child
  have hsz_ch : offset + child.size ≤ inst.tree.size := by
    simp only [NiceTree.size_introduce] at hsz; omega
  have hexp_ch : maxTableExp child ≤ E := (maxTableExp_le_introduce v child).trans hexp
  have hmv_ch : maxTreeVert child ≤ maxTreeVert inst.tree :=
    (maxTreeVert_le_introduce v child).trans hmv
  have hfit_bud_ch : s.frontier + child.size * perSpace ≤ F_lo + inst.tree.size * perSpace := by
    have hmul_le : child.size * perSpace ≤ (NiceTree.introduce v child).size * perSpace :=
      Nat.mul_le_mul_right _ (by simp [NiceTree.size_introduce])
    exact le_trans (Nat.add_le_add_left hmul_le _) hfit_bud
  have htree_app := htree
  rw [encodeNiceTreeAux, HoldsIn.append_iff, length_encodeNiceTreeAux] at htree_app
  obtain ⟨htree_ch, hroot_hold⟩ := htree_app
  obtain ⟨hsafe_ch, hv_ch, hres_ch, hfr_ch, hframe_ch, hdesc_ch, hc_ch⟩ :=
    ih offset s hsz_ch hexp_ch hmv_ch hwf hs_fr hfit_bud_ch hvars htree_ch hcons
  let cur := offset + child.size
  obtain ⟨s₁, hs₁_def⟩ :
      ∃ s₁, (Memory.spec 0).clientState s (iterate nodeStep env child.size offset) = s₁ := ⟨_, rfl⟩
  rw [hs₁_def] at hfr_ch hframe_ch hdesc_ch
  have hwf₁ : Memory.WellFormed w s₁ := hs₁_def ▸ wellFormed_clientState hwf hv_ch
  have hFlo₁ : F_lo ≤ s₁.frontier := hs_fr.trans hframe_ch.1
  have hout_vars : env.varsPtr + env.varsLen ≤ env.descBase + 4 * offset :=
    hvars_lt_desc.trans (Nat.le_add_right _ _)
  have hout_cons : env.consRawPtr + (inst.constraints.flatMap ConstraintTable.encode).length ≤
      env.descBase + 4 * offset :=
    hcons_lt_desc.trans (Nat.le_add_right _ _)
  have hout_root : env.treePtr + 4 * cur + [1, v, cur - 1, 0].length ≤
      env.descBase + 4 * offset := by
    simp only [List.length_cons, List.length_nil]
    change env.treePtr + 4 * (offset + child.size) + 4 ≤ env.descBase + 4 * offset
    simp only [NiceTree.size_introduce] at hsz
    dsimp only [env, subtreeEnv] at *
    omega
  have hvars₁ : HoldsIn env.varsPtr inst.vars s₁ :=
    hvars.frame_outsideRange (.inl hout_vars) hframe_ch
  have hcons₁ : HoldsIn env.consRawPtr (inst.constraints.flatMap ConstraintTable.encode) s₁ :=
    hcons.frame_outsideRange (.inl hout_cons) hframe_ch
  have hroot₁ : HoldsIn (env.treePtr + 4 * cur) [1, v, cur - 1, 0] s₁ := by
    rw [show env.treePtr + 4 * offset + 4 * child.size = env.treePtr + 4 * cur from by
      dsimp only [cur]; omega] at hroot_hold
    simpa only [cur, Nat.add_sub_cancel] using
      hroot_hold.frame_outsideRange (.inl hout_root) hframe_ch
  have hr_root := hroot₁
  rw [HoldsIn.cons_iff, HoldsIn.cons_iff, HoldsIn.cons_iff, HoldsIn.cons_iff] at hr_root
  obtain ⟨_, htag1, _, harg_v, _, hch1_eq, _, _, _⟩ := hr_root
  have hdCur_hi : env.descBase + 4 * cur + 4 ≤ F_lo := by
    simp only [NiceTree.size_introduce] at hsz; dsimp only [cur, F_lo, env, subtreeEnv] at *; omega
  have hbag_len_le : (v :: bagList child).length ≤ E := by
    have h1 : (v :: bagList child).length ≤ maxTableExp (.introduce v child) := le_max_left _ _
    exact h1.trans hexp
  have hcbag_len_le : (bagList child).length ≤ E :=
    (bagList_length_le_maxTableExp child).trans hexp_ch
  have hpow_le : inst.domainSize ^ (v :: bagList child).length ≤ inst.domainSize ^ E :=
    Nat.pow_le_pow_right hq hbag_len_le
  have hs₁_peak : Fits w (s₁.frontier +
      ((v :: bagList child).length + inst.domainSize ^ (v :: bagList child).length)) :=
    hfit_total'.of_le (by
      change s.frontier + (NiceTree.introduce v child).size * perSpace ≤
        F_lo + inst.tree.size * perSpace at hfit_bud
      simp only [NiceTree.size_introduce] at hfit_bud
      have hsp : (v :: bagList child).length + inst.domainSize ^ (v :: bagList child).length ≤
          perSpace := by dsimp only [perSpace]; omega
      have hmul_bud : (child.size + 1) * perSpace = child.size * perSpace + perSpace := by ring
      change s₁.frontier ≤ s.frontier + child.size * perSpace at hfr_ch
      omega)
  have hfit_v : Fits w v := hw.of_le (by
    have hv_m : v ≤ maxTreeVert (.introduce v child) := le_max_left _ _
    have hmvt : maxTreeVert inst.tree ≤ inst.maxVarLabel :=
      le_trans (le_max_left _ _) (le_max_right _ _)
    unfold TreeCSPInstance.wordBound; dsimp only; omega)
  let introArgs : IntroNodeArgs :=
    ⟨env.q, v, env.consRawPtr, env.numCons, env.descBase + 4 * (cur - 1), env.descBase + 4 * cur⟩
  have hcons_le : env.consRawPtr +
      (inst.constraints.flatMap ConstraintTable.encode).length ≤ F_lo := by
    dsimp only [F_lo, env, subtreeEnv] at *; omega
  obtain ⟨hv_in, hfr_in, hframe_in, hdesc_in, hc_in⟩ :=
    introNodeProg_spec (w := w) inst.counting introArgs hq hwf₁ hfit_v
      hcons₁ rfl hcons_le hdesc_ch hdCur_hi hFlo₁ hs₁_peak
  have htree_lt : env.treePtr + 4 * cur + 3 < s₁.frontier := by
    have := hroot₁.1; simp only [List.length_cons, List.length_nil] at this; omega
  have hne0 : s₁.mem (env.treePtr + 4 * cur) ≠ 0 := by omega
  have hsafe_root : nodeStepSafe w (env, cur) s₁ :=
    ⟨hfit_4, hfit_tree.of_le (by simp only [NiceTree.size_introduce] at hsz; omega),
      hfit_total.of_le (by dsimp only [F_lo, env, subtreeEnv, perSpace, E] at *; omega),
      hfit_total.of_le (by dsimp only [F_lo, env, subtreeEnv, perSpace, E] at *; omega),
      Or.inr (Or.inl ⟨htag1, hq, hfit_q,
        by rw [harg_v]; exact hfit_v,
        hfit_total.of_le (by
          rw [hch1_eq]; dsimp only [F_lo, env, subtreeEnv, perSpace, E] at *; omega),
        F_lo, inst.counting, child, inst.constraints, inst.vars,
        hwf₁, rfl, hcons₁, hcons_le, by rw [hch1_eq]; exact hdesc_ch, hFlo₁,
        by rw [harg_v]; exact hs₁_peak⟩)⟩
  have hr_s (x : ℕ) : (Memory.spec 0).clientState s₁ (Memory.read x) = s₁ := rfl
  have hr_r (x : ℕ) : (Memory.spec 0).clientResult s₁ (Memory.read x) = s₁.mem x := rfl
  have hst_root : (Memory.spec 0).clientState s₁ (nodeStep (env, cur)) =
      (Memory.spec 0).clientState s₁ (introNodeProg introArgs) := by
    unfold nodeStep; dsimp only
    iterate 4 rw [StateTransitionSpec.clientState_bind, hr_s, hr_r]
    rw [ite_eq_right hne0, ite_eq_left htag1, harg_v, hch1_eq,
      StateTransitionSpec.clientState_bind]
    rfl
  have hres_root : (Memory.spec 0).clientResult s₁ (nodeStep (env, cur)) = cur + 1 := by
    unfold nodeStep; dsimp only
    iterate 4 rw [StateTransitionSpec.clientResult_bind, hr_s, hr_r]
    rw [ite_eq_right hne0, ite_eq_left htag1, StateTransitionSpec.clientResult_bind]
    rfl
  have hv_root : (Memory.spec w).ValidHistory s₁
      ((Memory.spec w).clientHistory s₁ (nodeStep (env, cur))) := by
    unfold nodeStep; dsimp only
    refine validHistory_read_bind (by omega) ?_
    refine validHistory_read_bind (by omega) ?_
    refine validHistory_read_bind (by omega) ?_
    refine validHistory_read_bind (by omega) ?_
    rw [ite_eq_right hne0, ite_eq_left htag1, harg_v, hch1_eq]
    exact validHistory_bind_step hv_in (validHistory_pure w _ _)
  have hcost_root : memoryCost (nodeStep (env, cur)) s₁ ≤ perCost := by
    unfold nodeStep; dsimp only
    iterate 4 rw [memoryCost_bind', memoryCost_read, hr_s, hr_r]
    rw [ite_eq_right hne0, ite_eq_left htag1, harg_v, hch1_eq, memoryCost_bind',
      memoryCost_pure, Nat.add_zero]
    have hmul_c :
        inst.domainSize ^ (v :: bagList child).length *
          (2 + 3 * inst.constraints.length +
            inst.totalArity * (2 * (v :: bagList child).length + 3)) ≤
          inst.domainSize ^ E *
            (E ^ 2 + E + 4 + 3 * inst.constraints.length + inst.totalArity * (2 * E + 3)) := by
      refine Nat.mul_le_mul hpow_le ?_
      have har : inst.totalArity * (2 * (v :: bagList child).length + 3) ≤
          inst.totalArity * (2 * E + 3) := Nat.mul_le_mul_left _ (by omega)
      omega
    dsimp only [introArgs, TreeCSPInstance.totalArity, env, subtreeEnv, perCost] at hc_in hmul_c ⊢
    omega
  have hit_root_st : (Memory.spec 0).clientState s₁ (iterate nodeStep env 1 cur) =
      (Memory.spec 0).clientState s₁ (nodeStep (env, cur)) := by
    change (Memory.spec 0).clientState s₁ (nodeStep (env, cur) >>= iterate nodeStep env 0) = _
    rw [StateTransitionSpec.clientState_bind]; rfl
  have hit_root_res : (Memory.spec 0).clientResult s₁ (iterate nodeStep env 1 cur) = cur + 1 := by
    change (Memory.spec 0).clientResult s₁ (nodeStep (env, cur) >>= iterate nodeStep env 0) = _
    rw [StateTransitionSpec.clientResult_bind, hres_root]; rfl
  have hv_it_root : (Memory.spec w).ValidHistory s₁
      ((Memory.spec w).clientHistory s₁ (iterate nodeStep env 1 cur)) := by
    change (Memory.spec w).ValidHistory s₁
      ((Memory.spec w).clientHistory s₁ (nodeStep (env, cur) >>= iterate nodeStep env 0))
    exact validHistory_bind_step hv_root (validHistory_pure w _ _)
  have hc_it_root : memoryCost (iterate nodeStep env 1 cur) s₁ ≤ perCost := by
    change memoryCost (nodeStep (env, cur) >>= iterate nodeStep env 0) s₁ ≤ _
    rw [memoryCost_bind', show memoryCost (iterate nodeStep env 0 _) _ = 0 from rfl, Nat.add_zero]
    exact hcost_root
  simp only [NiceTree.size_introduce]
  refine ⟨iterationSafe_add nodeStep nodeStepSafe w env child.size 1 offset s hsafe_ch
      (by rw [hres_ch, hs₁_def]; exact ⟨hsafe_root, trivial⟩),
    validHistory_iterate_add nodeStep env child.size 1 offset s hv_ch
      (by dsimp only [cur]; rw [hres_ch, hs₁_def]; exact hv_it_root),
    by rw [clientResult_iterate_add, hres_ch, hs₁_def]; exact hit_root_res,
    ?_, ?_, ?_, ?_⟩
  · rw [clientState_iterate_add, hres_ch, hs₁_def, hit_root_st, hst_root]
    have hfr_le : (v :: bagList child).length +
        inst.domainSize ^ (v :: bagList child).length ≤ perSpace := by
      dsimp only [perSpace]; omega
    have hmul_bud : (child.size + 1) * perSpace = child.size * perSpace + perSpace := by ring
    change s₁.frontier ≤ s.frontier + child.size * perSpace at hfr_ch
    change _ ≤ s.frontier + (child.size + 1) * perSpace
    dsimp only [introArgs, env, subtreeEnv] at hfr_in hfr_ch ⊢
    omega
  · rw [clientState_iterate_add, hres_ch, hs₁_def]
    change FrameOutsideRange (env.descBase + 4 * offset)
      (env.descBase + 4 * (offset + (child.size + 1))) s
      ((Memory.spec 0).clientState s₁ (iterate nodeStep env 1 cur))
    rw [hit_root_st, hst_root]
    have hfr_in' : FrameOutsideRange (env.descBase + 4 * cur)
        (env.descBase + 4 * (cur + 1)) s₁
        ((Memory.spec 0).clientState s₁ (introNodeProg introArgs)) := by
      dsimp only [introArgs] at hframe_in
      simpa only [Nat.mul_add, Nat.mul_one, Nat.add_assoc] using hframe_in
    simpa only [cur, env, subtreeEnv, Nat.add_assoc] using
      FrameOutsideRange.trans
        (hframe_ch.mono_range le_rfl (by dsimp only [cur, env, subtreeEnv]; omega))
        (hfr_in'.mono_range (by dsimp only [cur, env, subtreeEnv]; omega) le_rfl)
  · rw [clientState_iterate_add, hres_ch, hs₁_def]
    change NodeDescAt F_lo inst.counting inst.domainSize inst.constraints inst.vars
      (.introduce v child) (env.descBase + 4 * (offset + (child.size + 1) - 1))
      ((Memory.spec 0).clientState s₁ (iterate nodeStep env 1 cur))
    rw [hit_root_st, hst_root, show offset + (child.size + 1) - 1 = cur from by omega]
    exact hdesc_in
  · rw [memoryCost_iterate_add, hres_ch, hs₁_def]
    change memoryCost (iterate nodeStep env child.size offset) s +
        memoryCost (iterate nodeStep env 1 cur) s₁ ≤ (child.size + 1) * perCost
    have : (child.size + 1) * perCost = child.size * perCost + perCost := by ring
    change memoryCost (iterate nodeStep env child.size offset) s ≤ child.size * perCost at hc_ch
    omega

private theorem subtree_full {w : ℕ} (inst : TreeCSPInstance) (hw : Fits w inst.wordBound) :
    ∀ (S : NiceTree ℕ) (offset : ℕ) (s : Memory.State),
      SubtreeFullSpec w inst S offset s := by
  intro S
  induction S with
  | leaf => exact subtree_leaf inst hw
  | introduce v child ih => exact subtree_introduce inst hw v child ih
  | forget v child ih => exact subtree_forget inst hw v child ih
  | join left right ihl ihr => exact subtree_join inst hw left right ihl ihr

/-- Top-level exact-basis Word-RAM program solving serialized `TreeCSPInstance` inputs. -/
def runTreeCSPProg (_ : Unit) : Memory.Prog ℕ := do
  let mode ← Memory.read 1
  let q ← Memory.read 2
  let varsLen ← Memory.read 3
  let numCons ← Memory.read 4
  let treeSize ← Memory.read 5
  let varsPtr := 6
  let treePtr := 6 + varsLen
  let consRawPtr := treePtr + 4 * treeSize
  let descBase ← Memory.allocDirty (4 * treeSize)
  let env : NodeEnv := ⟨mode, q, varsPtr, varsLen, treePtr, consRawPtr, numCons, descBase⟩
  let _ ← iterNodesProg ((env, 0), treeSize)
  let rootDesc := descBase + 4 * (treeSize - 1)
  let rootTblPtr ← Memory.read (rootDesc + 2)
  Memory.read rootTblPtr

/-- Every word of `inst.encode` (and its length) fits within `w` bits when
`Fits w inst.wordBound`. -/
theorem inputFits_encode {w : ℕ} (inst : TreeCSPInstance) (hw : Fits w inst.wordBound) :
    InputFits w inst.encode := by
  have hlen_enc := (holdsIn_encode_decode inst).2.1
  refine ⟨hw.of_le (by unfold TreeCSPInstance.wordBound; dsimp only; omega), fun x hx => ?_⟩
  unfold TreeCSPInstance.encode at hx
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_flatMap] at hx
  rcases hx with ((((rfl | rfl | rfl | rfl | rfl) | hx_v) | hx_t) | ⟨ct, hct, hx_c⟩)
  · exact hw.of_le (by split_ifs <;> (unfold TreeCSPInstance.wordBound; dsimp only; omega))
  · have hpow1 : 1 ≤ inst.domainSize ^ maxTableExp inst.tree :=
      Nat.one_le_pow _ _ inst.domainSize_pos
    have h1q : inst.domainSize ≤ inst.domainSize * inst.domainSize ^ maxTableExp inst.tree :=
      Nat.le_mul_of_pos_right _ hpow1
    exact hw.of_le (by unfold TreeCSPInstance.wordBound; dsimp only; omega)
  · exact hw.of_le (by unfold TreeCSPInstance.wordBound; dsimp only; omega)
  · have hcl : inst.constraints.length ≤
        (inst.constraints.flatMap ConstraintTable.encode).length := by
      have hlen : ∀ cs : List (ConstraintTable inst.domainSize),
          cs.length ≤ (cs.flatMap ConstraintTable.encode).length := by
        intro cs
        induction cs with
        | nil => exact le_rfl
        | cons c cs ih =>
          simp only [List.length_cons, List.flatMap_cons, List.length_append]
          have hce : 1 ≤ (ConstraintTable.encode c).length := by
            simp [ConstraintTable.encode]
          omega
      exact hlen inst.constraints
    exact hw.of_le (by unfold TreeCSPInstance.wordBound; dsimp only; omega)
  · exact hw.of_le (by unfold TreeCSPInstance.wordBound; dsimp only; omega)
  · have hv_m : x ≤ inst.vars.foldl max 0 := List.mem_le_foldl_max hx_v
    have hmvl : inst.vars.foldl max 0 ≤ inst.maxVarLabel := le_max_left _ _
    exact hw.of_le (by unfold TreeCSPInstance.wordBound; dsimp only; omega)
  · have ht_m := encodeNiceTreeAux_max_le 0 inst.tree x hx_t
    have hmvt : maxTreeVert inst.tree ≤ inst.maxVarLabel :=
      le_trans (le_max_left _ _) (le_max_right _ _)
    exact hw.of_le (by unfold TreeCSPInstance.wordBound; dsimp only; omega)
  · have hct_len : (ConstraintTable.encode ct).length ≤
        (inst.constraints.flatMap ConstraintTable.encode).length := by
      have hsub : ∀ cs : List (ConstraintTable inst.domainSize), ct ∈ cs →
          (ConstraintTable.encode ct).length ≤ (cs.flatMap ConstraintTable.encode).length := by
        intro cs hmem
        induction cs with
        | nil => simp at hmem
        | cons c cs ih =>
          simp only [List.mem_cons] at hmem
          simp only [List.flatMap_cons, List.length_append]
          rcases hmem with rfl | hmem
          · exact Nat.le_add_right _ _
          · exact (ih hmem).trans (Nat.le_add_left _ _)
      exact hsub inst.constraints hct
    have hce_len : (ConstraintTable.encode ct).length =
        2 + ct.scope.length + ct.table.length := by
      simp [ConstraintTable.encode]; omega
    unfold ConstraintTable.encode at hx_c
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx_c
    rcases hx_c with ((rfl | rfl) | hx_s) | hx_t
    · exact hw.of_le (by unfold TreeCSPInstance.wordBound; dsimp only; omega)
    · exact hw.of_le (by unfold TreeCSPInstance.wordBound; dsimp only; omega)
    · have hsm : x ≤ (inst.constraints.flatMap fun c => c.scope).foldl max 0 :=
        List.mem_le_foldl_max (List.mem_flatMap.2 ⟨ct, hct, hx_s⟩)
      have hmvs : (inst.constraints.flatMap fun c => c.scope).foldl max 0 ≤ inst.maxVarLabel :=
        le_trans (le_max_right _ _) (le_max_right _ _)
      exact hw.of_le (by unfold TreeCSPInstance.wordBound; dsimp only; omega)
    · have htb := ct.table_bool x hx_t
      exact hw.of_le (by unfold TreeCSPInstance.wordBound; dsimp only; omega)

/-- Full correctness, history validity, and step-cost bound for `runTreeCSPProg`. -/
theorem runTreeCSPProg_spec {w : ℕ} (inst : TreeCSPInstance)
    (hw : Fits w inst.wordBound) :
    let s₀ := Memory.State.init inst.encode
    (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ (runTreeCSPProg ())) ∧
    (Memory.spec 0).clientResult s₀ (runTreeCSPProg ()) = inst.result ∧
    memoryCost (runTreeCSPProg ()) s₀ ≤ inst.stepBound := by
  let s₀ := Memory.State.init inst.encode
  obtain ⟨hfr₀, hlen_enc, hm1, hm2, hm3, hm4, hm5, hvars₀, htree₀, hcons₀⟩ :=
    holdsIn_encode_decode inst
  have hts_pos : 0 < inst.tree.size := NiceTree.size_pos inst.tree
  have hf_len : Fits w (inst.encode.length + 1) :=
    hw.of_le (by unfold TreeCSPInstance.wordBound; dsimp only; omega)
  have hwf₀ : Memory.WellFormed w s₀ :=
    Memory.wellFormed_init (inputFits_encode inst hw) hf_len
  let treePtr := 6 + inst.vars.length
  let consRawPtr := treePtr + 4 * inst.tree.size
  let descBase := inst.encode.length + 1
  let F_lo := descBase + 4 * inst.tree.size
  let s₁ := (Memory.spec 0).clientState s₀ (Memory.allocDirty (4 * inst.tree.size))
  have hs₁_fr : s₁.frontier = F_lo := by
    change s₀.frontier + 4 * inst.tree.size = F_lo; rw [hfr₀]
  have hp₁ : PreservesBelow descBase s₀ s₁ := by
    dsimp only [descBase]; rw [← hfr₀]; exact preservesBelow_allocDirty s₀ (4 * inst.tree.size)
  have hfit_a1 : Fits w (s₀.frontier + 4 * inst.tree.size) := hw.of_le (by
    rw [hfr₀]; unfold TreeCSPInstance.wordBound; dsimp only; omega)
  have hv₁ : (Memory.spec w).ValidHistory s₀
      ((Memory.spec w).clientHistory s₀ (Memory.allocDirty (4 * inst.tree.size))) :=
    validHistory_allocDirty hfit_a1
  have hwf₁ : Memory.WellFormed w s₁ := wellFormed_clientState hwf₀ hv₁
  have hvars₁ : HoldsIn 6 inst.vars s₁ :=
    hvars₀.mono (by dsimp only [descBase]; omega) hp₁
  have htree₁ : HoldsIn (treePtr + 4 * 0) (encodeNiceTreeAux 0 inst.tree) s₁ := by
    rw [Nat.mul_zero, Nat.add_zero]
    exact htree₀.mono (by rw [length_encodeNiceTree]; dsimp only [treePtr, descBase]; omega) hp₁
  have hcons₁ : HoldsIn consRawPtr (inst.constraints.flatMap ConstraintTable.encode) s₁ :=
    hcons₀.mono (by dsimp only [consRawPtr, treePtr, descBase]; omega) hp₁
  let env : NodeEnv :=
    ⟨if inst.counting then 1 else 0, inst.domainSize, 6, inst.vars.length,
      treePtr, consRawPtr, inst.constraints.length, descBase⟩
  have hfull := subtree_full inst hw inst.tree 0 s₁ (by omega) le_rfl le_rfl hwf₁
    (le_of_eq hs₁_fr.symm) (by rw [hs₁_fr]) hvars₁ htree₁ hcons₁
  obtain ⟨hsafe_tr, hv_tr, _, hfr_tr, _, hdesc_tr, hc_tr⟩ := hfull
  let s₂ := (Memory.spec 0).clientState s₁ (iterNodesProg ((env, 0), inst.tree.size))
  have hroot_tbl := hdesc_tr.tbl_holds
  have hroot_len : (dpInstTree inst.counting inst.domainSize inst.constraints inst.vars
      inst.tree).length = inst.domainSize ^ (bagList inst.tree).length :=
    length_dpInstTree _ _ _ _ _
  have h0_lt : 0 < inst.domainSize ^ (bagList inst.tree).length :=
    Nat.one_le_pow _ _ inst.domainSize_pos
  have hroot_get : s₂.mem (s₂.mem (descBase + 4 * (inst.tree.size - 1) + 2)) = inst.result := by
    have hg := hroot_tbl.get 0 (by rw [hroot_len]; exact h0_lt)
    dsimp only [s₂, iterNodesProg, env, subtreeEnv, descBase, treePtr, consRawPtr] at hg ⊢
    simp only [Nat.add_zero, Nat.zero_add] at hg
    rw [hg]
    unfold TreeCSPInstance.result
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hroot_len]; exact h0_lt)]
    rfl
  have hroot_desc_lt : descBase + 4 * (inst.tree.size - 1) + 2 < s₂.frontier := by
    have := hdesc_tr.desc_hi
    have := hdesc_tr.tbl_holds.1
    have : s₁.frontier ≤ s₂.frontier := by
      have htl := hdesc_tr.tbl_lo
      have htbl1 := hdesc_tr.tbl_holds.1
      rw [Nat.zero_add] at htl htbl1
      dsimp only [F_lo, s₂, iterNodesProg, env, subtreeEnv, descBase, treePtr, consRawPtr]
        at htl htbl1 ⊢
      omega
    rw [Nat.zero_add] at *
    dsimp only [F_lo, s₂, iterNodesProg, env, subtreeEnv, descBase, treePtr, consRawPtr] at *; omega
  have hroot_tbl_lt : s₂.mem (descBase + 4 * (inst.tree.size - 1) + 2) < s₂.frontier := by
    have htbl1 := hroot_tbl.1
    rw [hroot_len] at htbl1
    dsimp only [s₂, iterNodesProg, env, subtreeEnv, descBase, treePtr, consRawPtr] at htbl1 ⊢
    rw [Nat.zero_add] at htbl1
    omega
  have h1_lt : 1 < s₀.frontier := by rw [hfr₀]; omega
  have h2_lt : 2 < s₀.frontier := by rw [hfr₀]; omega
  have h3_lt : 3 < s₀.frontier := by rw [hfr₀]; omega
  have h4_lt : 4 < s₀.frontier := by rw [hfr₀]; omega
  have h5_lt : 5 < s₀.frontier := by rw [hfr₀]; omega
  have hr₀_s (a : ℕ) : (Memory.spec 0).clientState s₀ (Memory.read a) = s₀ := rfl
  have hr₀_r (a : ℕ) : (Memory.spec 0).clientResult s₀ (Memory.read a) = s₀.mem a := rfl
  have ha1_s : (Memory.spec 0).clientState s₀ (Memory.allocDirty (4 * inst.tree.size)) = s₁ := rfl
  have ha1_r : (Memory.spec 0).clientResult s₀ (Memory.allocDirty (4 * inst.tree.size)) =
      descBase := by
    change s₀.frontier = descBase; exact hfr₀
  have hr₂_s (a : ℕ) : (Memory.spec 0).clientState s₂ (Memory.read a) = s₂ := rfl
  have hr₂_r (a : ℕ) : (Memory.spec 0).clientResult s₂ (Memory.read a) = s₂.mem a := rfl
  refine ⟨?_, ?_, ?_⟩
  · unfold runTreeCSPProg
    dsimp only
    refine validHistory_read_bind h1_lt ?_; rw [hm1]
    refine validHistory_read_bind h2_lt ?_; rw [hm2]
    refine validHistory_read_bind h3_lt ?_; rw [hm3]
    refine validHistory_read_bind h4_lt ?_; rw [hm4]
    refine validHistory_read_bind h5_lt ?_; rw [hm5]
    refine validHistory_bind_step hv₁ ?_
    rw [ha1_s, ha1_r]
    change (Memory.spec w).ValidHistory s₁
      ((Memory.spec w).clientHistory s₁ (iterNodesProg ((env, 0), inst.tree.size) >>= _))
    refine validHistory_bind_step hv_tr ?_
    change (Memory.spec w).ValidHistory s₂
      ((Memory.spec w).clientHistory s₂
        (Memory.read (descBase + 4 * (inst.tree.size - 1) + 2) >>= fun tp => Memory.read tp))
    exact validHistory_read_bind hroot_desc_lt (validHistory_read hroot_tbl_lt)
  · unfold runTreeCSPProg
    dsimp only
    iterate 5 rw [StateTransitionSpec.clientResult_bind, hr₀_s, hr₀_r]
    rw [hm1, hm2, hm3, hm4, hm5, StateTransitionSpec.clientResult_bind, ha1_s, ha1_r]
    change (Memory.spec 0).clientResult s₁ (iterNodesProg ((env, 0), inst.tree.size) >>= _) =
      inst.result
    rw [StateTransitionSpec.clientResult_bind]
    change (Memory.spec 0).clientResult s₂
      (Memory.read (descBase + 4 * (inst.tree.size - 1) + 2) >>= fun tp => Memory.read tp) =
      inst.result
    rw [StateTransitionSpec.clientResult_bind, hr₂_s, hr₂_r, hr₂_r]
    exact hroot_get
  · unfold runTreeCSPProg
    dsimp only
    iterate 5 rw [memoryCost_bind', memoryCost_read, hr₀_s, hr₀_r]
    rw [hm1, hm2, hm3, hm4, hm5, memoryCost_bind', memoryCost_allocDirty, ha1_s, ha1_r,
      memoryCost_bind']
    change 1 + (1 + (1 + (1 + (1 + (1 + (memoryCost (iterNodesProg ((env, 0), inst.tree.size)) s₁ +
      memoryCost (Memory.read (descBase + 4 * (inst.tree.size - 1) + 2) >>= fun tp =>
        Memory.read tp) s₂)))))) ≤ inst.stepBound
    rw [memoryCost_bind', memoryCost_read, memoryCost_read]
    unfold TreeCSPInstance.stepBound
    dsimp only [env, subtreeEnv, treePtr, consRawPtr, descBase] at hc_tr ⊢
    change 1 + (1 + (1 + (1 + (1 + (1 + (memoryCost (iterate nodeStep env inst.tree.size 0) s₁ +
      (1 + 1))))))) ≤ _
    dsimp only [env, subtreeEnv, treePtr, consRawPtr, descBase]
    omega

/-- Exact-basis Word-RAM realization certificate for `runTreeCSPProg`. -/
theorem runTreeCSPProg_realizes :
    Realizes .exact runTreeCSPProg WordEncoding.encode WordEncoding.encode
      (fun w _ s =>
        ∃ inst : TreeCSPInstance,
          s = Memory.State.init inst.encode ∧
          Fits w inst.wordBound)
      (fun _ _ => 0) := by
  unfold runTreeCSPProg
  realize [iterNodesProg_realizes]
  all_goals
    obtain ⟨inst, rfl, hw⟩ := h
    obtain ⟨hfr₀, hlen_enc, hm1, hm2, hm3, hm4, hm5, hvars₀, htree₀, hcons₀⟩ :=
      holdsIn_encode_decode inst
    have hts_pos : 0 < inst.tree.size := NiceTree.size_pos inst.tree
    have hf_len : Fits w (inst.encode.length + 1) :=
      hw.of_le (by unfold TreeCSPInstance.wordBound; dsimp only; omega)
    first
    | exact hts_pos
    | exact hw.of_le (by unfold TreeCSPInstance.wordBound; dsimp only; omega)
    | (rw [hm1, hm2, hm3, hm4, hm5]
       have hwf₀ : Memory.WellFormed w (Memory.State.init inst.encode) :=
         Memory.wellFormed_init (inputFits_encode inst hw) hf_len
       let treePtr := 6 + inst.vars.length
       let consRawPtr := treePtr + 4 * inst.tree.size
       let descBase := inst.encode.length + 1
       let F_lo := descBase + 4 * inst.tree.size
       let s₀ := Memory.State.init inst.encode
       let s₁ := (Memory.spec 0).clientState s₀ (Memory.allocDirty (4 * inst.tree.size))
       have hs₁_fr : s₁.frontier = F_lo := by
         change s₀.frontier + 4 * inst.tree.size = F_lo; rw [hfr₀]
       have hp₁ : PreservesBelow descBase s₀ s₁ := by
         dsimp only [descBase]; rw [← hfr₀]; exact preservesBelow_allocDirty s₀ (4 * inst.tree.size)
       have hfit_a1 : Fits w (s₀.frontier + 4 * inst.tree.size) := hw.of_le (by
         rw [hfr₀]; unfold TreeCSPInstance.wordBound; dsimp only; omega)
       have hv₁ : (Memory.spec w).ValidHistory s₀
           ((Memory.spec w).clientHistory s₀ (Memory.allocDirty (4 * inst.tree.size))) :=
         validHistory_allocDirty hfit_a1
       have hwf₁ : Memory.WellFormed w s₁ := wellFormed_clientState hwf₀ hv₁
       have hvars₁ : HoldsIn 6 inst.vars s₁ :=
         hvars₀.mono (by dsimp only [descBase]; omega) hp₁
       have htree₁ : HoldsIn (treePtr + 4 * 0) (encodeNiceTreeAux 0 inst.tree) s₁ := by
         rw [Nat.mul_zero, Nat.add_zero]
         exact htree₀.mono
           (by rw [length_encodeNiceTree]; dsimp only [treePtr, descBase]; omega) hp₁
       have hcons₁ : HoldsIn consRawPtr (inst.constraints.flatMap ConstraintTable.encode) s₁ :=
         hcons₀.mono (by dsimp only [consRawPtr, treePtr, descBase]; omega) hp₁
       have hfull := subtree_full inst hw inst.tree 0 s₁ (by omega) le_rfl le_rfl hwf₁
         (le_of_eq hs₁_fr.symm) (by rw [hs₁_fr]) hvars₁ htree₁ hcons₁
       exact hfull.1)

end Cslib.Algorithms.WordRAM.TreeDecomposition
