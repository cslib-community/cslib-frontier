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

/-! ## Runs of `nodeStep` -/

/-- What `n` consecutive `nodeStep`s from node `offset` at state `s` guarantee: the conclusions of
`SubtreeFullSpec` other than the descriptor of the subtree root. -/
private structure StepsSpec (w : ℕ) (inst : TreeCSPInstance) (n offset : ℕ) (s : Memory.State) :
    Prop where
  safe : iterationSafe nodeStep nodeStepSafe w (subtreeEnv inst) n offset s
  valid : (Memory.spec w).ValidHistory s
    ((Memory.spec w).clientHistory s (iterate nodeStep (subtreeEnv inst) n offset))
  result : (Memory.spec 0).clientResult s (iterate nodeStep (subtreeEnv inst) n offset) =
    offset + n
  frontier :
    ((Memory.spec 0).clientState s (iterate nodeStep (subtreeEnv inst) n offset)).frontier ≤
      s.frontier + n * (maxTableExp inst.tree + 2 + inst.domainSize ^ maxTableExp inst.tree)
  frame : FrameOutsideRange ((subtreeEnv inst).descBase + 4 * offset)
    ((subtreeEnv inst).descBase + 4 * (offset + n)) s
    ((Memory.spec 0).clientState s (iterate nodeStep (subtreeEnv inst) n offset))
  cost : memoryCost (iterate nodeStep (subtreeEnv inst) n offset) s ≤
    n * (16 + 4 * maxTableExp inst.tree + inst.vars.length +
      inst.domainSize ^ maxTableExp inst.tree *
        (maxTableExp inst.tree ^ 2 + maxTableExp inst.tree + 4 + 3 * inst.constraints.length +
          inst.totalArity * (2 * maxTableExp inst.tree + 3)))

/-- Consecutive runs of `nodeStep` compose. -/
private theorem StepsSpec.add {w : ℕ} {inst : TreeCSPInstance} {m n offset : ℕ}
    {s : Memory.State} (h₁ : StepsSpec w inst m offset s)
    (h₂ : StepsSpec w inst n (offset + m)
      ((Memory.spec 0).clientState s (iterate nodeStep (subtreeEnv inst) m offset))) :
    StepsSpec w inst (m + n) offset s where
  safe := iterationSafe_add _ _ _ _ _ _ _ _ h₁.safe (by rw [h₁.result]; exact h₂.safe)
  valid := validHistory_iterate_add _ _ _ _ _ _ h₁.valid (by rw [h₁.result]; exact h₂.valid)
  result := by rw [clientResult_iterate_add, h₁.result, h₂.result, Nat.add_assoc]
  frontier := by
    have := h₁.frontier; have := h₂.frontier
    rw [clientState_iterate_add, h₁.result, Nat.add_mul]; omega
  frame := by
    rw [clientState_iterate_add, h₁.result]
    exact (h₁.frame.mono_range le_rfl (by omega)).trans
      (h₂.frame.mono_range (by omega) (by omega))
  cost := by
    have := h₁.cost; have := h₂.cost
    rw [memoryCost_iterate_add, h₁.result, Nat.add_mul]; omega

/-- One `nodeStep` at node `cur`, whose header `[t, a, c₁, c₂]` selects the node program `P`
(`hK`), has the guarantees of `P` and ends where `P` ends. -/
private theorem stepsSpec_one {w : ℕ} {inst : TreeCSPInstance} {cur t a c₁ c₂ : ℕ}
    {s : Memory.State} {α : Type} {K : ℕ → ℕ → ℕ → ℕ → Memory.Prog ℕ} (P : Memory.Prog α)
    (hroot : HoldsIn ((subtreeEnv inst).treePtr + 4 * cur) [t, a, c₁, c₂] s)
    (hsel : nodeStep (subtreeEnv inst, cur) = do
      let tag ← Memory.read ((subtreeEnv inst).treePtr + 4 * cur)
      let arg ← Memory.read ((subtreeEnv inst).treePtr + 4 * cur + 1)
      let ch1 ← Memory.read ((subtreeEnv inst).treePtr + 4 * cur + 2)
      let ch2 ← Memory.read ((subtreeEnv inst).treePtr + 4 * cur + 3)
      K tag arg ch1 ch2)
    (hK : K t a c₁ c₂ = P >>= fun _ => pure (cur + 1))
    (hsafe : nodeStepSafe w (subtreeEnv inst, cur) s)
    (hv : (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s P))
    (hfr : ((Memory.spec 0).clientState s P).frontier ≤
      s.frontier + (maxTableExp inst.tree + 2 + inst.domainSize ^ maxTableExp inst.tree))
    (hframe : FrameOutsideRange ((subtreeEnv inst).descBase + 4 * cur)
      ((subtreeEnv inst).descBase + 4 * cur + 4) s ((Memory.spec 0).clientState s P))
    (hcost : 4 + memoryCost P s ≤
      16 + 4 * maxTableExp inst.tree + inst.vars.length +
        inst.domainSize ^ maxTableExp inst.tree *
          (maxTableExp inst.tree ^ 2 + maxTableExp inst.tree + 4 + 3 * inst.constraints.length +
            inst.totalArity * (2 * maxTableExp inst.tree + 3))) :
    StepsSpec w inst 1 cur s ∧
      (Memory.spec 0).clientState s (iterate nodeStep (subtreeEnv inst) 1 cur) =
        (Memory.spec 0).clientState s P := by
  have htree : (subtreeEnv inst).treePtr + 4 * cur + 4 ≤ s.frontier := hroot.1
  have hK' : K (s.mem ((subtreeEnv inst).treePtr + 4 * cur))
      (s.mem ((subtreeEnv inst).treePtr + 4 * cur + 1))
      (s.mem ((subtreeEnv inst).treePtr + 4 * cur + 2))
      (s.mem ((subtreeEnv inst).treePtr + 4 * cur + 3)) = P >>= fun _ => pure (cur + 1) := by
    have hr := hroot
    rw [HoldsIn.cons_iff, HoldsIn.cons_iff, HoldsIn.cons_iff, HoldsIn.cons_iff] at hr
    obtain ⟨-, h0, -, h1, -, h2, -, h3, -⟩ := hr
    rw [h0, h1, h2, h3]
    exact hK
  have hit : iterate nodeStep (subtreeEnv inst) 1 cur =
      nodeStep (subtreeEnv inst, cur) >>= iterate nodeStep (subtreeEnv inst) 0 := rfl
  have hr (x : ℕ) : (Memory.spec 0).clientState s (Memory.read x) = s := rfl
  have hst : (Memory.spec 0).clientState s (iterate nodeStep (subtreeEnv inst) 1 cur) =
      (Memory.spec 0).clientState s P := by
    rw [hit, hsel, StateTransitionSpec.clientState_bind]
    iterate 4 rw [clientState_bind_read]
    rw [hK', StateTransitionSpec.clientState_bind]
    rfl
  refine ⟨⟨⟨hsafe, trivial⟩, ?_, ?_, ?_, ?_, ?_⟩, hst⟩
  · rw [hit, hsel]
    refine validHistory_bind_step ?_ (validHistory_pure w _ _)
    refine validHistory_read_bind (by omega) (validHistory_read_bind (by omega)
      (validHistory_read_bind (by omega) (validHistory_read_bind (by omega) ?_)))
    rw [hK']
    exact validHistory_bind_step hv (validHistory_pure w _ _)
  · rw [hit, hsel, StateTransitionSpec.clientResult_bind]
    iterate 4 rw [clientState_bind_read, clientResult_bind_read]
    rw [hK', StateTransitionSpec.clientResult_bind]
    rfl
  · rw [hst, Nat.one_mul]; exact hfr
  · rw [hst, Nat.mul_add, Nat.mul_one, ← Nat.add_assoc]; exact hframe
  · rw [hit, hsel, memoryCost_bind', Nat.one_mul]
    iterate 4 rw [memoryCost_bind', memoryCost_read, StateTransitionSpec.clientState_bind, hr,
      clientResult_read]
    rw [hK', memoryCost_bind', memoryCost_pure]
    change 1 + (1 + (1 + (1 + (memoryCost P s + 0)))) + 0 ≤ _
    omega

/-- The word-size facts that `nodeStepSafe` needs at a node `cur` of the tree. -/
private theorem fits_node {w : ℕ} {inst : TreeCSPInstance} (hw : Fits w inst.wordBound)
    {cur : ℕ} (hcur : cur < inst.tree.size) :
    Fits w ((subtreeEnv inst).treePtr + 4 * cur + 3) ∧
      Fits w ((subtreeEnv inst).descBase + 4 * cur + 3) := by
  have hlen := (holdsIn_encode_decode inst).2.1
  obtain ⟨-, -, -, -, hfit_total, -⟩ := subtree_setup inst hw
  constructor <;> refine hfit_total.of_le ?_ <;> dsimp only [subtreeEnv] at * <;> omega

/-- The capacity bound of the table entries of a subtree `S` fits in a word. -/
private theorem fits_cap {w : ℕ} {inst : TreeCSPInstance} (hw : Fits w inst.wordBound)
    {S : NiceTree ℕ} (hS : S.size ≤ inst.tree.size) :
    Fits w (if inst.counting then inst.domainSize ^ S.size else 1) :=
  hw.of_le (by
    have := Nat.pow_le_pow_right inst.domainSize_pos hS
    unfold TreeCSPInstance.wordBound TreeCSPInstance.maxEntryBound
    dsimp only
    split_ifs <;> omega)

/-! ## The four node kinds -/

private theorem subtree_leaf {w : ℕ} (inst : TreeCSPInstance) (hw : Fits w inst.wordBound) :
    ∀ offset s, SubtreeFullSpec w inst .leaf offset s := by
  have hq : 0 < inst.domainSize := inst.domainSize_pos
  obtain ⟨hpow_ge1, hfit_4, -, hfit_tree, hfit_total, hcons_len_bound, -, -, -, -, hc_ge, -⟩ :=
    subtree_setup inst hw
  intro offset s hsz _ _ _ hs_fr hfit_bud _ htree hcons
  rw [NiceTree.size_leaf] at hsz hfit_bud ⊢
  have ht_eq := htree
  rw [encodeNiceTreeAux, HoldsIn.cons_iff] at ht_eq
  obtain ⟨-, htag0, -⟩ := ht_eq
  let leafArgs : LeafNodeArgs := ⟨(subtreeEnv inst).consRawPtr, (subtreeEnv inst).numCons,
    (subtreeEnv inst).descBase + 4 * offset⟩
  obtain ⟨hv_lf, hfr_lf, hframe_lf, hdesc_lf, hc_lf⟩ :=
    leafNodeProg_spec (w := w) inst.counting hq leafArgs (vars := inst.vars) hcons rfl
      (by dsimp only [leafArgs]; omega) hs_fr (hfit_total.of_le (by omega))
  have hcons_fit : Fits w ((subtreeEnv inst).consRawPtr +
      (inst.constraints.flatMap ConstraintTable.encode).length) :=
    hw.of_le (by
      rw [hcons_len_bound]; dsimp only [subtreeEnv]
      unfold TreeCSPInstance.wordBound; dsimp only; omega)
  have hmul_nc := (Nat.le_mul_of_pos_left (3 * inst.constraints.length) hpow_ge1).trans
    (hc_ge (3 * inst.constraints.length) (by omega))
  obtain ⟨hf_tree, hf_desc⟩ := fits_node hw (cur := offset) (by omega)
  obtain ⟨hstep, hst⟩ := stepsSpec_one (leafNodeProg leafArgs) htree rfl rfl
    ⟨hfit_4, hfit_tree.of_le hsz, hf_tree, hf_desc,
      Or.inl ⟨htag0, inst.domainSize, inst.constraints, hq, rfl, hcons, hcons_fit⟩⟩
    hv_lf (hfr_lf.trans (by omega)) hframe_lf
    (by dsimp only [leafArgs, subtreeEnv] at hc_lf ⊢; omega)
  exact ⟨hstep.safe, hstep.valid, hstep.result, hstep.frontier, hstep.frame,
    by rw [Nat.add_sub_cancel, hst]; exact hdesc_lf, hstep.cost⟩

/-- The subtree specification of a unary node `S` over `child`, whose header at node `cur` is
`[t, v, cur - 1, 0]`, from the specification of `child` and that of the step at the root. -/
private theorem subtree_unary {w : ℕ} (inst : TreeCSPInstance) (hw : Fits w inst.wordBound)
    (t v : ℕ) (S child : NiceTree ℕ) (hsize : S.size = child.size + 1)
    (henc : ∀ offset, encodeNiceTreeAux offset S =
      encodeNiceTreeAux offset child ++ [t, v, offset + child.size - 1, 0])
    (hexp : maxTableExp child ≤ maxTableExp S) (hmv : maxTreeVert child ≤ maxTreeVert S)
    (ih : ∀ offset s, SubtreeFullSpec w inst child offset s)
    (hroot : ∀ cur s₁, cur + 1 ≤ inst.tree.size → S.size ≤ inst.tree.size →
      maxTableExp S ≤ maxTableExp inst.tree → maxTreeVert S ≤ maxTreeVert inst.tree →
      Memory.WellFormed w s₁ → (subtreeEnv inst).descBase + 4 * inst.tree.size ≤ s₁.frontier →
      s₁.frontier + (maxTableExp inst.tree + 2 + inst.domainSize ^ maxTableExp inst.tree) ≤
        (subtreeEnv inst).descBase + 4 * inst.tree.size +
          inst.tree.size * (maxTableExp inst.tree + 2 + inst.domainSize ^ maxTableExp inst.tree) →
      HoldsIn (subtreeEnv inst).varsPtr inst.vars s₁ →
      HoldsIn (subtreeEnv inst).consRawPtr (inst.constraints.flatMap ConstraintTable.encode) s₁ →
      HoldsIn ((subtreeEnv inst).treePtr + 4 * cur) [t, v, cur - 1, 0] s₁ →
      NodeDescAt ((subtreeEnv inst).descBase + 4 * inst.tree.size) inst.counting
        inst.domainSize inst.constraints inst.vars child
        ((subtreeEnv inst).descBase + 4 * (cur - 1)) s₁ →
      StepsSpec w inst 1 cur s₁ ∧
        NodeDescAt ((subtreeEnv inst).descBase + 4 * inst.tree.size) inst.counting
          inst.domainSize inst.constraints inst.vars S ((subtreeEnv inst).descBase + 4 * cur)
          ((Memory.spec 0).clientState s₁ (iterate nodeStep (subtreeEnv inst) 1 cur))) :
    ∀ offset s, SubtreeFullSpec w inst S offset s := by
  obtain ⟨-, -, -, -, -, -, hvars_lt_desc, hcons_lt_desc, -⟩ := subtree_setup inst hw
  intro offset s hsz hexpS hmvS hwf hs_fr hbud hvars htree hcons
  have hS := hsz
  rw [hsize] at hsz hbud ⊢
  rw [henc, HoldsIn.append_iff, length_encodeNiceTreeAux] at htree
  obtain ⟨hsafe, hv, hres, hfr, hframe, hdesc, hc⟩ :=
    ih offset s (by omega) (hexp.trans hexpS) (hmv.trans hmvS) hwf hs_fr
      ((Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_succ _)) _).trans hbud) hvars
      htree.1 hcons
  have hroot₁ := htree.2.frame_outsideRange (.inl (by
    simp only [List.length_cons, List.length_nil]; dsimp only [subtreeEnv] at *; omega)) hframe
  rw [show (subtreeEnv inst).treePtr + 4 * offset + 4 * child.size =
    (subtreeEnv inst).treePtr + 4 * (offset + child.size) by ring] at hroot₁
  rw [Nat.succ_mul] at hbud
  obtain ⟨hstep, hdesc_root⟩ := hroot (offset + child.size) _ (by omega) (by omega) hexpS hmvS
    (wellFormed_clientState hwf hv) (hs_fr.trans hframe.1) (by omega)
    (hvars.frame_outsideRange (.inl (hvars_lt_desc.trans (Nat.le_add_right _ _))) hframe)
    (hcons.frame_outsideRange (.inl (hcons_lt_desc.trans (Nat.le_add_right _ _))) hframe)
    hroot₁ hdesc
  have h := StepsSpec.add (m := child.size) ⟨hsafe, hv, hres, hfr, hframe, hc⟩ hstep
  refine ⟨h.safe, h.valid, h.result, h.frontier, h.frame, ?_, h.cost⟩
  rw [clientState_iterate_add, hres, show offset + (child.size + 1) - 1 = offset + child.size
    by omega]
  exact hdesc_root

private theorem subtree_introduce {w : ℕ} (inst : TreeCSPInstance) (hw : Fits w inst.wordBound)
    (v : ℕ) (child : NiceTree ℕ) (ih : ∀ offset s, SubtreeFullSpec w inst child offset s) :
    ∀ offset s, SubtreeFullSpec w inst (.introduce v child) offset s := by
  refine subtree_unary inst hw 1 v _ child (NiceTree.size_introduce v child) (fun _ => rfl)
    (maxTableExp_le_introduce v child) (maxTreeVert_le_introduce v child) ih ?_
  intro cur s₁ hcur _ hexp hmv hwf₁ hFlo₁ hbud _ hcons₁ hroot₁ hdesc_ch
  have hq : 0 < inst.domainSize := inst.domainSize_pos
  obtain ⟨-, hfit_4, hfit_q, hfit_tree, hfit_total, -, -, hcons_lt_desc, -⟩ :=
    subtree_setup inst hw
  have hr_root := hroot₁
  rw [HoldsIn.cons_iff, HoldsIn.cons_iff, HoldsIn.cons_iff] at hr_root
  obtain ⟨-, htag1, -, harg_v, -, hch1_eq, -⟩ := hr_root
  have hbag_len_le : (v :: bagList child).length ≤ maxTableExp inst.tree :=
    (le_max_left _ _).trans hexp
  have hcbag_len_le : (bagList child).length + 1 ≤ maxTableExp inst.tree := hbag_len_le
  have hpow_le := Nat.pow_le_pow_right hq hbag_len_le
  have hs₁_peak : Fits w (s₁.frontier +
      ((v :: bagList child).length + inst.domainSize ^ (v :: bagList child).length)) :=
    hfit_total.of_le (by omega)
  have hfit_v : Fits w v := hw.of_le (by
    have hv_m : v ≤ maxTreeVert (.introduce v child) := le_max_left _ _
    have hmvt : maxTreeVert inst.tree ≤ inst.maxVarLabel :=
      le_trans (le_max_left _ _) (le_max_right _ _)
    unfold TreeCSPInstance.wordBound; dsimp only; omega)
  let introArgs : IntroNodeArgs := ⟨(subtreeEnv inst).q, v, (subtreeEnv inst).consRawPtr,
    (subtreeEnv inst).numCons, (subtreeEnv inst).descBase + 4 * (cur - 1),
    (subtreeEnv inst).descBase + 4 * cur⟩
  have hcons_le : (subtreeEnv inst).consRawPtr +
      (inst.constraints.flatMap ConstraintTable.encode).length ≤
        (subtreeEnv inst).descBase + 4 * inst.tree.size := by omega
  obtain ⟨hv_in, hfr_in, hframe_in, hdesc_in, hc_in⟩ :=
    introNodeProg_spec (w := w) inst.counting introArgs hq hwf₁ hfit_v hcons₁ rfl hcons_le
      hdesc_ch (by dsimp only [introArgs]; omega) hFlo₁ hs₁_peak
  obtain ⟨hf_tree, hf_desc⟩ := fits_node hw (cur := cur) (by omega)
  have hmul_c :
      inst.domainSize ^ (v :: bagList child).length *
        (2 + 3 * inst.constraints.length +
          inst.totalArity * (2 * (v :: bagList child).length + 3)) ≤
        inst.domainSize ^ maxTableExp inst.tree *
          (maxTableExp inst.tree ^ 2 + maxTableExp inst.tree + 4 + 3 * inst.constraints.length +
            inst.totalArity * (2 * maxTableExp inst.tree + 3)) := by
    gcongr ?_ * ?_
    have : inst.totalArity * (2 * (v :: bagList child).length + 3) ≤
        inst.totalArity * (2 * maxTableExp inst.tree + 3) := by gcongr
    omega
  obtain ⟨hstep, hst⟩ := stepsSpec_one (introNodeProg introArgs) hroot₁ rfl rfl
    ⟨hfit_4, hfit_tree.of_le hcur, hf_tree, hf_desc,
      Or.inr (Or.inl ⟨htag1, hq, hfit_q, by rw [harg_v]; exact hfit_v,
        by rw [hch1_eq]; exact (fits_node hw (by omega)).2,
        _, inst.counting, child, inst.constraints, inst.vars,
        hwf₁, rfl, hcons₁, hcons_le, by rw [hch1_eq]; exact hdesc_ch, hFlo₁,
        by rw [harg_v]; exact hs₁_peak⟩)⟩
    hv_in (hfr_in.trans (by dsimp only [introArgs, subtreeEnv]; omega)) hframe_in
    (by dsimp only [introArgs, TreeCSPInstance.totalArity, subtreeEnv] at hc_in hmul_c ⊢
        omega)
  exact ⟨hstep, by rw [hst]; exact hdesc_in⟩

private theorem subtree_forget {w : ℕ} (inst : TreeCSPInstance) (hw : Fits w inst.wordBound)
    (v : ℕ) (child : NiceTree ℕ) (ih : ∀ offset s, SubtreeFullSpec w inst child offset s) :
    ∀ offset s, SubtreeFullSpec w inst (.forget v child) offset s := by
  refine subtree_unary inst hw 2 v _ child (NiceTree.size_forget v child) (fun _ => rfl)
    (maxTableExp_le_forget v child) (maxTreeVert_le_forget v child) ih ?_
  intro cur s₁ hcur hS hexp hmv _ hFlo₁ hbud hvars₁ _ hroot₁ hdesc_ch
  have hq : 0 < inst.domainSize := inst.domainSize_pos
  obtain ⟨hpow_ge1, hfit_4, hfit_q, hfit_tree, hfit_total, -, hvars_lt_desc, -, -,
    hperSpace_le_total, hc_ge, hfit_tree_vert⟩ := subtree_setup inst hw
  have hr_root := hroot₁
  rw [HoldsIn.cons_iff, HoldsIn.cons_iff, HoldsIn.cons_iff] at hr_root
  obtain ⟨-, htag2, -, harg_v, -, hch1_eq, -⟩ := hr_root
  have hLB_succ_le : ((bagList child).erase v).length + 1 ≤ maxTableExp inst.tree :=
    (le_max_left _ _).trans hexp
  have hcbag_len_le : (bagList child).length ≤ maxTableExp inst.tree :=
    (bagList_length_le_maxTableExp child).trans ((maxTableExp_le_forget v child).trans hexp)
  have hpow_ch_le := Nat.pow_le_pow_right hq hcbag_len_le
  have hpow_LB1_le := Nat.pow_le_pow_right hq hLB_succ_le
  have hpow_LB_le : inst.domainSize ^ ((bagList child).erase v).length ≤
      inst.domainSize ^ maxTableExp inst.tree :=
    Nat.pow_le_pow_right hq (by omega)
  have hfit_cPow : Fits w (inst.domainSize ^ (bagList child).length) :=
    hfit_total.of_le (by omega)
  have hfit_vars : Fits w ((subtreeEnv inst).varsPtr + (subtreeEnv inst).varsLen) :=
    hfit_total.of_le (by omega)
  have hs₁_peak : Fits w (s₁.frontier + max (bagList child).length
      (((bagList child).erase v).length + inst.domainSize ^ ((bagList child).erase v).length)) :=
    hfit_total.of_le (by omega)
  have hfit_cap := fits_cap hw hS
  have hfit_bag_el := hfit_tree_vert child ((maxTreeVert_le_forget v child).trans hmv)
  let fgArgs : ForgetNodeArgs :=
    ⟨(subtreeEnv inst).mode, (subtreeEnv inst).q, v, (subtreeEnv inst).varsPtr,
      (subtreeEnv inst).varsLen, (subtreeEnv inst).descBase + 4 * (cur - 1),
      (subtreeEnv inst).descBase + 4 * cur⟩
  obtain ⟨hv_fg, hfr_fg, hframe_fg, hdesc_fg, hc_fg⟩ :=
    forgetNodeProg_spec (w := w) inst.counting fgArgs hq rfl hvars₁ rfl
      hfit_bag_el hdesc_ch (by dsimp only [fgArgs]; omega) hFlo₁ hs₁_peak hfit_cap
  obtain ⟨hf_tree, hf_desc⟩ := fits_node hw (cur := cur) (by omega)
  have hfg_mul :
      inst.domainSize ^ ((bagList child).erase v).length *
          (inst.domainSize * ((bagList child).length * (((bagList child).erase v).length + 1) +
            1) + 1) ≤
        inst.domainSize ^ maxTableExp inst.tree * (maxTableExp inst.tree ^ 2 + 2) :=
    calc _ = inst.domainSize ^ (((bagList child).erase v).length + 1) *
            ((bagList child).length * (((bagList child).erase v).length + 1) + 1) +
          inst.domainSize ^ ((bagList child).erase v).length := by
          rw [Nat.pow_succ]; ring
      _ ≤ inst.domainSize ^ maxTableExp inst.tree *
            (maxTableExp inst.tree * maxTableExp inst.tree + 1) +
          inst.domainSize ^ maxTableExp inst.tree := by gcongr
      _ = _ := by ring
  have hqE_mul : inst.domainSize ^ maxTableExp inst.tree * (maxTableExp inst.tree ^ 2 + 2) +
      2 * inst.domainSize ^ maxTableExp inst.tree ≤
        inst.domainSize ^ maxTableExp inst.tree *
          (maxTableExp inst.tree ^ 2 + maxTableExp inst.tree + 4) := by
    rw [show inst.domainSize ^ maxTableExp inst.tree * (maxTableExp inst.tree ^ 2 + 2) +
      2 * inst.domainSize ^ maxTableExp inst.tree =
        inst.domainSize ^ maxTableExp inst.tree * (maxTableExp inst.tree ^ 2 + 4) by ring]
    gcongr; omega
  have hmul_c := hc_ge (maxTableExp inst.tree ^ 2 + maxTableExp inst.tree + 4) (by omega)
  obtain ⟨hstep, hst⟩ := stepsSpec_one (forgetNodeProg fgArgs) hroot₁ rfl rfl
    ⟨hfit_4, hfit_tree.of_le hcur, hf_tree, hf_desc,
      Or.inr (Or.inr (Or.inl ⟨htag2, hq, hfit_q, hfit_vars,
        by rw [hch1_eq]; exact (fits_node hw (by omega)).2,
        _, inst.counting, child, inst.constraints, inst.vars,
        rfl, hfit_bag_el, by rw [hch1_eq]; exact hdesc_ch, hFlo₁,
        hfit_cPow, by rw [harg_v]; exact hs₁_peak, by rw [harg_v]; exact hfit_cap⟩))⟩
    hv_fg (hfr_fg.trans (by dsimp only [fgArgs, subtreeEnv]; omega)) hframe_fg
    (by dsimp only [fgArgs, subtreeEnv] at hc_fg ⊢; omega)
  exact ⟨hstep, by rw [hst]; exact hdesc_fg⟩

/-- The step at the root `cur` of a join whose children's descriptors are in place. -/
private theorem join_root {w : ℕ} (inst : TreeCSPInstance) (hw : Fits w inst.wordBound)
    (left right : NiceTree ℕ) (mid cur : ℕ) (s₂ : Memory.State) (hmid : mid ≤ cur)
    (hcur : cur + 1 ≤ inst.tree.size) (hS : (NiceTree.join left right).size ≤ inst.tree.size)
    (hexp_l : maxTableExp left ≤ maxTableExp inst.tree)
    (hexp_r : maxTableExp right ≤ maxTableExp inst.tree)
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
    StepsSpec w inst 1 cur s₂ ∧
      NodeDescAt ((subtreeEnv inst).descBase + 4 * inst.tree.size)
        inst.counting inst.domainSize inst.constraints inst.vars (.join left right)
        ((subtreeEnv inst).descBase + 4 * cur)
        ((Memory.spec 0).clientState s₂ (iterate nodeStep (subtreeEnv inst) 1 cur)) := by
  have hq : 0 < inst.domainSize := inst.domainSize_pos
  obtain ⟨-, hfit_4, hfit_q, hfit_tree, hfit_total, -, -, -, -, hperSpace_le_total, hc_ge, -⟩ :=
    subtree_setup inst hw
  have hr_root := hroot₂
  rw [HoldsIn.cons_iff, HoldsIn.cons_iff, HoldsIn.cons_iff, HoldsIn.cons_iff] at hr_root
  obtain ⟨-, htag3, -, -, -, hch1_eq, -, hch2_eq, -⟩ := hr_root
  have hllen_le := (bagList_length_le_maxTableExp left).trans hexp_l
  have hrlen_le := (bagList_length_le_maxTableExp right).trans hexp_r
  have hpow_l_le := Nat.pow_le_pow_right hq hllen_le
  have hpow_r_le := Nat.pow_le_pow_right hq hrlen_le
  have hfit_rPow : Fits w (inst.domainSize ^ (bagList right).length) :=
    hfit_total.of_le (by omega)
  have hs₂_peak : Fits w (s₂.frontier + inst.domainSize ^ (bagList left).length) :=
    hfit_total.of_le hfr_bound
  have hfit_cap := fits_cap hw hS
  let jnArgs : JoinNodeArgs := ⟨(subtreeEnv inst).q, (subtreeEnv inst).descBase + 4 * (mid - 1),
    (subtreeEnv inst).descBase + 4 * (cur - 1), (subtreeEnv inst).descBase + 4 * cur⟩
  obtain ⟨hv_jn, hfr_jn, hframe_jn, hdesc_jn, hc_jn⟩ :=
    joinNodeProg_spec (w := w) inst.counting jnArgs hq hdesc_l₂ hdesc_r
      (by dsimp only [jnArgs]; omega) hFlo₂ hs₂_peak hfit_cap
  obtain ⟨hf_tree, hf_desc⟩ := fits_node hw (cur := cur) (by omega)
  have hjn_mul :
      inst.domainSize ^ (bagList left).length *
          ((bagList right).length * ((bagList left).length + 1) + 3) ≤
        inst.domainSize ^ maxTableExp inst.tree *
          (maxTableExp inst.tree ^ 2 + maxTableExp inst.tree + 4) :=
    calc _ ≤ inst.domainSize ^ maxTableExp inst.tree *
          (maxTableExp inst.tree * (maxTableExp inst.tree + 1) + 3) := by gcongr
      _ ≤ _ := Nat.mul_le_mul_left _ (by ring_nf; omega)
  have hmul_c := hc_ge (maxTableExp inst.tree ^ 2 + maxTableExp inst.tree + 4) (by omega)
  obtain ⟨hstep, hst⟩ := stepsSpec_one (joinNodeProg jnArgs) hroot₂ rfl rfl
    ⟨hfit_4, hfit_tree.of_le hcur, hf_tree, hf_desc,
      Or.inr (Or.inr (Or.inr ⟨ne_of_eq_of_ne htag3 (by decide),
        ne_of_eq_of_ne htag3 (by decide), ne_of_eq_of_ne htag3 (by decide), hq, hfit_q,
        by rw [hch1_eq]; exact (fits_node hw (by omega)).2,
        by rw [hch2_eq]; exact (fits_node hw (cur := cur - 1) (by omega)).2.of_le (Nat.le_succ _),
        _, inst.counting, left, right, inst.constraints, inst.vars,
        by rw [hch1_eq]; exact hdesc_l₂, by rw [hch2_eq]; exact hdesc_r,
        hfit_rPow, hs₂_peak, hfit_cap⟩))⟩
    hv_jn (hfr_jn.trans (by dsimp only [jnArgs, subtreeEnv]; omega)) hframe_jn
    (by dsimp only [jnArgs, subtreeEnv] at hc_jn ⊢; omega)
  exact ⟨hstep, by rw [hst]; exact hdesc_jn⟩

private theorem subtree_join {w : ℕ} (inst : TreeCSPInstance) (hw : Fits w inst.wordBound)
    (left right : NiceTree ℕ)
    (ihl : ∀ offset s, SubtreeFullSpec w inst left offset s)
    (ihr : ∀ offset s, SubtreeFullSpec w inst right offset s) :
    ∀ offset s, SubtreeFullSpec w inst (.join left right) offset s := by
  have hq : 0 < inst.domainSize := inst.domainSize_pos
  obtain ⟨-, -, -, -, -, -, hvars_lt_desc, hcons_lt_desc, -⟩ := subtree_setup inst hw
  intro offset s hsz hexp hmv hwf hs_fr hfit_bud hvars htree hcons
  have hS := hsz
  rw [NiceTree.size_join] at hsz hfit_bud ⊢
  have hsz_l_pos := NiceTree.size_pos left
  have hsz_r_pos := NiceTree.size_pos right
  have hexp_l := (maxTableExp_le_join_left left right).trans hexp
  have hexp_r := (maxTableExp_le_join_right left right).trans hexp
  rw [encodeNiceTreeAux, List.append_assoc, HoldsIn.append_iff, length_encodeNiceTreeAux,
    HoldsIn.append_iff, length_encodeNiceTreeAux] at htree
  obtain ⟨htree_l, htree_r0, hroot_hold⟩ := htree
  rw [Nat.add_mul, Nat.add_mul, Nat.one_mul] at hfit_bud
  obtain ⟨hsafe_l, hv_l, hres_l, hfr_l, hframe_l, hdesc_l, hc_l⟩ :=
    ihl offset s (by omega) hexp_l ((maxTreeVert_le_join_left left right).trans hmv) hwf hs_fr
      (by omega) hvars htree_l hcons
  have hl : StepsSpec w inst left.size offset s :=
    ⟨hsafe_l, hv_l, hres_l, hfr_l, hframe_l, hc_l⟩
  obtain ⟨s₁, hs₁_def⟩ : ∃ s₁, (Memory.spec 0).clientState s
      (iterate nodeStep (subtreeEnv inst) left.size offset) = s₁ := ⟨_, rfl⟩
  rw [hs₁_def] at hfr_l hframe_l hdesc_l
  have htree_r₁ : HoldsIn ((subtreeEnv inst).treePtr + 4 * (offset + left.size))
      (encodeNiceTreeAux (offset + left.size) right) s₁ := by
    rw [show (subtreeEnv inst).treePtr + 4 * (offset + left.size) =
      (subtreeEnv inst).treePtr + 4 * offset + 4 * left.size by ring]
    exact htree_r0.frame_outsideRange (.inl (by
      rw [length_encodeNiceTreeAux]; dsimp only [subtreeEnv] at *; omega)) hframe_l
  have hroot₁ : HoldsIn ((subtreeEnv inst).treePtr + 4 * (offset + left.size + right.size))
      [3, 0, offset + left.size - 1, offset + left.size + right.size - 1] s₁ := by
    rw [show (subtreeEnv inst).treePtr + 4 * (offset + left.size + right.size) =
      (subtreeEnv inst).treePtr + 4 * offset + 4 * left.size + 4 * right.size by ring]
    exact hroot_hold.frame_outsideRange (.inl (by
      simp only [List.length_cons, List.length_nil]; dsimp only [subtreeEnv] at *; omega))
      hframe_l
  obtain ⟨hsafe_r, hv_r, hres_r, hfr_r, hframe_r, hdesc_r, hc_r⟩ :=
    ihr (offset + left.size) s₁ (by omega) hexp_r
      ((maxTreeVert_le_join_right left right).trans hmv)
      (hs₁_def ▸ wellFormed_clientState hwf hv_l) (hs_fr.trans hframe_l.1) (by omega)
      (hvars.frame_outsideRange (.inl (hvars_lt_desc.trans (Nat.le_add_right _ _))) hframe_l)
      htree_r₁
      (hcons.frame_outsideRange (.inl (hcons_lt_desc.trans (Nat.le_add_right _ _))) hframe_l)
  have hr : StepsSpec w inst right.size (offset + left.size) s₁ :=
    ⟨hsafe_r, hv_r, hres_r, hfr_r, hframe_r, hc_r⟩
  obtain ⟨s₂, hs₂_def⟩ : ∃ s₂, (Memory.spec 0).clientState s₁
      (iterate nodeStep (subtreeEnv inst) right.size (offset + left.size)) = s₂ := ⟨_, rfl⟩
  rw [hs₂_def] at hfr_r hframe_r hdesc_r
  have hpow_l_le : inst.domainSize ^ (bagList left).length ≤
      inst.domainSize ^ maxTableExp inst.tree :=
    Nat.pow_le_pow_right hq ((bagList_length_le_maxTableExp left).trans hexp_l)
  obtain ⟨hroot, hdesc_root⟩ := join_root inst hw left right (offset + left.size)
    (offset + left.size + right.size) s₂ (by omega) (by omega) (by omega) hexp_l hexp_r
    (hs_fr.trans (hframe_l.1.trans hframe_r.1)) (by omega)
    (hroot₁.frame_outsideRange (.inl (by
      simp only [List.length_cons, List.length_nil]; dsimp only [subtreeEnv] at *; omega))
      hframe_r)
    (hdesc_l.frame (.inl (by omega)) (by omega) hframe_r) hdesc_r
  have hlr := hl.add (by rw [hs₁_def]; exact hr)
  have hst_lr : (Memory.spec 0).clientState s
      (iterate nodeStep (subtreeEnv inst) (left.size + right.size) offset) = s₂ := by
    rw [clientState_iterate_add, hres_l, hs₁_def, hs₂_def]
  have h := hlr.add (by rw [hst_lr, ← Nat.add_assoc]; exact hroot)
  refine ⟨h.safe, h.valid, h.result, h.frontier, h.frame, ?_, h.cost⟩
  rw [clientState_iterate_add, hlr.result, hst_lr,
    show offset + (left.size + right.size + 1) - 1 = offset + left.size + right.size by omega,
    show offset + (left.size + right.size) = offset + left.size + right.size by omega]
  exact hdesc_root

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
