/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.VariableElimination.Memory
import CslibFrontier.Tactic.Realize

/-!
# Word-Block Copy (`copyWords`) and Inequality Filter (`filterNe`)

Realizable Word-RAM primitives copying a word range (`copyWords`) and filtering out occurrences of a
single variable from an array (`filterNe`).

## Main definitions

* `Cslib.Algorithms.WordRAM.VariableElimination.copyWords`: contiguous block copy.
* `Cslib.Algorithms.WordRAM.VariableElimination.filterNe`: append-only filter keeping words `≠ key`.
-/

public section

namespace Cslib.Algorithms.WordRAM.VariableElimination

open Cslib.Logic.PL Cslib.Logic.PL.CSP
open Cslib.Algorithms.Lean.CSP
open Cslib.DataStructure
open Cslib.WordRAM
open Cslib.WordRAM.Realization

/-! ### Primitive 2: Block copy (`copyWords`) and inequality filter (`filterNe`) -/

/-- Arguments `(src, dst, len)` for `copyWords`. -/
structure CopyArgs where
  /-- Field `src` of `CopyArgs`. -/
  src : ℕ
  /-- Field `dst` of `CopyArgs`. -/
  dst : ℕ
  /-- Field `len` of `CopyArgs`. -/
  len : ℕ

/-- Product equivalence encoding `CopyArgs` as words. -/
@[expose] def CopyArgs.equiv : CopyArgs ≃ (ℕ × ℕ) × ℕ where
  toFun a := ((a.src, a.dst), a.len)
  invFun := fun ((src, dst), len) => ⟨src, dst, len⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : WordEncoding CopyArgs := .ofEquiv CopyArgs.equiv

private structure CopyState where
  src : ℕ
  dst : ℕ

private def CopyState.equiv : CopyState ≃ ℕ × ℕ where
  toFun s := (s.src, s.dst)
  invFun := fun (src, dst) => ⟨src, dst⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding CopyState := .ofEquiv CopyState.equiv

private def copyWordsStep (env : Unit × CopyState) : Memory.Prog CopyState := do
  let v ← Memory.read env.2.src
  Memory.write env.2.dst v
  pure ⟨env.2.src + 1, env.2.dst + 1⟩

/-- Copy `len` consecutive words from `src` to `dst`. -/
def copyWords (args : CopyArgs) : Memory.Prog Unit := do
  let _ ← iterate copyWordsStep () args.len ⟨args.src, args.dst⟩
  pure ()

theorem copyWords_cost (args : CopyArgs) (s : Memory.State) :
    memoryCost (copyWords args) s ≤ 2 * args.len := by
  unfold copyWords
  rw [memoryCost_bind', memoryCost_pure, Nat.add_zero]
  exact memoryCost_iterate_le_of copyWordsStep 2 () (fun _ _ => le_rfl) args.len
    ⟨args.src, args.dst⟩ s

theorem copyWords_spec {w : ℕ} (args : CopyArgs) {xs : List ℕ} {F : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s)
    (hxs : Block.HoldsList args.src xs s.mem) (hlen : xs.length = args.len)
    (hsrcF : args.src + args.len ≤ F) (hFdst : F ≤ args.dst)
    (hdst : args.dst + args.len ≤ s.frontier) :
    let s' := (Memory.spec 0).clientState s (copyWords args)
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (copyWords args)) ∧
      s'.frontier = s.frontier ∧
      PreservesBelow F s s' ∧
      Block.HoldsList args.dst xs s'.mem := by
  dsimp only
  unfold copyWords
  rw [StateTransitionSpec.clientState_bind]
  have haux : ∀ (ys : List ℕ) (src dst G : ℕ) (t : Memory.State),
      Memory.WellFormed w t →
      Block.HoldsList src ys t.mem →
      src + ys.length ≤ G → G ≤ dst → dst + ys.length ≤ t.frontier →
      let t' := (Memory.spec 0).clientState t (iterate copyWordsStep () ys.length ⟨src, dst⟩)
      (Memory.spec w).ValidHistory t
        ((Memory.spec w).clientHistory t (iterate copyWordsStep () ys.length ⟨src, dst⟩)) ∧
      t'.frontier = t.frontier ∧
      PreservesBelow G t t' ∧
      Block.HoldsList dst ys t'.mem := by
    intro ys
    induction ys with
    | nil =>
      intro src dst G t _ _ _ hGdst hdstF
      exact ⟨validHistory_pure w t _, rfl, PreservesBelow.refl (by omega),
        Block.holdsList_nil dst t.mem⟩
    | cons v rest ih =>
      intro src dst G t hwf_t hys hsrcG hGdst hdstF
      simp only [List.length_cons] at hsrcG hdstF
      obtain ⟨hhead, htail⟩ := Block.holdsList_cons_iff.mp hys
      have hsrc_lt : src < t.frontier := by omega
      have hdst_lt : dst < t.frontier := by omega
      have hv_fit : Fits w v := hhead ▸ hwf_t.mem_fits src
      let t₁ : Memory.State := ⟨Function.update t.mem dst v, t.frontier⟩
      have hwf₁ : Memory.WellFormed w t₁ := hwf_t.step (o := .write dst v) ⟨hdst_lt, hv_fit⟩
      have htail₁ : Block.HoldsList (src + 1) rest t₁.mem :=
        htail.frame fun a _ hhi => Function.update_of_ne (by omega) v t.mem
      obtain ⟨hval_rest, hfr_rest, hpres_rest, hholds_rest⟩ :=
        ih (src + 1) (dst + 1) (dst + 1) t₁ hwf₁ htail₁ (by omega) le_rfl
          (by dsimp only [t₁]; omega)
      have hiter_eq : iterate copyWordsStep () (v :: rest).length ⟨src, dst⟩ =
          (copyWordsStep ((), ⟨src, dst⟩) >>= iterate copyWordsStep () rest.length) := rfl
      dsimp only
      rw [hiter_eq, StateTransitionSpec.clientState_bind]
      have hstep_st : (Memory.spec 0).clientState t (copyWordsStep ((), ⟨src, dst⟩)) = t₁ := by
        change (⟨Function.update t.mem dst (t.mem src), t.frontier⟩ : Memory.State) = t₁
        rw [hhead]
      have hstep_res : (Memory.spec 0).clientResult t (copyWordsStep ((), ⟨src, dst⟩)) =
          ⟨src + 1, dst + 1⟩ := rfl
      have hstep_val : (Memory.spec w).ValidHistory t
          ((Memory.spec w).clientHistory t (copyWordsStep ((), ⟨src, dst⟩))) :=
        validHistory_read_bind hsrc_lt
          (validHistory_write_bind hdst_lt (hwf_t.mem_fits src) (validHistory_pure w _ _))
      rw [hstep_st, hstep_res]
      refine ⟨validHistory_bind_step hstep_val (by simpa [hstep_st, hstep_res] using hval_rest),
        hfr_rest, ?_, ?_⟩
      · refine ⟨by omega, le_of_eq hfr_rest.symm, fun a ha => ?_⟩
        have ha_lt : a < dst + 1 := by omega
        have hne : a ≠ dst := by omega
        rw [hpres_rest.2.2 a ha_lt]
        exact Function.update_of_ne hne v t.mem
      · refine Block.holdsList_cons_iff.mpr ⟨?_, hholds_rest⟩
        have hdst_lt1 : dst < dst + 1 := by omega
        rw [hpres_rest.2.2 dst hdst_lt1]
        exact Function.update_self dst v t.mem
  rw [← hlen] at hsrcF hdst ⊢
  obtain ⟨hv, hfr, hpres, hholds⟩ := haux xs args.src args.dst F s hwf hxs hsrcF hFdst hdst
  exact ⟨validHistory_bind_step hv (validHistory_pure w _ _), hfr, hpres, hholds⟩

theorem copyWords_realizes :
    Realizes .exact copyWords WordEncoding.encode WordEncoding.encode
      (fun w args _ => Fits w (args.src + args.len) ∧ Fits w (args.dst + args.len))
      (fun _ _ => 0) := by
  unfold copyWords
  realize
  refine iterationSafe_of_stepInv _ _ w d
    (fun j st _ => st.src + j = d.src + d.len ∧ st.dst + j = d.dst + d.len)
    (fun j st t hinv => ?_) ⟨rfl, rfl⟩
  dsimp only
  refine ⟨⟨h.1.of_le (by omega), h.2.of_le (by omega)⟩, ?_⟩
  change (st.src + 1) + j = d.src + d.len ∧ (st.dst + 1) + j = d.dst + d.len
  omega

private structure FilterState where
  src : ℕ
  dst : ℕ
  count : ℕ

private def FilterState.equiv : FilterState ≃ (ℕ × ℕ) × ℕ where
  toFun s := ((s.src, s.dst), s.count)
  invFun := fun ((src, dst), count) => ⟨src, dst, count⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding FilterState := .ofEquiv FilterState.equiv

private def filterNeStep (env : ℕ × FilterState) : Memory.Prog FilterState := do
  let v ← Memory.read env.2.src
  if v = env.1 then
    pure ⟨env.2.src + 1, env.2.dst, env.2.count⟩
  else
    Memory.write env.2.dst v >>= fun _ =>
      pure ⟨env.2.src + 1, env.2.dst + 1, env.2.count + 1⟩

/-- Copy entries of `[ptr, ptr + len)` distinct from `key` to the frontier. -/
def filterNe (args : MemScanArgs) : Memory.Prog (ℕ × ℕ) := do
  let dst ← Memory.allocDirty args.len
  let res ← iterate filterNeStep args.target args.len ⟨args.base, dst, 0⟩
  pure (dst, res.count)

theorem filterNe_cost (args : MemScanArgs) (s : Memory.State) :
    memoryCost (filterNe args) s ≤ 1 + 2 * args.len := by
  unfold filterNe
  rw [memoryCost_bind', memoryCost_allocDirty, memoryCost_bind', memoryCost_pure, Nat.add_zero]
  have hstep : ∀ a t, memoryCost (filterNeStep (args.target, a)) t ≤ 2 := by
    intro a t
    unfold filterNeStep
    rw [memoryCost_bind', memoryCost_read]
    dsimp only
    rw [memoryCost_ite]
    split_ifs
    · simp
    · rw [memoryCost_bind', memoryCost_write, memoryCost_pure]
  have hiter := memoryCost_iterate_le_of filterNeStep 2 args.target hstep args.len
    ⟨args.base, s.frontier, 0⟩ ⟨s.mem, s.frontier + args.len⟩
  exact Nat.add_le_add_left hiter 1

theorem filterNe_spec {w : ℕ} (args : MemScanArgs) {xs : List ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s)
    (hxs : HoldsIn args.base xs s) (hlen : xs.length = args.len)
    (hfit : Fits w (s.frontier + args.len)) :
    let res := (Memory.spec 0).clientResult s (filterNe args)
    let s' := (Memory.spec 0).clientState s (filterNe args)
    let out := xs.filter fun v => decide (v ≠ args.target)
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (filterNe args)) ∧
      s'.frontier = s.frontier + args.len ∧
      PreservesBelow s.frontier s s' ∧
      res.1 = s.frontier ∧
      res.2 = out.length ∧
      HoldsIn res.1 out s' := by
  dsimp only
  unfold filterNe
  have halloc_val : (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (Memory.allocDirty args.len)) :=
    validHistory_allocDirty hfit
  let s₀ : Memory.State := ⟨s.mem, s.frontier + args.len⟩
  have hwf₀ : Memory.WellFormed w s₀ := hwf.step (o := .allocDirty args.len) hfit
  have haux : ∀ (ys : List ℕ) (src dst cnt G : ℕ) (t : Memory.State),
      Memory.WellFormed w t →
      Block.HoldsList src ys t.mem →
      src + ys.length ≤ G → G ≤ dst → dst + ys.length ≤ t.frontier →
      let p := iterate filterNeStep args.target ys.length ⟨src, dst, cnt⟩
      let r := (Memory.spec 0).clientResult t p
      let t' := (Memory.spec 0).clientState t p
      let out := ys.filter fun v => decide (v ≠ args.target)
      (Memory.spec w).ValidHistory t ((Memory.spec w).clientHistory t p) ∧
      t'.frontier = t.frontier ∧
      PreservesBelow G t t' ∧
      r.count = cnt + out.length ∧
      Block.HoldsList dst out t'.mem := by
    intro ys
    induction ys with
    | nil =>
      intro src dst cnt G t _ _ _ hGdst hdstF
      exact ⟨validHistory_pure w t _, rfl, PreservesBelow.refl (by omega), rfl,
        Block.holdsList_nil dst t.mem⟩
    | cons v rest ih =>
      intro src dst cnt G t hwf_t hys hsrcG hGdst hdstF
      simp only [List.length_cons] at hsrcG hdstF
      obtain ⟨hhead, htail⟩ := Block.holdsList_cons_iff.mp hys
      have hsrc_lt : src < t.frontier := by omega
      have hiter_eq : iterate filterNeStep args.target (v :: rest).length ⟨src, dst, cnt⟩ =
          (filterNeStep (args.target, ⟨src, dst, cnt⟩) >>=
            iterate filterNeStep args.target rest.length) := rfl
      dsimp only
      rw [hiter_eq, StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind]
      by_cases hvx : v = args.target
      · have hstep_val : (Memory.spec w).ValidHistory t
            ((Memory.spec w).clientHistory t (filterNeStep (args.target, ⟨src, dst, cnt⟩))) := by
          refine validHistory_read_bind hsrc_lt ?_
          rw [hhead, ite_eq_left hvx]
          exact validHistory_pure w t _
        have hstep_st : (Memory.spec 0).clientState t
            (filterNeStep (args.target, ⟨src, dst, cnt⟩)) = t := by
          unfold filterNeStep
          change (Memory.spec 0).clientState t (if t.mem src = args.target then _ else _) = t
          rw [hhead, ite_eq_left hvx]; rfl
        have hstep_res : (Memory.spec 0).clientResult t
            (filterNeStep (args.target, ⟨src, dst, cnt⟩)) = ⟨src + 1, dst, cnt⟩ := by
          unfold filterNeStep
          change (Memory.spec 0).clientResult t (if t.mem src = args.target then _ else _) = _
          rw [hhead, ite_eq_left hvx]; rfl
        rw [hstep_st, hstep_res]
        obtain ⟨hval_r, hfr_r, hpres_r, hcnt_r, hholds_r⟩ :=
          ih (src + 1) dst cnt G t hwf_t htail (by omega) hGdst (by omega)
        simp only [List.filter_cons, hvx, ne_eq, not_true_eq_false, decide_false,
          Bool.false_eq_true, ↓reduceIte]
        exact ⟨validHistory_bind_step hstep_val (by simpa [hstep_st, hstep_res] using hval_r),
          hfr_r, hpres_r, hcnt_r, hholds_r⟩
      · have hdst_lt : dst < t.frontier := by omega
        let t₁ : Memory.State := ⟨Function.update t.mem dst v, t.frontier⟩
        have hv_fit : Fits w v := hhead ▸ hwf_t.mem_fits src
        have hwf₁ : Memory.WellFormed w t₁ := hwf_t.step (o := .write dst v) ⟨hdst_lt, hv_fit⟩
        have hstep_val : (Memory.spec w).ValidHistory t
            ((Memory.spec w).clientHistory t (filterNeStep (args.target, ⟨src, dst, cnt⟩))) := by
          refine validHistory_read_bind hsrc_lt ?_
          rw [hhead, ite_eq_right hvx]
          exact validHistory_write_bind hdst_lt hv_fit (validHistory_pure w _ _)
        have hstep_st : (Memory.spec 0).clientState t
            (filterNeStep (args.target, ⟨src, dst, cnt⟩)) = t₁ := by
          unfold filterNeStep
          change (Memory.spec 0).clientState t (if t.mem src = args.target then _ else _) = t₁
          rw [hhead, ite_eq_right hvx]; rfl
        have hstep_res : (Memory.spec 0).clientResult t
            (filterNeStep (args.target, ⟨src, dst, cnt⟩)) = ⟨src + 1, dst + 1, cnt + 1⟩ := by
          unfold filterNeStep
          change (Memory.spec 0).clientResult t (if t.mem src = args.target then _ else _) = _
          rw [hhead, ite_eq_right hvx]; rfl
        have htail₁ : Block.HoldsList (src + 1) rest t₁.mem :=
          htail.frame fun a _ hhi => Function.update_of_ne (by omega) v t.mem
        rw [hstep_st, hstep_res]
        have ht₁_fr : t₁.frontier = t.frontier := rfl
        obtain ⟨hval_r, hfr_r, hpres_r, hcnt_r, hholds_r⟩ :=
          ih (src + 1) (dst + 1) (cnt + 1) (dst + 1) t₁ hwf₁ htail₁
            (by omega) le_rfl (by omega)
        simp only [List.filter_cons, decide_eq_true hvx, ↓reduceIte, List.length_cons]
        refine ⟨validHistory_bind_step hstep_val (by simpa [hstep_st, hstep_res] using hval_r),
          hfr_r, ?_, by omega, ?_⟩
        · refine ⟨by omega, le_of_eq hfr_r.symm, fun a ha => ?_⟩
          have ha_lt : a < dst + 1 := by omega
          have hne : a ≠ dst := by omega
          rw [hpres_r.2.2 a ha_lt]
          exact Function.update_of_ne hne v t.mem
        · refine Block.holdsList_cons_iff.mpr ⟨?_, hholds_r⟩
          have hdst_lt1 : dst < dst + 1 := by omega
          rw [hpres_r.2.2 dst hdst_lt1]
          exact Function.update_self dst v t.mem
  have hbase_le : args.base + xs.length ≤ s.frontier := hxs.1
  have halloc_val' : (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (Memory.allocDirty xs.length)) := by
    rw [hlen]; exact halloc_val
  have hwf₀' : Memory.WellFormed w ⟨s.mem, s.frontier + xs.length⟩ := by
    rw [hlen]; exact hwf₀
  obtain ⟨hv, hfr, hpres, hcnt, hholds⟩ :=
    haux xs args.base s.frontier 0 s.frontier ⟨s.mem, s.frontier + xs.length⟩ hwf₀' hxs.2 hbase_le
      le_rfl (by simp)
  rw [← hlen]
  rw [StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind,
    StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind]
  have ha_res : (Memory.spec 0).clientResult s (Memory.allocDirty xs.length) = s.frontier := rfl
  have ha_st : (Memory.spec 0).clientState s (Memory.allocDirty xs.length) =
      ⟨s.mem, s.frontier + xs.length⟩ := rfl
  rw [ha_res, ha_st]
  have hpure_st {α : Type} (x : α) (t : Memory.State) :
      (Memory.spec 0).clientState t (pure x) = t := rfl
  have hpure_res {α : Type} (x : α) (t : Memory.State) :
      (Memory.spec 0).clientResult t (pure x) = x := rfl
  rw [hpure_st, hpure_res]
  have hout_le : (xs.filter fun v => decide (v ≠ args.target)).length ≤ xs.length :=
    List.length_filter_le _ _
  refine ⟨validHistory_bind_step halloc_val'
    (validHistory_bind_step hv (validHistory_pure w _ _)), hfr, ?_, rfl, by omega, ?_⟩
  · exact ⟨le_rfl, (Nat.le_add_right _ _).trans (le_of_eq hfr.symm), hpres.2.2⟩
  · refine ⟨?_, hholds⟩
    rw [hfr]
    dsimp only
    omega

private theorem filterNeStep_result (target : ℕ) (st : FilterState) (t : Memory.State) :
    (Memory.spec 0).clientResult t (filterNeStep (target, st)) =
      if t.mem st.src = target then ⟨st.src + 1, st.dst, st.count⟩
      else ⟨st.src + 1, st.dst + 1, st.count + 1⟩ := by
  unfold filterNeStep
  change (Memory.spec 0).clientResult t
    (if t.mem st.src = target then
      (pure ⟨st.src + 1, st.dst, st.count⟩ : Memory.Prog FilterState)
     else
      Memory.write st.dst (t.mem st.src) >>= fun _ =>
        pure ⟨st.src + 1, st.dst + 1, st.count + 1⟩) = _
  split_ifs <;> rfl

theorem filterNe_realizes :
    Realizes .exact filterNe WordEncoding.encode WordEncoding.encode
      (fun w args s => Fits w (args.base + args.len) ∧ Fits w (s.frontier + args.len))
      (fun _ _ => 0) := by
  unfold filterNe
  realize
  refine iterationSafe_of_stepInv _ _ w _
    (fun j st _ => st.src + j = d.base + d.len ∧ st.dst + j ≤ s.frontier + d.len ∧
      st.count + j ≤ d.len)
    (fun j st t ⟨hsrc, hdst, hcnt⟩ => ?_)
    ⟨rfl, le_rfl, by simp⟩
  dsimp only
  refine ⟨?_, ?_⟩
  · split_ifs
    · exact h.1.of_le (by omega)
    · exact ⟨h.1.of_le (by omega), h.2.of_le (by omega), h.1.of_le (by omega)⟩
  · rw [filterNeStep_result]
    split_ifs <;> (dsimp only; omega)

theorem copyWords_frame (args : CopyArgs) (t : Memory.State) :
    ((Memory.spec 0).clientState t (copyWords args)).frontier = t.frontier ∧
    ∀ a, a < args.dst → ((Memory.spec 0).clientState t (copyWords args)).mem a = t.mem a := by
  unfold copyWords
  rw [StateTransitionSpec.clientState_bind]
  have hpure_st {α : Type} (x : α) (u : Memory.State) :
      (Memory.spec 0).clientState u (pure x) = u := rfl
  rw [hpure_st]
  suffices ∀ (n src dst : ℕ) (u : Memory.State),
      ((Memory.spec 0).clientState u (iterate copyWordsStep () n ⟨src, dst⟩)).frontier =
        u.frontier ∧
      ∀ a, a < dst →
        ((Memory.spec 0).clientState u (iterate copyWordsStep () n ⟨src, dst⟩)).mem a = u.mem a by
    exact this args.len args.src args.dst t
  intro n
  induction n with
  | zero => intro src dst u; exact ⟨rfl, fun _ _ => rfl⟩
  | succ n ih =>
    intro src dst u
    change ((Memory.spec 0).clientState u
      (copyWordsStep ((), ⟨src, dst⟩) >>= iterate copyWordsStep () n)).frontier = u.frontier ∧
      ∀ a < dst, ((Memory.spec 0).clientState u
        (copyWordsStep ((), ⟨src, dst⟩) >>= iterate copyWordsStep () n)).mem a = u.mem a
    rw [StateTransitionSpec.clientState_bind]
    have hstep_st : (Memory.spec 0).clientState u (copyWordsStep ((), ⟨src, dst⟩)) =
        ⟨Function.update u.mem dst (u.mem src), u.frontier⟩ := rfl
    have hstep_res : (Memory.spec 0).clientResult u (copyWordsStep ((), ⟨src, dst⟩)) =
        ⟨src + 1, dst + 1⟩ := rfl
    rw [hstep_st, hstep_res]
    obtain ⟨hfr_i, hmem_i⟩ := ih (src + 1) (dst + 1)
      ⟨Function.update u.mem dst (u.mem src), u.frontier⟩
    refine ⟨hfr_i, fun a ha => ?_⟩
    rw [hmem_i a (by omega)]
    exact Function.update_of_ne (by omega) _ u.mem

end Cslib.Algorithms.WordRAM.VariableElimination
