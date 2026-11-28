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
    intro ys src dst G t hwf_t hys hsrcG hGdst hdstF
    induction ys generalizing src dst G t with
    | nil =>
      exact ⟨validHistory_pure w t _, rfl, PreservesBelow.refl (by omega),
        Block.holdsList_nil dst t.mem⟩
    | cons v rest ih =>
      simp only [List.length_cons] at hsrcG hdstF
      obtain ⟨hhead, htail⟩ := Block.holdsList_cons_iff.mp hys
      have hsrc_lt : src < t.frontier := by omega
      have hdst_lt : dst < t.frontier := by omega
      obtain ⟨hval_rest, hfr_rest, hpres_rest, hholds_rest⟩ :=
        ih (src + 1) (dst + 1) (dst + 1) ⟨Function.update t.mem dst v, t.frontier⟩
          (hwf_t.step (o := .write dst v) ⟨hdst_lt, hhead ▸ hwf_t.mem_fits src⟩)
          (htail.frame fun a _ hhi => Function.update_of_ne (by omega) v t.mem) (by omega) le_rfl
          (by dsimp only; omega)
      have hstep_st : (Memory.spec 0).clientState t (copyWordsStep ((), ⟨src, dst⟩)) =
          ⟨Function.update t.mem dst v, t.frontier⟩ := hhead ▸ rfl
      dsimp only
      rw [List.length_cons, iterate, validHistory_bind', StateTransitionSpec.clientState_bind,
        hstep_st]
      refine ⟨⟨validHistory_read_bind hsrc_lt
          (validHistory_write_bind hdst_lt (hwf_t.mem_fits src) (validHistory_pure w _ _)),
          hval_rest⟩, hfr_rest,
        ⟨by omega, hfr_rest.ge, fun a ha =>
          (hpres_rest.2.2 a (by omega)).trans (Function.update_of_ne (by omega) v t.mem)⟩,
        Block.holdsList_cons_iff.mpr
          ⟨(hpres_rest.2.2 dst (by omega)).trans (Function.update_self dst v t.mem), hholds_rest⟩⟩
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
  refine Nat.add_le_add_left (memoryCost_iterate_le_of filterNeStep 2 args.target (fun a t => ?_)
    args.len ⟨args.base, s.frontier, 0⟩ ⟨s.mem, s.frontier + args.len⟩) 1
  simp only [filterNeStep, client_simps, memoryCost_ite]
  split_ifs <;> simp

private theorem filterNeStep_eval (target : ℕ) (st : FilterState) (t : Memory.State) :
    (Memory.spec 0).clientResult t (filterNeStep (target, st)) =
      (if t.mem st.src = target then ⟨st.src + 1, st.dst, st.count⟩
      else ⟨st.src + 1, st.dst + 1, st.count + 1⟩) ∧
    (Memory.spec 0).clientState t (filterNeStep (target, st)) =
      if t.mem st.src = target then t
      else ⟨Function.update t.mem st.dst (t.mem st.src), t.frontier⟩ := by
  simp only [filterNeStep]
  rw [StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind,
    clientResult_read, clientState_read]
  split_ifs <;> exact ⟨rfl, rfl⟩

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
  simp only [filterNe]
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
    intro ys src dst cnt G t hwf_t hys hsrcG hGdst hdstF
    induction ys generalizing src dst cnt G t with
    | nil =>
      exact ⟨validHistory_pure w t _, rfl, PreservesBelow.refl (by omega), rfl,
        Block.holdsList_nil dst t.mem⟩
    | cons v rest ih =>
      simp only [List.length_cons] at hsrcG hdstF
      obtain ⟨hhead, htail⟩ := Block.holdsList_cons_iff.mp hys
      have hsrc_lt : src < t.frontier := by omega
      obtain ⟨hres, hst⟩ := filterNeStep_eval args.target ⟨src, dst, cnt⟩ t
      dsimp only at hres hst ⊢
      rw [List.length_cons, iterate, validHistory_bind', StateTransitionSpec.clientResult_bind,
        StateTransitionSpec.clientState_bind, hres, hst, hhead]
      by_cases hvx : v = args.target
      · obtain ⟨hval_r, hfr_r, hpres_r, hcnt_r, hholds_r⟩ :=
          ih (src + 1) dst cnt G t hwf_t htail (by omega) hGdst (by omega)
        rw [ite_eq_left hvx, ite_eq_left hvx, List.filter_cons_of_neg (by simp [hvx])]
        exact ⟨⟨validHistory_read_bind hsrc_lt
          (by simpa only [hhead, hvx, ↓reduceIte] using validHistory_pure w t _), hval_r⟩,
          hfr_r, hpres_r, hcnt_r, hholds_r⟩
      · have hdst_lt : dst < t.frontier := by omega
        have hv_fit : Fits w v := hhead ▸ hwf_t.mem_fits src
        obtain ⟨hval_r, hfr_r, hpres_r, hcnt_r, hholds_r⟩ :=
          ih (src + 1) (dst + 1) (cnt + 1) (dst + 1) ⟨Function.update t.mem dst v, t.frontier⟩
            (hwf_t.step (o := .write dst v) ⟨hdst_lt, hv_fit⟩)
            (htail.frame fun a _ hhi => Function.update_of_ne (by omega) v t.mem) (by omega) le_rfl
            (by dsimp only; omega)
        rw [ite_eq_right hvx, ite_eq_right hvx, List.filter_cons_of_pos (by simpa using hvx),
          List.length_cons]
        refine ⟨⟨validHistory_read_bind hsrc_lt ?_, hval_r⟩, hfr_r,
          ⟨by omega, hfr_r.ge, fun a ha =>
            (hpres_r.2.2 a (by omega)).trans (Function.update_of_ne (by omega) v t.mem)⟩, by omega,
          Block.holdsList_cons_iff.mpr
            ⟨(hpres_r.2.2 dst (by omega)).trans (Function.update_self dst v t.mem), hholds_r⟩⟩
        rw [hhead, ite_eq_right hvx]
        exact validHistory_write_bind hdst_lt hv_fit (validHistory_pure w _ _)
  obtain ⟨hv, hfr, hpres, hcnt, hholds⟩ :=
    haux xs args.base s.frontier 0 s.frontier ⟨s.mem, s.frontier + xs.length⟩
      (by rw [hlen]; exact hwf.step (o := .allocDirty args.len) hfit) hxs.2 hxs.1 le_rfl le_rfl
  have hout_le := List.length_filter_le (fun v => decide (v ≠ args.target)) xs
  rw [← hlen] at hfit ⊢
  rw [StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind,
    clientResult_allocDirty, clientState_allocDirty, StateTransitionSpec.clientResult_bind,
    StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_pure,
    StateTransitionSpec.clientState_pure]
  dsimp only at hfr hcnt
  exact ⟨validHistory_allocDirty_bind hfit (validHistory_bind_step hv (validHistory_pure w _ _)),
    hfr, ⟨le_rfl, by omega, hpres.2.2⟩, rfl, by omega, ⟨by omega, hholds⟩⟩

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
  · rw [(filterNeStep_eval _ _ _).1]
    split_ifs <;> (dsimp only; omega)

theorem copyWords_frame (args : CopyArgs) (t : Memory.State) :
    ((Memory.spec 0).clientState t (copyWords args)).frontier = t.frontier ∧
    ∀ a, a < args.dst → ((Memory.spec 0).clientState t (copyWords args)).mem a = t.mem a := by
  obtain ⟨src, dst, n⟩ := args
  unfold copyWords
  rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_pure]
  induction n generalizing src dst t with
  | zero => exact ⟨rfl, fun _ _ => rfl⟩
  | succ n ih =>
    simp only [iterate]
    obtain ⟨hfr_i, hmem_i⟩ := ih ⟨Function.update t.mem dst (t.mem src), t.frontier⟩
      (src + 1) (dst + 1)
    exact ⟨hfr_i, fun a ha =>
      (hmem_i a (Nat.lt_succ_of_lt ha)).trans (Function.update_of_ne ha.ne _ t.mem)⟩

end Cslib.Algorithms.WordRAM.VariableElimination
