/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.TreeDecomposition.Scan
import CslibFrontier.Tactic.Realize

/-!
# Bit-mask bag projection and restriction scans (`keyMaskProg`, `restrictMaskProg`)

This module certifies the Word-RAM bit-mask transfer scans between a child bag `LB` and parent bag
`LP`, with no dependency on `MWISInstance`:

* `selMemBagProg` (private): tests selected membership `selMemMask` in a masked bag slice.
* `keyMaskProg`: computes `keyMask LB LP mask` (the parent-bag mask of a child subset) in
  `bagPLen * (bagBLen + 1)` memory operations.
* `restrictMaskProg`: computes `restrictMask LB LP mask` (the restriction of a parent mask to
  vertices also in `LB`) in `bagPLen * (bagBLen + 1)` memory operations.

## Main definitions

* `Cslib.Algorithms.WordRAM.TreeDecomposition.MaskTransArgs`: register arguments shared by
  `keyMaskProg` and `restrictMaskProg`.
* `Cslib.Algorithms.WordRAM.TreeDecomposition.keyMaskProg`: child-to-parent mask transfer scan.
* `Cslib.Algorithms.WordRAM.TreeDecomposition.restrictMaskProg`: parent-to-child mask restriction
  scan.

## Main results

* `Cslib.Algorithms.WordRAM.TreeDecomposition.keyMask_lt_two_pow`,
  `Cslib.Algorithms.WordRAM.TreeDecomposition.restrictMask_lt_two_pow`: `2 ^ |LP|` range bounds.
* `Cslib.Algorithms.WordRAM.TreeDecomposition.keyMaskProg_spec`,
  `Cslib.Algorithms.WordRAM.TreeDecomposition.keyMaskProg_realizes`: correctness and realization of
  `keyMaskProg`.
* `Cslib.Algorithms.WordRAM.TreeDecomposition.restrictMaskProg_spec`,
  `Cslib.Algorithms.WordRAM.TreeDecomposition.restrictMaskProg_realizes`: correctness and
  realization of `restrictMaskProg`.
-/

public section

namespace Cslib.Algorithms.WordRAM.TreeDecomposition

open Cslib.Algorithms.Lean.TreeDecomposition
open Cslib.DataStructure
open Cslib.WordRAM
open Cslib.WordRAM.Realization

/-! ### `2 ^ |LP|` range bounds for `keyMask` and `restrictMask` -/

/-- `keyMask LB LP t` always lies in `0 .. 2 ^ LP.length - 1`. -/
theorem keyMask_lt_two_pow (LB LP : List ℕ) (t : ℕ) : keyMask LB LP t < 2 ^ LP.length :=
  keyMask_eq_toMask LB LP t ▸ toMask_lt LP (ofMask LB t)

/-- `restrictMask LB LP s` always lies in `0 .. 2 ^ LP.length - 1`
(without requiring `LP.Nodup`). -/
theorem restrictMask_lt_two_pow (LB LP : List ℕ) (s : ℕ) :
    restrictMask LB LP s < 2 ^ LP.length := by
  induction LP generalizing s with
  | nil => simp [restrictMask]
  | cons u rest ih =>
    have hrec := ih (s / 2)
    simp only [restrictMask, List.length_cons, Nat.pow_succ]
    by_cases hbit : s % 2 = 1 <;> by_cases hin : u ∈ LB <;> simp [hbit, hin] <;> omega

/-! ### Selected-membership scan (`selMemBagProg`) -/

private structure SelMemArgs where
  target : ℕ
  ptr : ℕ
  len : ℕ
  mask : ℕ

private def SelMemArgs.equiv : SelMemArgs ≃ ((ℕ × ℕ) × ℕ) × ℕ where
  toFun a := (((a.target, a.ptr), a.len), a.mask)
  invFun := fun (((t, p), l), m) => ⟨t, p, l, m⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding SelMemArgs := .ofEquiv SelMemArgs.equiv

private structure SelMemState where
  cur : ℕ
  curM : ℕ
  found : ℕ

private def SelMemState.equiv : SelMemState ≃ (ℕ × ℕ) × ℕ where
  toFun s := ((s.cur, s.curM), s.found)
  invFun := fun ((c, m), f) => ⟨c, m, f⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding SelMemState := .ofEquiv SelMemState.equiv

private def selMemStep (p : ℕ × SelMemState) : Memory.Prog SelMemState := do
  let target := p.1
  let st := p.2
  let u ← Memory.read st.cur
  let bit := st.curM % 2
  let found' := if bit = 1 then (if target = u then 1 else st.found) else st.found
  pure ⟨st.cur + 1, st.curM / 2, found'⟩

private def selMemBagProg (args : SelMemArgs) : Memory.Prog ℕ := do
  let res ← iterate selMemStep args.target args.len ⟨args.ptr, args.mask, 0⟩
  pure res.found

private theorem selMemBagProg_state (args : SelMemArgs) (s : Memory.State) :
    (Memory.spec 0).clientState s (selMemBagProg args) = s := by
  unfold selMemBagProg
  rw [StateTransitionSpec.clientState_bind]
  exact clientState_iterate_eq_of selMemStep args.target (fun _ _ => rfl)
    args.len ⟨args.ptr, args.mask, 0⟩ s

private theorem selMemBagProg_spec {w : ℕ} (args : SelMemArgs) {xs : List ℕ} {s : Memory.State}
    (hxs : HoldsIn args.ptr xs s) (hlen : xs.length = args.len) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (selMemBagProg args)) ∧
    (Memory.spec 0).clientState s (selMemBagProg args) = s ∧
    (Memory.spec 0).clientResult s (selMemBagProg args) =
      (if selMemMask args.target xs args.mask then 1 else 0) ∧
    memoryCost (selMemBagProg args) s ≤ args.len := by
  have hcost : memoryCost (selMemBagProg args) s ≤ args.len := by
    unfold selMemBagProg
    rw [memoryCost_bind', memoryCost_pure, Nat.add_zero]
    simpa only [Nat.one_mul] using
      memoryCost_iterate_le_of selMemStep 1 args.target (fun _ _ => le_rfl)
        args.len ⟨args.ptr, args.mask, 0⟩ s
  suffices ∀ ys cur curM found, HoldsIn cur ys s → (found = 0 ∨ found = 1) →
      (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s
          (iterate selMemStep args.target ys.length ⟨cur, curM, found⟩)) ∧
      ((Memory.spec 0).clientResult s
        (iterate selMemStep args.target ys.length ⟨cur, curM, found⟩)).found =
        if found = 1 ∨ selMemMask args.target ys curM = true then 1 else 0 by
    have hrun := this xs args.ptr args.mask 0 hxs (.inl rfl)
    rw [hlen] at hrun
    unfold selMemBagProg
    refine ⟨validHistory_bind_step hrun.1 (validHistory_pure w _ _),
      selMemBagProg_state args s, ?_, hcost⟩
    rw [StateTransitionSpec.clientResult_bind]
    change ((Memory.spec 0).clientResult s
      (iterate selMemStep args.target args.len ⟨args.ptr, args.mask, 0⟩)).found = _
    rw [hrun.2]
    cases selMemMask args.target xs args.mask <;> rfl
  intro ys
  induction ys with
  | nil =>
    intro cur curM found _ hfd
    have h0 : iterate selMemStep args.target 0 ⟨cur, curM, found⟩ = pure ⟨cur, curM, found⟩ := rfl
    simp only [List.length_nil, h0, selMemMask]
    exact ⟨validHistory_pure w s _, by rcases hfd with rfl | rfl <;> rfl⟩
  | cons u rest ih =>
    intro cur curM found hcur hfd
    obtain ⟨hb, hmem_u, hrest⟩ := HoldsIn.cons_iff.mp hcur
    let found' := if curM % 2 = 1 then (if args.target = u then 1 else found) else found
    have hfd' : found' = 0 ∨ found' = 1 := by
      dsimp only [found']
      split_ifs <;> [exact .inr rfl; exact hfd; exact hfd]
    obtain ⟨hv_rest, hr_rest⟩ := ih (cur + 1) (curM / 2) found' hrest hfd'
    have hst_step :
        (Memory.spec 0).clientState s (selMemStep (args.target, ⟨cur, curM, found⟩)) = s := rfl
    have hres_step :
        (Memory.spec 0).clientResult s (selMemStep (args.target, ⟨cur, curM, found⟩)) =
        ⟨cur + 1, curM / 2, found'⟩ := by
      dsimp only [selMemStep, found']
      change (⟨cur + 1, curM / 2, _⟩ : SelMemState) = _
      rw [hmem_u]
    simp only [List.length_cons]
    have hiter : iterate selMemStep args.target (rest.length + 1) ⟨cur, curM, found⟩ =
        (selMemStep (args.target, ⟨cur, curM, found⟩) >>=
          iterate selMemStep args.target rest.length) := rfl
    rw [hiter]
    refine ⟨validHistory_bind_step
        (validHistory_read_bind (by dsimp only; omega) (validHistory_pure w s _))
        (by rwa [hst_step, hres_step]), ?_⟩
    rw [StateTransitionSpec.clientResult_bind, hst_step, hres_step, hr_rest]
    dsimp only [found', selMemMask]
    rcases hfd with rfl | rfl
    · by_cases hbit : curM % 2 = 1 <;> by_cases heq : args.target = u <;> simp [hbit, heq]
    · simp only [ite_self, true_or, ↓reduceIte]

private theorem selMemBagProg_realizes :
    Realizes .exact selMemBagProg WordEncoding.encode WordEncoding.encode
      (fun w args _ => Fits w 2 ∧ Fits w (args.ptr + args.len))
      (fun _ _ => 0) := by
  unfold selMemBagProg
  realize
  obtain ⟨h2, hfit⟩ := h
  have h1 : Fits w 1 := h2.of_le (by decide)
  have h2_ne : 2 ≠ 0 := by decide
  refine iterationSafe_of_stepInv _ _ w _
    (fun (j : ℕ) (st : SelMemState) (_ : Memory.State) =>
      st.cur + j = d.ptr + d.len ∧ st.found ≤ 1)
    (fun j st m ⟨hcur, hfd⟩ => ?_)
    ⟨rfl, Nat.zero_le _⟩
  dsimp only [selMemStep]
  have hcur_fit : Fits w (st.cur + 1) := hfit.of_le (by omega)
  refine ⟨?_, ?_, ?_⟩
  · repeat (first | split | assumption | refine And.intro ?_ ?_)
  · change (st.cur + 1) + j = d.ptr + d.len
    omega
  · change (if st.curM % 2 = 1 then
        if d.target = m.mem st.cur then 1 else st.found
      else st.found) ≤ 1
    split_ifs <;> omega

/-! ### Parent-bag mask (`keyMaskProg`) -/

/-- Register arguments `(bagBPtr, bagBLen, bagPPtr, bagPLen, mask)` for `keyMaskProg` and
`restrictMaskProg`. -/
structure MaskTransArgs where
  /-- Base memory address of child bag `LB`. -/
  bagBPtr : ℕ
  /-- Length of child bag `LB`. -/
  bagBLen : ℕ
  /-- Base memory address of parent bag `LP`. -/
  bagPPtr : ℕ
  /-- Length of parent bag `LP`. -/
  bagPLen : ℕ
  /-- Input subset bit mask (`t` over `LB` for `keyMaskProg`; `s` over `LP` for
  `restrictMaskProg`). -/
  mask : ℕ

/-- Tuple equivalence encoding `MaskTransArgs` into Word-RAM registers. -/
@[expose] def MaskTransArgs.equiv : MaskTransArgs ≃ (((ℕ × ℕ) × ℕ) × ℕ) × ℕ where
  toFun a := ((((a.bagBPtr, a.bagBLen), a.bagPPtr), a.bagPLen), a.mask)
  invFun := fun ((((bp, bl), pp), pl), m) => ⟨bp, bl, pp, pl, m⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : WordEncoding MaskTransArgs := .ofEquiv MaskTransArgs.equiv

private structure KeyMaskEnv where
  bagBPtr : ℕ
  bagBLen : ℕ
  mask : ℕ

private def KeyMaskEnv.equiv : KeyMaskEnv ≃ (ℕ × ℕ) × ℕ where
  toFun e := ((e.bagBPtr, e.bagBLen), e.mask)
  invFun := fun ((bp, bl), m) => ⟨bp, bl, m⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding KeyMaskEnv := .ofEquiv KeyMaskEnv.equiv

private structure KeyMaskState where
  curP : ℕ
  pow2 : ℕ
  acc : ℕ

private def KeyMaskState.equiv : KeyMaskState ≃ (ℕ × ℕ) × ℕ where
  toFun s := ((s.curP, s.pow2), s.acc)
  invFun := fun ((c, p), a) => ⟨c, p, a⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding KeyMaskState := .ofEquiv KeyMaskState.equiv

private def keyMaskStep (p : KeyMaskEnv × KeyMaskState) : Memory.Prog KeyMaskState := do
  let env := p.1
  let st := p.2
  let u ← Memory.read st.curP
  let sel ← selMemBagProg ⟨u, env.bagBPtr, env.bagBLen, env.mask⟩
  let addTerm := if sel = 1 then st.pow2 else 0
  pure ⟨st.curP + 1, 2 * st.pow2, st.acc + addTerm⟩

/-- Compute `keyMask LB LP args.mask` across materialized bag slices `LB` and `LP`. -/
def keyMaskProg (args : MaskTransArgs) : Memory.Prog ℕ := do
  let res ← iterate keyMaskStep ⟨args.bagBPtr, args.bagBLen, args.mask⟩ args.bagPLen
    ⟨args.bagPPtr, 1, 0⟩
  pure res.acc

/-- `keyMaskProg` is read-only and leaves memory unchanged. -/
theorem keyMaskProg_state (args : MaskTransArgs) (s : Memory.State) :
    (Memory.spec 0).clientState s (keyMaskProg args) = s := by
  unfold keyMaskProg
  rw [StateTransitionSpec.clientState_bind]
  refine clientState_iterate_eq_of keyMaskStep ⟨args.bagBPtr, args.bagBLen, args.mask⟩
    (fun st m => ?_) args.bagPLen ⟨args.bagPPtr, 1, 0⟩ s
  unfold keyMaskStep
  dsimp only
  rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
    selMemBagProg_state]
  rfl

/-- Correctness and `bagPLen * (bagBLen + 1)` memory-cost bound for `keyMaskProg`. -/
theorem keyMaskProg_spec {w : ℕ} (args : MaskTransArgs) {LB LP : List ℕ}
    {s : Memory.State}
    (hLB : HoldsIn args.bagBPtr LB s) (hlenB : LB.length = args.bagBLen)
    (hLP : HoldsIn args.bagPPtr LP s) (hlenP : LP.length = args.bagPLen) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (keyMaskProg args)) ∧
    (Memory.spec 0).clientState s (keyMaskProg args) = s ∧
    (Memory.spec 0).clientResult s (keyMaskProg args) = keyMask LB LP args.mask ∧
    memoryCost (keyMaskProg args) s ≤ args.bagPLen * (args.bagBLen + 1) := by
  let env : KeyMaskEnv := ⟨args.bagBPtr, args.bagBLen, args.mask⟩
  suffices ∀ ys curP pow2 acc, HoldsIn curP ys s →
      (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s (iterate keyMaskStep env ys.length ⟨curP, pow2, acc⟩)) ∧
      ((Memory.spec 0).clientResult s
        (iterate keyMaskStep env ys.length ⟨curP, pow2, acc⟩)).acc =
        acc + pow2 * keyMask LB ys args.mask ∧
      memoryCost (iterate keyMaskStep env ys.length ⟨curP, pow2, acc⟩) s ≤
        ys.length * (args.bagBLen + 1) by
    have hrun := this LP args.bagPPtr 1 0 hLP
    rw [hlenP] at hrun
    unfold keyMaskProg
    refine ⟨validHistory_bind_step hrun.1 (validHistory_pure w _ _),
      keyMaskProg_state args s, ?_, ?_⟩
    · rw [StateTransitionSpec.clientResult_bind]
      change ((Memory.spec 0).clientResult s
        (iterate keyMaskStep env args.bagPLen ⟨args.bagPPtr, 1, 0⟩)).acc = _
      rw [hrun.2.1, Nat.zero_add, Nat.one_mul]
    · rw [memoryCost_bind', memoryCost_pure, Nat.add_zero]
      exact hrun.2.2
  intro ys
  induction ys with
  | nil =>
    intro curP pow2 acc _
    have h0 : iterate keyMaskStep env 0 ⟨curP, pow2, acc⟩ = pure ⟨curP, pow2, acc⟩ := rfl
    simp only [List.length_nil, h0, keyMask, Nat.mul_zero, Nat.add_zero]
    exact ⟨validHistory_pure w s _, rfl, by simp [memoryCost_pure]⟩
  | cons u rest ih =>
    intro curP pow2 acc hcur
    obtain ⟨hb, hmem_u, hrest⟩ := HoldsIn.cons_iff.mp hcur
    obtain ⟨hv_sel, hst_sel, hr_sel, hc_sel⟩ :=
      selMemBagProg_spec (w := w) ⟨u, args.bagBPtr, args.bagBLen, args.mask⟩ hLB hlenB
    let addTerm := if selMemMask u LB args.mask then pow2 else 0
    obtain ⟨hv_rest, hr_rest, hc_rest⟩ := ih (curP + 1) (2 * pow2) (acc + addTerm) hrest
    dsimp only at hr_sel hc_sel
    have hadd_eq :
        (if (if selMemMask u LB args.mask then 1 else 0) = 1 then pow2 else 0) = addTerm := by
      dsimp only [addTerm]
      cases selMemMask u LB args.mask <;> rfl
    have hv_step : (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s (keyMaskStep (env, ⟨curP, pow2, acc⟩))) := by
      unfold keyMaskStep
      dsimp only [env]
      refine validHistory_read_bind (by omega) ?_
      rw [hmem_u]
      exact validHistory_bind_step hv_sel (validHistory_pure w _ _)
    have hst_step : (Memory.spec 0).clientState s (keyMaskStep (env, ⟨curP, pow2, acc⟩)) = s := by
      unfold keyMaskStep
      dsimp only
      rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
        selMemBagProg_state]
      rfl
    have hres_step : (Memory.spec 0).clientResult s (keyMaskStep (env, ⟨curP, pow2, acc⟩)) =
        ⟨curP + 1, 2 * pow2, acc + addTerm⟩ := by
      unfold keyMaskStep
      dsimp only [env]
      rw [StateTransitionSpec.clientResult_bind]
      change (Memory.spec 0).clientResult s
        (selMemBagProg ⟨s.mem curP, args.bagBPtr, args.bagBLen, args.mask⟩ >>= _) = _
      rw [hmem_u, StateTransitionSpec.clientResult_bind, hst_sel, hr_sel, hadd_eq]
      rfl
    have hc_step : memoryCost (keyMaskStep (env, ⟨curP, pow2, acc⟩)) s ≤ args.bagBLen + 1 := by
      unfold keyMaskStep
      dsimp only [env]
      rw [memoryCost_bind', memoryCost_read]
      change 1 + memoryCost
        (selMemBagProg ⟨s.mem curP, args.bagBPtr, args.bagBLen, args.mask⟩ >>= _) s ≤ _
      rw [hmem_u, memoryCost_bind', hst_sel, memoryCost_pure, Nat.add_zero]
      omega
    simp only [List.length_cons]
    have hiter_eq : iterate keyMaskStep env (rest.length + 1) ⟨curP, pow2, acc⟩ =
        (keyMaskStep (env, ⟨curP, pow2, acc⟩) >>= iterate keyMaskStep env rest.length) := rfl
    rw [hiter_eq]
    refine ⟨validHistory_bind_step hv_step (by rwa [hst_step, hres_step]), ?_, ?_⟩
    · rw [StateTransitionSpec.clientResult_bind, hst_step, hres_step, hr_rest]
      dsimp only [addTerm, keyMask]
      by_cases hsm : selMemMask u LB args.mask = true <;>
        simp only [hsm, Bool.false_eq_true, ↓reduceIte, Nat.left_distrib, Nat.mul_one,
          Nat.zero_add, ← Nat.mul_assoc, Nat.mul_comm pow2 2] <;> omega
    · rw [memoryCost_bind', hst_step, hres_step]
      exact (Nat.add_le_add hc_step hc_rest).trans_eq (by ring)

/-- Exact-basis Word-RAM realization certificate for `keyMaskProg`. -/
theorem keyMaskProg_realizes :
    Realizes .exact keyMaskProg WordEncoding.encode WordEncoding.encode
      (fun w args _ =>
        Fits w 2 ∧ Fits w (args.bagBPtr + args.bagBLen) ∧ Fits w (args.bagPPtr + args.bagPLen) ∧
        Fits w (2 ^ args.bagPLen))
      (fun _ _ => 0) := by
  unfold keyMaskProg
  realize [selMemBagProg_realizes]
  · exact h.1.of_le (by decide)
  · obtain ⟨h2, hfitB, hfitP, hpow⟩ := h
    have h1 : Fits w 1 := h2.of_le (by decide)
    refine iterationSafe_of_stepInv _ _ w _
      (fun (j : ℕ) (st : KeyMaskState) (_ : Memory.State) =>
        j ≤ d.bagPLen ∧ st.curP + j = d.bagPPtr + d.bagPLen ∧
        st.pow2 = 2 ^ (d.bagPLen - j) ∧ st.acc < st.pow2)
      (fun j st m ⟨hj_le, hcur, hp2, hacc_lt⟩ => ?_)
      ⟨le_rfl, rfl, by simp only [Nat.sub_self, Nat.pow_zero], Nat.zero_lt_one⟩
    have hp2_next : 2 * st.pow2 = 2 ^ (d.bagPLen - j) := by
      rw [hp2, show d.bagPLen - j = (d.bagPLen - (j + 1)) + 1 by omega, Nat.pow_succ, Nat.mul_comm]
    have hp2_fit : Fits w (2 * st.pow2) :=
      hpow.of_le (hp2_next ▸ Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _))
    have hcur_fit : Fits w (st.curP + 1) := hfitP.of_le (by omega)
    have hacc1_fit : Fits w (st.acc + st.pow2) := hp2_fit.of_le (by omega)
    have hacc0_fit : Fits w (st.acc + 0) := hp2_fit.of_le (by omega)
    have hres : ∃ add ≤ st.pow2, (Memory.spec 0).clientResult m
        (keyMaskStep (⟨d.bagBPtr, d.bagBLen, d.mask⟩, st)) =
        ⟨st.curP + 1, 2 * st.pow2, st.acc + add⟩ := by
      unfold keyMaskStep
      dsimp only
      rw [StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientResult_bind,
        selMemBagProg_state]
      exact ⟨_, by split_ifs <;> omega, rfl⟩
    obtain ⟨add, hadd_le, hres⟩ := hres
    refine ⟨by repeat (first | split | assumption | refine And.intro ?_ ?_),
      Nat.le_of_succ_le hj_le, ?_, ?_, ?_⟩ <;> rw [hres]
    · change (st.curP + 1) + j = d.bagPPtr + d.bagPLen
      omega
    · exact hp2_next
    · change st.acc + add < 2 * st.pow2
      omega

/-! ### Parent-mask restriction (`restrictMaskProg`) -/

private structure RestrictEnv where
  bagBPtr : ℕ
  bagBLen : ℕ

private def RestrictEnv.equiv : RestrictEnv ≃ ℕ × ℕ where
  toFun e := (e.bagBPtr, e.bagBLen)
  invFun := fun (bp, bl) => ⟨bp, bl⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding RestrictEnv := .ofEquiv RestrictEnv.equiv

private structure RestrictState where
  curP : ℕ
  curS : ℕ
  pow2 : ℕ
  acc : ℕ

private def RestrictState.equiv : RestrictState ≃ ((ℕ × ℕ) × ℕ) × ℕ where
  toFun s := (((s.curP, s.curS), s.pow2), s.acc)
  invFun := fun (((cp, cs), p2), a) => ⟨cp, cs, p2, a⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding RestrictState := .ofEquiv RestrictState.equiv

private def restrictStep (p : RestrictEnv × RestrictState) : Memory.Prog RestrictState := do
  let env := p.1
  let st := p.2
  let u ← Memory.read st.curP
  let inB ← bagMemProg ⟨u, env.bagBPtr, env.bagBLen⟩
  let bit := st.curS % 2
  let addTerm := if bit = 1 then (if inB = 1 then st.pow2 else 0) else 0
  pure ⟨st.curP + 1, st.curS / 2, 2 * st.pow2, st.acc + addTerm⟩

/-- Compute `restrictMask LB LP args.mask` across materialized bag slices `LB` and `LP`. -/
def restrictMaskProg (args : MaskTransArgs) : Memory.Prog ℕ := do
  let res ← iterate restrictStep ⟨args.bagBPtr, args.bagBLen⟩ args.bagPLen
    ⟨args.bagPPtr, args.mask, 1, 0⟩
  pure res.acc

private theorem restrictStep_state (env : RestrictEnv) (st : RestrictState) (m : Memory.State) :
    (Memory.spec 0).clientState m (restrictStep (env, st)) = m := by
  unfold restrictStep
  dsimp only
  rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind, bagMemProg_state]
  rfl

/-- `restrictMaskProg` is read-only and leaves memory unchanged. -/
theorem restrictMaskProg_state (args : MaskTransArgs) (s : Memory.State) :
    (Memory.spec 0).clientState s (restrictMaskProg args) = s := by
  unfold restrictMaskProg
  rw [StateTransitionSpec.clientState_bind]
  exact clientState_iterate_eq_of restrictStep ⟨args.bagBPtr, args.bagBLen⟩
    (restrictStep_state _) args.bagPLen ⟨args.bagPPtr, args.mask, 1, 0⟩ s

/-- Correctness and `bagPLen * (bagBLen + 1)` memory-cost bound for `restrictMaskProg`. -/
theorem restrictMaskProg_spec {w : ℕ} (args : MaskTransArgs) {LB LP : List ℕ}
    {s : Memory.State}
    (hLB : HoldsIn args.bagBPtr LB s) (hlenB : LB.length = args.bagBLen)
    (hLP : HoldsIn args.bagPPtr LP s) (hlenP : LP.length = args.bagPLen) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (restrictMaskProg args)) ∧
    (Memory.spec 0).clientState s (restrictMaskProg args) = s ∧
    (Memory.spec 0).clientResult s (restrictMaskProg args) = restrictMask LB LP args.mask ∧
    memoryCost (restrictMaskProg args) s ≤ args.bagPLen * (args.bagBLen + 1) := by
  let env : RestrictEnv := ⟨args.bagBPtr, args.bagBLen⟩
  suffices ∀ ys curP curS pow2 acc, HoldsIn curP ys s →
      (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s
          (iterate restrictStep env ys.length ⟨curP, curS, pow2, acc⟩)) ∧
      ((Memory.spec 0).clientResult s
        (iterate restrictStep env ys.length ⟨curP, curS, pow2, acc⟩)).acc =
        acc + pow2 * restrictMask LB ys curS ∧
      memoryCost (iterate restrictStep env ys.length ⟨curP, curS, pow2, acc⟩) s ≤
        ys.length * (args.bagBLen + 1) by
    have hrun := this LP args.bagPPtr args.mask 1 0 hLP
    rw [hlenP] at hrun
    unfold restrictMaskProg
    refine ⟨validHistory_bind_step hrun.1 (validHistory_pure w _ _),
      restrictMaskProg_state args s, ?_, ?_⟩
    · rw [StateTransitionSpec.clientResult_bind]
      change ((Memory.spec 0).clientResult s
        (iterate restrictStep env args.bagPLen ⟨args.bagPPtr, args.mask, 1, 0⟩)).acc = _
      rw [hrun.2.1, Nat.zero_add, Nat.one_mul]
    · rw [memoryCost_bind', memoryCost_pure, Nat.add_zero]
      exact hrun.2.2
  intro ys
  induction ys with
  | nil =>
    intro curP curS pow2 acc _
    have h0 : iterate restrictStep env 0 ⟨curP, curS, pow2, acc⟩ =
        pure ⟨curP, curS, pow2, acc⟩ := rfl
    simp only [List.length_nil, h0, restrictMask, Nat.mul_zero, Nat.add_zero]
    exact ⟨validHistory_pure w s _, rfl, by simp [memoryCost_pure]⟩
  | cons u rest ih =>
    intro curP curS pow2 acc hcur
    obtain ⟨hb, hmem_u, hrest⟩ := HoldsIn.cons_iff.mp hcur
    obtain ⟨hv_bm, hst_bm, hr_bm, hc_bm⟩ :=
      bagMemProg_spec (w := w) ⟨u, args.bagBPtr, args.bagBLen⟩ hLB hlenB
    let addTerm := if curS % 2 = 1 ∧ memBag u LB = true then pow2 else 0
    obtain ⟨hv_rest, hr_rest, hc_rest⟩ :=
      ih (curP + 1) (curS / 2) (2 * pow2) (acc + addTerm) hrest
    have hadd_eq :
        (if curS % 2 = 1 then
          if (if memBag u LB then 1 else 0) = 1 then pow2 else 0
        else 0) = addTerm := by
      dsimp only [addTerm]
      by_cases hbit : curS % 2 = 1 <;> cases memBag u LB <;> simp [hbit]
    have hv_step : (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s (restrictStep (env, ⟨curP, curS, pow2, acc⟩))) := by
      unfold restrictStep
      dsimp only [env]
      refine validHistory_read_bind (by omega) ?_
      rw [hmem_u]
      exact validHistory_bind_step hv_bm (validHistory_pure w _ _)
    have hst_step := restrictStep_state env ⟨curP, curS, pow2, acc⟩ s
    have hres_step : (Memory.spec 0).clientResult s
        (restrictStep (env, ⟨curP, curS, pow2, acc⟩)) =
        ⟨curP + 1, curS / 2, 2 * pow2, acc + addTerm⟩ := by
      unfold restrictStep
      dsimp only [env]
      rw [StateTransitionSpec.clientResult_bind]
      change (Memory.spec 0).clientResult s
        (bagMemProg ⟨s.mem curP, args.bagBPtr, args.bagBLen⟩ >>= _) = _
      rw [hmem_u, StateTransitionSpec.clientResult_bind, hst_bm, hr_bm, hadd_eq]
      rfl
    have hc_step : memoryCost (restrictStep (env, ⟨curP, curS, pow2, acc⟩)) s ≤
        args.bagBLen + 1 := by
      dsimp only at hc_bm
      unfold restrictStep
      dsimp only [env]
      rw [memoryCost_bind', memoryCost_read]
      change 1 + memoryCost (bagMemProg ⟨s.mem curP, args.bagBPtr, args.bagBLen⟩ >>= _) s ≤ _
      rw [hmem_u, memoryCost_bind', hst_bm, memoryCost_pure, Nat.add_zero]
      omega
    simp only [List.length_cons]
    have hiter_eq : iterate restrictStep env (rest.length + 1) ⟨curP, curS, pow2, acc⟩ =
        (restrictStep (env, ⟨curP, curS, pow2, acc⟩) >>= iterate restrictStep env rest.length) :=
      rfl
    rw [hiter_eq]
    refine ⟨validHistory_bind_step hv_step (by rwa [hst_step, hres_step]), ?_, ?_⟩
    · rw [StateTransitionSpec.clientResult_bind, hst_step, hres_step, hr_rest]
      dsimp only [addTerm, restrictMask]
      (by_cases hbit : curS % 2 = 1 <;> by_cases hin : u ∈ LB <;>
        simp only [hbit, memBag_eq_decide, hin, decide_true, decide_false, and_self, and_false,
          false_and, Bool.false_eq_true, ↓reduceIte, Nat.left_distrib, Nat.mul_one, Nat.add_zero,
          Nat.zero_add, ← Nat.mul_assoc, Nat.mul_comm pow2 2])
      omega
    · rw [memoryCost_bind', hst_step, hres_step]
      exact (Nat.add_le_add hc_step hc_rest).trans_eq (by ring)

/-- Exact-basis Word-RAM realization certificate for `restrictMaskProg`. -/
theorem restrictMaskProg_realizes :
    Realizes .exact restrictMaskProg WordEncoding.encode WordEncoding.encode
      (fun w args _ =>
        Fits w 2 ∧ Fits w (args.bagBPtr + args.bagBLen) ∧ Fits w (args.bagPPtr + args.bagPLen) ∧
        Fits w (2 ^ args.bagPLen))
      (fun _ _ => 0) := by
  unfold restrictMaskProg
  realize [bagMemProg_realizes]
  · exact h.1.of_le (by decide)
  · obtain ⟨h2, hfitB, hfitP, hpow⟩ := h
    have h1 : Fits w 1 := h2.of_le (by decide)
    have h2_ne : 2 ≠ 0 := by decide
    refine iterationSafe_of_stepInv _ _ w _
      (fun (j : ℕ) (st : RestrictState) (_ : Memory.State) =>
        j ≤ d.bagPLen ∧ st.curP + j = d.bagPPtr + d.bagPLen ∧
        st.pow2 = 2 ^ (d.bagPLen - j) ∧ st.acc < st.pow2)
      (fun j st m ⟨hj_le, hcur, hp2, hacc_lt⟩ => ?_)
      ⟨le_rfl, rfl, by simp only [Nat.sub_self, Nat.pow_zero], Nat.zero_lt_one⟩
    have hp2_next : 2 * st.pow2 = 2 ^ (d.bagPLen - j) := by
      rw [hp2, show d.bagPLen - j = (d.bagPLen - (j + 1)) + 1 by omega, Nat.pow_succ, Nat.mul_comm]
    have hp2_fit : Fits w (2 * st.pow2) :=
      hpow.of_le (hp2_next ▸ Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _))
    have hcur_fit : Fits w (st.curP + 1) := hfitP.of_le (by omega)
    have hacc1_fit : Fits w (st.acc + st.pow2) := hp2_fit.of_le (by omega)
    have hacc0_fit : Fits w (st.acc + 0) := hp2_fit.of_le (by omega)
    have hres : ∃ add ≤ st.pow2, (Memory.spec 0).clientResult m
        (restrictStep (⟨d.bagBPtr, d.bagBLen⟩, st)) =
        ⟨st.curP + 1, st.curS / 2, 2 * st.pow2, st.acc + add⟩ := by
      unfold restrictStep
      dsimp only
      rw [StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientResult_bind,
        bagMemProg_state]
      exact ⟨_, by split_ifs <;> omega, rfl⟩
    obtain ⟨add, hadd_le, hres⟩ := hres
    refine ⟨by repeat (first | split | assumption | refine And.intro ?_ ?_),
      Nat.le_of_succ_le hj_le, ?_, ?_, ?_⟩ <;> rw [hres]
    · change (st.curP + 1) + j = d.bagPPtr + d.bagPLen
      omega
    · exact hp2_next
    · change st.acc + add < 2 * st.pow2
      omega

end Cslib.Algorithms.WordRAM.TreeDecomposition
