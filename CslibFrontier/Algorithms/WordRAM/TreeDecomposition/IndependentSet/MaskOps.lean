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
    rw [StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientResult_pure]
    simpa only [zero_ne_one, false_or] using hrun.2
  intro ys
  induction ys with
  | nil =>
    intro cur curM found _ hfd
    dsimp only [List.length_nil, iterate, selMemMask]
    exact ⟨validHistory_pure w s _, by rcases hfd with rfl | rfl <;> rfl⟩
  | cons u rest ih =>
    intro cur curM found hcur hfd
    obtain ⟨hb, hmem_u, hrest⟩ := HoldsIn.cons_iff.mp hcur
    let found' := if curM % 2 = 1 then (if args.target = u then 1 else found) else found
    have hfd' : found' = 0 ∨ found' = 1 := by
      dsimp only [found']
      split_ifs <;> [exact .inr rfl; exact hfd; exact hfd]
    obtain ⟨hv_rest, hr_rest⟩ := ih (cur + 1) (curM / 2) found' hrest hfd'
    have hres_step :
        (Memory.spec 0).clientResult s (selMemStep (args.target, ⟨cur, curM, found⟩)) =
        ⟨cur + 1, curM / 2, found'⟩ := by
      change (⟨cur + 1, curM / 2, _⟩ : SelMemState) = _
      rw [hmem_u]
    dsimp only [List.length_cons, iterate]
    refine ⟨validHistory_bind_step
        (validHistory_read_bind (by dsimp only; omega) (validHistory_pure w s _))
        (by rwa [hres_step]), ?_⟩
    rw [StateTransitionSpec.clientResult_bind, hres_step]
    exact hr_rest.trans (by
      dsimp only [found', selMemMask]
      rcases hfd with rfl | rfl
      · by_cases hbit : curM % 2 = 1 <;> by_cases heq : args.target = u <;> simp [hbit, heq]
      · simp only [ite_self, true_or, ↓reduceIte])

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
  refine ⟨by repeat (first | split | assumption | refine And.intro ?_ ?_),
    Nat.add_right_comm st.cur 1 j ▸ hcur, ?_⟩
  change (if st.curM % 2 = 1 then
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

private theorem keyMaskStep_state (env : KeyMaskEnv) (st : KeyMaskState) (m : Memory.State) :
    (Memory.spec 0).clientState m (keyMaskStep (env, st)) = m := by
  unfold keyMaskStep
  dsimp only
  rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
    selMemBagProg_state]
  rfl

/-- `keyMaskProg` is read-only and leaves memory unchanged. -/
theorem keyMaskProg_state (args : MaskTransArgs) (s : Memory.State) :
    (Memory.spec 0).clientState s (keyMaskProg args) = s := by
  unfold keyMaskProg
  rw [StateTransitionSpec.clientState_bind]
  exact clientState_iterate_eq_of keyMaskStep ⟨args.bagBPtr, args.bagBLen, args.mask⟩
    (keyMaskStep_state _) args.bagPLen ⟨args.bagPPtr, 1, 0⟩ s

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
    refine ⟨validHistory_bind_step hrun.1 (validHistory_pure w _ _), keyMaskProg_state args s,
      ?_, by simpa only [memoryCost_bind', memoryCost_pure, Nat.add_zero] using hrun.2.2⟩
    rw [StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientResult_pure]
    simpa only [Nat.zero_add, Nat.one_mul] using hrun.2.1
  intro ys curP pow2 acc hcur
  induction ys generalizing curP pow2 acc with
  | nil =>
    dsimp only [List.length_nil, iterate, keyMask, Nat.mul_zero, Nat.add_zero]
    exact ⟨validHistory_pure w s _, rfl, by simp [memoryCost_pure]⟩
  | cons u rest ih =>
    obtain ⟨hb, hmem_u, hrest⟩ := HoldsIn.cons_iff.mp hcur
    obtain ⟨hv_sel, hst_sel, hr_sel, hc_sel⟩ :=
      selMemBagProg_spec (w := w) ⟨u, args.bagBPtr, args.bagBLen, args.mask⟩ hLB hlenB
    let addTerm := if selMemMask u LB args.mask then pow2 else 0
    obtain ⟨hv_rest, hr_rest, hc_rest⟩ := ih (curP + 1) (2 * pow2) (acc + addTerm) hrest
    dsimp only at hr_sel hc_sel
    have hv_step : (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s (keyMaskStep (env, ⟨curP, pow2, acc⟩))) :=
      validHistory_read_bind (by dsimp only; omega)
        (hmem_u.symm ▸ validHistory_bind_step hv_sel (validHistory_pure w _ _))
    have hst_step := keyMaskStep_state env ⟨curP, pow2, acc⟩ s
    have hres_step : (Memory.spec 0).clientResult s (keyMaskStep (env, ⟨curP, pow2, acc⟩)) =
        ⟨curP + 1, 2 * pow2, acc + addTerm⟩ := by
      dsimp only [keyMaskStep, env, addTerm]
      rw [StateTransitionSpec.clientResult_bind, clientState_read, clientResult_read, hmem_u,
        StateTransitionSpec.clientResult_bind, hst_sel, hr_sel]
      cases selMemMask u LB args.mask <;> rfl
    have hc_step : memoryCost (keyMaskStep (env, ⟨curP, pow2, acc⟩)) s ≤ args.bagBLen + 1 := by
      dsimp only [keyMaskStep, env]
      rw [memoryCost_bind', memoryCost_read, clientState_read, clientResult_read, hmem_u,
        memoryCost_bind', hst_sel, memoryCost_pure]
      omega
    dsimp only [List.length_cons, iterate]
    refine ⟨validHistory_bind_step hv_step (by rwa [hst_step, hres_step]), ?_, ?_⟩
    · rw [StateTransitionSpec.clientResult_bind, hst_step, hres_step, hr_rest]
      cases hsm : selMemMask u LB args.mask <;>
        simp only [addTerm, keyMask, hsm, Bool.false_eq_true, ↓reduceIte] <;> ring
    · rw [memoryCost_bind', hst_step, hres_step]
      calc memoryCost (keyMaskStep (env, ⟨curP, pow2, acc⟩)) s +
            memoryCost (iterate keyMaskStep env rest.length
              ⟨curP + 1, 2 * pow2, acc + addTerm⟩) s
          ≤ (args.bagBLen + 1) + rest.length * (args.bagBLen + 1) :=
            Nat.add_le_add hc_step hc_rest
        _ = (rest.length + 1) * (args.bagBLen + 1) := by ring

private theorem maskAccumulatorStep {w len j pow2 acc : ℕ} (hj : j + 1 ≤ len)
    (hp : pow2 = 2 ^ (len - (j + 1))) (ha : acc < pow2) (hw : Fits w (2 ^ len)) :
    2 * pow2 = 2 ^ (len - j) ∧ Fits w (2 * pow2) ∧
      ∀ add ≤ pow2, acc + add < 2 * pow2 ∧ Fits w (acc + add) := by
  have hnext : 2 * pow2 = 2 ^ (len - j) :=
    hp ▸ (Nat.pow_succ' ..).symm.trans (congrArg (2 ^ ·) (by lia))
  have hfit := hw.of_le (hnext ▸ Nat.pow_le_pow_right (by decide) (Nat.sub_le len j))
  exact ⟨hnext, hfit, fun add hadd =>
    have hlt : acc + add < 2 * pow2 := by lia
    ⟨hlt, hfit.of_le hlt.le⟩⟩

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
    obtain ⟨hp2_next, hp2_fit, hacc_step⟩ := maskAccumulatorStep hj_le hp2 hacc_lt hpow
    have hcur_fit : Fits w (st.curP + 1) := hfitP.of_le (by lia)
    have hacc1_fit := (hacc_step st.pow2 le_rfl).2
    have hacc0_fit := (hacc_step 0 (Nat.zero_le _)).2
    obtain ⟨add, hadd_le, hres⟩ : ∃ add ≤ st.pow2, (Memory.spec 0).clientResult m
        (keyMaskStep (⟨d.bagBPtr, d.bagBLen, d.mask⟩, st)) =
        ⟨st.curP + 1, 2 * st.pow2, st.acc + add⟩ := by
      unfold keyMaskStep
      dsimp only
      rw [StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientResult_bind,
        selMemBagProg_state]
      exact ⟨_, by split_ifs <;> first | exact le_rfl | exact Nat.zero_le _, rfl⟩
    refine ⟨by repeat (first | split | assumption | refine And.intro ?_ ?_),
      Nat.le_of_succ_le hj_le, ?_⟩
    rw [hres]
    exact ⟨Nat.add_right_comm st.curP 1 j ▸ hcur, hp2_next, (hacc_step add hadd_le).1⟩

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
      restrictMaskProg_state args s, ?_,
      by simpa only [memoryCost_bind', memoryCost_pure, Nat.add_zero] using hrun.2.2⟩
    rw [StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientResult_pure]
    simpa only [Nat.zero_add, Nat.one_mul] using hrun.2.1
  intro ys curP curS pow2 acc hcur
  induction ys generalizing curP curS pow2 acc with
  | nil =>
    dsimp only [List.length_nil, iterate, restrictMask, Nat.mul_zero, Nat.add_zero]
    exact ⟨validHistory_pure w s _, rfl, by simp [memoryCost_pure]⟩
  | cons u rest ih =>
    obtain ⟨hb, hmem_u, hrest⟩ := HoldsIn.cons_iff.mp hcur
    obtain ⟨hv_bm, hst_bm, hr_bm, hc_bm⟩ :=
      bagMemProg_spec (w := w) ⟨u, args.bagBPtr, args.bagBLen⟩ hLB hlenB
    let addTerm := if curS % 2 = 1 ∧ memBag u LB = true then pow2 else 0
    obtain ⟨hv_rest, hr_rest, hc_rest⟩ :=
      ih (curP + 1) (curS / 2) (2 * pow2) (acc + addTerm) hrest
    dsimp only at hr_bm hc_bm
    have hv_step : (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s (restrictStep (env, ⟨curP, curS, pow2, acc⟩))) :=
      validHistory_read_bind (by dsimp only; omega)
        (hmem_u.symm ▸ validHistory_bind_step hv_bm (validHistory_pure w _ _))
    have hst_step := restrictStep_state env ⟨curP, curS, pow2, acc⟩ s
    have hres_step : (Memory.spec 0).clientResult s
        (restrictStep (env, ⟨curP, curS, pow2, acc⟩)) =
        ⟨curP + 1, curS / 2, 2 * pow2, acc + addTerm⟩ := by
      dsimp only [restrictStep, env, addTerm]
      rw [StateTransitionSpec.clientResult_bind, clientState_read, clientResult_read, hmem_u,
        StateTransitionSpec.clientResult_bind, hst_bm, hr_bm, StateTransitionSpec.clientResult_pure]
      by_cases hbit : curS % 2 = 1 <;> cases memBag u LB <;> simp [hbit]
    have hc_step : memoryCost (restrictStep (env, ⟨curP, curS, pow2, acc⟩)) s ≤
        args.bagBLen + 1 := by
      dsimp only [restrictStep, env]
      rw [memoryCost_bind', memoryCost_read, clientState_read, clientResult_read, hmem_u,
        memoryCost_bind', hst_bm, memoryCost_pure]
      omega
    dsimp only [List.length_cons, iterate]
    refine ⟨validHistory_bind_step hv_step (by rwa [hst_step, hres_step]), ?_, ?_⟩
    · rw [StateTransitionSpec.clientResult_bind, hst_step, hres_step, hr_rest]
      by_cases hbit : curS % 2 = 1 <;> by_cases hin : u ∈ LB <;>
        simp only [addTerm, restrictMask, hbit, memBag_eq_decide, hin, decide_true, decide_false,
          and_self, and_false, false_and, Bool.false_eq_true, ↓reduceIte] <;> ring
    · rw [memoryCost_bind', hst_step, hres_step]
      calc memoryCost (restrictStep (env, ⟨curP, curS, pow2, acc⟩)) s +
            memoryCost (iterate restrictStep env rest.length
              ⟨curP + 1, curS / 2, 2 * pow2, acc + addTerm⟩) s
          ≤ (args.bagBLen + 1) + rest.length * (args.bagBLen + 1) :=
            Nat.add_le_add hc_step hc_rest
        _ = (rest.length + 1) * (args.bagBLen + 1) := by ring

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
    obtain ⟨hp2_next, hp2_fit, hacc_step⟩ := maskAccumulatorStep hj_le hp2 hacc_lt hpow
    have hcur_fit : Fits w (st.curP + 1) := hfitP.of_le (by lia)
    have hacc1_fit := (hacc_step st.pow2 le_rfl).2
    have hacc0_fit := (hacc_step 0 (Nat.zero_le _)).2
    obtain ⟨add, hadd_le, hres⟩ : ∃ add ≤ st.pow2, (Memory.spec 0).clientResult m
        (restrictStep (⟨d.bagBPtr, d.bagBLen⟩, st)) =
        ⟨st.curP + 1, st.curS / 2, 2 * st.pow2, st.acc + add⟩ := by
      unfold restrictStep
      dsimp only
      rw [StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientResult_bind,
        bagMemProg_state]
      exact ⟨_, by split_ifs <;> first | exact le_rfl | exact Nat.zero_le _, rfl⟩
    refine ⟨by repeat (first | split | assumption | refine And.intro ?_ ?_),
      Nat.le_of_succ_le hj_le, ?_⟩
    rw [hres]
    exact ⟨Nat.add_right_comm st.curP 1 j ▸ hcur, hp2_next, (hacc_step add hadd_le).1⟩

end Cslib.Algorithms.WordRAM.TreeDecomposition
