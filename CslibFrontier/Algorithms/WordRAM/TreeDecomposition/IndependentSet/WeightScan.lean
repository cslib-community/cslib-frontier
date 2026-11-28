/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.TreeDecomposition.Scan
import CslibFrontier.Foundations.Data.List.FoldMax
import CslibFrontier.Computability.WordRAM.Realization.FramedLoop
import CslibFrontier.Tactic.Realize

/-!
# Forgotten-vertex weight scan (`forgetWeightProg`)

This module certifies the Word-RAM scan accumulating the total weight `forgetWeight` of child-bag
vertices selected by `mask` that do not appear in the parent bag `LP`, with no dependency on
`MWISInstance`.

## Main definitions

* `Cslib.Algorithms.WordRAM.TreeDecomposition.ForgetWeightArgs`: register arguments for
  `forgetWeightProg`.
* `Cslib.Algorithms.WordRAM.TreeDecomposition.forgetWeightProg`: forgotten-vertex weight scan.

## Main results

* `Cslib.Algorithms.WordRAM.TreeDecomposition.forgetWeight_le_foldl_max`: `forgetWeight` is bounded
  by `|LB| * wtL.foldl max 0`.
* `Cslib.Algorithms.WordRAM.TreeDecomposition.forgetWeightProg_spec`: validity, functional
  correctness against `forgetWeight`, and `bagBLen * (bagPLen + 2)` cost bound.
* `Cslib.Algorithms.WordRAM.TreeDecomposition.forgetWeightProg_realizes`: exact-basis Word-RAM
  realization certificate.
* `Cslib.Algorithms.WordRAM.TreeDecomposition.forgetWeightProg_result_le`: direct result bound
  `≤ bagBLen * wtL.foldl max 0` derived from `forgetWeightProg_spec`.
-/

public section

namespace Cslib.Algorithms.WordRAM.TreeDecomposition

open Cslib.Algorithms.Lean.TreeDecomposition
open Cslib.DataStructure
open Cslib.WordRAM
open Cslib.WordRAM.Realization

/-- Register arguments `(wtPtr, bagPPtr, bagPLen, bagBPtr, bagBLen, mask)` for
`forgetWeightProg`. -/
structure ForgetWeightArgs where
  /-- Base memory address of the vertex weight array. -/
  wtPtr : ℕ
  /-- Base memory address of parent bag `LP`. -/
  bagPPtr : ℕ
  /-- Length of parent bag `LP`. -/
  bagPLen : ℕ
  /-- Base memory address of child bag `LB`. -/
  bagBPtr : ℕ
  /-- Length of child bag `LB`. -/
  bagBLen : ℕ
  /-- Subset bit mask over `LB`. -/
  mask : ℕ

/-- Tuple equivalence encoding `ForgetWeightArgs` into Word-RAM registers. -/
@[expose] def ForgetWeightArgs.equiv : ForgetWeightArgs ≃ ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ where
  toFun a := (((((a.wtPtr, a.bagPPtr), a.bagPLen), a.bagBPtr), a.bagBLen), a.mask)
  invFun := fun (((((wp, pp), pl), bp), bl), m) => ⟨wp, pp, pl, bp, bl, m⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : WordEncoding ForgetWeightArgs := .ofEquiv ForgetWeightArgs.equiv

private structure ForgetWeightEnv where
  wtPtr : ℕ
  bagPPtr : ℕ
  bagPLen : ℕ

private def ForgetWeightEnv.equiv : ForgetWeightEnv ≃ (ℕ × ℕ) × ℕ where
  toFun e := ((e.wtPtr, e.bagPPtr), e.bagPLen)
  invFun := fun ((wp, pp), pl) => ⟨wp, pp, pl⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding ForgetWeightEnv := .ofEquiv ForgetWeightEnv.equiv

private structure ForgetWeightState where
  curB : ℕ
  curT : ℕ
  acc : ℕ

private def ForgetWeightState.equiv : ForgetWeightState ≃ (ℕ × ℕ) × ℕ where
  toFun s := ((s.curB, s.curT), s.acc)
  invFun := fun ((cb, ct), a) => ⟨cb, ct, a⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding ForgetWeightState := .ofEquiv ForgetWeightState.equiv

private def forgetWeightStep (p : ForgetWeightEnv × ForgetWeightState) :
    Memory.Prog ForgetWeightState := do
  let env := p.1
  let st := p.2
  let u ← Memory.read st.curB
  let wu ← Memory.read (env.wtPtr + u)
  let inP ← bagMemProg ⟨u, env.bagPPtr, env.bagPLen⟩
  let bit := st.curT % 2
  let addW := if bit = 1 then (if inP = 0 then wu else 0) else 0
  pure ⟨st.curB + 1, st.curT / 2, st.acc + addW⟩

/-- Accumulate `forgetWeight` over materialized child bag `LB` relative to parent bag `LP`. -/
def forgetWeightProg (args : ForgetWeightArgs) : Memory.Prog ℕ := do
  let res ← iterate forgetWeightStep ⟨args.wtPtr, args.bagPPtr, args.bagPLen⟩ args.bagBLen
    ⟨args.bagBPtr, args.mask, 0⟩
  pure res.acc

private theorem forgetWeightStep_eval (env : ForgetWeightEnv) (st : ForgetWeightState)
    (s : Memory.State) :
    (Memory.spec 0).clientState s (forgetWeightStep (env, st)) = s ∧
    (Memory.spec 0).clientResult s (forgetWeightStep (env, st)) =
      ⟨st.curB + 1, st.curT / 2, st.acc +
        if st.curT % 2 = 1 then
          if (Memory.spec 0).clientResult s
              (bagMemProg ⟨s.mem st.curB, env.bagPPtr, env.bagPLen⟩) = 0 then
            s.mem (env.wtPtr + s.mem st.curB) else 0
        else 0⟩ := by
  dsimp only [forgetWeightStep]
  rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind,
    StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind,
    StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind,
    bagMemProg_state]
  exact ⟨rfl, rfl⟩

/-- `forgetWeightProg` is read-only and leaves memory unchanged. -/
theorem forgetWeightProg_state (args : ForgetWeightArgs) (s : Memory.State) :
    (Memory.spec 0).clientState s (forgetWeightProg args) = s := by
  unfold forgetWeightProg
  rw [StateTransitionSpec.clientState_bind]
  exact clientState_iterate_eq_of forgetWeightStep ⟨args.wtPtr, args.bagPPtr, args.bagPLen⟩
    (fun st m => (forgetWeightStep_eval _ st m).1) args.bagBLen ⟨args.bagBPtr, args.mask, 0⟩ s

/-- `forgetWeight` against a weight list `wtL` is bounded by `|LB| * wtL.foldl max 0`. -/
theorem forgetWeight_le_foldl_max (wtL LP : List ℕ) :
    ∀ (LB : List ℕ) (t : ℕ),
      (∀ u ∈ LB, u < wtL.length) →
      forgetWeight (fun u => wtL.getD u 0) LP LB t ≤ LB.length * wtL.foldl max 0
  | [], _, _ => by simp [forgetWeight]
  | u :: rest, t, hus => by
    have hhead :
        (if t % 2 = 1 ∧ memBag u LP = false then wtL.getD u 0 else 0) ≤ wtL.foldl max 0 := by
      split_ifs
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (hus u List.mem_cons_self),
          Option.getD_some]
        exact List.mem_le_foldl_max (List.getElem_mem _)
      · exact Nat.zero_le _
    simp only [forgetWeight, List.length_cons]
    calc (if t % 2 = 1 ∧ memBag u LP = false then wtL.getD u 0 else 0) +
            forgetWeight (fun x => wtL.getD x 0) LP rest (t / 2)
        ≤ wtL.foldl max 0 + rest.length * wtL.foldl max 0 :=
          Nat.add_le_add hhead (forgetWeight_le_foldl_max wtL LP rest (t / 2)
            fun v hv => hus v (List.mem_cons_of_mem u hv))
      _ = (rest.length + 1) * wtL.foldl max 0 := by rw [Nat.succ_mul, Nat.add_comm]

/-- Correctness and `bagBLen * (bagPLen + 2)` memory-cost bound for `forgetWeightProg`. -/
theorem forgetWeightProg_spec {w : ℕ} (args : ForgetWeightArgs) {wtL LP LB : List ℕ}
    {s : Memory.State}
    (hwt : HoldsIn args.wtPtr wtL s)
    (hLP : HoldsIn args.bagPPtr LP s) (hlenP : LP.length = args.bagPLen)
    (hLB : HoldsIn args.bagBPtr LB s) (hlenB : LB.length = args.bagBLen)
    (hLB_lt : ∀ u ∈ LB, u < wtL.length) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (forgetWeightProg args)) ∧
    (Memory.spec 0).clientState s (forgetWeightProg args) = s ∧
    (Memory.spec 0).clientResult s (forgetWeightProg args) =
      forgetWeight (fun u => wtL.getD u 0) LP LB args.mask ∧
    memoryCost (forgetWeightProg args) s ≤ args.bagBLen * (args.bagPLen + 2) := by
  have hbf := hLB.1
  have hwf := hwt.1
  obtain ⟨-, hloop⟩ := Memory.FramedTriple.iterate (s := s) (body := forgetWeightStep)
    (c := args.bagPLen + 2) (S := ∅) (safe := fun _ _ _ => True)
    (d := ⟨args.wtPtr, args.bagPPtr, args.bagPLen⟩) (n := args.bagBLen)
    (a₀ := ⟨args.bagBPtr, args.mask, 0⟩)
    (Q := fun st _ => st.acc = forgetWeight (fun u => wtL.getD u 0) LP LB args.mask)
    (fun k st t => t = s ∧ st.curB = args.bagBPtr + k ∧
      st.acc + forgetWeight (fun u => wtL.getD u 0) LP (LB.drop k) st.curT =
        forgetWeight (fun u => wtL.getD u 0) LP LB args.mask) ⟨rfl, rfl, by simp⟩
    (fun k hk st t ⟨ht, hcur, hacc⟩ _ => ⟨trivial, by
      subst t
      have hu : s.mem st.curB < wtL.length := by
        rw [hcur, hLB.get k (by omega)]; exact hLB_lt _ (List.getElem_mem _)
      have := bagMemProg_framed (w := w) ⟨s.mem st.curB, args.bagPPtr, args.bagPLen⟩ hLP hlenP
      unfold forgetWeightStep
      framed_triple
      refine ⟨rfl, by dsimp only; omega, ?_⟩
      have hwu : s.mem (args.wtPtr + s.mem st.curB) = wtL.getD (s.mem st.curB) 0 := by
        rw [hwt.get _ hu, List.getElem_eq_getD 0]
      rw [← hacc, hwu, hcur, hLB.get k (by omega), List.drop_eq_getElem_cons (i := k) (by omega)]
      dsimp only [forgetWeight]
      by_cases hbit : st.curT % 2 = 1 <;> cases memBag LB[k] LP <;> simp [hbit, Nat.add_assoc]⟩)
    fun st t ⟨_, _, h⟩ _ => by
      rw [← hlenB, List.drop_length] at h; simpa only [forgetWeight, Nat.add_zero] using h
  have hft : Memory.FramedTriple w s (forgetWeightProg args) (args.bagBLen * (args.bagPLen + 2))
      ∅ fun r _ => r = forgetWeight (fun u => wtL.getD u 0) LP LB args.mask :=
    Memory.FramedTriple.mono (Memory.FramedTriple.call (c₂ := 0) hloop subset_rfl
      fun st _ h _ => Memory.FramedTriple.pure h) (by rw [Nat.mul_comm]; omega) fun _ _ => id
  obtain ⟨hv, hc, -, hres⟩ := framedTriple_iff_realization.mp hft
  exact ⟨hv, forgetWeightProg_state args s, hres, hc⟩

/-- Result upper bound `≤ bagBLen * wtL.foldl max 0` for `forgetWeightProg`. -/
theorem forgetWeightProg_result_le (args : ForgetWeightArgs) {wtL LP LB : List ℕ}
    {t : Memory.State} (hwt_t : HoldsIn args.wtPtr wtL t)
    (hLP_t : HoldsIn args.bagPPtr LP t) (hLP_len : LP.length = args.bagPLen)
    (hLB_t : HoldsIn args.bagBPtr LB t) (hLB_len : LB.length = args.bagBLen)
    (hLB_lt_wt : ∀ u ∈ LB, u < wtL.length) :
    (Memory.spec 0).clientResult t (forgetWeightProg args) ≤ args.bagBLen * wtL.foldl max 0 := by
  rw [(forgetWeightProg_spec (w := 0) args hwt_t hLP_t hLP_len hLB_t hLB_len hLB_lt_wt).2.2.1,
    ← hLB_len]
  exact forgetWeight_le_foldl_max wtL LP LB args.mask hLB_lt_wt

/-- Exact-basis Word-RAM realization certificate for `forgetWeightProg`. -/
theorem forgetWeightProg_realizes :
    Realizes .exact forgetWeightProg WordEncoding.encode WordEncoding.encode
      (fun w args s =>
        Fits w 2 ∧
        ∃ wtL LB,
          HoldsIn args.wtPtr wtL s ∧ HoldsIn args.bagBPtr LB s ∧ LB.length = args.bagBLen ∧
          (∀ u ∈ LB, u < wtL.length) ∧
          Fits w (args.wtPtr + wtL.length) ∧
          Fits w (args.bagPPtr + args.bagPLen) ∧ Fits w (args.bagBPtr + args.bagBLen) ∧
          Fits w (args.bagBLen * wtL.foldl max 0))
      (fun _ _ => 0) := by
  unfold forgetWeightProg
  realize [bagMemProg_realizes]
  obtain ⟨h2, wtL, LB, hwt_h, hLB_h, hLB_len, hLB_lt, hfitW, hfitP, hfitB, hfitSum⟩ := h
  have h1 : Fits w 1 := h2.of_le (by decide)
  have h2_ne : 2 ≠ 0 := by decide
  let W := wtL.foldl max 0
  refine iterationSafe_of_stepInv _ _ w _
    (fun (j : ℕ) (st : ForgetWeightState) (t : Memory.State) =>
      j ≤ d.bagBLen ∧ st.curB + j = d.bagBPtr + d.bagBLen ∧
      HoldsIn d.wtPtr wtL t ∧ HoldsIn st.curB (LB.drop (d.bagBLen - j)) t ∧
      st.acc ≤ (d.bagBLen - j) * W)
    (fun j st t ⟨hj_le, hcur, hwt_t, hrem, hacc_le⟩ => ?_)
    ⟨le_rfl, rfl, hwt_h, by simpa only [Nat.sub_self, List.drop_zero] using hLB_h, by simp⟩
  have hj_lt : d.bagBLen - (j + 1) < LB.length := by omega
  have hsub : d.bagBLen - j = (d.bagBLen - (j + 1)) + 1 := by omega
  rw [List.drop_eq_getElem_cons hj_lt, ← hsub, HoldsIn.cons_iff] at hrem
  obtain ⟨_, hmem_u, hrem_next⟩ := hrem
  have hu_lt : t.mem st.curB < wtL.length := hmem_u ▸ hLB_lt _ (List.getElem_mem hj_lt)
  have hwu_le : t.mem (d.wtPtr + t.mem st.curB) ≤ W :=
    hwt_t.get _ hu_lt ▸ List.mem_le_foldl_max (List.getElem_mem hu_lt)
  have hacc_next_le : st.acc + t.mem (d.wtPtr + t.mem st.curB) ≤ (d.bagBLen - j) * W := by
    calc st.acc + t.mem (d.wtPtr + t.mem st.curB)
        ≤ (d.bagBLen - (j + 1)) * W + W := Nat.add_le_add hacc_le hwu_le
      _ = (d.bagBLen - j) * W := by rw [hsub, Nat.succ_mul]
  have hacc_max : (d.bagBLen - j) * W ≤ d.bagBLen * W :=
    Nat.mul_le_mul_right W (Nat.sub_le _ _)
  have hcur_fit : Fits w (st.curB + 1) := hfitB.of_le (by omega)
  have hwt_fit : Fits w (d.wtPtr + t.mem st.curB) := hfitW.of_le (by omega)
  have hadd_fit : Fits w (st.acc + t.mem (d.wtPtr + t.mem st.curB)) :=
    hfitSum.of_le (hacc_next_le.trans hacc_max)
  have hacc_fit : Fits w (st.acc + 0) := hadd_fit.of_le (Nat.add_le_add_left (Nat.zero_le _) _)
  let addW := if st.curT % 2 = 1 then
    if (Memory.spec 0).clientResult t (bagMemProg ⟨t.mem st.curB, d.bagPPtr, d.bagPLen⟩) = 0 then
      t.mem (d.wtPtr + t.mem st.curB) else 0
    else 0
  have hadd_le : addW ≤ t.mem (d.wtPtr + t.mem st.curB) := by
    dsimp only [addW]
    split_ifs <;> omega
  obtain ⟨hst_body, hres_body⟩ := forgetWeightStep_eval ⟨d.wtPtr, d.bagPPtr, d.bagPLen⟩ st t
  change _ = (⟨st.curB + 1, st.curT / 2, st.acc + addW⟩ : ForgetWeightState) at hres_body
  refine ⟨by repeat (first | split | assumption | refine And.intro ?_ ?_),
    Nat.le_of_succ_le hj_le, ?_, by rwa [hst_body], ?_, ?_⟩
  · simp only [hres_body]; omega
  · rwa [hst_body, hres_body]
  · simpa only [hres_body] using (Nat.add_le_add_left hadd_le _).trans hacc_next_le

end Cslib.Algorithms.WordRAM.TreeDecomposition
