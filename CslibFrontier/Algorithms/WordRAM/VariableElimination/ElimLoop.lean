/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.VariableElimination.ElimVar
import CslibFrontier.Tactic.Realize
import Mathlib.Tactic.Ring

/-!
# Sequential Elimination Loop (`elimOrderLoop`)

Iterates `elimVarProg` over the supplied elimination order array with amortized `M + T` bucket
factor accounting (`elimOrderLoop_spec`).

## Main definitions

* `Cslib.Algorithms.WordRAM.VariableElimination.elimOrderLoop`: order-sweep elimination loop.
-/

public section

namespace Cslib.Algorithms.WordRAM.VariableElimination

open Cslib.Logic.PL Cslib.Logic.PL.CSP
open Cslib.Algorithms.Lean.CSP
open Cslib.DataStructure
open Cslib.WordRAM
open Cslib.WordRAM.Realization

/-! ### Sequential elimination loop (`elimOrderLoop`) -/

private theorem scope_elimVar_le_of_le (d x : ℕ) (s : ElimState ℕ ℕ) {SW W : ℕ}
    (hs : ∀ f ∈ s.live, f.scope.length ≤ SW)
    (hstep : (stepStats d x s).jointScopeVars ≤ W) (hW_SW : W ≤ SW) :
    ∀ f ∈ (elimVar d x s).live, f.scope.length ≤ SW := by
  have h := scope_length_elimVar_le d x s (S := SW) (W := W)
    (fun f hf => (hs f hf).trans (le_max_left SW W)) hstep
  simpa [max_eq_left hW_SW] using h

private structure ElimLoopEnv where
  dom : ℕ
  orderPtr : ℕ

private def ElimLoopEnv.equiv : ElimLoopEnv ≃ ℕ × ℕ where
  toFun e := (e.dom, e.orderPtr)
  invFun := fun (dom, orderPtr) => ⟨dom, orderPtr⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding ElimLoopEnv := .ofEquiv ElimLoopEnv.equiv

/-- Loop-carried state tracking live descriptor/remaining arrays and cursors. -/
structure ElimLoopState where
  /-- Field `idx` of `ElimLoopState`. -/
  idx : ℕ
  /-- Field `scalar` of `ElimLoopState`. -/
  scalar : ℕ
  /-- Field `livePtr` of `ElimLoopState`. -/
  livePtr : ℕ
  /-- Field `liveLen` of `ElimLoopState`. -/
  liveLen : ℕ
  /-- Field `remPtr` of `ElimLoopState`. -/
  remPtr : ℕ
  /-- Field `remLen` of `ElimLoopState`. -/
  remLen : ℕ

/-- Product equivalence encoding `ElimLoopState` as words. -/
@[expose] def ElimLoopState.equiv :
    ElimLoopState ≃ ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ where
  toFun s := (((((s.idx, s.scalar), s.livePtr), s.liveLen), s.remPtr), s.remLen)
  invFun := fun (((((idx, scalar), livePtr), liveLen), remPtr), remLen) =>
    ⟨idx, scalar, livePtr, liveLen, remPtr, remLen⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : WordEncoding ElimLoopState := .ofEquiv ElimLoopState.equiv

/-- Arguments for driving `elimOrderLoop` across an elimination order. -/
structure ElimOrderArgs where
  /-- Field `dom` of `ElimOrderArgs`. -/
  dom : ℕ
  /-- Field `orderPtr` of `ElimOrderArgs`. -/
  orderPtr : ℕ
  /-- Field `orderLen` of `ElimOrderArgs`. -/
  orderLen : ℕ
  /-- Field `scalar` of `ElimOrderArgs`. -/
  scalar : ℕ
  /-- Field `livePtr` of `ElimOrderArgs`. -/
  livePtr : ℕ
  /-- Field `liveLen` of `ElimOrderArgs`. -/
  liveLen : ℕ
  /-- Field `remPtr` of `ElimOrderArgs`. -/
  remPtr : ℕ
  /-- Field `remLen` of `ElimOrderArgs`. -/
  remLen : ℕ

/-- Product equivalence encoding `ElimOrderArgs` as words. -/
@[expose] def ElimOrderArgs.equiv :
    ElimOrderArgs ≃ ((((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ where
  toFun s := (((((((s.dom, s.orderPtr), s.orderLen), s.scalar), s.livePtr), s.liveLen), s.remPtr),
    s.remLen)
  invFun := fun (((((((dom, orderPtr), orderLen), scalar), livePtr), liveLen), remPtr), remLen) =>
    ⟨dom, orderPtr, orderLen, scalar, livePtr, liveLen, remPtr, remLen⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : WordEncoding ElimOrderArgs := .ofEquiv ElimOrderArgs.equiv

private def elimOrderStep : ElimLoopEnv × ElimLoopState → Memory.Prog ElimLoopState :=
  fun ⟨env, st⟩ =>
    Memory.read (env.orderPtr + st.idx) >>= fun x =>
    elimVarProg ⟨env.dom, x, st.scalar, st.livePtr, st.liveLen, st.remPtr, st.remLen⟩ >>=
      fun st' =>
    pure ⟨st.idx + 1, st'.scalar, st'.livePtr, st'.liveLen, st'.remPtr, st'.remLen⟩

/-- Sequentially eliminate every variable in the stored order array. -/
def elimOrderLoop (args : ElimOrderArgs) : Memory.Prog ElimLoopState :=
  iterate elimOrderStep ⟨args.dom, args.orderPtr⟩ args.orderLen
    ⟨0, args.scalar, args.livePtr, args.liveLen, args.remPtr, args.remLen⟩

private theorem cap_split {d n c B : ℕ} (h : (max 1 d) ^ (n + 1) * c ≤ B) :
    max 1 d * c ≤ B ∧ (max 1 d) ^ n * (max 1 d * c) ≤ B := by
  rw [Nat.pow_succ, mul_assoc] at h
  exact ⟨(Nat.le_mul_of_pos_left _ (Nat.one_le_pow _ _ (le_max_left 1 d))).trans h, h⟩

/-- Invariant of `elimOrderLoop` at loop state `st` with the order suffix `ord` still to run. -/
private structure LoopInv (w : ℕ) (env : ElimLoopEnv) (R M SW W B : ℕ) (ord : List ℕ)
    (st : ElimLoopState) (es : ElimState ℕ ℕ) (t : Memory.State) : Prop where
  wf : Memory.WellFormed w t
  holds : HoldsIn (env.orderPtr + st.idx) ord t
  elim : HoldsElimState ⟨st.scalar, st.livePtr, st.liveLen, st.remPtr, st.remLen⟩ es t
  live : es.live.length ≤ M
  rem : es.remaining.length ≤ R
  scope : ∀ f ∈ es.live, f.scope.length ≤ SW
  joint : ∀ s_st ∈ traceOrder env.dom ord es, s_st.jointScopeVars ≤ W
  cap : (max 1 env.dom) ^ ord.length * stateCap es ≤ B
  fit : Fits w (t.frontier + ord.length * stepMemDelta R M SW env.dom W)

private theorem elimOrderStep_spec {w : ℕ} (env : ElimLoopEnv) {R M SW W B x : ℕ}
    {xs : List ℕ} {st : ElimLoopState} {es : ElimState ℕ ℕ} {t : Memory.State}
    (hW_SW : W ≤ SW) (hB : Fits w B) (h1 : Fits w 1) (hpowSW : Fits w ((max 1 env.dom) ^ SW))
    (hinv : LoopInv w env R M SW W B (x :: xs) st es t) :
    let p := elimOrderStep (env, st)
    let t' := (Memory.spec 0).clientState t p
    let r := (Memory.spec 0).clientResult t p
    (Memory.spec w).ValidHistory t ((Memory.spec w).clientHistory t p) ∧
      PreservesBelow t.frontier t t' ∧
      t'.frontier ≤ t.frontier + stepMemDelta R M SW env.dom W ∧ r.idx = st.idx + 1 ∧
      LoopInv w env R M SW W B xs r (elimVar env.dom x es) t' ∧
      memoryCost p t ≤ 1 + stepFixedCost R M SW env.dom W +
        (stepStats env.dom x es).bucketFactors * stepBucketUnitCost SW env.dom W := by
  obtain ⟨hwf, hord, hes, hM, hR, hSW, hW, hcap, hfit⟩ := hinv
  obtain ⟨hrd_lt, hm_x, hord_tail⟩ := holdsIn_cons_shift hord
  simp only [traceOrder, List.forall_mem_cons, List.length_cons] at hW hcap hfit
  obtain ⟨hcap_step, hcap₁⟩ := cap_split hcap
  have hvp := elimVarProg_spec (w := w)
    (args := ⟨env.dom, x, st.scalar, st.livePtr, st.liveLen, st.remPtr, st.remLen⟩) hwf hes hM
    hR hSW hW.1 hW_SW hcap_step hB h1 hpowSW
    (hfit.of_le (by dsimp only; rw [Nat.add_one_mul]; omega))
  dsimp only at hvp ⊢
  obtain ⟨hvp_val, hvp_pres, hvp_fr, hvp_es, hvp_cost⟩ := hvp
  unfold elimOrderStep
  dsimp only
  refine ⟨validHistory_read_bind hrd_lt ?_, ?_⟩
  · rw [hm_x]
    exact validHistory_bind_step hvp_val (validHistory_pure w _ _)
  rw [clientState_bind_read, clientResult_bind_read, hm_x, StateTransitionSpec.clientState_bind,
    StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_pure,
    StateTransitionSpec.clientResult_pure, memoryCost_bind', memoryCost_read, clientState_read,
    clientResult_read, hm_x, memoryCost_bind', memoryCost_pure]
  refine ⟨hvp_pres, hvp_fr, rfl, ⟨wellFormed_clientState hwf hvp_val, ?_, hvp_es,
    (length_elimVar_live_le env.dom x es).trans hM,
    (length_elimVar_remaining_le env.dom x es).trans hR,
    scope_elimVar_le_of_le env.dom x es hSW hW.1 hW_SW, hW.2,
    (Nat.mul_le_mul_left _ (stateCap_elimVar_le env.dom x es)).trans hcap₁,
    hfit.of_le (by rw [Nat.add_one_mul]; omega)⟩, by omega⟩
  rw [show env.orderPtr + (st.idx + 1) = env.orderPtr + st.idx + 1 by omega]
  exact hord_tail.mono_frontier hvp_pres

private theorem elimOrderLoop_aux {w : ℕ} (env : ElimLoopEnv) {R M SW W B : ℕ}
    (hW_SW : W ≤ SW) (hB : Fits w B) (h1 : Fits w 1) (hpowSW : Fits w ((max 1 env.dom) ^ SW)) :
    ∀ (ord : List ℕ) (st : ElimLoopState) (es : ElimState ℕ ℕ) (t : Memory.State),
      LoopInv w env R M SW W B ord st es t →
      let p := iterate elimOrderStep env ord.length st
      let r := (Memory.spec 0).clientResult t p
      let t' := (Memory.spec 0).clientState t p
      (Memory.spec w).ValidHistory t ((Memory.spec w).clientHistory t p) ∧
        PreservesBelow t.frontier t t' ∧
        t'.frontier ≤ t.frontier + ord.length * stepMemDelta R M SW env.dom W ∧
        HoldsElimState ⟨r.scalar, r.livePtr, r.liveLen, r.remPtr, r.remLen⟩
          (eliminateOrder env.dom ord es) t' ∧
        memoryCost p t ≤
          ord.length * (1 + stepFixedCost R M SW env.dom W) +
            ((traceOrder env.dom ord es).map ElimStepStats.bucketFactors).sum *
              stepBucketUnitCost SW env.dom W
  | [], st, es, t, hinv => by
      have h0 : iterate elimOrderStep env ([] : List ℕ).length st = pure st := rfl
      dsimp only
      rw [h0, memoryCost_pure]
      exact ⟨validHistory_pure w t _, PreservesBelow.refl le_rfl, Nat.le_add_right _ _, hinv.elim,
        Nat.zero_le _⟩
  | x :: xs, st, es, t, hinv => by
      obtain ⟨hval, hpres, hfr, -, hinv₁, hcost⟩ :=
        elimOrderStep_spec env hW_SW hB h1 hpowSW hinv
      obtain ⟨ih_val, ih_pres, ih_fr, ih_es, ih_cost⟩ :=
        elimOrderLoop_aux env hW_SW hB h1 hpowSW xs _ _ _ hinv₁
      have hiter : iterate elimOrderStep env (x :: xs).length st =
          elimOrderStep (env, st) >>= iterate elimOrderStep env xs.length := rfl
      dsimp only
      rw [hiter, validHistory_bind', StateTransitionSpec.clientResult_bind,
        StateTransitionSpec.clientState_bind, memoryCost_bind']
      simp only [List.length_cons, traceOrder, List.map_cons, List.sum_cons]
      refine ⟨⟨hval, ih_val⟩, hpres.trans (ih_pres.mono_bound hpres.2.1),
        by rw [Nat.add_one_mul]; omega, ih_es, ?_⟩
      rw [Nat.add_one_mul, Nat.add_mul]
      omega

theorem elimOrderLoop_spec {w : ℕ} {args : ElimOrderArgs}
    {ord : List ℕ} {es : ElimState ℕ ℕ} {R M SW W B : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s)
    (hord : HoldsIn args.orderPtr ord s) (hord_len : ord.length = args.orderLen)
    (hes : HoldsElimState ⟨args.scalar, args.livePtr, args.liveLen, args.remPtr, args.remLen⟩ es s)
    (hM : es.live.length ≤ M) (hR : es.remaining.length ≤ R)
    (hSW : ∀ f ∈ es.live, f.scope.length ≤ SW)
    (hW : ∀ st ∈ traceOrder args.dom ord es, st.jointScopeVars ≤ W) (hW_SW : W ≤ SW)
    (hcap : (max 1 args.dom) ^ args.orderLen * stateCap es ≤ B)
    (hB : Fits w B) (h1 : Fits w 1) (hpowSW : Fits w ((max 1 args.dom) ^ SW))
    (hfit_fr : Fits w (s.frontier + args.orderLen * stepMemDelta R M SW args.dom W)) :
    let r := (Memory.spec 0).clientResult s (elimOrderLoop args)
    let s' := (Memory.spec 0).clientState s (elimOrderLoop args)
    let es' := eliminateOrder args.dom ord es
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (elimOrderLoop args)) ∧
      PreservesBelow s.frontier s s' ∧
      s'.frontier ≤ s.frontier + args.orderLen * stepMemDelta R M SW args.dom W ∧
      HoldsElimState ⟨r.scalar, r.livePtr, r.liveLen, r.remPtr, r.remLen⟩ es' s' ∧
      memoryCost (elimOrderLoop args) s ≤
        args.orderLen * (1 + stepFixedCost R M SW args.dom W) +
          (M + args.orderLen) * stepBucketUnitCost SW args.dom W := by
  dsimp only
  unfold elimOrderLoop
  rw [← hord_len] at hcap hfit_fr ⊢
  obtain ⟨hval, hpres, hfr, hes', hcost⟩ :=
    elimOrderLoop_aux (w := w) ⟨args.dom, args.orderPtr⟩ hW_SW hB h1 hpowSW ord
      ⟨0, args.scalar, args.livePtr, args.liveLen, args.remPtr, args.remLen⟩ es s
      ⟨hwf, by simpa using hord, hes, hM, hR, hSW, hW, hcap, hfit_fr⟩
  dsimp only at hcost
  refine ⟨hval, hpres, hfr, hes', hcost.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ ?_) _)⟩
  have := sum_bucketFactors_le args.dom ord es
  omega

theorem elimOrderLoop_realizes :
    Realizes .exact elimOrderLoop WordEncoding.encode WordEncoding.encode
      (fun w args s =>
        ∃ ord es R M SW W B,
          Fits w 1 ∧
          ord.length = args.orderLen ∧
          HoldsIn args.orderPtr ord s ∧
          HoldsElimState
            ⟨args.scalar, args.livePtr, args.liveLen, args.remPtr, args.remLen⟩ es s ∧
          es.live.length ≤ M ∧
          es.remaining.length ≤ R ∧
          (∀ f ∈ es.live, f.scope.length ≤ SW) ∧
          (∀ st ∈ traceOrder args.dom ord es, st.jointScopeVars ≤ W) ∧
          W ≤ SW ∧
          (max 1 args.dom) ^ args.orderLen * stateCap es ≤ B ∧
          Fits w B ∧
          Fits w ((max 1 args.dom) ^ SW) ∧
          Fits w (s.frontier + args.orderLen * stepMemDelta R M SW args.dom W))
      (fun _ _ => 0) := by
  unfold elimOrderLoop
  realize [elimVarProg_realizes]
  obtain ⟨ord₀, es₀, R, M, SW, W, B, h1, hord_len, hord₀, hes₀, hM₀, hR₀, hSW₀,
    hW₀, hW_SW, hcap₀, hB, hpowSW, hfit_fr⟩ := h
  refine iterationSafe_of_stepInv _ _ w _
    (fun (j : ℕ) (st : ElimLoopState) (t : Memory.State) =>
      st.idx + j = d.orderLen ∧ ∃ ord es, ord.length = j ∧
        LoopInv w ⟨d.dom, d.orderPtr⟩ R M SW W B ord st es t)
    (fun j st t ⟨hidx_sum, ord, es, hlen_j, hinv⟩ => ?_)
    ⟨Nat.zero_add _, ord₀, es₀, hord_len,
      ⟨hmem, by simpa using hord₀, hes₀, hM₀, hR₀, hSW₀, hW₀, by rwa [hord_len], by rwa [hord_len]⟩⟩
  dsimp only
  rcases ord with _ | ⟨x, xs⟩
  · cases hlen_j
  simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen_j
  subst hlen_j
  obtain ⟨-, -, -, hidx, hinv₁, -⟩ := elimOrderStep_spec _ hW_SW hB h1 hpowSW hinv
  obtain ⟨hwf_t, hord_t, hes_t, hM_t, hR_t, hSW_t, hW_t, hcap_t, hfit_t⟩ := hinv
  obtain ⟨hrd_lt, hm_x, -⟩ := holdsIn_cons_shift hord_t
  have hbd := hord_t.1
  simp only [traceOrder, List.forall_mem_cons, List.length_cons] at hW_t hcap_t hfit_t hbd
  refine ⟨⟨hwf_t.frontier_fits.of_le hrd_lt.le, ?_, hwf_t.frontier_fits.of_le (by omega)⟩,
    by omega, xs, _, rfl, hinv₁⟩
  simp only [hm_x]
  exact ⟨h1, es, R, M, SW, W, B, hes_t, hM_t, hR_t, hSW_t, hW_t.1, hW_SW, (cap_split hcap_t).1, hB,
    hpowSW, hfit_t.of_le (by rw [Nat.add_one_mul]; omega)⟩

end Cslib.Algorithms.WordRAM.VariableElimination
