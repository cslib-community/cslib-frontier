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

private theorem elimOrderLoop_aux {w : ℕ} (env : ElimLoopEnv)
    {R M SW W B : ℕ} (hW_SW : W ≤ SW) (hB : Fits w B) (h1 : Fits w 1)
    (hpowSW : Fits w ((max 1 env.dom) ^ SW)) :
    ∀ (ord : List ℕ) (idx : ℕ) (st0 : ElimStepState) (es : ElimState ℕ ℕ) (t : Memory.State),
      Memory.WellFormed w t →
      HoldsIn (env.orderPtr + idx) ord t →
      HoldsElimState st0 es t →
      es.live.length ≤ M →
      es.remaining.length ≤ R →
      (∀ f ∈ es.live, f.scope.length ≤ SW) →
      (∀ s_st ∈ traceOrder env.dom ord es, s_st.jointScopeVars ≤ W) →
      (max 1 env.dom) ^ ord.length * stateCap es ≤ B →
      Fits w (t.frontier + ord.length * stepMemDelta R M SW env.dom W) →
      let st_in : ElimLoopState :=
        ⟨idx, st0.scalar, st0.livePtr, st0.liveLen, st0.remPtr, st0.remLen⟩
      let p := iterate elimOrderStep env ord.length st_in
      let r := (Memory.spec 0).clientResult t p
      let t' := (Memory.spec 0).clientState t p
      let es' := eliminateOrder env.dom ord es
      (Memory.spec w).ValidHistory t ((Memory.spec w).clientHistory t p) ∧
        PreservesBelow t.frontier t t' ∧
        t'.frontier ≤ t.frontier + ord.length * stepMemDelta R M SW env.dom W ∧
        HoldsElimState ⟨r.scalar, r.livePtr, r.liveLen, r.remPtr, r.remLen⟩ es' t' ∧
        memoryCost p t ≤
          ord.length * (1 + stepFixedCost R M SW env.dom W) +
            ((traceOrder env.dom ord es).map ElimStepStats.bucketFactors).sum *
              stepBucketUnitCost SW env.dom W
  | [], idx, st0, es, t, _, _, hes, _, _, _, _, _, _ => by
      dsimp only
      have h0 : iterate elimOrderStep env 0
          ⟨idx, st0.scalar, st0.livePtr, st0.liveLen, st0.remPtr, st0.remLen⟩ =
          pure ⟨idx, st0.scalar, st0.livePtr, st0.liveLen, st0.remPtr, st0.remLen⟩ := rfl
      simp only [List.length_nil]
      rw [h0]
      exact ⟨validHistory_pure w t _, PreservesBelow.refl le_rfl, Nat.le_add_right _ _, hes,
        by simp [memoryCost_pure, traceOrder]⟩
  | x :: xs, idx, st0, es, t, hwf, hord, hes, hM, hR, hSW, hW_all, hcap, hfit_fr => by
      dsimp only
      obtain ⟨hrd_lt, hm_x, hord_tail⟩ := holdsIn_cons_shift hord
      have hW_head : (stepStats env.dom x es).jointScopeVars ≤ W :=
        hW_all _ (by simp [traceOrder])
      have hW_tail : ∀ s_st ∈ traceOrder env.dom xs (elimVar env.dom x es),
          s_st.jointScopeVars ≤ W :=
        fun s_st hs => hW_all s_st (by simp [traceOrder, hs])
      simp only [List.length_cons] at hcap hfit_fr ⊢
      have hpow_pos : 1 ≤ (max 1 env.dom) ^ xs.length :=
        Nat.one_le_pow _ _ (le_max_left 1 env.dom)
      have hcap_step : max 1 env.dom * stateCap es ≤ B := by
        have hmul : 1 * (max 1 env.dom * stateCap es) ≤
            (max 1 env.dom) ^ xs.length * (max 1 env.dom * stateCap es) :=
          Nat.mul_le_mul_right _ hpow_pos
        have heq : (max 1 env.dom) ^ xs.length * (max 1 env.dom * stateCap es) =
            (max 1 env.dom) ^ (xs.length + 1) * stateCap es := by rw [Nat.pow_succ]; ring
        omega
      have hdelta_one : t.frontier + stepMemDelta R M SW env.dom W ≤
          t.frontier + (xs.length + 1) * stepMemDelta R M SW env.dom W := by
        rw [Nat.succ_mul]; omega
      let vpArgs : ElimVarArgs :=
        ⟨env.dom, x, st0.scalar, st0.livePtr, st0.liveLen, st0.remPtr, st0.remLen⟩
      have hvp := elimVarProg_spec (w := w) (args := vpArgs) hwf hes hM hR hSW hW_head hW_SW
        hcap_step hB h1 hpowSW (hfit_fr.of_le hdelta_one)
      dsimp only at hvp
      generalize ht₁ : (Memory.spec 0).clientState t (elimVarProg vpArgs) = t₁ at hvp
      generalize hst₁ : (Memory.spec 0).clientResult t (elimVarProg vpArgs) = st₁ at hvp
      obtain ⟨hvp_val, hvp_pres, hvp_fr, hvp_es, hvp_cost⟩ := hvp
      dsimp only [vpArgs] at hvp_fr hvp_es hvp_cost
      have hwf₁ : Memory.WellFormed w t₁ :=
        by rw [← ht₁]; exact wellFormed_clientState hwf hvp_val
      have hord_t₁ : HoldsIn (env.orderPtr + (idx + 1)) xs t₁ := by
        rw [show env.orderPtr + (idx + 1) = env.orderPtr + idx + 1 by omega]
        exact hord_tail.mono_frontier hvp_pres
      have hM₁ : (elimVar env.dom x es).live.length ≤ M :=
        (length_elimVar_live_le env.dom x es).trans hM
      have hR₁ : (elimVar env.dom x es).remaining.length ≤ R :=
        (length_elimVar_remaining_le env.dom x es).trans hR
      have hSW₁ : ∀ f ∈ (elimVar env.dom x es).live, f.scope.length ≤ SW :=
        scope_elimVar_le_of_le env.dom x es hSW hW_head hW_SW
      have hcap₁ : (max 1 env.dom) ^ xs.length * stateCap (elimVar env.dom x es) ≤ B := by
        calc (max 1 env.dom) ^ xs.length * stateCap (elimVar env.dom x es)
            ≤ (max 1 env.dom) ^ xs.length * (max 1 env.dom * stateCap es) :=
              Nat.mul_le_mul_left _ (stateCap_elimVar_le env.dom x es)
          _ = (max 1 env.dom) ^ (xs.length + 1) * stateCap es := by rw [Nat.pow_succ]; ring
          _ ≤ B := hcap
      have hfit₁ : Fits w (t₁.frontier + xs.length * stepMemDelta R M SW env.dom W) := by
        refine hfit_fr.of_le ?_
        rw [Nat.succ_mul]
        omega
      have hih := elimOrderLoop_aux env hW_SW hB h1 hpowSW xs (idx + 1) st₁
        (elimVar env.dom x es) t₁ hwf₁ hord_t₁ hvp_es hM₁ hR₁ hSW₁ hW_tail hcap₁ hfit₁
      dsimp only at hih
      obtain ⟨hih_val, hih_pres, hih_fr, hih_es, hih_cost⟩ := hih
      have hr_st (addr : ℕ) : (Memory.spec 0).clientState t (Memory.read addr) = t := rfl
      have hr_res (addr : ℕ) : (Memory.spec 0).clientResult t (Memory.read addr) = t.mem addr := rfl
      have hpure_st {α : Type} (y : α) (u : Memory.State) :
          (Memory.spec 0).clientState u (pure y) = u := rfl
      have hpure_res {α : Type} (y : α) (u : Memory.State) :
          (Memory.spec 0).clientResult u (pure y) = y := rfl
      have hstep_st : (Memory.spec 0).clientState t
          (elimOrderStep (env, ⟨idx, st0.scalar, st0.livePtr, st0.liveLen, st0.remPtr,
            st0.remLen⟩)) = t₁ := by
        unfold elimOrderStep
        dsimp only
        rw [StateTransitionSpec.clientState_bind, hr_st, hr_res, hm_x,
          StateTransitionSpec.clientState_bind, ht₁, hst₁, hpure_st]
      have hstep_res : (Memory.spec 0).clientResult t
          (elimOrderStep (env, ⟨idx, st0.scalar, st0.livePtr, st0.liveLen, st0.remPtr,
            st0.remLen⟩)) =
          ⟨idx + 1, st₁.scalar, st₁.livePtr, st₁.liveLen, st₁.remPtr, st₁.remLen⟩ := by
        unfold elimOrderStep
        dsimp only
        rw [StateTransitionSpec.clientResult_bind, hr_st, hr_res, hm_x,
          StateTransitionSpec.clientResult_bind, ht₁, hst₁, hpure_res]
      have hstep_val : (Memory.spec w).ValidHistory t
          ((Memory.spec w).clientHistory t (elimOrderStep
            (env, ⟨idx, st0.scalar, st0.livePtr, st0.liveLen, st0.remPtr, st0.remLen⟩))) := by
        unfold elimOrderStep
        dsimp only
        refine validHistory_read_bind hrd_lt ?_
        rw [hm_x]
        refine validHistory_bind_step hvp_val ?_
        rw [ht₁, hst₁]
        exact validHistory_pure w t₁ _
      have hstep_cost : memoryCost (elimOrderStep
          (env, ⟨idx, st0.scalar, st0.livePtr, st0.liveLen, st0.remPtr, st0.remLen⟩)) t ≤
          1 + stepFixedCost R M SW env.dom W +
            (stepStats env.dom x es).bucketFactors * stepBucketUnitCost SW env.dom W := by
        unfold elimOrderStep
        dsimp only
        rw [memoryCost_bind', memoryCost_read, hr_st, hr_res, hm_x,
          memoryCost_bind', ht₁, hst₁, memoryCost_pure, Nat.add_zero]
        omega
      have hiter_eq : iterate elimOrderStep env (xs.length + 1)
          ⟨idx, st0.scalar, st0.livePtr, st0.liveLen, st0.remPtr, st0.remLen⟩ =
          (elimOrderStep
            (env, ⟨idx, st0.scalar, st0.livePtr, st0.liveLen, st0.remPtr, st0.remLen⟩) >>=
            iterate elimOrderStep env xs.length) := rfl
      rw [hiter_eq, StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind,
        hstep_st, hstep_res]
      refine ⟨validHistory_bind_step hstep_val ?_,
        hvp_pres.trans (hih_pres.mono_bound hvp_pres.2.1),
        by rw [Nat.succ_mul]; omega,
        hih_es, ?_⟩
      · rw [hstep_st, hstep_res]
        exact hih_val
      · rw [memoryCost_bind', hstep_st, hstep_res]
        simp only [traceOrder, List.map_cons, List.sum_cons]
        calc memoryCost _ t + _
            ≤ (1 + stepFixedCost R M SW env.dom W +
                (stepStats env.dom x es).bucketFactors * stepBucketUnitCost SW env.dom W) +
              (xs.length * (1 + stepFixedCost R M SW env.dom W) +
                ((traceOrder env.dom xs (elimVar env.dom x es)).map
                  ElimStepStats.bucketFactors).sum * stepBucketUnitCost SW env.dom W) :=
              Nat.add_le_add hstep_cost hih_cost
          _ = (xs.length + 1) * (1 + stepFixedCost R M SW env.dom W) +
                ((stepStats env.dom x es).bucketFactors +
                  ((traceOrder env.dom xs (elimVar env.dom x es)).map
                    ElimStepStats.bucketFactors).sum) * stepBucketUnitCost SW env.dom W := by ring

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
  have hord0 : HoldsIn (args.orderPtr + 0) ord s := by simpa using hord
  obtain ⟨hval, hpres, hfr, hes', hcost⟩ :=
    elimOrderLoop_aux (w := w) ⟨args.dom, args.orderPtr⟩ hW_SW hB h1 hpowSW ord 0
      ⟨args.scalar, args.livePtr, args.liveLen, args.remPtr, args.remLen⟩ es s
      hwf hord0 hes hM hR hSW hW hcap hfit_fr
  refine ⟨hval, hpres, hfr, hes', ?_⟩
  have hbk_sum : ((traceOrder args.dom ord es).map ElimStepStats.bucketFactors).sum ≤
      M + ord.length := by
    have hsb := sum_bucketFactors_le args.dom ord es
    omega
  exact hcost.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ hbk_sum) _)

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
      Memory.WellFormed w t ∧
      st.idx + j = d.orderLen ∧
      ∃ ord es,
        ord.length = j ∧
        HoldsIn (d.orderPtr + st.idx) ord t ∧
        HoldsElimState ⟨st.scalar, st.livePtr, st.liveLen, st.remPtr, st.remLen⟩ es t ∧
        es.live.length ≤ M ∧
        es.remaining.length ≤ R ∧
        (∀ f ∈ es.live, f.scope.length ≤ SW) ∧
        (∀ s_st ∈ traceOrder d.dom ord es, s_st.jointScopeVars ≤ W) ∧
        (max 1 d.dom) ^ j * stateCap es ≤ B ∧
        Fits w (t.frontier + j * stepMemDelta R M SW d.dom W))
    (fun j st t ⟨hwf_t, hidx_sum, ord, es, hlen_j, hord_t, hes_t, hM_t, hR_t, hSW_t,
      hW_t, hcap_t, hfit_t⟩ => ?_)
    ⟨hmem, Nat.zero_add _, ord₀, es₀, hord_len, by simpa using hord₀, hes₀, hM₀, hR₀, hSW₀,
      hW₀, hcap₀, hfit_fr⟩
  dsimp only
  rcases ord with _ | ⟨x, xs⟩
  · cases hlen_j
  simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen_j
  subst hlen_j
  obtain ⟨hrd_lt, hm_x, hord_tail⟩ := holdsIn_cons_shift hord_t
  have hW_head : (stepStats d.dom x es).jointScopeVars ≤ W := hW_t _ (by simp [traceOrder])
  have hW_tail : ∀ s_st ∈ traceOrder d.dom xs (elimVar d.dom x es), s_st.jointScopeVars ≤ W :=
    fun s_st hs => hW_t s_st (by simp [traceOrder, hs])
  have hpow_pos : 1 ≤ (max 1 d.dom) ^ xs.length := Nat.one_le_pow _ _ (le_max_left 1 d.dom)
  have hcap_step : max 1 d.dom * stateCap es ≤ B := by
    have hmul : 1 * (max 1 d.dom * stateCap es) ≤
        (max 1 d.dom) ^ xs.length * (max 1 d.dom * stateCap es) :=
      Nat.mul_le_mul_right _ hpow_pos
    have heq : (max 1 d.dom) ^ xs.length * (max 1 d.dom * stateCap es) =
        (max 1 d.dom) ^ (xs.length + 1) * stateCap es := by rw [Nat.pow_succ]; ring
    omega
  have hfit_one : Fits w (t.frontier + stepMemDelta R M SW d.dom W) :=
    hfit_t.of_le (by rw [Nat.succ_mul]; omega)
  have hr_st (addr : ℕ) : (Memory.spec 0).clientState t (Memory.read addr) = t := rfl
  have hr_res (addr : ℕ) : (Memory.spec 0).clientResult t (Memory.read addr) = t.mem addr := rfl
  have hpure_st {α : Type} (y : α) (u : Memory.State) :
      (Memory.spec 0).clientState u (pure y) = u := rfl
  have hpure_res {α : Type} (y : α) (u : Memory.State) :
      (Memory.spec 0).clientResult u (pure y) = y := rfl
  refine ⟨?_, ?_⟩
  · refine ⟨hwf_t.frontier_fits.of_le hrd_lt.le, ?_, ?_⟩
    · simp only [hm_x]
      exact ⟨h1, es, R, M, SW, W, B, hes_t, hM_t, hR_t, hSW_t, hW_head, hW_SW,
        hcap_step, hB, hpowSW, hfit_one⟩
    · have hidx_lt : st.idx + 1 ≤ t.frontier := by
        have hbd := hord_t.1
        simp only [List.length_cons] at hbd
        omega
      exact hwf_t.frontier_fits.of_le hidx_lt
  · let vpArgs : ElimVarArgs :=
      ⟨d.dom, x, st.scalar, st.livePtr, st.liveLen, st.remPtr, st.remLen⟩
    have hvp := elimVarProg_spec (w := w) (args := vpArgs) hwf_t hes_t hM_t hR_t hSW_t
      hW_head hW_SW hcap_step hB h1 hpowSW hfit_one
    dsimp only at hvp
    generalize ht₁ : (Memory.spec 0).clientState t (elimVarProg vpArgs) = t₁ at hvp
    generalize hst₁ : (Memory.spec 0).clientResult t (elimVarProg vpArgs) = st₁ at hvp
    obtain ⟨hvp_val, hvp_pres, hvp_fr, hvp_es, _⟩ := hvp
    dsimp only [vpArgs] at hvp_fr hvp_es
    have hwf₁ : Memory.WellFormed w t₁ :=
      by rw [← ht₁]; exact wellFormed_clientState hwf_t hvp_val
    unfold elimOrderStep
    dsimp only
    rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind,
      hr_st, hr_res, hm_x,
      StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind,
      ht₁, hst₁, hpure_st, hpure_res]
    refine ⟨hwf₁, by dsimp only; omega, xs, elimVar d.dom x es, rfl, ?_, hvp_es,
      (length_elimVar_live_le d.dom x es).trans hM_t,
      (length_elimVar_remaining_le d.dom x es).trans hR_t,
      scope_elimVar_le_of_le d.dom x es hSW_t hW_head hW_SW,
      hW_tail, ?_, ?_⟩
    · dsimp only
      rw [show d.orderPtr + (st.idx + 1) = d.orderPtr + st.idx + 1 by omega]
      exact hord_tail.mono_frontier hvp_pres
    · calc (max 1 d.dom) ^ xs.length * stateCap (elimVar d.dom x es)
          ≤ (max 1 d.dom) ^ xs.length * (max 1 d.dom * stateCap es) :=
            Nat.mul_le_mul_left _ (stateCap_elimVar_le d.dom x es)
        _ = (max 1 d.dom) ^ (xs.length + 1) * stateCap es := by rw [Nat.pow_succ]; ring
        _ ≤ B := hcap_t
    · refine hfit_t.of_le ?_
      rw [Nat.succ_mul]
      omega

end Cslib.Algorithms.WordRAM.VariableElimination
