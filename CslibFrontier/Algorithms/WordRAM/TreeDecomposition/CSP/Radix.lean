/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.TreeDecomposition.BagAssignment
public import CslibFrontier.Algorithms.WordRAM.TreeDecomposition.Scan
import CslibFrontier.Tactic.Realize

/-!
# Word-RAM radix decoding and Horner projection routines

This module certifies `radixProjProg`, the read-only Word-RAM helper that decodes digits of
`ofRadix q srcL srcM` (using the private single-variable lookup loop `lookupRadixProg`) and
evaluates `toRadix` along a destination variable list via Horner's method, optionally overriding a
single variable `updVar ↦ updVal`.

## Main definitions

* `Cslib.Algorithms.WordRAM.TreeDecomposition.RadixProjArgs`: argument structure for
  `radixProjProg`.
* `Cslib.Algorithms.WordRAM.TreeDecomposition.radixProjAssign`: target assignment function
  modeled by `radixProjProg`.
* `Cslib.Algorithms.WordRAM.TreeDecomposition.radixProjProg`: Horner base-`q` projection program.

## Main results

* `Cslib.Algorithms.WordRAM.TreeDecomposition.radixProjProg_state`,
  `Cslib.Algorithms.WordRAM.TreeDecomposition.radixProjProg_result_lt`,
  `Cslib.Algorithms.WordRAM.TreeDecomposition.radixProjProg_spec`,
  `Cslib.Algorithms.WordRAM.TreeDecomposition.radixProjProg_realizes`: read-only preservation,
  range bound, functional specification, and exact-basis realization of `radixProjProg`.
-/

public section

namespace Cslib.Algorithms.WordRAM.TreeDecomposition

open Cslib.Algorithms.Lean.TreeDecomposition
open Cslib.DataStructure
open Cslib.WordRAM
open Cslib.WordRAM.Realization

/-! ### Low-level Word-RAM bag, radix, and constraint-table routines -/

private structure LookupRadixArgs where
  q : ℕ
  bagPtr : ℕ
  bagLen : ℕ
  m : ℕ
  target : ℕ

private def LookupRadixArgs.equiv : LookupRadixArgs ≃ (((ℕ × ℕ) × ℕ) × ℕ) × ℕ where
  toFun a := ((((a.q, a.bagPtr), a.bagLen), a.m), a.target)
  invFun := fun ((((q, bp), bl), m), t) => ⟨q, bp, bl, m, t⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding LookupRadixArgs := .ofEquiv LookupRadixArgs.equiv

private structure LookupRadixState where
  curPtr : ℕ
  curM : ℕ
  found : ℕ
  ans : ℕ

private def LookupRadixState.equiv : LookupRadixState ≃ ((ℕ × ℕ) × ℕ) × ℕ where
  toFun s := (((s.curPtr, s.curM), s.found), s.ans)
  invFun := fun (((cp, cm), f), a) => ⟨cp, cm, f, a⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding LookupRadixState := .ofEquiv LookupRadixState.equiv

private def lookupRadixStep (env : (ℕ × ℕ) × LookupRadixState) :
    Memory.Prog LookupRadixState := do
  let q := env.1.1
  let target := env.1.2
  let st := env.2
  let v ← Memory.read st.curPtr
  let digit := st.curM % q
  let nextM := st.curM / q
  let hit := if st.found = 0 ∧ target = v then 1 else 0
  let ans' := if hit = 1 then digit else st.ans
  let found' := if hit = 1 then 1 else st.found
  pure ⟨st.curPtr + 1, nextM, found', ans'⟩

private def lookupRadixProg (args : LookupRadixArgs) : Memory.Prog ℕ := do
  let res ← iterate lookupRadixStep (args.q, args.target) args.bagLen
    ⟨args.bagPtr, args.m, 0, 0⟩
  pure res.ans

private theorem lookupRadixProg_state (args : LookupRadixArgs) (s : Memory.State) :
    (Memory.spec 0).clientState s (lookupRadixProg args) = s := by
  unfold lookupRadixProg
  rw [StateTransitionSpec.clientState_bind]
  exact clientState_iterate_eq_of lookupRadixStep (args.q, args.target)
    (fun _ _ => rfl) args.bagLen ⟨args.bagPtr, args.m, 0, 0⟩ s

private theorem lookupRadixProg_result (args : LookupRadixArgs) {LB : List ℕ} {s : Memory.State}
    (hLB : HoldsIn args.bagPtr LB s) (hlen : LB.length = args.bagLen) :
    (Memory.spec 0).clientResult s (lookupRadixProg args) =
      ofRadix args.q LB args.m args.target := by
  unfold lookupRadixProg
  rw [StateTransitionSpec.clientResult_bind]
  suffices ∀ ys curPtr curM found ans,
      HoldsIn curPtr ys s →
      ((found = 0 ∧ ans = 0) ∨ found = 1) →
      ((Memory.spec 0).clientResult s
        (iterate lookupRadixStep (args.q, args.target) ys.length
          ⟨curPtr, curM, found, ans⟩)).ans =
        if found = 1 then ans else ofRadix args.q ys curM args.target by
    have hrun := this LB args.bagPtr args.m 0 0 hLB (.inl ⟨rfl, rfl⟩)
    rw [hlen] at hrun
    exact hrun
  intro ys
  induction ys with
  | nil =>
    intro curPtr curM found ans _ hfd
    change ans = _
    rcases hfd with ⟨rfl, rfl⟩ | rfl <;> simp [ofRadix]
  | cons v rest ih =>
    intro curPtr curM found ans hcur hfd
    obtain ⟨_, hmem_v, hrest⟩ := HoldsIn.cons_iff.mp hcur
    rw [List.length_cons, iterate, StateTransitionSpec.clientResult_bind]
    have hstep_res : (Memory.spec 0).clientResult s
        (lookupRadixStep ((args.q, args.target), ⟨curPtr, curM, found, ans⟩)) =
        ⟨curPtr + 1, curM / args.q,
         if (if found = 0 ∧ args.target = v then 1 else 0) = 1 then 1 else found,
         if (if found = 0 ∧ args.target = v then 1 else 0) = 1 then curM % args.q else ans⟩ := by
      dsimp only [lookupRadixStep]
      rw [clientResult_bind_read, hmem_v]
      rfl
    have hstep_st : (Memory.spec 0).clientState s
        (lookupRadixStep ((args.q, args.target), ⟨curPtr, curM, found, ans⟩)) = s := rfl
    rw [hstep_st, hstep_res]
    rcases hfd with ⟨rfl, rfl⟩ | rfl
    · by_cases htv : args.target = v
      · subst htv
        simpa [ofRadix] using ih (curPtr + 1) (curM / args.q) 1 (curM % args.q) hrest (.inr rfl)
      · simpa [htv, ofRadix] using ih (curPtr + 1) (curM / args.q) 0 0 hrest (.inl ⟨rfl, rfl⟩)
    · simpa using ih (curPtr + 1) (curM / args.q) 1 ans hrest (.inr rfl)

private theorem lookupRadixProg_spec {w : ℕ} (args : LookupRadixArgs)
    {LB : List ℕ} {s : Memory.State}
    (hLB : HoldsIn args.bagPtr LB s) (hlen : LB.length = args.bagLen) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (lookupRadixProg args)) ∧
    (Memory.spec 0).clientState s (lookupRadixProg args) = s ∧
    (Memory.spec 0).clientResult s (lookupRadixProg args) =
      ofRadix args.q LB args.m args.target ∧
    memoryCost (lookupRadixProg args) s ≤ args.bagLen := by
  have hcost : memoryCost (lookupRadixProg args) s ≤ args.bagLen := by
    unfold lookupRadixProg
    rw [memoryCost_bind', memoryCost_pure, Nat.add_zero]
    simpa only [Nat.one_mul] using
      memoryCost_iterate_le_of lookupRadixStep 1 (args.q, args.target)
        (fun _ _ => le_rfl) args.bagLen ⟨args.bagPtr, args.m, 0, 0⟩ s
  suffices ∀ ys st, HoldsIn st.curPtr ys s →
      (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s
          (iterate lookupRadixStep (args.q, args.target) ys.length st)) by
    have hv := this LB ⟨args.bagPtr, args.m, 0, 0⟩ hLB
    rw [hlen] at hv
    refine ⟨?_, lookupRadixProg_state args s, lookupRadixProg_result args hLB hlen, hcost⟩
    unfold lookupRadixProg
    exact validHistory_bind_step hv (validHistory_pure w _ _)
  intro ys
  induction ys with
  | nil => exact fun st _ => validHistory_pure w s st
  | cons _ rest ih =>
    intro st hcur
    rw [HoldsIn.cons_iff] at hcur
    obtain ⟨hb, _, hrest⟩ := hcur
    have hlt : st.curPtr < s.frontier := by omega
    simp only [List.length_cons]
    exact validHistory_bind_step
      (validHistory_read_bind hlt (validHistory_pure w s _))
      (ih _ hrest)

private theorem lookupRadixProg_realizes :
    Realizes .exact lookupRadixProg WordEncoding.encode WordEncoding.encode
      (fun w args _ =>
        0 < args.q ∧ Fits w 1 ∧ Fits w args.q ∧ Fits w args.m ∧
        Fits w (args.bagPtr + args.bagLen))
      (fun _ _ => 0) := by
  unfold lookupRadixProg
  realize
  obtain ⟨hq_pos, h1, hfit_q, hfit_m, hfit_bag⟩ := h
  refine iterationSafe_of_stepInv _ _ w _
    (fun (j : ℕ) (st : LookupRadixState) (_ : Memory.State) =>
      st.curPtr + j = d.bagPtr + d.bagLen ∧
      st.curM ≤ d.m ∧ st.found ≤ 1 ∧ st.ans ≤ d.q)
    (fun j st m ⟨hptr, hm_le, hfd_le, hans_le⟩ => ?_)
    ⟨rfl, le_rfl, Nat.zero_le _, Nat.zero_le _⟩
  dsimp only [lookupRadixStep]
  have hq_ne : d.q ≠ 0 := by omega
  have hfit_ptr : Fits w (st.curPtr + 1) := hfit_bag.of_le (by omega)
  have hm_div : st.curM / d.q ≤ d.m := (Nat.div_le_self _ _).trans hm_le
  have hmod_le : st.curM % d.q ≤ d.q := le_of_lt (Nat.mod_lt _ hq_pos)
  have hfit_div : Fits w (st.curM / d.q) := hfit_m.of_le hm_div
  have hfit_mod : Fits w (st.curM % d.q) := hfit_q.of_le hmod_le
  have hfit_fd : Fits w st.found := h1.of_le hfd_le
  have hfit_ans : Fits w st.ans := hfit_q.of_le hans_le
  refine ⟨?_, ?_, hm_div, ?_, ?_⟩
  · repeat (
      first
      | split
      | exact trivial
      | assumption
      | refine And.intro ?_ ?_)
  · change (st.curPtr + 1) + j = d.bagPtr + d.bagLen; omega
  · change (if _ then 1 else st.found) ≤ 1; split_ifs <;> omega
  · change (if _ then _ else st.ans) ≤ d.q; split_ifs <;> omega

/-! ### General Horner radix projection (`radixProjProg`) -/

/-- Register arguments for the Horner radix projection routine `radixProjProg`. -/
structure RadixProjArgs where
  /-- Domain size `q`. -/
  q : ℕ
  /-- Base memory address of the source variable bag. -/
  srcPtr : ℕ
  /-- Length of the source variable bag. -/
  srcLen : ℕ
  /-- Source radix index `m`. -/
  srcM : ℕ
  /-- Optional override variable index (active when `hasUpd = 1`). -/
  updVar : ℕ
  /-- Optional override value for `updVar`. -/
  updVal : ℕ
  /-- Override toggle (`1` applies `updVar ↦ updVal`, `0` leaves `ofRadix` unmodified). -/
  hasUpd : ℕ
  /-- Base memory address of the destination variable list. -/
  dstPtr : ℕ
  /-- Length of the destination variable list. -/
  dstLen : ℕ

/-- Tuple equivalence encoding `RadixProjArgs` into Word-RAM registers. -/
@[expose] def RadixProjArgs.equiv :
    RadixProjArgs ≃ (((((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ where
  toFun a :=
    ((((((((a.q, a.srcPtr), a.srcLen), a.srcM), a.updVar), a.updVal), a.hasUpd), a.dstPtr),
      a.dstLen)
  invFun := fun ((((((((q, sp), sl), sm), uv), uval), hu), dp), dl) =>
    ⟨q, sp, sl, sm, uv, uval, hu, dp, dl⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : WordEncoding RadixProjArgs := .ofEquiv RadixProjArgs.equiv

private structure RadixProjState where
  remIdx : ℕ
  acc : ℕ

private def RadixProjState.equiv : RadixProjState ≃ ℕ × ℕ where
  toFun s := (s.remIdx, s.acc)
  invFun := fun (r, a) => ⟨r, a⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding RadixProjState := .ofEquiv RadixProjState.equiv

/-- Functional assignment looked up by `radixProjProg`. -/
@[expose] def radixProjAssign (args : RadixProjArgs) (srcL : List ℕ) : ℕ → ℕ :=
  if args.hasUpd = 1 then
    Function.update (ofRadix args.q srcL args.srcM) args.updVar args.updVal
  else
    ofRadix args.q srcL args.srcM

private def radixProjStep (p : RadixProjArgs × RadixProjState) :
    Memory.Prog RadixProjState := do
  let a := p.1
  let st := p.2
  let idx := st.remIdx - 1
  let v ← Memory.read (a.dstPtr + idx)
  let looked ← lookupRadixProg ⟨a.q, a.srcPtr, a.srcLen, a.srcM, v⟩
  let val := if a.hasUpd = 1 ∧ v = a.updVar then a.updVal else looked
  pure ⟨idx, val % a.q + a.q * st.acc⟩

/-- Horner projection evaluating `toRadix` along a materialized destination variable list. -/
def radixProjProg (args : RadixProjArgs) : Memory.Prog ℕ := do
  let res ← iterate radixProjStep args args.dstLen ⟨args.dstLen, 0⟩
  pure res.acc

private theorem radixProjStep_eval (a : RadixProjArgs) (st : RadixProjState) (t : Memory.State) :
    let idx := st.remIdx - 1
    let v := t.mem (a.dstPtr + idx)
    let looked := (Memory.spec 0).clientResult t
      (lookupRadixProg ⟨a.q, a.srcPtr, a.srcLen, a.srcM, v⟩)
    let val := if a.hasUpd = 1 ∧ v = a.updVar then a.updVal else looked
    (Memory.spec 0).clientState t (radixProjStep (a, st)) = t ∧
    (Memory.spec 0).clientResult t (radixProjStep (a, st)) =
      ⟨idx, val % a.q + a.q * st.acc⟩ := by
  unfold radixProjStep
  dsimp only
  rw [clientState_bind_read, clientResult_bind_read, StateTransitionSpec.clientState_bind,
    StateTransitionSpec.clientResult_bind, lookupRadixProg_state]
  exact ⟨rfl, rfl⟩

/-- One Horner step `v % q + q * acc` stays below the next power of `q`. -/
private theorem horner_step_lt {q acc n j : ℕ} (hq : 0 < q) (hj : j < n)
    (hacc : acc < q ^ (n - (j + 1))) (v : ℕ) : v % q + q * acc < q ^ (n - j) := by
  have hmod : v % q < q := Nat.mod_lt v hq
  have hmul : q * (acc + 1) ≤ q * q ^ (n - (j + 1)) := Nat.mul_le_mul_left q hacc
  rw [show n - j = n - (j + 1) + 1 by omega, Nat.pow_succ, Nat.mul_comm (q ^ _) q]
  rw [Nat.mul_add, Nat.mul_one] at hmul
  omega

/-- `radixProjProg` is read-only and leaves memory unchanged. -/
theorem radixProjProg_state (args : RadixProjArgs) (s : Memory.State) :
    (Memory.spec 0).clientState s (radixProjProg args) = s := by
  unfold radixProjProg
  rw [StateTransitionSpec.clientState_bind]
  exact clientState_iterate_eq_of radixProjStep args
    (fun st m => (radixProjStep_eval args st m).1) args.dstLen ⟨args.dstLen, 0⟩ s

/-- The projected radix index lies strictly below `args.q ^ dstL.length`. -/
theorem radixProjProg_result_lt {args : RadixProjArgs} (hq : 0 < args.q)
    (s : Memory.State) :
    (Memory.spec 0).clientResult s (radixProjProg args) < args.q ^ args.dstLen := by
  unfold radixProjProg
  rw [StateTransitionSpec.clientResult_bind]
  suffices ∀ k st, st.acc < args.q ^ (args.dstLen - k) → k ≤ args.dstLen →
      ((Memory.spec 0).clientResult s (iterate radixProjStep args k st)).acc <
        args.q ^ args.dstLen from
    this args.dstLen ⟨args.dstLen, 0⟩
      (by simp only [Nat.sub_self, Nat.pow_zero]; exact Nat.zero_lt_one) le_rfl
  intro k
  induction k with
  | zero => exact fun st hacc _ => by rwa [Nat.sub_zero] at hacc
  | succ j ih =>
    intro st hacc hj_le
    obtain ⟨hst_ev, hres_ev⟩ := radixProjStep_eval args st s
    rw [iterate, StateTransitionSpec.clientResult_bind, hst_ev, hres_ev]
    exact ih _ (horner_step_lt hq hj_le hacc _) (Nat.le_of_succ_le hj_le)

/-- Memory validity, functional correctness, and cost bound for `radixProjProg`. -/
theorem radixProjProg_spec {w : ℕ} (args : RadixProjArgs)
    {srcL dstL : List ℕ} {s : Memory.State}
    (hsrc : HoldsIn args.srcPtr srcL s) (hsrc_len : srcL.length = args.srcLen)
    (hdst : HoldsIn args.dstPtr dstL s) (hdst_len : dstL.length = args.dstLen) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (radixProjProg args)) ∧
    (Memory.spec 0).clientState s (radixProjProg args) = s ∧
    (Memory.spec 0).clientResult s (radixProjProg args) =
      toRadix args.q dstL (radixProjAssign args srcL) ∧
    memoryCost (radixProjProg args) s ≤ args.dstLen * (args.srcLen + 1) := by
  let stepCost := args.srcLen + 1
  suffices ∀ rem (hrem : rem ≤ dstL.length),
      (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s
          (iterate radixProjStep args rem
            ⟨rem, toRadix args.q (dstL.drop rem) (radixProjAssign args srcL)⟩)) ∧
      ((Memory.spec 0).clientResult s
        (iterate radixProjStep args rem
          ⟨rem, toRadix args.q (dstL.drop rem) (radixProjAssign args srcL)⟩)).acc =
        toRadix args.q dstL (radixProjAssign args srcL) ∧
      memoryCost
        (iterate radixProjStep args rem
          ⟨rem, toRadix args.q (dstL.drop rem) (radixProjAssign args srcL)⟩) s ≤
        rem * stepCost by
    have hrun := this dstL.length le_rfl
    rw [List.drop_length, toRadix_nil, hdst_len] at hrun
    unfold radixProjProg
    refine ⟨validHistory_bind_step hrun.1 (validHistory_pure w _ _), radixProjProg_state args s,
      (StateTransitionSpec.clientResult_bind ..).trans hrun.2.1,
      by simpa only [memoryCost_bind', memoryCost_pure, Nat.add_zero] using hrun.2.2⟩
  intro rem
  induction rem with
  | zero => exact fun _ => ⟨validHistory_pure w s _, rfl, by simp [iterate, memoryCost_pure]⟩
  | succ k ih =>
    intro hk_le
    have hk_lt : k < dstL.length := hk_le
    have haddr_lt : args.dstPtr + k < s.frontier := by have := hdst.1; omega
    have hmem_v : s.mem (args.dstPtr + k) = dstL[k] := hdst.get k hk_lt
    obtain ⟨hv_lk, hst_lk, hr_lk, hc_lk⟩ :=
      lookupRadixProg_spec (w := w) ⟨args.q, args.srcPtr, args.srcLen, args.srcM, dstL[k]⟩
        hsrc hsrc_len
    dsimp only at hr_lk hc_lk
    let curAcc := toRadix args.q (dstL.drop (k + 1)) (radixProjAssign args srcL)
    obtain ⟨hst_step, hres_step⟩ := radixProjStep_eval args ⟨k + 1, curAcc⟩ s
    have hval_eq :
        (if args.hasUpd = 1 ∧ dstL[k] = args.updVar then args.updVal
         else ofRadix args.q srcL args.srcM dstL[k]) =
          radixProjAssign args srcL dstL[k] := by
      unfold radixProjAssign
      by_cases h1 : args.hasUpd = 1 <;> by_cases h2 : dstL[k] = args.updVar <;> simp [h1, h2]
    have hacc_next :
        radixProjAssign args srcL dstL[k] % args.q + args.q * curAcc =
          toRadix args.q (dstL.drop k) (radixProjAssign args srcL) := by
      rw [List.drop_eq_getElem_cons hk_lt, toRadix_cons]
    have hres_step' : (Memory.spec 0).clientResult s (radixProjStep (args, ⟨k + 1, curAcc⟩)) =
        ⟨k, toRadix args.q (dstL.drop k) (radixProjAssign args srcL)⟩ := by
      rw [hres_step]
      simp only [Nat.add_sub_cancel, hmem_v, hr_lk, hval_eq, hacc_next]
    have hv_step : (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s (radixProjStep (args, ⟨k + 1, curAcc⟩))) := by
      refine validHistory_read_bind (by simpa only [Nat.add_sub_cancel] using haddr_lt) ?_
      simpa only [Nat.add_sub_cancel, hmem_v] using
        validHistory_bind_step hv_lk (validHistory_pure w _ (⟨k, _⟩ : RadixProjState))
    have hc_step : memoryCost (radixProjStep (args, ⟨k + 1, curAcc⟩)) s ≤ stepCost := by
      unfold radixProjStep
      dsimp only
      rw [Nat.add_sub_cancel, memoryCost_bind', memoryCost_read, clientState_read,
        clientResult_read, hmem_v, memoryCost_bind', hst_lk, memoryCost_pure]
      dsimp only [stepCost]
      omega
    obtain ⟨hv_rem, hr_rem, hc_rem⟩ := ih (Nat.le_of_succ_le hk_le)
    rw [iterate]
    refine ⟨validHistory_bind_step hv_step (by rwa [hst_step, hres_step']), ?_, ?_⟩
    · rw [StateTransitionSpec.clientResult_bind, hst_step, hres_step']
      exact hr_rem
    · rw [memoryCost_bind', hst_step, hres_step', Nat.succ_mul, Nat.add_comm _ stepCost]
      exact Nat.add_le_add hc_step hc_rem

/-- Exact-basis Word-RAM realization certificate for `radixProjProg`. -/
theorem radixProjProg_realizes :
    Realizes .exact radixProjProg WordEncoding.encode WordEncoding.encode
      (fun w args _ =>
        0 < args.q ∧ Fits w 1 ∧ Fits w args.q ∧ Fits w args.srcM ∧
        Fits w (args.srcPtr + args.srcLen) ∧
        Fits w (args.dstPtr + args.dstLen) ∧
        Fits w (args.q ^ args.dstLen))
      (fun _ _ => 0) := by
  unfold radixProjProg
  realize [lookupRadixProg_realizes]
  obtain ⟨hq_pos, h1, hfit_q, hfit_srcM, hfit_src, hfit_dst, hfit_pow⟩ := h
  refine iterationSafe_of_stepInv _ _ w _
    (fun (j : ℕ) (st : RadixProjState) (_ : Memory.State) =>
      j ≤ d.dstLen ∧ st.remIdx = j ∧ st.acc < d.q ^ (d.dstLen - j))
    (fun j st m ⟨hj_le, hrem_eq, hacc_lt⟩ => ?_)
    ⟨le_rfl, rfl, by simp only [Nat.sub_self, Nat.pow_zero]; exact Nat.zero_lt_one⟩
  have hst_eta : st = ⟨j + 1, st.acc⟩ := by rw [← hrem_eq]
  rw [hst_eta]
  have hnext_lt : ∀ v, v % d.q + d.q * st.acc < d.q ^ (d.dstLen - j) :=
    horner_step_lt hq_pos hj_le hacc_lt
  have hpow_le : d.q ^ (d.dstLen - j) ≤ d.q ^ d.dstLen :=
    Nat.pow_le_pow_right hq_pos (Nat.sub_le _ _)
  have hlk_safe :
      0 < d.q ∧ Fits w 1 ∧ Fits w d.q ∧ Fits w d.srcM ∧ Fits w (d.srcPtr + d.srcLen) :=
    ⟨hq_pos, h1, hfit_q, hfit_srcM, hfit_src⟩
  have h1_le : 1 ≤ j + 1 := by omega
  have hfit_sub : Fits w (j + 1 - 1) := hfit_dst.of_le (by omega)
  have hfit_addr : Fits w (d.dstPtr + (j + 1 - 1)) := hfit_dst.of_le (by omega)
  have hq_ne : d.q ≠ 0 := by omega
  have hfit_mul : Fits w (d.q * st.acc) := by
    have h0 : d.q * st.acc < d.q ^ (d.dstLen - j) := by simpa using hnext_lt 0
    exact hfit_pow.of_le (le_of_lt (h0.trans_le hpow_le))
  have hfit_next (v : ℕ) : Fits w (v % d.q + d.q * st.acc) :=
    hfit_pow.of_le (le_of_lt ((hnext_lt v).trans_le hpow_le))
  have hfit_upd : Fits w (d.updVal % d.q + d.q * st.acc) := hfit_next d.updVal
  let lkVal := (Memory.spec 0).clientResult m
    (lookupRadixProg ⟨d.q, d.srcPtr, d.srcLen, d.srcM, m.mem (d.dstPtr + (j + 1 - 1))⟩)
  have hfit_lk : Fits w (lkVal % d.q + d.q * st.acc) := hfit_next lkVal
  obtain ⟨_, hres_ev⟩ := radixProjStep_eval d ⟨j + 1, st.acc⟩ m
  refine ⟨?_, Nat.le_of_succ_le hj_le, ?_, ?_⟩
  · dsimp only [radixProjStep]
    repeat (
      first
      | split
      | exact hlk_safe
      | assumption
      | refine And.intro ?_ ?_)
  · rw [hres_ev]; exact Nat.add_sub_cancel j 1
  · rw [hres_ev]; exact hnext_lt _

end Cslib.Algorithms.WordRAM.TreeDecomposition
