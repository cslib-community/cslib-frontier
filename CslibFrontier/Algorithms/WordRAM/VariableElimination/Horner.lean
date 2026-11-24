/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.VariableElimination.Memory
public import CslibFrontier.Algorithms.WordRAM.VariableElimination.Radix
import CslibFrontier.Foundations.Data.List.FoldMax
import CslibFrontier.Tactic.Realize
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.List

/-!
# Factor Entry Capacity (`capFactor`, `stateCap`) and Horner Scope Evaluation

Multiplicative capacity bounds (`capFactor` and `stateCap`) bounding intermediate table values and
bucket products, paired with `evalScopeIdx` implementing Horner mixed-radix index evaluation.

## Main definitions

* `Cslib.Algorithms.WordRAM.VariableElimination.capFactor`: per-factor entry ceiling `≥ 1`.
* `Cslib.Algorithms.WordRAM.VariableElimination.stateCap`: product capacity across live factors.
* `Cslib.Algorithms.WordRAM.VariableElimination.evalScopeIdx`: Horner radix-index evaluator.
-/

public section

namespace Cslib.Algorithms.WordRAM.VariableElimination

open Cslib.Logic.PL Cslib.Logic.PL.CSP
open Cslib.Algorithms.Lean.CSP
open Cslib.DataStructure
open Cslib.WordRAM
open Cslib.WordRAM.Realization

/-! ### Multiplicative factor capacity and Horner scope evaluation -/

/-- Multiplicative upper bound `max 1 (maxEntry f)` on entries of factor `f`. -/
@[expose] def capFactor (f : FactorTable ℕ ℕ) : ℕ :=
  max 1 (f.entries.toList.foldl max 0)

theorem one_le_capFactor (f : FactorTable ℕ ℕ) : 1 ≤ capFactor f :=
  le_max_left 1 _

private theorem mem_entries_le_capFactor {f : FactorTable ℕ ℕ} {v : ℕ}
    (hv : v ∈ f.entries.toList) : v ≤ capFactor f :=
  (List.mem_le_foldl_max hv).trans (le_max_right 1 _)

private theorem evalAt_le_capFactor (d : ℕ) (f : FactorTable ℕ ℕ) (σ : ℕ → ℕ) :
    f.evalAt d σ ≤ capFactor f := by
  rw [FactorTable.evalAt, Array.getD]
  split_ifs with hlt
  · exact mem_entries_le_capFactor (Array.getElem_mem_toList hlt)
  · exact Nat.zero_le _

theorem holdsFactor_read_entry_le {descAddr : ℕ} {f : FactorTable ℕ ℕ} {s : Memory.State}
    (hf : HoldsFactor descAddr f s) (fIdx : ℕ) :
    (if fIdx < s.mem (descAddr + 3) then s.mem (s.mem (descAddr + 2) + fIdx) else 0) ≤
      capFactor f := by
  obtain ⟨_, _, hel, _, hent⟩ := hf
  rw [hel]
  split_ifs with hlt
  · have hlt' : fIdx < f.entries.toList.length := by simpa using hlt
    rw [hent.2.get fIdx hlt']
    exact mem_entries_le_capFactor (List.getElem_mem hlt')
  · exact Nat.zero_le _

private theorem horner_step_bounds {dom scopeLen j acc pow valV : ℕ}
    (hdom : 0 < dom) (hval : valV < dom) (hacc : acc < pow)
    (hpow : pow * dom ^ (j + 1) = dom ^ scopeLen) :
    acc + valV * pow < pow * dom ∧
    (pow * dom) * dom ^ j = dom ^ scopeLen ∧
    pow * dom ≤ dom ^ scopeLen := by
  have hp1 : (1 + valV) * pow ≤ dom * pow := Nat.mul_le_mul_right pow (by omega)
  have hlt : acc + valV * pow < pow * dom := by
    calc acc + valV * pow < pow + valV * pow := Nat.add_lt_add_right hacc _
      _ = (1 + valV) * pow := by ring
      _ ≤ dom * pow := hp1
      _ = pow * dom := Nat.mul_comm dom pow
  have heq : (pow * dom) * dom ^ j = dom ^ scopeLen := by
    calc (pow * dom) * dom ^ j = pow * (dom * dom ^ j) := Nat.mul_assoc pow dom _
      _ = pow * dom ^ (j + 1) := by rw [pow_succ']
      _ = dom ^ scopeLen := hpow
  have hle : pow * dom ≤ dom ^ scopeLen := by
    have h1 : 1 ≤ dom ^ j := Nat.one_le_pow j dom hdom
    calc pow * dom ≤ (pow * dom) * dom ^ j := Nat.le_mul_of_pos_right _ h1
      _ = dom ^ scopeLen := heq
  exact ⟨hlt, heq, hle⟩

/-- Arguments for evaluating a factor's radix index via Horner's rule. -/
structure EvalScopeArgs where
  /-- Field `dom` of `EvalScopeArgs`. -/
  dom : ℕ
  /-- Field `x` of `EvalScopeArgs`. -/
  x : ℕ
  /-- Field `a` of `EvalScopeArgs`. -/
  a : ℕ
  /-- Field `outPtr` of `EvalScopeArgs`. -/
  outPtr : ℕ
  /-- Field `outLen` of `EvalScopeArgs`. -/
  outLen : ℕ
  /-- Field `idx` of `EvalScopeArgs`. -/
  idx : ℕ
  /-- Field `scopePtr` of `EvalScopeArgs`. -/
  scopePtr : ℕ
  /-- Field `scopeLen` of `EvalScopeArgs`. -/
  scopeLen : ℕ

/-- Product equivalence encoding `EvalScopeArgs` as words. -/
@[expose] def EvalScopeArgs.equiv :
    EvalScopeArgs ≃ ((((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ where
  toFun s := (((((((s.dom, s.x), s.a), s.outPtr), s.outLen), s.idx), s.scopePtr), s.scopeLen)
  invFun := fun (((((((dom, x), a), outPtr), outLen), idx), scopePtr), scopeLen) =>
    ⟨dom, x, a, outPtr, outLen, idx, scopePtr, scopeLen⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : WordEncoding EvalScopeArgs := .ofEquiv EvalScopeArgs.equiv

/-- Read-only environment record forwarded into Horner scope-index iteration. -/
structure EvalScopeEnv where
  /-- Field `dom` of `EvalScopeEnv`. -/
  dom : ℕ
  /-- Field `x` of `EvalScopeEnv`. -/
  x : ℕ
  /-- Field `a` of `EvalScopeEnv`. -/
  a : ℕ
  /-- Field `outPtr` of `EvalScopeEnv`. -/
  outPtr : ℕ
  /-- Field `outLen` of `EvalScopeEnv`. -/
  outLen : ℕ
  /-- Field `idx` of `EvalScopeEnv`. -/
  idx : ℕ

/-- Product equivalence encoding `EvalScopeEnv` as words. -/
@[expose] def EvalScopeEnv.equiv : EvalScopeEnv ≃ ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ where
  toFun e := (((((e.dom, e.x), e.a), e.outPtr), e.outLen), e.idx)
  invFun := fun (((((dom, x), a), outPtr), outLen), idx) => ⟨dom, x, a, outPtr, outLen, idx⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : WordEncoding EvalScopeEnv := .ofEquiv EvalScopeEnv.equiv

private structure EvalScopeState where
  cur : ℕ
  acc : ℕ
  pow : ℕ

private def EvalScopeState.equiv : EvalScopeState ≃ (ℕ × ℕ) × ℕ where
  toFun s := ((s.cur, s.acc), s.pow)
  invFun := fun ((cur, acc), pow) => ⟨cur, acc, pow⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding EvalScopeState := .ofEquiv EvalScopeState.equiv

private def evalScopeStep (p : EvalScopeEnv × EvalScopeState) : Memory.Prog EvalScopeState :=
  Memory.read p.2.cur >>= fun v =>
    (if v = p.1.x then pure p.1.a
      else lookupAssign ⟨p.1.dom, v, p.1.outPtr, p.1.outLen, p.1.idx⟩) >>= fun valV =>
      pure ⟨p.2.cur + 1, p.2.acc + valV * p.2.pow, p.2.pow * p.1.dom⟩

/-- Compute the flat table index of `f.scope` under an assignment via Horner. -/
def evalScopeIdx (args : EvalScopeArgs) : Memory.Prog ℕ := do
  let res ← iterate evalScopeStep
    ⟨args.dom, args.x, args.a, args.outPtr, args.outLen, args.idx⟩
    args.scopeLen ⟨args.scopePtr, 0, 1⟩
  pure res.acc

private theorem evalScopeStep_state (env : EvalScopeEnv) (st : EvalScopeState) (s : Memory.State) :
    (Memory.spec 0).clientState s (evalScopeStep (env, st)) = s := by
  unfold evalScopeStep
  rw [StateTransitionSpec.clientState_bind]
  have h1 : (Memory.spec 0).clientState s (Memory.read st.cur) = s := rfl
  have h2 : (Memory.spec 0).clientResult s (Memory.read st.cur) = s.mem st.cur := rfl
  rw [h1, h2, StateTransitionSpec.clientState_bind]
  split_ifs
  · rfl
  · rw [lookupAssign_state]; rfl

theorem evalScopeIdx_state (args : EvalScopeArgs) (s : Memory.State) :
    (Memory.spec 0).clientState s (evalScopeIdx args) = s := by
  unfold evalScopeIdx
  rw [StateTransitionSpec.clientState_bind]
  exact clientState_iterate_eq_of evalScopeStep _ (evalScopeStep_state _) args.scopeLen _ s

theorem evalScopeIdx_cost (args : EvalScopeArgs) (s : Memory.State) :
    memoryCost (evalScopeIdx args) s ≤ args.scopeLen * (args.outLen + 1) := by
  unfold evalScopeIdx
  rw [memoryCost_bind', memoryCost_pure, Nat.add_zero, Nat.mul_comm]
  refine memoryCost_iterate_le_of evalScopeStep (args.outLen + 1) _ (fun st t => ?_)
    args.scopeLen ⟨args.scopePtr, 0, 1⟩ s
  unfold evalScopeStep
  dsimp only
  have hr : (Memory.spec 0).clientState t (Memory.read st.cur) = t := rfl
  have hres : (Memory.spec 0).clientResult t (Memory.read st.cur) = t.mem st.cur := rfl
  rw [memoryCost_bind', memoryCost_read, hr, hres, memoryCost_bind']
  split_ifs
  · rw [memoryCost_pure, memoryCost_pure]; omega
  · rw [lookupAssign_state, memoryCost_pure]
    have hlk := lookupAssign_cost ⟨args.dom, t.mem st.cur, args.outPtr, args.outLen, args.idx⟩ t
    dsimp only at hlk
    omega

theorem evalScopeIdx_valid {w : ℕ} (args : EvalScopeArgs) {s : Memory.State}
    (hout : args.outPtr + args.outLen ≤ s.frontier)
    (hsc : args.scopePtr + args.scopeLen ≤ s.frontier) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (evalScopeIdx args)) := by
  unfold evalScopeIdx
  refine validHistory_bind_step ?_ (validHistory_pure w _ _)
  let env : EvalScopeEnv := ⟨args.dom, args.x, args.a, args.outPtr, args.outLen, args.idx⟩
  suffices ∀ len cur, cur + len ≤ s.frontier → ∀ acc pow,
      (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s (iterate evalScopeStep env len ⟨cur, acc, pow⟩)) from
    this args.scopeLen args.scopePtr hsc 0 1
  intro len
  induction len with
  | zero => intro _ _ _ _; exact validHistory_pure w s _
  | succ len ih =>
    intro cur hcur acc pow
    have hlt : cur < s.frontier := by omega
    have hstep : (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s (evalScopeStep (env, ⟨cur, acc, pow⟩))) := by
      unfold evalScopeStep
      refine validHistory_read_bind hlt ?_
      refine validHistory_bind_step ?_ (validHistory_pure w _ _)
      split_ifs
      · exact validHistory_pure w s _
      · exact lookupAssign_valid _ hout
    have hcur_next : ((Memory.spec 0).clientResult s
        (evalScopeStep (env, ⟨cur, acc, pow⟩))).cur = cur + 1 := by
      unfold evalScopeStep
      rw [StateTransitionSpec.clientResult_bind]
      have h1 : (Memory.spec 0).clientState s (Memory.read cur) = s := rfl
      have h2 : (Memory.spec 0).clientResult s (Memory.read cur) = s.mem cur := rfl
      rw [h1, h2, StateTransitionSpec.clientResult_bind]
      split_ifs <;> rfl
    change (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s
        (evalScopeStep (env, ⟨cur, acc, pow⟩) >>= iterate evalScopeStep env len))
    refine validHistory_bind_step hstep ?_
    rw [evalScopeStep_state]
    let r := (Memory.spec 0).clientResult s (evalScopeStep (env, ⟨cur, acc, pow⟩))
    exact ih r.cur (by rw [hcur_next]; omega) r.acc r.pow

theorem evalScopeIdx_result {args : EvalScopeArgs} {outScope fScope : List ℕ}
    {s : Memory.State}
    (hout : Block.HoldsList args.outPtr outScope s.mem) (hout_len : outScope.length = args.outLen)
    (hsc : Block.HoldsList args.scopePtr fScope s.mem) (hsc_len : fScope.length = args.scopeLen) :
    (Memory.spec 0).clientResult s (evalScopeIdx args) =
      Nat.ofDigits args.dom (fScope.map fun v =>
        if v = args.x then args.a
        else assignScope outScope (lsbDecode args.dom outScope.length args.idx) v) := by
  unfold evalScopeIdx
  rw [StateTransitionSpec.clientResult_bind, ← hsc_len]
  have hpure (t : Memory.State) (v : ℕ) : (Memory.spec 0).clientResult t (pure v) = v := rfl
  rw [hpure]
  let env : EvalScopeEnv := ⟨args.dom, args.x, args.a, args.outPtr, args.outLen, args.idx⟩
  let σ : ℕ → ℕ := fun v =>
    if v = args.x then args.a
    else assignScope outScope (lsbDecode args.dom outScope.length args.idx) v
  suffices ∀ (ys : List ℕ) (cur acc pow : ℕ), Block.HoldsList cur ys s.mem →
      ((Memory.spec 0).clientResult s (iterate evalScopeStep env ys.length ⟨cur, acc, pow⟩)).acc =
      acc + pow * Nat.ofDigits args.dom (ys.map σ) by
    simpa [env, σ] using this fScope args.scopePtr 0 1 hsc
  intro ys
  induction ys with
  | nil => intro cur acc pow _; change acc = acc + pow * 0; simp
  | cons v rest ih =>
    intro cur acc pow hcur
    obtain ⟨hhead, htail⟩ := Block.holdsList_cons_iff.mp hcur
    change ((Memory.spec 0).clientResult s
      (evalScopeStep (env, ⟨cur, acc, pow⟩) >>= iterate evalScopeStep env rest.length)).acc = _
    rw [StateTransitionSpec.clientResult_bind, evalScopeStep_state]
    have hstep_res : (Memory.spec 0).clientResult s (evalScopeStep (env, ⟨cur, acc, pow⟩)) =
        ⟨cur + 1, acc + σ v * pow, pow * args.dom⟩ := by
      unfold evalScopeStep
      rw [StateTransitionSpec.clientResult_bind]
      have h1 : (Memory.spec 0).clientState s (Memory.read cur) = s := rfl
      have h2 : (Memory.spec 0).clientResult s (Memory.read cur) = v := hhead
      rw [h1, h2, StateTransitionSpec.clientResult_bind]
      by_cases hvx : v = args.x
      · simp [env, σ, hvx]; rfl
      · simp only [env, σ, hvx, ↓reduceIte]
        rw [lookupAssign_state, lookupAssign_result hout hout_len]
        rfl
    rw [hstep_res, ih (cur + 1) _ _ htail, List.map_cons, Nat.ofDigits_cons]
    ring

theorem evalScopeIdx_realizes :
    Realizes .exact evalScopeIdx WordEncoding.encode WordEncoding.encode
      (fun w args _ => 0 < args.dom ∧ args.a < args.dom ∧ Fits w 1 ∧
        Fits w (args.outPtr + args.outLen) ∧ Fits w (args.scopePtr + args.scopeLen) ∧
        Fits w (args.dom ^ args.scopeLen))
      (fun _ _ => 0) := by
  unfold evalScopeIdx
  realize [lookupAssign_realizes]
  · exact h.2.2.1
  · refine iterationSafe_of_stepInv _ _ w d
      (fun j st _ => st.cur + j = d.scopePtr + d.scopeLen ∧ st.acc < st.pow ∧
        st.pow * d.dom ^ j = d.dom ^ d.scopeLen)
      (fun j st t ⟨hcur, hacc, hpow⟩ => ?_)
      ⟨rfl, Nat.zero_lt_one, Nat.one_mul _⟩
    dsimp only
    obtain ⟨hdom, ha, h1, hout, hsc, hpow_fit⟩ := h
    let lkArgs : LookupArgs := ⟨d.dom, t.mem st.cur, d.outPtr, d.outLen, d.idx⟩
    have hlk_lt : (Memory.spec 0).clientResult t (lookupAssign lkArgs) < d.dom :=
      lookupAssign_lt hdom t
    have hb_a := horner_step_bounds hdom ha hacc hpow
    have hb_lk := horner_step_bounds hdom hlk_lt hacc hpow
    refine ⟨?_, ?_⟩
    · split_ifs
      · exact ⟨trivial, hsc.of_le (by omega), hpow_fit.of_le (hb_a.1.le.trans hb_a.2.2),
          hpow_fit.of_le hb_a.2.2⟩
      · exact ⟨⟨hdom, h1, hout⟩, hsc.of_le (by omega),
          hpow_fit.of_le (hb_lk.1.le.trans hb_lk.2.2), hpow_fit.of_le hb_lk.2.2⟩
    · unfold evalScopeStep
      rw [StateTransitionSpec.clientResult_bind]
      have hr1 : (Memory.spec 0).clientState t (Memory.read st.cur) = t := rfl
      have hr2 : (Memory.spec 0).clientResult t (Memory.read st.cur) = t.mem st.cur := rfl
      rw [hr1, hr2, StateTransitionSpec.clientResult_bind]
      split_ifs
      · change (st.cur + 1) + j = d.scopePtr + d.scopeLen ∧ st.acc + d.a * st.pow < st.pow * d.dom ∧
          (st.pow * d.dom) * d.dom ^ j = d.dom ^ d.scopeLen
        exact ⟨by omega, hb_a.1, hb_a.2.1⟩
      · rw [lookupAssign_state]
        change (st.cur + 1) + j = d.scopePtr + d.scopeLen ∧
          st.acc + (Memory.spec 0).clientResult t (lookupAssign lkArgs) * st.pow < st.pow * d.dom ∧
          (st.pow * d.dom) * d.dom ^ j = d.dom ^ d.scopeLen
        exact ⟨by omega, hb_lk.1, hb_lk.2.1⟩

/-! ### Multiplicative state-capacity budget (`stateCap`), `elimVarProg`, and `elimOrderLoop` -/

private theorem capFactor_elimBucketTable (d x : ℕ) (bucket : List (FactorTable ℕ ℕ)) :
    capFactor (elimBucketTable d x bucket) ≤ max 1 d * (bucket.map capFactor).prod := by
  rw [capFactor]
  refine max_le (Nat.mul_le_mul (le_max_left 1 d)
    (List.one_le_prod_of_one_le (by simp [one_le_capFactor]))) ?_
  refine List.foldl_max_le (Nat.zero_le _) fun v hv => ?_
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv
  rw [Array.getElem_toList]
  simp only [elimBucketTable, Array.getElem_ofFn]
  have hsum : (∑ a : Fin d,
      (bucket.map fun f => f.evalAt d fun u =>
        if u = x then a.1
        else assignScope (bucketOutScope x bucket)
          (lsbDecode d (bucketOutScope x bucket).length i) u).prod) ≤
      ∑ _ : Fin d, (bucket.map capFactor).prod := by
    refine Finset.sum_le_sum fun a _ => ?_
    exact List.prod_map_le_prod_map₀ _ _ (fun _ _ => Nat.zero_le _)
      fun f _ => evalAt_le_capFactor d f _
  calc _ ≤ ∑ _ : Fin d, (bucket.map capFactor).prod := hsum
    _ = d * (bucket.map capFactor).prod := by simp
    _ ≤ max 1 d * (bucket.map capFactor).prod := Nat.mul_le_mul_right _ (le_max_right 1 d)

/-- Product of `capFactor` over all live factors in `ElimState`. -/
@[expose] def stateCap (s : ElimState ℕ ℕ) : ℕ :=
  max 1 s.scalar * (s.live.map capFactor).prod

private theorem max_one_mul_le (a d : ℕ) : max 1 (a * d) ≤ max 1 d * max 1 a := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp
  · rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp
    · rw [max_eq_right (Nat.mul_pos ha hd), max_eq_right hd, max_eq_right ha, Nat.mul_comm]

theorem bucket_prod_le_stateCap (x : ℕ) (s : ElimState ℕ ℕ) :
    (((s.live.filter fun f => decide (x ∈ f.scope)).map capFactor).prod) ≤ stateCap s := by
  have hsplit :=
    ((List.filter_append_perm (fun f => decide (x ∈ f.scope)) s.live).map capFactor).prod_eq
  rw [List.map_append, List.prod_append] at hsplit
  have h1 : 1 ≤ ((s.live.filter fun f => !decide (x ∈ f.scope)).map capFactor).prod :=
    List.one_le_prod_of_one_le fun _ hn => by
      rcases List.mem_map.mp hn with ⟨f, _, rfl⟩
      exact one_le_capFactor f
  have hle_live : ((s.live.filter fun f => decide (x ∈ f.scope)).map capFactor).prod ≤
      (s.live.map capFactor).prod := by
    calc _ ≤ _ * ((s.live.filter fun f => !decide (x ∈ f.scope)).map capFactor).prod :=
          Nat.le_mul_of_pos_right _ h1
      _ = (s.live.map capFactor).prod := hsplit
  exact hle_live.trans (Nat.le_mul_of_pos_left _ (le_max_left 1 s.scalar))

theorem stateCap_elimVar_le (d x : ℕ) (s : ElimState ℕ ℕ) :
    stateCap (elimVar d x s) ≤ max 1 d * stateCap s := by
  by_cases hx : x ∈ s.remaining
  · simp only [elimVar, hx, ↓reduceIte]
    split_ifs with hb
    · unfold stateCap
      dsimp only
      calc max 1 (s.scalar * d) * (s.live.map capFactor).prod
          ≤ (max 1 d * max 1 s.scalar) * (s.live.map capFactor).prod :=
            Nat.mul_le_mul_right _ (max_one_mul_le s.scalar d)
        _ = max 1 d * (max 1 s.scalar * (s.live.map capFactor).prod) := Nat.mul_assoc _ _ _
    · unfold stateCap
      dsimp only
      simp only [List.map_cons, List.prod_cons]
      have hcap := capFactor_elimBucketTable d x (s.live.filter fun f => decide (x ∈ f.scope))
      have hrest_eq : (s.live.filter fun f => decide (x ∉ f.scope)) =
          (s.live.filter fun f => !decide (x ∈ f.scope)) := by
        refine List.filter_congr fun f _ => ?_
        simp
      rw [hrest_eq]
      have hsplit :=
        ((List.filter_append_perm (fun f => decide (x ∈ f.scope)) s.live).map capFactor).prod_eq
      rw [List.map_append, List.prod_append] at hsplit
      calc max 1 s.scalar *
            (capFactor (elimBucketTable d x (s.live.filter fun f => decide (x ∈ f.scope))) *
              ((s.live.filter fun f => !decide (x ∈ f.scope)).map capFactor).prod)
          ≤ max 1 s.scalar *
              ((max 1 d * ((s.live.filter fun f => decide (x ∈ f.scope)).map capFactor).prod) *
                ((s.live.filter fun f => !decide (x ∈ f.scope)).map capFactor).prod) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hcap)
        _ = max 1 d * (max 1 s.scalar *
              (((s.live.filter fun f => decide (x ∈ f.scope)).map capFactor).prod *
                ((s.live.filter fun f => !decide (x ∈ f.scope)).map capFactor).prod)) := by ring
        _ = max 1 d * (max 1 s.scalar * (s.live.map capFactor).prod) := by rw [hsplit]
  · simp only [elimVar, hx, ↓reduceIte]
    exact Nat.le_mul_of_pos_left _ (le_max_left 1 d)

end Cslib.Algorithms.WordRAM.VariableElimination
