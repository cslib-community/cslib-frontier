/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.TreeDecomposition.CSP.Model
public import CslibFrontier.Algorithms.WordRAM.TreeDecomposition.Scan
import CslibFrontier.Algorithms.WordRAM.TreeDecomposition.CSP.BagOps
import CslibFrontier.Algorithms.WordRAM.TreeDecomposition.CSP.Radix
import CslibFrontier.Tactic.Realize

/-!
# Word-RAM constraint-table scans for `leaf` and `introduce` nodes

This module certifies the two read-only constraint scanning programs operating over serialized
`ConstraintTable.encode` lists:

* `checkLeafConstraintsProg`: checks all zero-arity constraints at a `leaf` node.
* `checkIntroConstraintsProg`: checks all constraints containing the newly introduced variable `v`
  whose scope is contained in the current bag, indexing their truth tables via `radixProjProg`.

## Main definitions

* `Cslib.Algorithms.WordRAM.TreeDecomposition.IntroConsArgs`: register bundle for
  `checkIntroConstraintsProg`.
* `Cslib.Algorithms.WordRAM.TreeDecomposition.checkLeafConstraintsProg`: leaf-node constraint scan.
* `Cslib.Algorithms.WordRAM.TreeDecomposition.checkIntroConstraintsProg`: introduce-node constraint
  scan.

## Main results

* `Cslib.Algorithms.WordRAM.TreeDecomposition.checkLeafConstraintsProg_spec`,
  `Cslib.Algorithms.WordRAM.TreeDecomposition.checkLeafConstraintsProg_realizes`: correctness and
  realization of `checkLeafConstraintsProg`.
* `Cslib.Algorithms.WordRAM.TreeDecomposition.checkIntroConstraintsProg_spec`,
  `Cslib.Algorithms.WordRAM.TreeDecomposition.checkIntroConstraintsProg_realizes`: correctness and
  realization of `checkIntroConstraintsProg`.
-/

public section

namespace Cslib.Algorithms.WordRAM.TreeDecomposition

open Cslib.Algorithms.Lean.TreeDecomposition
open Cslib.DataStructure
open Cslib.WordRAM
open Cslib.WordRAM.Realization

/-! ### Constraint-list scans for `leaf` and `introduce` nodes -/

private def checkLeafStep (env : Unit × SubScanState) : Memory.Prog SubScanState := do
  let st := env.2
  let scopeLen ← Memory.read st.cur
  let tblLen ← Memory.read (st.cur + 1)
  let t0 ← Memory.read (st.cur + 2 + scopeLen)
  let ok' := if scopeLen = 0 then (if t0 = 1 then st.found else 0) else st.found
  pure ⟨st.cur + 2 + scopeLen + tblLen, ok'⟩

/-- Check all serialized empty-scope constraints (`leaf` node), returning `1` iff satisfied. -/
def checkLeafConstraintsProg (args : ℕ × ℕ) : Memory.Prog ℕ := do
  let res ← iterate checkLeafStep () args.2 ⟨args.1, 1⟩
  pure res.found

private theorem checkLeafConstraintsProg_state (args : ℕ × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (checkLeafConstraintsProg args) = s := by
  unfold checkLeafConstraintsProg
  rw [StateTransitionSpec.clientState_bind]
  exact clientState_iterate_eq_of checkLeafStep () (fun _ _ => rfl) args.2 ⟨args.1, 1⟩ s

/-- Memory validity, read-only behavior, and cost bound for `checkLeafConstraintsProg`. -/
theorem checkLeafConstraintsProg_spec {w q : ℕ} (hq : 0 < q) (args : ℕ × ℕ)
    {cs : List (ConstraintTable q)} {s : Memory.State}
    (hcs : HoldsIn args.1 (cs.flatMap ConstraintTable.encode) s)
    (hlen : cs.length = args.2) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (checkLeafConstraintsProg args)) ∧
    (Memory.spec 0).clientState s (checkLeafConstraintsProg args) = s ∧
    (Memory.spec 0).clientResult s (checkLeafConstraintsProg args) =
      (if cs.all fun ct => !decide (ct.scope = []) || ct.eval (fun _ => 0) then 1 else 0) ∧
    memoryCost (checkLeafConstraintsProg args) s ≤ 3 * args.2 := by
  suffices ∀ (rem : List (ConstraintTable q)) cur ok,
      HoldsIn cur (rem.flatMap ConstraintTable.encode) s →
      (ok = 0 ∨ ok = 1) →
      (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s (iterate checkLeafStep () rem.length ⟨cur, ok⟩)) ∧
      ((Memory.spec 0).clientResult s
        (iterate checkLeafStep () rem.length ⟨cur, ok⟩)).found =
        (if ok = 1 ∧
            (rem.all fun ct => !decide (ct.scope = []) || ct.eval (fun _ => 0)) = true
          then 1 else 0) ∧
      memoryCost (iterate checkLeafStep () rem.length ⟨cur, ok⟩) s ≤ 3 * rem.length by
    have hrun := this cs args.1 1 hcs (.inr rfl)
    rw [hlen] at hrun
    refine ⟨?_, checkLeafConstraintsProg_state args s, ?_, ?_⟩
    · unfold checkLeafConstraintsProg
      exact validHistory_bind_step hrun.1 (validHistory_pure w _ _)
    · unfold checkLeafConstraintsProg
      rw [StateTransitionSpec.clientResult_bind, hrun.2.1]
      cases cs.all fun ct => !decide (ct.scope = []) || ct.eval (fun _ => 0) <;> rfl
    · unfold checkLeafConstraintsProg
      rw [memoryCost_bind', memoryCost_pure, Nat.add_zero]
      exact hrun.2.2
  intro rem
  induction rem with
  | nil =>
    intro cur ok _ hok
    have h0 : iterate checkLeafStep () 0 ⟨cur, ok⟩ = pure ⟨cur, ok⟩ := rfl
    rw [List.length_nil, h0]
    refine ⟨validHistory_pure w s _, ?_, by simp [memoryCost_pure]⟩
    rcases hok with rfl | rfl <;> rfl
  | cons ct rest ih =>
    intro cur ok hcur hok
    rw [List.flatMap_cons, ConstraintTable.encode] at hcur
    have hcons_split :
        ([ct.scope.length, ct.table.length] ++ ct.scope ++ ct.table) ++
          rest.flatMap ConstraintTable.encode =
        ct.scope.length :: ct.table.length ::
          (ct.scope ++ (ct.table ++ rest.flatMap ConstraintTable.encode)) := by
      simp [List.append_assoc]
    rw [hcons_split, HoldsIn.cons_iff] at hcur
    obtain ⟨_, hm_sl, hcur1⟩ := hcur
    rw [HoldsIn.cons_iff] at hcur1
    obtain ⟨_, hm_tl, hcur2⟩ := hcur1
    rw [HoldsIn.append_iff] at hcur2
    obtain ⟨_, hcur3⟩ := hcur2
    rw [HoldsIn.append_iff] at hcur3
    obtain ⟨htbl_h, hrest_h⟩ := hcur3
    have htl_pos : 0 < ct.table.length := by
      rw [ct.table_len]
      exact Nat.one_le_pow _ _ hq
    have h0_lt : cur < s.frontier := by have := htbl_h.1; omega
    have h1_lt : cur + 1 < s.frontier := by have := htbl_h.1; omega
    have ht0_lt : cur + 2 + ct.scope.length < s.frontier := by have := htbl_h.1; omega
    have hm_t0 : s.mem (cur + 2 + ct.scope.length) = ct.table[0] := by
      have haddr : cur + 2 + ct.scope.length = cur + 1 + 1 + ct.scope.length + 0 := by omega
      rw [haddr]
      exact htbl_h.get 0 htl_pos
    let ok' := if ct.scope.length = 0 then (if ct.table[0] = 1 then ok else 0) else ok
    have hok' : ok' = 0 ∨ ok' = 1 := by
      dsimp only [ok']
      split_ifs <;> first | exact hok | exact .inl rfl
    have hstep_res : (Memory.spec 0).clientResult s (checkLeafStep ((), ⟨cur, ok⟩)) =
        ⟨cur + 2 + ct.scope.length + ct.table.length, ok'⟩ := by
      unfold checkLeafStep
      dsimp only
      have hr_s (x : ℕ) : (Memory.spec 0).clientState s (Memory.read x) = s := rfl
      have hr_r (x : ℕ) : (Memory.spec 0).clientResult s (Memory.read x) = s.mem x := rfl
      rw [StateTransitionSpec.clientResult_bind, hr_s, hr_r, hm_sl,
        StateTransitionSpec.clientResult_bind, hr_s, hr_r, hm_tl,
        StateTransitionSpec.clientResult_bind, hr_s, hr_r, hm_t0]
      rfl
    have hv_step : (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s (checkLeafStep ((), ⟨cur, ok⟩))) := by
      unfold checkLeafStep
      dsimp only
      refine validHistory_read_bind h0_lt ?_
      rw [hm_sl]
      refine validHistory_read_bind h1_lt ?_
      rw [hm_tl]
      exact validHistory_read_bind ht0_lt (validHistory_pure w s _)
    have hc_step : memoryCost (checkLeafStep ((), ⟨cur, ok⟩)) s ≤ 3 := by
      have hr_s (x : ℕ) : (Memory.spec 0).clientState s (Memory.read x) = s := rfl
      have hr_r (x : ℕ) : (Memory.spec 0).clientResult s (Memory.read x) = s.mem x := rfl
      unfold checkLeafStep
      dsimp only
      rw [memoryCost_bind', memoryCost_read, hr_s, hr_r, hm_sl,
        memoryCost_bind', memoryCost_read, hr_s, hr_r, hm_tl,
        memoryCost_bind', memoryCost_read, hr_s, hr_r, memoryCost_pure]
    have hrest_ptr : cur + 1 + 1 + ct.scope.length + ct.table.length =
        cur + 2 + ct.scope.length + ct.table.length := by omega
    rw [hrest_ptr] at hrest_h
    obtain ⟨hv_rem, hr_rem, hc_rem⟩ := ih _ ok' hrest_h hok'
    simp only [List.length_cons, List.all_cons]
    have hiter_eq : iterate checkLeafStep () (rest.length + 1) ⟨cur, ok⟩ =
        (checkLeafStep ((), ⟨cur, ok⟩) >>= iterate checkLeafStep () rest.length) := rfl
    rw [hiter_eq]
    refine ⟨validHistory_bind_step hv_step (by rwa [hstep_res]), ?_, ?_⟩
    · rw [StateTransitionSpec.clientResult_bind, hstep_res]
      change ((Memory.spec 0).clientResult s
        (iterate checkLeafStep () rest.length _)).found = _
      rw [hr_rem]
      refine if_congr ?_ rfl rfl
      rw [Bool.and_eq_true]
      have hct_pred :
          (!decide (ct.scope = []) || ct.eval (fun _ => 0)) =
            if ct.scope.length = 0 then decide (ct.table[0] = 1) else true := by
        by_cases hsl : ct.scope.length = 0
        · have hnil : ct.scope = [] := List.eq_nil_of_length_eq_zero hsl
          rw [ite_eq_left hsl]
          refine Bool.eq_iff_iff.2 ?_
          simp [hnil, ConstraintTable.eval, toRadix_nil, List.getD_eq_getElem?_getD,
            List.getElem?_eq_getElem htl_pos]
        · have hnnil : ct.scope ≠ [] := fun h => hsl (by simp [h])
          simp [hsl, hnnil]
      rw [hct_pred]
      dsimp only [ok']
      rcases hok with rfl | rfl
      · split_ifs <;> simp
      · by_cases hsl : ct.scope.length = 0
        · by_cases ht1 : ct.table[0] = 1 <;> simp [hsl, ht1]
        · simp [hsl]
    · rw [memoryCost_bind']
      change memoryCost (checkLeafStep ((), ⟨cur, ok⟩)) s +
          memoryCost (iterate checkLeafStep () rest.length _) s ≤ _
      rw [hstep_res]
      omega

/-- Exact-basis Word-RAM realization certificate for `checkLeafConstraintsProg`. -/
theorem checkLeafConstraintsProg_realizes :
    Realizes .exact checkLeafConstraintsProg WordEncoding.encode WordEncoding.encode
      (fun w args s =>
        Fits w 2 ∧
        ∃ (q : ℕ) (cs : List (ConstraintTable q)),
          0 < q ∧
          cs.length = args.2 ∧
          HoldsIn args.1 (cs.flatMap ConstraintTable.encode) s ∧
          Fits w (args.1 + (cs.flatMap ConstraintTable.encode).length))
      (fun _ _ => 0) := by
  unfold checkLeafConstraintsProg
  realize
  · exact h.1.of_le (by decide)
  · obtain ⟨h2, q, cs, hq, hcs_len, hcs_h, hfit_end⟩ := h
    have h1 : Fits w 1 := h2.of_le (by decide)
    let endPtr := d.1 + (cs.flatMap ConstraintTable.encode).length
    refine iterationSafe_of_stepInv _ _ w _
      (fun (j : ℕ) (st : SubScanState) (t : Memory.State) =>
        j ≤ d.2 ∧ st.found ≤ 1 ∧
        st.cur + ((cs.drop (d.2 - j)).flatMap ConstraintTable.encode).length = endPtr ∧
        HoldsIn st.cur ((cs.drop (d.2 - j)).flatMap ConstraintTable.encode) t)
      (fun j st t ⟨hj_le, hfd_le, hcur_end, hcur_h⟩ => ?_)
      ⟨le_rfl, le_rfl, by simp [endPtr], by simpa only [Nat.sub_self, List.drop_zero] using hcs_h⟩
    have hidx_lt : d.2 - (j + 1) < cs.length := by omega
    have hdrop_cons : cs.drop (d.2 - (j + 1)) =
        cs[d.2 - (j + 1)] :: cs.drop (d.2 - j) := by
      have heq : d.2 - (j + 1) + 1 = d.2 - j := by omega
      rw [← heq]
      exact List.drop_eq_getElem_cons hidx_lt
    let ct := cs[d.2 - (j + 1)]
    rw [hdrop_cons, List.flatMap_cons, ConstraintTable.encode] at hcur_h hcur_end
    have hcons_split :
        ([ct.scope.length, ct.table.length] ++ ct.scope ++ ct.table) ++
          (cs.drop (d.2 - j)).flatMap ConstraintTable.encode =
        ct.scope.length :: ct.table.length ::
          (ct.scope ++ (ct.table ++ (cs.drop (d.2 - j)).flatMap ConstraintTable.encode)) := by
      simp [ct, List.append_assoc]
    rw [hcons_split, HoldsIn.cons_iff] at hcur_h
    obtain ⟨_, hm_sl, hcur1⟩ := hcur_h
    rw [HoldsIn.cons_iff] at hcur1
    obtain ⟨_, hm_tl, hcur2⟩ := hcur1
    rw [HoldsIn.append_iff] at hcur2
    obtain ⟨_, hcur3⟩ := hcur2
    rw [HoldsIn.append_iff] at hcur3
    obtain ⟨_, hrest_h⟩ := hcur3
    have htl_pos : 0 < ct.table.length := by
      rw [ct.table_len]; exact Nat.one_le_pow _ _ hq
    simp only [List.length_append, List.length_cons, List.length_nil] at hcur_end
    have hfit_cur1 : Fits w (st.cur + 1) := hfit_end.of_le (by dsimp only [endPtr] at *; omega)
    have hfit_cur2 : Fits w (st.cur + 2) := hfit_end.of_le (by dsimp only [endPtr] at *; omega)
    have hfit_t0 : Fits w (st.cur + 2 + t.mem st.cur) := hfit_end.of_le (by
      rw [hm_sl]; dsimp only [ct, endPtr] at *; omega)
    have hfit_next : Fits w (st.cur + 2 + t.mem st.cur + t.mem (st.cur + 1)) :=
      hfit_end.of_le (by rw [hm_sl, hm_tl]; dsimp only [ct, endPtr] at *; omega)
    have hfit_fd : Fits w st.found := h1.of_le hfd_le
    refine ⟨?_, Nat.le_of_succ_le hj_le, ?_, ?_, ?_⟩
    · dsimp only [checkLeafStep]
      repeat (
        first
        | split
        | assumption
        | refine And.intro ?_ ?_)
    · dsimp only [checkLeafStep]
      rw [StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientResult_bind,
        StateTransitionSpec.clientResult_bind]
      change (if _ then (if _ then st.found else 0) else st.found) ≤ 1
      split_ifs <;> omega
    · dsimp only [checkLeafStep]
      rw [StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientResult_bind,
        StateTransitionSpec.clientResult_bind]
      change (st.cur + 2 + t.mem st.cur + t.mem (st.cur + 1)) + _ = endPtr
      rw [hm_sl, hm_tl]
      dsimp only [ct] at *
      omega
    · dsimp only [checkLeafStep]
      rw [StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind,
        StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind,
        StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind]
      change HoldsIn (st.cur + 2 + t.mem st.cur + t.mem (st.cur + 1)) _ t
      rw [hm_sl, hm_tl]
      have hptr : st.cur + 1 + 1 + ct.scope.length + ct.table.length =
          st.cur + 2 + ct.scope.length + ct.table.length := by omega
      rwa [hptr] at hrest_h

private structure IntroConsEnv where
  q : ℕ
  v : ℕ
  bagPtr : ℕ
  bagLen : ℕ
  m : ℕ

private def IntroConsEnv.equiv : IntroConsEnv ≃ (((ℕ × ℕ) × ℕ) × ℕ) × ℕ where
  toFun e := ((((e.q, e.v), e.bagPtr), e.bagLen), e.m)
  invFun := fun ((((q, v), bp), bl), m) => ⟨q, v, bp, bl, m⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding IntroConsEnv := .ofEquiv IntroConsEnv.equiv

/-- Register arguments for `checkIntroConstraintsProg`. -/
structure IntroConsArgs where
  /-- Domain size `q`. -/
  q : ℕ
  /-- Newly introduced vertex label `v`. -/
  v : ℕ
  /-- Base address of the current bag `(v :: bagList child)`. -/
  bagPtr : ℕ
  /-- Length of the current bag. -/
  bagLen : ℕ
  /-- Radix assignment index being tested. -/
  m : ℕ
  /-- Base address of the serialized constraint-table array. -/
  consRawPtr : ℕ
  /-- Number of serialized constraint tables. -/
  numCons : ℕ

/-- Tuple equivalence encoding `IntroConsArgs` into Word-RAM registers. -/
@[expose] def IntroConsArgs.equiv :
    IntroConsArgs ≃ (((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ where
  toFun a := ((((((a.q, a.v), a.bagPtr), a.bagLen), a.m), a.consRawPtr), a.numCons)
  invFun := fun ((((((q, v), bp), bl), m), cp), nc) => ⟨q, v, bp, bl, m, cp, nc⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : WordEncoding IntroConsArgs := .ofEquiv IntroConsArgs.equiv

private def checkIntroStep (p : IntroConsEnv × SubScanState) : Memory.Prog SubScanState := do
  let e := p.1
  let st := p.2
  let scopeLen ← Memory.read st.cur
  let tblLen ← Memory.read (st.cur + 1)
  let scopePtr := st.cur + 2
  let tblPtr := scopePtr + scopeLen
  let isSub ← subsetBagProg ⟨scopePtr, scopeLen, e.bagPtr, e.bagLen⟩
  let hasV ← bagMemProg ⟨e.v, scopePtr, scopeLen⟩
  let idx ← radixProjProg ⟨e.q, e.bagPtr, e.bagLen, e.m, 0, 0, 0, scopePtr, scopeLen⟩
  let sat ← Memory.read (tblPtr + idx)
  let ok' := if isSub = 1 ∧ hasV = 1 then (if sat = 1 then st.found else 0) else st.found
  pure ⟨tblPtr + tblLen, ok'⟩

/-- Check all serialized constraints active at an `introduce` node containing `args.v`. -/
def checkIntroConstraintsProg (args : IntroConsArgs) : Memory.Prog ℕ := do
  let env : IntroConsEnv := ⟨args.q, args.v, args.bagPtr, args.bagLen, args.m⟩
  let res ← iterate checkIntroStep env args.numCons ⟨args.consRawPtr, 1⟩
  pure res.found

private theorem checkIntroStep_eval (e : IntroConsEnv) (st : SubScanState) (t : Memory.State) :
    let scopeLen := t.mem st.cur
    let tblLen := t.mem (st.cur + 1)
    let scopePtr := st.cur + 2
    let tblPtr := scopePtr + scopeLen
    let isSub := (Memory.spec 0).clientResult t
      (subsetBagProg ⟨scopePtr, scopeLen, e.bagPtr, e.bagLen⟩)
    let hasV := (Memory.spec 0).clientResult t (bagMemProg ⟨e.v, scopePtr, scopeLen⟩)
    let idx := (Memory.spec 0).clientResult t
      (radixProjProg ⟨e.q, e.bagPtr, e.bagLen, e.m, 0, 0, 0, scopePtr, scopeLen⟩)
    let sat := t.mem (tblPtr + idx)
    let ok' := if isSub = 1 ∧ hasV = 1 then (if sat = 1 then st.found else 0) else st.found
    (Memory.spec 0).clientState t (checkIntroStep (e, st)) = t ∧
    (Memory.spec 0).clientResult t (checkIntroStep (e, st)) = ⟨tblPtr + tblLen, ok'⟩ := by
  have hr_st (x : ℕ) : (Memory.spec 0).clientState t (Memory.read x) = t := rfl
  have hr_res (x : ℕ) : (Memory.spec 0).clientResult t (Memory.read x) = t.mem x := rfl
  unfold checkIntroStep
  dsimp only
  rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind, hr_st, hr_res,
    StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind, hr_st, hr_res,
    StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind,
    subsetBagProg_state,
    StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind,
    bagMemProg_state,
    StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind,
    radixProjProg_state,
    StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind, hr_st, hr_res]
  exact ⟨rfl, rfl⟩

/-- `checkIntroConstraintsProg` is read-only and leaves memory unchanged. -/
theorem checkIntroConstraintsProg_state (args : IntroConsArgs) (s : Memory.State) :
    (Memory.spec 0).clientState s (checkIntroConstraintsProg args) = s := by
  unfold checkIntroConstraintsProg
  dsimp only
  rw [StateTransitionSpec.clientState_bind]
  exact clientState_iterate_eq_of checkIntroStep
    ⟨args.q, args.v, args.bagPtr, args.bagLen, args.m⟩
    (fun st m => (checkIntroStep_eval _ st m).1) args.numCons ⟨args.consRawPtr, 1⟩ s

/-- Memory validity, functional correctness, and cost bound for `checkIntroConstraintsProg`. -/
theorem checkIntroConstraintsProg_spec {w : ℕ} (args : IntroConsArgs) (hq : 0 < args.q)
    {LB : List ℕ} {cs : List (ConstraintTable args.q)} {s : Memory.State}
    (hLB : HoldsIn args.bagPtr LB s) (hLB_len : LB.length = args.bagLen)
    (hcs : HoldsIn args.consRawPtr (cs.flatMap ConstraintTable.encode) s)
    (hcs_len : cs.length = args.numCons) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (checkIntroConstraintsProg args)) ∧
    (Memory.spec 0).clientState s (checkIntroConstraintsProg args) = s ∧
    (Memory.spec 0).clientResult s (checkIntroConstraintsProg args) =
      (if cs.all fun ct =>
          !(decide (ct.scope.toFinset ⊆ LB.toFinset) && decide (args.v ∈ ct.scope)) ||
            ct.eval (ofRadix args.q LB args.m)
        then 1 else 0) ∧
    memoryCost (checkIntroConstraintsProg args) s ≤
      3 * args.numCons +
        (cs.map fun ct => ct.scope.length).sum * (2 * args.bagLen + 3) := by
  let env : IntroConsEnv := ⟨args.q, args.v, args.bagPtr, args.bagLen, args.m⟩
  suffices ∀ (rem : List (ConstraintTable args.q)) cur ok,
      HoldsIn cur (rem.flatMap ConstraintTable.encode) s →
      (ok = 0 ∨ ok = 1) →
      (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s (iterate checkIntroStep env rem.length ⟨cur, ok⟩)) ∧
      ((Memory.spec 0).clientResult s
        (iterate checkIntroStep env rem.length ⟨cur, ok⟩)).found =
        (if ok = 1 ∧
            (rem.all fun ct =>
              !(decide (ct.scope.toFinset ⊆ LB.toFinset) && decide (args.v ∈ ct.scope)) ||
                ct.eval (ofRadix args.q LB args.m)) = true
          then 1 else 0) ∧
      memoryCost (iterate checkIntroStep env rem.length ⟨cur, ok⟩) s ≤
        3 * rem.length +
          (rem.map fun ct => ct.scope.length).sum * (2 * args.bagLen + 3) by
    have hrun := this cs args.consRawPtr 1 hcs (.inr rfl)
    rw [hcs_len] at hrun
    refine ⟨?_, checkIntroConstraintsProg_state args s, ?_, ?_⟩
    · unfold checkIntroConstraintsProg
      exact validHistory_bind_step hrun.1 (validHistory_pure w _ _)
    · unfold checkIntroConstraintsProg
      rw [StateTransitionSpec.clientResult_bind, hrun.2.1]
      cases cs.all fun ct =>
        !(decide (ct.scope.toFinset ⊆ LB.toFinset) && decide (args.v ∈ ct.scope)) ||
          ct.eval (ofRadix args.q LB args.m) <;> rfl
    · unfold checkIntroConstraintsProg
      rw [memoryCost_bind', memoryCost_pure, Nat.add_zero]
      exact hrun.2.2
  intro rem
  induction rem with
  | nil =>
    intro cur ok _ hok
    have h0 : iterate checkIntroStep env 0 ⟨cur, ok⟩ = pure ⟨cur, ok⟩ := rfl
    rw [List.length_nil, h0]
    refine ⟨validHistory_pure w s _, ?_, by simp [memoryCost_pure]⟩
    rcases hok with rfl | rfl <;> rfl
  | cons ct rest ih =>
    intro cur ok hcur hok
    rw [List.flatMap_cons, ConstraintTable.encode] at hcur
    have hcons_split :
        ([ct.scope.length, ct.table.length] ++ ct.scope ++ ct.table) ++
          rest.flatMap ConstraintTable.encode =
        ct.scope.length :: ct.table.length ::
          (ct.scope ++ (ct.table ++ rest.flatMap ConstraintTable.encode)) := by
      simp [List.append_assoc]
    rw [hcons_split, HoldsIn.cons_iff] at hcur
    obtain ⟨_, hm_sl, hcur1⟩ := hcur
    rw [HoldsIn.cons_iff] at hcur1
    obtain ⟨_, hm_tl, hcur2⟩ := hcur1
    have hcur11 : cur + 1 + 1 = cur + 2 := by omega
    rw [hcur11, HoldsIn.append_iff] at hcur2
    obtain ⟨hscope_h, hcur3⟩ := hcur2
    rw [HoldsIn.append_iff] at hcur3
    obtain ⟨htbl_h, hrest_h⟩ := hcur3
    have h0_lt : cur < s.frontier := by have := htbl_h.1; omega
    have h1_lt : cur + 1 < s.frontier := by have := htbl_h.1; omega
    obtain ⟨hv_sub, hst_sub, hr_sub, hc_sub⟩ :=
      subsetBagProg_spec (w := w) ⟨cur + 2, ct.scope.length, args.bagPtr, args.bagLen⟩
        hscope_h rfl hLB hLB_len
    obtain ⟨hv_bm, hst_bm, hr_bm, hc_bm⟩ :=
      bagMemProg_spec (w := w) ⟨args.v, cur + 2, ct.scope.length⟩ hscope_h rfl
    obtain ⟨hv_rp, hst_rp, hr_rp, hc_rp⟩ :=
      radixProjProg_spec (w := w)
        ⟨args.q, args.bagPtr, args.bagLen, args.m, 0, 0, 0, cur + 2, ct.scope.length⟩
        hLB hLB_len hscope_h rfl
    simp only [radixProjAssign, Nat.zero_ne_one, ↓reduceIte] at hr_rp hc_rp
    let idx := toRadix args.q ct.scope (ofRadix args.q LB args.m)
    have hidx_lt : idx < ct.table.length := by
      rw [ct.table_len]
      exact toRadix_lt hq _ _
    have hsat_addr : cur + 2 + ct.scope.length + idx < s.frontier := by
      have := htbl_h.1; omega
    have hm_sat : s.mem (cur + 2 + ct.scope.length + idx) = ct.table[idx] :=
      htbl_h.get idx hidx_lt
    let isSubB := decide (ct.scope.toFinset ⊆ LB.toFinset)
    let hasVB := memBag args.v ct.scope
    let ok' :=
      if (if isSubB then 1 else 0) = 1 ∧ (if hasVB then 1 else 0) = 1 then
        if ct.table[idx] = 1 then ok else 0
      else ok
    have hok' : ok' = 0 ∨ ok' = 1 := by
      dsimp only [ok']
      split_ifs <;> first | exact hok | exact .inl rfl
    obtain ⟨hst_step, hres_step⟩ := checkIntroStep_eval env ⟨cur, ok⟩ s
    have hres_step' :
        (Memory.spec 0).clientResult s (checkIntroStep (env, ⟨cur, ok⟩)) =
          ⟨cur + 2 + ct.scope.length + ct.table.length, ok'⟩ := by
      rw [hres_step]
      dsimp only [env]
      dsimp only [idx] at hm_sat
      rw [hm_sl, hm_tl, hr_sub, hr_bm, hr_rp, hm_sat]
    have hv_step : (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s (checkIntroStep (env, ⟨cur, ok⟩))) := by
      unfold checkIntroStep
      dsimp only [env]
      refine validHistory_read_bind h0_lt ?_
      rw [hm_sl]
      refine validHistory_read_bind h1_lt ?_
      rw [hm_tl]
      refine validHistory_bind_step hv_sub ?_
      rw [hst_sub, hr_sub]
      refine validHistory_bind_step hv_bm ?_
      rw [hst_bm, hr_bm]
      refine validHistory_bind_step hv_rp ?_
      rw [hst_rp, hr_rp]
      exact validHistory_read_bind hsat_addr (validHistory_pure w s _)
    have hc_step : memoryCost (checkIntroStep (env, ⟨cur, ok⟩)) s ≤
        3 + ct.scope.length * (2 * args.bagLen + 3) := by
      have hr_s (x : ℕ) : (Memory.spec 0).clientState s (Memory.read x) = s := rfl
      have hr_r (x : ℕ) : (Memory.spec 0).clientResult s (Memory.read x) = s.mem x := rfl
      dsimp only at hc_sub hc_bm hc_rp
      unfold checkIntroStep
      dsimp only [env]
      rw [memoryCost_bind', memoryCost_read, hr_s, hr_r, hm_sl,
        memoryCost_bind', memoryCost_read, hr_s, hr_r, hm_tl,
        memoryCost_bind', hst_sub, hr_sub,
        memoryCost_bind', hst_bm, hr_bm,
        memoryCost_bind', hst_rp, hr_rp,
        memoryCost_bind', memoryCost_read, hr_s, hr_r, memoryCost_pure]
      have hring :
          ct.scope.length * (args.bagLen + 1) + ct.scope.length +
            ct.scope.length * (args.bagLen + 1) =
          ct.scope.length * (2 * args.bagLen + 3) := by
        simp only [Nat.mul_add, Nat.mul_one, Nat.two_mul]
        omega
      omega
    obtain ⟨hv_rem, hr_rem, hc_rem⟩ := ih _ ok' hrest_h hok'
    simp only [List.length_cons, List.all_cons, List.map_cons, List.sum_cons]
    have hiter_eq : iterate checkIntroStep env (rest.length + 1) ⟨cur, ok⟩ =
        (checkIntroStep (env, ⟨cur, ok⟩) >>= iterate checkIntroStep env rest.length) := rfl
    rw [hiter_eq]
    refine ⟨validHistory_bind_step hv_step (by rwa [hst_step, hres_step']), ?_, ?_⟩
    · rw [StateTransitionSpec.clientResult_bind, hst_step, hres_step', hr_rem]
      refine if_congr ?_ rfl rfl
      rw [Bool.and_eq_true]
      have heval_eq : ct.eval (ofRadix args.q LB args.m) = decide (ct.table[idx] = 1) := by
        refine Bool.eq_iff_iff.2 ?_
        simp [ConstraintTable.eval, idx, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hidx_lt]
      have hhasV_eq : decide (args.v ∈ ct.scope) = hasVB := (memBag_eq_decide _ _).symm
      rw [heval_eq, hhasV_eq]
      change (ok' = 1 ∧ _) ↔
        ok = 1 ∧ ((!(isSubB && hasVB) || decide (ct.table[idx] = 1)) = true ∧ _)
      dsimp only [ok']
      rcases hok with rfl | rfl
      · cases isSubB <;> cases hasVB <;> split_ifs <;> simp
      · cases isSubB <;> cases hasVB
        · simp
        · simp
        · simp
        · by_cases ht1 : ct.table[idx] = 1 <;> simp [ht1]
    · rw [memoryCost_bind', hst_step, hres_step']
      have hadd_mul :
          (ct.scope.length + (rest.map fun c => c.scope.length).sum) * (2 * args.bagLen + 3) =
            ct.scope.length * (2 * args.bagLen + 3) +
              (rest.map fun c => c.scope.length).sum * (2 * args.bagLen + 3) :=
        Nat.add_mul _ _ _
      rw [hadd_mul]
      omega

/-- Exact-basis Word-RAM realization certificate for `checkIntroConstraintsProg`. -/
theorem checkIntroConstraintsProg_realizes :
    Realizes .exact checkIntroConstraintsProg WordEncoding.encode WordEncoding.encode
      (fun w args s =>
        0 < args.q ∧ Fits w 2 ∧ Fits w args.q ∧ Fits w args.m ∧
        Fits w (args.bagPtr + args.bagLen) ∧
        ∃ cs : List (ConstraintTable args.q),
          cs.length = args.numCons ∧
          HoldsIn args.consRawPtr (cs.flatMap ConstraintTable.encode) s ∧
          Fits w (args.consRawPtr + (cs.flatMap ConstraintTable.encode).length))
      (fun _ _ => 0) := by
  unfold checkIntroConstraintsProg
  realize [subsetBagProg_realizes, bagMemProg_realizes, radixProjProg_realizes]
  · exact h.2.1.of_le (by decide)
  · obtain ⟨hq_pos, h2, hfit_q, hfit_m, hfit_bag, cs, hcs_len, hcs_h, hfit_end⟩ := h
    have h1 : Fits w 1 := h2.of_le (by decide)
    let endPtr := d.consRawPtr + (cs.flatMap ConstraintTable.encode).length
    refine iterationSafe_of_stepInv _ _ w _
      (fun (j : ℕ) (st : SubScanState) (t : Memory.State) =>
        j ≤ d.numCons ∧ st.found ≤ 1 ∧
        st.cur + ((cs.drop (d.numCons - j)).flatMap ConstraintTable.encode).length = endPtr ∧
        HoldsIn st.cur ((cs.drop (d.numCons - j)).flatMap ConstraintTable.encode) t)
      (fun j st t ⟨hj_le, hfd_le, hcur_end, hcur_h⟩ => ?_)
      ⟨le_rfl, le_rfl, by simp [endPtr], by simpa only [Nat.sub_self, List.drop_zero] using hcs_h⟩
    have hidx_lt : d.numCons - (j + 1) < cs.length := by omega
    have hdrop_cons : cs.drop (d.numCons - (j + 1)) =
        cs[d.numCons - (j + 1)] :: cs.drop (d.numCons - j) := by
      have heq : d.numCons - (j + 1) + 1 = d.numCons - j := by omega
      rw [← heq]
      exact List.drop_eq_getElem_cons hidx_lt
    let ct := cs[d.numCons - (j + 1)]
    rw [hdrop_cons, List.flatMap_cons, ConstraintTable.encode] at hcur_h hcur_end
    have hcons_split :
        ([ct.scope.length, ct.table.length] ++ ct.scope ++ ct.table) ++
          (cs.drop (d.numCons - j)).flatMap ConstraintTable.encode =
        ct.scope.length :: ct.table.length ::
          (ct.scope ++ (ct.table ++ (cs.drop (d.numCons - j)).flatMap ConstraintTable.encode)) :=
      by
      simp [ct, List.append_assoc]
    rw [hcons_split, HoldsIn.cons_iff] at hcur_h
    obtain ⟨_, hm_sl, hcur1⟩ := hcur_h
    rw [HoldsIn.cons_iff] at hcur1
    obtain ⟨_, hm_tl, hcur2⟩ := hcur1
    have hcur11 : st.cur + 1 + 1 = st.cur + 2 := by omega
    rw [hcur11, HoldsIn.append_iff] at hcur2
    obtain ⟨hscope_h, hcur3⟩ := hcur2
    rw [HoldsIn.append_iff] at hcur3
    obtain ⟨_, hrest_h⟩ := hcur3
    simp only [List.length_append, List.length_cons, List.length_nil] at hcur_end
    have hfit_cur1 : Fits w (st.cur + 1) := hfit_end.of_le (by dsimp only [endPtr] at *; omega)
    have hfit_cur2 : Fits w (st.cur + 2) := hfit_end.of_le (by dsimp only [endPtr] at *; omega)
    have hfit_sc_end : Fits w (st.cur + 2 + t.mem st.cur) := hfit_end.of_le (by
      rw [hm_sl]; dsimp only [ct, endPtr] at *; omega)
    have hpow_eq : d.q ^ t.mem st.cur = ct.table.length := by
      rw [hm_sl, ct.table_len]
    have hfit_pow : Fits w (d.q ^ t.mem st.cur) := hfit_end.of_le (by
      rw [hpow_eq]; dsimp only [ct, endPtr] at *; omega)
    let rpArgs : RadixProjArgs :=
      ⟨d.q, d.bagPtr, d.bagLen, d.m, 0, 0, 0, st.cur + 2, t.mem st.cur⟩
    have hfit_sat (m' : Memory.State) :
        Fits w (st.cur + 2 + t.mem st.cur +
          (Memory.spec 0).clientResult m' (radixProjProg rpArgs)) := by
      have hlt : (Memory.spec 0).clientResult m' (radixProjProg rpArgs) < ct.table.length := by
        have h := radixProjProg_result_lt (args := rpArgs) hq_pos m'
        dsimp only [rpArgs] at h
        rwa [hpow_eq] at h
      exact hfit_end.of_le (by rw [hm_sl]; dsimp only [ct, endPtr] at *; omega)
    have hfit_next : Fits w (st.cur + 2 + t.mem st.cur + t.mem (st.cur + 1)) :=
      hfit_end.of_le (by rw [hm_sl, hm_tl]; dsimp only [ct, endPtr] at *; omega)
    have hfit_fd : Fits w st.found := h1.of_le hfd_le
    have hsub_safe : Fits w 1 ∧ Fits w (st.cur + 2 + t.mem st.cur) ∧
        Fits w (d.bagPtr + d.bagLen) := ⟨h1, hfit_sc_end, hfit_bag⟩
    have hbm_safe : Fits w 1 ∧ Fits w (st.cur + 2 + t.mem st.cur) := ⟨h1, hfit_sc_end⟩
    have hrp_safe :
        0 < d.q ∧ Fits w 1 ∧ Fits w d.q ∧ Fits w d.m ∧
          Fits w (d.bagPtr + d.bagLen) ∧ Fits w (st.cur + 2 + t.mem st.cur) ∧
          Fits w (d.q ^ t.mem st.cur) :=
      ⟨hq_pos, h1, hfit_q, hfit_m, hfit_bag, hfit_sc_end, hfit_pow⟩
    obtain ⟨hst_ev, hres_ev⟩ :=
      checkIntroStep_eval ⟨d.q, d.v, d.bagPtr, d.bagLen, d.m⟩ st t
    refine ⟨?_, Nat.le_of_succ_le hj_le, ?_, ?_, ?_⟩
    · dsimp only [checkIntroStep]
      refine ⟨hfit_cur1, ⟨hfit_cur2, hsub_safe⟩, ⟨hfit_cur2, hbm_safe⟩, ⟨hfit_cur2, hrp_safe⟩,
        hfit_sat _, h1, ?_⟩
      repeat (
        first
        | split
        | exact h1
        | exact hfit_next
        | refine And.intro ?_ ?_)
    · rw [hres_ev]
      dsimp only
      split_ifs <;> omega
    · rw [hres_ev]
      dsimp only
      rw [hm_sl, hm_tl]
      dsimp only [ct] at *
      omega
    · rw [hst_ev, hres_ev]
      dsimp only
      rw [hm_sl, hm_tl]
      exact hrest_h

end Cslib.Algorithms.WordRAM.TreeDecomposition
