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

/-! ### Scanning serialized constraint tables

Both scans run `iterate step env n ⟨ptr, 1⟩` over `cs.flatMap ConstraintTable.encode`: each step
reads one table in place, moves the cursor past it and clears the flag when the table is
violated. `scanConstraints_spec` and `scanConstraints_iterationSafe` carry out the induction over
the table list once; the two scans supply only their per-table step. -/

/-- The header words and the two blocks of one serialized constraint table. -/
private theorem holdsIn_encode {q cur : ℕ} {ct : ConstraintTable q} {s : Memory.State}
    (h : HoldsIn cur ct.encode s) :
    s.mem cur = ct.scope.length ∧ s.mem (cur + 1) = ct.table.length ∧
      HoldsIn (cur + 2) ct.scope s ∧ HoldsIn (cur + 2 + ct.scope.length) ct.table s := by
  rw [ConstraintTable.encode, HoldsIn.append_iff, HoldsIn.append_iff, HoldsIn.cons_iff,
    HoldsIn.cons_iff] at h
  obtain ⟨⟨⟨_, hsl, _, htl, _⟩, hscope⟩, htbl⟩ := h
  rw [List.length_append, ← Nat.add_assoc] at htbl
  exact ⟨hsl, htl, hscope, htbl⟩

private theorem length_encode {q : ℕ} (ct : ConstraintTable q) :
    ct.encode.length = 2 + ct.scope.length + ct.table.length := by
  simp only [ConstraintTable.encode, List.length_append, List.length_cons, List.length_nil]

/-- Specification of a read-only scan over serialized constraint tables: if each step on a table
`ct` advances the cursor past `ct`, keeps the flag exactly when `P ct` holds, and costs at most
`c ct`, then the scan returns `1` iff every table satisfies `P`, within cost `(cs.map c).sum`. -/
private theorem scanConstraints_spec {δ : Type} {w q n ptr : ℕ}
    (step : δ × SubScanState → Memory.Prog SubScanState) (e : δ)
    (P : ConstraintTable q → Bool) (c : ConstraintTable q → ℕ)
    {cs : List (ConstraintTable q)} {s : Memory.State}
    (hstep : ∀ (ct : ConstraintTable q) (cur ok : ℕ), HoldsIn cur ct.encode s →
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (step (e, ⟨cur, ok⟩))) ∧
      (Memory.spec 0).clientState s (step (e, ⟨cur, ok⟩)) = s ∧
      (Memory.spec 0).clientResult s (step (e, ⟨cur, ok⟩)) =
        ⟨cur + 2 + ct.scope.length + ct.table.length, if P ct then ok else 0⟩ ∧
      memoryCost (step (e, ⟨cur, ok⟩)) s ≤ c ct)
    (hcs : HoldsIn ptr (cs.flatMap ConstraintTable.encode) s) (hlen : cs.length = n) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (iterate step e n ⟨ptr, 1⟩ >>= fun res => pure res.found)) ∧
    (Memory.spec 0).clientResult s (iterate step e n ⟨ptr, 1⟩ >>= fun res => pure res.found) =
      (if cs.all P then 1 else 0) ∧
    memoryCost (iterate step e n ⟨ptr, 1⟩ >>= fun res => pure res.found) s ≤ (cs.map c).sum := by
  suffices ∀ (rem : List (ConstraintTable q)) (cur ok : ℕ),
      HoldsIn cur (rem.flatMap ConstraintTable.encode) s →
      (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s (iterate step e rem.length ⟨cur, ok⟩)) ∧
      ((Memory.spec 0).clientResult s (iterate step e rem.length ⟨cur, ok⟩)).found =
        (if rem.all P then ok else 0) ∧
      memoryCost (iterate step e rem.length ⟨cur, ok⟩) s ≤ (rem.map c).sum by
    subst hlen
    obtain ⟨hv, hr, hc⟩ := this cs ptr 1 hcs
    refine ⟨validHistory_bind_step hv (validHistory_pure w _ _), ?_, ?_⟩
    · rw [StateTransitionSpec.clientResult_bind, hr]
      rfl
    · rw [memoryCost_bind', memoryCost_pure, Nat.add_zero]
      exact hc
  intro rem
  induction rem with
  | nil => exact fun _ _ _ => ⟨validHistory_pure w s _, rfl, by simp [iterate, memoryCost_pure]⟩
  | cons ct rest ih =>
    intro cur ok hcur
    rw [List.flatMap_cons, HoldsIn.append_iff, length_encode, ← Nat.add_assoc,
      ← Nat.add_assoc] at hcur
    obtain ⟨hv, hst, hres, hc⟩ := hstep ct cur ok hcur.1
    obtain ⟨hv', hres', hc'⟩ := ih _ (if P ct then ok else 0) hcur.2
    change (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
        (step (e, ⟨cur, ok⟩) >>= iterate step e rest.length)) ∧
      ((Memory.spec 0).clientResult s
        (step (e, ⟨cur, ok⟩) >>= iterate step e rest.length)).found = _ ∧
      memoryCost (step (e, ⟨cur, ok⟩) >>= iterate step e rest.length) s ≤ _
    refine ⟨validHistory_bind_step hv (by rwa [hst, hres]), ?_, ?_⟩
    · rw [StateTransitionSpec.clientResult_bind, hst, hres, hres', List.all_cons]
      cases P ct <;> cases rest.all P <;> rfl
    · rw [memoryCost_bind', hst, hres, List.map_cons, List.sum_cons]
      omega

/-- Realization safety of a read-only scan over serialized constraint tables: if each step on a
table `ct` that fits in `w` bits is safe, leaves memory unchanged, advances the cursor past `ct`
and keeps the flag at most `1`, then the whole scan is safe. -/
private theorem scanConstraints_iterationSafe {δ : Type} {w q n ptr : ℕ}
    (step : δ × SubScanState → Memory.Prog SubScanState)
    (safe : ℕ → δ × SubScanState → Memory.State → Prop) (e : δ)
    {cs : List (ConstraintTable q)} {s : Memory.State}
    (hstep : ∀ (ct : ConstraintTable q) (st : SubScanState) (t : Memory.State),
      st.found ≤ 1 → HoldsIn st.cur ct.encode t →
      Fits w (st.cur + 2 + ct.scope.length + ct.table.length) →
      safe w (e, st) t ∧ (Memory.spec 0).clientState t (step (e, st)) = t ∧
      ((Memory.spec 0).clientResult t (step (e, st))).cur =
        st.cur + 2 + ct.scope.length + ct.table.length ∧
      ((Memory.spec 0).clientResult t (step (e, st))).found ≤ 1)
    (hcs : HoldsIn ptr (cs.flatMap ConstraintTable.encode) s) (hlen : cs.length = n)
    (hfit : Fits w (ptr + (cs.flatMap ConstraintTable.encode).length)) :
    iterationSafe step safe w e n ⟨ptr, 1⟩ s := by
  subst hlen
  refine iterationSafe_of_stepInv step safe w e
    (fun j st t => ∃ rem : List (ConstraintTable q), rem.length = j ∧ st.found ≤ 1 ∧
      Fits w (st.cur + (rem.flatMap ConstraintTable.encode).length) ∧
      HoldsIn st.cur (rem.flatMap ConstraintTable.encode) t)
    (fun j st t ⟨rem, hrem, hfd, hfit, hcur⟩ => ?_) ⟨cs, rfl, le_rfl, hfit, hcs⟩
  cases rem with
  | nil => exact absurd hrem (Nat.succ_ne_zero j).symm
  | cons ct rest =>
    rw [List.flatMap_cons, HoldsIn.append_iff, length_encode, ← Nat.add_assoc,
      ← Nat.add_assoc] at hcur
    rw [List.flatMap_cons, List.length_append, length_encode, ← Nat.add_assoc, ← Nat.add_assoc,
      ← Nat.add_assoc] at hfit
    obtain ⟨hsafe, hst, hcur', hfd'⟩ :=
      hstep ct st t hfd hcur.1 (hfit.of_le (Nat.le_add_right _ _))
    refine ⟨hsafe, rest, Nat.succ_inj.1 hrem, hfd', ?_, ?_⟩
    · rwa [hcur']
    · rw [hst, hcur']
      exact hcur.2

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

/-- One `checkLeafStep` reads a serialized table and clears the flag iff the table is a violated
empty-scope constraint. -/
private theorem checkLeafStep_spec {w q : ℕ} (hq : 0 < q) {ct : ConstraintTable q}
    {cur ok : ℕ} {s : Memory.State} (hct : HoldsIn cur ct.encode s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (checkLeafStep ((), ⟨cur, ok⟩))) ∧
    (Memory.spec 0).clientState s (checkLeafStep ((), ⟨cur, ok⟩)) = s ∧
    (Memory.spec 0).clientResult s (checkLeafStep ((), ⟨cur, ok⟩)) =
      ⟨cur + 2 + ct.scope.length + ct.table.length,
        if !decide (ct.scope = []) || ct.eval (fun _ => 0) then ok else 0⟩ ∧
    memoryCost (checkLeafStep ((), ⟨cur, ok⟩)) s ≤ 3 := by
  obtain ⟨hm_sl, hm_tl, -, htbl_h⟩ := holdsIn_encode hct
  have htl_pos : 0 < ct.table.length := by
    rw [ct.table_len]
    exact Nat.one_le_pow _ _ hq
  have hm_t0 : s.mem (cur + 2 + ct.scope.length) = ct.table[0] := htbl_h.get 0 htl_pos
  have hr_s (x : ℕ) : (Memory.spec 0).clientState s (Memory.read x) = s := rfl
  have hr_r (x : ℕ) : (Memory.spec 0).clientResult s (Memory.read x) = s.mem x := rfl
  refine ⟨?_, rfl, ?_, ?_⟩
  · unfold checkLeafStep
    dsimp only
    refine validHistory_read_bind (by have := htbl_h.1; omega) ?_
    rw [hm_sl]
    refine validHistory_read_bind (by have := htbl_h.1; omega) ?_
    rw [hm_tl]
    exact validHistory_read_bind (by have := htbl_h.1; omega) (validHistory_pure w s _)
  · unfold checkLeafStep
    dsimp only
    rw [StateTransitionSpec.clientResult_bind, hr_s, hr_r, hm_sl,
      StateTransitionSpec.clientResult_bind, hr_s, hr_r, hm_tl,
      StateTransitionSpec.clientResult_bind, hr_s, hr_r, hm_t0]
    change SubScanState.mk _ (if _ then _ else _) = SubScanState.mk _ (if _ then _ else _)
    by_cases hnil : ct.scope = []
    · have heval : ct.eval (fun _ => 0) = decide (ct.table[0] = 1) := by
        refine Bool.eq_iff_iff.2 ?_
        simp [hnil, ConstraintTable.eval, toRadix_nil, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem htl_pos]
      simp only [hnil, List.length_nil, heval, decide_true, Bool.not_true, Bool.false_or,
        decide_eq_true_eq, ↓reduceIte]
    · simp [hnil]
  · unfold checkLeafStep
    dsimp only
    rw [memoryCost_bind', memoryCost_read, hr_s, hr_r, hm_sl,
      memoryCost_bind', memoryCost_read, hr_s, hr_r, hm_tl,
      memoryCost_bind', memoryCost_read, hr_s, hr_r, memoryCost_pure]

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
  obtain ⟨hv, hr, hc⟩ := scanConstraints_spec (w := w) checkLeafStep ()
    (fun ct => !decide (ct.scope = []) || ct.eval (fun _ => 0)) (fun _ => 3)
    (fun _ _ _ hct => checkLeafStep_spec hq hct) hcs hlen
  refine ⟨hv, checkLeafConstraintsProg_state args s, hr, ?_⟩
  rw [List.map_const', List.sum_replicate, smul_eq_mul, hlen, Nat.mul_comm] at hc
  exact hc

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
    refine scanConstraints_iterationSafe _ _ _
      (fun ct st t hfd_le hct hfit => ?_) hcs_h hcs_len hfit_end
    obtain ⟨hm_sl, hm_tl, -, -⟩ := holdsIn_encode hct
    have hfit_cur1 : Fits w (st.cur + 1) := hfit.of_le (by omega)
    have hfit_cur2 : Fits w (st.cur + 2) := hfit.of_le (by omega)
    have hfit_t0 : Fits w (st.cur + 2 + t.mem st.cur) := hfit.of_le (by rw [hm_sl]; omega)
    have hfit_next : Fits w (st.cur + 2 + t.mem st.cur + t.mem (st.cur + 1)) := by
      rwa [hm_sl, hm_tl]
    have hfit_fd : Fits w st.found := h1.of_le hfd_le
    refine ⟨?_, rfl, ?_, ?_⟩
    · dsimp only [checkLeafStep]
      repeat (
        first
        | split
        | assumption
        | refine And.intro ?_ ?_)
    · change st.cur + 2 + t.mem st.cur + t.mem (st.cur + 1) = _
      rw [hm_sl, hm_tl]
    · change (if _ then (if _ then st.found else 0) else st.found) ≤ 1
      split_ifs <;> omega

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

/-- One `checkIntroStep` reads a serialized table and clears the flag iff the table's scope lies
in the bag `LB`, contains `e.v`, and is violated by the assignment decoded from `e.m`. -/
private theorem checkIntroStep_spec {w : ℕ} (e : IntroConsEnv) (hq : 0 < e.q) {LB : List ℕ}
    {ct : ConstraintTable e.q} {cur ok : ℕ} {s : Memory.State}
    (hLB : HoldsIn e.bagPtr LB s) (hLB_len : LB.length = e.bagLen)
    (hct : HoldsIn cur ct.encode s) :
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (checkIntroStep (e, ⟨cur, ok⟩))) ∧
    (Memory.spec 0).clientState s (checkIntroStep (e, ⟨cur, ok⟩)) = s ∧
    (Memory.spec 0).clientResult s (checkIntroStep (e, ⟨cur, ok⟩)) =
      ⟨cur + 2 + ct.scope.length + ct.table.length,
        if !(decide (ct.scope.toFinset ⊆ LB.toFinset) && decide (e.v ∈ ct.scope)) ||
            ct.eval (ofRadix e.q LB e.m)
          then ok else 0⟩ ∧
    memoryCost (checkIntroStep (e, ⟨cur, ok⟩)) s ≤
      3 + ct.scope.length * (2 * e.bagLen + 3) := by
  obtain ⟨hm_sl, hm_tl, hscope_h, htbl_h⟩ := holdsIn_encode hct
  obtain ⟨hv_sub, hst_sub, hr_sub, hc_sub⟩ :=
    subsetBagProg_spec (w := w) ⟨cur + 2, ct.scope.length, e.bagPtr, e.bagLen⟩
      hscope_h rfl hLB hLB_len
  obtain ⟨hv_bm, hst_bm, hr_bm, hc_bm⟩ :=
    bagMemProg_spec (w := w) ⟨e.v, cur + 2, ct.scope.length⟩ hscope_h rfl
  obtain ⟨hv_rp, hst_rp, hr_rp, hc_rp⟩ :=
    radixProjProg_spec (w := w)
      ⟨e.q, e.bagPtr, e.bagLen, e.m, 0, 0, 0, cur + 2, ct.scope.length⟩
      hLB hLB_len hscope_h rfl
  simp only [radixProjAssign, Nat.zero_ne_one, ↓reduceIte] at hr_rp hc_rp
  set idx := toRadix e.q ct.scope (ofRadix e.q LB e.m) with hidx
  have hidx_lt : idx < ct.table.length := by
    rw [ct.table_len]
    exact toRadix_lt hq _ _
  have hm_sat : s.mem (cur + 2 + ct.scope.length + idx) = ct.table[idx] :=
    htbl_h.get idx hidx_lt
  obtain ⟨hst_step, hres_step⟩ := checkIntroStep_eval e ⟨cur, ok⟩ s
  have hr_s (x : ℕ) : (Memory.spec 0).clientState s (Memory.read x) = s := rfl
  have hr_r (x : ℕ) : (Memory.spec 0).clientResult s (Memory.read x) = s.mem x := rfl
  refine ⟨?_, hst_step, ?_, ?_⟩
  · unfold checkIntroStep
    dsimp only
    refine validHistory_read_bind (by have := htbl_h.1; omega) ?_
    rw [hm_sl]
    refine validHistory_read_bind (by have := htbl_h.1; omega) ?_
    rw [hm_tl]
    refine validHistory_bind_step hv_sub ?_
    rw [hst_sub, hr_sub]
    refine validHistory_bind_step hv_bm ?_
    rw [hst_bm, hr_bm]
    refine validHistory_bind_step hv_rp ?_
    rw [hst_rp, hr_rp]
    exact validHistory_read_bind (by have := htbl_h.1; omega) (validHistory_pure w s _)
  · rw [hres_step]
    dsimp only
    rw [hm_sl, hm_tl, hr_sub, hr_bm, hr_rp, hm_sat]
    have heval_eq : ct.eval (ofRadix e.q LB e.m) = decide (ct.table[idx] = 1) := by
      refine Bool.eq_iff_iff.2 ?_
      simp [ConstraintTable.eval, ← hidx, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hidx_lt]
    rw [heval_eq, ← memBag_eq_decide]
    change SubScanState.mk _ (if _ then _ else _) = SubScanState.mk _ (if _ then _ else _)
    cases decide (ct.scope.toFinset ⊆ LB.toFinset) <;> cases memBag e.v ct.scope <;>
      by_cases ht1 : ct.table[idx] = 1 <;> simp [ht1]
  · dsimp only at hc_sub hc_bm hc_rp
    unfold checkIntroStep
    dsimp only
    rw [memoryCost_bind', memoryCost_read, hr_s, hr_r, hm_sl,
      memoryCost_bind', memoryCost_read, hr_s, hr_r, hm_tl,
      memoryCost_bind', hst_sub, hr_sub,
      memoryCost_bind', hst_bm, hr_bm,
      memoryCost_bind', hst_rp, hr_rp,
      memoryCost_bind', memoryCost_read, hr_s, hr_r, memoryCost_pure]
    have hring :
        ct.scope.length * (e.bagLen + 1) + ct.scope.length +
          ct.scope.length * (e.bagLen + 1) =
        ct.scope.length * (2 * e.bagLen + 3) := by
      simp only [Nat.mul_add, Nat.mul_one, Nat.two_mul]
      omega
    omega

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
  obtain ⟨hv, hr, hc⟩ := scanConstraints_spec (w := w) checkIntroStep
    ⟨args.q, args.v, args.bagPtr, args.bagLen, args.m⟩
    (fun ct => !(decide (ct.scope.toFinset ⊆ LB.toFinset) && decide (args.v ∈ ct.scope)) ||
      ct.eval (ofRadix args.q LB args.m))
    (fun ct => 3 + ct.scope.length * (2 * args.bagLen + 3))
    (fun _ _ _ hct => checkIntroStep_spec _ hq hLB hLB_len hct) hcs hcs_len
  refine ⟨hv, checkIntroConstraintsProg_state args s, hr, ?_⟩
  rw [List.sum_map_add, List.map_const', List.sum_replicate, smul_eq_mul, hcs_len,
    List.sum_map_mul_right, Nat.mul_comm args.numCons] at hc
  exact hc

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
    refine scanConstraints_iterationSafe _ _ _
      (fun ct st t hfd_le hct hfit => ?_) hcs_h hcs_len hfit_end
    obtain ⟨hm_sl, hm_tl, -, -⟩ := holdsIn_encode hct
    have hfit_cur1 : Fits w (st.cur + 1) := hfit.of_le (by omega)
    have hfit_cur2 : Fits w (st.cur + 2) := hfit.of_le (by omega)
    have hfit_sc_end : Fits w (st.cur + 2 + t.mem st.cur) := hfit.of_le (by rw [hm_sl]; omega)
    have hpow_eq : d.q ^ t.mem st.cur = ct.table.length := by
      rw [hm_sl, ct.table_len]
    have hfit_pow : Fits w (d.q ^ t.mem st.cur) := hfit.of_le (by rw [hpow_eq]; omega)
    let rpArgs : RadixProjArgs :=
      ⟨d.q, d.bagPtr, d.bagLen, d.m, 0, 0, 0, st.cur + 2, t.mem st.cur⟩
    have hfit_sat (m' : Memory.State) :
        Fits w (st.cur + 2 + t.mem st.cur +
          (Memory.spec 0).clientResult m' (radixProjProg rpArgs)) := by
      have hlt : (Memory.spec 0).clientResult m' (radixProjProg rpArgs) < ct.table.length := by
        have h := radixProjProg_result_lt (args := rpArgs) hq_pos m'
        dsimp only [rpArgs] at h
        rwa [hpow_eq] at h
      exact hfit.of_le (by rw [hm_sl]; omega)
    have hfit_next : Fits w (st.cur + 2 + t.mem st.cur + t.mem (st.cur + 1)) := by
      rwa [hm_sl, hm_tl]
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
    refine ⟨?_, hst_ev, ?_, ?_⟩
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
      rw [hm_sl, hm_tl]
    · rw [hres_ev]
      dsimp only
      split_ifs <;> omega

end Cslib.Algorithms.WordRAM.TreeDecomposition
