/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.TreeDecomposition.Scan
import CslibFrontier.Computability.WordRAM.Realization.FramedLoop
import CslibFrontier.Tactic.Realize

/-!
# Word-RAM bag inclusion and erasure routines

This module certifies two materialized-bag subroutines used by the CSP dynamic program:

* `subsetBagProg`: tests whether a constraint scope slice is a subset of a bag slice via repeated
  `bagMemProg` calls.
* `eraseBagProg`: allocates `|xs.erase v|` words and copies the bag list omitting the first
  occurrence of `v`.

## Main definitions

* `Cslib.Algorithms.WordRAM.TreeDecomposition.SubsetBagArgs`,
  `Cslib.Algorithms.WordRAM.TreeDecomposition.SubScanState`: loop input and accumulator states.
* `Cslib.Algorithms.WordRAM.TreeDecomposition.subsetBagProg`: scope-inclusion check.
* `Cslib.Algorithms.WordRAM.TreeDecomposition.eraseBagProg`: single-element bag erasure copy.

## Main results

* `Cslib.Algorithms.WordRAM.TreeDecomposition.subsetBagProg_spec`,
  `Cslib.Algorithms.WordRAM.TreeDecomposition.subsetBagProg_realizes`: correctness and
  realization of `subsetBagProg`.
* `Cslib.Algorithms.WordRAM.TreeDecomposition.eraseBagProg_spec`,
  `Cslib.Algorithms.WordRAM.TreeDecomposition.eraseBagProg_realizes`: correctness and realization
  of `eraseBagProg`.
-/

public section

namespace Cslib.Algorithms.WordRAM.TreeDecomposition

open Cslib.Algorithms.Lean.TreeDecomposition
open Cslib.DataStructure
open Cslib.WordRAM
open Cslib.WordRAM.Realization

/-! ### Scope subset test (`subsetBagProg`) and bag erasure (`eraseBagProg`) -/

/-- Register arguments for the linear scope-inclusion test `subsetBagProg`. -/
structure SubsetBagArgs where
  /-- Base memory address of the constraint scope list. -/
  scopePtr : ℕ
  /-- Length of the constraint scope list. -/
  scopeLen : ℕ
  /-- Base memory address of the bag list. -/
  bagPtr : ℕ
  /-- Length of the bag list. -/
  bagLen : ℕ

/-- Tuple equivalence encoding `SubsetBagArgs` into Word-RAM registers. -/
@[expose] def SubsetBagArgs.equiv : SubsetBagArgs ≃ ((ℕ × ℕ) × ℕ) × ℕ where
  toFun a := (((a.scopePtr, a.scopeLen), a.bagPtr), a.bagLen)
  invFun := fun (((sp, sl), bp), bl) => ⟨sp, sl, bp, bl⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : WordEncoding SubsetBagArgs := .ofEquiv SubsetBagArgs.equiv

/-- Loop cursor and accumulator flag used by `subsetBagProg` and constraint scans. -/
structure SubScanState where
  /-- Current memory pointer in the scanned slice. -/
  cur : ℕ
  /-- Boolean-in-`ℕ` accumulator flag (`1` while all entries pass, `0` once falsified). -/
  found : ℕ

/-- Tuple equivalence encoding `SubScanState` into Word-RAM registers. -/
@[expose] def SubScanState.equiv : SubScanState ≃ ℕ × ℕ where
  toFun s := (s.cur, s.found)
  invFun := fun (cur, found) => ⟨cur, found⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : WordEncoding SubScanState := .ofEquiv SubScanState.equiv

private def subsetBagStep (p : (ℕ × ℕ) × SubScanState) : Memory.Prog SubScanState := do
  let bagPtr := p.1.1
  let bagLen := p.1.2
  let st := p.2
  let u ← Memory.read st.cur
  let mem ← bagMemProg ⟨u, bagPtr, bagLen⟩
  pure ⟨st.cur + 1, if mem = 1 then st.found else 0⟩

/-- Decide whether every element of the scope slice appears in the bag slice (`1` iff true). -/
def subsetBagProg (args : SubsetBagArgs) : Memory.Prog ℕ := do
  let res ← iterate subsetBagStep (args.bagPtr, args.bagLen) args.scopeLen ⟨args.scopePtr, 1⟩
  pure res.found

private theorem subsetBagStep_eval (bp bl : ℕ) (st : SubScanState) (t : Memory.State) :
    let u := t.mem st.cur
    let mem := (Memory.spec 0).clientResult t (bagMemProg ⟨u, bp, bl⟩)
    (Memory.spec 0).clientState t (subsetBagStep ((bp, bl), st)) = t ∧
    (Memory.spec 0).clientResult t (subsetBagStep ((bp, bl), st)) =
      ⟨st.cur + 1, if mem = 1 then st.found else 0⟩ := by
  unfold subsetBagStep
  dsimp only
  rw [clientState_bind_read, clientResult_bind_read, StateTransitionSpec.clientState_bind,
    StateTransitionSpec.clientResult_bind, bagMemProg_state]
  exact ⟨rfl, rfl⟩

/-- `subsetBagProg` is read-only and leaves memory unchanged. -/
theorem subsetBagProg_state (args : SubsetBagArgs) (s : Memory.State) :
    (Memory.spec 0).clientState s (subsetBagProg args) = s := by
  unfold subsetBagProg
  rw [StateTransitionSpec.clientState_bind]
  exact clientState_iterate_eq_of subsetBagStep (args.bagPtr, args.bagLen)
    (fun st m => (subsetBagStep_eval args.bagPtr args.bagLen st m).1)
    args.scopeLen ⟨args.scopePtr, 1⟩ s

/-- Memory validity, functional correctness, and cost bound for `subsetBagProg`. -/
theorem subsetBagProg_spec {w : ℕ} (args : SubsetBagArgs)
    {scopeL bagL : List ℕ} {s : Memory.State}
    (hscope : HoldsIn args.scopePtr scopeL s) (hscope_len : scopeL.length = args.scopeLen)
    (hbag : HoldsIn args.bagPtr bagL s) (hbag_len : bagL.length = args.bagLen) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (subsetBagProg args)) ∧
    (Memory.spec 0).clientState s (subsetBagProg args) = s ∧
    (Memory.spec 0).clientResult s (subsetBagProg args) =
      (if decide (scopeL.toFinset ⊆ bagL.toFinset) then 1 else 0) ∧
    memoryCost (subsetBagProg args) s ≤ args.scopeLen * (args.bagLen + 1) := by
  have hsc := hscope.1
  obtain ⟨-, hloop⟩ := Memory.FramedTriple.iterate (s := s) (body := subsetBagStep)
    (c := args.bagLen + 1) (S := ∅) (safe := fun _ _ _ => True) (d := (args.bagPtr, args.bagLen))
    (n := args.scopeLen) (a₀ := ⟨args.scopePtr, 1⟩)
    (Q := fun st _ => st.found = if ∀ u ∈ scopeL, u ∈ bagL then 1 else 0)
    (fun k st t => t = s ∧ st.cur = args.scopePtr + k ∧
      st.found = if ∀ u ∈ scopeL.take k, u ∈ bagL then 1 else 0) ⟨rfl, rfl, by simp⟩
    (fun k hk st t ⟨ht, hcur, hfd⟩ _ => ⟨trivial, by
      subst t
      have hbm := bagMemProg_framed (w := w) ⟨s.mem st.cur, args.bagPtr, args.bagLen⟩ hbag hbag_len
      unfold subsetBagStep
      framed_triple
      refine ⟨rfl, by dsimp only; omega, ?_⟩
      rw [hfd, hcur, hscope.get k (by omega), List.take_add_one,
        List.getElem?_eq_getElem (by omega), memBag_eq_decide]
      simp only [Option.toList_some, List.forall_mem_append, List.forall_mem_singleton]
      by_cases hu : scopeL[k] ∈ bagL <;> simp [hu]⟩)
    fun st t ⟨_, _, hfd⟩ _ => by rwa [← hscope_len, List.take_length] at hfd
  have hft : Memory.FramedTriple w s (subsetBagProg args) (args.scopeLen * (args.bagLen + 1)) ∅
      fun r _ => r = if decide (scopeL.toFinset ⊆ bagL.toFinset) then 1 else 0 :=
    Memory.FramedTriple.mono (Memory.FramedTriple.call (c₂ := 0) hloop subset_rfl
      fun st _ h _ => Memory.FramedTriple.pure (by simp [h, Finset.subset_iff]))
      (by rw [Nat.mul_comm]; omega) fun _ _ => id
  obtain ⟨hv, hc, -, hres⟩ := framedTriple_iff_realization.mp hft
  exact ⟨hv, subsetBagProg_state args s, hres, hc⟩

/-- Exact-basis Word-RAM realization certificate for `subsetBagProg`. -/
theorem subsetBagProg_realizes :
    Realizes .exact subsetBagProg WordEncoding.encode WordEncoding.encode
      (fun w args _ =>
        Fits w 1 ∧ Fits w (args.scopePtr + args.scopeLen) ∧ Fits w (args.bagPtr + args.bagLen))
      (fun _ _ => 0) := by
  unfold subsetBagProg
  realize [bagMemProg_realizes]
  · exact h.1
  · obtain ⟨h1, hfit_sc, hfit_bg⟩ := h
    refine iterationSafe_of_stepInv _ _ w _
      (fun (j : ℕ) (st : SubScanState) (_ : Memory.State) =>
        st.cur + j = d.scopePtr + d.scopeLen ∧ st.found ≤ 1)
      (fun j st m ⟨hcur, hfd⟩ => ?_)
      ⟨rfl, le_rfl⟩
    have hbm_safe : Fits w 1 ∧ Fits w (d.bagPtr + d.bagLen) := ⟨h1, hfit_bg⟩
    have hfit_cur1 : Fits w (st.cur + 1) := hfit_sc.of_le (by omega)
    have hfit_fd : Fits w st.found := h1.of_le hfd
    obtain ⟨_, hres_ev⟩ := subsetBagStep_eval d.bagPtr d.bagLen st m
    refine ⟨?_, ?_, ?_⟩
    · dsimp only [subsetBagStep]
      repeat (
        first
        | split
        | exact hbm_safe
        | assumption
        | refine And.intro ?_ ?_)
    · rw [hres_ev]; dsimp only; omega
    · rw [hres_ev]; dsimp only; split_ifs <;> omega

/-! ### Materialized bag erasure (`eraseBagProg`) -/

private structure EraseState where
  srcCur : ℕ
  dstCur : ℕ
  skipped : ℕ

private def EraseState.equiv : EraseState ≃ (ℕ × ℕ) × ℕ where
  toFun s := ((s.srcCur, s.dstCur), s.skipped)
  invFun := fun ((sc, dc), sk) => ⟨sc, dc, sk⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding EraseState := .ofEquiv EraseState.equiv

private def eraseCopyStep (env : ℕ × EraseState) : Memory.Prog EraseState := do
  let target := env.1
  let st := env.2
  let x ← Memory.read st.srcCur
  if st.skipped = 0 ∧ x = target then
    pure ⟨st.srcCur + 1, st.dstCur, 1⟩
  else do
    Memory.write st.dstCur x
    pure ⟨st.srcCur + 1, st.dstCur + 1, st.skipped⟩

private theorem eraseCopyStep_eval (target : ℕ) (st : EraseState) (t : Memory.State) :
    let x := t.mem st.srcCur
    (Memory.spec 0).clientState t (eraseCopyStep (target, st)) =
      (if st.skipped = 0 ∧ x = target then t
       else ⟨Function.update t.mem st.dstCur x, t.frontier⟩) ∧
    (Memory.spec 0).clientResult t (eraseCopyStep (target, st)) =
      (if st.skipped = 0 ∧ x = target then ⟨st.srcCur + 1, st.dstCur, 1⟩
       else ⟨st.srcCur + 1, st.dstCur + 1, st.skipped⟩) := by
  unfold eraseCopyStep
  dsimp only
  rw [clientState_bind_read, clientResult_bind_read]
  split_ifs <;> exact ⟨rfl, rfl⟩

private theorem sub_memBag_eq_length_erase {xs : List ℕ} {n target : ℕ} (hlen : xs.length = n) :
    n - (if memBag target xs then 1 else 0) = (xs.erase target).length := by
  subst hlen
  rw [memBag_eq_decide, List.length_erase]
  by_cases hm : target ∈ xs <;> simp [hm]

/-- Allocate and copy a materialized bag with the first occurrence of `args.target` erased. -/
def eraseBagProg (args : BagScanArgs) : Memory.Prog (ℕ × ℕ) := do
  let hasV ← bagMemProg args
  let bagLen := args.len - hasV
  let bagPtr ← Memory.allocDirty bagLen
  let _ ← iterate eraseCopyStep args.target args.len ⟨args.base, bagPtr, 0⟩
  pure (bagPtr, bagLen)

/-- Memory validity, framing, functional correctness, and cost bound for `eraseBagProg`. -/
theorem eraseBagProg_spec {w : ℕ} (args : BagScanArgs)
    {xs : List ℕ} {s : Memory.State}
    (hxs : HoldsIn args.base xs s) (hlen : xs.length = args.len)
    (hfit_elems : ∀ u ∈ xs, Fits w u)
    (hfit_fr : Fits w (s.frontier + (xs.erase args.target).length)) :
    let bagLen := (xs.erase args.target).length
    let s₁ := (Memory.spec 0).clientState s (eraseBagProg args)
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (eraseBagProg args)) ∧
    (Memory.spec 0).clientResult s (eraseBagProg args) = (s.frontier, bagLen) ∧
    s₁.frontier = s.frontier + bagLen ∧
    PreservesBelow s.frontier s s₁ ∧
    HoldsIn s.frontier (xs.erase args.target) s₁ ∧
    memoryCost (eraseBagProg args) s ≤ 3 * args.len + 1 := by
  intro bagLen s₁
  have hxsf := hxs.1
  have hlen_er : args.len - (if memBag args.target xs then 1 else 0) = bagLen :=
    sub_memBag_eq_length_erase hlen
  obtain ⟨-, hloop⟩ := Memory.FramedTriple.iterate (s := ⟨s.mem, s.frontier + bagLen⟩)
    (body := eraseCopyStep) (c := 2) (S := Set.Ico s.frontier (s.frontier + bagLen))
    (safe := fun _ _ _ => True) (d := args.target) (n := args.len)
    (a₀ := ⟨args.base, s.frontier, 0⟩)
    (Q := fun _ t => t.frontier = s.frontier + bagLen ∧ HoldsIn s.frontier (xs.erase args.target) t)
    (fun k st t => t.frontier = s.frontier + bagLen ∧ ∃ written sk,
      st = ⟨args.base + k, s.frontier + written.length, sk⟩ ∧ (sk = 0 ∨ sk = 1) ∧
      HoldsIn s.frontier written t ∧ written ++
        (if sk = 1 then xs.drop k else (xs.drop k).erase args.target) = xs.erase args.target)
    ⟨rfl, [], 0, rfl, .inl rfl, HoldsIn.nil (by dsimp only; omega), by simp⟩
    (fun k hk st t ⟨htf, written, sk, hst, hsk, hwr, hcat⟩ hmod => ⟨trivial, by
      subst hst
      have hxk : t.mem (args.base + k) = xs[k] :=
        (hmod.2 _ (by dsimp only; omega) (by region_omega)).trans (hxs.get k (by omega))
      have hfitx : Fits w (t.mem (args.base + k)) := hxk ▸ hfit_elems _ (List.getElem_mem _)
      rw [List.drop_eq_getElem_cons (by omega)] at hcat
      have hlt : ¬(sk = 0 ∧ t.mem (args.base + k) = args.target) →
          written.length < bagLen := fun hc => by
        have := congrArg List.length hcat
        rw [hxk] at hc
        rcases hsk with rfl | rfl
        · rw [ite_eq_right (by omega), List.erase_cons_tail (by simpa using hc)] at this
          simp only [List.length_append, List.length_cons] at this; omega
        · simp only [↓reduceIte, List.length_append, List.length_cons] at this; omega
      unfold eraseCopyStep
      framed_walk
      · rename_i hc
        refine ⟨htf, written, 1, rfl, .inr rfl, hwr, ?_⟩
        obtain ⟨rfl, hx⟩ := hc
        rw [hxk] at hx
        simpa [hx] using hcat
      · rename_i hc
        refine ⟨htf, written ++ [t.mem (args.base + k)], sk, by simp [Nat.add_assoc], hsk,
          holdsIn_append_one hwr (by omega), ?_⟩
        rw [hxk] at hc ⊢
        rcases hsk with rfl | rfl
        · rw [ite_eq_right (by omega), List.erase_cons_tail (by simpa using hc)] at hcat
          simpa using hcat
        · simpa using hcat⟩)
    fun st t ⟨htf, written, sk, _, _, hwr, hcat⟩ _ => ⟨htf, by
      rw [← hcat, ← hlen, List.drop_length]; split <;> simpa using hwr⟩
  have hft : Memory.FramedTriple w s (eraseBagProg args) (3 * args.len + 1)
      (Set.Ico s.frontier (s.frontier + bagLen)) fun r t =>
        r = (s.frontier, bagLen) ∧ t.frontier = s.frontier + bagLen ∧
          HoldsIn s.frontier (xs.erase args.target) t := by
    unfold eraseBagProg
    exact Memory.FramedTriple.mono (Memory.FramedTriple.call_eq
      (bagMemProg_framed (w := w) args hxs hlen) (Set.empty_subset _) (by
        dsimp only; rw [hlen_er]
        exact Memory.FramedTriple.allocDirty_bind hfit_fr (Memory.FramedTriple.call (c₂ := 0)
          hloop subset_rfl fun _ t h _ => Memory.FramedTriple.pure ⟨rfl, h⟩)))
      (by omega) fun _ _ => id
  obtain ⟨hv, hc, hm, hres, hfr, hhold⟩ := framedTriple_iff_realization.mp hft
  exact ⟨hv, hres, hfr, ⟨le_rfl, hm.1, fun a ha => hm.2 a ha (by simp; omega)⟩, hhold, hc⟩

/-- Exact-basis Word-RAM realization certificate for `eraseBagProg`. -/
theorem eraseBagProg_realizes :
    Realizes .exact eraseBagProg WordEncoding.encode WordEncoding.encode
      (fun w args s =>
        Fits w 1 ∧
        ∃ xs,
          HoldsIn args.base xs s ∧
          xs.length = args.len ∧
          args.base + args.len ≤ s.frontier ∧
          (∀ u ∈ xs, Fits w u) ∧
          Fits w (s.frontier + args.len))
      (fun _ _ => 0) := by
  unfold eraseBagProg
  realize [bagMemProg_realizes]
  · exact h.1
  · obtain ⟨_, _, _, _, hbase_le, _, hfit_fr⟩ := h
    exact hfit_fr.of_le (by omega)
  · obtain ⟨_, xs, hxs, hlen, _, _, _⟩ := h
    obtain ⟨_, _, hr_bm, _⟩ := bagMemProg_spec (w := w) d hxs hlen
    rw [hr_bm, memBag_eq_decide, ← hlen]
    by_cases hm : d.target ∈ xs
    · simpa only [hm, decide_true, ↓reduceIte] using Nat.succ_le_of_lt (List.length_pos_of_mem hm)
    · simp [hm]
  · obtain ⟨h1, xs, hxs, hlen, hbase_le, hfit_elems, hfit_fr⟩ := h
    obtain ⟨_, hst_bm, hr_bm, _⟩ := bagMemProg_spec (w := w) d hxs hlen
    rw [hst_bm, hr_bm, sub_memBag_eq_length_erase hlen]
    let bagLen := (xs.erase d.target).length
    have hbagLen_le : bagLen ≤ d.len := hlen ▸ List.length_erase_le
    let s_a : Memory.State := { mem := s.mem, frontier := s.frontier + bagLen }
    have hp_a : PreservesBelow s.frontier s s_a := ⟨le_rfl, Nat.le_add_right _ _, fun _ _ => rfl⟩
    refine iterationSafe_of_stepInv _ _ w _
      (fun (j : ℕ) (st : EraseState) (t : Memory.State) =>
        j ≤ d.len ∧
        st.srcCur + j = d.base + d.len ∧
        s.frontier ≤ st.dstCur ∧
        st.dstCur ≤ s.frontier + (d.len - j) ∧
        st.skipped ≤ 1 ∧
        HoldsIn st.srcCur (xs.drop (d.len - j)) t)
      (fun j st t ⟨hj_le, hsrc_eq, hdst_lo, hdst_hi, hsk_le, hdrop_t⟩ => ?_)
      ⟨le_rfl, by simp, le_rfl, by simp, Nat.zero_le _,
        by dsimp only; rw [Nat.sub_self, List.drop_zero]; exact hxs.mono_frontier hp_a⟩
    have hidx_lt : d.len - (j + 1) < xs.length := by omega
    have hdrop_cons : xs.drop (d.len - (j + 1)) =
        xs[d.len - (j + 1)] :: xs.drop (d.len - j) :=
      (List.drop_eq_getElem_cons hidx_lt).trans (congrArg (_ :: xs.drop ·) (by omega))
    obtain ⟨_, hmem_cur, hrest_t⟩ := HoldsIn.cons_iff.mp (hdrop_cons ▸ hdrop_t)
    have hx_fit : Fits w (t.mem st.srcCur) := hmem_cur ▸ hfit_elems _ (List.getElem_mem hidx_lt)
    have hfit_src1 : Fits w (st.srcCur + 1) := hfit_fr.of_le (by omega)
    have hfit_dst : Fits w st.dstCur := hfit_fr.of_le (by omega)
    have hfit_dst1 : Fits w (st.dstCur + 1) := hfit_fr.of_le (by omega)
    have hfit_sk : Fits w st.skipped := h1.of_le hsk_le
    obtain ⟨hst_ev, hres_ev⟩ := eraseCopyStep_eval d.target st t
    dsimp only at hst_ev hres_ev
    refine ⟨?_, Nat.le_of_succ_le hj_le, ?_⟩
    · dsimp only [eraseCopyStep]
      repeat (
        first
        | split
        | assumption
        | refine And.intro ?_ ?_)
    · rw [hst_ev, hres_ev]
      by_cases hc : st.skipped = 0 ∧ t.mem st.srcCur = d.target
      · rw [ite_eq_left hc, ite_eq_left hc]
        exact ⟨by dsimp only; omega, hdst_lo,
          hdst_hi.trans (Nat.add_le_add_left (by omega) _), le_rfl, hrest_t⟩
      · rw [ite_eq_right hc, ite_eq_right hc]
        dsimp only
        refine ⟨by omega, by omega, by omega, hsk_le, hrest_t.1,
          hrest_t.2.frame fun a _ ha => ?_⟩
        have hdl : (xs.drop (d.len - j)).length = j := by simp [hlen]; omega
        exact Function.update_of_ne (by omega) _ t.mem

end Cslib.Algorithms.WordRAM.TreeDecomposition
