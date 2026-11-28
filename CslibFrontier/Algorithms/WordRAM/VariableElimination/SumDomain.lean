/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.VariableElimination.BucketProd
import CslibFrontier.Tactic.Realize
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.List

/-!
# Domain Value Summation (`sumDomainValues`)

Sums the bucket factor product over all values `a : Fin dom` assigned to the eliminated variable `x`
at a fixed outer-scope radix index.

## Main definitions

* `Cslib.Algorithms.WordRAM.VariableElimination.sumDomainValues`: domain-sum `Memory.Prog`.
-/

public section

namespace Cslib.Algorithms.WordRAM.VariableElimination

open Cslib.Logic.PL Cslib.Logic.PL.CSP
open Cslib.Algorithms.Lean.CSP
open Cslib.DataStructure
open Cslib.WordRAM
open Cslib.WordRAM.Realization

/-! ### Domain summation (`sumDomainValues`) and table materialization (`buildOutEntries`) -/

/-- Arguments for summing `evalBucketProd` over `a ∈ [0, dom)`. -/
structure SumDomainArgs where
  /-- Field `dom` of `SumDomainArgs`. -/
  dom : ℕ
  /-- Field `x` of `SumDomainArgs`. -/
  x : ℕ
  /-- Field `outPtr` of `SumDomainArgs`. -/
  outPtr : ℕ
  /-- Field `outLen` of `SumDomainArgs`. -/
  outLen : ℕ
  /-- Field `idx` of `SumDomainArgs`. -/
  idx : ℕ
  /-- Field `bucketPtr` of `SumDomainArgs`. -/
  bucketPtr : ℕ
  /-- Field `bucketLen` of `SumDomainArgs`. -/
  bucketLen : ℕ

/-- Product equivalence encoding `SumDomainArgs` as words. -/
@[expose] def SumDomainArgs.equiv :
    SumDomainArgs ≃ (((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ where
  toFun s := ((((((s.dom, s.x), s.outPtr), s.outLen), s.idx), s.bucketPtr), s.bucketLen)
  invFun := fun ((((((dom, x), outPtr), outLen), idx), bucketPtr), bucketLen) =>
    ⟨dom, x, outPtr, outLen, idx, bucketPtr, bucketLen⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : WordEncoding SumDomainArgs := .ofEquiv SumDomainArgs.equiv

private structure SumDomainState where
  curA : ℕ
  sumAcc : ℕ

private def SumDomainState.equiv : SumDomainState ≃ ℕ × ℕ where
  toFun s := (s.curA, s.sumAcc)
  invFun := fun (curA, sumAcc) => ⟨curA, sumAcc⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding SumDomainState := .ofEquiv SumDomainState.equiv

private def sumDomainStep (p : SumDomainArgs × SumDomainState) : Memory.Prog SumDomainState :=
  Memory.read 0 >>= fun _ =>
  evalBucketProd
    ⟨p.1.dom, p.1.x, p.2.curA, p.1.outPtr, p.1.outLen, p.1.idx, p.1.bucketPtr, p.1.bucketLen⟩
    >>= fun prod =>
  pure ⟨p.2.curA + 1, p.2.sumAcc + prod⟩

/-- Sum `evalBucketProd` across all domain values of the eliminated variable. -/
def sumDomainValues (args : SumDomainArgs) : Memory.Prog ℕ :=
  iterate sumDomainStep args args.dom ⟨0, 0⟩ >>= fun res => pure res.sumAcc

private theorem sumDomainStep_state (args : SumDomainArgs) (st : SumDomainState)
    (s : Memory.State) :
    (Memory.spec 0).clientState s (sumDomainStep (args, st)) = s := by
  unfold sumDomainStep
  have hr : (Memory.spec 0).clientState s (Memory.read 0) = s := rfl
  rw [StateTransitionSpec.clientState_bind, hr, StateTransitionSpec.clientState_bind,
    evalBucketProd_state]
  rfl

private theorem sumDomainStep_result (args : SumDomainArgs) (st : SumDomainState)
    (s : Memory.State) :
    (Memory.spec 0).clientResult s (sumDomainStep (args, st)) =
      ⟨st.curA + 1, st.sumAcc + (Memory.spec 0).clientResult s (evalBucketProd
        ⟨args.dom, args.x, st.curA, args.outPtr, args.outLen, args.idx,
          args.bucketPtr, args.bucketLen⟩)⟩ := by
  unfold sumDomainStep
  have hr : (Memory.spec 0).clientState s (Memory.read 0) = s := rfl
  rw [StateTransitionSpec.clientResult_bind, hr, StateTransitionSpec.clientResult_bind,
    evalBucketProd_state]
  rfl

theorem sumDomainValues_state (args : SumDomainArgs) (s : Memory.State) :
    (Memory.spec 0).clientState s (sumDomainValues args) = s := by
  unfold sumDomainValues
  rw [StateTransitionSpec.clientState_bind]
  exact clientState_iterate_eq_of sumDomainStep args (sumDomainStep_state args) args.dom ⟨0, 0⟩ s

private theorem memoryCost_iterate_le_of_state_eq {α δ : Type} (step : δ × α → Memory.Prog α)
    (c : ℕ) (env : δ) (s : Memory.State)
    (hst : ∀ a, (Memory.spec 0).clientState s (step (env, a)) = s)
    (hcost : ∀ a, memoryCost (step (env, a)) s ≤ c) :
    ∀ n a, memoryCost (iterate step env n a) s ≤ n * c
  | 0, _ => by simp [iterate]
  | n + 1, a => by
    change memoryCost (step (env, a) >>= iterate step env n) s ≤ (n + 1) * c
    rw [memoryCost_bind', hst a]
    calc memoryCost (step (env, a)) s + _
        ≤ c + n * c := Nat.add_le_add (hcost a)
          (memoryCost_iterate_le_of_state_eq step c env s hst hcost n _)
      _ = (n + 1) * c := by ring

theorem sumDomainValues_cost {args : SumDomainArgs} {bucket : List (FactorTable ℕ ℕ)}
    {maxScope : ℕ} {s : Memory.State}
    (hb : HoldsFactorList args.bucketPtr bucket s) (hlen : bucket.length = args.bucketLen)
    (hmax : ∀ f ∈ bucket, f.scope.length ≤ maxScope) :
    memoryCost (sumDomainValues args) s ≤
      args.dom * (1 + args.bucketLen * (5 + maxScope * (args.outLen + 1))) := by
  unfold sumDomainValues
  rw [memoryCost_bind', memoryCost_pure, Nat.add_zero]
  refine memoryCost_iterate_le_of_state_eq sumDomainStep
    (1 + args.bucketLen * (5 + maxScope * (args.outLen + 1))) args s
    (fun st => sumDomainStep_state args st s) (fun st => ?_) args.dom ⟨0, 0⟩
  unfold sumDomainStep
  have hr : (Memory.spec 0).clientState s (Memory.read 0) = s := rfl
  rw [memoryCost_bind', memoryCost_read, hr, memoryCost_bind', evalBucketProd_state,
    memoryCost_pure, Nat.add_zero]
  exact Nat.add_le_add_left (evalBucketProd_cost hb hlen hmax) 1

theorem sumDomainValues_valid {w : ℕ} {args : SumDomainArgs}
    {bucket : List (FactorTable ℕ ℕ)} {s : Memory.State}
    (hs0 : 0 < s.frontier) (hout : args.outPtr + args.outLen ≤ s.frontier)
    (hb : HoldsFactorList args.bucketPtr bucket s) (hlen : bucket.length = args.bucketLen) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (sumDomainValues args)) := by
  unfold sumDomainValues
  refine validHistory_bind_step ?_ (validHistory_pure w _ _)
  suffices ∀ n st, (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (iterate sumDomainStep args n st)) from
    this args.dom ⟨0, 0⟩
  intro n
  induction n with
  | zero => intro _; exact validHistory_pure w s _
  | succ n ih =>
    intro st
    have hstep : (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s (sumDomainStep (args, st))) := by
      unfold sumDomainStep
      exact validHistory_read_bind hs0
        (validHistory_bind_step (evalBucketProd_valid hout hb hlen) (validHistory_pure w _ _))
    change (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s
        (sumDomainStep (args, st) >>= iterate sumDomainStep args n))
    refine validHistory_bind_step hstep ?_
    rw [sumDomainStep_state]
    exact ih _

theorem sumDomainValues_le_cap {args : SumDomainArgs} {bucket : List (FactorTable ℕ ℕ)}
    {s : Memory.State} (hb : HoldsFactorList args.bucketPtr bucket s)
    (hlen : bucket.length = args.bucketLen) :
    (Memory.spec 0).clientResult s (sumDomainValues args) ≤
      args.dom * (bucket.map capFactor).prod := by
  unfold sumDomainValues
  rw [StateTransitionSpec.clientResult_bind]
  have hpure (t : Memory.State) (v : ℕ) : (Memory.spec 0).clientResult t (pure v) = v := rfl
  rw [hpure]
  suffices ∀ (k curA acc : ℕ),
      ((Memory.spec 0).clientResult s (iterate sumDomainStep args k ⟨curA, acc⟩)).sumAcc ≤
      acc + k * (bucket.map capFactor).prod by
    simpa using this args.dom 0 0
  intro k
  induction k with
  | zero => intro curA acc; change acc ≤ acc + 0 * _; simp
  | succ k ih =>
    intro curA acc
    change ((Memory.spec 0).clientResult s
      (sumDomainStep (args, ⟨curA, acc⟩) >>= iterate sumDomainStep args k)).sumAcc ≤ _
    rw [StateTransitionSpec.clientResult_bind, sumDomainStep_state, sumDomainStep_result]
    have hp := evalBucketProd_le_cap
      (args := ⟨args.dom, args.x, curA, args.outPtr, args.outLen, args.idx,
        args.bucketPtr, args.bucketLen⟩) hb hlen
    exact (ih (curA + 1) _).trans (by linarith)

theorem sumDomainValues_result {args : SumDomainArgs} {outScope : List ℕ}
    {bucket : List (FactorTable ℕ ℕ)} {s : Memory.State}
    (hout : Block.HoldsList args.outPtr outScope s.mem) (hout_len : outScope.length = args.outLen)
    (hb : HoldsFactorList args.bucketPtr bucket s) (hlen : bucket.length = args.bucketLen) :
    (Memory.spec 0).clientResult s (sumDomainValues args) =
      ∑ a : Fin args.dom,
        (bucket.map fun f => f.evalAt args.dom fun v =>
          if v = args.x then a.val
          else assignScope outScope (lsbDecode args.dom outScope.length args.idx) v).prod := by
  unfold sumDomainValues
  rw [StateTransitionSpec.clientResult_bind,
    Fin.sum_univ_eq_sum_range (fun a =>
      (bucket.map fun f => f.evalAt args.dom fun v =>
        if v = args.x then a
        else assignScope outScope (lsbDecode args.dom outScope.length args.idx) v).prod)]
  have hpure (t : Memory.State) (v : ℕ) : (Memory.spec 0).clientResult t (pure v) = v := rfl
  rw [hpure]
  let term : ℕ → ℕ := fun a =>
    (bucket.map fun f => f.evalAt args.dom fun v =>
      if v = args.x then a
      else assignScope outScope (lsbDecode args.dom outScope.length args.idx) v).prod
  suffices ∀ (k startA acc : ℕ),
      ((Memory.spec 0).clientResult s (iterate sumDomainStep args k ⟨startA, acc⟩)).sumAcc =
      acc + ∑ i ∈ Finset.range k, term (startA + i) by
    simpa [term] using this args.dom 0 0
  intro k
  induction k with
  | zero => intro startA acc; change acc = acc + 0; simp
  | succ k ih =>
    intro startA acc
    change ((Memory.spec 0).clientResult s
      (sumDomainStep (args, ⟨startA, acc⟩) >>= iterate sumDomainStep args k)).sumAcc = _
    rw [StateTransitionSpec.clientResult_bind, sumDomainStep_state, sumDomainStep_result]
    have hev : (Memory.spec 0).clientResult s (evalBucketProd
        ⟨args.dom, args.x, startA, args.outPtr, args.outLen, args.idx,
          args.bucketPtr, args.bucketLen⟩) = term startA :=
      evalBucketProd_result hout hout_len hb hlen
    rw [hev, ih (startA + 1) _, Finset.sum_range_succ']
    have hshift : (∑ i ∈ Finset.range k, term (startA + 1 + i)) =
        ∑ i ∈ Finset.range k, term (startA + (i + 1)) :=
      Finset.sum_congr rfl fun i _ => congrArg term (by omega)
    rw [hshift, Nat.add_zero]
    ring

theorem sumDomainValues_realizes :
    Realizes .exact sumDomainValues WordEncoding.encode WordEncoding.encode
      (fun w args s =>
        0 < args.dom ∧ Fits w 1 ∧
        args.outPtr + args.outLen ≤ s.frontier ∧
        ∃ bucket B maxScope,
          bucket.length = args.bucketLen ∧
          HoldsFactorList args.bucketPtr bucket s ∧
          (∀ f ∈ bucket, f.scope.length ≤ maxScope) ∧
          Fits w (args.dom ^ maxScope) ∧
          args.dom * (bucket.map capFactor).prod ≤ B ∧
          Fits w B)
      (fun _ _ => 0) := by
  unfold sumDomainValues
  realize [evalBucketProd_realizes]
  obtain ⟨hdom, h1, hout, bucket, B, maxScope, hblen, hbf, hmax, hdomPow, hcapB, hB⟩ := h
  refine iterationSafe_of_stepInv _ _ w d
    (fun j st t => t = s ∧ st.curA + j = d.dom ∧ st.sumAcc ≤ st.curA * (bucket.map capFactor).prod)
    (fun j st t ⟨ht, hcurA, hsum⟩ => ?_)
    ⟨rfl, by simp, by simp⟩
  subst t
  dsimp only
  have h1_prod : 1 ≤ (bucket.map capFactor).prod :=
    List.one_le_prod_of_one_le (by simp [one_le_capFactor])
  have hprod_le_B : (bucket.map capFactor).prod ≤ B := (Nat.le_mul_of_pos_left _ hdom).trans hcapB
  have hcurA_fit : Fits w (st.curA + 1) := hB.of_le
    ((show st.curA + 1 ≤ d.dom by omega).trans ((Nat.le_mul_of_pos_right _ h1_prod).trans hcapB))
  have hp := evalBucketProd_le_cap
    (args := ⟨d.dom, d.x, st.curA, d.outPtr, d.outLen, d.idx, d.bucketPtr, d.bucketLen⟩) hbf hblen
  have hsum_next : st.sumAcc + (Memory.spec 0).clientResult s (evalBucketProd
      ⟨d.dom, d.x, st.curA, d.outPtr, d.outLen, d.idx, d.bucketPtr, d.bucketLen⟩) ≤
      (st.curA + 1) * (bucket.map capFactor).prod := (Nat.add_le_add hsum hp).trans_eq (by ring)
  have hsum_B : (st.curA + 1) * (bucket.map capFactor).prod ≤ B :=
    (Nat.mul_le_mul_right _ (by omega : st.curA + 1 ≤ d.dom)).trans hcapB
  refine ⟨?_, ?_⟩
  · exact ⟨⟨hdom, by omega, h1, hout, bucket, B, maxScope, hblen, hbf, hmax, hdomPow,
      hprod_le_B, hB⟩, hcurA_fit, hB.of_le (hsum_next.trans hsum_B)⟩
  · rw [sumDomainStep_state, sumDomainStep_result]
    exact ⟨rfl, by dsimp only; omega, hsum_next⟩

end Cslib.Algorithms.WordRAM.VariableElimination
