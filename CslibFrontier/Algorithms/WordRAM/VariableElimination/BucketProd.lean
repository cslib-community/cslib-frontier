/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.VariableElimination.Horner
import CslibFrontier.Tactic.Realize

/-!
# Bucket Product Evaluation (`evalBucketProd`)

Multiplies the entries of all factor tables in a bucket at a fixed assignment to `outScope` and the
eliminated variable `x`, preserving overflow bounds via `capFactor`.

## Main definitions

* `Cslib.Algorithms.WordRAM.VariableElimination.evalBucketProd`: bucket-product `Memory.Prog`.
-/

public section

namespace Cslib.Algorithms.WordRAM.VariableElimination

open Cslib.Logic.PL Cslib.Logic.PL.CSP
open Cslib.Algorithms.Lean.CSP
open Cslib.DataStructure
open Cslib.WordRAM
open Cslib.WordRAM.Realization

/-! ### Bucket product evaluation (`evalBucketProd`) -/

/-- Arguments for multiplying all bucket factors at one assignment. -/
structure BucketProdArgs where
  /-- Field `dom` of `BucketProdArgs`. -/
  dom : ℕ
  /-- Field `x` of `BucketProdArgs`. -/
  x : ℕ
  /-- Field `a` of `BucketProdArgs`. -/
  a : ℕ
  /-- Field `outPtr` of `BucketProdArgs`. -/
  outPtr : ℕ
  /-- Field `outLen` of `BucketProdArgs`. -/
  outLen : ℕ
  /-- Field `idx` of `BucketProdArgs`. -/
  idx : ℕ
  /-- Field `bucketPtr` of `BucketProdArgs`. -/
  bucketPtr : ℕ
  /-- Field `bucketLen` of `BucketProdArgs`. -/
  bucketLen : ℕ

/-- Product equivalence encoding `BucketProdArgs` as words. -/
@[expose] def BucketProdArgs.equiv :
    BucketProdArgs ≃ ((((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ where
  toFun s := (((((((s.dom, s.x), s.a), s.outPtr), s.outLen), s.idx), s.bucketPtr), s.bucketLen)
  invFun := fun (((((((dom, x), a), outPtr), outLen), idx), bucketPtr), bucketLen) =>
    ⟨dom, x, a, outPtr, outLen, idx, bucketPtr, bucketLen⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : WordEncoding BucketProdArgs := .ofEquiv BucketProdArgs.equiv

private structure BucketProdState where
  curDesc : ℕ
  prod : ℕ

private def BucketProdState.equiv : BucketProdState ≃ ℕ × ℕ where
  toFun s := (s.curDesc, s.prod)
  invFun := fun (curDesc, prod) => ⟨curDesc, prod⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding BucketProdState := .ofEquiv BucketProdState.equiv

private def bucketProdStep (p : EvalScopeEnv × BucketProdState) : Memory.Prog BucketProdState :=
  Memory.read p.2.curDesc >>= fun scopePtr =>
  Memory.read (p.2.curDesc + 1) >>= fun scopeLen =>
  Memory.read (p.2.curDesc + 2) >>= fun entriesPtr =>
  Memory.read (p.2.curDesc + 3) >>= fun entriesLen =>
  evalScopeIdx ⟨p.1.dom, p.1.x, p.1.a, p.1.outPtr, p.1.outLen, p.1.idx, scopePtr, scopeLen⟩ >>=
    fun fIdx =>
    (if fIdx < entriesLen then Memory.read (entriesPtr + fIdx) else pure 0) >>= fun entry =>
      pure ⟨p.2.curDesc + 4, p.2.prod * entry⟩

/-- Evaluate the product of all factor tables in a bucket at one assignment. -/
def evalBucketProd (args : BucketProdArgs) : Memory.Prog ℕ := do
  let res ← iterate bucketProdStep
    ⟨args.dom, args.x, args.a, args.outPtr, args.outLen, args.idx⟩
    args.bucketLen ⟨args.bucketPtr, 1⟩
  pure res.prod

private theorem bucketProdStep_state (env : EvalScopeEnv) (st : BucketProdState)
    (s : Memory.State) :
    (Memory.spec 0).clientState s (bucketProdStep (env, st)) = s := by
  unfold bucketProdStep
  rw [clientState_bind_read, clientState_bind_read, clientState_bind_read, clientState_bind_read,
    StateTransitionSpec.clientState_bind, evalScopeIdx_state, StateTransitionSpec.clientState_bind]
  split_ifs <;> rfl

theorem evalBucketProd_state (args : BucketProdArgs) (s : Memory.State) :
    (Memory.spec 0).clientState s (evalBucketProd args) = s := by
  unfold evalBucketProd
  rw [StateTransitionSpec.clientState_bind]
  exact clientState_iterate_eq_of bucketProdStep _ (bucketProdStep_state _) args.bucketLen _ s

private theorem bucketProdStep_result (env : EvalScopeEnv) (st : BucketProdState)
    (s : Memory.State) :
    (Memory.spec 0).clientResult s (bucketProdStep (env, st)) =
      let fIdx := (Memory.spec 0).clientResult s (evalScopeIdx
        ⟨env.dom, env.x, env.a, env.outPtr, env.outLen, env.idx,
          s.mem st.curDesc, s.mem (st.curDesc + 1)⟩)
      let entry := if fIdx < s.mem (st.curDesc + 3) then s.mem (s.mem (st.curDesc + 2) + fIdx)
        else 0
      ⟨st.curDesc + 4, st.prod * entry⟩ := by
  unfold bucketProdStep
  dsimp only
  rw [clientResult_bind_read, clientResult_bind_read, clientResult_bind_read,
    clientResult_bind_read, StateTransitionSpec.clientResult_bind, evalScopeIdx_state,
    StateTransitionSpec.clientResult_bind]
  split_ifs <;> rfl

theorem evalBucketProd_cost {args : BucketProdArgs} {bucket : List (FactorTable ℕ ℕ)}
    {maxScope : ℕ} {s : Memory.State}
    (hb : HoldsFactorList args.bucketPtr bucket s) (hlen : bucket.length = args.bucketLen)
    (hmax : ∀ f ∈ bucket, f.scope.length ≤ maxScope) :
    memoryCost (evalBucketProd args) s ≤ args.bucketLen * (5 + maxScope * (args.outLen + 1)) := by
  unfold evalBucketProd
  rw [memoryCost_bind', memoryCost_pure, Nat.add_zero, ← hlen]
  let env : EvalScopeEnv := ⟨args.dom, args.x, args.a, args.outPtr, args.outLen, args.idx⟩
  suffices ∀ (fs : List (FactorTable ℕ ℕ)) (cur prod : ℕ),
      HoldsFactorList cur fs s → (∀ f ∈ fs, f.scope.length ≤ maxScope) →
      memoryCost (iterate bucketProdStep env fs.length ⟨cur, prod⟩) s ≤
        fs.length * (5 + maxScope * (args.outLen + 1)) from
    this bucket args.bucketPtr 1 hb hmax
  intro fs
  induction fs with
  | nil => intro _ _ _ _; simp [iterate]
  | cons f rest ih =>
    intro cur prod ⟨hf, hrest⟩ hmax_fs
    have hstep_cost : memoryCost (bucketProdStep (env, ⟨cur, prod⟩)) s ≤
        5 + maxScope * (args.outLen + 1) := by
      unfold bucketProdStep
      dsimp only [env]
      rw [memoryCost_bind', memoryCost_read, clientState_read, clientResult_read,
        memoryCost_bind', memoryCost_read, clientState_read, clientResult_read,
        memoryCost_bind', memoryCost_read, clientState_read, clientResult_read,
        memoryCost_bind', memoryCost_read, clientState_read, clientResult_read,
        memoryCost_bind', evalScopeIdx_state, memoryCost_bind']
      have hev := evalScopeIdx_cost ⟨args.dom, args.x, args.a, args.outPtr, args.outLen, args.idx,
        s.mem cur, s.mem (cur + 1)⟩ s
      dsimp only at hev
      have hsc_le : s.mem (cur + 1) * (args.outLen + 1) ≤ maxScope * (args.outLen + 1) := by
        rw [hf.2.1]
        exact Nat.mul_le_mul_right _ (hmax_fs f (List.mem_cons_self ..))
      split_ifs <;> simp only [memoryCost_read, memoryCost_pure] <;> omega
    rw [List.length_cons, iterate, memoryCost_bind', bucketProdStep_state, bucketProdStep_result]
    refine (Nat.add_le_add hstep_cost
      (ih (cur + 4) _ hrest fun g hg => hmax_fs g (List.mem_cons_of_mem f hg))).trans ?_
    rw [Nat.add_one_mul]
    omega

theorem evalBucketProd_valid {w : ℕ} {args : BucketProdArgs}
    {bucket : List (FactorTable ℕ ℕ)} {s : Memory.State}
    (hout : args.outPtr + args.outLen ≤ s.frontier)
    (hb : HoldsFactorList args.bucketPtr bucket s) (hlen : bucket.length = args.bucketLen) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (evalBucketProd args)) := by
  unfold evalBucketProd
  refine validHistory_bind_step ?_ (validHistory_pure w _ _)
  rw [← hlen]
  let env : EvalScopeEnv := ⟨args.dom, args.x, args.a, args.outPtr, args.outLen, args.idx⟩
  suffices ∀ (fs : List (FactorTable ℕ ℕ)) (cur prod : ℕ), HoldsFactorList cur fs s →
      (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s (iterate bucketProdStep env fs.length ⟨cur, prod⟩)) from
    this bucket args.bucketPtr 1 hb
  intro fs
  induction fs with
  | nil => intro _ _ _; exact validHistory_pure w s _
  | cons f rest ih =>
    intro cur prod ⟨⟨hd, hsl, hel, hsc, hent⟩, hrest⟩
    have hstep : (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s (bucketProdStep (env, ⟨cur, prod⟩))) := by
      unfold bucketProdStep
      dsimp only [env]
      refine validHistory_read_bind (by omega) (validHistory_read_bind (by omega)
        (validHistory_read_bind (by omega) (validHistory_read_bind (by omega) ?_)))
      refine validHistory_bind_step
        (evalScopeIdx_valid _ hout (by dsimp only; rw [hsl]; exact hsc.1)) ?_
      rw [evalScopeIdx_state]
      refine validHistory_bind_step ?_ (validHistory_pure w _ _)
      split_ifs with hlt
      · have hent_le : s.mem (cur + 2) + s.mem (cur + 3) ≤ s.frontier := by
          simpa [hel] using hent.1
        exact validHistory_read (by omega)
      · exact validHistory_pure w s _
    rw [List.length_cons, iterate, validHistory_bind', bucketProdStep_state, bucketProdStep_result]
    exact ⟨hstep, ih (cur + 4) _ hrest⟩

theorem evalBucketProd_result {args : BucketProdArgs} {outScope : List ℕ}
    {bucket : List (FactorTable ℕ ℕ)} {s : Memory.State}
    (hout : Block.HoldsList args.outPtr outScope s.mem) (hout_len : outScope.length = args.outLen)
    (hb : HoldsFactorList args.bucketPtr bucket s) (hlen : bucket.length = args.bucketLen) :
    (Memory.spec 0).clientResult s (evalBucketProd args) =
      (bucket.map fun f => f.evalAt args.dom fun v =>
        if v = args.x then args.a
        else assignScope outScope (lsbDecode args.dom outScope.length args.idx) v).prod := by
  unfold evalBucketProd
  rw [StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientResult_pure, ← hlen]
  let env : EvalScopeEnv := ⟨args.dom, args.x, args.a, args.outPtr, args.outLen, args.idx⟩
  let σ : ℕ → ℕ := fun v =>
    if v = args.x then args.a
    else assignScope outScope (lsbDecode args.dom outScope.length args.idx) v
  suffices ∀ (fs : List (FactorTable ℕ ℕ)) (cur prod : ℕ), HoldsFactorList cur fs s →
      ((Memory.spec 0).clientResult s (iterate bucketProdStep env fs.length ⟨cur, prod⟩)).prod =
      prod * (fs.map fun f => f.evalAt args.dom σ).prod by
    simpa [env, σ] using this bucket args.bucketPtr 1 hb
  intro fs
  induction fs with
  | nil => intro cur prod _; change prod = prod * 1; simp
  | cons f rest ih =>
    intro cur prod ⟨⟨hd, hsl, hel, hsc, hent⟩, hrest⟩
    rw [List.length_cons, iterate, StateTransitionSpec.clientResult_bind, bucketProdStep_state,
      bucketProdStep_result]
    have hentry : (if Nat.ofDigits args.dom (f.scope.map σ) < s.mem (cur + 3) then
        s.mem (s.mem (cur + 2) + Nat.ofDigits args.dom (f.scope.map σ)) else 0) =
        f.evalAt args.dom σ := by
      rw [hel, FactorTable.evalAt, Array.getD]
      split_ifs with hlt
      · exact (hent.2.get _ (Array.length_toList ▸ hlt)).trans (Array.getElem_toList _)
      · rfl
    dsimp only [env]
    rw [evalScopeIdx_result hout hout_len hsc.2 hsl.symm, hentry, ih (cur + 4) _ hrest,
      List.map_cons, List.prod_cons, Nat.mul_assoc]

theorem evalBucketProd_realizes :
    Realizes .exact evalBucketProd WordEncoding.encode WordEncoding.encode
      (fun w args s =>
        0 < args.dom ∧ args.a < args.dom ∧ Fits w 1 ∧
        args.outPtr + args.outLen ≤ s.frontier ∧
        ∃ bucket B maxScope,
          bucket.length = args.bucketLen ∧
          HoldsFactorList args.bucketPtr bucket s ∧
          (∀ f ∈ bucket, f.scope.length ≤ maxScope) ∧
          Fits w (args.dom ^ maxScope) ∧
          (bucket.map capFactor).prod ≤ B ∧
          Fits w B)
      (fun _ _ => 0) := by
  unfold evalBucketProd
  realize [evalScopeIdx_realizes]
  · exact h.2.2.1
  · obtain ⟨hdom, ha, h1, hout, bucket, B, maxScope, hblen, hbf, hmax, hdomPow, hcapB, hB⟩ := h
    refine iterationSafe_of_stepInv _ _ w d
      (fun j st t => t = s ∧ ∃ rem, rem.length = j ∧ HoldsFactorList st.curDesc rem s ∧
        (∀ f ∈ rem, f.scope.length ≤ maxScope) ∧ st.prod * (rem.map capFactor).prod ≤ B)
      (fun j st t ⟨ht, rem, hrem_len, hrem_holds, hrem_max, hprod_le⟩ => ?_)
      ⟨rfl, bucket, hblen, hbf, hmax, by simpa using hcapB⟩
    subst t
    dsimp only
    rcases rem with _ | ⟨f, rem'⟩
    · simp at hrem_len
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hrem_len
    obtain ⟨hf, hrem'_holds⟩ := hrem_holds
    have hent_le : ∀ fIdx,
        (if fIdx < s.mem (st.curDesc + 3) then s.mem (s.mem (st.curDesc + 2) + fIdx) else 0) ≤
          capFactor f := holdsFactor_read_entry_le hf
    have hprod_cap : st.prod * capFactor f * (rem'.map capFactor).prod ≤ B := by
      simpa [List.map_cons, List.prod_cons, Nat.mul_assoc] using hprod_le
    have hprod_f : st.prod * capFactor f ≤ B :=
      (Nat.le_mul_of_pos_right _ (List.one_le_prod_of_one_le (l := rem'.map capFactor)
        (by simp [one_le_capFactor]))).trans hprod_cap
    obtain ⟨hd, hsl, hel, hsc, hent⟩ := hf
    have hpow_f : Fits w (d.dom ^ s.mem (st.curDesc + 1)) :=
      hsl ▸ hdomPow.of_le (Nat.pow_le_pow_right hdom (hrem_max f (List.mem_cons_self ..)))
    refine ⟨⟨hmem.frontier_fits.of_le (by omega), hmem.frontier_fits.of_le (by omega),
      hmem.frontier_fits.of_le (by omega), ⟨hdom, ha, h1, hmem.frontier_fits.of_le hout,
        hmem.frontier_fits.of_le (by rw [hsl]; exact hsc.1), hpow_f⟩, ?_⟩, ?_⟩
    · rw [evalScopeIdx_state]
      generalize (Memory.spec 0).clientResult s (evalScopeIdx _) = fIdx
      have he := hent_le fIdx
      split_ifs with hlt
      · rw [ite_eq_left hlt] at he
        have hent_sz : s.mem (st.curDesc + 2) + s.mem (st.curDesc + 3) ≤ s.frontier := by
          simpa [hel] using hent.1
        exact ⟨hmem.frontier_fits.of_le (by omega), hmem.frontier_fits.of_le hd,
          hB.of_le ((Nat.mul_le_mul_left st.prod he).trans hprod_f)⟩
      · exact ⟨trivial, hmem.frontier_fits.of_le hd, Nat.mul_zero st.prod ▸ fits_zero w⟩
    · rw [bucketProdStep_state, bucketProdStep_result]
      exact ⟨rfl, rem', hrem_len, hrem'_holds, fun g hg => hrem_max g (List.mem_cons_of_mem f hg),
        (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left st.prod (hent_le _))).trans hprod_cap⟩

theorem evalBucketProd_le_cap {args : BucketProdArgs} {bucket : List (FactorTable ℕ ℕ)}
    {s : Memory.State} (hb : HoldsFactorList args.bucketPtr bucket s)
    (hlen : bucket.length = args.bucketLen) :
    (Memory.spec 0).clientResult s (evalBucketProd args) ≤ (bucket.map capFactor).prod := by
  unfold evalBucketProd
  rw [StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientResult_pure, ← hlen]
  let env : EvalScopeEnv := ⟨args.dom, args.x, args.a, args.outPtr, args.outLen, args.idx⟩
  suffices ∀ (fs : List (FactorTable ℕ ℕ)) (cur prod : ℕ), HoldsFactorList cur fs s →
      ((Memory.spec 0).clientResult s (iterate bucketProdStep env fs.length ⟨cur, prod⟩)).prod ≤
      prod * (fs.map capFactor).prod by
    simpa [env] using this bucket args.bucketPtr 1 hb
  intro fs
  induction fs with
  | nil => intro cur prod _; change prod ≤ prod * 1; simp
  | cons f rest ih =>
    intro cur prod ⟨hf, hrest⟩
    rw [List.length_cons, iterate, StateTransitionSpec.clientResult_bind, bucketProdStep_state,
      bucketProdStep_result]
    dsimp only [env]
    have he := holdsFactor_read_entry_le hf ((Memory.spec 0).clientResult s (evalScopeIdx
      ⟨args.dom, args.x, args.a, args.outPtr, args.outLen, args.idx,
        s.mem cur, s.mem (cur + 1)⟩))
    calc ((Memory.spec 0).clientResult s (iterate bucketProdStep env rest.length _)).prod
        ≤ (prod * _) * (rest.map capFactor).prod := ih (cur + 4) _ hrest
      _ ≤ (prod * capFactor f) * (rest.map capFactor).prod :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left prod he)
      _ = prod * ((f :: rest).map capFactor).prod := by
          simp [List.map_cons, List.prod_cons, Nat.mul_assoc]

end Cslib.Algorithms.WordRAM.VariableElimination
