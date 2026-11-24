/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.VariableElimination.Horner
import CslibFrontier.Foundations.Data.List.FoldMax
import CslibFrontier.Tactic.Realize
import Mathlib.Algebra.Order.BigOperators.Group.List

/-!
# Final Scalar-Table Product (`finalResultProd`)

Multiplies the constant (`index 0`) entry of each remaining factor table after eliminating all
ordered variables, yielding `ElimState.result`. Independent of `BuildEntries`, `Partition`,
`OutScope`, `ElimVar`, and `ElimLoop`.

## Main definitions

* `Cslib.Algorithms.WordRAM.VariableElimination.finalResultProd`: final scalar product program.
-/

public section

namespace Cslib.Algorithms.WordRAM.VariableElimination

open Cslib.Logic.PL Cslib.Logic.PL.CSP
open Cslib.Algorithms.Lean.CSP
open Cslib.DataStructure
open Cslib.WordRAM
open Cslib.WordRAM.Realization

/-! ### Final scalar-table product (`finalResultProd`) and factor parsing (`initFactors`) -/

private theorem getD_zero_le_capFactor (f : FactorTable ℕ ℕ) :
    f.entries.getD 0 0 ≤ capFactor f := by
  unfold Array.getD capFactor
  split_ifs with h0
  · refine le_trans ?_ (le_max_right 1 _)
    have hmem : f.entries[0] ∈ f.entries.toList := by
      rw [← Array.getElem_toList (xs := f.entries) (i := 0) (by simpa using h0)]
      exact List.getElem_mem _
    exact List.mem_le_foldl_max hmem
  · omega

/-- Arguments `(livePtr, liveLen)` for `finalResultProd`. -/
structure FinalProdArgs where
  /-- Field `livePtr` of `FinalProdArgs`. -/
  livePtr : ℕ
  /-- Field `liveLen` of `FinalProdArgs`. -/
  liveLen : ℕ
  /-- Field `scalar` of `FinalProdArgs`. -/
  scalar : ℕ

/-- Product equivalence encoding `FinalProdArgs` as words. -/
@[expose] def FinalProdArgs.equiv : FinalProdArgs ≃ (ℕ × ℕ) × ℕ where
  toFun a := ((a.livePtr, a.liveLen), a.scalar)
  invFun := fun ((livePtr, liveLen), scalar) => ⟨livePtr, liveLen, scalar⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : WordEncoding FinalProdArgs := .ofEquiv FinalProdArgs.equiv

private def finalProdStep : Unit × (ℕ × ℕ) → Memory.Prog (ℕ × ℕ) :=
  fun ⟨_, (curDesc, acc)⟩ =>
    Memory.read (curDesc + 2) >>= fun enPtr =>
    Memory.read (curDesc + 3) >>= fun enLen =>
    (if enLen = 0 then pure 0 else Memory.read enPtr) >>= fun e0 =>
    pure (curDesc + 4, acc * e0)

/-- Multiply the `0`-th entries of all final scalar factor tables. -/
def finalResultProd (args : FinalProdArgs) : Memory.Prog ℕ :=
  iterate finalProdStep () args.liveLen (args.livePtr, args.scalar) >>= fun res =>
  pure res.2

private theorem finalResultProd_aux {w B : ℕ} (hB : Fits w B) {s : Memory.State} :
    ∀ (rem : List (FactorTable ℕ ℕ)) (cur acc : ℕ),
      HoldsFactorList cur rem s →
      acc * (rem.map capFactor).prod ≤ B →
      let p := iterate finalProdStep () rem.length (cur, acc)
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s p) ∧
        (Memory.spec 0).clientState s p = s ∧
        ((Memory.spec 0).clientResult s p).2 =
          acc * (rem.map fun f => f.entries.getD 0 0).prod ∧
        memoryCost p s ≤ 3 * rem.length
  | [], cur, acc, _, _ => by
      dsimp only
      have h0 : iterate finalProdStep () 0 (cur, acc) = pure (cur, acc) := rfl
      simp only [List.length_nil]
      rw [h0]
      exact ⟨validHistory_pure w s _, rfl,
        by simp only [List.map_nil, List.prod_nil, Nat.mul_one]; rfl,
        by simp [memoryCost_pure]⟩
  | f :: rest, cur, acc, ⟨hf, hrest⟩, hcap => by
      dsimp only
      obtain ⟨hd, _, hel, _, hent⟩ := hf
      simp only [List.map_cons, List.prod_cons] at hcap ⊢
      have he0_le : f.entries.getD 0 0 ≤ capFactor f := getD_zero_le_capFactor f
      have hcap' : (acc * f.entries.getD 0 0) * (rest.map capFactor).prod ≤ B := by
        calc (acc * f.entries.getD 0 0) * (rest.map capFactor).prod
            ≤ (acc * capFactor f) * (rest.map capFactor).prod :=
              Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ he0_le)
          _ = acc * (capFactor f * (rest.map capFactor).prod) := Nat.mul_assoc _ _ _
          _ ≤ B := hcap
      obtain ⟨hih_val, hih_st, hih_res, hih_cost⟩ :=
        finalResultProd_aux hB rest (cur + 4) (acc * f.entries.getD 0 0) hrest hcap'
      have hr_st (addr : ℕ) : (Memory.spec 0).clientState s (Memory.read addr) = s := rfl
      have hr_res (addr : ℕ) : (Memory.spec 0).clientResult s (Memory.read addr) = s.mem addr := rfl
      have hpure_st {α : Type} (x : α) (u : Memory.State) :
          (Memory.spec 0).clientState u (pure x) = u := rfl
      have hpure_res {α : Type} (x : α) (u : Memory.State) :
          (Memory.spec 0).clientResult u (pure x) = x := rfl
      have hbr_spec :
          let br : Memory.Prog ℕ :=
            if s.mem (cur + 3) = 0 then pure 0 else Memory.read (s.mem (cur + 2))
          (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s br) ∧
            (Memory.spec 0).clientState s br = s ∧
            (Memory.spec 0).clientResult s br = f.entries.getD 0 0 ∧
            memoryCost br s ≤ 1 := by
        dsimp only
        by_cases hz : s.mem (cur + 3) = 0
        · rw [ite_eq_left hz]
          have hsz0 : ¬ (0 < f.entries.size) := by omega
          have hget0 : f.entries.getD 0 0 = 0 := by simp [Array.getD, hsz0]
          exact ⟨validHistory_pure w s 0, rfl, hget0.symm, by rw [memoryCost_pure]; omega⟩
        · rw [ite_eq_right hz]
          have hsz_pos : 0 < f.entries.size := by omega
          have hlt_fr : s.mem (cur + 2) < s.frontier := by
            have hbd := hent.1
            rw [Array.length_toList] at hbd
            omega
          have hmem0 : s.mem (s.mem (cur + 2)) = f.entries.getD 0 0 := by
            have h0 := hent.2.get 0 (by rw [Array.length_toList]; exact hsz_pos)
            simp only [Nat.add_zero, Array.getElem_toList] at h0
            simp only [Array.getD, hsz_pos, ↓reduceDIte]
            exact h0
          exact ⟨validHistory_read hlt_fr, rfl, hmem0, by rw [memoryCost_read]⟩
      obtain ⟨hbr_val, hbr_st, hbr_res, hbr_cost⟩ := hbr_spec
      have hstep_val : (Memory.spec w).ValidHistory s
          ((Memory.spec w).clientHistory s (finalProdStep ((), (cur, acc)))) := by
        unfold finalProdStep
        dsimp only
        refine validHistory_read_bind (by omega) ?_
        refine validHistory_read_bind (by omega) ?_
        exact validHistory_bind_step hbr_val (validHistory_pure w _ _)
      have hstep_st : (Memory.spec 0).clientState s (finalProdStep ((), (cur, acc))) = s := by
        unfold finalProdStep
        dsimp only
        rw [StateTransitionSpec.clientState_bind, hr_st, hr_res,
          StateTransitionSpec.clientState_bind, hr_st, hr_res,
          StateTransitionSpec.clientState_bind, hbr_st, hbr_res, hpure_st]
      have hstep_res : (Memory.spec 0).clientResult s (finalProdStep ((), (cur, acc))) =
          (cur + 4, acc * f.entries.getD 0 0) := by
        unfold finalProdStep
        dsimp only
        rw [StateTransitionSpec.clientResult_bind, hr_st, hr_res,
          StateTransitionSpec.clientResult_bind, hr_st, hr_res,
          StateTransitionSpec.clientResult_bind, hbr_st, hbr_res, hpure_res]
      have hstep_cost : memoryCost (finalProdStep ((), (cur, acc))) s ≤ 3 := by
        unfold finalProdStep
        dsimp only
        rw [memoryCost_bind', memoryCost_read, hr_st, hr_res,
          memoryCost_bind', memoryCost_read, hr_st, hr_res,
          memoryCost_bind', hbr_st, hbr_res, memoryCost_pure, Nat.add_zero]
        omega
      simp only [List.length_cons]
      have hiter_eq : iterate finalProdStep () (rest.length + 1) (cur, acc) =
          (finalProdStep ((), (cur, acc)) >>= iterate finalProdStep () rest.length) := rfl
      rw [hiter_eq, StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind,
        hstep_st, hstep_res, hih_st, hih_res, Nat.mul_assoc]
      refine ⟨validHistory_bind_step hstep_val ?_, rfl, rfl, ?_⟩
      · rw [hstep_st, hstep_res]; exact hih_val
      · rw [memoryCost_bind', hstep_st, hstep_res]; omega

theorem finalResultProd_spec {w B : ℕ} {args : FinalProdArgs}
    {es : ElimState ℕ ℕ} {s : Memory.State}
    (hB : Fits w B) (hcap : stateCap es ≤ B)
    (hsc : args.scalar = es.scalar) (hlen : args.liveLen = es.live.length)
    (hlive : HoldsFactorList args.livePtr es.live s) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (finalResultProd args)) ∧
      (Memory.spec 0).clientState s (finalResultProd args) = s ∧
      (Memory.spec 0).clientResult s (finalResultProd args) = es.result ∧
      memoryCost (finalResultProd args) s ≤ 3 * args.liveLen := by
  unfold finalResultProd
  rw [hlen, hsc]
  have hcap0 : es.scalar * (es.live.map capFactor).prod ≤ B :=
    (Nat.mul_le_mul_right _ (le_max_right 1 es.scalar)).trans hcap
  obtain ⟨hval, hst, hres, hcost⟩ := finalResultProd_aux hB es.live args.livePtr es.scalar
    hlive hcap0
  have hpure_st {α : Type} (x : α) (u : Memory.State) :
      (Memory.spec 0).clientState u (pure x) = u := rfl
  have hpure_res {α : Type} (x : α) (u : Memory.State) :
      (Memory.spec 0).clientResult u (pure x) = x := rfl
  rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind,
    hst, hpure_st, hpure_res, hres]
  refine ⟨validHistory_bind_step hval (by rw [hst]; exact validHistory_pure w s _),
    rfl, rfl, ?_⟩
  rw [memoryCost_bind', hst, memoryCost_pure, Nat.add_zero]
  exact hcost

theorem finalResultProd_realizes :
    Realizes .exact finalResultProd WordEncoding.encode WordEncoding.encode
      (fun w args s =>
        ∃ live B,
          Fits w 4 ∧
          live.length = args.liveLen ∧
          HoldsFactorList args.livePtr live s ∧
          args.scalar * (live.map capFactor).prod ≤ B ∧
          Fits w B)
      (fun _ _ => 0) := by
  unfold finalResultProd
  realize
  obtain ⟨live₀, B, h4, hlen₀, hlive₀, hcap₀, hB⟩ := h
  refine iterationSafe_of_stepInv _ _ w _
    (fun (j : ℕ) (st : ℕ × ℕ) (t : Memory.State) =>
      t = s ∧
      ∃ rem,
        rem.length = j ∧
        HoldsFactorList st.1 rem s ∧
        st.2 * (rem.map capFactor).prod ≤ B)
    (fun j st t ⟨ht_eq, rem, hrem_l, hrem_h, hcap_t⟩ => ?_)
    ⟨rfl, live₀, hlen₀, hlive₀, hcap₀⟩
  dsimp only
  rcases ht_eq.symm with rfl
  rcases rem with _ | ⟨f, rest⟩
  · cases hrem_l
  simp only [List.length_cons, Nat.add_right_cancel_iff] at hrem_l
  subst hrem_l
  obtain ⟨hf, hrest⟩ := hrem_h
  obtain ⟨hd, _, hel, _, hent⟩ := hf
  simp only [List.map_cons, List.prod_cons] at hcap_t
  have hr_st (addr : ℕ) : (Memory.spec 0).clientState s (Memory.read addr) = s := rfl
  have hr_res (addr : ℕ) : (Memory.spec 0).clientResult s (Memory.read addr) = s.mem addr := rfl
  have hpure_res {α : Type} (x : α) (u : Memory.State) :
      (Memory.spec 0).clientResult u (pure x) = x := rfl
  have hbr_eq :
      let br : Memory.Prog ℕ :=
        if s.mem (st.1 + 3) = 0 then pure 0 else Memory.read (s.mem (st.1 + 2))
      (Memory.spec 0).clientState s br = s ∧
        (Memory.spec 0).clientResult s br = f.entries.getD 0 0 := by
    dsimp only
    by_cases hz : s.mem (st.1 + 3) = 0
    · rw [ite_eq_left hz]
      have hsz0 : ¬ (0 < f.entries.size) := by omega
      have hget0 : f.entries.getD 0 0 = 0 := by simp [Array.getD, hsz0]
      exact ⟨rfl, hget0.symm⟩
    · rw [ite_eq_right hz]
      have hsz_pos : 0 < f.entries.size := by omega
      have h0 := hent.2.get 0 (by rw [Array.length_toList]; exact hsz_pos)
      simp only [Nat.add_zero, Array.getElem_toList] at h0
      simp only [Array.getD, hsz_pos, ↓reduceDIte]
      exact ⟨rfl, h0⟩
  obtain ⟨hbr_st, hbr_res⟩ := hbr_eq
  have he0_le : f.entries.getD 0 0 ≤ capFactor f := getD_zero_le_capFactor f
  have hcap' : (st.2 * f.entries.getD 0 0) * (rest.map capFactor).prod ≤ B := by
    calc (st.2 * f.entries.getD 0 0) * (rest.map capFactor).prod
        ≤ (st.2 * capFactor f) * (rest.map capFactor).prod :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ he0_le)
      _ = st.2 * (capFactor f * (rest.map capFactor).prod) := Nat.mul_assoc _ _ _
      _ ≤ B := hcap_t
  have hprod_le : st.2 * f.entries.getD 0 0 ≤ B := by
    have h1_rest : 1 ≤ (rest.map capFactor).prod :=
      List.one_le_prod_of_one_le (by simp [one_le_capFactor])
    exact (Nat.le_mul_of_pos_right _ h1_rest).trans hcap'
  refine ⟨?_, ?_⟩
  · refine ⟨hmem.frontier_fits.of_le (by omega), hmem.frontier_fits.of_le (by omega), ?_, ?_⟩
    · split_ifs
    · rw [hbr_res]
      exact ⟨hmem.frontier_fits.of_le (by omega), hB.of_le hprod_le⟩
  · unfold finalProdStep
    dsimp only
    rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind,
      hr_st, hr_res,
      StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind,
      hr_st, hr_res,
      StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind,
      hbr_st, hbr_res, hpure_res]
    exact ⟨rfl, rest, rfl, hrest, hcap'⟩

end Cslib.Algorithms.WordRAM.VariableElimination
