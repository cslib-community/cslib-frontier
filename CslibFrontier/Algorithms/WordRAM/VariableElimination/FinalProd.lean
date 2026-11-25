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

private theorem mul_getD_zero_le {acc B : ℕ} {f : FactorTable ℕ ℕ}
    {rest : List (FactorTable ℕ ℕ)} (h : acc * (capFactor f * (rest.map capFactor).prod) ≤ B) :
    acc * f.entries.getD 0 0 * (rest.map capFactor).prod ≤ B :=
  (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (getD_zero_le_capFactor f))).trans
    ((Nat.mul_assoc _ _ _).trans_le h)

/-- The conditional entry-`0` read of `finalProdStep` on a descriptor for `f`. -/
private theorem finalProdBranch_spec {w cur : ℕ} {f : FactorTable ℕ ℕ} {s : Memory.State}
    (hf : HoldsFactor cur f s) :
    let br : Memory.Prog ℕ :=
      if s.mem (cur + 3) = 0 then pure 0 else Memory.read (s.mem (cur + 2))
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s br) ∧
      (Memory.spec 0).clientState s br = s ∧
      (Memory.spec 0).clientResult s br = f.entries.getD 0 0 ∧
      memoryCost br s ≤ 1 := by
  obtain ⟨-, -, hel, -, hent⟩ := hf
  dsimp only
  by_cases hz : s.mem (cur + 3) = 0
  · rw [ite_eq_left hz]
    have hsz0 : ¬ (0 < f.entries.size) := by omega
    exact ⟨validHistory_pure w s 0, rfl, (by simp [Array.getD, hsz0] : f.entries.getD 0 0 = 0).symm,
      by rw [memoryCost_pure]; omega⟩
  · rw [ite_eq_right hz]
    have hsz_pos : 0 < f.entries.size := by omega
    have hbd := hent.1
    rw [Array.length_toList] at hbd
    have h0 := hent.2.get 0 (by rw [Array.length_toList]; exact hsz_pos)
    simp only [Nat.add_zero, Array.getElem_toList] at h0
    refine ⟨validHistory_read (by omega), rfl, ?_, (memoryCost_read _ _).le⟩
    change s.mem (s.mem (cur + 2)) = _
    simp only [Array.getD, hsz_pos, ↓reduceDIte]
    exact h0

private theorem finalProdStep_spec {w cur acc : ℕ} {f : FactorTable ℕ ℕ} {s : Memory.State}
    (hf : HoldsFactor cur f s) :
    let p := finalProdStep ((), (cur, acc))
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s p) ∧
      (Memory.spec 0).clientState s p = s ∧
      (Memory.spec 0).clientResult s p = (cur + 4, acc * f.entries.getD 0 0) ∧
      memoryCost p s ≤ 3 := by
  obtain ⟨hv, hst, hres, hcost⟩ := finalProdBranch_spec (w := w) hf
  have hd := hf.1
  unfold finalProdStep
  dsimp only at hv hst hres hcost ⊢
  rw [clientState_bind_read, clientState_bind_read, clientResult_bind_read, clientResult_bind_read,
    StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind, hst, hres,
    memoryCost_bind', memoryCost_read, clientState_read, clientResult_read, memoryCost_bind',
    memoryCost_read, clientState_read, clientResult_read, memoryCost_bind', hst, hres]
  exact ⟨validHistory_read_bind (by omega) (validHistory_read_bind (by omega)
    (validHistory_bind_step hv (by rw [hst]; exact validHistory_pure _ _ _))), rfl, rfl,
    by rw [memoryCost_pure]; omega⟩

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
  | [], _, acc, _, _ => by
      simp only [List.length_nil, List.map_nil, List.prod_nil, Nat.mul_one, Nat.mul_zero]
      exact ⟨validHistory_pure w s _, rfl, rfl, (memoryCost_pure _ _).le⟩
  | f :: rest, cur, acc, ⟨hf, hrest⟩, hcap => by
      simp only [List.map_cons, List.prod_cons] at hcap ⊢
      obtain ⟨hv, hst, hres, hcost⟩ := finalProdStep_spec (w := w) (acc := acc) hf
      obtain ⟨hv', hst', hres', hcost'⟩ :=
        finalResultProd_aux hB rest (cur + 4) _ hrest (mul_getD_zero_le hcap)
      rw [List.length_cons, iterate, StateTransitionSpec.clientState_bind,
        StateTransitionSpec.clientResult_bind, memoryCost_bind', hst, hres, hst', hres',
        Nat.mul_assoc]
      exact ⟨validHistory_bind_step hv (by rwa [hst, hres]), rfl, rfl, by omega⟩

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
  obtain ⟨hval, hst, hres, hcost⟩ := finalResultProd_aux hB es.live args.livePtr es.scalar
    hlive ((Nat.mul_le_mul_right _ (le_max_right 1 es.scalar)).trans hcap)
  rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind, hst,
    StateTransitionSpec.clientState_pure, StateTransitionSpec.clientResult_pure, hres,
    memoryCost_bind', hst, memoryCost_pure, Nat.add_zero]
  exact ⟨validHistory_bind_step hval (by rw [hst]; exact validHistory_pure w s _), rfl, rfl, hcost⟩

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
      t = s ∧ ∃ rem : List (FactorTable ℕ ℕ), rem.length = j ∧ HoldsFactorList st.1 rem s ∧
        st.2 * (rem.map capFactor).prod ≤ B)
    (fun j ⟨cur, acc⟩ t ⟨ht_eq, rem, hrem_l, hrem_h, hcap_t⟩ => ?_)
    ⟨rfl, live₀, hlen₀, hlive₀, hcap₀⟩
  rcases ht_eq.symm with rfl
  rcases rem with _ | ⟨f, rest⟩
  · cases hrem_l
  simp only [List.length_cons, Nat.add_right_cancel_iff] at hrem_l
  subst hrem_l
  obtain ⟨hf, hrest⟩ := hrem_h
  simp only [List.map_cons, List.prod_cons] at hcap_t
  have hcap' := mul_getD_zero_le hcap_t
  have h1 : 1 ≤ (rest.map capFactor).prod :=
    List.one_le_prod_of_one_le (by simp [one_le_capFactor])
  have hprod_le : acc * f.entries.getD 0 0 ≤ B := (Nat.le_mul_of_pos_right _ h1).trans hcap'
  obtain ⟨-, -, hbr_res, -⟩ := finalProdBranch_spec (w := w) hf
  obtain ⟨-, hst, hres, -⟩ := finalProdStep_spec (w := w) (acc := acc) hf
  have hd := hf.1
  dsimp only at hbr_res ⊢
  rw [hst, hres]
  refine ⟨⟨hmem.frontier_fits.of_le (by omega), hmem.frontier_fits.of_le (by omega), ?_, ?_⟩,
    rfl, rest, rfl, hrest, hcap'⟩
  · split_ifs
  · rw [hbr_res]
    exact ⟨hmem.frontier_fits.of_le (by omega), hB.of_le hprod_le⟩

end Cslib.Algorithms.WordRAM.VariableElimination
