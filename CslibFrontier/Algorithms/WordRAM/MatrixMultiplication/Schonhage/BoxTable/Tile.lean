/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable.TileChildren
public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable.Values
public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable.Geometry
import Mathlib.Algebra.BigOperators.Fin

import CslibFrontier.Computability.WordRAM.CountingLoop
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call

/-!
# Complete native compact box-value table

The native e-major loop writes one signed value per computed catalogue record. Its
children have smaller actual compact ranks, so no value-table clearing or assumed
table construction is used. Original encoding-array bounds cover all signed partials.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable

open Cslib.WordRAM Finset Cslib.Algorithms.MatrixMultiplication.Schonhage
open scoped BigOperators

private theorem exists_count_rank (p : ℕ → Prop) [DecidablePred p] {S j : ℕ}
    (hj : j < Nat.count p S) : ∃ s < S, p s ∧ Nat.count p s = j := by
  induction S with
  | zero => simp at hj
  | succ S ih =>
    by_cases hlt : j < Nat.count p S
    · obtain ⟨s, hs, hps, hr⟩ := ih hlt
      exact ⟨s, Nat.lt_succ_of_lt hs, hps, hr⟩
    · rw [Nat.count_succ] at hj
      split_ifs at hj with hp
      · exact ⟨S, Nat.lt_succ_self S, hp, by omega⟩
      · omega

private theorem child_stars {L H s : ℕ} (hv : Eligible L H s)
    (he : 0 < recordStars L s) (d : Fin 10) :
    recordStars L (childSlot L s d) = recordStars L s - 1 := by
  simpa only [childSlot] using recordStars_slot (recordStars L s - 1)
    (⟨childCode L s d, childCode_lt hv he d⟩ : Fin (10 ^ L))

private theorem slotValue_children {L H s : ℕ} (hv : Eligible L H s)
    (he : 0 < recordStars L s) (a b : Leaf L → ℤ) :
    slotValue a b s = ∑ d : Fin 10, slotValue a b (childSlot L s d) := by
  rw [slotValue, boxValue_eq_sum_childSlots hv he]
  exact sum_congr rfl fun d _ => by rw [slotValue, child_stars hv he]

/-- Registers that may change while constructing one tile's compact values. -/
@[expose] def TileLocal (i : Fin registers) : Prop :=
  RecordLocal i ∨ ProductLocal i ∨ ChildLocal i ∨ i = Reg.current ∨
    i = Reg.nil ∨ i = Reg.one ∨ i = Reg.ten ∨ i = Reg.nine ∨ i = Reg.three

instance (i : Fin registers) : Decidable (TileLocal i) :=
  inferInstanceAs (Decidable (RecordLocal i ∨ ProductLocal i ∨ ChildLocal i ∨
    i = Reg.current ∨ i = Reg.nil ∨ i = Reg.one ∨ i = Reg.ten ∨
    i = Reg.nine ∨ i = Reg.three))

/-- Evaluate one actual descriptor using the stored earlier children or two actual leaf words. -/
theorem exec_tileValue {w L H D V AA BB A B s : ℕ} (x : Data registers)
    (a b : Leaf L → ℤ) (hv : Eligible L H s)
    (ha : ∀ τ, (a τ).natAbs ≤ A) (hb : ∀ τ, (b τ).natAbs ≤ B)
    (hD : x.regs Reg.directory = D) (hV : x.regs Reg.values = V)
    (hAA : x.regs Reg.arrayA = AA) (hBB : x.regs Reg.arrayB = BB)
    (hc : x.regs Reg.completion = recordCode L s)
    (he : x.regs Reg.stars = recordStars L s)
    (hT : x.regs Reg.span = 10 ^ L) (hp : x.regs Reg.starPower = recordStride L s)
    (h0 : x.regs Reg.nil = 0) (h9 : x.regs Reg.nine = 9)
    (h1 : x.regs Reg.one = 1) (h10 : x.regs Reg.ten = 10)
    (hleft : x.mem (AA + recordCode L s) = Signed.encode (a (completionAt L s)))
    (hright : x.mem (BB + recordCode L s) = Signed.encode (b (completionAt L s)))
    (hrank : 0 < recordStars L s → ∀ d : Fin 10,
      x.mem (D + childSlot L s d) = Nat.count (Eligible L H) (childSlot L s d) + 1)
    (hvalue : 0 < recordStars L s → ∀ d : Fin 10, x.mem
      (V + Nat.count (Eligible L H) (childSlot L s d)) =
        Signed.encode (slotValue a b (childSlot L s d)))
    (hfit : Fits (w + 2)
      (D + V + AA + BB + 20 * ((H + 1) * 10 ^ L) + 20 * 10 ^ L + 30))
    (hsigned : GenericRAM.Signed.Fits w (A + B + 10 ^ L * (A * B) : ℕ)) :
    ∃ y, ExecWithin (w + 2) tileValue x y 316 ∧
      y.regs Reg.accumulator = Signed.encode (slotValue a b s) ∧ y.mem = x.mem ∧
      (∀ i, ¬(ProductLocal i ∨ ChildLocal i) → y.regs i = x.regs i) := by
  have hTpos : 0 < 10 ^ L := by positivity
  have hcode : recordCode L s < 10 ^ L := Nat.mod_lt _ hTpos
  have heL : recordStars L s ≤ L := hv.1.trans (population_le _ _)
  have hAB : A * B ≤ 10 ^ L * (A * B) := Nat.le_mul_of_pos_left _ hTpos
  suffices ∃ y, ExecWithin (w + 2) tileValue x y 316 ∧
      y.regs Reg.accumulator = Signed.encode (slotValue a b s) ∧ y.mem = x.mem by
    obtain ⟨y, hy', hyr, hym⟩ := this
    exact ⟨y, hy', hyr, hym,
      fun i hi => hy'.regs_eq (by unfold ProductLocal ChildLocal at hi; decide +revert)⟩
  by_cases he0 : recordStars L s = 0
  · have ha0 : GenericRAM.Signed.Fits w (a (completionAt L s)) :=
      hsigned.of_natAbs_le ((ha _).trans (by omega))
    have hb0 : GenericRAM.Signed.Fits w (b (completionAt L s)) :=
      hsigned.of_natAbs_le ((hb _).trans (by omega))
    have hp0 : GenericRAM.Signed.Fits w (a (completionAt L s) * b (completionAt L s)) :=
      hsigned.of_natAbs_le ((Int.natAbs_mul ..).trans_le
        ((Nat.mul_le_mul (ha _) (hb _)).trans (hAB.trans (by omega))))
    obtain ⟨y, hy, hyr, hym, _⟩ := exec_leafProduct ha0 hb0 hp0 x
      (by simpa only [hAA, hc] using hleft) (by simpa only [hBB, hc] using hright)
      (hfit.of_le (by rw [hAA, hc]; omega)) (hfit.of_le (by rw [hBB, hc]; omega))
    exact ⟨y, (hy.branch_pos (by simp [Cond.holds_eq, he, h0, he0])).mono (by decide),
      by simpa only [slotValue, he0, boxValue, starsToP0_slotCube] using hyr, hym⟩
  · have hepos : 0 < recordStars L s := Nat.pos_of_ne_zero he0
    have hstar : recordStars L s ≤ H := hv.1.trans hv.2
    let val (d : ℕ) := slotValue a b (childSlot L s ⟨d % 10, Nat.mod_lt _ (by decide)⟩)
    let rank (d : ℕ) := Nat.count (Eligible L H)
      (childSlot L s ⟨d % 10, Nat.mod_lt _ (by decide)⟩)
    let C := 10 ^ (recordStars L s - 1) * (A * B)
    have hC : 10 * C ≤ 10 ^ L * (A * B) := by
      rw [← Nat.mul_assoc, ← pow_succ', Nat.sub_add_cancel hepos]
      exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) heL)
    let u := (x.set Reg.accumulator 0).set Reg.term 0
    have hstart : ExecWithin (w + 2) childrenStart x u 2 := by
      unfold childrenStart; wram_exec
    have hrange (d : ℕ) (_hd : d < 10) : rank d ≤ (H + 1) * 10 ^ L := by
      have hc' := childCode_lt hv hepos ⟨d % 10, Nat.mod_lt _ (by decide)⟩
      have hm := Nat.add_one_mul (recordStars L s - 1) (10 ^ L) ▸
        Nat.mul_le_mul_right (10 ^ L) (show recordStars L s - 1 + 1 ≤ H + 1 by omega)
      exact (Nat.count_le _).trans (by dsimp only [childSlot]; omega)
    obtain ⟨y, hy, _, hya, hym, _⟩ := exec_childLoop (R := (H + 1) * 10 ^ L) (C := C) u val rank
      (by regs_frame) (by regs_frame) (by regs_frame) (by regs_frame) (by regs_frame) hTpos
      (by regs_frame) (by simp only [u, Data.set_regs_self])
      (by simp only [u, Data.set_regs_of_ne (by decide : Reg.accumulator ≠ Reg.term),
        Data.set_regs_self])
      (by regs_frame) (by regs_frame) (by regs_frame)
      (fun d hd => by
        simpa only [u, Data.set_mem, childSlot, childCode, rank, Nat.mod_eq_of_lt hd]
          using hrank hepos ⟨d, hd⟩)
      (fun d hd => by
        simpa only [u, Data.set_mem, val, rank, Nat.mod_eq_of_lt hd]
          using hvalue hepos (⟨d, hd⟩ : Fin 10)) hrange
      (fun d _ => by
        dsimp only [val, slotValue]
        rw [child_stars hv hepos]
        exact natAbs_boxValue_le a b ha hb _ _)
      (hsigned.of_natAbs_le (by
        simpa only [Int.natAbs_natCast] using hC.trans (Nat.le_add_left _ _)))
      (hfit.of_le (by
        have hp' := starStride_le (recordCode L s) (recordStars L s) L
        have hes : recordStars L s * 10 ^ L ≤ (H + 1) * 10 ^ L :=
          Nat.mul_le_mul_right _ (by omega)
        dsimp only [recordStride] at *
        omega))
    refine ⟨y, ((hstart.seq hy).branch_neg (by simp [Cond.holds_eq, he, h0, he0])).mono (by decide),
      ?_, hym⟩
    rw [slotValue_children hv hepos a b, hya, ← Fin.sum_univ_eq_sum_range]
    exact congrArg Signed.encode (sum_congr rfl fun d _ => by simp [val, Nat.mod_eq_of_lt d.isLt])

/-- Load, evaluate and store one compact record with all native control and address work. -/
theorem exec_tileStep {w L H D R V AA BB A B s : ℕ} (x : Data registers)
    (a b : Leaf L → ℤ) (hv : Eligible L H s) (hs : s < (H + 1) * 10 ^ L)
    (ha : ∀ τ, (a τ).natAbs ≤ A) (hb : ∀ τ, (b τ).natAbs ≤ B)
    (hx : CatalogueParameters L H D R x)
    (hV : x.regs Reg.values = V) (hAA : x.regs Reg.arrayA = AA)
    (hBB : x.regs Reg.arrayB = BB)
    (hj : x.regs Reg.current = Nat.count (Eligible L H) s)
    (hcode : x.mem (R + 3 * Nat.count (Eligible L H) s) = recordCode L s)
    (hstars : x.mem (R + 3 * Nat.count (Eligible L H) s + 1) = recordStars L s)
    (hstride : x.mem (R + 3 * Nat.count (Eligible L H) s + 2) = recordStride L s)
    (hleft : x.mem (AA + recordCode L s) = Signed.encode (a (completionAt L s)))
    (hright : x.mem (BB + recordCode L s) = Signed.encode (b (completionAt L s)))
    (hrank : 0 < recordStars L s → ∀ d : Fin 10,
      x.mem (D + childSlot L s d) = Nat.count (Eligible L H) (childSlot L s d) + 1)
    (hvalue : 0 < recordStars L s → ∀ d : Fin 10,
      x.mem (V + Nat.count (Eligible L H) (childSlot L s d)) =
        Signed.encode (slotValue a b (childSlot L s d)))
    (hfit : Fits (w + 2)
      (D + R + V + AA + BB + 20 * ((H + 1) * 10 ^ L) + 20 * 10 ^ L + 30))
    (hsigned : GenericRAM.Signed.Fits w (A + B + 10 ^ L * (A * B) : ℕ)) :
    ∃ y, ExecWithin (w + 2) tileStep x y 326 ∧
      y.regs Reg.current = Nat.count (Eligible L H) s + 1 ∧
      y.mem = Function.update x.mem (V + Nat.count (Eligible L H) s)
        (Signed.encode (slotValue a b s)) := by
  have hjlt : Nat.count (Eligible L H) s < (H + 1) * 10 ^ L :=
    (Nat.count_le _).trans_lt hs
  refine WP.exists_execWithin ?_
  unfold tileStep tileStore
  wram_call (exec_loadRecord x hx.records hj hx.one hx.three
    (by simpa only [Nat.mul_comm] using hcode)
    (by simpa only [Nat.mul_comm] using hstars)
    (by simpa only [Nat.mul_comm] using hstride) (hfit.of_le (by omega)))
    with u ⟨uc, ue, up, um, uf⟩
  wram_call (exec_tileValue u a b hv ha hb
    (by regs_frame) (by regs_frame) (by regs_frame) (by regs_frame)
    uc ue (by regs_frame) up
    (by regs_frame) (by regs_frame) (by regs_frame) (by regs_frame)
    (um.symm ▸ hleft) (um.symm ▸ hright) (um.symm ▸ hrank) (um.symm ▸ hvalue)
    (hfit.of_le (by omega)) hsigned)
    with v ⟨vacc, vm, vf⟩
  obtain ⟨vV, vj, v1⟩ : v.regs Reg.values = V ∧
      v.regs Reg.current = Nat.count (Eligible L H) s ∧ v.regs Reg.one = 1 := by regs_frame
  wram_exec [vV, vj, v1, vacc]
  exact ⟨by wram_simp, by simp only [Data.set_mem, Data.write_mem, vm, um]⟩

/-- The native compact loop computes every eligible slot, preserving the catalogue and inputs. -/
theorem exec_tileLoop {w L H D R V AA BB A B : ℕ} {μ : ℕ → ℕ} (x : Data registers)
    (a b : Leaf L → ℤ)
    (ha : ∀ τ, (a τ).natAbs ≤ A) (hb : ∀ τ, (b τ).natAbs ≤ B)
    (hx : CatalogueParameters L H D R x)
    (hV : x.regs Reg.values = V) (hAA : x.regs Reg.arrayA = AA)
    (hBB : x.regs Reg.arrayB = BB)
    (hcount : x.regs Reg.count = Nat.count (Eligible L H) ((H + 1) * 10 ^ L))
    (hcurrent : x.regs Reg.current = 0)
    (hcat : CataloguePrefix L H D R ((H + 1) * 10 ^ L) μ x.mem)
    (hDR : D + (H + 1) * 10 ^ L ≤ R)
    (hRV : R + 3 * Nat.count (Eligible L H) ((H + 1) * 10 ^ L) ≤ V)
    (hAV : AA + 10 ^ L ≤ V) (hBV : BB + 10 ^ L ≤ V)
    (hleft : ∀ c : Fin (10 ^ L), x.mem (AA + c.val) = Signed.encode (a (leafAt c)))
    (hright : ∀ c : Fin (10 ^ L), x.mem (BB + c.val) = Signed.encode (b (leafAt c)))
    (hfit : Fits (w + 2)
      (D + R + V + AA + BB + 20 * ((H + 1) * 10 ^ L) + 20 * 10 ^ L + 30))
    (hsigned : GenericRAM.Signed.Fits w (A + B + 10 ^ L * (A * B) : ℕ)) :
    ∃ y, ExecWithin (w + 2) (.loop (.lt Reg.current Reg.count) tileStep) x y
        (328 * Nat.count (Eligible L H) ((H + 1) * 10 ^ L) + 2) ∧
      (∀ s < (H + 1) * 10 ^ L, Eligible L H s →
        y.mem (V + Nat.count (Eligible L H) s) = Signed.encode (slotValue a b s)) ∧
      (∀ q, ¬(V ≤ q ∧ q < V + Nat.count (Eligible L H) ((H + 1) * 10 ^ L)) →
        y.mem q = x.mem q) := by
  let S := (H + 1) * 10 ^ L
  let K := Nat.count (Eligible L H) S
  let P (j : ℕ) (y : Data registers) : Prop :=
    CatalogueParameters L H D R y ∧ y.regs Reg.values = V ∧
      y.regs Reg.arrayA = AA ∧ y.regs Reg.arrayB = BB ∧ y.regs Reg.count = K ∧
      (∀ s < S, Eligible L H s → Nat.count (Eligible L H) s < j →
        y.mem (V + Nat.count (Eligible L H) s) = Signed.encode (slotValue a b s)) ∧
      (∀ q, ¬(V ≤ q ∧ q < V + j) → y.mem q = x.mem q)
  have hi : P (x.regs Reg.current) x :=
    ⟨hx, hV, hAA, hBB, hcount, by simp [hcurrent], fun _ _ => rfl⟩
  have hbody (y : Data registers) (hy : P (y.regs Reg.current) y) (hjlt : y.regs Reg.current < K) :
      ∃ z, ExecWithin (w + 2) tileStep y z 326 ∧ P (y.regs Reg.current + 1) z ∧
        z.regs Reg.current = y.regs Reg.current + 1 := by
    obtain ⟨yp, yV, yA, yB, yK, yvalues, yframe⟩ := hy
    obtain ⟨s, hs, hvs, hsj⟩ := exists_count_rank (Eligible L H) hjlt
    have hlow (q : ℕ) (hq : q < V) : y.mem q = x.mem q := yframe q (by omega)
    have hsK : Nat.count (Eligible L H) s < Nat.count (Eligible L H) ((H + 1) * 10 ^ L) :=
      Nat.count_strict_mono hvs hs
    have hcode : recordCode L s < 10 ^ L := Nat.mod_lt _ (by positivity)
    obtain ⟨z, hz, hzj, hzm⟩ := exec_tileStep y a b hvs hs ha hb yp yV yA yB hsj.symm
      ((hlow _ (by omega)).trans (hcat.code s hs hvs))
      ((hlow _ (by omega)).trans (hcat.stars s hs hvs))
      ((hlow _ (by omega)).trans (hcat.stride s hs hvs))
      ((hlow _ (by omega)).trans (hleft ⟨recordCode L s, hcode⟩))
      ((hlow _ (by omega)).trans (hright ⟨recordCode L s, hcode⟩))
      (fun he d => by
        have hchild : childSlot L s d < S := (childSlot_lt hvs he d).trans hs
        rw [hlow _ (by dsimp only [S] at hchild; omega), hcat.directory _ hchild,
          directoryWord, ite_eq_left (eligible_childSlot hvs he d)])
      (fun he d => yvalues _ ((childSlot_lt hvs he d).trans hs)
        (eligible_childSlot hvs he d) ((child_rank_lt hvs he d).trans_eq hsj))
      hfit hsigned
    refine ⟨z, hz, ⟨by regs_frame, by regs_frame, by regs_frame, by regs_frame,
      by regs_frame, ?_, ?_⟩, by omega⟩
    · intro i hi hvi hji
      rw [hzm]
      by_cases hij : Nat.count (Eligible L H) i = Nat.count (Eligible L H) s
      · obtain rfl := Nat.count_injective hvi hvs hij
        exact Function.update_self ..
      · rw [Function.update_of_ne (by omega)]
        exact yvalues i hi hvi (by omega)
    · intro q hq
      rw [hzm, Function.update_of_ne (by omega)]
      exact yframe q (by omega)
  obtain ⟨y, hy, ⟨_, _, _, _, _, yvalues, yframe⟩, _⟩ := ExecWithin.loop_count P
    (fun _ ⟨_, _, _, _, hcount, _⟩ => hcount) hbody (by simp [hcurrent]) hi
  exact ⟨y, by simpa only [hcurrent, Nat.sub_zero, K, S, Nat.reduceAdd, Nat.mul_comm] using hy,
    fun s hs hv => yvalues s hs hv (Nat.count_strict_mono hv hs), yframe⟩

/-- Complete one-tile execution, including actual constant/counter setup, with no dirty-memory
restriction. The catalogue and both input arrays lie below the value-table base. -/
theorem exec_tile {w L H D R V AA BB A B : ℕ} {μ : ℕ → ℕ} (x : Data registers)
    (a b : Leaf L → ℤ)
    (ha : ∀ τ, (a τ).natAbs ≤ A) (hb : ∀ τ, (b τ).natAbs ≤ B)
    (hx : CatalogueParameters L H D R x)
    (hV : x.regs Reg.values = V) (hAA : x.regs Reg.arrayA = AA)
    (hBB : x.regs Reg.arrayB = BB)
    (hcount : x.regs Reg.count = Nat.count (Eligible L H) ((H + 1) * 10 ^ L))
    (hcat : CataloguePrefix L H D R ((H + 1) * 10 ^ L) μ x.mem)
    (hDR : D + (H + 1) * 10 ^ L ≤ R)
    (hRV : R + 3 * Nat.count (Eligible L H) ((H + 1) * 10 ^ L) ≤ V)
    (hAV : AA + 10 ^ L ≤ V) (hBV : BB + 10 ^ L ≤ V)
    (hleft : ∀ c : Fin (10 ^ L), x.mem (AA + c.val) = Signed.encode (a (leafAt c)))
    (hright : ∀ c : Fin (10 ^ L), x.mem (BB + c.val) = Signed.encode (b (leafAt c)))
    (hfit : Fits (w + 2)
      (D + R + V + AA + BB + 20 * ((H + 1) * 10 ^ L) + 20 * 10 ^ L + 30))
    (hsigned : GenericRAM.Signed.Fits w (A + B + 10 ^ L * (A * B) : ℕ)) :
    ∃ y, ExecWithin (w + 2) tile x y
        (328 * Nat.count (Eligible L H) ((H + 1) * 10 ^ L) + 8) ∧
      (∀ s < (H + 1) * 10 ^ L, Eligible L H s →
        y.mem (V + Nat.count (Eligible L H) s) = Signed.encode (slotValue a b s)) ∧
      (∀ q, ¬(V ≤ q ∧ q < V + Nat.count (Eligible L H) ((H + 1) * 10 ^ L)) →
        y.mem q = x.mem q) ∧ (∀ i, ¬TileLocal i → y.regs i = x.regs i) := by
  suffices ∃ y, ExecWithin (w + 2) tile x y
        (328 * Nat.count (Eligible L H) ((H + 1) * 10 ^ L) + 8) ∧
      (∀ s < (H + 1) * 10 ^ L, Eligible L H s →
        y.mem (V + Nat.count (Eligible L H) s) = Signed.encode (slotValue a b s)) ∧
      (∀ q, ¬(V ≤ q ∧ q < V + Nat.count (Eligible L H) ((H + 1) * 10 ^ L)) →
        y.mem q = x.mem q) by
    obtain ⟨y, he, hvalues, hframe⟩ := this
    exact ⟨y, he, hvalues, hframe, fun i hi =>
      he.regs_eq (by unfold TileLocal RecordLocal ProductLocal ChildLocal at hi; decide +revert)⟩
  refine WP.exists_execWithin ?_
  unfold tile tileSetup
  wram_call (exec_constants x (hfit.of_le (by omega)))
    with u ⟨u0, u1, u10, u9, u3, um, uf⟩
  wram_exec
  wram_call (exec_tileLoop _ a b ha hb (by regs_frame)
    (by regs_frame) (by regs_frame) (by regs_frame) (by regs_frame)
    (by wram_simp) (um.symm ▸ hcat) hDR hRV hAV hBV
    (um.symm ▸ hleft) (um.symm ▸ hright) hfit hsigned)
    with y ⟨hvalues, hframe⟩
  exact ⟨by omega, hvalues, um ▸ hframe⟩

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable
