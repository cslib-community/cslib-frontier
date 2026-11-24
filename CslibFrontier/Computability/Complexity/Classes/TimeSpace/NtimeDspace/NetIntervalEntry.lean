/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.NetIntervalTerm

/-!
# The interval tensor entry term computes `intervalEntryNum`

`intervalEntryT_denote`: from a term `L` implementing the letter numbers of the
edges, `intervalEntryT` computes the tensor entry `intervalEntryNum` of
interval `i` of the explicit block network.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.LocalSim

open ProgTerm ProgTerm.Term Cslib.Turing _root_.Turing _root_.Turing.MultiTapePTM
  _root_.Turing.MultiTapeNTM.ChoiceTable

variable {w : List Bool} {k s : ℕ} {State : Type}

section Def

variable (e : State ≃ Fin s) (machine : MultiTapePTM k Bool State)

/-- Whether the control edge leaving `i` carries a control record and its block edges carry
block contents. -/
def guardT (qT bT : Term) (L : Term → Term) (iT : Term) : Term :=
  mul (lt (L iT) (ccountT k s bT))
    (allT (const (k * 3)) fun x =>
      sub (const 1) (lt (L (add qT (add x (mul (const (k * 3)) iT)))) (ccountT k s bT)))

/-- **The tensor entry of interval `i`.** -/
def intervalEntryT (RT NT qT bT σT : Term) (L : Term → Term) (iT : Term) : Term :=
  ite (guardT (k := k) (s := s) qT bT L iT)
    (intervalCountT e machine RT NT bT (digitCountT k σT (const 0) (const 2) iT)
      (digitCountT k σT (const 0) (const 0) iT)
      (inStT k s (stc e (some machine.initial)) bT L iT) (inTrT k s bT L iT)
      (ctlStT k s bT (L iT)) (ctlTrT k bT (L iT))
      (inOffT k s bT L iT) (inCellT k s qT bT σT L iT)
      (fun c => ctlOffT k bT (L iT) c) (fun c => sdigT k σT c iT) (outCellT k s qT bT L iT))
    (const 0)

end Def

theorem forall_lt_mul_three_iff (P : ℕ → Prop) :
    (∀ x < k * 3, P x) ↔ ∀ h : Fin k, ∀ δ : Fin 3, P (δ + 3 * h) := by
  constructor
  · intro hP h δ; exact hP _ (by have := h.isLt; have := δ.isLt; omega)
  · intro hP x hx
    have := hP ⟨x / 3, by omega⟩ ⟨x % 3, Nat.mod_lt _ (by norm_num)⟩
    simp only at this
    rwa [show x % 3 + 3 * (x / 3) = x by omega] at this

variable {e : State ≃ Fin s} {machine : MultiTapePTM k Bool State}

open Classical in
theorem denote_guardT {qT bT iT : Term} {L : Term → Term} {Lv : ℕ → ℕ} {env : List ℕ}
    (hq : StableAt w qT env) (hb : StableAt w bT env) (hi : StableAt w iT env)
    (hL : ImplementsFun w env L Lv) :
    (guardT (k := k) (s := s) qT bT L iT).denote w env =
      if Lv (iT.denote w env) < controlCount k s (bT.denote w env) ∧
        ∀ h : Fin k, ∀ δ : Fin 3, ¬ Lv (qT.denote w env + (δ + 3 * h + k * 3 * iT.denote w env)) <
          controlCount k s (bT.denote w env) then 1 else 0 := by
  unfold guardT
  rw [denote_mul, denote_lt, hL.den hi, denote_ccountT hb,
    allT_denote _ _ env (fun x => ¬ Lv (qT.denote w env + (x + k * 3 * iT.denote w env)) <
      controlCount k s (bT.denote w env)) fun acc x => by
        have harg : StableAt w (add qT (add (lvl env.length) (mul (const (k * 3)) iT)))
            ([acc, x] ++ env) :=
          (hq.extend _).add ((stableAt_lvl (by simp)).add ((stableAt_const _ _).mul (hi.extend _)))
        have hv := (hL [acc, x] _ harg).1
        simp only [List.cons_append, List.nil_append] at hv
        have hc := denote_ccountT (k := k) (s := s) (hb.extend [acc, x])
        simp only [List.cons_append, List.nil_append] at hc
        simp only [denote_sub, denote_const, denote_lt, hv, hc, denote_add, denote_mul,
          hq.cons₂, hi.cons₂, hb.cons₂, denote_lvl_index]
        split_ifs <;> simp_all, denote_const]
  rw [ite_iff_mul]
  apply ite_iff
  rw [forall_lt_mul_three_iff]
  where
    ite_iff_mul : ∀ {P Q : Prop} [Decidable P] [Decidable Q],
        ((if P then 1 else 0) * (if Q then 1 else 0) : ℕ) = if P ∧ Q then 1 else 0 := by
      intro P Q _ _; by_cases hp : P <;> by_cases hq : Q <;> simp [hp, hq]

/-- **The interval entry term computes the interval tensor entry.** -/
theorem intervalEntryT_denote [DecidableEq State] {RT NT qT bT σT iT : Term} {L : Term → Term}
    {Lv : ℕ → ℕ} {env : List ℕ} (hR : StableAt w RT env) (hN : StableAt w NT env)
    (hq : StableAt w qT env) (hb : StableAt w bT env) (hσ : StableAt w σT env)
    (hi : StableAt w iT env) (hL : ImplementsFun w env L Lv)
    (hbpos : 0 < bT.denote w env)
    (hRv : RT.denote w env = radix (bT.denote w env) w.length s)
    (hNv : NT.denote w env = w.length) :
    (intervalEntryT e machine RT NT qT bT σT L iT).denote w env =
      intervalEntryNum e (bT.denote w env) machine w (qT.denote w env) (σT.denote w env) Lv
        (iT.denote w env) := by
  classical
  set b := bT.denote w env
  set q := qT.denote w env
  set σ := σT.denote w env
  set i := iT.denote w env
  -- stability of the scalar data
  have hstI : StableAt w (inStT k s (stc e (some machine.initial)) bT L iT) env := fun extra => by
    rw [denote_inStT _ (hb.extend extra) (hi.extend extra) (hL.extend' extra),
      denote_inStT _ hb hi hL, hb extra, hi extra]
  have htrI : StableAt w (inTrT k s bT L iT) env := fun extra => by
    rw [denote_inTrT (hb.extend extra) (hi.extend extra) (hL.extend' extra),
      denote_inTrT hb hi hL, hb extra, hi extra]
  have hLi : StableAt w (L iT) env := hL.stable hi
  have hstO : StableAt w (ctlStT k s bT (L iT)) env := fun extra => by
    rw [denote_ctlStT _ (hb.extend extra), denote_ctlStT _ hb, hb extra, hLi extra]
  have htrO : StableAt w (ctlTrT k bT (L iT)) env := fun extra => by
    rw [denote_ctlTrT _ (hb.extend extra), denote_ctlTrT _ hb, hb extra, hLi extra]
  -- the function data
  have hoffI : ImplementsFun w env (inOffT k s bT L iT) (inOff k s b Lv i) :=
    implementsFun_of_denote fun extra a ha => by
      rw [denote_inOffT (hb.extend extra) (hi.extend extra) (hL.extend' extra), hb extra,
        hi extra]
  have hcellI : ImplementsFun w env (inCellT k s qT bT σT L iT)
      (fun x => inCell k q s b σ Lv i (x / (3 * b)) (x % (3 * b))) :=
    implementsFun_of_denote fun extra a ha => by
      rw [denote_inCellT (hq.extend extra) (hb.extend extra) (hσ.extend extra) (hi.extend extra)
        (hL.extend' extra) ha, hq extra, hb extra, hσ extra, hi extra]
  have hoffO : ImplementsFun w env (fun c => ctlOffT k bT (L iT) c) (ctlOff k b (Lv i)) :=
    implementsFun_of_denote fun extra a ha => by
      rw [denote_ctlOffT _ _ (hb.extend extra), hb extra, hLi extra, hL.den hi]
  have hdc : ImplementsFun w env (fun c => sdigT k σT c iT)
      (fun c => σ / 3 ^ (c + (k + 1) * i) % 3) :=
    implementsFun_of_denote fun extra a ha => by
      rw [denote_sdigT, hσ extra, hi extra]
  have hcellO : ImplementsFun w env (outCellT k s qT bT L iT)
      (fun x => outCell k q s b Lv i (x / (3 * b)) (x % (3 * b))) :=
    implementsFun_of_denote fun extra a ha => by
      rw [denote_outCellT (hq.extend extra) (hb.extend extra) (hi.extend extra)
        (hL.extend' extra) ha, hq extra, hb extra, hi extra]
  have hdiv : ∀ (h : Fin k) c, c < 3 * b → (↑h * (3 * b) + c) / (3 * b) = h ∧
      (↑h * (3 * b) + c) % (3 * b) = c := fun h c hc => by
    constructor
    · rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hc, zero_add]
    · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]
  obtain ⟨cIst, cIoff, cItr⟩ := inControl_codes e b machine.initial Lv i
  obtain ⟨cOst, cOoff, cOtr⟩ := decodeControlData_codes (k := k) e b (Lv i)
  unfold intervalEntryT intervalEntryNum
  rw [denote_ite, denote_guardT hq hb hi hL]
  by_cases hg : Lv (iT.denote w env) < controlCount k s (bT.denote w env) ∧
      ∀ h : Fin k, ∀ δ : Fin 3, ¬ Lv (qT.denote w env + (δ + 3 * h + k * 3 * iT.denote w env)) <
        controlCount k s (bT.denote w env)
  · rw [ite_eq_left hg, ite_eq_left Nat.one_pos, ite_eq_left hg]
    exact intervalCountT_denote (e := e) (machine := machine) hR hb hN
      (StableAt.digitCountT k hσ (stableAt_const _ _) (stableAt_const _ _) hi)
      (StableAt.digitCountT k hσ (stableAt_const _ _) (stableAt_const _ _) hi)
      hstI htrI hstO htrO hoffI hcellI hoffO hdc hcellO b
      (blockIndexNum k σ i) (blockMoveNum k σ i) (inControlNum e b machine.initial Lv i)
      (fun h => inCellsNum k q s b σ Lv i h) (decodeControlData e b (Lv i))
      (fun h => outCellsNum k q s b Lv i h) (digitCount k σ 0 2 i) (digitCount k σ 0 0 i)
      hRv rfl hNv (denote_digitCountT k _ hσ (stableAt_const _ _) (stableAt_const _ _))
      (denote_digitCountT k _ hσ (stableAt_const _ _) (stableAt_const _ _))
      (by rw [denote_inStT _ hb hi hL, cIst])
      (by rw [denote_inTrT hb hi hL, cItr])
      (by rw [denote_ctlStT _ hb, hL.den hi, cOst])
      (by rw [denote_ctlTrT _ hb, hL.den hi, cOtr])
      (blockIndexNum_none σ i)
      (by rw [cIoff none, finSuccEquiv_symm_none])
      (fun h => by rw [cIoff (some h), finSuccEquiv_symm_some])
      (fun h => by rw [cIoff (some h)]; exact inOff_lt hbpos _ _ _)
      (fun h => length_inCellsNum _ _ _ _ _ _ _ _)
      (fun h c hc => by
        simp only [(hdiv h c hc).1, (hdiv h c hc).2]
        rw [inCellsNum_getD _ _ _ _ _ _ _ _ _ hc])
      (by rw [sgnCode_blockMoveNum, finSuccEquiv_symm_none])
      (fun h => by rw [sgnCode_blockMoveNum, finSuccEquiv_symm_some])
      (by rw [cOoff none, finSuccEquiv_symm_none])
      (fun h => by rw [cOoff (some h), finSuccEquiv_symm_some])
      (fun h => length_outCellsNum _ _ _ _ _ _ _)
      (fun h c hc => by
        simp only [(hdiv h c hc).1, (hdiv h c hc).2]
        rw [outCellsNum_getD _ _ _ _ _ _ _ _ hc])
  · rw [ite_eq_right hg, ite_eq_right (lt_irrefl 0), ite_eq_right hg]; rfl

end Cslib.Complexity.NtimeDspace.LocalSim
