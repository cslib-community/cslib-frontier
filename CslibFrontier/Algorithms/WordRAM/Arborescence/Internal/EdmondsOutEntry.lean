/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.Arborescence.Internal.EdmondsEntry
import CslibFrontier.Algorithms.WordRAM.Arborescence.Internal.FinEnumBridges
import CslibFrontier.Foundations.Data.List.RowMajor
import CslibFrontier.Tactic.Realize

/-!
# Out-arborescence transpose loader and `edmondsOutProg` entry (internal)

Implements matrix transposition (`transposeProg`) and `edmondsOutProg`, reusing `finishArbProg`
on the transposed graph and cost table, with `Realizes .exact` and `O(n³)` specifications.
-/

namespace Cslib.Algorithms.WordRAM.Arborescence.Internal

open Cslib.Algorithms.Lean.Arborescence
open Cslib.DataStructure
open Cslib.WordRAM
open Cslib.WordRAM.Realization
open Cslib.WordRAM.Realization.Signed

attribute [local client_simps] StateTransitionSpec.clientState
  StateTransitionSpec.runClient_pure'
  runClient_read runClient_write runClient_allocDirty runClient_ite
  prog_clientState_ite

private structure TransposeRowArgs where
  n : ℕ
  u : ℕ
  ws : ℕ

private word_enc_structure encTransposeRowArgs : TransposeRowArgs where
  n : wordWords, u : wordWords, ws : wordWords

private instance : WordEncoding TransposeRowArgs := ⟨3, encTransposeRowArgs⟩

private def transposeRowStep (q : TransposeRowArgs × ℕ) : Memory.Prog ℕ := do
  let env := Prod.fst q
  let col := Prod.snd q
  let a ← Memory.read (3 + col * env.n + env.u)
  let c ← Memory.read (3 + env.n * env.n + col * env.n + env.u)
  Memory.write (curAdjBase env.ws env.n + env.u * env.n + col) a
  Memory.write (curCostBase env.ws env.n + env.u * env.n + col) c
  pure (col + 1)

private abbrev TransposeRowStepSafe (w : ℕ) (q : TransposeRowArgs × ℕ) (_ : Memory.State) : Prop :=
  let env := Prod.fst q
  let col := Prod.snd q
  env.u < env.n ∧ col < env.n ∧ WsFits w env.ws env.n ∧ Fits w (3 + 2 * (env.n * env.n))

private theorem transposeRowStep_realizes :
    Realizes .exact transposeRowStep (appendWords encTransposeRowArgs wordWords) wordWords
      TransposeRowStepSafe (fun _ _ => 0) := by
  unfold transposeRowStep
  realize
  all_goals
    obtain ⟨hu, hc, hws, hin⟩ := h
    first
    | exact hin.of_le (by nlinarith)
    | exact hws.of_le (by dsimp only [wsSize, curAdjBase, curCostBase]; nlinarith)

private def fillTransposeRowProg (a : TransposeRowArgs) : Memory.Prog ℕ :=
  iterate transposeRowStep a a.n 0

private theorem fillTransposeRowProg_realizes :
    Realizes .exact fillTransposeRowProg encTransposeRowArgs wordWords
      (fun w a s => iterationSafe transposeRowStep TransposeRowStepSafe w a a.n 0 s)
      (fun _ _ => 0) := by
  unfold fillTransposeRowProg
  realize [transposeRowStep_realizes]
  exact h

private def transposeOuterStep (q : (ℕ × ℕ) × ℕ) : Memory.Prog ℕ := do
  let env := Prod.fst q
  let u := Prod.snd q
  let _ ← Memory.read 0
  let _ ← fillTransposeRowProg ⟨Prod.fst env, u, Prod.snd env⟩
  pure (u + 1)

private abbrev TransposeOuterStepSafe (w : ℕ) (q : (ℕ × ℕ) × ℕ) (s : Memory.State) : Prop :=
  let env := Prod.fst q
  let u := Prod.snd q
  Fits w (u + 1) ∧
    iterationSafe transposeRowStep TransposeRowStepSafe w ⟨Prod.fst env, u, Prod.snd env⟩
      (Prod.fst env) 0 s

private theorem transposeOuterStep_realizes :
    Realizes .exact transposeOuterStep (appendWords pairWords wordWords) wordWords
      TransposeOuterStepSafe (fun _ _ => 0) := by
  unfold transposeOuterStep
  realize [fillTransposeRowProg_realizes]
  all_goals first | exact h.1 | exact h.2

private def transposeProg (d : ℕ × ℕ) : Memory.Prog ℕ :=
  iterate transposeOuterStep d (Prod.fst d) 0

private theorem transposeProg_realizes :
    Realizes .exact transposeProg pairWords wordWords
      (fun w d s => iterationSafe transposeOuterStep TransposeOuterStepSafe w d (Prod.fst d) 0 s)
      (fun _ _ => 0) := by
  unfold transposeProg
  realize [transposeOuterStep_realizes]
  exact h

private theorem fillTransposeRowProg_spec {w n ws : ℕ} (uFin : Fin n)
    (adj : Fin n → Fin n → Bool) (cost : Fin n → Fin n → ℤ) (s : Memory.State)
    (hws : WsFits w ws n) (hin_fit : Fits w (3 + 2 * (n * n)))
    (hws_lo : 3 + 2 * (n * n) ≤ ws) (hf : ws + wsSize n ≤ s.frontier)
    (hadj_in : ∀ x y : Fin n, s.mem (3 + (x.1 * n + y.1)) = if adj x y then 1 else 0)
    (hcost_in : ∀ x y : Fin n, s.mem (3 + n * n + (x.1 * n + y.1)) = Signed.encode (cost x y))
    (hfit_c : ∀ x y : Fin n, Fits w (Signed.encode (cost x y))) :
    let ra : TransposeRowArgs := ⟨n, uFin.1, ws⟩
    let sr' := (Memory.spec 0).clientState s (fillTransposeRowProg ra)
    iterationSafe transposeRowStep TransposeRowStepSafe w ra n 0 s ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (fillTransposeRowProg ra)) ∧
      memoryCost (fillTransposeRowProg ra) s ≤ 4 * n ∧
      sr'.frontier = s.frontier ∧
      (∀ addr, ¬(curAdjBase ws n + uFin.1 * n ≤ addr ∧ addr < curAdjBase ws n + uFin.1 * n + n ∨
        curCostBase ws n + uFin.1 * n ≤ addr ∧ addr < curCostBase ws n + uFin.1 * n + n) →
        sr'.mem addr = s.mem addr) ∧
      (∀ col : Fin n,
        sr'.mem (curAdjBase ws n + uFin.1 * n + col.1) = (if adj col uFin then 1 else 0) ∧
        sr'.mem (curCostBase ws n + uFin.1 * n + col.1) = Signed.encode (cost col uFin)) := by
  let ra : TransposeRowArgs := ⟨n, uFin.1, ws⟩
  have h1 : Fits w 1 := hws.of_le (by dsimp only [wsSize]; omega)
  have hu_lt := uFin.isLt
  have hrow := iterate_spec transposeRowStep TransposeRowStepSafe w ra 4 n
    (fun col idxR sr =>
      idxR = col ∧ sr.frontier = s.frontier ∧
        (∀ x y : Fin n, sr.mem (3 + (x.1 * n + y.1)) = if adj x y then 1 else 0) ∧
        (∀ x y : Fin n, sr.mem (3 + n * n + (x.1 * n + y.1)) = Signed.encode (cost x y)) ∧
        (∀ c0 : Fin n, c0.1 < col →
          sr.mem (curAdjBase ws n + uFin.1 * n + c0.1) = (if adj c0 uFin then 1 else 0) ∧
          sr.mem (curCostBase ws n + uFin.1 * n + c0.1) = Signed.encode (cost c0 uFin)))
    (fun addr => curAdjBase ws n + uFin.1 * n ≤ addr ∧ addr < curAdjBase ws n + uFin.1 * n + n ∨
      curCostBase ws n + uFin.1 * n ≤ addr ∧ addr < curCostBase ws n + uFin.1 * n + n)
    (fun col hcol idxR sr ⟨hidxR, hfr_r, ha_r, hc_r, hdone_r⟩ => by
      subst idxR
      set colFin : Fin n := ⟨col, hcol⟩
      have ha_cu : sr.mem (3 + col * n + uFin.1) = if adj colFin uFin then 1 else 0 := by
        simpa [Nat.add_assoc] using ha_r colFin uFin
      have hc_cu : sr.mem (3 + n * n + col * n + uFin.1) = Signed.encode (cost colFin uFin) := by
        simpa [Nat.add_assoc] using hc_r colFin uFin
      refine ⟨by dsimp only [TransposeRowStepSafe, ra]; exact ⟨hu_lt, hcol, hws, hin_fit⟩,
        ?_, ?_, ?_, ?_, ?_⟩
      · unfold transposeRowStep
        dsimp only [ra]
        exact validHistory_read_bind
          (by dsimp only [wsSize] at hf hfr_r ⊢; nlinarith)
          (validHistory_read_bind
            (by dsimp only [wsSize] at hf hfr_r ⊢; nlinarith)
            (validHistory_write_bind
              (by dsimp only [wsSize, curAdjBase] at hf hfr_r ⊢; nlinarith)
              (by rw [ha_cu]; split_ifs <;> first | exact h1 | exact fits_zero w)
              (validHistory_write_bind
                (by dsimp only [wsSize, curCostBase] at hf hfr_r ⊢; nlinarith)
                (hc_cu ▸ hfit_c colFin uFin)
                (validHistory_pure w _ _))))
      · unfold transposeRowStep
        dsimp only [ra]
        rw [memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
          memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
          memoryCost_bind', memoryCost_write, memoryCost_bind', memoryCost_write]
        simp [client_simps]
      · simp [transposeRowStep, ra, client_simps, hfr_r]
      · intro addr haddr
        simp only [transposeRowStep, ra, client_simps]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      · unfold transposeRowStep
        dsimp only [ra]
        simp only [client_simps]
        refine ⟨trivial, hfr_r, ?_, ?_, ?_⟩
        · intro x y
          have := x.isLt; have := y.isLt
          rw [Function.update_of_ne (by dsimp only [curCostBase]; nlinarith),
            Function.update_of_ne (by dsimp only [curAdjBase]; nlinarith)]
          exact ha_r x y
        · intro x y
          have := x.isLt; have := y.isLt
          rw [Function.update_of_ne (by dsimp only [curCostBase]; nlinarith),
            Function.update_of_ne (by dsimp only [curAdjBase]; nlinarith)]
          exact hc_r x y
        · intro c0 hc0
          by_cases heq : c0.1 = col
          · have hc0_eq : c0 = colFin := Fin.ext heq
            subst hc0_eq
            simp only [Function.update_self, colFin]
            rw [Function.update_of_ne (by dsimp only [curAdjBase, curCostBase]; nlinarith),
              Function.update_self]
            simp only [ha_cu, hc_cu]
            exact ⟨rfl, rfl⟩
          · rw [Function.update_of_ne (by dsimp only [curAdjBase, curCostBase]; nlinarith),
              Function.update_of_ne (by omega),
              Function.update_of_ne (by omega),
              Function.update_of_ne (by dsimp only [curAdjBase, curCostBase]; nlinarith)]
            exact hdone_r c0 (by omega))
    0 s ⟨rfl, rfl, hadj_in, hcost_in, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  obtain ⟨hsafe, hvh, hmc, hfr_end, hmod_end, _, _, _, _, hdone_end⟩ := hrow
  unfold fillTransposeRowProg
  exact ⟨hsafe, hvh, hmc, hfr_end, hmod_end, fun col => hdone_end col col.isLt⟩

private theorem transposeProg_spec {w n ws : ℕ} (hpos : 0 < n)
    (adj : Fin n → Fin n → Bool) (cost : Fin n → Fin n → ℤ) (s₀ : Memory.State)
    (hws : WsFits w ws n) (hin_fit : Fits w (3 + 2 * (n * n)))
    (hws_lo : 3 + 2 * (n * n) ≤ ws) (hf : ws + wsSize n ≤ s₀.frontier)
    (hadj_in : ∀ x y : Fin n, s₀.mem (3 + (x.1 * n + y.1)) = if adj x y then 1 else 0)
    (hcost_in : ∀ x y : Fin n, s₀.mem (3 + n * n + (x.1 * n + y.1)) = Signed.encode (cost x y))
    (hfit_c : ∀ x y : Fin n, Fits w (Signed.encode (cost x y))) :
    let s' := (Memory.spec 0).clientState s₀ (transposeProg (n, ws))
    iterationSafe transposeOuterStep TransposeOuterStepSafe w (n, ws) n 0 s₀ ∧
      (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ (transposeProg (n, ws))) ∧
      memoryCost (transposeProg (n, ws)) s₀ ≤ (4 * n + 1) * n ∧
      s'.frontier = s₀.frontier ∧
      (∀ u col : Fin n,
        s'.mem (curAdjBase ws n + u.1 * n + col.1) = if adj col u then 1 else 0) ∧
      (∀ u col : Fin n,
        s'.mem (curCostBase ws n + u.1 * n + col.1) = Signed.encode (cost col u)) := by
  have hf_pos : 0 < s₀.frontier := by dsimp only [wsSize] at hf; nlinarith
  have h := iterate_spec transposeOuterStep TransposeOuterStepSafe w (n, ws) (4 * n + 1) n
    (fun m idx s =>
      idx = m ∧ s.frontier = s₀.frontier ∧
        (∀ x y : Fin n, s.mem (3 + (x.1 * n + y.1)) = if adj x y then 1 else 0) ∧
        (∀ x y : Fin n, s.mem (3 + n * n + (x.1 * n + y.1)) = Signed.encode (cost x y)) ∧
        (∀ u col : Fin n, u.1 < m →
          s.mem (curAdjBase ws n + u.1 * n + col.1) = (if adj col u then 1 else 0) ∧
          s.mem (curCostBase ws n + u.1 * n + col.1) = Signed.encode (cost col u)))
    (fun addr => curAdjBase ws n ≤ addr ∧ addr < curCostBase ws n + n * n)
    (fun m hm idx s ⟨hidx, hfr, ha_s, hc_s, hdone_o⟩ => by
      subst idx
      set uFin : Fin n := ⟨m, hm⟩
      have hrow := fillTransposeRowProg_spec uFin adj cost s hws hin_fit hws_lo
        (by rw [hfr]; exact hf) ha_s hc_s hfit_c
      have hdisj : ∀ addr, addr < curAdjBase ws n + m * n ∨
          curAdjBase ws n + m * n + n ≤ addr ∧ addr < curCostBase ws n + m * n ∨
          curCostBase ws n + m * n + n ≤ addr →
          ((Memory.spec 0).clientState s (fillTransposeRowProg ⟨n, m, ws⟩)).mem addr =
            s.mem addr :=
        fun addr h => hrow.2.2.2.2.1 addr
          (by dsimp only [uFin, curAdjBase, curCostBase] at h ⊢; omega)
      refine ⟨by dsimp only [TransposeOuterStepSafe]; exact ⟨hws.of_le
          (by dsimp only [wsSize]; nlinarith), hrow.1⟩,
        ?_, ?_, ?_, ?_, ?_⟩
      · unfold transposeOuterStep
        dsimp only
        exact validHistory_read_bind (by omega)
          (validHistory_bind_step hrow.2.1 (validHistory_pure w _ _))
      · unfold transposeOuterStep
        dsimp only
        rw [memoryCost_bind', memoryCost_read, clientState_read, memoryCost_bind']
        have hc_r : memoryCost (fillTransposeRowProg ⟨n, m, ws⟩) s ≤ 4 * n := hrow.2.2.1
        simp only [client_simps]
        omega
      · unfold transposeOuterStep
        dsimp only
        have hrow_fr := hrow.2.2.2.1
        dsimp only [uFin] at hrow_fr
        simp [client_simps, hrow_fr, hfr]
      · intro addr haddr
        unfold transposeOuterStep
        dsimp only
        simp only [client_simps]
        exact hrow.2.2.2.2.1 addr
          (by have := Nat.mul_le_mul_right n (Nat.succ_le_of_lt hm)
              dsimp only [uFin, curAdjBase, curCostBase] at haddr ⊢
              rw [Nat.succ_mul] at this
              omega)
      · unfold transposeOuterStep
        dsimp only
        have hrow_fr := hrow.2.2.2.1
        dsimp only [uFin] at hrow_fr
        simp only [client_simps]
        refine ⟨trivial, hrow_fr.trans hfr, ?_, ?_, ?_⟩
        · intro x y
          have := List.mul_add_lt_sq x.isLt y.isLt
          rw [hdisj _ (Or.inl (by dsimp only [curAdjBase]; omega))]
          exact ha_s x y
        · intro x y
          have := List.mul_add_lt_sq x.isLt y.isLt
          rw [hdisj _ (Or.inl (by dsimp only [curAdjBase]; omega))]
          exact hc_s x y
        · intro u0 c0 hu0
          rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hu0) with hlt | heq
          · have hlt_mul : u0.1 * n + c0.1 < m * n := by
              have := c0.isLt
              have := Nat.mul_le_mul_right n hlt
              linarith [Nat.succ_mul u0.1 n]
            have hm_mul : m * n + n ≤ n * n := by
              simpa [Nat.succ_mul] using Nat.mul_le_mul_right n hm
            rw [hdisj _ (Or.inl (by dsimp only [curAdjBase]; omega)),
              hdisj _ (Or.inr (Or.inl (by dsimp only [curAdjBase, curCostBase]; omega)))]
            exact hdone_o u0 c0 hlt
          · have hu_eq : u0 = uFin := Fin.ext heq
            subst hu_eq
            exact hrow.2.2.2.2.2 c0)
    0 s₀ ⟨rfl, rfl, hadj_in, hcost_in, fun _ _ h => absurd h (Nat.not_lt_zero _)⟩
  obtain ⟨hsafe, hvh, hmc, hfr_end, _, _, _, _, _, hdone_end⟩ := h
  unfold transposeProg
  exact ⟨hsafe, hvh, hmc, hfr_end,
    fun u col => (hdone_end u col u.isLt).1,
    fun u col => (hdone_end u col u.isLt).2⟩

/-- Word-RAM entry program solving rooted minimum-cost spanning out-arborescence for `(n, root)`
by transposing the input matrices into the workspace and running `finishArbProg`. -/
public def edmondsOutProg (d : ℕ × ℕ) : Memory.Prog ℕ := do
  let n := Prod.fst d
  let r := Prod.snd d
  let ws ← Memory.allocDirty (wsSize n)
  let outAddr ← Memory.allocDirty (n + 1)
  let _ ← transposeProg (n, ws)
  finishArbProg ⟨n, r, ws, outAddr⟩

/-- Safety precondition for `edmondsOutProg`. -/
public def EdmondsOutProgSafe (w : ℕ) (d : ℕ × ℕ) (s₀ : Memory.State) : Prop :=
  let n := Prod.fst d
  let r := Prod.snd d
  let ws := s₀.frontier
  let outAddr := ws + wsSize n
  let s1 : Memory.State := ⟨s₀.mem, outAddr + (n + 1)⟩
  let s3 := (Memory.spec 0).clientState s1 (transposeProg (n, ws))
  Fits w (outAddr + (n + 1) + 8) ∧ r < n ∧
    iterationSafe transposeOuterStep TransposeOuterStepSafe w (n, ws) n 0 s1 ∧
    FinishArbSafe w ⟨n, r, ws, outAddr⟩ s3

public theorem edmondsOutProg_realizes :
    Realizes .exact edmondsOutProg pairWords wordWords EdmondsOutProgSafe (fun _ _ => 0) := by
  unfold edmondsOutProg
  realize [transposeProg_realizes, finishArbProg_realizes]
  all_goals
    obtain ⟨hfit, hr, htr, hfin⟩ := h
    first
    | exact htr
    | exact hfin
    | exact hfit.of_le (by dsimp only [wsSize]; nlinarith)

public theorem edmondsOutProg_spec {w M₀ : ℕ} (I : ArborescenceInput)
    (hM : ∀ u v, (I.cost u v).natAbs ≤ M₀) (hwb : Fits w (wordBound I.n M₀)) :
    let s₀ := Memory.State.init I.encode
    let d := (I.n, I.root.1)
    let outAddr := (Memory.spec 0).clientResult s₀ (edmondsOutProg d)
    let s' := (Memory.spec 0).clientState s₀ (edmondsOutProg d)
    EdmondsOutProgSafe w d s₀ ∧
      (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ (edmondsOutProg d)) ∧
      memoryCost (edmondsOutProg d) s₀ ≤ 43 * I.n ^ 3 + 22 * I.n ^ 2 + 9 * I.n + 3 ∧
      outputList s'.mem outAddr = I.expectedOutParentList ∧
      Fits w (outAddr + I.expectedOutParentList.length) := by
  rcases I with ⟨n, root, adj, cost⟩
  let I : ArborescenceInput := ⟨n, root, adj, cost⟩
  set s₀ := Memory.State.init I.encode
  let ws := s₀.frontier
  let outAddr := ws + wsSize n
  have hws_eq : ws = 3 + 2 * (n * n) := by
    change I.encode.length + 1 = _
    simp [I, ArborescenceInput.encode]
    omega
  have hfit_top : Fits w (outAddr + (n + 1) + 8) :=
    hwb.of_le (by
      have hsq := sq_le_wordBound n M₀
      dsimp only [outAddr, ws, wsSize] at hws_eq ⊢
      rw [hws_eq]
      nlinarith only [hsq])
  have hws_fit : WsFits w ws n := hfit_top.of_le (by dsimp only [outAddr, ws]; omega)
  obtain ⟨hfit_len1, hin_fits⟩ := inputFits_arb_encode I hM hwb
  have hwf0 := Memory.wellFormed_init hin_fits hfit_len1
  let s1 : Memory.State := ⟨s₀.mem, outAddr + (n + 1)⟩
  have hfit_c : ∀ x y : Fin n, Fits w (Signed.encode (cost x y)) := fun x y => by
    rw [← init_mem_encode_arb_cost I x y]
    exact hwf0.mem_fits _
  have htr := transposeProg_spec root.pos adj cost s1 hws_fit
    (hfit_top.of_le (by dsimp only [outAddr, ws, wsSize] at hws_eq ⊢; rw [hws_eq]; nlinarith))
    (by rw [hws_eq])
    (by dsimp only [s1, outAddr, ws]; omega)
    (fun x y => init_mem_encode_arb_adj I x y)
    (fun x y => init_mem_encode_arb_cost I x y)
    hfit_c
  let s3 := (Memory.spec 0).clientState s1 (transposeProg (n, ws))
  have hs3_fr : s3.frontier = outAddr + (n + 1) := htr.2.2.2.1
  let a₀ := initAdjTable n fun u col => decide (I.digraph.Adj col u)
  let c₀ := initCostTable n fun u col => cost col u
  have ha3 : ∀ u col : Fin n,
      s3.mem (curAdjBase ws n + u.1 * n + col.1) = if a₀[u.1][col.1] then 1 else 0 := by
    intro u col
    dsimp only [a₀, initAdjTable, ArborescenceInput.digraph, I]
    simp only [Vector.getElem_ofFn]
    exact htr.2.2.2.2.1 u col
  have hc3 : ∀ u col : Fin n,
      s3.mem (curCostBase ws n + u.1 * n + col.1) = Signed.encode c₀[u.1][col.1] := by
    intro u col
    dsimp only [c₀, initCostTable]
    simp only [Vector.getElem_ofFn]
    exact htr.2.2.2.2.2 u col
  have hB₀ : ∀ u col : Fin n, (c₀[u.1][col.1]).natAbs ≤ M₀ := by
    intro u col; simp [c₀, initCostTable, hM col u]
  have hexp : match edmondsTableAux root n a₀ c₀ with
      | some pTab => I.expectedOutParentList = (List.finRange n).map fun v => (pTab[v.1]).1
      | none => I.expectedOutParentList = [] := by
    have hmap_eq := edmondsOut_fin_map_eq I.digraph cost root
    rw [show initAdjTable n _ = a₀ from rfl, show initCostTable n _ = c₀ from rfl] at hmap_eq
    unfold ArborescenceInput.expectedOutParentList
    dsimp only [I] at hmap_eq ⊢
    revert hmap_eq
    cases edmondsTableAux root n a₀ c₀ <;>
      cases edmondsOut (ArborescenceInput.digraph ⟨n, root, adj, cost⟩) cost root <;> simp
  have hfin := finishArbProg_spec root a₀ c₀ s3 I.expectedOutParentList hfit_top hs3_fr hwb
    ha3 hc3 hB₀ hexp
  unfold edmondsOutProg
  dsimp only [I]
  refine ⟨⟨hfit_top, root.isLt, htr.1, hfin.1⟩, ?_, ?_, ?_, ?_⟩
  · exact validHistory_allocDirty_bind
      (hfit_top.of_le (by dsimp only [outAddr, ws]; omega))
      (validHistory_allocDirty_bind
        (hfit_top.of_le (by dsimp only [outAddr, ws]; omega))
        (validHistory_bind_step htr.2.1 hfin.2.1))
  · rw [memoryCost_bind', memoryCost_allocDirty]
    simp only [client_simps]
    have cTr := htr.2.2.1
    have cFin := hfin.2.2.1
    dsimp only [s3, s1, outAddr, ws, I] at cTr cFin ⊢
    have hid : 1 + (1 + ((4 * n + 1) * n + (43 * n ^ 3 + 18 * n ^ 2 + 8 * n + 1))) =
        43 * n ^ 3 + 22 * n ^ 2 + 9 * n + 3 := by ring
    linarith only [cTr, cFin, hid]
  · simp only [client_simps]
    rw [hfin.2.2.2.1]
    exact hfin.2.2.2.2.1
  · simp only [client_simps]
    rw [hfin.2.2.2.1]
    exact hfin.2.2.2.2.2

end Cslib.Algorithms.WordRAM.Arborescence.Internal
