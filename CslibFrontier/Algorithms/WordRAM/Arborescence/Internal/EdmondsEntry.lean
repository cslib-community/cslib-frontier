/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.Arborescence.Internal.CoreSpec
import CslibFrontier.Algorithms.WordRAM.Arborescence.Internal.BasicSpec
import CslibFrontier.Algorithms.WordRAM.Arborescence.Internal.FinEnumBridges
import CslibFrontier.Foundations.Data.List.RowMajor
import CslibFrontier.Tactic.Realize

/-!
# Entry point `edmondsProg` and shared `finishArbProg` wrapper (internal)

Implements `finishArbProg` (running `edmondsCoreProg` on the workspace and formatting the
length-prefixed parent list) and `edmondsProg` (loading initialized input into the workspace),
with `Realizes .exact` and `O(n³)` specifications.
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

/-- Parameters for `finishArbProg`. -/
public structure FinishArbArgs where
  /-- Number of vertices. -/
  n : ℕ
  /-- Designated root vertex index. -/
  r : ℕ
  /-- Workspace base address. -/
  ws : ℕ
  /-- Output list base address. -/
  outAddr : ℕ

/-- Word encoding of `FinishArbArgs` into 4 consecutive registers. -/
public word_enc_structure encFinishArbArgs : FinishArbArgs where
  n : wordWords, r : wordWords, ws : wordWords, outAddr : wordWords

private instance : WordEncoding FinishArbArgs := ⟨4, encFinishArbArgs⟩

/-- Runs `edmondsCoreProg` and writes the length-prefixed parent list (or `0` when infeasible) at
`a.outAddr`. -/
public def finishArbProg (a : FinishArbArgs) : Memory.Prog ℕ := do
  let status ← edmondsCoreProg ⟨a.n, a.r, a.ws⟩
  if status = 1 then
    Memory.write a.outAddr a.n
    let _ ← copyWordsProg ⟨curParentBase a.ws a.n, a.outAddr + 1, a.n⟩
    pure a.outAddr
  else
    Memory.write a.outAddr 0
    pure a.outAddr

/-- Safety precondition for `finishArbProg`. -/
public abbrev FinishArbSafe (w : ℕ) (a : FinishArbArgs) (s₃ : Memory.State) : Prop :=
  let ca : CoreArgs := ⟨a.n, a.r, a.ws⟩
  let res := (Memory.spec 0).clientResult s₃ (forwardProg ca)
  let sf := (Memory.spec 0).clientState s₃ (forwardProg ca)
  let status := (Memory.spec 0).clientResult s₃ (edmondsCoreProg ca)
  let s₄ := (Memory.spec 0).clientState s₃ (edmondsCoreProg ca)
  let s₄w : Memory.State := ⟨Function.update s₄.mem a.outAddr a.n, s₄.frontier⟩
  a.outAddr = a.ws + wsSize a.n ∧ Fits w (a.outAddr + (a.n + 1) + 8) ∧
    iterationSafe forwardStep ForwardStepSafe w ca a.n ⟨0, 0, 0⟩ s₃ ∧
    (res.status = 1 →
      iterationSafe backwardStep BackwardStepSafe w ⟨a.n, a.ws, res.depth⟩ res.depth 0 sf) ∧
    (status = 1 →
      iterationSafe copyStep CopyStepSafe w ⟨curParentBase a.ws a.n, a.outAddr + 1, a.n⟩
        a.n 0 s₄w)

public theorem finishArbProg_realizes :
    Realizes .exact finishArbProg encFinishArbArgs wordWords FinishArbSafe (fun _ _ => 0) := by
  unfold finishArbProg
  realize [edmondsCoreProg_realizes, copyWordsProg_realizes]
  all_goals
    obtain ⟨hout, hfit, hfwd, hbwd, hcpOut⟩ := h
    first
    | exact hfwd
    | exact hbwd
    | exact hcpOut ‹_›
    | exact hfit.of_le (by rw [hout]; dsimp only [wsSize, curParentBase, frameBase]; nlinarith)

public theorem finishArbProg_spec {w n ws M₀ : ℕ} (root : Fin n)
    (a₀ : AdjTable n) (c₀ : CostTable ℤ n) (s₃ : Memory.State) (expected : List ℕ)
    (hfit_top : Fits w (ws + wsSize n + (n + 1) + 8))
    (hs₃_fr : s₃.frontier = ws + wsSize n + (n + 1))
    (hwb : Fits w (wordBound n M₀))
    (ha₃ : ∀ u col : Fin n,
      s₃.mem (curAdjBase ws n + u.val * n + col.val) = if a₀[u.val][col.val] then 1 else 0)
    (hc₃ : ∀ u col : Fin n,
      s₃.mem (curCostBase ws n + u.val * n + col.val) = Signed.encode c₀[u.val][col.val])
    (hB₀ : ∀ u col : Fin n, (c₀[u.val][col.val]).natAbs ≤ M₀)
    (hexp : match edmondsTableAux root n a₀ c₀ with
      | some pTab => expected = (List.finRange n).map fun v => (pTab[v.val]).val
      | none => expected = []) :
    let outAddr := ws + wsSize n
    let fa : FinishArbArgs := ⟨n, root.val, ws, outAddr⟩
    let s' := (Memory.spec 0).clientState s₃ (finishArbProg fa)
    FinishArbSafe w fa s₃ ∧
      (Memory.spec w).ValidHistory s₃ ((Memory.spec w).clientHistory s₃ (finishArbProg fa)) ∧
      memoryCost (finishArbProg fa) s₃ ≤ 43 * n ^ 3 + 18 * n ^ 2 + 8 * n + 1 ∧
      (Memory.spec 0).clientResult s₃ (finishArbProg fa) = outAddr ∧
      outputList s'.mem outAddr = expected ∧
      Fits w (outAddr + expected.length) := by
  let outAddr := ws + wsSize n
  let fa : FinishArbArgs := ⟨n, root.val, ws, outAddr⟩
  have hws_fit : WsFits w ws n := hfit_top.of_le (by omega)
  have hcore := edmondsCoreProg_spec root a₀ c₀ s₃ hws_fit
    (by rw [hs₃_fr]; omega) hwb ha₃ hc₃ hB₀
  let ca : CoreArgs := ⟨n, root.val, ws⟩
  let s₄ := (Memory.spec 0).clientState s₃ (edmondsCoreProg ca)
  have hs₄_fr : s₄.frontier = outAddr + (n + 1) := hcore.2.2.2.1.trans hs₃_fr
  cases haux : edmondsTableAux root n a₀ c₀ with
  | some pTab =>
    rw [haux] at hexp
    have hcore_res : (Memory.spec 0).clientResult s₃ (edmondsCoreProg ca) = 1 ∧
        ∀ v : Fin n, s₄.mem (curParentBase ws n + v.val) = (pTab[v.val]).val := by
      have h := hcore.2.2.2.2.2
      rwa [haux] at h
    let s₄w : Memory.State := ⟨Function.update s₄.mem outAddr n, s₄.frontier⟩
    let cpOut : CopyArgs := ⟨curParentBase ws n, outAddr + 1, n⟩
    have hcpOut := copyWordsProg_spec cpOut s₄w
      (by dsimp only [cpOut, s₄w]; rw [hs₄_fr]; dsimp only [outAddr, wsSize, curParentBase];
          nlinarith)
      (by dsimp only [cpOut, s₄w]; rw [hs₄_fr]; dsimp only [outAddr]; omega)
      (Or.inl (by dsimp only [cpOut, outAddr, wsSize, curParentBase]; nlinarith))
      (hfit_top.of_le (by dsimp only [cpOut, outAddr, wsSize, curParentBase]; nlinarith))
      (hfit_top.of_le (by dsimp only [cpOut, outAddr]; omega))
      (hfit_top.of_le (by dsimp only [cpOut, outAddr]; omega))
      (fun i hi => by
        dsimp only [cpOut, s₄w]
        rw [Function.update_of_ne (by dsimp only [outAddr, wsSize, curParentBase]; nlinarith),
          hcore_res.2 ⟨i, hi⟩]
        dsimp only
        exact hfit_top.of_le (by have := (pTab[i]).isLt; omega))
    unfold finishArbProg
    refine ⟨⟨rfl, hfit_top, hcore.1.2.1, hcore.1.2.2, fun _ => hcpOut.1⟩, ?_, ?_, ?_, ?_, ?_⟩
    · refine validHistory_bind_step hcore.2.1 ?_
      change (Memory.spec w).ValidHistory s₄
        ((Memory.spec w).clientHistory s₄
          (if (Memory.spec 0).clientResult s₃ (edmondsCoreProg ca) = 1 then
            Memory.write outAddr n >>= fun _ => copyWordsProg cpOut >>= fun _ => pure outAddr
          else Memory.write outAddr 0 >>= fun _ => pure outAddr))
      rw [hcore_res.1]
      simp only [↓reduceIte]
      exact validHistory_write_bind (by rw [hs₄_fr]; dsimp only [outAddr]; omega)
        (hfit_top.of_le (by omega))
        (validHistory_bind_step hcpOut.2.1 (validHistory_pure w _ _))
    · rw [memoryCost_bind']
      have hcore_r := hcore_res.1
      have cCore := hcore.2.2.1
      have cOut := hcpOut.2.2.1
      dsimp only [fa, ca, cpOut, s₄w, s₄, outAddr] at hcore_r cCore cOut ⊢
      rw [hcore_r]
      simp only [↓reduceIte, memoryCost_bind', memoryCost_write, client_simps]
      linarith only [cCore, cOut]
    · have hcore_r := hcore_res.1
      dsimp only [fa, ca, outAddr] at hcore_r ⊢
      simp [client_simps, hcore_r]
    · have hcore_r := hcore_res.1
      have hcore_m := hcore_res.2
      have hcpOut_m := hcpOut.2.2.2.2.1
      have hcpOut_v := hcpOut.2.2.2.2.2
      dsimp only [fa, ca, cpOut, s₄w, s₄, outAddr] at hcore_r hcore_m hcpOut_m hcpOut_v ⊢
      simp only [client_simps, hcore_r, ↓reduceIte]
      rw [hexp, outputList_eq_iff]
      refine ⟨?_, fun i => ?_⟩
      · simp only [List.length_map, List.length_finRange]
        rw [hcpOut_m (ws + wsSize n) (by omega)]
        exact Function.update_self _ _ _
      · have hi : i.val < n := by simpa using i.isLt
        change ((Memory.spec 0).clientState _ _).mem (ws + wsSize n + 1 + i.val) =
          ((List.finRange n).map fun v => (pTab[v.val]).val)[i.val]
        simp only [List.getElem_map, List.getElem_finRange]
        rw [hcpOut_v i.val hi, Function.update_of_ne (by dsimp only [wsSize, curParentBase]; omega)]
        exact (hcore_m ⟨i.val, hi⟩).trans (by simp)
    · rw [hexp]
      simp only [List.length_map, List.length_finRange]
      exact hfit_top.of_le (by omega)
  | none =>
    rw [haux] at hexp
    have hcore_res : (Memory.spec 0).clientResult s₃ (edmondsCoreProg ca) = 0 := by
      have h := hcore.2.2.2.2.2
      rwa [haux] at h
    unfold finishArbProg
    refine ⟨⟨rfl, hfit_top, hcore.1.2.1, hcore.1.2.2,
        fun h1' => by rw [hcore_res] at h1'; cases h1'⟩, ?_, ?_, ?_, ?_, ?_⟩
    · refine validHistory_bind_step hcore.2.1 ?_
      change (Memory.spec w).ValidHistory s₄
        ((Memory.spec w).clientHistory s₄
          (if (Memory.spec 0).clientResult s₃ (edmondsCoreProg ca) = 1 then _
          else Memory.write outAddr 0 >>= fun _ => pure outAddr))
      rw [hcore_res]
      simp only [Nat.zero_ne_one, ↓reduceIte]
      exact validHistory_write_bind (by rw [hs₄_fr]; dsimp only [outAddr]; omega)
        (fits_zero w) (validHistory_pure w _ _)
    · rw [memoryCost_bind']
      have hcore_r := hcore_res
      have cCore := hcore.2.2.1
      dsimp only [fa, ca, outAddr] at hcore_r cCore ⊢
      rw [hcore_r]
      simp only [Nat.zero_ne_one, ↓reduceIte, memoryCost_bind', memoryCost_write, client_simps]
      linarith only [cCore]
    · have hcore_r := hcore_res
      dsimp only [fa, ca, outAddr] at hcore_r ⊢
      simp [client_simps, hcore_r]
    · have hcore_r := hcore_res
      dsimp only [fa, ca, outAddr] at hcore_r ⊢
      simp only [client_simps, hcore_r, Nat.zero_ne_one, ↓reduceIte]
      rw [hexp, outputList_eq_iff]
      exact ⟨Function.update_self _ _ _, fun i => Fin.elim0 i⟩
    · rw [hexp, List.length_nil]
      exact hfit_top.of_le (by omega)

/-- Word-RAM entry program solving rooted minimum-cost spanning in-arborescence for `(n, root)`. -/
public def edmondsProg (d : ℕ × ℕ) : Memory.Prog ℕ := do
  let n := Prod.fst d
  let r := Prod.snd d
  let ws ← Memory.allocDirty (wsSize n)
  let outAddr ← Memory.allocDirty (n + 1)
  let _ ← copyWordsProg ⟨3, curAdjBase ws n, 2 * (n * n)⟩
  finishArbProg ⟨n, r, ws, outAddr⟩

/-- Safety precondition for `edmondsProg`. -/
public abbrev EdmondsProgSafe (w : ℕ) (d : ℕ × ℕ) (s₀ : Memory.State) : Prop :=
  let n := Prod.fst d
  let r := Prod.snd d
  let ws := s₀.frontier
  let outAddr := ws + wsSize n
  let s1 : Memory.State := ⟨s₀.mem, outAddr + (n + 1)⟩
  let cp : CopyArgs := ⟨3, curAdjBase ws n, 2 * (n * n)⟩
  let s3 := (Memory.spec 0).clientState s1 (copyWordsProg cp)
  Fits w (outAddr + (n + 1) + 8) ∧ r < n ∧
    iterationSafe copyStep CopyStepSafe w cp (2 * (n * n)) 0 s1 ∧
    FinishArbSafe w ⟨n, r, ws, outAddr⟩ s3

public theorem edmondsProg_realizes :
    Realizes .exact edmondsProg pairWords wordWords EdmondsProgSafe (fun _ _ => 0) := by
  unfold edmondsProg
  realize [copyWordsProg_realizes, finishArbProg_realizes]
  all_goals
    obtain ⟨hfit, hr, hcp, hfin⟩ := h
    first
    | exact hcp
    | exact hfin
    | exact hfit.of_le (by dsimp only [wsSize, curAdjBase]; nlinarith)

public theorem edmondsProg_spec {w M₀ : ℕ} (I : ArborescenceInput)
    (hM : ∀ u v, (I.cost u v).natAbs ≤ M₀) (hwb : Fits w (wordBound I.n M₀)) :
    let s₀ := Memory.State.init I.encode
    let d := (I.n, I.root.val)
    let outAddr := (Memory.spec 0).clientResult s₀ (edmondsProg d)
    let s' := (Memory.spec 0).clientState s₀ (edmondsProg d)
    EdmondsProgSafe w d s₀ ∧
      (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ (edmondsProg d)) ∧
      memoryCost (edmondsProg d) s₀ ≤ 43 * I.n ^ 3 + 22 * I.n ^ 2 + 8 * I.n + 3 ∧
      outputList s'.mem outAddr = I.expectedParentList ∧
      Fits w (outAddr + I.expectedParentList.length) := by
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
  obtain ⟨hfit_len1, hin_fits⟩ := inputFits_arb_encode I hM hwb
  have hwf0 := Memory.wellFormed_init hin_fits hfit_len1
  let s1 : Memory.State := ⟨s₀.mem, outAddr + (n + 1)⟩
  let cp : CopyArgs := ⟨3, curAdjBase ws n, 2 * (n * n)⟩
  have hcp := copyWordsProg_spec cp s1
    (by dsimp only [cp, s1, outAddr, ws, wsSize] at hws_eq ⊢; rw [hws_eq]; omega)
    (by dsimp only [cp, s1, outAddr, ws, wsSize, curAdjBase]; omega)
    (Or.inl (by dsimp only [cp, ws, curAdjBase] at hws_eq ⊢; rw [hws_eq]))
    (hfit_top.of_le (by dsimp only [cp, outAddr, ws, wsSize] at hws_eq ⊢; rw [hws_eq]; omega))
    (hfit_top.of_le (by dsimp only [cp, outAddr, ws, wsSize, curAdjBase]; omega))
    (hfit_top.of_le (by dsimp only [cp, outAddr, ws, wsSize]; omega))
    (fun i _ => hwf0.mem_fits (3 + i))
  let s3 := (Memory.spec 0).clientState s1 (copyWordsProg cp)
  have hs3_fr : s3.frontier = outAddr + (n + 1) := hcp.2.2.2.1
  let a₀ := initAdjTable n fun u col => decide (I.digraph.Adj u col)
  let c₀ := initCostTable n cost
  have ha3 : ∀ u col : Fin n,
      s3.mem (curAdjBase ws n + u.val * n + col.val) = if a₀[u.val][col.val] then 1 else 0 := by
    intro u col
    have hlt : u.val * n + col.val < 2 * (n * n) := by
      have := List.mul_add_lt_sq u.isLt col.isLt; omega
    rw [show curAdjBase ws n + u.val * n + col.val = cp.dst + (u.val * n + col.val) by
        dsimp only [cp, ws, curAdjBase]; omega,
      hcp.2.2.2.2.2 _ hlt]
    dsimp only [cp, s1, a₀, initAdjTable, ArborescenceInput.digraph, I]
    simp only [Vector.getElem_ofFn]
    exact init_mem_encode_arb_adj I u col
  have hc3 : ∀ u col : Fin n,
      s3.mem (curCostBase ws n + u.val * n + col.val) = Signed.encode c₀[u.val][col.val] := by
    intro u col
    have hlt : n * n + (u.val * n + col.val) < 2 * (n * n) := by
      have := List.mul_add_lt_sq u.isLt col.isLt; omega
    rw [show curCostBase ws n + u.val * n + col.val = cp.dst + (n * n + (u.val * n + col.val)) by
        dsimp only [cp, ws, curAdjBase, curCostBase]; omega,
      hcp.2.2.2.2.2 _ hlt]
    dsimp only [cp, s1, c₀, initCostTable]
    simp only [Vector.getElem_ofFn]
    simpa [Nat.add_assoc] using init_mem_encode_arb_cost I u col
  have hB₀ : ∀ u col : Fin n, (c₀[u.val][col.val]).natAbs ≤ M₀ := by
    intro u col; simp [c₀, initCostTable, hM u col]
  have hexp : match edmondsTableAux root n a₀ c₀ with
      | some pTab => I.expectedParentList = (List.finRange n).map fun v => (pTab[v.val]).val
      | none => I.expectedParentList = [] := by
    have hmap_eq := edmonds_fin_map_eq I.digraph cost root
    rw [show initAdjTable n _ = a₀ from rfl, show initCostTable n _ = c₀ from rfl] at hmap_eq
    unfold ArborescenceInput.expectedParentList
    dsimp only [I] at hmap_eq ⊢
    revert hmap_eq
    cases edmondsTableAux root n a₀ c₀ <;>
      cases edmonds (ArborescenceInput.digraph ⟨n, root, adj, cost⟩) cost root <;> simp
  have hfin := finishArbProg_spec root a₀ c₀ s3 I.expectedParentList hfit_top hs3_fr hwb
    ha3 hc3 hB₀ hexp
  unfold edmondsProg
  dsimp only [I]
  refine ⟨⟨hfit_top, root.isLt, hcp.1, hfin.1⟩, ?_, ?_, ?_, ?_⟩
  · exact validHistory_allocDirty_bind
      (hfit_top.of_le (by dsimp only [outAddr, ws]; omega))
      (validHistory_allocDirty_bind
        (hfit_top.of_le (by dsimp only [outAddr, ws]; omega))
        (validHistory_bind_step hcp.2.1 hfin.2.1))
  · rw [memoryCost_bind', memoryCost_allocDirty]
    simp only [client_simps]
    have cCp := hcp.2.2.1
    have cFin := hfin.2.2.1
    dsimp only [s3, s1, cp, outAddr, ws, I] at cCp cFin ⊢
    have hid : 1 + (1 + (2 * (2 * (n * n)) + (43 * n ^ 3 + 18 * n ^ 2 + 8 * n + 1))) =
        43 * n ^ 3 + 22 * n ^ 2 + 8 * n + 3 := by ring
    linarith only [cCp, cFin, hid]
  · simp only [client_simps]
    rw [hfin.2.2.2.1]
    exact hfin.2.2.2.2.1
  · simp only [client_simps]
    rw [hfin.2.2.2.1]
    exact hfin.2.2.2.2.2

-- Transpose loader for `edmondsOutProg`

end Cslib.Algorithms.WordRAM.Arborescence.Internal
