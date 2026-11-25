/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.DFS.ForwardDFS
public import CslibFrontier.Algorithms.WordRAM.DFS.Transpose
public import CslibFrontier.Algorithms.WordRAM.DFS.Kosaraju
public import CslibFrontier.Computability.WordRAM.ListOutput
import all CslibFrontier.Algorithms.WordRAM.DFS.CSR
import all CslibFrontier.Algorithms.WordRAM.DFS.Visit
import all CslibFrontier.Algorithms.WordRAM.DFS.ForwardDFS
import all CslibFrontier.Algorithms.WordRAM.DFS.Transpose
import all CslibFrontier.Algorithms.WordRAM.DFS.Kosaraju
import CslibFrontier.Computability.WordRAM.SymbolicExec
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Ring

/-!
# End-to-end Word-RAM topological sort and Kosaraju SCC programs

## Main definitions

* `Cslib.Algorithms.WordRAM.DFS.sccIndexCode`: combined forward DFS, transpose, and Kosaraju
  peeling pass (`220 * N + 92 * Mc + 42` instructions).
* `Cslib.Algorithms.WordRAM.DFS.Graph`, `Cslib.Algorithms.WordRAM.DFS.Graph.m`,
  `Cslib.Algorithms.WordRAM.DFS.Graph.encodeCSR`, `Cslib.Algorithms.WordRAM.DFS.Graph.wordBound`.
* `Cslib.Algorithms.WordRAM.DFS.topoWords`, `Cslib.Algorithms.WordRAM.DFS.sccWords`.
* `Cslib.Algorithms.WordRAM.DFS.topoCode`, `Cslib.Algorithms.WordRAM.DFS.topoProgram`.
* `Cslib.Algorithms.WordRAM.DFS.sccCode`, `Cslib.Algorithms.WordRAM.DFS.sccProgram`.

## Main results

* `Cslib.Algorithms.WordRAM.DFS.sccIndexCode_spec`.
* `Cslib.Algorithms.WordRAM.DFS.Graph.csrAt_init`,
  `Cslib.Algorithms.WordRAM.DFS.Graph.inputFits_encodeCSR`.
* `Cslib.Algorithms.WordRAM.DFS.topoCode_spec`,
  `Cslib.Algorithms.WordRAM.DFS.computesListInTime_topoProgram`.
* `Cslib.Algorithms.WordRAM.DFS.sccCode_spec`,
  `Cslib.Algorithms.WordRAM.DFS.computesListInTime_sccProgram`.
* `Cslib.Algorithms.WordRAM.DFS.not_readsWidth_sccIndexCode`,
  `Cslib.Algorithms.WordRAM.DFS.not_readsWidth_topoProgram`,
  `Cslib.Algorithms.WordRAM.DFS.not_readsWidth_sccProgram`.
-/

public section

namespace Cslib.Algorithms.WordRAM.DFS

open Cslib.WordRAM
open Cslib.Algorithms.Lean.DFS

namespace Reg
/-- Arc count `m` (end-to-end programs). -/
private abbrev mArcs : Fin 28 := ⟨2, by decide⟩
end Reg

open Reg

local macro "reg_ne" : tactic =>
  `(tactic| exact Fin.ne_of_val_ne (by
    simp only [ne_eq, Fin.ext_iff, cZero, cOne, cThree, nVerts, offB, edgeB, visB, finB, stkB,
      curB, revOffB, revEdgeB, ordB, compB, iReg, pReg, finCnt, compIdxReg, oldFinReg, uReg, vReg,
      jReg, jEndReg, addr, mArcs, outReg] at *
    omega))

local macro "regs_lt" : tactic =>
  `(tactic| (
    repeat (first
      | rw [Data.write_regs_apply]
      | rw [Data.set_regs_of_ne (by reg_ne)])
    try rfl))

local macro "mem_upd" : tactic =>
  `(tactic| simp only [Data.set_mem, Data.set_mem_apply, Data.write_mem])

/-! ### Forward DFS, transpose and Kosaraju peeling as one pass (`O(N + M)`) -/

/-- Kosaraju's strongly connected components on the CSR graph at `kOffAddr wb`: forward DFS
finishing order, CSR transpose, and peeling the transpose in reverse finishing order, writing the
topological component index of every vertex to `kCompAddr wb N Mc`. -/
def sccIndexCode : Code .standard 28 :=
  forwardDFSCode.seq
    (transposeCSRCode.seq
      ((ram[ finB ← ordB + nVerts ]).seq kosarajuIndexCode))

/-- `sccIndexCode` does not read the word width. -/
theorem not_readsWidth_sccIndexCode : ¬ sccIndexCode.ReadsWidth := by decide +kernel

/-- `sccIndexCode` is `rand`-free. -/
theorem isRandFree_sccIndexCode : sccIndexCode.IsRandFree := by decide +kernel

/-- **Kosaraju's algorithm on the word RAM in `O(N + M)` instructions.** From the scratch layout
based at `wb` (with a CSR graph `adj` of at most `Mc` arcs at `kOffAddr wb`), `sccIndexCode`
writes `indexComponents (sccs adj (List.finRange N)) u` to `kCompAddr wb N Mc + u` for every
vertex `u`, leaving memory below `wb` unchanged. -/
theorem sccIndexCode_spec {N w : ℕ} (hN : 0 < N) (adj : Fin N → List (Fin N))
    (wb Mc : ℕ) (hmc : csrOffset adj N ≤ Mc)
    (hfit : Fits w (kTopAddr wb N Mc + Mc + 4)) {x : Data 28}
    (hregs : DfsRegs (kOffAddr wb) (kEdgeAddr wb N) (kVisAddr wb N Mc) (kOrdAddr wb N Mc)
      (kStkAddr wb N Mc) x)
    (hNv : x.regs nVerts = N) (hcur : x.regs curB = kCurAddr wb N Mc)
    (hroff : x.regs revOffB = kRevOffAddr wb N Mc)
    (hredge : x.regs revEdgeB = kRevEdgeAddr wb N Mc)
    (hordB : x.regs ordB = kOrdAddr wb N Mc) (hcompB : x.regs compB = kCompAddr wb N Mc)
    (hcsr : CSRAt adj (kOffAddr wb) (kEdgeAddr wb N) x.mem) :
    ∃ y, ExecWithin w sccIndexCode x y (220 * N + 92 * Mc + 42) ∧
      (∀ u : Fin N, y.mem (kCompAddr wb N Mc + u.val) =
        indexComponents (sccs adj (List.finRange N)) u) ∧
      (∀ a, a < wb → y.mem a = x.mem a) ∧
      (∀ r : Fin 28, r.val < 18 → r ≠ offB → r ≠ edgeB → r ≠ finB → y.regs r = x.regs r) := by
  obtain ⟨s₁, hs₁_ex, hs₁_olen, hs₁_omem, hs₁_csr, hs₁_out, hs₁_fr⟩ :=
    forwardDFSCode_spec hN adj wb Mc hmc hfit hregs hNv hcsr
  obtain ⟨s₂, hs₂_ex, hs₂_rcsr, hs₂_off, hs₂_edge, hs₂_out, hs₂_fr⟩ :=
    transposeCSRCode_spec adj wb Mc hmc hfit
      ((hs₁_fr cZero (by decide)).trans hregs.czero)
      ((hs₁_fr cOne (by decide)).trans hregs.cone)
      ((hs₁_fr nVerts (by decide)).trans hNv)
      ((hs₁_fr offB (by decide)).trans hregs.hoff)
      ((hs₁_fr edgeB (by decide)).trans hregs.hedge)
      ((hs₁_fr curB (by decide)).trans hcur)
      ((hs₁_fr revOffB (by decide)).trans hroff)
      ((hs₁_fr revEdgeB (by decide)).trans hredge)
      hs₁_csr
  have hs₂_fr0 : ∀ r : Fin 28, r.val < 18 → r ≠ offB → r ≠ edgeB → s₂.regs r = x.regs r :=
    fun r hr hno hne => (hs₂_fr r hr hno hne).trans (hs₁_fr r hr)
  let s₃ := s₂.set finB (kFinAddr wb N Mc)
  have hs₃_ex : ExecWithin w (ram[ finB ← ordB + nVerts ]) s₂ s₃ 1 := by
    have h_ordB : s₂.regs ordB = kOrdAddr wb N Mc :=
      (hs₂_fr0 ordB (by decide) (by decide) (by decide)).trans hordB
    have h_Nv : s₂.regs nVerts = N :=
      (hs₂_fr0 nVerts (by decide) (by decide) (by decide)).trans hNv
    have htriv : s₃ = s₂.set finB (kOrdAddr wb N Mc + N) := by
      simp only [s₃, kOrdAddr, kFinAddr]; ring_nf
    rw [htriv]
    have hf_on : Fits w (kOrdAddr wb N Mc + N) :=
      hfit.of_le (by simp only [kOrdAddr, kTopAddr]; omega)
    wram_exec [h_ordB, h_Nv, hf_on]
  have hs₃_fr : ∀ r : Fin 28, r.val < 18 → r ≠ offB → r ≠ edgeB → r ≠ finB →
      s₃.regs r = x.regs r := fun r hr h1 h2 h3 => by
    simp only [s₃]
    rw [Data.set_regs_of_ne h3]
    exact hs₂_fr0 r hr h1 h2
  have hs₃_dregs : DfsRegs (kRevOffAddr wb N Mc) (kRevEdgeAddr wb N Mc)
      (kVisAddr wb N Mc) (kFinAddr wb N Mc) (kStkAddr wb N Mc) s₃ :=
    { czero := (hs₃_fr cZero (by decide) (by decide) (by decide) (by decide)).trans hregs.czero
      cone := (hs₃_fr cOne (by decide) (by decide) (by decide) (by decide)).trans hregs.cone
      cthree := (hs₃_fr cThree (by decide) (by decide) (by decide) (by decide)).trans hregs.cthree
      hoff := by simp only [s₃]; rw [Data.set_regs_of_ne (by decide)]; exact hs₂_off
      hedge := by simp only [s₃]; rw [Data.set_regs_of_ne (by decide)]; exact hs₂_edge
      hvis := (hs₃_fr visB (by decide) (by decide) (by decide) (by decide)).trans hregs.hvis
      hfin := Data.set_regs_self _ _ _
      hstk := (hs₃_fr stkB (by decide) (by decide) (by decide) (by decide)).trans hregs.hstk }
  have hs₃_omem : ∀ idx (hidx : idx < N),
      s₃.mem (kOrdAddr wb N Mc + (N - 1 - idx)) =
        ((topologicalSort adj (List.finRange N))[idx]'(by
          rw [length_topologicalSort_finRange]; exact hidx)).val :=
    fun idx hidx => by
      simp only [s₃]; mem_upd
      rw [hs₂_out _ (by dsimp only [kRevOffAddr, kRevEdgeAddr, kCurAddr, kOrdAddr]; omega)]
      exact hs₁_omem idx hidx
  obtain ⟨y, hy_ex, hy_comp, hy_out, hy_fr⟩ :=
    kosarajuIndexCode_spec hN adj wb Mc hmc hfit hs₃_dregs
      ((hs₃_fr nVerts (by decide) (by decide) (by decide) (by decide)).trans hNv)
      ((hs₃_fr ordB (by decide) (by decide) (by decide) (by decide)).trans hordB)
      ((hs₃_fr compB (by decide) (by decide) (by decide) (by decide)).trans hcompB)
      hs₂_rcsr hs₁_olen hs₃_omem
  refine ⟨y, (hs₁_ex.seq (hs₂_ex.seq (hs₃_ex.seq hy_ex))).mono (by omega), hy_comp,
    fun a ha => ?_, fun r hr h1 h2 h3 => (hy_fr r hr).trans (hs₃_fr r hr h1 h2 h3)⟩
  rw [hy_out a (by simp only [kVisAddr]; omega)]
  simp only [s₃]; mem_upd
  rw [hs₂_out a (by dsimp only [kRevOffAddr, kRevEdgeAddr, kCurAddr]; omega),
    hs₁_out a (by dsimp only [kVisAddr, kOrdAddr, kStkAddr]; omega)]

/-! ### Graphs in CSR form -/

/-- A directed multigraph on `Fin n` given by successor lists; parallel arcs and self-loops are
allowed. -/
structure Graph where
  /-- Number of vertices. -/
  n : ℕ
  /-- Successor lists. -/
  adj : Fin n → List (Fin n)

namespace Graph

/-- Number of arcs `∑ u, (G.adj u).length`. -/
@[expose] def m (G : Graph) : ℕ := csrOffset G.adj G.n

/-- **CSR (offset-array) input encoding** `[n, m, off 0, …, off n] ++ arcs`, where
`off u = csrOffset G.adj u` counts the arcs leaving vertices below `u` and `arcs` lists the
successors of `0, …, n - 1` in successor-list order. -/
@[expose] def encodeCSR (G : Graph) : List ℕ :=
  G.n :: G.m :: ((List.range (G.n + 1)).map (csrOffset G.adj) ++
    (List.finRange G.n).flatMap fun u => (G.adj u).map Fin.val)

/-- Linear word-size envelope `16 * (n + m + 1)` covering the input and the scratch layout. -/
@[expose] def wordBound (G : Graph) : ℕ := 16 * (G.n + G.m + 1)

private theorem length_flatMap_take {N : ℕ} (adj : Fin N → List (Fin N)) (u : ℕ) :
    (((List.finRange N).take u).flatMap fun v => (adj v).map Fin.val).length =
      csrOffset adj u := by
  simp [csrOffset, List.length_flatMap]

private theorem length_arcs (G : Graph) :
    ((List.finRange G.n).flatMap fun v => (G.adj v).map Fin.val).length = G.m := by
  have h := length_flatMap_take G.adj G.n
  rwa [List.take_of_length_le (by simp)] at h

private theorem getElem?_arcs {N : ℕ} (adj : Fin N → List (Fin N)) (u : Fin N) (k : ℕ)
    (hk : k < (adj u).length) :
    ((List.finRange N).flatMap fun v => (adj v).map Fin.val)[csrOffset adj u.val + k]? =
      some ((adj u)[k]).val := by
  have hsplit : List.finRange N =
      (List.finRange N).take u.val ++ u :: (List.finRange N).drop (u.val + 1) := by
    conv_lhs => rw [← List.take_append_drop u.val (List.finRange N)]
    rw [List.drop_eq_getElem_cons (by simp)]
    simp
  rw [hsplit, List.flatMap_append, List.flatMap_cons,
    List.getElem?_append_right (by rw [length_flatMap_take]; omega), length_flatMap_take,
    Nat.add_sub_cancel_left, List.getElem?_append_left (by simpa using hk)]
  simp [hk]

/-- The CSR input encoding installs `G.adj` as a CSR graph at `kOffAddr 3`. -/
theorem csrAt_init (G : Graph) :
    CSRAt G.adj (kOffAddr 3) (kEdgeAddr 3 G.n) (Data.init G.encodeCSR : Data 28).mem := by
  have hoffs : ((List.range (G.n + 1)).map (csrOffset G.adj)).length = G.n + 1 := by simp
  refine ⟨fun u hu => ?_, fun u k hk => ?_⟩
  · rw [show kOffAddr 3 + u = u + 2 + 1 by simp only [kOffAddr]; omega, Data.init_mem_succ,
      List.getD_eq_getElem?_getD]
    simp only [encodeCSR, List.getElem?_cons_succ]
    rw [List.getElem?_append_left (by rw [hoffs]; omega)]
    simp [Nat.lt_succ_of_le hu]
  · rw [show kEdgeAddr 3 G.n + csrOffset G.adj u.val + k =
        G.n + 1 + (csrOffset G.adj u.val + k) + 1 + 1 + 1 by simp only [kEdgeAddr]; omega,
      Data.init_mem_succ, List.getD_eq_getElem?_getD]
    simp only [encodeCSR, List.getElem?_cons_succ]
    rw [List.getElem?_append_right (by rw [hoffs]; omega), hoffs, Nat.add_sub_cancel_left,
      getElem?_arcs G.adj u k hk]
    rfl

/-- Every word of `G.encodeCSR`, and its length, fits any word width admitting
`G.wordBound`. -/
theorem inputFits_encodeCSR (G : Graph) {w : ℕ} (hfit : Fits w G.wordBound) :
    InputFits w G.encodeCSR := by
  refine ⟨hfit.of_le ?_, fun v hv => hfit.of_le ?_⟩
  · simp only [encodeCSR, List.length_cons, List.length_append, List.length_map,
      List.length_range, length_arcs, wordBound]
    omega
  · simp only [encodeCSR, List.mem_cons, List.mem_append, List.mem_map, List.mem_range,
      List.mem_flatMap] at hv
    rcases hv with rfl | rfl | ⟨a, ha, rfl⟩ | ⟨u, -, e, -, rfl⟩
    · unfold wordBound; omega
    · unfold wordBound; omega
    · have := csrOffset_mono G.adj (by omega : a ≤ G.n)
      unfold wordBound m; omega
    · have := e.isLt
      unfold wordBound; omega

end Graph

/-! ### End-to-end programs -/

/-- Load the constants, `n`, `m`, and the scratch layout based at `wb = 3` with `Mc = m`,
directly above the CSR input. -/
private def setupCode : Code .standard 28 := ram[
  cZero ← #0; cOne ← #1; cThree ← #3;
  nVerts ← *cOne; addr ← cOne + cOne; mArcs ← *addr;
  offB ← cThree;
  edgeB ← offB + nVerts; edgeB ← edgeB + cOne;
  revOffB ← edgeB + mArcs;
  revEdgeB ← revOffB + nVerts; revEdgeB ← revEdgeB + cOne;
  curB ← revEdgeB + mArcs;
  visB ← curB + nVerts; visB ← visB + cOne;
  ordB ← visB + nVerts;
  finB ← ordB;
  stkB ← ordB + nVerts; stkB ← stkB + nVerts;
  compB ← stkB + nVerts; compB ← compB + nVerts; compB ← compB + nVerts ]

private theorem setupCode_spec (G : Graph) {w : ℕ} (hfit : Fits w G.wordBound) :
    ∃ s, ExecWithin w setupCode (Data.init G.encodeCSR) s 23 ∧
      s.mem = (Data.init G.encodeCSR : Data 28).mem ∧
      s.regs outReg = 0 ∧ s.regs nVerts = G.n ∧
      DfsRegs (kOffAddr 3) (kEdgeAddr 3 G.n) (kVisAddr 3 G.n G.m) (kOrdAddr 3 G.n G.m)
        (kStkAddr 3 G.n G.m) s ∧
      s.regs curB = kCurAddr 3 G.n G.m ∧ s.regs revOffB = kRevOffAddr 3 G.n G.m ∧
      s.regs revEdgeB = kRevEdgeAddr 3 G.n G.m ∧ s.regs ordB = kOrdAddr 3 G.n G.m ∧
      s.regs compB = kCompAddr 3 G.n G.m := by
  have hm1 : (Data.init G.encodeCSR : Data 28).mem 1 = G.n := rfl
  have hm2 : (Data.init G.encodeCSR : Data 28).mem 2 = G.m := rfl
  let Post (s : Data 28) : Prop :=
    s.mem = (Data.init G.encodeCSR : Data 28).mem ∧
      s.regs outReg = 0 ∧ s.regs nVerts = G.n ∧
      DfsRegs (kOffAddr 3) (kEdgeAddr 3 G.n) (kVisAddr 3 G.n G.m) (kOrdAddr 3 G.n G.m)
        (kStkAddr 3 G.n G.m) s ∧
      s.regs curB = kCurAddr 3 G.n G.m ∧ s.regs revOffB = kRevOffAddr 3 G.n G.m ∧
      s.regs revEdgeB = kRevEdgeAddr 3 G.n G.m ∧ s.regs ordB = kOrdAddr 3 G.n G.m ∧
      s.regs compB = kCompAddr 3 G.n G.m
  change ∃ s, ExecWithin w setupCode (Data.init G.encodeCSR) s 23 ∧ Post s
  unfold setupCode
  wram_exec [Data.init_regs, hm1, hm2]
  · dsimp only [Post]
    refine ⟨rfl, by wram_simp; exact Data.init_regs _ _, ?_,
      ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
    all_goals wram_simp
    all_goals
      dsimp only [kOffAddr, kEdgeAddr, kRevOffAddr, kRevEdgeAddr, kCurAddr, kVisAddr,
        kOrdAddr, kStkAddr, kCompAddr]
    all_goals omega
  all_goals exact hfit.of_le (by unfold Graph.wordBound; omega)

/-- One step of the reversed copy `out[i] := ord[N - 1 - i]`. -/
private def revCopyBody : Code .standard 28 := ram[
  addr ← nVerts - cOne; addr ← addr - iReg; addr ← ordB + addr; vReg ← *addr;
  addr ← outReg + iReg; addr ← addr + cOne; *addr ← vReg; iReg ← iReg + cOne ]

private theorem revCopyLoop_spec {N w : ℕ} (O P : ℕ) (hOP : O + N ≤ P)
    (hfit : Fits w (P + N + 1)) (f : ℕ → ℕ) :
    ∀ (rem k : ℕ) (x : Data 28) (_ : k + rem = N),
      (∀ q, q < N → x.mem (O + (N - 1 - q)) = f q) →
      (∀ q, q < k → x.mem (P + 1 + q) = f q) →
      x.regs cOne = 1 → x.regs nVerts = N → x.regs ordB = O → x.regs outReg = P →
      x.regs iReg = k →
      ∃ y, ExecWithin w (.loop (.lt iReg nVerts) revCopyBody) x y (10 * rem + 2) ∧
        (∀ q, q < N → y.mem (P + 1 + q) = f q) ∧
        (∀ a, a ≤ P → y.mem a = x.mem a) ∧
        (∀ r : Fin 28, r.val < 18 → y.regs r = x.regs r)
  | 0, k, x, hk, _, hcp, _, hNv, _, _, hi => by
    have hend : ¬ (Cond.lt iReg nVerts).Holds x := by
      change ¬ x.regs iReg < x.regs nVerts; omega
    exact ⟨x, ⟨2, by omega, Exec.loop_exit hend⟩, fun q hq => hcp q (by omega),
      fun _ _ => rfl, fun _ _ => rfl⟩
  | rem + 1, k, x, hk, hord, hcp, hc1, hNv, hO, hP, hi => by
    have hm : x.mem (O + (N - 1 - k)) = f k := hord k (by omega)
    have hf1 : Fits w (N - 1) := hfit.of_le (by omega)
    have hf2 : Fits w (N - 1 - k) := hfit.of_le (by omega)
    have hf3 : Fits w (O + (N - 1 - k)) := hfit.of_le (by omega)
    have hf4 : Fits w (P + k) := hfit.of_le (by omega)
    have hf5 : Fits w (P + k + 1) := hfit.of_le (by omega)
    have hf6 : Fits w (k + 1) := hfit.of_le (by omega)
    let StepPost (x₁ : Data 28) : Prop :=
      (∀ q, q < N → x₁.mem (O + (N - 1 - q)) = f q) ∧
        (∀ q, q < k + 1 → x₁.mem (P + 1 + q) = f q) ∧
        (∀ a, a ≤ P → x₁.mem a = x.mem a) ∧
        x₁.regs iReg = k + 1 ∧
        (∀ r : Fin 28, r.val < 18 → x₁.regs r = x.regs r)
    have hstep : ∃ x₁, ExecWithin w revCopyBody x x₁ 8 ∧ StepPost x₁ := by
      unfold revCopyBody
      wram_exec [hc1, hNv, hO, hP, hi, hm, hf1, hf2, hf3, hf4, hf5, hf6]
      dsimp only [StepPost]
      refine ⟨fun q hq => ?_, fun q hq => ?_, fun a ha => ?_, by wram_simp, fun r hr => ?_⟩
      · mem_upd
        rw [Function.update_of_ne (by omega)]
        exact hord q hq
      · mem_upd
        by_cases hqk : q = k
        · rw [hqk, show P + 1 + k = P + k + 1 by omega, Function.update_self]
        · rw [Function.update_of_ne (by omega)]
          exact hcp q (by omega)
      · mem_upd
        exact Function.update_of_ne (by omega) _ _
      · regs_lt
    obtain ⟨x₁, hx₁_ex, hx₁_ord, hx₁_cp, hx₁_low, hx₁_i, hx₁_fr⟩ := hstep
    obtain ⟨y, hy_ex, hy_cp, hy_low, hy_fr⟩ :=
      revCopyLoop_spec O P hOP hfit f rem (k + 1) x₁ (by omega) hx₁_ord hx₁_cp
        ((hx₁_fr cOne (by decide)).trans hc1) ((hx₁_fr nVerts (by decide)).trans hNv)
        ((hx₁_fr ordB (by decide)).trans hO) ((hx₁_fr outReg (by decide)).trans hP) hx₁_i
    obtain ⟨t₁, ht₁, he₁⟩ := hx₁_ex
    obtain ⟨t₂, ht₂, he₂⟩ := hy_ex
    have hlt : (Cond.lt iReg nVerts).Holds x := by
      change x.regs iReg < x.regs nVerts; omega
    exact ⟨y, ⟨t₁ + t₂ + 2, by omega, Exec.loop_iter hlt he₁ he₂⟩, hy_cp,
      fun a ha => (hy_low a ha).trans (hx₁_low a ha),
      fun r hr => (hy_fr r hr).trans (hx₁_fr r hr)⟩

/-- Topological-sort output: `topologicalSort G.adj (List.finRange G.n)` (the vertices in reverse
DFS finishing order) as vertex numbers. -/
@[expose] def topoWords (G : Graph) : List ℕ :=
  (topologicalSort G.adj (List.finRange G.n)).map Fin.val

/-- Strongly-connected-component output: the topological component index
`indexComponents (sccs G.adj (List.finRange G.n)) v` of each vertex `v = 0, …, n - 1`. -/
@[expose] def sccWords (G : Graph) : List ℕ :=
  (List.finRange G.n).map (indexComponents (sccs G.adj (List.finRange G.n)))

/-- Structured topological sort: setup, forward DFS, and reversed copy of the finishing order. -/
def topoCode : Code .standard 28 :=
  setupCode.seq
    (Code.branch (.eq nVerts cZero)
      (ram[ *cZero ← cZero ])
      (forwardDFSCode.seq
        ((ram[ outReg ← ordB + nVerts; *outReg ← nVerts; iReg ← cZero ]).seq
          (Code.loop (.lt iReg nVerts) revCopyBody))))

/-- Structured strongly-connected-component indexing: setup, then `sccIndexCode`. -/
def sccCode : Code .standard 28 :=
  setupCode.seq
    (Code.branch (.eq nVerts cZero)
      (ram[ *cZero ← cZero ])
      (sccIndexCode.seq (ram[ outReg ← compB - cOne; *outReg ← nVerts ])))

/-- Flat topological-sort program returning `topoWords G` via `ExecutesList`. -/
def topoProgram : Program .standard 28 := topoCode.program outReg

/-- Flat strongly-connected-component program returning `sccWords G` via `ExecutesList`. -/
def sccProgram : Program .standard 28 := sccCode.program outReg

private theorem n_eq_zero_branch {w : ℕ} {s : Data 28} (hs_out : s.regs outReg = 0)
    (hs_n : s.regs nVerts = 0) (hs_0 : s.regs cZero = 0) (pos : Code .standard 28) :
    ∃ y, ExecWithin w (Code.branch (.eq nVerts cZero) (ram[ *cZero ← cZero ]) pos) s y 2 ∧
      y.regs outReg = 0 ∧ outputList y.mem 0 = [] := by
  have hcond : (Cond.eq nVerts cZero).Holds s := by
    change s.regs nVerts = s.regs cZero; omega
  have hst : Exec (B := .standard) w (ram[ *cZero ← cZero ]) s (s.write 0 0) 1 := by
    have h := Exec.store (B := .standard) (w := w) (x := s) (a := cZero) (s := cZero)
    rwa [hs_0] at h
  refine ⟨s.write 0 0, ⟨2, le_rfl, Exec.branch_pos hcond hst⟩, hs_out, ?_⟩
  rw [outputList_eq_iff]
  exact ⟨Data.write_mem_self _ _ _, Block.holdsList_nil _ _⟩

private theorem topoWords_eq_nil (G : Graph) (hn0 : G.n = 0) : topoWords G = [] := by
  apply List.eq_nil_of_length_eq_zero
  rw [topoWords, List.length_map, length_topologicalSort_finRange, hn0]

private theorem sccWords_eq_nil (G : Graph) (hn0 : G.n = 0) : sccWords G = [] := by
  apply List.eq_nil_of_length_eq_zero
  rw [sccWords, List.length_map, List.length_finRange, hn0]

private theorem fits_top (G : Graph) {w : ℕ} (hfit : Fits w G.wordBound) :
    Fits w (kTopAddr 3 G.n G.m + G.m + 4) :=
  hfit.of_le (by simp only [kTopAddr, Graph.wordBound]; omega)

/-- **Linear-time topological sort on the word RAM.** From the CSR input `G.encodeCSR`, `topoCode`
leaves `topoWords G` (the reverse DFS finishing order, which by
`Cslib.Algorithms.Lean.DFS.isTopologicalOrder_topologicalSort_iff` is a topological order exactly
when `G` is acyclic) at the address in `outReg`, within `128 * (G.n + G.m + 1) - 1` instructions at
every word width `w` with `Fits w G.wordBound`. -/
theorem topoCode_spec (G : Graph) {w : ℕ} (hfit : Fits w G.wordBound) :
    ∃ y, ExecWithin w topoCode (Data.init G.encodeCSR) y (128 * (G.n + G.m + 1) - 1) ∧
      outputList y.mem (y.regs outReg) = topoWords G ∧
      Fits w (y.regs outReg + (topoWords G).length) := by
  obtain ⟨s, hs_ex, hs_mem, hs_out, hs_n, hs_r, -, -, -, hs_ord, -⟩ :=
    setupCode_spec G hfit
  by_cases hn0 : G.n = 0
  · obtain ⟨y, hy_ex, hy_out, hy_list⟩ :=
      n_eq_zero_branch hs_out (hs_n.trans hn0) hs_r.czero _
    refine ⟨y, (hs_ex.seq hy_ex).mono (by omega), ?_, ?_⟩
    · rw [hy_out, hy_list, topoWords_eq_nil G hn0]
    · rw [hy_out, topoWords_eq_nil G hn0]; exact fits_zero w
  have hN : 0 < G.n := Nat.pos_of_ne_zero hn0
  have hncond : ¬ (Cond.eq nVerts cZero).Holds s := by
    have := hs_r.czero
    change ¬ s.regs nVerts = s.regs cZero; omega
  have hfit_top := fits_top G hfit
  obtain ⟨s₁, hs₁_ex, -, hs₁_omem, -, -, hs₁_fr⟩ :=
    forwardDFSCode_spec hN G.adj 3 G.m le_rfl hfit_top hs_r hs_n (hs_mem ▸ G.csrAt_init)
  set O := kOrdAddr 3 G.n G.m with hO_def
  set P := O + G.n with hP_def
  have hP_fit : Fits w (P + G.n + 1) := hfit.of_le (by
    rw [hP_def, hO_def]; simp only [kOrdAddr, Graph.wordBound]; omega)
  let x₂ := ((s₁.set outReg P).write P G.n).set iReg 0
  have hs₂_ex : ExecWithin (B := .standard) w
      (ram[ outReg ← ordB + nVerts; *outReg ← nVerts; iReg ← cZero ]) s₁ x₂ 3 := by
    have h_ord : s₁.regs ordB = O := (hs₁_fr ordB (by decide)).trans hs_ord
    have h_n : s₁.regs nVerts = G.n := (hs₁_fr nVerts (by decide)).trans hs_n
    have h_0 : s₁.regs cZero = 0 := (hs₁_fr cZero (by decide)).trans hs_r.czero
    have hf_P : Fits w P := hP_fit.of_le (by omega)
    have htriv : x₂ = ((s₁.set outReg (O + G.n)).write (O + G.n) G.n).set iReg 0 := rfl
    wram_exec [h_ord, h_n, h_0, hf_P]
  have hlen : (topoWords G).length = G.n := by
    rw [topoWords, List.length_map, length_topologicalSort_finRange]
  obtain ⟨y, hy_ex, hy_cp, hy_low, hy_fr⟩ :=
    revCopyLoop_spec O P le_rfl hP_fit (fun q => (topoWords G).getD q 0) G.n 0 x₂ (by omega)
      (fun q hq => by
        simp only [x₂]; mem_upd
        rw [Function.update_of_ne (by omega), hs₁_omem q hq,
          List.getD_eq_getElem _ 0 (by rw [hlen]; exact hq)]
        simp [topoWords])
      (fun q hq => absurd hq (Nat.not_lt_zero q))
      (by simp only [x₂]; wram_simp; exact (hs₁_fr cOne (by decide)).trans hs_r.cone)
      (by simp only [x₂]; wram_simp; exact (hs₁_fr nVerts (by decide)).trans hs_n)
      (by simp only [x₂]; wram_simp; exact (hs₁_fr ordB (by decide)).trans hs_ord)
      (by simp only [x₂]; wram_simp)
      (by simp only [x₂]; wram_simp)
  have hy_out : y.regs outReg = P :=
    (hy_fr outReg (by decide)).trans (by simp only [x₂]; wram_simp)
  have hbr : ExecWithin w
      (Code.branch (.eq nVerts cZero) (ram[ *cZero ← cZero ])
        (forwardDFSCode.seq
          ((ram[ outReg ← ordB + nVerts; *outReg ← nVerts; iReg ← cZero ]).seq
            (Code.loop (.lt iReg nVerts) revCopyBody))))
      s y (97 * G.n + 36 * G.m + 17) := by
    obtain ⟨t, ht, he⟩ := (hs₁_ex.seq (hs₂_ex.seq hy_ex)).mono
      (show 87 * G.n + 36 * G.m + 10 + (3 + (10 * G.n + 2)) ≤ 97 * G.n + 36 * G.m + 15 by omega)
    exact ⟨t + 2, by omega, Exec.branch_neg hncond he⟩
  refine ⟨y, (hs_ex.seq hbr).mono (by omega), ?_, ?_⟩
  · rw [hy_out, outputList_eq_iff]
    refine ⟨?_, fun i => ?_⟩
    · rw [hy_low P le_rfl, hlen]
      simp only [x₂]; mem_upd
      rw [Function.update_self]
    · change y.mem (P + 1 + i.val) = (topoWords G)[i.val]
      have hi : i.val < G.n := by
        have h : i.val < (topoWords G).length := i.isLt
        omega
      rw [hy_cp i.val hi, List.getD_eq_getElem _ 0 (by exact i.isLt)]
  · rw [hy_out, hlen]; exact hP_fit.of_le (by omega)

/-- **Linear-time Kosaraju strongly connected components on the word RAM.** From the CSR input
`G.encodeCSR`, `sccCode` leaves `sccWords G` (each vertex's topological component index in
`Cslib.Algorithms.Lean.DFS.sccs`; by
`Cslib.Algorithms.Lean.DFS.IsSCCCondensation.indexComponents_eq_iff` two vertices receive the same
index exactly when they are strongly connected) at the address in `outReg`, within
`256 * (G.n + G.m + 1) - 1` instructions at every word width `w` with `Fits w G.wordBound`. -/
theorem sccCode_spec (G : Graph) {w : ℕ} (hfit : Fits w G.wordBound) :
    ∃ y, ExecWithin w sccCode (Data.init G.encodeCSR) y (256 * (G.n + G.m + 1) - 1) ∧
      outputList y.mem (y.regs outReg) = sccWords G ∧
      Fits w (y.regs outReg + (sccWords G).length) := by
  obtain ⟨s, hs_ex, hs_mem, hs_out, hs_n, hs_r, hs_cur, hs_roff, hs_redge, hs_ord, hs_comp⟩ :=
    setupCode_spec G hfit
  by_cases hn0 : G.n = 0
  · obtain ⟨y, hy_ex, hy_out, hy_list⟩ :=
      n_eq_zero_branch hs_out (hs_n.trans hn0) hs_r.czero _
    refine ⟨y, (hs_ex.seq hy_ex).mono (by omega), ?_, ?_⟩
    · rw [hy_out, hy_list, sccWords_eq_nil G hn0]
    · rw [hy_out, sccWords_eq_nil G hn0]; exact fits_zero w
  have hN : 0 < G.n := Nat.pos_of_ne_zero hn0
  have hncond : ¬ (Cond.eq nVerts cZero).Holds s := by
    have := hs_r.czero
    change ¬ s.regs nVerts = s.regs cZero; omega
  have hfit_top := fits_top G hfit
  obtain ⟨s₁, hs₁_ex, hs₁_comp, -, hs₁_fr⟩ :=
    sccIndexCode_spec hN G.adj 3 G.m le_rfl hfit_top hs_r hs_n hs_cur hs_roff hs_redge hs_ord
      hs_comp (hs_mem ▸ G.csrAt_init)
  set C := kCompAddr 3 G.n G.m with hC_def
  set P := C - 1 with hP_def
  have hC : C = P + 1 := by rw [hP_def, hC_def]; simp only [kCompAddr]; omega
  have hP_fit : Fits w (P + G.n + 1) := hfit.of_le (by
    rw [hP_def, hC_def]; simp only [kCompAddr, Graph.wordBound]; omega)
  let y := (s₁.set outReg P).write P G.n
  have hs₂_ex : ExecWithin (B := .standard) w (ram[ outReg ← compB - cOne; *outReg ← nVerts ])
      s₁ y 2 := by
    have h_c : s₁.regs compB = C :=
      (hs₁_fr compB (by decide) (by decide) (by decide) (by decide)).trans hs_comp
    have h_1 : s₁.regs cOne = 1 :=
      (hs₁_fr cOne (by decide) (by decide) (by decide) (by decide)).trans hs_r.cone
    have h_n : s₁.regs nVerts = G.n :=
      (hs₁_fr nVerts (by decide) (by decide) (by decide) (by decide)).trans hs_n
    have hf_P : Fits w P := hP_fit.of_le (by omega)
    have htriv : y = (s₁.set outReg (C - 1)).write (C - 1) G.n := rfl
    wram_exec [h_c, h_1, h_n, hf_P]
  have hlen : (sccWords G).length = G.n := by
    rw [sccWords, List.length_map, List.length_finRange]
  have hy_out : y.regs outReg = P := by simp only [y]; wram_simp
  have hbr : ExecWithin w
      (Code.branch (.eq nVerts cZero) (ram[ *cZero ← cZero ])
        (sccIndexCode.seq (ram[ outReg ← compB - cOne; *outReg ← nVerts ])))
      s y (220 * G.n + 92 * G.m + 46) := by
    obtain ⟨t, ht, he⟩ := hs₁_ex.seq hs₂_ex
    exact ⟨t + 2, by omega, Exec.branch_neg hncond he⟩
  refine ⟨y, (hs_ex.seq hbr).mono (by omega), ?_, ?_⟩
  · rw [hy_out, outputList_eq_iff]
    refine ⟨?_, fun i => ?_⟩
    · rw [hlen]; simp only [y]; mem_upd; rw [Function.update_self]
    · change y.mem (P + 1 + i.val) = (sccWords G)[i.val]
      have hi : i.val < G.n := by
        have h : i.val < (sccWords G).length := i.isLt
        omega
      simp only [y]; mem_upd
      rw [Function.update_of_ne (by omega), ← hC,
        show C + i.val = C + (⟨i.val, hi⟩ : Fin G.n).val from rfl, hs₁_comp ⟨i.val, hi⟩]
      simp [sccWords]
  · rw [hy_out, hlen]; exact hP_fit.of_le (by omega)

/-- `topoProgram` computes `topoWords` in `O(n + m)` instructions
(`Program.ComputesListInTime`). -/
theorem computesListInTime_topoProgram :
    topoProgram.ComputesListInTime (fun _ G => G.encodeCSR)
      (fun G _ => 128 * (G.n + G.m + 1)) (fun G w => Fits w G.wordBound) topoWords := by
  intro G w hfit _
  obtain ⟨y, ⟨steps, hsteps, hexec⟩, hylist, hyfit⟩ := topoCode_spec G hfit
  refine ⟨steps + 1, ?_, by dsimp only; omega⟩
  have hex := hexec.executesList outReg (by rwa [hylist])
  rwa [hylist] at hex

/-- `sccProgram` computes `sccWords` in `O(n + m)` instructions
(`Program.ComputesListInTime`). -/
theorem computesListInTime_sccProgram :
    sccProgram.ComputesListInTime (fun _ G => G.encodeCSR)
      (fun G _ => 256 * (G.n + G.m + 1)) (fun G w => Fits w G.wordBound) sccWords := by
  intro G w hfit _
  obtain ⟨y, ⟨steps, hsteps, hexec⟩, hylist, hyfit⟩ := sccCode_spec G hfit
  refine ⟨steps + 1, ?_, by dsimp only; omega⟩
  have hex := hexec.executesList outReg (by rwa [hylist])
  rwa [hylist] at hex

/-- `topoProgram` does not read the word width. -/
theorem not_readsWidth_topoProgram : ¬ topoProgram.ReadsWidth := by
  apply Code.not_readsWidth_program
  decide +kernel

/-- `topoProgram` is `rand`-free. -/
theorem isRandFree_topoProgram : topoProgram.IsRandFree := by
  rw [topoProgram, Code.isRandFree_program]
  decide +kernel

/-- `sccProgram` does not read the word width. -/
theorem not_readsWidth_sccProgram : ¬ sccProgram.ReadsWidth := by
  apply Code.not_readsWidth_program
  decide +kernel

/-- `sccProgram` is `rand`-free. -/
theorem isRandFree_sccProgram : sccProgram.IsRandFree := by
  rw [sccProgram, Code.isRandFree_program]
  decide +kernel

end Cslib.Algorithms.WordRAM.DFS
