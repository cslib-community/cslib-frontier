/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.TwoSAT.Defs
public import CslibFrontier.Computability.WordRAM.ListOutput
public import CslibFrontier.Computability.WordRAM.Notation
import CslibFrontier.Algorithms.WordRAM.DFS.Programs
import CslibFrontier.Algorithms.WordRAM.TwoSAT.ClauseCheck
import CslibFrontier.Algorithms.WordRAM.TwoSAT.EquivDFS
import CslibFrontier.Algorithms.WordRAM.TwoSAT.Extract
import CslibFrontier.Algorithms.WordRAM.TwoSAT.ImplCSR
import CslibFrontier.Algorithms.WordRAM.TwoSAT.Layout
import CslibFrontier.Foundations.Data.List.Fold
import Mathlib.Data.List.GetD

/-!
# End-to-end linear-time Word-RAM 2-SAT solver (`solver`, `program`)

Proves input-fit and output-decoding specifications (`Instance.inputFits_encode`,
`decodeAnswer_answerWords`, `answerWords_eq_nil_iff`, `eval_of_decodeAnswer_eq_some`) and combines
clause validation, CSR implication-graph construction, Kosaraju SCC indexing, and witness extraction
into `solver` and `program`, proving `O(n + |φ|)` execution (`solver_spec`, `program_spec`,
`computesListInTime_program`), width-independence, and determinism.
-/

public section

namespace Cslib.Algorithms.WordRAM.TwoSAT

open Cslib.Logic.PL Cslib.WordRAM
open Cslib.Algorithms.Lean.DFS Cslib.Algorithms.Lean.TwoSAT
open Cslib.Algorithms.WordRAM.ClauseCode
open Reg Cslib.Algorithms.WordRAM.DFS Cslib.Algorithms.WordRAM.DFS.Reg

namespace Instance

/-- Every word of `G.encode`, together with its length, fits in any word width admitting
`G.wordBound`. -/
theorem inputFits_encode (G : Instance) {w : ℕ} (hfit : Fits w G.wordBound) :
    InputFits w G.encode := by
  refine ⟨hfit.of_le (by simp only [G.encode_length, wordBound]; omega),
    fun v hv => hfit.of_le ?_⟩
  unfold wordBound
  simp only [encode, List.mem_cons, List.mem_flatMap, encodeClauseBy, List.mem_map] at hv
  rcases hv with rfl | rfl | ⟨c, hc, rfl | ⟨ℓ, _, rfl⟩⟩
  · omega
  · omega
  · have : c.length ≤ G.totalLits := List.le_sum_of_mem (List.mem_map_of_mem hc)
    omega
  · have := ℓ.1.isLt
    have := Bool.toNat_le ℓ.2
    unfold litCodeBy
    omega

end Instance

/-- Decoding `answerWords G` recovers `TwoSAT.solveFin G.n G.φ` losslessly. -/
@[simp]
theorem decodeAnswer_answerWords (G : Instance) :
    decodeAnswer G (answerWords G) = solveFin G.n G.φ := by
  unfold answerWords
  cases h : solveFin G.n G.φ with
  | none => rfl
  | some σ =>
    simp only [encodeAssignment, decodeAnswer, Option.some.injEq]
    funext v
    rw [List.getD_eq_getElem _ 0 (by simp [v.isLt])]
    cases hσ : σ v <;> simp [hσ]

/-- `answerWords G` is empty if and only if `G.φ` is either not width-at-most-`2` or
unsatisfiable. -/
theorem answerWords_eq_nil_iff (G : Instance) :
    answerWords G = [] ↔ ¬ ((∀ c ∈ G.φ, c.length ≤ 2) ∧ G.φ.Satisfiable) := by
  rw [← isSome_solveFin_iff]
  unfold answerWords
  cases solveFin G.n G.φ <;> simp [encodeAssignment]

/-- Any assignment decoded from `answerWords G` witnesses width `≤ 2` and satisfies `G.φ`. -/
theorem eval_of_decodeAnswer_eq_some {G : Instance} {σ : Fin G.n → Bool}
    (h : decodeAnswer G (answerWords G) = some σ) :
    (∀ c ∈ G.φ, c.length ≤ 2) ∧ G.φ.eval σ = true := by
  exact solveFin_eq_some (decodeAnswer_answerWords G ▸ h)

/-- Structured standard-basis Word-RAM solver for 2-SAT. -/
def solver : Code .standard 28 :=
  headerSetupCode.seq
    (checkClausesCode.seq
      (.branch (.eq compIdxReg cOne)
        (.branch (.eq nv cZero)
          (ram[ *outBase ← cOne; addr ← outBase + cOne; *addr ← cOne ])
          (setupWorkRegsCode.seq
            (buildImplCSRCode.seq
              (sccIndexCode.seq extractAssignmentCode))))
        (ram[ *outBase ← cZero ])))

/-- Flat standard-basis Word-RAM 2-SAT program returning `answerWords G` via `ExecutesList`. -/
def program : Program .standard 28 := solver.program outBase

/-- Structured execution of `solver` computes `answerWords G` at `outAddrBase` within
`512 * (G.n + G.φ.length + 1) - 1` instructions. -/
theorem solver_spec (G : Instance) {w : ℕ} (hfit : Fits w G.wordBound) :
    ∃ y, ExecWithin w solver (Data.init G.encode) y (512 * (G.n + G.φ.length + 1) - 1) ∧
      y.regs outBase = G.outAddrBase ∧ outputList y.mem (y.regs outBase) = answerWords G := by
  have hm0 : (Data.init G.encode : Data 28).mem 0 = G.encode.length := Data.init_mem_zero _
  have hm1 : (Data.init G.encode : Data 28).mem 1 = G.n := rfl
  have hm2 : (Data.init G.encode : Data 28).mem 2 = G.φ.length := rfl
  have hf3 : Fits w 3 := G.fits_of_le hfit (by unfold Instance.wordBound; omega)
  have hf_ob1 : Fits w (G.outAddrBase + 1) := G.fits_of_le hfit (by
    simp only [Instance.outAddrBase, G.encode_length, Instance.wordBound]; omega)
  obtain ⟨s₀, hsetup, hs₀_mem, hs₀_0, hs₀_1, hs₀_2, hs₀_3, hs₀_ob, hs₀_nv, hs₀_mc⟩ :
      ∃ s₀, ExecWithin w headerSetupCode (Data.init G.encode) s₀ 8 ∧
      s₀.mem = (Data.init G.encode : Data 28).mem ∧
      s₀.regs cZero = 0 ∧ s₀.regs cOne = 1 ∧ s₀.regs cTwo = 2 ∧ s₀.regs cThree = 3 ∧
      s₀.regs outBase = G.outAddrBase ∧ s₀.regs nv = G.n ∧ s₀.regs mClauses = G.φ.length := by
    unfold headerSetupCode
    have hf_ob : Fits w (G.encode.length + 1) :=
      hf_ob1.of_le (by simp only [Instance.outAddrBase]; omega)
    wram_exec [Data.init_regs, hm0, hm1, hm2, hf3.of_le (by decide : 1 ≤ 3),
      hf3.of_le (by decide : 2 ≤ 3), hf3, hf_ob]
    exact ⟨rfl, by wram_simp, by wram_simp, by wram_simp, by wram_simp,
      by wram_simp; rfl, by wram_simp, by wram_simp⟩
  let s₁ := ((s₀.set compIdxReg 1).set pReg 3).set iReg 0
  have hchk_prep : ExecWithin (B := .standard) w
      (ram[ compIdxReg ← cOne; pReg ← cThree; iReg ← cZero ]) s₀ s₁ 3 := by
    wram_exec [hs₀_1, hs₀_3, hs₀_0]
  have hlen_enc : 3 + (G.φ.flatMap (encodeClauseBy Fin.val)).length = G.encode.length + 1 := by
    simp only [Instance.encode, List.length_cons]; omega
  obtain ⟨s₂, hs₂_ex, hs₂_mem, hs₂_ok, hs₂_fr⟩ :=
    checkClausesLoop_spec G hfit G.φ 0 3 true s₁ (by simp) hlen_enc
      (hs₀_mem ▸ clauseMemAt_init G)
      (by wram_simp [s₁, hs₀_0]) (by wram_simp [s₁, hs₀_1]) (by wram_simp [s₁, hs₀_2])
      (by wram_simp [s₁, hs₀_mc]) (by wram_simp [s₁]) (by wram_simp [s₁])
      (by wram_simp [s₁]; rfl)
  have hchk_ex : ExecWithin w checkClausesCode s₀ s₂ (12 * G.φ.length + 5) :=
    (hchk_prep.seq hs₂_ex).mono (by omega)
  have hs₂_fr0 : ∀ r : Fin 28, r.val < 18 → s₂.regs r = s₀.regs r := fun r hr =>
    (hs₂_fr r hr).trans (by wram_simp [s₁])
  have hs₂_0 : s₂.regs cZero = 0 := (hs₂_fr0 cZero (by decide)).trans hs₀_0
  have hs₂_1 : s₂.regs cOne = 1 := (hs₂_fr0 cOne (by decide)).trans hs₀_1
  have hs₂_2 : s₂.regs cTwo = 2 := (hs₂_fr0 cTwo (by decide)).trans hs₀_2
  have hs₂_3 : s₂.regs cThree = 3 := (hs₂_fr0 cThree (by decide)).trans hs₀_3
  have hs₂_ob : s₂.regs outBase = G.outAddrBase := (hs₂_fr0 outBase (by decide)).trans hs₀_ob
  have hs₂_nv : s₂.regs nv = G.n := (hs₂_fr0 nv (by decide)).trans hs₀_nv
  have hs₂_mc : s₂.regs mClauses = G.φ.length := (hs₂_fr0 mClauses (by decide)).trans hs₀_mc
  have hwrite_nil (s : Data 28) (h0 : s.regs cZero = 0) (h1 : s.regs cOne = 1)
      (hok : s.regs compIdxReg = 0) (hob : s.regs outBase = G.outAddrBase)
      (hans : answerWords G = []) {pos : Code .standard 28} :
      ExecWithin w (.branch (.eq compIdxReg cOne) pos (ram[ *outBase ← cZero ]))
        s (s.write G.outAddrBase 0) 3 ∧
      outputList (s.write G.outAddrBase 0).mem G.outAddrBase = answerWords G := by
    have hn : ¬ (Cond.eq compIdxReg cOne).Holds s := by
      change ¬ s.regs compIdxReg = s.regs cOne
      omega
    have hneg : ExecWithin (B := .standard) w (ram[ *outBase ← cZero ])
        s (s.write G.outAddrBase 0) 1 := by
      wram_exec [hob, h0]
    exact ⟨hneg.branch_neg hn,
      hans ▸ outputList_eq_iff.mpr ⟨Data.write_mem_self _ _ _, Block.holdsList_nil _ _⟩⟩
  cases hchk : checkClauses G.φ
  · -- Invalid clause width: return `[]`
    obtain ⟨hbr, hout⟩ := hwrite_nil s₂ hs₂_0 hs₂_1
      (hs₂_ok.trans (congrArg Bool.toNat hchk)) hs₂_ob
      (by simp [answerWords, solveFin, solve, hchk])
    exact ⟨_, (hsetup.seq (hchk_ex.seq hbr)).mono (by omega), hs₂_ob,
      (Data.write_regs_apply ..).symm ▸ hs₂_ob.symm ▸ hout⟩
  · -- Valid 2-CNF: every clause has `1 ≤ length ≤ 2`
    have hs₂_ok1 : s₂.regs compIdxReg = 1 := hs₂_ok.trans (congrArg Bool.toNat hchk)
    have hcond_chk : (Cond.eq compIdxReg cOne).Holds s₂ := by
      change s₂.regs compIdxReg = s₂.regs cOne; omega
    obtain ⟨hw_φ, hnil_φ⟩ := (checkClauses_eq_true_iff G.φ).1 hchk
    have hcs_φ : ∀ c ∈ G.φ, 1 ≤ c.length ∧ c.length ≤ 2 := fun c hc =>
      ⟨List.length_pos_of_ne_nil fun h => hnil_φ (h ▸ hc), hw_φ c hc⟩
    by_cases hn0 : G.n = 0
    · -- `G.n = 0`: `G.φ = []`, `answerWords G = [1]`
      have hφ_nil : G.φ = [] := List.eq_nil_iff_forall_not_mem.2 fun c hc => by
        obtain ⟨ℓ, -⟩ := List.exists_mem_of_length_pos (hcs_φ c hc).1
        have := ℓ.1.isLt
        omega
      have hcond_n0 : (Cond.eq nv cZero).Holds s₂ := by
        change s₂.regs nv = s₂.regs cZero; omega
      let y_n0 := ((s₂.write G.outAddrBase 1).set addr (G.outAddrBase + 1)).write
        (G.outAddrBase + 1) 1
      have hpos_n0 : ExecWithin (B := .standard) w
          (ram[ *outBase ← cOne; addr ← outBase + cOne; *addr ← cOne ]) s₂ y_n0 3 := by
        wram_exec [hs₂_ob, hs₂_1, hf_ob1]
      have hob_y : y_n0.regs outBase = G.outAddrBase := by wram_simp [y_n0, hs₂_ob]
      refine ⟨y_n0, (hsetup.seq (hchk_ex.seq
        ((hpos_n0.branch_pos hcond_n0).branch_pos hcond_chk))).mono (by omega), hob_y, ?_⟩
      rw [hob_y, outputList_eq_iff]
      have hans : answerWords G = [1] := match G, hn0, hφ_nil with | ⟨0, []⟩, rfl, rfl => rfl
      rw [hans]
      refine ⟨by wram_simp [y_n0]; rfl, fun ⟨i, hi⟩ => ?_⟩
      obtain rfl : i = 0 := by simpa using hi
      wram_simp [Block.read, y_n0]; rfl
    · -- `0 < G.n`: full Kosaraju + witness extraction
      have hn_pos : 0 < G.n := Nat.pos_of_ne_zero hn0
      have hN_pos : 0 < 2 * G.n := by omega
      have hncond_n0 : ¬ (Cond.eq nv cZero).Holds s₂ := by
        change ¬ s₂.regs nv = s₂.regs cZero; omega
      set wb := G.workBase
      set N := 2 * G.n
      set Mc := 2 * G.φ.length
      have hfit_top : Fits w (kTopAddr wb N Mc + Mc + 4) :=
        G.fits_of_le hfit (by
          simp only [wb, N, Mc, kTopAddr, Instance.workBase, Instance.outAddrBase,
            G.encode_length, Instance.wordBound]; omega)
      obtain ⟨s₃, hs₃_ex, hs₃_mem, hs₃_0, hs₃_1, hs₃_2, hs₃_3, hs₃_nv, hs₃_mc, hs₃_Nv, hs₃_ob,
        hs₃_off, hs₃_edge, hs₃_roff, hs₃_redge, hs₃_cur, hs₃_vis, hs₃_ord, hs₃_fin,
        hs₃_stk, hs₃_comp⟩ : ∃ s₃, ExecWithin w setupWorkRegsCode s₂ s₃ 19 ∧
          s₃.mem = s₂.mem ∧
          s₃.regs cZero = 0 ∧ s₃.regs cOne = 1 ∧ s₃.regs cTwo = 2 ∧ s₃.regs cThree = 3 ∧
          s₃.regs nv = G.n ∧ s₃.regs mClauses = G.φ.length ∧ s₃.regs nVerts = N ∧
          s₃.regs outBase = G.outAddrBase ∧
          s₃.regs offB = kOffAddr wb ∧ s₃.regs edgeB = kEdgeAddr wb N ∧
          s₃.regs revOffB = kRevOffAddr wb N Mc ∧ s₃.regs revEdgeB = kRevEdgeAddr wb N Mc ∧
          s₃.regs curB = kCurAddr wb N Mc ∧ s₃.regs visB = kVisAddr wb N Mc ∧
          s₃.regs ordB = kOrdAddr wb N Mc ∧ s₃.regs finB = kOrdAddr wb N Mc ∧
          s₃.regs stkB = kStkAddr wb N Mc ∧ s₃.regs compB = kCompAddr wb N Mc := by
        unfold setupWorkRegsCode
        wram_exec [hs₂_0, hs₂_1, hs₂_2, hs₂_3, hs₂_ob, hs₂_nv, hs₂_mc]
        · refine ⟨rfl, by wram_simp [hs₂_0], by wram_simp [hs₂_1], by wram_simp [hs₂_2],
            by wram_simp [hs₂_3], by wram_simp [hs₂_nv], by wram_simp [hs₂_mc], by wram_simp; rfl,
            by wram_simp [hs₂_ob], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          all_goals wram_simp
          all_goals
            dsimp only [wb, N, Mc, Instance.workBase, kOffAddr, kEdgeAddr, kRevOffAddr,
              kRevEdgeAddr, kCurAddr, kVisAddr, kOrdAddr, kStkAddr, kCompAddr]
          all_goals omega
        all_goals
          exact hfit_top.of_le (by
            dsimp only [wb, N, Mc, Instance.workBase, kTopAddr]
            omega)
      have hcm₃ : ClauseMemAt s₃.mem 3 G.φ :=
        hs₃_mem ▸ hs₂_mem ▸ hs₀_mem ▸ clauseMemAt_init G
      obtain ⟨s₄, hs₄_ex, hs₄_csr, _, hs₄_fr⟩ :=
        buildImplCSRCode_spec G hfit hcs_φ hcm₃ hs₃_0 hs₃_1 hs₃_3 hs₃_mc hs₃_Nv
          hs₃_off hs₃_edge hs₃_cur
      have hmc_adj : csrOffset G.adjFin N ≤ Mc := csrOffset_adjFin_le G
      have hs₄_dregs : DfsRegs (kOffAddr wb) (kEdgeAddr wb N) (kVisAddr wb N Mc)
          (kOrdAddr wb N Mc) (kStkAddr wb N Mc) s₄ := by
        constructor <;> wram_simp [hs₄_fr, hs₃_0, hs₃_1, hs₃_3, hs₃_off, hs₃_edge, hs₃_vis,
          hs₃_fin, hs₃_stk]
      obtain ⟨s₇, hs₇_ex, hs₇_comp, -, hs₇_fr⟩ :=
        sccIndexCode_spec hN_pos G.adjFin wb Mc hmc_adj hfit_top hs₄_dregs
          (by wram_simp [hs₄_fr, hs₃_Nv]) (by wram_simp [hs₄_fr, hs₃_cur])
          (by wram_simp [hs₄_fr, hs₃_roff]) (by wram_simp [hs₄_fr, hs₃_redge])
          (by wram_simp [hs₄_fr, hs₃_ord]) (by wram_simp [hs₄_fr, hs₃_comp]) hs₄_csr
      have hs₇_fr3 : ∀ r : Fin 28, r.val < 18 → r ≠ offB → r ≠ edgeB → r ≠ finB →
          s₇.regs r = s₃.regs r := fun r hr h1 h2 h3 =>
        (hs₇_fr r hr h1 h2 h3).trans (hs₄_fr r hr)
      set compIdx := indexComponents (sccs (implicationAdj G.φ) (literalList (List.finRange G.n)))
      have hs₇_comp' (u : Fin (2 * G.n)) :
          s₇.mem (kCompAddr wb N Mc + u.val) = compIdx ((litEquiv G.n).symm u) :=
        (hs₇_comp u).trans (by simpa using G.indexComponents_adjFin ((litEquiv G.n).symm u))
      let s₇' := (s₇.set compIdxReg 1).set iReg 0
      have hp_ext : ExecWithin (B := .standard) w (ram[ compIdxReg ← cOne; iReg ← cZero ])
          s₇ s₇' 2 := by
        wram_exec [hs₇_fr3, hs₃_1, hs₃_0]
      obtain ⟨s₈, hs₈_ex, hs₈_ob, hs₈_nv, hs₈_0, hs₈_1, hs₈_ok, hs₈_bits⟩ :=
        extractVarLoop_spec G hfit compIdx (List.finRange G.n) 0 true s₇' (by simp)
          (fun q _ => by simp) hs₇_comp' (fun _ hq _ => by omega)
          (by wram_simp [s₇', hs₇_fr3, hs₃_0]) (by wram_simp [s₇', hs₇_fr3, hs₃_1])
          (by wram_simp [s₇', hs₇_fr3, hs₃_2]) (by wram_simp [s₇', hs₇_fr3, hs₃_nv])
          (by wram_simp [s₇', hs₇_fr3, hs₃_ob]) (by wram_simp [s₇', hs₇_fr3, hs₃_comp]; rfl)
          (by wram_simp [s₇']) (by wram_simp [s₇']; rfl)
      rw [List.length_finRange] at hs₈_ex
      have hfin_ext : ∃ y, ExecWithin w
          (.branch (.eq compIdxReg cOne)
            (ram[ addr ← nv + cOne; *outBase ← addr; addr ← outBase + cOne; *addr ← cOne ])
            (ram[ *outBase ← cZero ]))
          s₈ y 5 ∧ y.regs outBase = G.outAddrBase ∧
          outputList y.mem G.outAddrBase = answerWords G := by
        cases hok_all : (List.finRange G.n).foldl
          (fun acc v => acc && decide (compIdx (v, true) ≠ compIdx (v, false))) true
        · have hans : answerWords G = [] := by
            dsimp only [answerWords, solveFin, solve, extractAssignment]
            rw [hchk, hok_all]
            rfl
          obtain ⟨hbr, hout⟩ := hwrite_nil s₈ hs₈_0 hs₈_1
            (hs₈_ok.trans (congrArg Bool.toNat hok_all)) hs₈_ob hans
          exact ⟨_, hbr.mono (by omega), hs₈_ob, hout⟩
        · have hs₈_ok1 : s₈.regs compIdxReg = 1 := by rw [hs₈_ok, hok_all]; rfl
          have hcond_ok : (Cond.eq compIdxReg cOne).Holds s₈ := by
            change s₈.regs compIdxReg = s₈.regs cOne; omega
          have hf_n1 : Fits w (G.n + 1) :=
            G.fits_of_le hfit (by unfold Instance.wordBound; omega)
          let y_sat := (((s₈.set addr (G.n + 1)).write G.outAddrBase (G.n + 1)).set
            addr (G.outAddrBase + 1)).write (G.outAddrBase + 1) 1
          have hpos_sat : ExecWithin (B := .standard) w
              (ram[ addr ← nv + cOne; *outBase ← addr; addr ← outBase + cOne; *addr ← cOne ])
              s₈ y_sat 4 := by
            wram_exec [hs₈_nv, hs₈_1, hs₈_ob, hf_n1, hf_ob1]
          have hdist_all : ∀ v : Fin G.n, compIdx (v, true) ≠ compIdx (v, false) := by
            have hall := hok_all
            rw [foldl_and_eq_and_all, Bool.true_and, List.all_eq_true] at hall
            exact fun v => of_decide_eq_true (hall v (List.mem_finRange v))
          refine ⟨y_sat, (hpos_sat.branch_pos hcond_ok).mono (by omega),
            by wram_simp [y_sat, hs₈_ob], ?_⟩
          rw [outputList_eq_iff]
          have hans : answerWords G =
              1 :: (List.finRange G.n).map
                (fun v => (decide (compIdx (v, false) < compIdx (v, true))).toNat) := by
            simp [answerWords, solveFin, solve, extractAssignment, encodeAssignment, compIdx, hchk,
              hdist_all]
          rw [hans]
          refine ⟨by wram_simp [y_sat]; simp, fun ⟨i, hi⟩ => ?_⟩
          rcases i with _ | q
          · wram_simp [Block.read, y_sat]; rfl
          · have hq : q < G.n := by simpa using hi
            rw [Block.read, show G.outAddrBase + 1 + (q + 1) = G.outAddrBase + 2 + q by omega]
            wram_simp [y_sat, hs₈_bits ⟨q, hq⟩ (hdist_all ⟨q, hq⟩)]
            simp
      obtain ⟨y, hy_br, hy_ob, hy_list⟩ := hfin_ext
      have hext_ex : ExecWithin w extractAssignmentCode s₇ y (16 * G.n + 9) :=
        (hp_ext.seq (hs₈_ex.seq hy_br)).mono (by omega)
      exact ⟨y, (hsetup.seq (hchk_ex.seq (((hs₃_ex.seq (hs₄_ex.seq (hs₇_ex.seq hext_ex))).branch_neg
        hncond_n0).branch_pos hcond_chk))).mono (by dsimp only [N, Mc] at *; omega), hy_ob,
        by rwa [hy_ob]⟩

/-- **Linear-time 2-SAT on the word RAM (`O(n + |φ|)`).** At every word width `w` with
`Fits w G.wordBound`, `program` halts within `512 * (G.n + G.φ.length + 1)` instructions and
outputs `answerWords G`: `[]` if `G.φ` is either not a 2-CNF or unsatisfiable, and
`1 :: [(σ 0).toNat, …, (σ (n - 1)).toNat]` for the canonical satisfying assignment `σ`
otherwise. -/
theorem program_spec (G : Instance) {w : ℕ} (hfit : Fits w G.wordBound) :
    ∃ steps ≤ 512 * (G.n + G.φ.length + 1),
      ExecutesList w program (State.init G.encode) (answerWords G) steps := by
  obtain ⟨y, ⟨steps, hsteps, hexec⟩, hyout, hylist⟩ := solver_spec G hfit
  have hlen := length_answerWords_le G
  have hfit_out : Fits w (y.regs outBase + (outputList y.mem (y.regs outBase)).length) := by
    rw [hylist, hyout]
    exact G.fits_of_le hfit
      (by simp only [Instance.outAddrBase, G.encode_length, Instance.wordBound]; omega)
  exact ⟨steps + 1, by omega, hylist ▸ hexec.executesList outBase hfit_out⟩

/-- Fixed-program `Program.ComputesListInTime` certificate for Word-RAM 2-SAT. -/
theorem computesListInTime_program :
    program.ComputesListInTime (fun _ G => G.encode)
      (fun G _ => 512 * (G.n + G.φ.length + 1))
      (fun G w => Fits w G.wordBound)
      answerWords := by
  intro G w hfit _
  exact (program_spec G hfit).imp fun _ ⟨hle, hex⟩ => ⟨hex, hle⟩

/-- `program` does not read the word width (`width%`). -/
theorem not_readsWidth_program : ¬ program.ReadsWidth := by
  apply Code.not_readsWidth_program
  simp [solver, Code.ReadsWidth, Op.ReadsWidth, Op.bin,
    not_readsWidth_headerSetupCode, not_readsWidth_checkClausesCode,
    not_readsWidth_setupWorkRegsCode, not_readsWidth_buildImplCSRCode,
    not_readsWidth_sccIndexCode, not_readsWidth_extractAssignmentCode]

/-- `program` is deterministic (`rand`-free). -/
theorem isRandFree_program : program.IsRandFree := by
  rw [program, Code.isRandFree_program]
  simp only [solver, Code.IsRandFree,
    isRandFree_headerSetupCode, isRandFree_checkClausesCode,
    isRandFree_setupWorkRegsCode, isRandFree_buildImplCSRCode,
    isRandFree_sccIndexCode, isRandFree_extractAssignmentCode, and_self]

end Cslib.Algorithms.WordRAM.TwoSAT
