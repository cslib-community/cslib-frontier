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
  refine ⟨hfit.of_le (by rw [G.encode_length]; unfold wordBound; omega), fun v hv => ?_⟩
  simp only [encode, List.mem_cons, List.mem_flatMap] at hv
  rcases hv with rfl | rfl | ⟨c, hc, hvc⟩
  · exact hfit.of_le (by unfold wordBound; omega)
  · exact hfit.of_le (by unfold wordBound; omega)
  · simp only [encodeClauseBy, List.mem_cons, List.mem_map] at hvc
    rcases hvc with rfl | ⟨ℓ, _, rfl⟩
    · have hle : c.length ≤ G.totalLits := List.le_sum_of_mem (List.mem_map_of_mem hc)
      exact hfit.of_le (by unfold wordBound; omega)
    · have hlt : litCodeBy Fin.val ℓ < 2 * G.n := by
        have := ℓ.1.isLt
        have := Bool.toNat_le ℓ.2
        unfold litCodeBy
        omega
      exact hfit.of_le (by unfold wordBound; omega)

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
    have hv : v.val < ((List.finRange G.n).map fun u => (σ u).toNat).length := by
      simp [v.isLt]
    rw [List.getD_eq_getElem _ 0 hv]
    simp only [List.getElem_map, List.getElem_finRange, Fin.cast_mk, Fin.eta]
    cases σ v <;> rfl

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
  rw [decodeAnswer_answerWords] at h
  exact solveFin_eq_some h

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
  have hf1 : Fits w 1 := G.fits_of_le hfit (by unfold Instance.wordBound; omega)
  have hf2 : Fits w 2 := G.fits_of_le hfit (by unfold Instance.wordBound; omega)
  have hf3 : Fits w 3 := G.fits_of_le hfit (by unfold Instance.wordBound; omega)
  have hf_ob : Fits w (G.encode.length + 1) :=
    G.fits_of_le hfit (by simp only [G.encode_length, Instance.wordBound]; omega)
  have hsetup0 : ∃ s₀, ExecWithin w headerSetupCode (Data.init G.encode) s₀ 8 ∧
      s₀.mem = (Data.init G.encode : Data 28).mem ∧
      s₀.regs cZero = 0 ∧ s₀.regs cOne = 1 ∧ s₀.regs cTwo = 2 ∧ s₀.regs cThree = 3 ∧
      s₀.regs outBase = G.outAddrBase ∧ s₀.regs nv = G.n ∧ s₀.regs mClauses = G.φ.length := by
    let Setup0Post (s₀ : Data 28) : Prop :=
      s₀.mem = (Data.init G.encode : Data 28).mem ∧
        s₀.regs cZero = 0 ∧ s₀.regs cOne = 1 ∧ s₀.regs cTwo = 2 ∧ s₀.regs cThree = 3 ∧
        s₀.regs outBase = G.outAddrBase ∧ s₀.regs nv = G.n ∧ s₀.regs mClauses = G.φ.length
    change ∃ s₀, ExecWithin w headerSetupCode (Data.init G.encode) s₀ 8 ∧ Setup0Post s₀
    unfold headerSetupCode
    wram_exec [Data.init_regs, hm0, hm1, hm2, hf1, hf2, hf3, hf_ob]
    dsimp only [Setup0Post]
    exact ⟨rfl, by wram_simp, by wram_simp, by wram_simp, by wram_simp,
      by wram_simp; rfl, by wram_simp, by wram_simp⟩
  obtain ⟨s₀, hsetup, hs₀_mem, hs₀_0, hs₀_1, hs₀_2, hs₀_3, hs₀_ob, hs₀_nv, hs₀_mc⟩ := hsetup0
  let s₁ := ((s₀.set compIdxReg 1).set pReg 3).set iReg 0
  have hchk_prep : ExecWithin (B := .standard) w
      (ram[ compIdxReg ← cOne; pReg ← cThree; iReg ← cZero ]) s₀ s₁ 3 := by
    wram_exec [hs₀_1, hs₀_3, hs₀_0]
  have hlen_enc : 3 + (G.φ.flatMap (encodeClauseBy Fin.val)).length = G.encode.length + 1 := by
    simp only [Instance.encode, List.length_cons]; omega
  obtain ⟨s₂, hs₂_ex, hs₂_mem, hs₂_ok, hs₂_fr⟩ :=
    checkClausesLoop_spec G hfit G.φ 0 3 true s₁ (by simp) hlen_enc
      (hs₀_mem ▸ clauseMemAt_init G)
      (by dsimp only [s₁]; wram_simp; exact hs₀_0)
      (by dsimp only [s₁]; wram_simp; exact hs₀_1)
      (by dsimp only [s₁]; wram_simp; exact hs₀_2)
      (by dsimp only [s₁]; wram_simp; exact hs₀_mc)
      (by dsimp only [s₁]; wram_simp)
      (by dsimp only [s₁]; wram_simp)
      (by dsimp only [s₁]; wram_simp; rfl)
  have hchk_ex : ExecWithin w checkClausesCode s₀ s₂ (12 * G.φ.length + 5) :=
    (hchk_prep.seq hs₂_ex).mono (by omega)
  have hs₂_fr0 : ∀ r : Fin 28, r.val < 18 → s₂.regs r = s₀.regs r := fun r hr => by
    rw [hs₂_fr r hr]
    dsimp only [s₁]
    have h1 : r ≠ iReg := by reg_ne
    have h2 : r ≠ pReg := by reg_ne
    have h3 : r ≠ compIdxReg := by reg_ne
    simp [Data.set_regs_of_ne h1, Data.set_regs_of_ne h2, Data.set_regs_of_ne h3]
  have hs₂_0 : s₂.regs cZero = 0 := (hs₂_fr0 cZero (by decide)).trans hs₀_0
  have hs₂_1 : s₂.regs cOne = 1 := (hs₂_fr0 cOne (by decide)).trans hs₀_1
  have hs₂_2 : s₂.regs cTwo = 2 := (hs₂_fr0 cTwo (by decide)).trans hs₀_2
  have hs₂_3 : s₂.regs cThree = 3 := (hs₂_fr0 cThree (by decide)).trans hs₀_3
  have hs₂_ob : s₂.regs outBase = G.outAddrBase := (hs₂_fr0 outBase (by decide)).trans hs₀_ob
  have hs₂_nv : s₂.regs nv = G.n := (hs₂_fr0 nv (by decide)).trans hs₀_nv
  have hs₂_mc : s₂.regs mClauses = G.φ.length := (hs₂_fr0 mClauses (by decide)).trans hs₀_mc
  cases hchk : checkClauses G.φ
  · -- Invalid clause width: return `[]`
    have hs₂_ok0 : s₂.regs compIdxReg = 0 := by
      rw [hs₂_ok, show G.φ.foldl (fun acc c => acc && isValidTwoClause c) true =
        checkClauses G.φ from rfl, hchk]
      rfl
    have hncond : ¬ (Cond.eq compIdxReg cOne).Holds s₂ := by
      change ¬ s₂.regs compIdxReg = s₂.regs cOne; omega
    have hneg : Exec (B := .standard) w (ram[ *outBase ← cZero ])
        s₂ (s₂.write G.outAddrBase 0) 1 := by
      have hst := Exec.store (B := .standard) (w := w) (x := s₂) (a := outBase) (s := cZero)
      rwa [hs₂_ob, hs₂_0] at hst
    have hbr : ExecWithin w
        (.branch (.eq compIdxReg cOne)
          (.branch (.eq nv cZero)
            (ram[ *outBase ← cOne; addr ← outBase + cOne; *addr ← cOne ])
            (setupWorkRegsCode.seq
              (buildImplCSRCode.seq
                (sccIndexCode.seq extractAssignmentCode))))
          (ram[ *outBase ← cZero ]))
        s₂ (s₂.write G.outAddrBase 0) 3 :=
      ⟨3, le_rfl, Exec.branch_neg hncond hneg⟩
    refine ⟨s₂.write G.outAddrBase 0,
      (hsetup.seq (hchk_ex.seq hbr)).mono (by omega),
      hs₂_ob, ?_⟩
    rw [Data.write_regs_apply, hs₂_ob, outputList_eq_iff]
    have hans : answerWords G = [] := by simp [answerWords, solveFin, solve, hchk]
    rw [hans]
    exact ⟨Data.write_mem_self _ _ _, Block.holdsList_nil _ _⟩
  · -- Valid 2-CNF: every clause has `1 ≤ length ≤ 2`
    have hs₂_ok1 : s₂.regs compIdxReg = 1 := by
      rw [hs₂_ok, show G.φ.foldl (fun acc c => acc && isValidTwoClause c) true =
        checkClauses G.φ from rfl, hchk]
      rfl
    have hcond_chk : (Cond.eq compIdxReg cOne).Holds s₂ := by
      change s₂.regs compIdxReg = s₂.regs cOne; omega
    obtain ⟨hw_φ, hnil_φ⟩ := (checkClauses_eq_true_iff G.φ).1 hchk
    have hcs_φ : ∀ c ∈ G.φ, 1 ≤ c.length ∧ c.length ≤ 2 := fun c hc => by
      refine ⟨?_, hw_φ c hc⟩
      cases c with
      | nil => exact absurd hc hnil_φ
      | cons _ _ => simp
    by_cases hn0 : G.n = 0
    · -- `G.n = 0`: `G.φ = []`, `answerWords G = [1]`
      have hφ_nil : G.φ = [] := by
        cases hφ : G.φ with
        | nil => rfl
        | cons c cs =>
          have hc1 := (hcs_φ c (by simp [hφ])).1
          cases c with
          | nil => simp at hc1
          | cons ℓ _ =>
            have := ℓ.1.isLt
            omega
      have hcond_n0 : (Cond.eq nv cZero).Holds s₂ := by
        change s₂.regs nv = s₂.regs cZero; omega
      have hf_ob1 : Fits w (G.outAddrBase + 1) :=
        G.fits_of_le hfit (by
          simp only [Instance.outAddrBase, G.encode_length, Instance.wordBound]; omega)
      let y_n0 := ((s₂.write G.outAddrBase 1).set addr (G.outAddrBase + 1)).write
        (G.outAddrBase + 1) 1
      have hpos_n0 : ExecWithin w
          (ram[ *outBase ← cOne; addr ← outBase + cOne; *addr ← cOne ]) s₂ y_n0 3 := by
        have htriv : y_n0 = ((s₂.write G.outAddrBase 1).set addr (G.outAddrBase + 1)).write
          (G.outAddrBase + 1) 1 := rfl
        wram_exec [hs₂_ob, hs₂_1, hf_ob1]
      obtain ⟨tn0, htn0, hen0⟩ := hpos_n0
      have hbr_inner : Exec w
          (.branch (.eq nv cZero)
            (ram[ *outBase ← cOne; addr ← outBase + cOne; *addr ← cOne ])
            (setupWorkRegsCode.seq
              (buildImplCSRCode.seq
                (sccIndexCode.seq extractAssignmentCode))))
          s₂ y_n0 (tn0 + 1) :=
        Exec.branch_pos hcond_n0 hen0
      have hbr_outer : ExecWithin w
          (.branch (.eq compIdxReg cOne)
            (.branch (.eq nv cZero)
              (ram[ *outBase ← cOne; addr ← outBase + cOne; *addr ← cOne ])
              (setupWorkRegsCode.seq
                (buildImplCSRCode.seq
                  (sccIndexCode.seq extractAssignmentCode))))
            (ram[ *outBase ← cZero ]))
          s₂ y_n0 5 :=
        ⟨tn0 + 2, by omega, Exec.branch_pos hcond_chk hbr_inner⟩
      refine ⟨y_n0, (hsetup.seq (hchk_ex.seq hbr_outer)).mono (by omega),
        by dsimp only [y_n0]; wram_simp; exact hs₂_ob, ?_⟩
      have hob_y : y_n0.regs outBase = G.outAddrBase := by
        dsimp only [y_n0]; wram_simp; exact hs₂_ob
      rw [hob_y, outputList_eq_iff]
      have hans : answerWords G = [1] := by
        cases G with
        | mk n φ =>
          dsimp only at hn0 hφ_nil
          subst hn0 hφ_nil
          rfl
      rw [hans]
      refine ⟨?_, fun i => ?_⟩
      · dsimp only [y_n0]
        rw [Data.write_mem_of_ne (by omega), Data.set_mem, Data.write_mem_self]
        rfl
      · rcases i with ⟨_ | k, hlt⟩
        · dsimp only [Block.read, y_n0]
          rw [Nat.add_zero, Data.write_mem_self]
          rfl
        · change k + 1 < 1 at hlt
          omega
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
      have hsetup_regs : ∃ s₃, ExecWithin w setupWorkRegsCode s₂ s₃ 19 ∧
          s₃.mem = s₂.mem ∧
          s₃.regs cZero = 0 ∧ s₃.regs cOne = 1 ∧ s₃.regs cTwo = 2 ∧ s₃.regs cThree = 3 ∧
          s₃.regs nv = G.n ∧ s₃.regs mClauses = G.φ.length ∧ s₃.regs nVerts = N ∧
          s₃.regs outBase = G.outAddrBase ∧
          s₃.regs offB = kOffAddr wb ∧ s₃.regs edgeB = kEdgeAddr wb N ∧
          s₃.regs revOffB = kRevOffAddr wb N Mc ∧ s₃.regs revEdgeB = kRevEdgeAddr wb N Mc ∧
          s₃.regs curB = kCurAddr wb N Mc ∧ s₃.regs visB = kVisAddr wb N Mc ∧
          s₃.regs ordB = kOrdAddr wb N Mc ∧ s₃.regs finB = kOrdAddr wb N Mc ∧
          s₃.regs stkB = kStkAddr wb N Mc ∧ s₃.regs compB = kCompAddr wb N Mc := by
        let SetupPost (s₃ : Data 28) : Prop :=
          s₃.mem = s₂.mem ∧
            s₃.regs cZero = 0 ∧ s₃.regs cOne = 1 ∧ s₃.regs cTwo = 2 ∧ s₃.regs cThree = 3 ∧
            s₃.regs nv = G.n ∧ s₃.regs mClauses = G.φ.length ∧ s₃.regs nVerts = N ∧
            s₃.regs outBase = G.outAddrBase ∧
            s₃.regs offB = kOffAddr wb ∧ s₃.regs edgeB = kEdgeAddr wb N ∧
            s₃.regs revOffB = kRevOffAddr wb N Mc ∧ s₃.regs revEdgeB = kRevEdgeAddr wb N Mc ∧
            s₃.regs curB = kCurAddr wb N Mc ∧ s₃.regs visB = kVisAddr wb N Mc ∧
            s₃.regs ordB = kOrdAddr wb N Mc ∧ s₃.regs finB = kOrdAddr wb N Mc ∧
            s₃.regs stkB = kStkAddr wb N Mc ∧ s₃.regs compB = kCompAddr wb N Mc
        change ∃ s₃, ExecWithin w setupWorkRegsCode s₂ s₃ 19 ∧ SetupPost s₃
        unfold setupWorkRegsCode
        wram_exec [hs₂_0, hs₂_1, hs₂_2, hs₂_3, hs₂_ob, hs₂_nv, hs₂_mc]
        · dsimp only [SetupPost]
          refine ⟨rfl, by wram_simp; exact hs₂_0, by wram_simp; exact hs₂_1,
            by wram_simp; exact hs₂_2, by wram_simp; exact hs₂_3,
            by wram_simp; exact hs₂_nv, by wram_simp; exact hs₂_mc, by wram_simp; rfl,
            by wram_simp; exact hs₂_ob, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          all_goals wram_simp
          all_goals
            dsimp only [wb, N, Mc, Instance.workBase, kOffAddr, kEdgeAddr, kRevOffAddr,
              kRevEdgeAddr, kCurAddr, kVisAddr, kOrdAddr, kStkAddr, kCompAddr]
          all_goals omega
        all_goals
          exact hfit_top.of_le (by
            dsimp only [wb, N, Mc, Instance.workBase, kTopAddr]
            omega)
      obtain ⟨s₃, hs₃_ex, hs₃_mem, hs₃_0, hs₃_1, hs₃_2, hs₃_3, hs₃_nv, hs₃_mc, hs₃_Nv, hs₃_ob,
        hs₃_off, hs₃_edge, hs₃_roff, hs₃_redge, hs₃_cur, hs₃_vis, hs₃_ord, hs₃_fin,
        hs₃_stk, hs₃_comp⟩ := hsetup_regs
      have hcm₃ : ClauseMemAt s₃.mem 3 G.φ :=
        hs₃_mem ▸ hs₂_mem ▸ hs₀_mem ▸ clauseMemAt_init G
      obtain ⟨s₄, hs₄_ex, hs₄_csr, _, hs₄_fr⟩ :=
        buildImplCSRCode_spec G hfit hcs_φ hcm₃ hs₃_0 hs₃_1 hs₃_3 hs₃_mc hs₃_Nv
          hs₃_off hs₃_edge hs₃_cur
      have hmc_adj : csrOffset G.adjFin N ≤ Mc := csrOffset_adjFin_le G
      have hs₄_dregs : DfsRegs (kOffAddr wb) (kEdgeAddr wb N) (kVisAddr wb N Mc)
          (kOrdAddr wb N Mc) (kStkAddr wb N Mc) s₄ :=
        { czero := (hs₄_fr cZero (by decide)).trans hs₃_0
          cone := (hs₄_fr cOne (by decide)).trans hs₃_1
          cthree := (hs₄_fr cThree (by decide)).trans hs₃_3
          hoff := (hs₄_fr offB (by decide)).trans hs₃_off
          hedge := (hs₄_fr edgeB (by decide)).trans hs₃_edge
          hvis := (hs₄_fr visB (by decide)).trans hs₃_vis
          hfin := (hs₄_fr finB (by decide)).trans hs₃_fin
          hstk := (hs₄_fr stkB (by decide)).trans hs₃_stk }
      obtain ⟨s₇, hs₇_ex, hs₇_comp, -, hs₇_fr⟩ :=
        sccIndexCode_spec hN_pos G.adjFin wb Mc hmc_adj hfit_top hs₄_dregs
          ((hs₄_fr nVerts (by decide)).trans hs₃_Nv)
          ((hs₄_fr curB (by decide)).trans hs₃_cur)
          ((hs₄_fr revOffB (by decide)).trans hs₃_roff)
          ((hs₄_fr revEdgeB (by decide)).trans hs₃_redge)
          ((hs₄_fr ordB (by decide)).trans hs₃_ord)
          ((hs₄_fr compB (by decide)).trans hs₃_comp)
          hs₄_csr
      have hs₇_fr3 : ∀ r : Fin 28, r.val < 18 → r ≠ offB → r ≠ edgeB → r ≠ finB →
          s₇.regs r = s₃.regs r := fun r hr h1 h2 h3 =>
        (hs₇_fr r hr h1 h2 h3).trans (hs₄_fr r hr)
      set compIdx := indexComponents (sccs (implicationAdj G.φ) (literalList (List.finRange G.n)))
      have hs₇_comp' : ∀ u : Fin (2 * G.n),
          s₇.mem (kCompAddr wb N Mc + u.val) = compIdx ((litEquiv G.n).symm u) := fun u => by
        rw [hs₇_comp u]
        have htr := G.indexComponents_adjFin ((litEquiv G.n).symm u)
        rwa [Equiv.apply_symm_apply] at htr
      let s₇' := (s₇.set compIdxReg 1).set iReg 0
      have hp_ext : ExecWithin (B := .standard) w (ram[ compIdxReg ← cOne; iReg ← cZero ])
          s₇ s₇' 2 := by
        have h1' : s₇.regs cOne = 1 :=
          (hs₇_fr3 cOne (by decide) (by decide) (by decide) (by decide)).trans hs₃_1
        have h0' : s₇.regs cZero = 0 :=
          (hs₇_fr3 cZero (by decide) (by decide) (by decide) (by decide)).trans hs₃_0
        wram_exec [h1', h0']
      obtain ⟨s₈, hs₈_ex, hs₈_ob, hs₈_nv, hs₈_0, hs₈_1, hs₈_ok, hs₈_bits⟩ :=
        extractVarLoop_spec G hfit compIdx (List.finRange G.n) 0 true s₇' (by simp)
          (fun q _ => by simp) hs₇_comp' (fun _ hq _ => by omega)
          (by
            dsimp only [s₇']; wram_simp
            exact (hs₇_fr3 cZero (by decide) (by decide) (by decide) (by decide)).trans hs₃_0)
          (by
            dsimp only [s₇']; wram_simp
            exact (hs₇_fr3 cOne (by decide) (by decide) (by decide) (by decide)).trans hs₃_1)
          (by
            dsimp only [s₇']; wram_simp
            exact (hs₇_fr3 cTwo (by decide) (by decide) (by decide) (by decide)).trans hs₃_2)
          (by
            dsimp only [s₇']; wram_simp
            exact (hs₇_fr3 nv (by decide) (by decide) (by decide) (by decide)).trans hs₃_nv)
          (by
            dsimp only [s₇']; wram_simp
            exact (hs₇_fr3 outBase (by decide) (by decide) (by decide) (by decide)).trans hs₃_ob)
          (by
            dsimp only [s₇']; wram_simp
            exact (hs₇_fr3 compB (by decide) (by decide) (by decide) (by decide)).trans hs₃_comp)
          (by dsimp only [s₇']; wram_simp)
          (by dsimp only [s₇']; wram_simp; rfl)
      rw [List.length_finRange] at hs₈_ex
      have hfin_ext : ∃ y, ExecWithin w
          (.branch (.eq compIdxReg cOne)
            (ram[ addr ← nv + cOne; *outBase ← addr; addr ← outBase + cOne; *addr ← cOne ])
            (ram[ *outBase ← cZero ]))
          s₈ y 5 ∧ y.regs outBase = G.outAddrBase ∧
          outputList y.mem G.outAddrBase = answerWords G := by
        set ok_all := (List.finRange G.n).foldl
          (fun acc v => acc && decide (compIdx (v, true) ≠ compIdx (v, false))) true
        cases hok_all : ok_all
        · have hs₈_ok0 : s₈.regs compIdxReg = 0 := by rw [hs₈_ok, hok_all]; rfl
          have hncond_ok : ¬ (Cond.eq compIdxReg cOne).Holds s₈ := by
            change ¬ s₈.regs compIdxReg = s₈.regs cOne; omega
          have hneg : Exec (B := .standard) w (ram[ *outBase ← cZero ])
              s₈ (s₈.write G.outAddrBase 0) 1 := by
            have hst := Exec.store (B := .standard) (w := w) (x := s₈) (a := outBase) (s := cZero)
            rwa [hs₈_ob, hs₈_0] at hst
          refine ⟨s₈.write G.outAddrBase 0, ⟨3, by omega, Exec.branch_neg hncond_ok hneg⟩,
            hs₈_ob, ?_⟩
          rw [outputList_eq_iff]
          have hans : answerWords G = [] := by
            dsimp only [answerWords, solveFin, solve, extractAssignment]
            have hfold_eq :
                (List.finRange G.n).foldl
                  (fun ok v => ok && decide (compIdx (v, true) ≠ compIdx (v, false))) true =
                ok_all := rfl
            rw [hchk, hfold_eq, hok_all]
            rfl
          rw [hans]
          exact ⟨Data.write_mem_self _ _ _, Block.holdsList_nil _ _⟩
        · have hs₈_ok1 : s₈.regs compIdxReg = 1 := by rw [hs₈_ok, hok_all]; rfl
          have hcond_ok : (Cond.eq compIdxReg cOne).Holds s₈ := by
            change s₈.regs compIdxReg = s₈.regs cOne; omega
          have hf_n1 : Fits w (G.n + 1) :=
            G.fits_of_le hfit (by unfold Instance.wordBound; omega)
          have hf_ob1 : Fits w (G.outAddrBase + 1) :=
            G.fits_of_le hfit (by
              simp only [Instance.outAddrBase, G.encode_length, Instance.wordBound]; omega)
          let y_sat := (((s₈.set addr (G.n + 1)).write G.outAddrBase (G.n + 1)).set
            addr (G.outAddrBase + 1)).write (G.outAddrBase + 1) 1
          have hpos_sat : ExecWithin w
              (ram[ addr ← nv + cOne; *outBase ← addr; addr ← outBase + cOne; *addr ← cOne ])
              s₈ y_sat 4 := by
            have htriv : y_sat = (((s₈.set addr (G.n + 1)).write G.outAddrBase (G.n + 1)).set
              addr (G.outAddrBase + 1)).write (G.outAddrBase + 1) 1 := rfl
            wram_exec [hs₈_nv, hs₈_1, hs₈_ob, hf_n1, hf_ob1]
          obtain ⟨ts, hts, hes⟩ := hpos_sat
          have hdist_all : ∀ v : Fin G.n, compIdx (v, true) ≠ compIdx (v, false) := by
            have hall : (List.finRange G.n).foldl
                (fun acc v => acc && decide (compIdx (v, true) ≠ compIdx (v, false))) true =
                  true := hok_all
            rw [foldl_and_eq_and_all, Bool.true_and, List.all_eq_true] at hall
            exact fun v => of_decide_eq_true (hall v (List.mem_finRange v))
          refine ⟨y_sat, ⟨ts + 1, by omega, Exec.branch_pos hcond_ok hes⟩,
            by dsimp only [y_sat]; wram_simp; exact hs₈_ob, ?_⟩
          rw [outputList_eq_iff]
          have hans : answerWords G =
              1 :: (List.finRange G.n).map
                (fun v => (decide (compIdx (v, false) < compIdx (v, true))).toNat) := by
            dsimp only [answerWords, solveFin, solve, extractAssignment, encodeAssignment]
            have hfold_eq :
                (List.finRange G.n).foldl
                  (fun ok v => ok && decide (compIdx (v, true) ≠ compIdx (v, false))) true =
                ok_all := rfl
            rw [hchk, hfold_eq, hok_all]
            rfl
          rw [hans]
          refine ⟨?_, fun i => ?_⟩
          · dsimp only [y_sat]
            rw [Data.write_mem_of_ne (by omega), Data.set_mem, Data.write_mem_self]
            simp
          · dsimp only [Block.read, y_sat]
            cases hi_eq : i.val with
            | zero =>
              rw [Nat.add_zero, Data.write_mem_self]
              simp [hi_eq]
            | succ q =>
              have hq_lt : q < G.n := by have := i.isLt; simp at this; omega
              rw [show G.outAddrBase + 1 + (q + 1) = G.outAddrBase + 2 + q by omega,
                Data.write_mem_of_ne (by omega), Data.set_mem,
                Data.write_mem_of_ne (by omega), Data.set_mem,
                hs₈_bits ⟨q, hq_lt⟩ (hdist_all ⟨q, hq_lt⟩)]
              simp [hi_eq]
      obtain ⟨y, hy_br, hy_ob, hy_list⟩ := hfin_ext
      have hext_ex : ExecWithin w extractAssignmentCode s₇ y (16 * G.n + 9) :=
        (hp_ext.seq (hs₈_ex.seq hy_br)).mono (by omega)
      have hfull_pos : ExecWithin w
          (setupWorkRegsCode.seq
            (buildImplCSRCode.seq
              (sccIndexCode.seq extractAssignmentCode)))
          s₂ y (498 * G.n + 245 * G.φ.length + 88) :=
        (hs₃_ex.seq (hs₄_ex.seq (hs₇_ex.seq hext_ex))).mono
          (by dsimp only [N, Mc] at *; omega)
      obtain ⟨tf, htf, hef⟩ := hfull_pos
      have hbr_inner : Exec w
          (.branch (.eq nv cZero)
            (ram[ *outBase ← cOne; addr ← outBase + cOne; *addr ← cOne ])
            (setupWorkRegsCode.seq
              (buildImplCSRCode.seq
                (sccIndexCode.seq extractAssignmentCode))))
          s₂ y (tf + 2) :=
        Exec.branch_neg hncond_n0 hef
      have hbr_outer : ExecWithin w
          (.branch (.eq compIdxReg cOne)
            (.branch (.eq nv cZero)
              (ram[ *outBase ← cOne; addr ← outBase + cOne; *addr ← cOne ])
              (setupWorkRegsCode.seq
                (buildImplCSRCode.seq
                  (sccIndexCode.seq extractAssignmentCode))))
            (ram[ *outBase ← cZero ]))
          s₂ y (498 * G.n + 245 * G.φ.length + 91) :=
        ⟨tf + 3, by omega, Exec.branch_pos hcond_chk hbr_inner⟩
      exact ⟨y, (hsetup.seq (hchk_ex.seq hbr_outer)).mono (by omega), hy_ob,
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
  refine ⟨steps + 1, by omega, ?_⟩
  have hex := hexec.executesList outBase hfit_out
  rwa [hylist] at hex

/-- Fixed-program `Program.ComputesListInTime` certificate for Word-RAM 2-SAT. -/
theorem computesListInTime_program :
    program.ComputesListInTime (fun _ G => G.encode)
      (fun G _ => 512 * (G.n + G.φ.length + 1))
      (fun G w => Fits w G.wordBound)
      answerWords := by
  intro G w hfit _
  obtain ⟨steps, hle, hex⟩ := program_spec G hfit
  exact ⟨steps, hex, hle⟩


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
