/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.TwoSAT.EquivDFS
public import CslibFrontier.Algorithms.WordRAM.TwoSAT.Layout

/-!
# Implication-graph CSR edge backfill (`implFillBody`, `implFillLoop_spec`)

Internal Pass 2b loop populating the CSR edge array of `G.adjFin` in `O(|φ|)` steps.
-/

public section

namespace Cslib.Algorithms.WordRAM.TwoSAT

open Cslib.Logic.PL Cslib.WordRAM
open Cslib.Algorithms.Lean.TwoSAT
open Cslib.Algorithms.WordRAM.ClauseCode
open Reg Cslib.Algorithms.WordRAM.DFS Cslib.Algorithms.WordRAM.DFS.Reg

/-- Loop body backfilling implication-graph CSR arcs for one clause of width `1` or `2`. -/
def implFillBody : Code .standard 28 := ram[
  jReg ← *pReg;
  pReg ← pReg + cOne; oldFinReg ← *pReg;
  if jReg = cOne then [
    vReg ← oldFinReg ^^^ cOne; uReg ← oldFinReg;
    ⟪backfillStepCode⟫;
    pReg ← pReg + cOne ]
  else [
    pReg ← pReg + cOne; jReg ← *pReg;
    vReg ← oldFinReg ^^^ cOne; uReg ← jReg;
    ⟪backfillStepCode⟫;
    vReg ← jReg ^^^ cOne; uReg ← oldFinReg;
    ⟪backfillStepCode⟫;
    pReg ← pReg + cOne ];
  iReg ← iReg + cOne ]

theorem implFillLoop_spec (G : Instance) {w : ℕ} (hfit : Fits w G.wordBound) :
    ∀ (cs : CNF (Fin G.n)) (g : Literal (Fin G.n) → List (Literal (Fin G.n)))
      (idx p : ℕ) (x : Data 28),
      (∀ c ∈ cs, 1 ≤ c.length ∧ c.length ≤ 2) →
      G.φ = [] ∨ cs.foldl addClauseEdges g = implicationAdj G.φ →
      idx + cs.length = G.φ.length →
      p + (cs.flatMap (encodeClauseBy Fin.val)).length = G.encode.length + 1 →
      ClauseMemAt x.mem p cs →
      PartialCSRAt G.adjFin (mapAdj (litEquiv G.n) g)
        (kCurAddr G.workBase (2 * G.n) (2 * G.φ.length))
        (kEdgeAddr G.workBase (2 * G.n)) x.mem →
      x.regs cOne = 1 → x.regs mClauses = G.φ.length →
      x.regs curB = kCurAddr G.workBase (2 * G.n) (2 * G.φ.length) →
      x.regs edgeB = kEdgeAddr G.workBase (2 * G.n) →
      x.regs iReg = idx → x.regs pReg = p →
      ∃ y, ExecWithin w (.loop (.lt iReg mClauses) implFillBody) x y (28 * cs.length + 2) ∧
        PartialCSRAt G.adjFin (mapAdj (litEquiv G.n) (cs.foldl addClauseEdges g))
          (kCurAddr G.workBase (2 * G.n) (2 * G.φ.length))
          (kEdgeAddr G.workBase (2 * G.n)) y.mem ∧
        (∀ a, ¬ ((kCurAddr G.workBase (2 * G.n) (2 * G.φ.length) ≤ a ∧
              a < kCurAddr G.workBase (2 * G.n) (2 * G.φ.length) + 2 * G.n) ∨
            (kEdgeAddr G.workBase (2 * G.n) ≤ a ∧
              a < kEdgeAddr G.workBase (2 * G.n) + csrOffset G.adjFin (2 * G.n))) →
          y.mem a = x.mem a) ∧
        (∀ r : Fin 28, r.val < 18 → y.regs r = x.regs r)
  | [], g, idx, _, x, _, _, hidx, _, _, hpcsr, _, hm, _, _, hi, _ => by
    simp only [List.length_nil] at hidx
    have hend : ¬ (Cond.lt iReg mClauses).Holds x := by
      change ¬ x.regs iReg < x.regs mClauses
      omega
    refine ⟨x, ⟨2, by omega, Exec.loop_exit hend⟩,
      hpcsr, fun _ _ => rfl, fun _ _ => rfl⟩
  | c :: cs, g, idx, p, x, hcs, htarget, hidx, hp, hcm, hpcsr, hc1, hm, hcur, hedge, hi, hpR => by
    have hc := hcs c List.mem_cons_self
    have hrest : ∀ c' ∈ cs, 1 ≤ c'.length ∧ c'.length ≤ 2 :=
      fun c' hc' => hcs c' (List.mem_cons_of_mem c hc')
    set curBase := kCurAddr G.workBase (2 * G.n) (2 * G.φ.length)
    set edgeBase := kEdgeAddr G.workBase (2 * G.n)
    have hdisj : edgeBase + 2 * G.φ.length ≤ curBase := by
      simp only [edgeBase, curBase, kEdgeAddr, kCurAddr]; omega
    have hmc := csrOffset_adjFin_le G
    have hfit_bf : Fits w (curBase + 2 * G.n + 2 * G.φ.length + 1) :=
      G.fits_of_le hfit (by
        simp only [curBase, kCurAddr, Instance.workBase, Instance.outAddrBase,
          G.encode_length, Instance.wordBound]
        omega)
    obtain ⟨hlen_p, hlit_p, hcm_rest⟩ := clauseMemAt_cons hcm
    have hflat_cons : ((c :: cs).flatMap (encodeClauseBy Fin.val)).length =
        c.length + 1 + (cs.flatMap (encodeClauseBy Fin.val)).length := by
      simp [List.flatMap_cons, length_encodeClauseBy, Nat.add_assoc]
    have htarget' : cs.foldl addClauseEdges (addClauseEdges g c) = implicationAdj G.φ := by
      rcases htarget with hnil | hfold
      · simp [hnil] at hidx
      · simpa using hfold
    let FillStepPost (x₁ : Data 28) : Prop :=
      PartialCSRAt G.adjFin (mapAdj (litEquiv G.n) (addClauseEdges g c))
          curBase edgeBase x₁.mem ∧
        (∀ a, ¬ ((curBase ≤ a ∧ a < curBase + 2 * G.n) ∨
            (edgeBase ≤ a ∧ a < edgeBase + csrOffset G.adjFin (2 * G.n))) → x₁.mem a = x.mem a) ∧
        x₁.regs iReg = idx + 1 ∧ x₁.regs pReg = p + 1 + c.length ∧
        (∀ r : Fin 28, r.val < 18 → x₁.regs r = x.regs r)
    have hstep : ∃ x₁, ExecWithin w implFillBody x x₁ 26 ∧ FillStepPost x₁ := by
      rcases c with _ | ⟨a, _ | ⟨b, _ | ⟨d, rest⟩⟩⟩
      · simp at hc
      · have hmem_a : x.mem (p + 1) = litCodeBy Fin.val a := by simpa using hlit_p 0 (by simp)
        have hxor_a : litCodeBy Fin.val a ^^^ 1 = (litEquiv G.n a.negate).val :=
          litCodeBy_xor_one Fin.val a
        have hroom_a : (mapAdj (litEquiv G.n) g (litEquiv G.n a.negate)).length + 1 ≤
            (G.adjFin (litEquiv G.n a.negate)).length := by
          have hle := length_le_foldl_addClauseEdges cs (addClauseEdges g [a]) a.negate
          rw [htarget'] at hle
          simpa [Instance.adjFin, mapAdj, addClauseEdges] using hle
        have hf_p1 : Fits w (p + 1) :=
          G.fits_of_le hfit (by have := G.encode_length; unfold Instance.wordBound; omega)
        have hf_p2 : Fits w (p + 1 + 1) :=
          G.fits_of_le hfit (by have := G.encode_length; unfold Instance.wordBound; omega)
        have hf_na : Fits w (litCodeBy Fin.val a ^^^ 1) :=
          G.fits_of_le hfit (by
            rw [hxor_a]
            have := (litEquiv G.n a.negate).isLt
            unfold Instance.wordBound
            omega)
        have hf_i1 : Fits w (idx + 1) := G.fits_of_le hfit (by unfold Instance.wordBound; omega)
        let st_v := ((((x.set jReg 1).set pReg (p + 1)).set oldFinReg (litCodeBy Fin.val a)).set
          vReg (litCodeBy Fin.val a ^^^ 1)).set uReg (litCodeBy Fin.val a)
        obtain ⟨y₁, hy₁_ex, hy₁_p, hy₁_out, hy₁_fr⟩ :=
          backfillStepCode_spec G.adjFin (mapAdj (litEquiv G.n) g) curBase edgeBase
            (2 * G.φ.length) hdisj hmc hfit_bf (litEquiv G.n a.negate) (litEquiv G.n a) hroom_a
            (x := st_v) (by dsimp only [st_v]; wram_simp; exact hc1)
            (by dsimp only [st_v]; wram_simp; exact hcur)
            (by dsimp only [st_v]; wram_simp; exact hedge)
            (by dsimp only [st_v]; wram_simp; exact hxor_a)
            (by dsimp only [st_v, litEquiv]; wram_simp; rfl)
            (by dsimp only [st_v]; exact hpcsr)
        have hlen_1 : x.mem p = 1 := by simpa using hlen_p
        unfold implFillBody
        wram_exec [hc1, hpR, hi, hlen_1, hmem_a, hf_p1, hf_na]
        refine WP.of_execWithin hy₁_ex ?_
        have hy₁_1 : y₁.regs cOne = 1 :=
          (hy₁_fr cOne (by decide) (by decide)).trans (by dsimp only [st_v]; wram_simp; exact hc1)
        have hy₁_pr : y₁.regs pReg = p + 1 :=
          (hy₁_fr pReg (by decide) (by decide)).trans (by dsimp only [st_v]; wram_simp)
        have hy₁_i : y₁.regs iReg = idx :=
          (hy₁_fr iReg (by decide) (by decide)).trans (by dsimp only [st_v]; wram_simp; exact hi)
        wram_exec [hy₁_1, hy₁_pr, hy₁_i, hf_p2, hf_i1]
        dsimp only [FillStepPost]
        refine ⟨?_, fun addr_a ha => ?_, by wram_simp, by wram_simp; omega, fun r hr => ?_⟩
        · wram_simp
          rwa [mapAdj_addClauseEdges_one]
        · wram_simp
          exact hy₁_out addr_a ha
        · regs_lt
          rw [hy₁_fr r (by reg_ne) (by reg_ne)]
          dsimp only [st_v]; regs_lt
      · have hmem_a : x.mem (p + 1) = litCodeBy Fin.val a := by simpa using hlit_p 0 (by simp)
        have hmem_b : x.mem (p + 1 + 1) = litCodeBy Fin.val b := by
          simpa [Nat.add_assoc] using hlit_p 1 (by simp)
        have hlen_2 : x.mem p = 2 := by simpa using hlen_p
        have hxor_a : litCodeBy Fin.val a ^^^ 1 = (litEquiv G.n a.negate).val :=
          litCodeBy_xor_one Fin.val a
        have hxor_b : litCodeBy Fin.val b ^^^ 1 = (litEquiv G.n b.negate).val :=
          litCodeBy_xor_one Fin.val b
        let g₁ := Function.update g a.negate (b :: g a.negate)
        have hg₁_map : mapAdj (litEquiv G.n) g₁ =
            Function.update (mapAdj (litEquiv G.n) g) (litEquiv G.n a.negate)
              (litEquiv G.n b :: mapAdj (litEquiv G.n) g (litEquiv G.n a.negate)) :=
          (mapAdj_update_cons (litEquiv G.n) g a.negate b).symm
        have hroom_a : (mapAdj (litEquiv G.n) g (litEquiv G.n a.negate)).length + 1 ≤
            (G.adjFin (litEquiv G.n a.negate)).length := by
          have hle1 : (g₁ a.negate).length ≤ (addClauseEdges g [a, b] a.negate).length := by
            dsimp only [addClauseEdges, g₁]
            by_cases hab : a.negate = b.negate <;> simp [hab]
          have hle2 := length_le_foldl_addClauseEdges cs (addClauseEdges g [a, b]) a.negate
          rw [htarget'] at hle2
          have htot := hle1.trans hle2
          simpa [Instance.adjFin, mapAdj, g₁] using htot
        have hroom_b : (mapAdj (litEquiv G.n) g₁ (litEquiv G.n b.negate)).length + 1 ≤
            (G.adjFin (litEquiv G.n b.negate)).length := by
          have hle2 := length_le_foldl_addClauseEdges cs (addClauseEdges g [a, b]) b.negate
          rw [htarget'] at hle2
          simpa [Instance.adjFin, mapAdj, addClauseEdges, g₁] using hle2
        have hf_p1 : Fits w (p + 1) :=
          G.fits_of_le hfit (by have := G.encode_length; unfold Instance.wordBound; omega)
        have hf_p2 : Fits w (p + 1 + 1) :=
          G.fits_of_le hfit (by have := G.encode_length; unfold Instance.wordBound; omega)
        have hf_p3 : Fits w (p + 1 + 1 + 1) :=
          G.fits_of_le hfit (by have := G.encode_length; unfold Instance.wordBound; omega)
        have hf_na : Fits w (litCodeBy Fin.val a ^^^ 1) :=
          G.fits_of_le hfit (by
            rw [hxor_a]
            have := (litEquiv G.n a.negate).isLt
            unfold Instance.wordBound
            omega)
        have hf_nb : Fits w (litCodeBy Fin.val b ^^^ 1) :=
          G.fits_of_le hfit (by
            rw [hxor_b]
            have := (litEquiv G.n b.negate).isLt
            unfold Instance.wordBound
            omega)
        have hf_i1 : Fits w (idx + 1) := G.fits_of_le hfit (by unfold Instance.wordBound; omega)
        let st_v1 := ((((((x.set jReg 2).set pReg (p + 1)).set oldFinReg (litCodeBy Fin.val a)).set
          pReg (p + 1 + 1)).set jReg (litCodeBy Fin.val b)).set
          vReg (litCodeBy Fin.val a ^^^ 1)).set uReg (litCodeBy Fin.val b)
        obtain ⟨y₁, hy₁_ex, hy₁_p, hy₁_out, hy₁_fr⟩ :=
          backfillStepCode_spec G.adjFin (mapAdj (litEquiv G.n) g) curBase edgeBase
            (2 * G.φ.length) hdisj hmc hfit_bf (litEquiv G.n a.negate) (litEquiv G.n b) hroom_a
            (x := st_v1) (by dsimp only [st_v1]; wram_simp; exact hc1)
            (by dsimp only [st_v1]; wram_simp; exact hcur)
            (by dsimp only [st_v1]; wram_simp; exact hedge)
            (by dsimp only [st_v1]; wram_simp; exact hxor_a)
            (by dsimp only [st_v1, litEquiv]; wram_simp; rfl)
            (by dsimp only [st_v1]; exact hpcsr)
        have hy₁_p' : PartialCSRAt G.adjFin (mapAdj (litEquiv G.n) g₁) curBase edgeBase y₁.mem := by
          rwa [hg₁_map]
        have hy₁_1 : y₁.regs cOne = 1 :=
          (hy₁_fr cOne (by decide) (by decide)).trans (by dsimp only [st_v1]; wram_simp; exact hc1)
        have hy₁_cur : y₁.regs curB = curBase :=
          (hy₁_fr curB (by decide) (by decide)).trans (by dsimp only [st_v1]; wram_simp; exact hcur)
        have hy₁_edge : y₁.regs edgeB = edgeBase :=
          (hy₁_fr edgeB (by decide) (by decide)).trans
            (by dsimp only [st_v1]; wram_simp; exact hedge)
        have hy₁_a : y₁.regs oldFinReg = litCodeBy Fin.val a :=
          (hy₁_fr oldFinReg (by decide) (by decide)).trans (by dsimp only [st_v1]; wram_simp)
        have hy₁_b : y₁.regs jReg = litCodeBy Fin.val b :=
          (hy₁_fr jReg (by decide) (by decide)).trans (by dsimp only [st_v1]; wram_simp)
        let st_v2 := (y₁.set vReg (litCodeBy Fin.val b ^^^ 1)).set uReg (litCodeBy Fin.val a)
        obtain ⟨y₂, hy₂_ex, hy₂_p, hy₂_out, hy₂_fr⟩ :=
          backfillStepCode_spec G.adjFin (mapAdj (litEquiv G.n) g₁) curBase edgeBase
            (2 * G.φ.length) hdisj hmc hfit_bf (litEquiv G.n b.negate) (litEquiv G.n a) hroom_b
            (x := st_v2) (by dsimp only [st_v2]; wram_simp; exact hy₁_1)
            (by dsimp only [st_v2]; wram_simp; exact hy₁_cur)
            (by dsimp only [st_v2]; wram_simp; exact hy₁_edge)
            (by dsimp only [st_v2]; wram_simp; exact hxor_b)
            (by dsimp only [st_v2, litEquiv]; wram_simp; rfl)
            (by dsimp only [st_v2]; exact hy₁_p')
        unfold implFillBody
        wram_exec [hc1, hpR, hi, hlen_2, hmem_a, hmem_b, hf_p1, hf_p2, hf_na]
        refine WP.of_execWithin hy₁_ex ?_
        wram_exec [hy₁_1, hy₁_a, hy₁_b, hf_nb]
        refine WP.of_execWithin hy₂_ex ?_
        have hy₂_1 : y₂.regs cOne = 1 :=
          (hy₂_fr cOne (by decide) (by decide)).trans
            (by dsimp only [st_v2]; wram_simp; exact hy₁_1)
        have hy₂_pr : y₂.regs pReg = p + 1 + 1 :=
          (hy₂_fr pReg (by decide) (by decide)).trans
            ((hy₁_fr pReg (by decide) (by decide)).trans (by dsimp only [st_v1]; wram_simp))
        have hy₂_i : y₂.regs iReg = idx :=
          (hy₂_fr iReg (by decide) (by decide)).trans
            ((hy₁_fr iReg (by decide) (by decide)).trans
              (by dsimp only [st_v1]; wram_simp; exact hi))
        wram_exec [hy₂_1, hy₂_pr, hy₂_i, hf_p3, hf_i1]
        dsimp only [FillStepPost]
        refine ⟨?_, fun addr_a ha => ?_, by wram_simp, by wram_simp; omega, fun r hr => ?_⟩
        · wram_simp
          rwa [mapAdj_addClauseEdges_two, ← hg₁_map]
        · wram_simp
          exact (hy₂_out addr_a ha).trans (hy₁_out addr_a ha)
        · regs_lt
          rw [hy₂_fr r (by reg_ne) (by reg_ne)]
          dsimp only [st_v2]; regs_lt
          rw [hy₁_fr r (by reg_ne) (by reg_ne)]
          dsimp only [st_v1]; regs_lt
      · simp at hc
    obtain ⟨x₁, hx₁_ex, hx₁_p_csr, hx₁_out, hx₁_i, hx₁_p, hx₁_fr⟩ := hstep
    have hcm_x₁ : ClauseMemAt x₁.mem (p + 1 + c.length) cs := by
      intro k hk
      have hk_bound : p + 1 + c.length + k < G.workBase := by
        rw [hflat_cons] at hp
        simp only [Instance.workBase, Instance.outAddrBase]
        omega
      rw [hx₁_out _ (by simp only [curBase, edgeBase, kCurAddr, kEdgeAddr]; omega)]
      exact hcm_rest k hk
    have hlt : (Cond.lt iReg mClauses).Holds x := by
      change x.regs iReg < x.regs mClauses
      simp only [List.length_cons] at hidx
      omega
    obtain ⟨y, hy_ex, hy_p_csr, hy_out, hy_fr⟩ := implFillLoop_spec G hfit cs
      (addClauseEdges g c) (idx + 1) (p + 1 + c.length) x₁ hrest (.inr htarget')
      (by simp only [List.length_cons] at hidx; omega)
      (by rw [hflat_cons] at hp; omega) hcm_x₁ hx₁_p_csr
      ((hx₁_fr cOne (by decide)).trans hc1)
      ((hx₁_fr mClauses (by decide)).trans hm)
      ((hx₁_fr curB (by decide)).trans hcur)
      ((hx₁_fr edgeB (by decide)).trans hedge)
      hx₁_i hx₁_p
    obtain ⟨t₁, ht₁, he₁⟩ := hx₁_ex
    obtain ⟨t₂, ht₂, he₂⟩ := hy_ex
    refine ⟨y, ⟨t₁ + t₂ + 2, by simp only [List.length_cons]; omega,
        Exec.loop_iter hlt he₁ he₂⟩, hy_p_csr,
      fun a ha => (hy_out a ha).trans (hx₁_out a ha),
      fun r hr => (hy_fr r hr).trans (hx₁_fr r hr)⟩

theorem not_readsWidth_implFillBody : ¬ implFillBody.ReadsWidth := by
  simp [implFillBody, Code.ReadsWidth, Op.ReadsWidth, Op.bin, not_readsWidth_backfillStepCode]

theorem isRandFree_implFillBody : implFillBody.IsRandFree := by
  simp only [implFillBody, Code.IsRandFree, isRandFree_backfillStepCode, and_self]

end Cslib.Algorithms.WordRAM.TwoSAT
