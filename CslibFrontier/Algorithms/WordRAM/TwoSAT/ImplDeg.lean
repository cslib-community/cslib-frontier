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
# Implication-graph CSR out-degree counting (`implDegBody`, `implDegLoop_spec`)

Internal Pass 2a loop counting out-degrees of the implication graph `G.adjFin` in `O(|φ|)` steps.
-/

public section

namespace Cslib.Algorithms.WordRAM.TwoSAT

open Cslib.Logic.PL Cslib.WordRAM
open Cslib.Algorithms.Lean.TwoSAT
open Cslib.Algorithms.WordRAM.ClauseCode
open Reg Cslib.Algorithms.WordRAM.DFS Cslib.Algorithms.WordRAM.DFS.Reg

/-- Loop body incrementing CSR out-degrees in `curB` for one clause of width `1` or `2`. -/
def implDegBody : Code .standard 28 := ram[
  jReg ← *pReg;
  pReg ← pReg + cOne; uReg ← *pReg;
  if jReg = cOne then [
    vReg ← uReg ^^^ cOne;
    ⟪incCurCode⟫;
    pReg ← pReg + cOne ]
  else [
    pReg ← pReg + cOne; oldFinReg ← *pReg;
    vReg ← uReg ^^^ cOne;
    ⟪incCurCode⟫;
    vReg ← oldFinReg ^^^ cOne;
    ⟪incCurCode⟫;
    pReg ← pReg + cOne ];
  iReg ← iReg + cOne ]

/-- The negated literal code `litCodeBy Fin.val a ^^^ 1` fits the word width. -/
private theorem fits_litCode_xor_one (G : Instance) {w : ℕ} (hfit : Fits w G.wordBound)
    (a : Literal (Fin G.n)) : Fits w (litCodeBy Fin.val a ^^^ 1) :=
  G.fits_of_le hfit (by
    rw [show litCodeBy Fin.val a ^^^ 1 = (litEquiv G.n a.negate).val from
      litCodeBy_xor_one Fin.val a]
    have := (litEquiv G.n a.negate).isLt
    unfold Instance.wordBound
    omega)

theorem implDegLoop_spec (G : Instance) {w : ℕ} (hfit : Fits w G.wordBound) :
    ∀ (cs : CNF (Fin G.n)) (g : Literal (Fin G.n) → List (Literal (Fin G.n)))
      (idx p : ℕ) (x : Data 28),
      (∀ c ∈ cs, 1 ≤ c.length ∧ c.length ≤ 2) →
      G.φ = [] ∨ cs.foldl addClauseEdges g = implicationAdj G.φ →
      idx + cs.length = G.φ.length →
      p + (cs.flatMap (encodeClauseBy Fin.val)).length = G.encode.length + 1 →
      ClauseMemAt x.mem p cs →
      (∀ u : Fin (2 * G.n), x.mem (kCurAddr G.workBase (2 * G.n) (2 * G.φ.length) + u.val) =
        (mapAdj (litEquiv G.n) g u).length) →
      x.regs cOne = 1 → x.regs mClauses = G.φ.length →
      x.regs curB = kCurAddr G.workBase (2 * G.n) (2 * G.φ.length) →
      x.regs iReg = idx → x.regs pReg = p →
      ∃ y, ExecWithin w (.loop (.lt iReg mClauses) implDegBody) x y (21 * cs.length + 2) ∧
        (∀ u : Fin (2 * G.n), y.mem (kCurAddr G.workBase (2 * G.n) (2 * G.φ.length) + u.val) =
          (mapAdj (litEquiv G.n) (cs.foldl addClauseEdges g) u).length) ∧
        (∀ a, ¬ (kCurAddr G.workBase (2 * G.n) (2 * G.φ.length) ≤ a ∧
            a < kCurAddr G.workBase (2 * G.n) (2 * G.φ.length) + 2 * G.n) → y.mem a = x.mem a) ∧
        (∀ r : Fin 28, r.val < 18 → y.regs r = x.regs r)
  | [], g, idx, _, x, _, _, hidx, _, _, hdeg, _, hm, _, hi, _ => by
    simp only [List.length_nil] at hidx
    have hend : ¬ (Cond.lt iReg mClauses).Holds x := by
      change ¬ x.regs iReg < x.regs mClauses
      omega
    exact ⟨x, ExecWithin.loop_exit hend, hdeg, fun _ _ => rfl, fun _ _ => rfl⟩
  | c :: cs, g, idx, p, x, hcs, htarget, hidx, hp, hcm, hdeg, hc1, hm, hcur, hi, hpR => by
    have hc := hcs c List.mem_cons_self
    have hrest : ∀ c' ∈ cs, 1 ≤ c'.length ∧ c'.length ≤ 2 :=
      fun c' hc' => hcs c' (List.mem_cons_of_mem c hc')
    set curBase := kCurAddr G.workBase (2 * G.n) (2 * G.φ.length)
    have hfit_cur : Fits w (curBase + 2 * G.n + 2 * G.φ.length + 1) :=
      G.fits_of_le hfit (by
        simp only [curBase, kCurAddr, Instance.workBase, Instance.outAddrBase,
          G.encode_length, Instance.wordBound]
        omega)
    have hp_lt_cur : p + c.length + 1 ≤ curBase := by
      simp only [curBase, kCurAddr, Instance.workBase, Instance.outAddrBase]
      omega
    obtain ⟨hlen_p, hlit_p, hcm_rest⟩ := clauseMemAt_cons hcm
    have hflat_cons : ((c :: cs).flatMap (encodeClauseBy Fin.val)).length =
        c.length + 1 + (cs.flatMap (encodeClauseBy Fin.val)).length := by
      simp [List.flatMap_cons, length_encodeClauseBy, Nat.add_assoc]
    have hbound_imp : ∀ w_u : Fin (2 * G.n), (G.adjFin w_u).length ≤ 2 * G.φ.length := by
      intro w_u
      have h1 := csrOffset_succ G.adjFin w_u.isLt
      have h2 := csrOffset_mono G.adjFin (by omega : w_u.val + 1 ≤ 2 * G.n)
      have h3 := csrOffset_adjFin_le G
      simp only [Fin.eta] at h1
      omega
    have htarget' : cs.foldl addClauseEdges (addClauseEdges g c) = implicationAdj G.φ := by
      rcases htarget with hnil | hfold
      · simp [hnil] at hidx
      · simpa using hfold
    obtain ⟨x₁, hx₁_ex, hx₁_deg, hx₁_out, hx₁_i, hx₁_p, hx₁_fr⟩ :
        ∃ x₁, ExecWithin w implDegBody x x₁ 19 ∧
          (∀ u : Fin (2 * G.n), x₁.mem (curBase + u.val) =
            (mapAdj (litEquiv G.n) (addClauseEdges g c) u).length) ∧
          (∀ a, ¬ (curBase ≤ a ∧ a < curBase + 2 * G.n) → x₁.mem a = x.mem a) ∧
          x₁.regs iReg = idx + 1 ∧ x₁.regs pReg = p + 1 + c.length ∧
          (∀ r : Fin 28, r.val < 18 → x₁.regs r = x.regs r) := by
      rcases c with _ | ⟨a, _ | ⟨b, _ | ⟨d, rest⟩⟩⟩
      · simp at hc
      · have hmem_a : x.mem (p + 1) = litCodeBy Fin.val a := by simpa using hlit_p 0 (by simp)
        have hxor_a : litCodeBy Fin.val a ^^^ 1 = (litEquiv G.n a.negate).val :=
          litCodeBy_xor_one Fin.val a
        have hroom_a : (mapAdj (litEquiv G.n) g (litEquiv G.n a.negate)).length + 1 ≤
            2 * G.φ.length := by
          have hle := length_le_foldl_addClauseEdges cs (addClauseEdges g [a]) a.negate
          rw [htarget'] at hle
          have hfin := hbound_imp (litEquiv G.n a.negate)
          simp only [Instance.adjFin, mapAdj, Equiv.symm_apply_apply, List.length_map,
            addClauseEdges, Function.update_self, List.length_cons] at hle hfin ⊢
          omega
        have hf_p2 : Fits w (p + 1 + 1) :=
          G.fits_of_le hfit (by have := G.encode_length; unfold Instance.wordBound; omega)
        have hf_na := fits_litCode_xor_one G hfit a
        have hf_i1 : Fits w (idx + 1) := G.fits_of_le hfit (by unfold Instance.wordBound; omega)
        let st_pre := ((x.set jReg 1).set pReg (p + 1)).set uReg (litCodeBy Fin.val a)
        let st_v := st_pre.set vReg (litCodeBy Fin.val a ^^^ 1)
        obtain ⟨y₁, hy₁_ex, hy₁_deg, hy₁_out, hy₁_fr⟩ :=
          incCurCode_spec (N := 2 * G.n) curBase (2 * G.φ.length) hfit_cur
            (fun u => (mapAdj (litEquiv G.n) g u).length) (litEquiv G.n a.negate) hroom_a
            (x := st_v) (by wram_simp [st_v, st_pre, hc1]) (by wram_simp [st_v, st_pre, hcur])
            (by wram_simp [st_v, hxor_a]) hdeg
        have hlen_1 : x.mem p = 1 := by simpa using hlen_p
        unfold implDegBody
        wram_exec [hc1, hpR, hi, hlen_1, hmem_a, hf_na]
        refine WP.of_execWithin hy₁_ex ?_
        wram_exec [hy₁_fr, st_v, st_pre, hc1, hi, hf_p2, hf_i1]
        refine ⟨fun u => ?_, fun addr_a ha => ?_, by wram_simp, by wram_simp; omega,
          fun r hr => ?_⟩
        · wram_simp
          rw [hy₁_deg u, mapAdj_addClauseEdges_one]
          by_cases hu : u = litEquiv G.n a.negate <;> simp [hu]
        · wram_simp; exact hy₁_out addr_a ha
        · wram_simp [hy₁_fr r (by reg_ne) (by reg_ne), st_v, st_pre]
      · have hmem_a : x.mem (p + 1) = litCodeBy Fin.val a := by simpa using hlit_p 0 (by simp)
        have hmem_b : x.mem (p + 1 + 1) = litCodeBy Fin.val b := by
          simpa [Nat.add_assoc] using hlit_p 1 (by simp)
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
            2 * G.φ.length := by
          have hle1 : (g₁ a.negate).length ≤ (addClauseEdges g [a, b] a.negate).length := by
            dsimp only [addClauseEdges, g₁]
            by_cases hab : a.negate = b.negate <;> simp [hab]
          have hle2 := length_le_foldl_addClauseEdges cs (addClauseEdges g [a, b]) a.negate
          rw [htarget'] at hle2
          have hfin := hbound_imp (litEquiv G.n a.negate)
          simp only [Instance.adjFin, mapAdj, Equiv.symm_apply_apply, List.length_map, g₁,
            Function.update_self, List.length_cons] at hle1 hle2 hfin ⊢
          omega
        have hroom_b : (mapAdj (litEquiv G.n) g₁ (litEquiv G.n b.negate)).length + 1 ≤
            2 * G.φ.length := by
          have hle2 := length_le_foldl_addClauseEdges cs (addClauseEdges g [a, b]) b.negate
          rw [htarget'] at hle2
          have hfin := hbound_imp (litEquiv G.n b.negate)
          simp only [Instance.adjFin, mapAdj, Equiv.symm_apply_apply, List.length_map,
            addClauseEdges, Function.update_self, List.length_cons] at hle2 hfin ⊢
          exact hle2.trans hfin
        have hf_p3 : Fits w (p + 1 + 1 + 1) :=
          G.fits_of_le hfit (by have := G.encode_length; unfold Instance.wordBound; omega)
        have hf_na := fits_litCode_xor_one G hfit a
        have hf_nb := fits_litCode_xor_one G hfit b
        have hf_i1 : Fits w (idx + 1) := G.fits_of_le hfit (by unfold Instance.wordBound; omega)
        let st_v1 := (((((x.set jReg 2).set pReg (p + 1)).set uReg (litCodeBy Fin.val a)).set
          pReg (p + 1 + 1)).set oldFinReg (litCodeBy Fin.val b)).set
          vReg (litCodeBy Fin.val a ^^^ 1)
        obtain ⟨y₁, hy₁_ex, hy₁_deg, hy₁_out, hy₁_fr⟩ :=
          incCurCode_spec (N := 2 * G.n) curBase (2 * G.φ.length) hfit_cur
            (fun u => (mapAdj (litEquiv G.n) g u).length) (litEquiv G.n a.negate) hroom_a
            (x := st_v1) (by wram_simp [st_v1, hc1]) (by wram_simp [st_v1, hcur])
            (by wram_simp [st_v1, hxor_a]) hdeg
        have hy₁_deg' : ∀ u : Fin (2 * G.n), y₁.mem (curBase + u.val) =
            (mapAdj (litEquiv G.n) g₁ u).length := by
          intro u
          rw [hy₁_deg u, hg₁_map]
          by_cases hu : u = litEquiv G.n a.negate <;> simp [hu]
        let st_v2 := y₁.set vReg (litCodeBy Fin.val b ^^^ 1)
        obtain ⟨y₂, hy₂_ex, hy₂_deg, hy₂_out, hy₂_fr⟩ :=
          incCurCode_spec (N := 2 * G.n) curBase (2 * G.φ.length) hfit_cur
            (fun u => (mapAdj (litEquiv G.n) g₁ u).length) (litEquiv G.n b.negate) hroom_b
            (x := st_v2) (by wram_simp [st_v2, hy₁_fr, st_v1, hc1])
            (by wram_simp [st_v2, hy₁_fr, st_v1, hcur]) (by wram_simp [st_v2, hxor_b]) hy₁_deg'
        have hlen_2 : x.mem p = 2 := by simpa using hlen_p
        unfold implDegBody
        wram_exec [hc1, hpR, hi, hlen_2, hmem_a, hmem_b, hf_na]
        refine WP.of_execWithin hy₁_ex ?_
        wram_exec [hy₁_fr, st_v1, hc1, hf_nb]
        refine WP.of_execWithin hy₂_ex ?_
        wram_exec [hy₂_fr, st_v2, hy₁_fr, st_v1, hc1, hi, hf_p3, hf_i1]
        refine ⟨fun u => ?_, fun addr_a ha => ?_, by wram_simp, by wram_simp; omega,
          fun r hr => ?_⟩
        · wram_simp
          rw [hy₂_deg u, mapAdj_addClauseEdges_two, ← hg₁_map]
          by_cases hu : u = litEquiv G.n b.negate <;> simp [hu]
        · wram_simp; exact (hy₂_out addr_a ha).trans (hy₁_out addr_a ha)
        · wram_simp [hy₂_fr r (by reg_ne) (by reg_ne), st_v2, hy₁_fr r (by reg_ne) (by reg_ne),
            st_v1]
      · simp at hc
    have hcm_x₁ : ClauseMemAt x₁.mem (p + 1 + c.length) cs := by
      intro k hk
      have hk_bound : p + 1 + c.length + k < curBase := by
        rw [hflat_cons] at hp
        simp only [curBase, kCurAddr, Instance.workBase, Instance.outAddrBase]
        omega
      rw [hx₁_out _ (by omega)]
      exact hcm_rest k hk
    have hlt : (Cond.lt iReg mClauses).Holds x := by
      change x.regs iReg < x.regs mClauses
      simp only [List.length_cons] at hidx
      omega
    obtain ⟨y, hy_ex, hy_deg, hy_out, hy_fr⟩ := implDegLoop_spec G hfit cs
      (addClauseEdges g c) (idx + 1) (p + 1 + c.length) x₁ hrest (.inr htarget')
      (by simp only [List.length_cons] at hidx; omega)
      (by rw [hflat_cons] at hp; omega) hcm_x₁ hx₁_deg
      ((hx₁_fr cOne (by decide)).trans hc1)
      ((hx₁_fr mClauses (by decide)).trans hm)
      ((hx₁_fr curB (by decide)).trans hcur)
      hx₁_i hx₁_p
    refine ⟨y, (hx₁_ex.loop_iter hlt hy_ex).mono (by simp only [List.length_cons]; omega), hy_deg,
      fun a ha => (hy_out a ha).trans (hx₁_out a ha),
      fun r hr => (hy_fr r hr).trans (hx₁_fr r hr)⟩

theorem not_readsWidth_implDegBody : ¬ implDegBody.ReadsWidth := by
  simp [implDegBody, Code.ReadsWidth, Op.ReadsWidth, Op.bin, not_readsWidth_incCurCode]

theorem isRandFree_implDegBody : implDegBody.IsRandFree := by
  simp only [implDegBody, Code.IsRandFree, isRandFree_incCurCode, and_self]

end Cslib.Algorithms.WordRAM.TwoSAT
