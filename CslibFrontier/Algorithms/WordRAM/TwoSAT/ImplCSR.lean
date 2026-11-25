/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.TwoSAT.EquivDFS
public import CslibFrontier.Algorithms.WordRAM.TwoSAT.Layout
import CslibFrontier.Algorithms.WordRAM.TwoSAT.ImplDeg
import CslibFrontier.Algorithms.WordRAM.TwoSAT.ImplFill

/-!
# Implication-graph CSR assembly (`buildImplCSRCode`, `buildImplCSRCode_spec`)

Combines degree counting, prefix sums, and edge backfilling to establish `CSRAt G.adjFin`.
-/

public section

namespace Cslib.Algorithms.WordRAM.TwoSAT

open Cslib.Logic.PL Cslib.WordRAM
open Cslib.Algorithms.Lean.TwoSAT
open Cslib.Algorithms.WordRAM.ClauseCode
open Reg Cslib.Algorithms.WordRAM.DFS Cslib.Algorithms.WordRAM.DFS.Reg

/-- Build the CSR representation of `G.adjFin` at `(offB, edgeB)` in `O(n + |φ|)` steps. -/
def buildImplCSRCode : Code .standard 28 :=
  (zeroBlockCode curB).seq
    ((ram[ iReg ← cZero; pReg ← cThree ]).seq
      ((Code.loop (.lt iReg mClauses) implDegBody).seq
        (prefixSumCode.seq
          ((ram[ iReg ← cZero; pReg ← cThree ]).seq
            (Code.loop (.lt iReg mClauses) implFillBody)))))

theorem buildImplCSRCode_spec (G : Instance) {w : ℕ} (hfit : Fits w G.wordBound)
    (hcs : ∀ c ∈ G.φ, 1 ≤ c.length ∧ c.length ≤ 2) {x : Data 28}
    (hcm : ClauseMemAt x.mem 3 G.φ)
    (hc0 : x.regs cZero = 0) (hc1 : x.regs cOne = 1) (hc3 : x.regs cThree = 3)
    (hm : x.regs mClauses = G.φ.length) (hNv : x.regs nVerts = 2 * G.n)
    (hoffB : x.regs offB = kOffAddr G.workBase)
    (hedgeB : x.regs edgeB = kEdgeAddr G.workBase (2 * G.n))
    (hcurB : x.regs curB = kCurAddr G.workBase (2 * G.n) (2 * G.φ.length)) :
    ∃ y, ExecWithin w buildImplCSRCode x y (26 * G.n + 49 * G.φ.length + 18) ∧
      CSRAt G.adjFin (kOffAddr G.workBase) (kEdgeAddr G.workBase (2 * G.n)) y.mem ∧
      (∀ a, a < G.workBase → y.mem a = x.mem a) ∧
      (∀ r : Fin 28, r.val < 18 → y.regs r = x.regs r) := by
  set N := 2 * G.n
  set Mc := 2 * G.φ.length
  set curBase := kCurAddr G.workBase N Mc
  set offBase := kOffAddr G.workBase
  set edgeBase := kEdgeAddr G.workBase N
  have hfit_cur : Fits w (curBase + N) :=
    G.fits_of_le hfit (by
      simp only [curBase, N, Mc, kCurAddr, Instance.workBase, Instance.outAddrBase,
        G.encode_length, Instance.wordBound]; omega)
  obtain ⟨x₁, hx₁_ex, hx₁_zero, hx₁_out, hx₁_fr⟩ :=
    zeroBlockCode_spec curB (by decide) curBase N hfit_cur hc0 hc1 hcurB hNv
  have hcm₁ : ClauseMemAt x₁.mem 3 G.φ := by
    intro k hk
    rw [hx₁_out _ (by
      simp only [curBase, kCurAddr, Instance.workBase, Instance.outAddrBase,
        Instance.encode, List.length_cons] at *; omega)]
    exact hcm k hk
  have resetCursor (s : Data 28) (h0 : s.regs cZero = 0) (h3 : s.regs cThree = 3) :
      ExecWithin (B := .standard) w (ram[ iReg ← cZero; pReg ← cThree ])
        s ((s.set iReg 0).set pReg 3) 2 := by wram_exec [h0, h3]
  let x₂ := (x₁.set iReg 0).set pReg 3
  have hp₁ := resetCursor x₁ ((hx₁_fr cZero (by decide)).trans hc0)
    ((hx₁_fr cThree (by decide)).trans hc3)
  have hlen_enc : 3 + (G.φ.flatMap (encodeClauseBy Fin.val)).length = G.encode.length + 1 := by
    simp only [Instance.encode, List.length_cons]; omega
  obtain ⟨x₃, hx₃_ex, hx₃_deg, hx₃_out, hx₃_fr⟩ :=
    implDegLoop_spec G hfit G.φ (fun _ => []) 0 3 x₂ hcs (.inr rfl) (by simp) hlen_enc hcm₁
      (fun u => by dsimp only [x₂]; simpa [mapAdj] using hx₁_zero u.val u.isLt)
      (by dsimp only [x₂]; wram_simp; exact (hx₁_fr cOne (by decide)).trans hc1)
      (by dsimp only [x₂]; wram_simp; exact (hx₁_fr mClauses (by decide)).trans hm)
      (by dsimp only [x₂]; wram_simp; exact (hx₁_fr curB (by decide)).trans hcurB)
      (by dsimp only [x₂]; wram_simp)
      (by dsimp only [x₂]; wram_simp)
  have hx₃_fr0 : ∀ r : Fin 28, r.val < 18 → x₃.regs r = x.regs r := fun r hr => by
    rw [hx₃_fr r hr]; dsimp only [x₂]; regs_lt; exact hx₁_fr r hr
  have hfit_ps : Fits w (curBase + N + Mc + 2) :=
    G.fits_of_le hfit (by
      simp only [curBase, N, Mc, kCurAddr, Instance.workBase, Instance.outAddrBase,
        G.encode_length, Instance.wordBound]; omega)
  obtain ⟨x₄, hx₄_ex, hx₄_off, hx₄_cur, hx₄_out, hx₄_fr⟩ :=
    prefixSumCode_spec G.adjFin curBase offBase Mc
      (by simp only [offBase, curBase, kOffAddr, kCurAddr]; omega)
      (csrOffset_adjFin_le G) hfit_ps
      ((hx₃_fr0 cZero (by decide)).trans hc0)
      ((hx₃_fr0 cOne (by decide)).trans hc1)
      ((hx₃_fr0 curB (by decide)).trans hcurB)
      ((hx₃_fr0 offB (by decide)).trans hoffB)
      ((hx₃_fr0 nVerts (by decide)).trans hNv)
      hx₃_deg
  have hx₄_fr0 : ∀ r : Fin 28, r.val < 18 → x₄.regs r = x.regs r :=
    fun r hr => (hx₄_fr r hr).trans (hx₃_fr0 r hr)
  have hcm₄ : ClauseMemAt x₄.mem 3 G.φ := by
    intro k hk
    have hk_lt : 3 + k < G.workBase := by
      simp only [Instance.workBase, Instance.outAddrBase, Instance.encode,
        List.length_cons] at *; omega
    rw [hx₄_out _ (by dsimp only [offBase, curBase, N, Mc]; simp only [kOffAddr, kCurAddr]; omega),
      hx₃_out _ (by dsimp only [kCurAddr]; omega)]
    exact hcm₁ k hk
  let x₅ := (x₄.set iReg 0).set pReg 3
  have hp₂ := resetCursor x₄ ((hx₄_fr0 cZero (by decide)).trans hc0)
    ((hx₄_fr0 cThree (by decide)).trans hc3)
  have hmap_empty : mapAdj (litEquiv G.n) (fun _ => []) = (fun _ => []) := funext fun _ => rfl
  obtain ⟨y, hy_ex, hy_pcsr, hy_out, hy_fr⟩ :=
    implFillLoop_spec G hfit G.φ (fun _ => []) 0 3 x₅ hcs (.inr rfl) (by simp) hlen_enc hcm₄
      (hmap_empty ▸ partialCSRAt_init G.adjFin curBase edgeBase x₄.mem hx₄_cur)
      (by dsimp only [x₅]; wram_simp; exact (hx₄_fr0 cOne (by decide)).trans hc1)
      (by dsimp only [x₅]; wram_simp; exact (hx₄_fr0 mClauses (by decide)).trans hm)
      (by dsimp only [x₅]; wram_simp; exact (hx₄_fr0 curB (by decide)).trans hcurB)
      (by dsimp only [x₅]; wram_simp; exact (hx₄_fr0 edgeB (by decide)).trans hedgeB)
      (by dsimp only [x₅]; wram_simp)
      (by dsimp only [x₅]; wram_simp)
  have hy_off : ∀ u ≤ N, y.mem (offBase + u) = csrOffset G.adjFin u := fun u hu => by
    rw [hy_out _ (by dsimp only [offBase, N, kOffAddr, kCurAddr, kEdgeAddr]; omega)]
    exact hx₄_off u hu
  have hy_csr : CSRAt G.adjFin offBase edgeBase y.mem :=
    csrAt_of_partialCSRAt G.adjFin offBase curBase edgeBase y.mem hy_off hy_pcsr
  refine ⟨y,
    (hx₁_ex.seq (hp₁.seq (hx₃_ex.seq (hx₄_ex.seq (hp₂.seq hy_ex))))).mono
      (by dsimp only [N]; omega),
    hy_csr, fun a ha => ?_, fun r hr => ?_⟩
  · rw [hy_out _ (by dsimp only [kCurAddr, kEdgeAddr]; omega)]
    dsimp only [x₅]; mem_upd
    rw [hx₄_out _ (by dsimp only [offBase, curBase, N, Mc, kOffAddr, kCurAddr]; omega),
      hx₃_out _ (by dsimp only [kCurAddr]; omega)]
    dsimp only [x₂]; mem_upd
    exact hx₁_out _ (by dsimp only [curBase, N, Mc, kCurAddr]; omega)
  · rw [hy_fr r hr]; dsimp only [x₅]; regs_lt; exact hx₄_fr0 r hr

theorem not_readsWidth_buildImplCSRCode : ¬ buildImplCSRCode.ReadsWidth := by
  simp [buildImplCSRCode, Code.ReadsWidth, Op.ReadsWidth,
    not_readsWidth_zeroBlockCode, not_readsWidth_implDegBody,
    not_readsWidth_prefixSumCode, not_readsWidth_implFillBody]

theorem isRandFree_buildImplCSRCode : buildImplCSRCode.IsRandFree := by
  simp only [buildImplCSRCode, Code.IsRandFree,
    isRandFree_zeroBlockCode, isRandFree_implDegBody,
    isRandFree_prefixSumCode, isRandFree_implFillBody, and_self]

end Cslib.Algorithms.WordRAM.TwoSAT
