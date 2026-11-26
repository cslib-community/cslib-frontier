/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.DFS.CSR
import all CslibFrontier.Algorithms.WordRAM.DFS.CSR
import CslibFrontier.Computability.WordRAM.SymbolicExec

/-!
# Word-RAM CSR graph transposition (`O(N + M)`)

## Main definitions

* `Cslib.Algorithms.WordRAM.DFS.transposeCSRCode`: in-degree count, prefix sums, and backward
  fill of reversed CSR arcs.

## Main results

* `Cslib.Algorithms.WordRAM.DFS.transposeCSRCode_spec`: proves `transposeCSRCode` builds
  `CSRAt (transposeAdj adj (List.finRange N))` in `31 * N + 20 * Mc + 22` instructions.
-/

public section

namespace Cslib.Algorithms.WordRAM.DFS

open Cslib.WordRAM
open Cslib.Algorithms.Lean.DFS
open Reg

/-! ### Pass 2: CSR transpose construction (`O(N + M)`) -/

/-- Scan the CSR arcs leaving `uIdxReg` and run `stepBody` on each `(u = uIdxReg, v = vReg)`. -/
private def forEachArcInner (fwdEdgeReg : Fin 28) (stepBody : Code .standard 28) :
    Code .standard 28 :=
  (ram[ addr ← fwdEdgeReg + jReg; vReg ← *addr ]).seq
    (stepBody.seq (ram[ jReg ← jReg + cOne ]))

/-- Scan every CSR vertex `uIdxReg < nVerts` and its outgoing arcs, running `stepBody` on each. -/
private def forEachArc (fwdEdgeReg uIdxReg : Fin 28) (stepBody : Code .standard 28) :
    Code .standard 28 :=
  Code.loop (.lt uIdxReg nVerts)
    ((ram[ addr ← offB + uIdxReg; jReg ← *addr; addr ← addr + cOne; oldFinReg ← *addr ]).seq
      ((Code.loop (.lt jReg oldFinReg) (forEachArcInner fwdEdgeReg stepBody)).seq
        (ram[ uIdxReg ← uIdxReg + cOne ])))

/-- CSR transposition: in-degree count, prefix sums and backward fill of the reversed arcs. -/
def transposeCSRCode : Code .standard 28 :=
  (zeroBlockCode curB).seq
    ((ram[ iReg ← cZero ]).seq
      ((forEachArc edgeB iReg incCurCode).seq
        ((ram[ compIdxReg ← offB; offB ← revOffB ]).seq
          (prefixSumCode.seq
            ((ram[ offB ← compIdxReg; finCnt ← edgeB; edgeB ← revEdgeB; uReg ← cZero ]).seq
              ((forEachArc finCnt uReg backfillStepCode).seq
                (ram[ offB ← revOffB ])))))))

private theorem length_foldl_rev_le {N : ℕ} (u : Fin N) :
    ∀ (es : List (Fin N)) (rev : Fin N → List (Fin N)) (w : Fin N),
      (rev w).length ≤
        (es.foldl (fun r v => Function.update r v (u :: r v)) rev w).length
  | [], _, _ => le_rfl
  | v :: es, rev, w => by
    have h1 : (rev w).length ≤ (Function.update rev v (u :: rev v) w).length := by
      by_cases hw : w = v <;> simp [hw]
    exact h1.trans (length_foldl_rev_le u es (Function.update rev v (u :: rev v)) w)

private theorem length_foldl_vs_rev_le {N : ℕ} (adj : Fin N → List (Fin N)) :
    ∀ (us : List (Fin N)) (rev : Fin N → List (Fin N)) (w : Fin N),
      (rev w).length ≤
        (us.foldl (fun r u => (adj u).foldl (fun r v => Function.update r v (u :: r v)) r)
          rev w).length
  | [], _, _ => le_rfl
  | u :: us, rev, w =>
    (length_foldl_rev_le u (adj u) rev w).trans
      (length_foldl_vs_rev_le adj us _ w)

private abbrev revGraph {N : ℕ} (adj : Fin N → List (Fin N)) : Fin N → List (Fin N) :=
  transposeAdj adj (List.finRange N)


/-- A CSR graph survives a run that writes only addresses `MemWrite` outside it. -/
private theorem CSRAt.of_unwritten {N : ℕ} {adj : Fin N → List (Fin N)} {wb : ℕ}
    {MemWrite : ℕ → Prop} {mem₁ mem₂ : ℕ → ℕ}
    (h : CSRAt adj (kOffAddr wb) (kEdgeAddr wb N) mem₁)
    (hdisj : ∀ a, MemWrite a →
      ¬ ((kOffAddr wb ≤ a ∧ a < kOffAddr wb + N + 1) ∨
        (kEdgeAddr wb N ≤ a ∧ a < kEdgeAddr wb N + csrOffset adj N)))
    (hout : ∀ a, ¬ MemWrite a → mem₂ a = mem₁ a) :
    CSRAt adj (kOffAddr wb) (kEdgeAddr wb N) mem₂ :=
  h.of_eqOn (fun _ _ => hout _ fun hw => hdisj _ hw (.inl ⟨by omega, by omega⟩))
    (fun _ _ => hout _ fun hw => hdisj _ hw (.inr ⟨by omega, by omega⟩))

private theorem forEachArcInner_spec {N w : ℕ} (adj : Fin N → List (Fin N))
    (wb Mc : ℕ) (hmc : csrOffset adj N ≤ Mc) (hfit : Fits w (kTopAddr wb N Mc + Mc + 4))
    (fwdEdgeReg uIdxReg : Fin 28) (stepBody : Code .standard 28) (stepTime : ℕ)
    (bound : Fin N → ℕ) (Inv : (Fin N → List (Fin N)) → (ℕ → ℕ) → Prop)
    (MemWrite : ℕ → Prop) (ConstRegs : Data 28 → Prop)
    (hu_lo : 18 ≤ uIdxReg.val) (hu_hi : uIdxReg.val < 24)
    (hfwd_hi : fwdEdgeReg.val < 24) (hfwd_ne : fwdEdgeReg ≠ uIdxReg)
    (hdisj : ∀ a, MemWrite a →
      ¬ ((kOffAddr wb ≤ a ∧ a < kOffAddr wb + N + 1) ∨
        (kEdgeAddr wb N ≤ a ∧ a < kEdgeAddr wb N + csrOffset adj N)))
    (hconst_regs : ∀ d₁ d₂ : Data 28,
      (∀ r : Fin 28, r.val < 18 → d₁.regs r = d₂.regs r) → ConstRegs d₁ → ConstRegs d₂)
    (hstep : ∀ (u v : Fin N) (rev : Fin N → List (Fin N)) (s : Data 28),
      (rev v).length + 1 ≤ bound v → Inv rev s.mem →
      s.regs cOne = 1 → s.regs uIdxReg = u.val → s.regs vReg = v.val → ConstRegs s →
      ∃ y, ExecWithin w stepBody s y stepTime ∧
        Inv (Function.update rev v (u :: rev v)) y.mem ∧
        (∀ a, ¬ MemWrite a → y.mem a = s.mem a) ∧
        (∀ r : Fin 28, r ≠ addr → r ≠ jEndReg → y.regs r = s.regs r))
    (u : Fin N) :
    ∀ (es : List (Fin N)) (k : ℕ) (rev : Fin N → List (Fin N)) (x : Data 28)
      (_ : k + es.length = (adj u).length),
      (∀ q (hq : q < es.length), (adj u)[k + q]'(by omega) = es[q]) →
      (∀ z : Fin N,
        (es.foldl (fun r v => Function.update r v (u :: r v)) rev z).length ≤ bound z) →
      Inv rev x.mem → CSRAt adj (kOffAddr wb) (kEdgeAddr wb N) x.mem →
      x.regs cOne = 1 → x.regs fwdEdgeReg = kEdgeAddr wb N → ConstRegs x →
      x.regs uIdxReg = u.val → x.regs jReg = csrOffset adj u.val + k →
      x.regs oldFinReg = csrOffset adj u.val + (adj u).length →
      ∃ y, ExecWithin w (.loop (.lt jReg oldFinReg) (forEachArcInner fwdEdgeReg stepBody)) x y
          ((stepTime + 5) * es.length + 2) ∧
        Inv (es.foldl (fun r v => Function.update r v (u :: r v)) rev) y.mem ∧
        (∀ a, ¬ MemWrite a → y.mem a = x.mem a) ∧
        (∀ r : Fin 28, r.val < 24 → y.regs r = x.regs r)
  | [], k, rev, x, hk, _, _, hinv, _, _, _, _, _, hj, hof => by
    simp only [List.length_nil, Nat.add_zero] at hk
    have hend : ¬ (Cond.lt jReg oldFinReg).Holds x := by
      change ¬ x.regs jReg < x.regs oldFinReg; omega
    exact ⟨x, ExecWithin.loop_exit hend, hinv, fun _ _ => rfl, fun _ _ => rfl⟩
  | v :: es, k, rev, x, hk, hget, hroom_all, hinv, hcsr, hc1, hfwd, hconst, huR, hj, hof => by
    simp only [List.length_cons] at hk
    have hk_lt : k < (adj u).length := by omega
    have hv_eq : (adj u)[k] = v := by
      simpa only [Nat.add_zero, List.getElem_cons_zero] using hget 0 (Nat.zero_lt_succ _)
    have hmem_e : x.mem (kEdgeAddr wb N + (csrOffset adj u.val + k)) = v.val := by
      rw [← Nat.add_assoc, hcsr.2 u k hk_lt, hv_eq]
    have hj_lt_M : csrOffset adj u.val + k < csrOffset adj N := by
      have h1 := csrOffset_succ adj u.isLt; simp only [Fin.eta] at h1
      have h2 := csrOffset_mono adj (by omega : u.val + 1 ≤ N); omega
    have hf_eaddr : Fits w (kEdgeAddr wb N + (csrOffset adj u.val + k)) :=
      hfit.of_le (by simp only [kEdgeAddr, kTopAddr]; omega)
    have hf_j1 : Fits w (csrOffset adj u.val + k + 1) :=
      hfit.of_le (by simp only [kTopAddr]; omega)
    have hroom_v : (rev v).length + 1 ≤ bound v := by
      simpa using (length_foldl_rev_le u es (Function.update rev v (u :: rev v)) v).trans
        (hroom_all v)
    let st_v := (x.set addr (kEdgeAddr wb N + (csrOffset adj u.val + k))).set vReg v.val
    have hp1 : ExecWithin w (ram[ addr ← fwdEdgeReg + jReg; vReg ← *addr ]) x st_v 2 := by
      wram_exec [hfwd, hj, hmem_e]
    obtain ⟨y₁, hy₁_ex, hy₁_inv, hy₁_out, hy₁_fr⟩ :=
      hstep u v rev st_v hroom_v hinv (by wram_simp [st_v, hc1]) (by wram_simp [st_v, huR])
        (by wram_simp [st_v]) (hconst_regs _ _ (fun r hr => by wram_simp [st_v]) hconst)
    have hy₁_lt : ∀ r : Fin 28, r.val < 24 → y₁.regs r = x.regs r := fun r hr => by
      rw [hy₁_fr r (Fin.ne_of_val_ne (by change r.val ≠ 27; omega))
        (Fin.ne_of_val_ne (by change r.val ≠ 26; omega))]
      wram_simp [st_v]
    have hy₁_j : y₁.regs jReg = csrOffset adj u.val + k :=
      (hy₁_fr jReg (by decide) (by decide)).trans (by wram_simp [st_v, hj])
    let x₂ := y₁.set jReg (csrOffset adj u.val + k + 1)
    have hp2 : ExecWithin w (ram[ jReg ← jReg + cOne ]) y₁ x₂ 1 := by
      wram_exec [hy₁_j, hy₁_lt cOne (by decide), hc1, hf_j1]
    have hx₂_lt : ∀ r : Fin 28, r.val < 24 → x₂.regs r = x.regs r := fun r hr => by
      rw [← hy₁_lt r hr]; wram_simp [x₂]
    obtain ⟨y, hy_ex, hy_inv, hy_out, hy_fr⟩ :=
      forEachArcInner_spec adj wb Mc hmc hfit fwdEdgeReg uIdxReg stepBody stepTime bound Inv
        MemWrite ConstRegs hu_lo hu_hi hfwd_hi hfwd_ne hdisj hconst_regs hstep u es (k + 1)
        (Function.update rev v (u :: rev v)) x₂ (by omega)
        (fun q hq => by
          simpa [Nat.add_assoc, Nat.add_comm 1 q] using hget (q + 1) (Nat.succ_lt_succ hq))
        (fun z => by simpa [List.foldl_cons] using hroom_all z)
        hy₁_inv (hcsr.of_unwritten hdisj hy₁_out) ((hx₂_lt cOne (by decide)).trans hc1)
        ((hx₂_lt _ hfwd_hi).trans hfwd)
        (hconst_regs _ _ (fun r hr => (hx₂_lt r (by omega)).symm) hconst)
        ((hx₂_lt _ hu_hi).trans huR) (by wram_simp [x₂]; omega)
        ((hx₂_lt oldFinReg (by decide)).trans hof)
    have hlt : (Cond.lt jReg oldFinReg).Holds x := by
      change x.regs jReg < x.regs oldFinReg; omega
    refine ⟨y, ((hp1.seq (hy₁_ex.seq hp2)).loop_iter hlt hy_ex).mono ?_, hy_inv,
      fun a ha => (hy_out a ha).trans (hy₁_out a ha), fun r hr => (hy_fr r hr).trans (hx₂_lt r hr)⟩
    simp only [List.length_cons, Nat.mul_add, Nat.mul_one]
    omega

private theorem forEachArc_spec {N w : ℕ} (adj : Fin N → List (Fin N))
    (wb Mc : ℕ) (hmc : csrOffset adj N ≤ Mc) (hfit : Fits w (kTopAddr wb N Mc + Mc + 4))
    (fwdEdgeReg uIdxReg : Fin 28) (stepBody : Code .standard 28) (stepTime : ℕ)
    (bound : Fin N → ℕ) (Inv : (Fin N → List (Fin N)) → (ℕ → ℕ) → Prop)
    (MemWrite : ℕ → Prop) (ConstRegs : Data 28 → Prop)
    (hu_lo : 18 ≤ uIdxReg.val) (hu_hi : uIdxReg.val < 24) (hu_ne_of : uIdxReg ≠ oldFinReg)
    (hfwd_hi : fwdEdgeReg.val < 24) (hfwd_ne_of : fwdEdgeReg ≠ oldFinReg)
    (hfwd_ne : fwdEdgeReg ≠ uIdxReg)
    (hdisj : ∀ a, MemWrite a →
      ¬ ((kOffAddr wb ≤ a ∧ a < kOffAddr wb + N + 1) ∨
        (kEdgeAddr wb N ≤ a ∧ a < kEdgeAddr wb N + csrOffset adj N)))
    (hconst_regs : ∀ d₁ d₂ : Data 28,
      (∀ r : Fin 28, r.val < 18 → d₁.regs r = d₂.regs r) → ConstRegs d₁ → ConstRegs d₂)
    (hstep : ∀ (u v : Fin N) (rev : Fin N → List (Fin N)) (s : Data 28),
      (rev v).length + 1 ≤ bound v → Inv rev s.mem →
      s.regs cOne = 1 → s.regs uIdxReg = u.val → s.regs vReg = v.val → ConstRegs s →
      ∃ y, ExecWithin w stepBody s y stepTime ∧
        Inv (Function.update rev v (u :: rev v)) y.mem ∧
        (∀ a, ¬ MemWrite a → y.mem a = s.mem a) ∧
        (∀ r : Fin 28, r ≠ addr → r ≠ jEndReg → y.regs r = s.regs r)) :
    ∀ (us : List (Fin N)) (idx : ℕ) (rev : Fin N → List (Fin N)) (x : Data 28)
      (_ : idx + us.length = N),
      (∀ q (hq : q < us.length), us[q].val = idx + q) →
      (∀ z : Fin N,
        (us.foldl (fun r u => (adj u).foldl (fun r v => Function.update r v (u :: r v)) r)
          rev z).length ≤ bound z) →
      Inv rev x.mem → CSRAt adj (kOffAddr wb) (kEdgeAddr wb N) x.mem →
      x.regs cOne = 1 → x.regs nVerts = N → x.regs offB = kOffAddr wb →
      x.regs fwdEdgeReg = kEdgeAddr wb N → ConstRegs x → x.regs uIdxReg = idx →
      ∃ y, ExecWithin w (forEachArc fwdEdgeReg uIdxReg stepBody) x y
          (9 * us.length + (stepTime + 5) * outDegreeSum adj us + 2) ∧
        Inv (us.foldl (fun r u => (adj u).foldl (fun r v => Function.update r v (u :: r v)) r)
          rev) y.mem ∧
        (∀ a, ¬ MemWrite a → y.mem a = x.mem a) ∧
        (∀ r : Fin 28, r.val < 18 → y.regs r = x.regs r)
  | [], idx, rev, x, hidx, _, _, hinv, _, _, hNv, _, _, _, huIdx => by
    simp only [List.length_nil, Nat.add_zero] at hidx
    have hend : ¬ (Cond.lt uIdxReg nVerts).Holds x := by
      change ¬ x.regs uIdxReg < x.regs nVerts; omega
    exact ⟨x, (ExecWithin.loop_exit hend).mono (by simp [outDegreeSum]),
      hinv, fun _ _ => rfl, fun _ _ => rfl⟩
  | u :: us, idx, rev, x, hidx, hus, hroom_all, hinv, hcsr, hc1, hNv, hoff, hfwd, hconst,
      huIdx => by
    simp only [List.length_cons] at hidx
    have hu_val : u.val = idx := by
      simpa only [List.getElem_cons_zero, Nat.add_zero] using hus 0 (Nat.zero_lt_succ _)
    have hoff_u : x.mem (kOffAddr wb + idx) = csrOffset adj u.val := by
      rw [← hu_val]; exact hcsr.1 u.val (by omega)
    have hoff_u1 : x.mem (kOffAddr wb + idx + 1) = csrOffset adj u.val + (adj u).length := by
      simpa [← hu_val, Nat.add_assoc, csrOffset_succ adj u.isLt] using
        hcsr.1 (u.val + 1) (by omega)
    have hf_oa1 : Fits w (kOffAddr wb + idx + 1) :=
      hfit.of_le (by simp only [kOffAddr, kTopAddr]; omega)
    have hf_i1 : Fits w (idx + 1) := hfit.of_le (by simp only [kTopAddr]; omega)
    let x₁ := (((x.set addr (kOffAddr wb + idx)).set jReg (csrOffset adj u.val)).set
      addr (kOffAddr wb + idx + 1)).set oldFinReg (csrOffset adj u.val + (adj u).length)
    have hp1 : ExecWithin w
        (ram[ addr ← offB + uIdxReg; jReg ← *addr; addr ← addr + cOne; oldFinReg ← *addr ])
        x x₁ 4 := by
      wram_exec [hoff, huIdx, hoff_u, hoff_u1, hc1]
    have hx₁_fr : ∀ r : Fin 28, r.val < 18 → x₁.regs r = x.regs r := fun r hr => by
      wram_simp [x₁]
    have hroom_u : ∀ z : Fin N,
        ((adj u).foldl (fun r v => Function.update r v (u :: r v)) rev z).length ≤ bound z :=
      fun z => (length_foldl_vs_rev_le adj us _ z).trans
        (by simpa [List.foldl_cons] using hroom_all z)
    obtain ⟨y₁, hy₁_ex, hy₁_inv, hy₁_out, hy₁_fr⟩ :=
      forEachArcInner_spec adj wb Mc hmc hfit fwdEdgeReg uIdxReg stepBody stepTime bound Inv
        MemWrite ConstRegs hu_lo hu_hi hfwd_hi hfwd_ne hdisj hconst_regs hstep u (adj u) 0 rev x₁
        (by simp) (fun q _ => by simp) hroom_u hinv hcsr (by wram_simp [x₁, hc1])
        (by wram_simp [x₁, hfwd]) (hconst_regs _ _ (fun r hr => (hx₁_fr r hr).symm) hconst)
        (by wram_simp [x₁, huIdx, hu_val]) (by wram_simp [x₁]) (by wram_simp [x₁])
    have hy₁_u : y₁.regs uIdxReg = idx := (hy₁_fr _ hu_hi).trans (by wram_simp [x₁, huIdx])
    have hy₁_1 : y₁.regs cOne = 1 := (hy₁_fr cOne (by decide)).trans (by wram_simp [x₁, hc1])
    let x₂ := y₁.set uIdxReg (idx + 1)
    have hp2 : ExecWithin w (ram[ uIdxReg ← uIdxReg + cOne ]) y₁ x₂ 1 := by
      wram_exec [hy₁_u, hy₁_1, hf_i1]
    have hx₂_fr0 : ∀ r : Fin 28, r.val < 18 → x₂.regs r = x.regs r := fun r hr => by
      rw [← hx₁_fr r hr, ← hy₁_fr r (by omega)]; wram_simp [x₂]
    obtain ⟨y, hy_ex, hy_inv, hy_out, hy_fr⟩ :=
      forEachArc_spec adj wb Mc hmc hfit fwdEdgeReg uIdxReg stepBody stepTime bound Inv MemWrite
        ConstRegs hu_lo hu_hi hu_ne_of hfwd_hi hfwd_ne_of hfwd_ne hdisj hconst_regs hstep
        us (idx + 1) ((adj u).foldl (fun r v => Function.update r v (u :: r v)) rev) x₂ (by omega)
        (fun q hq => by
          simpa [Nat.add_assoc, Nat.add_comm 1 q] using hus (q + 1) (Nat.succ_lt_succ hq))
        (fun z => by simpa [List.foldl_cons] using hroom_all z)
        hy₁_inv (hcsr.of_unwritten hdisj hy₁_out) ((hx₂_fr0 cOne (by decide)).trans hc1)
        ((hx₂_fr0 nVerts (by decide)).trans hNv) ((hx₂_fr0 offB (by decide)).trans hoff)
        (by rw [show x₂.regs fwdEdgeReg = y₁.regs fwdEdgeReg by wram_simp [x₂],
          hy₁_fr _ hfwd_hi]; wram_simp [x₁, hfwd])
        (hconst_regs _ _ (fun r hr => (hx₂_fr0 r hr).symm) hconst) (by wram_simp [x₂])
    have hlt : (Cond.lt uIdxReg nVerts).Holds x := by
      change x.regs uIdxReg < x.regs nVerts; omega
    refine ⟨y, ((hp1.seq (hy₁_ex.seq hp2)).loop_iter hlt hy_ex).mono ?_, hy_inv,
      fun a ha => (hy_out a ha).trans (hy₁_out a ha),
      fun r hr => (hy_fr r hr).trans (hx₂_fr0 r hr)⟩
    simp only [List.length_cons, outDegreeSum, List.map_cons, List.sum_cons,
      Nat.mul_add, Nat.mul_one]
    omega

theorem transposeCSRCode_spec {N w : ℕ} (adj : Fin N → List (Fin N))
    (wb Mc : ℕ) (hmc : csrOffset adj N ≤ Mc)
    (hfit : Fits w (kTopAddr wb N Mc + Mc + 4)) {x : Data 28}
    (hc0 : x.regs cZero = 0) (hc1 : x.regs cOne = 1) (hNv : x.regs nVerts = N)
    (hoff : x.regs offB = kOffAddr wb) (hedge : x.regs edgeB = kEdgeAddr wb N)
    (hcur : x.regs curB = kCurAddr wb N Mc)
    (hroff : x.regs revOffB = kRevOffAddr wb N Mc)
    (hredge : x.regs revEdgeB = kRevEdgeAddr wb N Mc)
    (hcsr : CSRAt adj (kOffAddr wb) (kEdgeAddr wb N) x.mem) :
    let revAdj := transposeAdj adj (List.finRange N)
    ∃ y, ExecWithin w transposeCSRCode x y (31 * N + 20 * Mc + 22) ∧
      CSRAt revAdj (kRevOffAddr wb N Mc) (kRevEdgeAddr wb N Mc) y.mem ∧
      y.regs offB = kRevOffAddr wb N Mc ∧
      y.regs edgeB = kRevEdgeAddr wb N Mc ∧
      (∀ a, ¬ ((kRevOffAddr wb N Mc ≤ a ∧ a < kRevOffAddr wb N Mc + N + 1) ∨
          (kRevEdgeAddr wb N Mc ≤ a ∧ a < kRevEdgeAddr wb N Mc + Mc) ∨
          (kCurAddr wb N Mc ≤ a ∧ a < kCurAddr wb N Mc + N)) → y.mem a = x.mem a) ∧
      (∀ r : Fin 28, r.val < 18 → r ≠ offB → r ≠ edgeB → y.regs r = x.regs r) := by
  set revAdj := transposeAdj adj (List.finRange N)
  have hmc_rev : csrOffset revAdj N ≤ Mc := by
    dsimp only [revAdj]; rwa [csrOffset_transposeAdj_eq]
  have hfit_ps : Fits w (kCurAddr wb N Mc + N + Mc + 2) :=
    hfit.of_le (by simp only [kCurAddr, kTopAddr]; omega)
  obtain ⟨x₁, hx₁_ex, hx₁_zero, hx₁_out, hx₁_fr⟩ :=
    zeroBlockCode_spec curB (by decide) (kCurAddr wb N Mc) N (hfit_ps.of_le (by omega)) hc0 hc1
      hcur hNv
  have hx₁_csr : CSRAt adj (kOffAddr wb) (kEdgeAddr wb N) x₁.mem :=
    hcsr.of_eqOn
      (fun _ _ => hx₁_out _ (by dsimp only [kOffAddr, kCurAddr]; omega))
      (fun _ _ => hx₁_out _ (by dsimp only [kEdgeAddr, kCurAddr]; omega))
  let x₂ := x₁.set iReg 0
  have hp1 : ExecWithin (B := .standard) w (ram[ iReg ← cZero ]) x₁ x₂ 1 := by
    wram_exec [hx₁_fr cZero (by decide), hc0]
  have hroom_rev : ∀ z : Fin N, (revAdj z).length ≤ Mc := by
    intro z
    have h1 := csrOffset_succ revAdj z.isLt; simp only [Fin.eta] at h1
    have h2 := csrOffset_mono revAdj (by omega : z.val + 1 ≤ N); omega
  have hf_cur : Fits w (kCurAddr wb N Mc + N + Mc + 1) := hfit_ps.of_le (by omega)
  obtain ⟨x₃, hx₃_ex, hx₃_deg, hx₃_out, hx₃_fr⟩ :=
    forEachArc_spec adj wb Mc hmc hfit edgeB iReg incCurCode 4 (fun _ => Mc)
      (fun rev mem => ∀ z : Fin N, mem (kCurAddr wb N Mc + z.val) = (rev z).length)
      (fun a => kCurAddr wb N Mc ≤ a ∧ a < kCurAddr wb N Mc + N)
      (fun d => d.regs curB = kCurAddr wb N Mc)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun a ha => by dsimp only [kOffAddr, kEdgeAddr, kCurAddr] at ha ⊢; omega)
      (fun d₁ d₂ hd h => by rw [← hd curB (by decide)]; exact h)
      (fun u v rev s hroom hinv hc1' _ hv hcur' => by
        obtain ⟨y, hy_ex, hy_deg, hy_out, hy_fr⟩ :=
          incCurCode_spec (kCurAddr wb N Mc) Mc hf_cur (fun z => (rev z).length) v hroom
            hc1' hcur' hv hinv
        refine ⟨y, hy_ex, fun z => ?_, hy_out, hy_fr⟩
        rw [hy_deg z]
        by_cases hz : z = v <;> simp [hz])
      (List.finRange N) 0 (fun _ => []) x₂ (by simp) (fun q _ => by simp)
      (fun z => hroom_rev z) (fun z => hx₁_zero z.val z.isLt)
      hx₁_csr (by wram_simp [x₂, hx₁_fr, hc1]) (by wram_simp [x₂, hx₁_fr, hNv])
      (by wram_simp [x₂, hx₁_fr, hoff]) (by wram_simp [x₂, hx₁_fr, hedge])
      (by wram_simp [x₂, hx₁_fr, hcur]) (by wram_simp [x₂])
  have hx₃_fr0 : ∀ r : Fin 28, r.val < 18 → x₃.regs r = x.regs r := fun r hr =>
    (hx₃_fr r hr).trans (by wram_simp [x₂, hx₁_fr r hr])
  let x₄ := (x₃.set compIdxReg (kOffAddr wb)).set offB (kRevOffAddr wb N Mc)
  have hp2 : ExecWithin (B := .standard) w (ram[ compIdxReg ← offB; offB ← revOffB ]) x₃ x₄ 2 := by
    wram_exec [hx₃_fr0, hoff, hroff]
  obtain ⟨x₅, hx₅_ex, hx₅_roff, hx₅_cur, hx₅_out, hx₅_fr⟩ :=
    prefixSumCode_spec revAdj (kCurAddr wb N Mc) (kRevOffAddr wb N Mc) Mc
      (by simp only [kRevOffAddr, kCurAddr]; omega) hmc_rev hfit_ps (x := x₄)
      (by wram_simp [x₄, hx₃_fr0, hc0]) (by wram_simp [x₄, hx₃_fr0, hc1])
      (by wram_simp [x₄, hx₃_fr0, hcur]) (by wram_simp [x₄])
      (by wram_simp [x₄, hx₃_fr0, hNv]) hx₃_deg
  have hx₅_comp : x₅.regs compIdxReg = kOffAddr wb :=
    (hx₅_ex.regs_eq (by decide)).trans (by wram_simp [x₄])
  have hx₅_fr0 : ∀ r : Fin 28, r.val < 18 → r ≠ offB → x₅.regs r = x.regs r := fun r hr hno =>
    (hx₅_fr r hr).trans (by wram_simp [x₄, hx₃_fr0 r hr])
  let x₆ := (((x₅.set offB (kOffAddr wb)).set finCnt (kEdgeAddr wb N)).set
    edgeB (kRevEdgeAddr wb N Mc)).set uReg 0
  have hp3 : ExecWithin (B := .standard) w
      (ram[ offB ← compIdxReg; finCnt ← edgeB; edgeB ← revEdgeB; uReg ← cZero ]) x₅ x₆ 4 := by
    wram_exec [hx₅_comp, hx₅_fr0, hedge, hredge, hc0]
  have hx₅_csr : CSRAt adj (kOffAddr wb) (kEdgeAddr wb N) x₅.mem :=
    hx₁_csr.of_eqOn
      (fun _ _ => (hx₅_out _ (by dsimp only [kOffAddr, kRevOffAddr, kCurAddr]; omega)).trans
        (hx₃_out _ (by dsimp only [kOffAddr, kCurAddr]; omega)))
      (fun _ _ => (hx₅_out _ (by dsimp only [kEdgeAddr, kRevOffAddr, kCurAddr]; omega)).trans
        (hx₃_out _ (by dsimp only [kEdgeAddr, kCurAddr]; omega)))
  obtain ⟨x₇, hx₇_ex, hx₇_pcsr, hx₇_out, hx₇_fr⟩ :=
    forEachArc_spec adj wb Mc hmc hfit finCnt uReg backfillStepCode 6 (fun z => (revAdj z).length)
      (fun rev mem => PartialCSRAt revAdj rev (kCurAddr wb N Mc) (kRevEdgeAddr wb N Mc) mem)
      (fun a => (kCurAddr wb N Mc ≤ a ∧ a < kCurAddr wb N Mc + N) ∨
        (kRevEdgeAddr wb N Mc ≤ a ∧ a < kRevEdgeAddr wb N Mc + csrOffset revAdj N))
      (fun d => d.regs curB = kCurAddr wb N Mc ∧ d.regs edgeB = kRevEdgeAddr wb N Mc)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun a ha => by
        dsimp only [kOffAddr, kEdgeAddr, kCurAddr, kRevEdgeAddr] at ha ⊢
        omega)
      (fun d₁ d₂ hd h => ⟨(hd curB (by decide)).symm ▸ h.1, (hd edgeB (by decide)).symm ▸ h.2⟩)
      (fun u v rev s hroom hinv hc1' hu hv ⟨hcur', hedge'⟩ =>
        backfillStepCode_spec revAdj rev (kCurAddr wb N Mc) (kRevEdgeAddr wb N Mc) Mc
          (by simp only [kRevEdgeAddr, kCurAddr]; omega) hmc_rev hf_cur v u hroom
          hc1' hcur' hedge' hv hu hinv)
      (List.finRange N) 0 (fun _ => []) x₆ (by simp) (fun q _ => by simp) (fun _ => le_rfl)
      (partialCSRAt_init revAdj (kCurAddr wb N Mc) (kRevEdgeAddr wb N Mc) x₅.mem hx₅_cur)
      hx₅_csr (by wram_simp [x₆, hx₅_fr0, hc1]) (by wram_simp [x₆, hx₅_fr0, hNv])
      (by wram_simp [x₆]) (by wram_simp [x₆])
      ⟨by wram_simp [x₆, hx₅_fr0, hcur], by wram_simp [x₆]⟩ (by wram_simp [x₆])
  have hx₇_rcsr : CSRAt revAdj (kRevOffAddr wb N Mc) (kRevEdgeAddr wb N Mc) x₇.mem :=
    csrAt_of_partialCSRAt revAdj (kRevOffAddr wb N Mc) (kCurAddr wb N Mc) (kRevEdgeAddr wb N Mc)
      x₇.mem (fun u hu => by
        rw [hx₇_out _ (by simp only [kRevOffAddr, kCurAddr, kRevEdgeAddr]; omega)]
        exact hx₅_roff u hu) hx₇_pcsr
  let y := x₇.set offB (kRevOffAddr wb N Mc)
  have hp4 : ExecWithin (B := .standard) w (ram[ offB ← revOffB ]) x₇ y 1 := by
    wram_exec [hx₇_fr revOffB (by decide), x₆, hx₅_fr0, hroff]
  rw [List.length_finRange, ← csrOffset_eq_outDegreeSum] at hx₃_ex hx₇_ex
  refine ⟨y,
    (hx₁_ex.seq (hp1.seq (hx₃_ex.seq (hp2.seq (hx₅_ex.seq (hp3.seq (hx₇_ex.seq hp4))))))).mono
      (by omega),
    hx₇_rcsr, by wram_simp [y], by wram_simp [y, hx₇_fr edgeB (by decide), x₆],
    fun a ha => ?_, fun r hr hno hne => ?_⟩
  · rw [show y.mem a = x₇.mem a from rfl, hx₇_out _ (by dsimp only [revAdj, revGraph] at *; omega),
      show x₆.mem a = x₅.mem a from rfl, hx₅_out _ (by omega)]
    exact (hx₃_out _ (by omega)).trans (hx₁_out _ (by omega))
  · rw [show y.regs r = x₇.regs r by wram_simp [y], hx₇_fr r hr]
    wram_simp [x₆, hx₅_fr0 r hr hno]

end Cslib.Algorithms.WordRAM.DFS
