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

local macro "reg_ne" : tactic =>
  `(tactic| exact Fin.ne_of_val_ne (by
    simp only [ne_eq, Fin.ext_iff, cZero, cOne, cThree, nVerts, offB, edgeB, visB, finB, stkB,
      curB, revOffB, revEdgeB, ordB, compB, iReg, pReg, finCnt, compIdxReg, oldFinReg, uReg, vReg,
      jReg, jEndReg, addr, outReg] at *
    omega))

local macro "regs_lt" : tactic =>
  `(tactic| (
    repeat (first
      | rw [Data.write_regs_apply]
      | rw [Data.set_regs_of_ne (by reg_ne)])
    try rfl))

local macro "mem_upd" : tactic =>
  `(tactic| simp only [Data.set_mem, Data.set_mem_apply, Data.write_mem])

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
        (∀ r : Fin 28, r ≠ addr → r ≠ jEndReg → r ≠ vReg → r ≠ jReg → y.regs r = x.regs r)
  | [], k, rev, x, hk, _, _, hinv, _, _, _, _, _, hj, hof => by
    simp only [List.length_nil, Nat.add_zero] at hk
    have hend : ¬ (Cond.lt jReg oldFinReg).Holds x := by
      change ¬ x.regs jReg < x.regs oldFinReg; omega
    exact ⟨x, ⟨2, by simp, Exec.loop_exit hend⟩, hinv, fun _ _ => rfl, fun _ _ _ _ _ => rfl⟩
  | v :: es, k, rev, x, hk, hget, hroom_all, hinv, hcsr, hc1, hfwd, hconst, huR, hj, hof => by
    simp only [List.length_cons] at hk
    have hk_lt : k < (adj u).length := by omega
    have hv_eq : (adj u)[k] = v := by
      have h0 := hget 0 (by simp)
      simpa only [Nat.add_zero, List.getElem_cons_zero] using h0
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
      have hle := length_foldl_rev_le u es (Function.update rev v (u :: rev v)) v
      have hall := hroom_all v
      simp only [List.foldl_cons] at hall
      simpa using hle.trans hall
    let st_v := (x.set addr (kEdgeAddr wb N + (csrOffset adj u.val + k))).set vReg v.val
    have hst_fr : ∀ r : Fin 28, r.val < 18 → st_v.regs r = x.regs r := fun r hr => by
      dsimp only [st_v]; rw [Data.set_regs_of_ne (by reg_ne), Data.set_regs_of_ne (by reg_ne)]
    have hst_u : st_v.regs uIdxReg = u.val := by
      dsimp only [st_v]
      have h1 : uIdxReg ≠ vReg := Fin.ne_of_val_ne (by change uIdxReg.val ≠ 24; omega)
      have h2 : uIdxReg ≠ addr := Fin.ne_of_val_ne (by change uIdxReg.val ≠ 27; omega)
      rw [Data.set_regs_of_ne h1, Data.set_regs_of_ne h2, huR]
    have hst_c1 : st_v.regs cOne = 1 := (hst_fr cOne (by decide)).trans hc1
    obtain ⟨y₁, hy₁_ex, hy₁_inv, hy₁_out, hy₁_fr⟩ :=
      hstep u v rev st_v hroom_v hinv hst_c1 hst_u
        (by dsimp only [st_v]; wram_simp) (hconst_regs _ _ (fun r hr => (hst_fr r hr).symm) hconst)
    have hp1 : ExecWithin (B := .standard) w (ram[ addr ← fwdEdgeReg + jReg; vReg ← *addr ])
        x st_v 2 := by
      have hfwd_ne_a : fwdEdgeReg ≠ addr := Fin.ne_of_val_ne (by change fwdEdgeReg.val ≠ 27; omega)
      have hj_ne_a : jReg ≠ addr := by reg_ne
      have h1 : Exec (B := .standard) w (ram[ addr ← fwdEdgeReg + jReg ]) x
          (x.set addr (kEdgeAddr wb N + (csrOffset adj u.val + k))) 1 := by
        have h : Exec (B := .standard) w (ram[ addr ← fwdEdgeReg + jReg ]) x _ 1 :=
          Exec.bin (by
            change Fits w (x.regs fwdEdgeReg + x.regs jReg); rw [hfwd, hj]; exact hf_eaddr)
        simpa [BinOp.eval, hfwd, hj] using h
      have h2 : Exec (B := .standard) w (ram[ vReg ← *addr ])
          (x.set addr (kEdgeAddr wb N + (csrOffset adj u.val + k))) st_v 1 := by
        have h := Exec.load (B := .standard) (w := w)
          (x := x.set addr (kEdgeAddr wb N + (csrOffset adj u.val + k))) (d := vReg) (a := addr)
        simpa [Data.set_regs_self, Data.set_mem, hmem_e, st_v] using h
      exact ⟨2, le_rfl, h1.seq h2⟩
    have hy₁_1 : y₁.regs cOne = 1 :=
      (hy₁_fr cOne (by decide) (by decide)).trans hst_c1
    have hy₁_j : y₁.regs jReg = csrOffset adj u.val + k :=
      (hy₁_fr jReg (by decide) (by decide)).trans (by dsimp only [st_v]; wram_simp; exact hj)
    let x₂ := y₁.set jReg (csrOffset adj u.val + (k + 1))
    have hp2 : ExecWithin w (ram[ jReg ← jReg + cOne ]) y₁ x₂ 1 := by
      have htriv : x₂ = y₁.set jReg (csrOffset adj u.val + k + 1) := by
        simp [x₂, Nat.add_assoc]
      rw [htriv]
      wram_exec [hy₁_j, hy₁_1, hf_j1]
    have hx₂_csr : CSRAt adj (kOffAddr wb) (kEdgeAddr wb N) x₂.mem :=
      hcsr.of_eqOn
        (fun i hi => by
          by_contra hne
          have hmem : MemWrite (kOffAddr wb + i) := by
            by_contra hnw; exact hne (hy₁_out _ hnw)
          exact hdisj _ hmem (.inl ⟨by omega, by omega⟩))
        (fun e he => by
          by_contra hne
          have hmem : MemWrite (kEdgeAddr wb N + e) := by
            by_contra hnw; exact hne (hy₁_out _ hnw)
          exact hdisj _ hmem (.inr ⟨by omega, by omega⟩))
    have hx₂_fr : ∀ r : Fin 28, r.val < 18 → x₂.regs r = x.regs r := fun r hr => by
      dsimp only [x₂]
      rw [Data.set_regs_of_ne (by reg_ne), hy₁_fr r (by reg_ne) (by reg_ne), hst_fr r hr]
    have hx₂_fwd : x₂.regs fwdEdgeReg = kEdgeAddr wb N := by
      dsimp only [x₂]
      have h1 : fwdEdgeReg ≠ jReg := Fin.ne_of_val_ne (by change fwdEdgeReg.val ≠ 25; omega)
      have h2 : fwdEdgeReg ≠ addr := Fin.ne_of_val_ne (by change fwdEdgeReg.val ≠ 27; omega)
      have h3 : fwdEdgeReg ≠ jEndReg := Fin.ne_of_val_ne (by change fwdEdgeReg.val ≠ 26; omega)
      have h4 : fwdEdgeReg ≠ vReg := Fin.ne_of_val_ne (by change fwdEdgeReg.val ≠ 24; omega)
      rw [Data.set_regs_of_ne h1, hy₁_fr fwdEdgeReg h2 h3]
      dsimp only [st_v]
      rw [Data.set_regs_of_ne h4, Data.set_regs_of_ne h2, hfwd]
    have hx₂_u : x₂.regs uIdxReg = u.val := by
      dsimp only [x₂]
      have h1 : uIdxReg ≠ jReg := Fin.ne_of_val_ne (by change uIdxReg.val ≠ 25; omega)
      have h2 : uIdxReg ≠ addr := Fin.ne_of_val_ne (by change uIdxReg.val ≠ 27; omega)
      have h3 : uIdxReg ≠ jEndReg := Fin.ne_of_val_ne (by change uIdxReg.val ≠ 26; omega)
      rw [Data.set_regs_of_ne h1, hy₁_fr uIdxReg h2 h3, hst_u]
    have hx₂_of : x₂.regs oldFinReg = csrOffset adj u.val + (adj u).length := by
      dsimp only [x₂]
      rw [Data.set_regs_of_ne (by reg_ne), hy₁_fr oldFinReg (by decide) (by decide)]
      dsimp only [st_v]; wram_simp; exact hof
    obtain ⟨y, hy_ex, hy_inv, hy_out, hy_fr⟩ :=
      forEachArcInner_spec adj wb Mc hmc hfit fwdEdgeReg uIdxReg stepBody stepTime bound Inv
        MemWrite ConstRegs hu_lo hu_hi hfwd_hi hfwd_ne hdisj hconst_regs hstep u es (k + 1)
        (Function.update rev v (u :: rev v)) x₂ (by omega)
        (fun q hq => by
          have h := hget (q + 1) (by simp; omega)
          simpa [Nat.add_assoc, Nat.add_comm 1 q] using h)
        (fun z => by simpa [List.foldl_cons] using hroom_all z)
        hy₁_inv hx₂_csr ((hx₂_fr cOne (by decide)).trans hc1) hx₂_fwd
        (hconst_regs _ _ (fun r hr => (hx₂_fr r hr).symm) hconst) hx₂_u
        (by dsimp only [x₂]; wram_simp) hx₂_of
    have hbody_ex : ExecWithin w (forEachArcInner fwdEdgeReg stepBody) x x₂ (stepTime + 3) :=
      (hp1.seq (hy₁_ex.seq hp2)).mono (by omega)
    obtain ⟨t₁, ht₁, he₁⟩ := hbody_ex
    obtain ⟨t₂, ht₂, he₂⟩ := hy_ex
    have hlt : (Cond.lt jReg oldFinReg).Holds x := by
      change x.regs jReg < x.regs oldFinReg; omega
    refine ⟨y, ⟨t₁ + t₂ + 2, by simp only [List.length_cons]; rw [Nat.mul_add, Nat.mul_one]; omega,
        Exec.loop_iter hlt he₁ he₂⟩,
      hy_inv, fun a ha => (hy_out a ha).trans (hy₁_out a ha), fun r h1 h2 h3 h4 => ?_⟩
    rw [hy_fr r h1 h2 h3 h4]
    dsimp only [x₂]
    rw [Data.set_regs_of_ne h4, hy₁_fr r h1 h2]
    dsimp only [st_v]
    rw [Data.set_regs_of_ne h3, Data.set_regs_of_ne h1]

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
    exact ⟨x, ⟨2, by simp [outDegreeSum], Exec.loop_exit hend⟩,
      hinv, fun _ _ => rfl, fun _ _ => rfl⟩
  | u :: us, idx, rev, x, hidx, hus, hroom_all, hinv, hcsr, hc1, hNv, hoff, hfwd, hconst,
      huIdx => by
    simp only [List.length_cons] at hidx
    have hu_val : u.val = idx := by
      have h0 := hus 0 (by simp)
      rwa [List.getElem_cons_zero, Nat.add_zero] at h0
    have hoff_u : x.mem (kOffAddr wb + idx) = csrOffset adj u.val := by
      rw [← hu_val]; exact hcsr.1 u.val (by omega)
    have hoff_u1 : x.mem (kOffAddr wb + idx + 1) = csrOffset adj u.val + (adj u).length := by
      simpa [← hu_val, Nat.add_assoc, csrOffset_succ adj u.isLt] using
        hcsr.1 (u.val + 1) (by omega)
    have hf_oa : Fits w (kOffAddr wb + idx) :=
      hfit.of_le (by simp only [kOffAddr, kTopAddr]; omega)
    have hf_oa1 : Fits w (kOffAddr wb + idx + 1) :=
      hfit.of_le (by simp only [kOffAddr, kTopAddr]; omega)
    have hf_i1 : Fits w (idx + 1) := hfit.of_le (by simp only [kTopAddr]; omega)
    let x₁ := (((x.set addr (kOffAddr wb + idx)).set jReg (csrOffset adj u.val)).set
      addr (kOffAddr wb + idx + 1)).set oldFinReg (csrOffset adj u.val + (adj u).length)
    have hp1 : ExecWithin (B := .standard) w
        (ram[ addr ← offB + uIdxReg; jReg ← *addr; addr ← addr + cOne; oldFinReg ← *addr ])
        x x₁ 4 := by
      let d₁ := x.set addr (kOffAddr wb + idx)
      let d₂ := d₁.set jReg (csrOffset adj u.val)
      let d₃ := d₂.set addr (kOffAddr wb + idx + 1)
      have h_u1 : uIdxReg ≠ addr := Fin.ne_of_val_ne (by change uIdxReg.val ≠ 27; omega)
      have he1 : Exec (B := .standard) w (ram[ addr ← offB + uIdxReg ]) x d₁ 1 := by
        have h : Exec (B := .standard) w (ram[ addr ← offB + uIdxReg ]) x _ 1 :=
          Exec.bin (by change Fits w (x.regs offB + x.regs uIdxReg); rw [hoff, huIdx]; exact hf_oa)
        simpa [d₁, BinOp.eval, hoff, huIdx] using h
      have he2 : Exec (B := .standard) w (ram[ jReg ← *addr ]) d₁ d₂ 1 := by
        have h := Exec.load (B := .standard) (w := w) (x := d₁) (d := jReg) (a := addr)
        simpa [d₂, d₁, Data.set_regs_self, Data.set_mem, hoff_u] using h
      have he3 : Exec (B := .standard) w (ram[ addr ← addr + cOne ]) d₂ d₃ 1 := by
        have hc1_2 : d₂.regs cOne = 1 := by
          dsimp only [d₂, d₁]
          rw [Data.set_regs_of_ne (by reg_ne), Data.set_regs_of_ne (by reg_ne), hc1]
        have ha_2 : d₂.regs addr = kOffAddr wb + idx := by
          dsimp only [d₂, d₁]; rw [Data.set_regs_of_ne (by reg_ne), Data.set_regs_self]
        have h : Exec (B := .standard) w (ram[ addr ← addr + cOne ]) d₂ _ 1 :=
          Exec.bin (by change Fits w (d₂.regs addr + d₂.regs cOne); rw [ha_2, hc1_2]; exact hf_oa1)
        simpa [d₃, BinOp.eval, ha_2, show d₂.regs 1 = 1 from hc1_2] using h
      have he4 : Exec (B := .standard) w (ram[ oldFinReg ← *addr ]) d₃ x₁ 1 := by
        have h := Exec.load (B := .standard) (w := w) (x := d₃) (d := oldFinReg) (a := addr)
        simpa [x₁, d₃, d₂, d₁, Data.set_regs_self, Data.set_mem, hoff_u1] using h
      exact ⟨4, le_rfl, he1.seq (he2.seq (he3.seq he4))⟩
    have hx₁_fr : ∀ r : Fin 28, r.val < 18 → x₁.regs r = x.regs r := fun r hr => by
      dsimp only [x₁]
      simp [Data.set_regs_of_ne (by reg_ne : r ≠ oldFinReg),
        Data.set_regs_of_ne (by reg_ne : r ≠ addr), Data.set_regs_of_ne (by reg_ne : r ≠ jReg)]
    have hx₁_fwd : x₁.regs fwdEdgeReg = kEdgeAddr wb N := by
      dsimp only [x₁]
      have h2 : fwdEdgeReg ≠ addr := Fin.ne_of_val_ne (by change fwdEdgeReg.val ≠ 27; omega)
      have h3 : fwdEdgeReg ≠ jReg := Fin.ne_of_val_ne (by change fwdEdgeReg.val ≠ 25; omega)
      rw [Data.set_regs_of_ne hfwd_ne_of, Data.set_regs_of_ne h2, Data.set_regs_of_ne h3,
        Data.set_regs_of_ne h2, hfwd]
    have hx₁_u : x₁.regs uIdxReg = u.val := by
      dsimp only [x₁]
      have h2 : uIdxReg ≠ addr := Fin.ne_of_val_ne (by change uIdxReg.val ≠ 27; omega)
      have h3 : uIdxReg ≠ jReg := Fin.ne_of_val_ne (by change uIdxReg.val ≠ 25; omega)
      rw [Data.set_regs_of_ne hu_ne_of, Data.set_regs_of_ne h2, Data.set_regs_of_ne h3,
        Data.set_regs_of_ne h2, huIdx, hu_val]
    have hroom_u : ∀ z : Fin N,
        ((adj u).foldl (fun r v => Function.update r v (u :: r v)) rev z).length ≤ bound z := by
      intro z
      have hle : ((adj u).foldl (fun r v => Function.update r v (u :: r v)) rev z).length ≤
          (us.foldl (fun r u' => (adj u').foldl (fun r v => Function.update r v (u' :: r v)) r)
            ((adj u).foldl (fun r v => Function.update r v (u :: r v)) rev) z).length :=
        length_foldl_vs_rev_le adj us _ z
      exact hle.trans (by simpa [List.foldl_cons] using hroom_all z)
    obtain ⟨y₁, hy₁_ex, hy₁_inv, hy₁_out, hy₁_fr⟩ :=
      forEachArcInner_spec adj wb Mc hmc hfit fwdEdgeReg uIdxReg stepBody stepTime bound Inv
        MemWrite ConstRegs hu_lo hu_hi hfwd_hi hfwd_ne hdisj hconst_regs hstep u (adj u) 0 rev x₁
        (by simp) (fun q _ => by simp) hroom_u (by dsimp only [x₁]; exact hinv)
        (by dsimp only [x₁]; exact hcsr)
        ((hx₁_fr cOne (by decide)).trans hc1) hx₁_fwd
        (hconst_regs _ _ (fun r hr => (hx₁_fr r hr).symm) hconst) hx₁_u
        (by dsimp only [x₁]; wram_simp) (by dsimp only [x₁]; wram_simp)
    have hy₁_u : y₁.regs uIdxReg = idx := by
      have h1 : uIdxReg ≠ addr := Fin.ne_of_val_ne (by change uIdxReg.val ≠ 27; omega)
      have h2 : uIdxReg ≠ jEndReg := Fin.ne_of_val_ne (by change uIdxReg.val ≠ 26; omega)
      have h3 : uIdxReg ≠ vReg := Fin.ne_of_val_ne (by change uIdxReg.val ≠ 24; omega)
      have h4 : uIdxReg ≠ jReg := Fin.ne_of_val_ne (by change uIdxReg.val ≠ 25; omega)
      rw [hy₁_fr uIdxReg h1 h2 h3 h4, hx₁_u, hu_val]
    have hy₁_1 : y₁.regs cOne = 1 :=
      (hy₁_fr cOne (by decide) (by decide) (by decide) (by decide)).trans
        ((hx₁_fr cOne (by decide)).trans hc1)
    let x₂ := y₁.set uIdxReg (idx + 1)
    have hp2 : ExecWithin (B := .standard) w (ram[ uIdxReg ← uIdxReg + cOne ]) y₁ x₂ 1 := by
      have h : Exec (B := .standard) w (ram[ uIdxReg ← uIdxReg + cOne ]) y₁ _ 1 :=
        Exec.bin (by change Fits w (y₁.regs uIdxReg + y₁.regs cOne); rw [hy₁_u, hy₁_1]; exact hf_i1)
      exact ⟨1, le_rfl, by simpa [x₂, BinOp.eval, hy₁_u, show y₁.regs 1 = 1 from hy₁_1] using h⟩
    have hx₂_csr : CSRAt adj (kOffAddr wb) (kEdgeAddr wb N) x₂.mem :=
      hcsr.of_eqOn
        (fun i hi => by
          by_contra hne
          have hmem : MemWrite (kOffAddr wb + i) := by
            by_contra hnw; exact hne (hy₁_out _ hnw)
          exact hdisj _ hmem (.inl ⟨by omega, by omega⟩))
        (fun e he => by
          by_contra hne
          have hmem : MemWrite (kEdgeAddr wb N + e) := by
            by_contra hnw; exact hne (hy₁_out _ hnw)
          exact hdisj _ hmem (.inr ⟨by omega, by omega⟩))
    have hx₂_fr0 : ∀ r : Fin 28, r.val < 18 → x₂.regs r = x.regs r := fun r hr => by
      have hne_u : r ≠ uIdxReg := Fin.ne_of_val_ne (by omega)
      dsimp only [x₂]
      rw [Data.set_regs_of_ne hne_u, hy₁_fr r (by reg_ne) (by reg_ne) (by reg_ne) (by reg_ne),
        hx₁_fr r hr]
    have hx₂_fwd : x₂.regs fwdEdgeReg = kEdgeAddr wb N := by
      have h1 : fwdEdgeReg ≠ addr := Fin.ne_of_val_ne (by change fwdEdgeReg.val ≠ 27; omega)
      have h2 : fwdEdgeReg ≠ jEndReg := Fin.ne_of_val_ne (by change fwdEdgeReg.val ≠ 26; omega)
      have h3 : fwdEdgeReg ≠ vReg := Fin.ne_of_val_ne (by change fwdEdgeReg.val ≠ 24; omega)
      have h4 : fwdEdgeReg ≠ jReg := Fin.ne_of_val_ne (by change fwdEdgeReg.val ≠ 25; omega)
      dsimp only [x₂]
      rw [Data.set_regs_of_ne hfwd_ne, hy₁_fr fwdEdgeReg h1 h2 h3 h4, hx₁_fwd]
    obtain ⟨y, hy_ex, hy_inv, hy_out, hy_fr⟩ :=
      forEachArc_spec adj wb Mc hmc hfit fwdEdgeReg uIdxReg stepBody stepTime bound Inv MemWrite
        ConstRegs hu_lo hu_hi hu_ne_of hfwd_hi hfwd_ne_of hfwd_ne hdisj hconst_regs hstep
        us (idx + 1) ((adj u).foldl (fun r v => Function.update r v (u :: r v)) rev) x₂ (by omega)
        (fun q hq => by
          have h := hus (q + 1) (by simp; omega)
          simpa [Nat.add_assoc, Nat.add_comm 1 q] using h)
        (fun z => by simpa [List.foldl_cons] using hroom_all z)
        hy₁_inv hx₂_csr ((hx₂_fr0 cOne (by decide)).trans hc1)
        ((hx₂_fr0 nVerts (by decide)).trans hNv) ((hx₂_fr0 offB (by decide)).trans hoff)
        hx₂_fwd (hconst_regs _ _ (fun r hr => (hx₂_fr0 r hr).symm) hconst)
        (by dsimp only [x₂]; wram_simp)
    have hbody_ex : ExecWithin w
        ((ram[ addr ← offB + uIdxReg; jReg ← *addr; addr ← addr + cOne; oldFinReg ← *addr ]).seq
          ((Code.loop (.lt jReg oldFinReg) (forEachArcInner fwdEdgeReg stepBody)).seq
            (ram[ uIdxReg ← uIdxReg + cOne ])))
        x x₂ (9 + (stepTime + 5) * (adj u).length - 2) := by
      have := (hp1.seq (hy₁_ex.seq hp2)).mono
        (show 4 + ((stepTime + 5) * (adj u).length + 2 + 1) ≤
          9 + (stepTime + 5) * (adj u).length - 2 by omega)
      exact this
    obtain ⟨t₁, ht₁, he₁⟩ := hbody_ex
    obtain ⟨t₂, ht₂, he₂⟩ := hy_ex
    have hlt : (Cond.lt uIdxReg nVerts).Holds x := by
      change x.regs uIdxReg < x.regs nVerts; omega
    refine ⟨y, ⟨t₁ + t₂ + 2, ?_, Exec.loop_iter hlt he₁ he₂⟩,
      hy_inv, fun a ha => (hy_out a ha).trans (hy₁_out a ha),
      fun r hr => (hy_fr r hr).trans (hx₂_fr0 r hr)⟩
    simp only [List.length_cons, outDegreeSum, List.map_cons, List.sum_cons,
      Nat.mul_add, Nat.mul_one] at ht₂ ⊢
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
  have hfit_cur : Fits w (kCurAddr wb N Mc + N) :=
    hfit.of_le (by simp only [kCurAddr, kTopAddr]; omega)
  obtain ⟨x₁, hx₁_ex, hx₁_zero, hx₁_out, hx₁_fr⟩ :=
    zeroBlockCode_spec curB (by decide) (kCurAddr wb N Mc) N hfit_cur hc0 hc1 hcur hNv
  have hx₁_csr : CSRAt adj (kOffAddr wb) (kEdgeAddr wb N) x₁.mem :=
    hcsr.of_eqOn
      (fun _ _ => hx₁_out _ (by dsimp only [kOffAddr, kCurAddr]; omega))
      (fun _ _ => hx₁_out _ (by dsimp only [kEdgeAddr, kCurAddr]; omega))
  let x₂ := x₁.set iReg 0
  have hp1 : ExecWithin (B := .standard) w (ram[ iReg ← cZero ]) x₁ x₂ 1 := by
    have h0' : x₁.regs cZero = 0 := (hx₁_fr cZero (by decide)).trans hc0
    wram_exec [h0']
  have hroom_rev : ∀ z : Fin N, (revAdj z).length ≤ Mc := by
    intro z
    have h1 := csrOffset_succ revAdj z.isLt; simp only [Fin.eta] at h1
    have h2 := csrOffset_mono revAdj (by omega : z.val + 1 ≤ N); omega
  have hf_cur : Fits w (kCurAddr wb N Mc + N + Mc + 1) :=
    hfit.of_le (by simp only [kCurAddr, kTopAddr]; omega)
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
      (fun z => hroom_rev z) (fun z => by dsimp only [x₂]; exact hx₁_zero z.val z.isLt)
      hx₁_csr (by dsimp only [x₂]; wram_simp; exact (hx₁_fr cOne (by decide)).trans hc1)
      (by dsimp only [x₂]; wram_simp; exact (hx₁_fr nVerts (by decide)).trans hNv)
      (by dsimp only [x₂]; wram_simp; exact (hx₁_fr offB (by decide)).trans hoff)
      (by dsimp only [x₂]; wram_simp; exact (hx₁_fr edgeB (by decide)).trans hedge)
      (by dsimp only [x₂]; wram_simp; exact (hx₁_fr curB (by decide)).trans hcur)
      (by dsimp only [x₂]; wram_simp)
  have hx₃_fr0 : ∀ r : Fin 28, r.val < 18 → x₃.regs r = x.regs r := fun r hr => by
    have h3 := hx₃_fr r hr
    have hne : r ≠ iReg := by reg_ne
    dsimp only [x₂] at h3
    rw [h3, Data.set_regs_of_ne hne]
    exact hx₁_fr r hr
  let x₄ := (x₃.set compIdxReg (kOffAddr wb)).set offB (kRevOffAddr wb N Mc)
  have hp2 : ExecWithin (B := .standard) w (ram[ compIdxReg ← offB; offB ← revOffB ]) x₃ x₄ 2 := by
    have h_ob : x₃.regs offB = kOffAddr wb := (hx₃_fr0 offB (by decide)).trans hoff
    have h_rob : x₃.regs revOffB = kRevOffAddr wb N Mc := (hx₃_fr0 revOffB (by decide)).trans hroff
    wram_exec [h_ob, h_rob]
  have hfit_ps : Fits w (kCurAddr wb N Mc + N + Mc + 2) :=
    hfit.of_le (by simp only [kCurAddr, kTopAddr]; omega)
  obtain ⟨x₅, hx₅_ex, hx₅_roff, hx₅_cur, hx₅_out, hx₅_fr⟩ :=
    prefixSumCode_spec revAdj (kCurAddr wb N Mc) (kRevOffAddr wb N Mc) Mc
      (by simp only [kRevOffAddr, kCurAddr]; omega) hmc_rev hfit_ps (x := x₄)
      (by dsimp only [x₄]; wram_simp; exact (hx₃_fr0 cZero (by decide)).trans hc0)
      (by dsimp only [x₄]; wram_simp; exact (hx₃_fr0 cOne (by decide)).trans hc1)
      (by dsimp only [x₄]; wram_simp; exact (hx₃_fr0 curB (by decide)).trans hcur)
      (by dsimp only [x₄]; wram_simp)
      (by dsimp only [x₄]; wram_simp; exact (hx₃_fr0 nVerts (by decide)).trans hNv)
      hx₃_deg
  have hx₅_comp : x₅.regs compIdxReg = kOffAddr wb :=
    (hx₅_ex.regs_eq (by decide)).trans (by dsimp only [x₄]; wram_simp)
  have hx₅_fr0 : ∀ r : Fin 28, r.val < 18 → r ≠ offB → x₅.regs r = x.regs r := fun r hr hno => by
    rw [hx₅_fr r hr]
    dsimp only [x₄]
    have hne_c : r ≠ compIdxReg := by reg_ne
    rw [Data.set_regs_of_ne hno, Data.set_regs_of_ne hne_c]
    exact hx₃_fr0 r hr
  let x₆ := (((x₅.set offB (kOffAddr wb)).set finCnt (kEdgeAddr wb N)).set
    edgeB (kRevEdgeAddr wb N Mc)).set uReg 0
  have hp3 : ExecWithin (B := .standard) w
      (ram[ offB ← compIdxReg; finCnt ← edgeB; edgeB ← revEdgeB; uReg ← cZero ]) x₅ x₆ 4 := by
    have h_eb : x₅.regs edgeB = kEdgeAddr wb N :=
      (hx₅_fr0 edgeB (by decide) (by decide)).trans hedge
    have h_reb : x₅.regs revEdgeB = kRevEdgeAddr wb N Mc :=
      (hx₅_fr0 revEdgeB (by decide) (by decide)).trans hredge
    have h_c0 : x₅.regs cZero = 0 := (hx₅_fr0 cZero (by decide) (by decide)).trans hc0
    wram_exec [hx₅_comp, h_eb, h_reb, h_c0]
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
      hx₅_csr
      (by dsimp only [x₆]; wram_simp; exact (hx₅_fr0 cOne (by decide) (by decide)).trans hc1)
      (by dsimp only [x₆]; wram_simp; exact (hx₅_fr0 nVerts (by decide) (by decide)).trans hNv)
      (by dsimp only [x₆]; wram_simp)
      (by dsimp only [x₆]; wram_simp)
      ⟨by dsimp only [x₆]; wram_simp; exact (hx₅_fr0 curB (by decide) (by decide)).trans hcur,
        by dsimp only [x₆]; wram_simp⟩
      (by dsimp only [x₆]; wram_simp)
  have hx₇_roff : ∀ u ≤ N, x₇.mem (kRevOffAddr wb N Mc + u) = csrOffset revAdj u := fun u hu => by
    rw [hx₇_out _ (by simp only [kRevOffAddr, kCurAddr, kRevEdgeAddr]; omega)]
    exact hx₅_roff u hu
  have hx₇_rcsr : CSRAt revAdj (kRevOffAddr wb N Mc) (kRevEdgeAddr wb N Mc) x₇.mem :=
    csrAt_of_partialCSRAt revAdj (kRevOffAddr wb N Mc) (kCurAddr wb N Mc) (kRevEdgeAddr wb N Mc)
      x₇.mem hx₇_roff hx₇_pcsr
  have hx₇_rob : x₇.regs revOffB = kRevOffAddr wb N Mc := by
    rw [hx₇_fr revOffB (by decide)]
    dsimp only [x₆]; wram_simp
    exact (hx₅_fr0 revOffB (by decide) (by decide)).trans hroff
  let y := x₇.set offB (kRevOffAddr wb N Mc)
  have hp4 : ExecWithin (B := .standard) w (ram[ offB ← revOffB ]) x₇ y 1 := by
    wram_exec [hx₇_rob]
  have hout_sum : outDegreeSum adj (List.finRange N) = csrOffset adj N :=
    (csrOffset_eq_outDegreeSum adj).symm
  rw [List.length_finRange, hout_sum] at hx₃_ex hx₇_ex
  refine ⟨y,
    (hx₁_ex.seq (hp1.seq (hx₃_ex.seq (hp2.seq (hx₅_ex.seq (hp3.seq (hx₇_ex.seq hp4))))))).mono
      (by omega),
    hx₇_rcsr,
    by dsimp only [y]; wram_simp,
    by
      dsimp only [y]; wram_simp
      rw [hx₇_fr edgeB (by decide)]; dsimp only [x₆]; wram_simp,
    fun a ha => ?_,
    fun r hr hno hne => ?_⟩
  · dsimp only [y]; mem_upd
    rw [hx₇_out _ (by dsimp only [revAdj, revGraph] at *; omega)]
    dsimp only [x₆]; mem_upd
    rw [hx₅_out _ (by omega)]
    dsimp only [x₄]; mem_upd
    rw [hx₃_out _ (by omega)]
    dsimp only [x₂]; mem_upd
    exact hx₁_out _ (by omega)
  · dsimp only [y]
    rw [Data.set_regs_of_ne hno, hx₇_fr r hr]
    dsimp only [x₆]
    have hne_u : r ≠ uReg := by reg_ne
    have hne_fc : r ≠ finCnt := by reg_ne
    rw [Data.set_regs_of_ne hne_u, Data.set_regs_of_ne hne, Data.set_regs_of_ne hne_fc,
      Data.set_regs_of_ne hno]
    exact hx₅_fr0 r hr hno

end Cslib.Algorithms.WordRAM.DFS
