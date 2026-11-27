/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.VanEmdeBoas.Successor
public import CslibFrontier.DataStructure.VanEmdeBoas.WordRAM.Model
public import CslibFrontier.DataStructure.VanEmdeBoas.WordRAM.Program
import CslibFrontier.Computability.WordRAM.SymbolicExec

/-!
# Native van Emde Boas strict-successor certification

This module certifies the native strict-successor operation (`successorDescent` followed by
`successorUnwind`) in `CslibFrontier.DataStructure.VanEmdeBoas.WordRAM.Program`.

During descent, each recursive cluster or summary call pushes a four-word continuation frame
(`kind`, `payload`, `q`, `t`) into the scratch stack `[stackBase₀, stackBase₀ + 4 * d)`.
Because `Tree.successor` checks the cached maximum before recursing, every recursive descent is
guaranteed to find a key (`found = 1`), and `successorUnwind` pops the pushed frames to
reconstruct the universe key in `out` while restoring `sp = stackBase₀`.

## Main definitions

* `SuccessorEntry`: register invariant at entry to `successorDescent`.
* `UnwindState`: register and memory invariant during `successorUnwind`.

## Main results

* `successor_loop_spec`: `successorDescent; successorUnwind` executes in at most
  `65 * (d + 1) + 4` instructions, computes `tree.successor query`, restores `sp = stackBase₀`,
  preserves `Rep tree base z.mem`, and leaves all memory outside `[stackBase₀, stackBase₀ + 4 * d)`
  unchanged.

## References

* [E. Demaine, *Divide and conquer: van Emde Boas trees*, Lecture 4][Demaine2015VanEmdeBoas]
-/

@[expose] public section

namespace Cslib.DataStructure.VanEmdeBoas.WordRAM

open Cslib.WordRAM
open Cslib.DataStructure.VanEmdeBoas

/-- The constant, stack, and traversal registers at entry to `successorDescent`. -/
structure SuccessorEntry (stackBase₀ sp₀ base query : ℕ) (s : Data 32) : Prop where
  zero_eq : s.regs zero = 0
  one_eq : s.regs one = 1
  two_eq : s.regs two = 2
  three_eq : s.regs three = 3
  four_eq : s.regs four = 4
  five_eq : s.regs five = 5
  stackBase_eq : s.regs stackBase = stackBase₀
  sp_eq : s.regs sp = sp₀
  p_eq : s.regs p = base
  x_eq : s.regs x = query
  runFlag_eq : s.regs runFlag = 1

/-- Transfer `SuccessorEntry` across register updates once `sp`, `p`, `x`, and `runFlag` are
checked and `zero..five` and `stackBase` are preserved. -/
private theorem SuccessorEntry.of_regs {stackBase₀ sp₀ base query sp' base' query' : ℕ}
    {s s' : Data 32} (hs : SuccessorEntry stackBase₀ sp₀ base query s)
    (h0 : s'.regs zero = s.regs zero) (h1 : s'.regs one = s.regs one)
    (h2 : s'.regs two = s.regs two) (h3 : s'.regs three = s.regs three)
    (h4 : s'.regs four = s.regs four) (h5 : s'.regs five = s.regs five)
    (hsb : s'.regs stackBase = s.regs stackBase)
    (hsp : s'.regs sp = sp') (hp : s'.regs p = base') (hx : s'.regs x = query')
    (hrun : s'.regs runFlag = 1) :
    SuccessorEntry stackBase₀ sp' base' query' s' :=
  ⟨h0.trans hs.zero_eq, h1.trans hs.one_eq, h2.trans hs.two_eq,
    h3.trans hs.three_eq, h4.trans hs.four_eq, h5.trans hs.five_eq,
    hsb.trans hs.stackBase_eq, hsp, hp, hx, hrun⟩

/-- Register and memory invariant at the start of an unwind stage at stack pointer `sp₀`. -/
structure UnwindState (stackBase₀ sp₀ ans : ℕ) (mem : ℕ → ℕ) (s : Data 32) : Prop where
  zero_eq : s.regs zero = 0
  one_eq : s.regs one = 1
  five_eq : s.regs five = 5
  stackBase_eq : s.regs stackBase = stackBase₀
  sp_eq : s.regs sp = sp₀
  found_eq : s.regs found = 1
  out_eq : s.regs out = ans
  mem_eq : s.mem = mem

/-- Transfer `UnwindState` across register updates once `sp`, `out`, and `mem` are checked and
`zero`, `one`, `five`, `stackBase`, and `found` are preserved. -/
private theorem UnwindState.of_regs {stackBase₀ sp₀ ans sp' ans' : ℕ} {mem : ℕ → ℕ}
    {s s' : Data 32} (hs : UnwindState stackBase₀ sp₀ ans mem s)
    (h0 : s'.regs zero = s.regs zero) (h1 : s'.regs one = s.regs one)
    (h5 : s'.regs five = s.regs five) (hsb : s'.regs stackBase = s.regs stackBase)
    (hsp : s'.regs sp = sp') (hfound : s'.regs found = s.regs found)
    (hout : s'.regs out = ans') (hmem : s'.mem = s.mem) :
    UnwindState stackBase₀ sp' ans' mem s' :=
  ⟨h0.trans hs.zero_eq, h1.trans hs.one_eq, h5.trans hs.five_eq,
    hsb.trans hs.stackBase_eq, hsp, hfound.trans hs.found_eq, hout, hmem.trans hs.mem_eq⟩

/-- One cluster-return unwind step (`kind = 0`) executes in at most 19 instructions and reconstructs
`pay + childAns` in `out` at stack pointer `sp₀`. -/
private theorem successorUnwindBody_cluster_spec {w stackBase₀ sp₀ pay childAns : ℕ}
    {mem : ℕ → ℕ} {s : Data 32}
    (hs : UnwindState stackBase₀ (sp₀ + 4) childAns mem s)
    (hk : mem sp₀ = 0) (hpay : mem (sp₀ + 1) = pay)
    (hsp : Fits w (sp₀ + 4)) (hout : Fits w (pay + childAns)) :
    ∃ s', ExecWithin w successorUnwindBody s s' 19 ∧
      UnwindState stackBase₀ sp₀ (pay + childAns) mem s' := by
  obtain ⟨hz, ho, hfive, hsb, hsp_eq, hfound, hout_eq, hmem⟩ := hs
  apply WP.exists_execWithin
  unfold successorUnwindBody popFrame
  wram_exec [hz, ho, hfive, hsp_eq, hout_eq, hmem, hk, hpay, Nat.add_sub_assoc, Nat.add_zero]
  exact UnwindState.of_regs ⟨hz, ho, hfive, hsb, hsp_eq, hfound, hout_eq, hmem⟩
    (by wram_simp) (by wram_simp) (by wram_simp) (by wram_simp)
    (by wram_simp) (by wram_simp) (by wram_simp) (by wram_simp)

/-- One summary-return unwind step (`kind = 1`) executes in at most 19 instructions and reconstructs
`j * universeSize d + cm` in `out` at stack pointer `sp₀`. -/
private theorem successorUnwindBody_summary_spec {d w stackBase₀ sp₀ base j cm : ℕ}
    {mem : ℕ → ℕ} {s : Data 32}
    (hs : UnwindState stackBase₀ (sp₀ + 4) j mem s)
    (hk : mem sp₀ = 1) (hpay : mem (sp₀ + 1) = base)
    (hqv : mem (sp₀ + 2) = universeSize d) (htv : mem (sp₀ + 3) = span d)
    (hj : j < universeSize d)
    (hcm : mem (base + 5 + (j + 1) * span d + 1) = cm) (hcm_lt : cm < universeSize d)
    (ha : Fits w (base + span (d + 1))) (hsp : Fits w (sp₀ + 4)) :
    ∃ s', ExecWithin w successorUnwindBody s s' 19 ∧
      UnwindState stackBase₀ sp₀ (j * universeSize d + cm) mem s' := by
  obtain ⟨hz, ho, hfive, hsb, hsp_eq, hfound, hout_eq, hmem⟩ := hs
  have hend := cluster_end_le_span d hj
  dsimp only [clusterOffset] at hend
  have hj1 : Fits w (j + 1) :=
    ha.of_le (by have := (universeSize_le_span d).trans (span_le_succ d); omega)
  have hch1 : Fits w (base + 5 + (j + 1) * span d + 1) :=
    ha.of_le (by have := five_le_span d; omega)
  have hmul_lt : j * universeSize d + cm < universeSize (d + 1) := by
    rw [universeSize_succ]
    have h := Nat.mul_le_mul_right (universeSize d) (show j + 1 ≤ universeSize d by omega)
    rw [Nat.succ_mul] at h
    omega
  have hu1_le : universeSize (d + 1) ≤ span (d + 1) := universeSize_le_span (d + 1)
  have hans : Fits w (j * universeSize d + cm) := ha.of_le (by omega)
  apply WP.exists_execWithin
  unfold successorUnwindBody popFrame readAt
  wram_exec [hz, ho, hfive, hsp_eq, hout_eq, hmem, hk, hpay, hqv, htv, hcm,
    Nat.add_sub_assoc, Nat.add_zero]
  exact UnwindState.of_regs ⟨hz, ho, hfive, hsb, hsp_eq, hfound, hout_eq, hmem⟩
    (by wram_simp) (by wram_simp) (by wram_simp) (by wram_simp)
    (by wram_simp) (by wram_simp) (by wram_simp) (by wram_simp)

/-- Four consecutive memory updates at `sp₀ .. sp₀ + 3` leave every address outside
`[sp₀, sp₀ + 4)` unchanged. -/
private theorem update4_away (m : ℕ → ℕ) (sp₀ v₀ v₁ v₂ v₃ a : ℕ)
    (ha : a < sp₀ ∨ sp₀ + 4 ≤ a) :
    Function.update
      (Function.update
        (Function.update (Function.update m sp₀ v₀) (sp₀ + 1) v₁)
        (sp₀ + 2) v₂)
      (sp₀ + 3) v₃ a = m a := by
  rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
    Function.update_of_ne (by omega), Function.update_of_ne (by omega)]

/-- One frame-pushing descent step: a `successorDescentBody` step to `next` that pushes `(k, pay,
qv, tv)` at `sp₀` and enters child `child` at `(P, X)` combines with the child's recursive
descent/unwind certificate `hrec` and the single-frame pop `hclose` into the certificate at `sp₀`.
-/
private theorem successor_push_step
    {d w stackBase₀ sp₀ base query ans childAns P X k pay qv tv : ℕ}
    {child : Tree d} {s : Data 32} (hs : SuccessorEntry stackBase₀ sp₀ base query s)
    (hsp_le : stackBase₀ ≤ sp₀) (hdisj : base + span (d + 1) ≤ sp₀)
    (hfit : Fits w (sp₀ + 4 * (d + 1)))
    (hstep : ∃ next, ExecWithin w successorDescentBody s next 42 ∧
      SuccessorEntry stackBase₀ (sp₀ + 4) P X next ∧
      (next.mem sp₀ = k ∧ next.mem (sp₀ + 1) = pay ∧
        next.mem (sp₀ + 2) = qv ∧ next.mem (sp₀ + 3) = tv) ∧
      (∀ a, a < sp₀ ∨ sp₀ + 4 ≤ a → next.mem a = s.mem a))
    (hrc : Rep child P s.mem) (hend : P + span d ≤ base + span (d + 1))
    (hrec : ∀ {next : Data 32},
      SuccessorEntry stackBase₀ (sp₀ + 4) P X next →
      Rep child P next.mem → stackBase₀ ≤ sp₀ + 4 →
      P + span d ≤ sp₀ + 4 → Fits w (sp₀ + 4 + 4 * d) →
      ∃ s₁ s₂, ExecWithin w successorDescent next s₁ (44 * (d + 1) + 2) ∧
        (∀ a, a < sp₀ + 4 ∨ sp₀ + 4 + 4 * d ≤ a → s₁.mem a = next.mem a) ∧
        UnwindState stackBase₀ (sp₀ + 4) childAns s₁.mem s₂ ∧
        ∀ z T, ExecWithin w successorUnwind s₂ z T →
          ExecWithin w successorUnwind s₁ z (21 * d + T))
    (hclose : ∀ s₁ s₂ : Data 32, UnwindState stackBase₀ (sp₀ + 4) childAns s₁.mem s₂ →
      s₁.mem sp₀ = k → s₁.mem (sp₀ + 1) = pay → s₁.mem (sp₀ + 2) = qv →
      s₁.mem (sp₀ + 3) = tv → (∀ a < sp₀, s₁.mem a = s.mem a) →
      ∃ s₃, ExecWithin w successorUnwindBody s₂ s₃ 19 ∧
        UnwindState stackBase₀ sp₀ ans s₁.mem s₃) :
    ∃ s₁ s₃, ExecWithin w successorDescent s s₁ (44 * (d + 1 + 1) + 2) ∧
      (∀ a, a < sp₀ ∨ sp₀ + 4 * (d + 1) ≤ a → s₁.mem a = s.mem a) ∧
      UnwindState stackBase₀ sp₀ ans s₁.mem s₃ ∧
      ∀ z T, ExecWithin w successorUnwind s₃ z T →
        ExecWithin w successorUnwind s₁ z (21 * (d + 1) + T) := by
  obtain ⟨next, he, hentry, ⟨hw0, hw1, hw2, hw3⟩, hnext_away⟩ := hstep
  have hrc_next : Rep child P next.mem :=
    rep_frame hrc fun a _ _ => hnext_away a (Or.inl (by omega))
  have hfit' : Fits w (sp₀ + 4 + 4 * d) := by
    simpa only [Nat.mul_succ, ← Nat.add_assoc, Nat.add_right_comm sp₀ (4 * d) 4] using hfit
  obtain ⟨s₁, s₂, hs₁, hframe₁, hs₂, hunwind₁⟩ :=
    hrec hentry hrc_next (by omega) (by omega) hfit'
  have hframe_sp : ∀ a < sp₀ + 4, s₁.mem a = next.mem a := fun a ha' => hframe₁ a (Or.inl ha')
  obtain ⟨s₃, hbody, hs₃⟩ := hclose s₁ s₂ hs₂
    ((hframe_sp _ (by omega)).trans hw0)
    ((hframe_sp _ (by omega)).trans hw1)
    ((hframe_sp _ (by omega)).trans hw2)
    ((hframe_sp _ (by omega)).trans hw3)
    (fun a ha' => (hframe_sp a (by omega)).trans (hnext_away a (Or.inl ha')))
  refine ⟨s₁, s₃, (he.loop_iter (cond := .lt zero runFlag) ?_ hs₁).mono (by omega), ?_, hs₃, ?_⟩
  · simp only [Cond.holds_lt, hs.zero_eq, hs.runFlag_eq]
    decide
  · intro a ha'
    by_cases ha4 : a < sp₀
    · exact (hframe₁ a (Or.inl (by omega))).trans (hnext_away a (Or.inl ha4))
    · exact (hframe₁ a (Or.inr (by omega))).trans (hnext_away a (Or.inr (by omega)))
  · intro z T hcont
    have hiter : ExecWithin w successorUnwind s₂ z (21 + T) := by
      refine (hbody.loop_iter (cond := .lt stackBase sp) ?_ hcont).mono (by omega)
      simp only [Cond.holds_lt, hs₂.stackBase_eq, hs₂.sp_eq]
      omega
    exact (hunwind₁ z (21 + T) hiter).mono (by omega)

/-- Terminate `successorDescent` in one body pass when `successorDescentBody` clears `runFlag`
without pushing any stack frames. -/
private theorem successor_some_finish {d w stackBase₀ sp₀ base query ans : ℕ} {s : Data 32}
    (hs : SuccessorEntry stackBase₀ sp₀ base query s)
    (hstep : ∃ s₁, ExecWithin w successorDescentBody s s₁ 42 ∧
      s₁.regs runFlag = 0 ∧ UnwindState stackBase₀ sp₀ ans s.mem s₁) :
    ∃ s₁ s₃, ExecWithin w successorDescent s s₁ (44 * (d + 1) + 2) ∧
      (∀ a, a < sp₀ ∨ sp₀ + 4 * d ≤ a → s₁.mem a = s.mem a) ∧
      UnwindState stackBase₀ sp₀ ans s₁.mem s₃ ∧
      ∀ z T, ExecWithin w successorUnwind s₃ z T →
        ExecWithin w successorUnwind s₁ z (21 * d + T) := by
  obtain ⟨s₁, he, hk, hu⟩ := hstep
  refine ⟨s₁, s₁, (he.loop_once (cond := .lt zero runFlag) ?_ ?_).mono (by omega),
    fun a _ => by rw [hu.mem_eq], hu.mem_eq ▸ hu, fun z T hcont => hcont.mono (by omega)⟩
  · simp only [Cond.holds_lt, hs.zero_eq, hs.runFlag_eq]
    decide
  · simp only [Cond.holds_lt, hu.zero_eq, hk, lt_self_iff_false, not_false_eq_true]

/-- Combined inductive certification of `successorDescent` and CPS `successorUnwind` whenever
`tree.successor query = some ans`. -/
private theorem successor_some_spec {d w stackBase₀ sp₀ base query ans : ℕ} {tree : Tree d}
    {s : Data 32} (hs : SuccessorEntry stackBase₀ sp₀ base query s) (ht : tree.Valid)
    (hr : Rep tree base s.mem) (hans : tree.successor query = some ans)
    (hsp_le : stackBase₀ ≤ sp₀) (hdisj : base + span d ≤ sp₀) (hfit : Fits w (sp₀ + 4 * d)) :
    ∃ s₁ s₃, ExecWithin w successorDescent s s₁ (44 * (d + 1) + 2) ∧
      (∀ a, a < sp₀ ∨ sp₀ + 4 * d ≤ a → s₁.mem a = s.mem a) ∧
      UnwindState stackBase₀ sp₀ ans s₁.mem s₃ ∧
      ∀ z T, ExecWithin w successorUnwind s₃ z T →
        ExecWithin w successorUnwind s₁ z (21 * d + T) := by
  have ha : Fits w (base + span d) := hfit.of_le (by omega)
  have hbase4 : Fits w (base + 4) := ha.of_le (by have := five_le_span d; omega)
  have hz := hs.zero_eq; have ho := hs.one_eq; have htwo := hs.two_eq
  have hthree := hs.three_eq; have hfour := hs.four_eq; have hfive := hs.five_eq
  have hsb := hs.stackBase_eq; have hsp_eq := hs.sp_eq; have hp := hs.p_eq
  have hx := hs.x_eq; have hrun := hs.runFlag_eq
  have hheader := hr.header
  rcases hb : tree.bounds with _ | ⟨m, M⟩ <;> rw [hb] at hheader
  · exfalso
    cases tree <;> simp_all [Tree.bounds, Tree.successor]
  obtain ⟨hpres_raw, ⟨hm, hM⟩, hq, hspan⟩ := hheader
  have hpres : s.mem base = 1 := hpres_raw
  by_cases hlt_m : query < m
  · have hans_eq : ans = m := by
      cases tree <;> simp_all [Tree.bounds, Tree.successor]
    apply successor_some_finish hs
    apply WP.exists_execWithin
    unfold successorDescentBody readAt finishMin
    wram_exec [hz, ho, hp, hx, hpres, hm, hlt_m]
    exact ⟨by wram_simp, ⟨by wram_simp [hz], by wram_simp [ho], by wram_simp [hfive],
      by wram_simp [hsb], by wram_simp [hsp_eq], by wram_simp,
      by wram_simp [hans_eq], by wram_simp⟩⟩
  cases tree with
  | leaf b =>
    obtain rfl : b = some (m, M) := hb
    have hlt_M : query < M := by
      by_contra hge
      simp [Tree.successor, hlt_m, hge] at hans
    have hans_eq : ans = M := by
      simpa [Tree.successor, hlt_m, hlt_M] using hans.symm
    apply successor_some_finish hs
    apply WP.exists_execWithin
    unfold successorDescentBody readAt finishMax
    wram_exec [hz, ho, htwo, hthree, hp, hx, hpres, hm, hM, hq, splitSize, hlt_m, hlt_M]
    exact ⟨by wram_simp, ⟨by wram_simp [hz], by wram_simp [ho], by wram_simp [hfive],
      by wram_simp [hsb], by wram_simp [hsp_eq], by wram_simp,
      by wram_simp [hans_eq], by wram_simp⟩⟩
  | @node d b summary cluster =>
    obtain rfl : b = some (m, M) := hb
    have hlt_M : query < M := by
      by_contra hge
      have hle : M ≤ query := Nat.le_of_not_lt hge
      simp [Tree.successor, hlt_m, hle] at hans
    have hnot_le : ¬M ≤ query := not_le.mpr hlt_M
    obtain ⟨hi, hlo, hend⟩ := member_descent_safe ht hr (by simpa only [hM] using hlt_M)
    have hu_le : universeSize d ≤ span (d + 1) :=
      (universeSize_le_span d).trans (span_le_succ d)
    have hqne : universeSize d ≠ 0 := Nat.ne_of_gt (universeSize_pos d)
    have hw_lo : Fits w (query % universeSize d) := ha.of_le (by omega)
    have hw_hi1 : Fits w (query / universeSize d + 1) := ha.of_le (by omega)
    have hw_ch2 : Fits w (base + 5 + (query / universeSize d + 1) * span d + 2) :=
      ha.of_le (by have := five_le_span d; dsimp only [clusterOffset] at hend; omega)
    let i : Fin (universeSize d) := ⟨query / universeSize d, hi⟩
    let lo := query % universeSize d
    let ch := base + clusterOffset d i.val
    have hch_eq : base + 5 + (query / universeSize d + 1) * span d = ch := by
      dsimp only [ch, clusterOffset, i]
      omega
    have summary_branch
        (hc_max : (cluster i).maximum.any (lo < ·) = false)
        (hstep : ∃ next, ExecWithin w successorDescentBody s next 42 ∧
          SuccessorEntry stackBase₀ (sp₀ + 4) (base + 5) i.val next ∧
          (next.mem sp₀ = 1 ∧ next.mem (sp₀ + 1) = base ∧
            next.mem (sp₀ + 2) = universeSize d ∧ next.mem (sp₀ + 3) = span d) ∧
          (∀ a, a < sp₀ ∨ sp₀ + 4 ≤ a → next.mem a = s.mem a)) :
        ∃ s₁ s₃, ExecWithin w successorDescent s s₁ (44 * (d + 1 + 1) + 2) ∧
          (∀ a, a < sp₀ ∨ sp₀ + 4 * (d + 1) ≤ a → s₁.mem a = s.mem a) ∧
          UnwindState stackBase₀ sp₀ ans s₁.mem s₃ ∧
          ∀ z T, ExecWithin w successorUnwind s₃ z T →
            ExecWithin w successorUnwind s₁ z (21 * (d + 1) + T) := by
      have hans' :
          (summary.successor i.val).bind (fun j =>
            if hj : j < universeSize d then
              (cluster ⟨j, hj⟩).minimum.map (j * universeSize d + ·)
            else none) = some ans := by
        simpa only [Tree.successor, hlt_m, hnot_le, hi, ↓reduceDIte, ↓reduceIte,
          i, lo, hc_max, Bool.false_eq_true, bind] using hans
      cases hsuc : summary.successor i.val with
      | none => simp [hsuc] at hans'
      | some j =>
        simp only [hsuc, Option.bind_some] at hans'
        by_cases hj : j < universeSize d
        · simp only [hj, ↓reduceDIte] at hans'
          let k : Fin (universeSize d) := ⟨j, hj⟩
          change (cluster k).minimum.map (j * universeSize d + ·) = some ans at hans'
          cases hck : (cluster k).bounds with
          | none => simp [Tree.minimum, hck] at hans'
          | some cbounds =>
            obtain ⟨cm, cM⟩ := cbounds
            have hans_eq : j * universeSize d + cm = ans := by
              simpa [Tree.minimum, hck] using hans'
            have hce := (ht.2.2.1 k).extrema_of_bounds hck
            have hcm_lt : cm < universeSize d := hce.1.trans_lt hce.2.1
            have hcm_mem : s.mem (base + 5 + (j + 1) * span d + 1) = cm := by
              have hh := (hr.2.2 k).header
              simp only [Header, hck] at hh
              simpa only [clusterOffset, k, Nat.add_assoc] using hh.2.1.1
            have hsum_end := summary_end_le_span d
            dsimp only [summaryOffset] at hsum_end
            refine successor_push_step hs hsp_le hdisj hfit hstep hr.2.1 (by omega)
              (fun hentry' hrc' hsp' hdisj' hfit' =>
                successor_some_spec hentry' ht.2.1 hrc' hsuc hsp' hdisj' hfit') ?_
            intro s₁ s₂ hs₂ hk_mem hpay_mem hqv_mem htv_mem hlow
            have hcm_s₁ : s₁.mem (base + 5 + (j + 1) * span d + 1) = cm := by
              have hend_j := cluster_end_le_span d hj
              have := five_le_span d
              dsimp only [clusterOffset] at hend_j
              rw [hlow _ (by omega), hcm_mem]
            exact hans_eq ▸ successorUnwindBody_summary_spec hs₂ hk_mem hpay_mem hqv_mem htv_mem
              hj hcm_s₁ hcm_lt ha (hfit.of_le (by omega))
        · simp [hj] at hans'
    cases hcb : (cluster i).bounds with
    | none =>
      have hch0 : s.mem (base + 5 + (query / universeSize d + 1) * span d) = 0 := by
        rw [hch_eq]
        simpa only [ch, hcb, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] using
          (hr.2.2 i).header.1
      have hc_max : (cluster i).maximum.any (lo < ·) = false := by simp [Tree.maximum, hcb]
      apply summary_branch hc_max
      apply WP.exists_execWithin
      unfold successorDescentBody readAt coordinates descendSummary pushFrame
      wram_exec [hz, ho, htwo, hthree, hfour, hfive, hsp_eq, hp, hx,
        hpres, hm, hM, hq, hspan, splitSize, childSpan, hlt_m, hlt_M, hqne, hch0]
      refine ⟨hs.of_regs (by wram_simp) (by wram_simp) (by wram_simp) (by wram_simp)
        (by wram_simp) (by wram_simp) (by wram_simp) (by wram_simp) (by wram_simp)
        (by wram_simp [i]) (by wram_simp [hrun]),
        ⟨by wram_simp, by wram_simp, by wram_simp, by wram_simp⟩,
        fun a ha' => ?_⟩
      simpa only [Data.set_mem, Data.write_mem, Nat.add_assoc] using
        update4_away s.mem sp₀ 1 base (universeSize d) (span d) a ha'
    | some cbounds =>
      obtain ⟨cm, cM⟩ := cbounds
      have hch1 : s.mem ch = 1 := by
        simpa only [ch, hcb, Option.isSome_some, ↓reduceIte] using (hr.2.2 i).header.1
      have hch_ne0 : s.mem (base + 5 + (query / universeSize d + 1) * span d) ≠ 0 := by
        rw [hch_eq, hch1]; decide
      have hcM : s.mem (base + 5 + (query / universeSize d + 1) * span d + 2) = cM := by
        rw [hch_eq]
        have hh := (hr.2.2 i).header
        simp only [Header, hcb] at hh
        exact hh.2.1.2
      by_cases hlo_cM : lo < cM
      · have hlo_mx : query % universeSize d < cM := hlo_cM
        have hc_max : (cluster i).maximum.any (lo < ·) = true := by
          simp [Tree.maximum, hcb, hlo_cM]
        have hans' : ((cluster i).successor lo).map (i.val * universeSize d + ·) = some ans := by
          simpa only [Tree.successor, hlt_m, hnot_le, hi, ↓reduceDIte, ↓reduceIte,
            i, lo, hc_max] using hans
        obtain ⟨y, hy_lt, hy_suc⟩ := Tree.successor_isSome_of_lt_max (ht.2.2.1 i) hcb hlo_cM
        have hans_eq : i.val * universeSize d + y = ans := by
          simpa only [hy_suc, Option.map_some, Option.some.injEq] using hans'
        have hw_pay : Fits w (query / universeSize d * universeSize d) := by
          have hle : query / universeSize d * universeSize d ≤ query :=
            Nat.div_mul_le_self query (universeSize d)
          have hM_lt : M < universeSize (d + 1) := (maximum_lt_universe ht hr rfl).2
          have hu1_le : universeSize (d + 1) ≤ span (d + 1) := universeSize_le_span (d + 1)
          exact ha.of_le (by omega)
        have hstep : ∃ next, ExecWithin w successorDescentBody s next 42 ∧
            SuccessorEntry stackBase₀ (sp₀ + 4) ch lo next ∧
            (next.mem sp₀ = 0 ∧ next.mem (sp₀ + 1) = i.val * universeSize d ∧
              next.mem (sp₀ + 2) = universeSize d ∧ next.mem (sp₀ + 3) = span d) ∧
            (∀ a, a < sp₀ ∨ sp₀ + 4 ≤ a → next.mem a = s.mem a) := by
          apply WP.exists_execWithin
          unfold successorDescentBody readAt coordinates descendCluster pushFrame
          wram_exec [hz, ho, htwo, hthree, hfour, hfive, hsp_eq, hp, hx,
            hpres, hm, hM, hq, hspan, splitSize, childSpan, hlt_m, hlt_M, hqne, hch_ne0, hcM,
            hlo_mx]
          refine ⟨hs.of_regs (by wram_simp) (by wram_simp) (by wram_simp) (by wram_simp)
            (by wram_simp) (by wram_simp) (by wram_simp) (by wram_simp)
            (by wram_simp [hch_eq]) (by wram_simp [lo]) (by wram_simp [hrun]),
            ⟨by wram_simp, by wram_simp [i], by wram_simp, by wram_simp⟩,
            fun a ha' => ?_⟩
          simpa only [Data.set_mem, Data.write_mem, Nat.add_assoc] using
            update4_away s.mem sp₀ 0 (query / universeSize d * universeSize d)
              (universeSize d) (span d) a ha'
        refine successor_push_step hs hsp_le hdisj hfit hstep (hr.2.2 i) hend
          (fun hentry' hrc' hsp' hdisj' hfit' =>
            successor_some_spec hentry' (ht.2.2.1 i) hrc' hy_suc hsp' hdisj' hfit') ?_
        intro s₁ s₂ hs₂ hk_mem hpay_mem _ _ _
        have hout_fit : Fits w (i.val * universeSize d + y) := by
          have hmul_lt : i.val * universeSize d + y < universeSize (d + 1) := by
            rw [universeSize_succ]
            have h := Nat.mul_le_mul_right (universeSize d)
              (show i.val + 1 ≤ universeSize d by exact hi)
            rw [Nat.succ_mul] at h
            omega
          have hu1_le := universeSize_le_span (d + 1)
          exact ha.of_le (by omega)
        exact hans_eq ▸ successorUnwindBody_cluster_spec hs₂ hk_mem hpay_mem
          (hfit.of_le (by omega)) hout_fit
      · have hlo_mx : ¬query % universeSize d < cM := hlo_cM
        have hc_max : (cluster i).maximum.any (lo < ·) = false := by
          simp [Tree.maximum, hcb, hlo_cM]
        apply summary_branch hc_max
        apply WP.exists_execWithin
        unfold successorDescentBody readAt coordinates descendSummary pushFrame
        wram_exec [hz, ho, htwo, hthree, hfour, hfive, hsp_eq, hp, hx,
          hpres, hm, hM, hq, hspan, splitSize, childSpan, hlt_m, hlt_M, hqne, hch_ne0, hcM,
          hlo_mx]
        refine ⟨hs.of_regs (by wram_simp) (by wram_simp) (by wram_simp) (by wram_simp)
          (by wram_simp) (by wram_simp) (by wram_simp) (by wram_simp) (by wram_simp)
          (by wram_simp [i]) (by wram_simp [hrun]),
          ⟨by wram_simp, by wram_simp, by wram_simp, by wram_simp⟩,
          fun a ha' => ?_⟩
        simpa only [Data.set_mem, Data.write_mem, Nat.add_assoc] using
          update4_away s.mem sp₀ 1 base (universeSize d) (span d) a ha'

/-- When `tree.successor query = none`, `successorDescent` terminates in one iteration (46
instructions) with `found = 0`, `out = 0`, `sp = sp₀`, and unchanged memory. -/
private theorem successor_none_spec {d w stackBase₀ sp₀ base query : ℕ} {tree : Tree d}
    {s : Data 32} (hs : SuccessorEntry stackBase₀ sp₀ base query s) (ht : tree.Valid)
    (hr : Rep tree base s.mem) (hnone : tree.successor query = none)
    (hdisj : base + span d ≤ sp₀) (hfit : Fits w (sp₀ + 4 * d)) :
    ∃ s₁, ExecWithin w successorDescent s s₁ 46 ∧
      s₁.regs stackBase = stackBase₀ ∧ s₁.regs sp = sp₀ ∧
      s₁.regs found = 0 ∧ s₁.regs out = 0 ∧ s₁.mem = s.mem := by
  have ha : Fits w (base + span d) := hfit.of_le (by omega)
  have hbase4 : Fits w (base + 4) := ha.of_le (by have := five_le_span d; omega)
  have hz := hs.zero_eq; have ho := hs.one_eq; have htwo := hs.two_eq
  have hsb := hs.stackBase_eq; have hsp_eq := hs.sp_eq; have hp := hs.p_eq
  have hx := hs.x_eq; have hrun := hs.runFlag_eq
  have hheader := hr.header
  have hstep : ∃ s₁, ExecWithin w successorDescentBody s s₁ 42 ∧
      s₁.regs zero = 0 ∧ s₁.regs runFlag = 0 ∧ s₁.regs stackBase = stackBase₀ ∧
      s₁.regs sp = sp₀ ∧ s₁.regs found = 0 ∧ s₁.regs out = 0 ∧ s₁.mem = s.mem := by
    apply WP.exists_execWithin
    unfold successorDescentBody readAt finishNone
    rcases hb : tree.bounds with _ | ⟨m, M⟩ <;> rw [hb] at hheader
    · have hempty : s.mem base = 0 := hheader.1
      wram_exec [hz, hp, hempty]
      exact ⟨by wram_simp [hz], by wram_simp, by wram_simp [hsb], by wram_simp [hsp_eq],
        by wram_simp, by wram_simp, by wram_simp⟩
    · obtain ⟨hpres_raw, ⟨hm, hM⟩, _⟩ := hheader
      have hpres : s.mem base = 1 := hpres_raw
      have hnot_M : ¬query < M := by
        intro hlt
        obtain ⟨ans, _, hans⟩ := Tree.successor_isSome_of_lt_max ht hb hlt
        simp [hans] at hnone
      have hnot_m : ¬query < m := by
        have := (ht.extrema_of_bounds hb).1
        omega
      wram_exec [hz, ho, htwo, hp, hx, hpres, hm, hM, hnot_m, hnot_M]
      exact ⟨by wram_simp [hz], by wram_simp, by wram_simp [hsb], by wram_simp [hsp_eq],
        by wram_simp, by wram_simp, by wram_simp⟩
  obtain ⟨s₁, he, hz₁, hk₁, hsb₁, hsp₁, hfound₁, hout₁, hmem₁⟩ := hstep
  refine ⟨s₁, he.loop_once (cond := .lt zero runFlag) ?_ ?_, hsb₁, hsp₁, hfound₁, hout₁, hmem₁⟩
  · simp only [Cond.holds_lt, hz, hrun]
    decide
  · simp only [Cond.holds_lt, hz₁, hk₁, lt_self_iff_false, not_false_eq_true]

/-- Complete certification of `successorDescent; successorUnwind` from `sp = stackBase₀`:
executes in at most `65 * (d + 1) + 4` instructions, computes `tree.successor query`,
restores `sp = stackBase₀`, preserves `Rep tree base z.mem`, and frames memory outside
`[stackBase₀, stackBase₀ + 4 * d)`. -/
theorem successor_loop_spec {d w stackBase₀ base query : ℕ} {tree : Tree d} {s : Data 32}
    (hs : SuccessorEntry stackBase₀ stackBase₀ base query s)
    (ht : tree.Valid) (hr : Rep tree base s.mem)
    (hdisj : base + span d ≤ stackBase₀) (hfit : Fits w (stackBase₀ + 4 * d)) :
    ∃ z, ExecWithin w (ram[ ⟪successorDescent⟫; ⟪successorUnwind⟫ ]) s z (65 * (d + 1) + 4) ∧
      (if z.regs found = 0 then none else some (z.regs out)) = tree.successor query ∧
      z.regs sp = stackBase₀ ∧
      Rep tree base z.mem ∧
      (∀ a, a < stackBase₀ ∨ stackBase₀ + 4 * d ≤ a → z.mem a = s.mem a) := by
  cases hsuc : tree.successor query with
  | none =>
    obtain ⟨s₁, hs₁, hsb₁, hsp₁, hfound₁, _, hmem₁⟩ :=
      successor_none_spec hs ht hr hsuc hdisj hfit
    have hexit : ExecWithin w successorUnwind s₁ s₁ 2 := by
      apply ExecWithin.loop_exit
      simp only [Cond.holds_lt, hsb₁, hsp₁, lt_self_iff_false, not_false_eq_true]
    refine ⟨s₁, (hs₁.seq hexit).mono (by omega), ?_, hsp₁, hmem₁ ▸ hr, fun a _ => by rw [hmem₁]⟩
    simp [hfound₁]
  | some ans =>
    obtain ⟨s₁, z, hs₁, hframe₁, hz, hunwind₁⟩ :=
      successor_some_spec hs ht hr hsuc le_rfl hdisj hfit
    have hexit : ExecWithin w successorUnwind z z 2 := by
      apply ExecWithin.loop_exit
      simp only [Cond.holds_lt, hz.stackBase_eq, hz.sp_eq, lt_self_iff_false, not_false_eq_true]
    have hunwind := hunwind₁ z 2 hexit
    refine ⟨z, (hs₁.seq hunwind).mono (by omega), ?_, hz.sp_eq, ?_, ?_⟩
    · simp [hz.found_eq, hz.out_eq]
    · apply rep_frame hr
      intro a hlo hhi
      rw [hz.mem_eq]
      exact hframe₁ a (Or.inl (by omega))
    · intro a ha
      rw [hz.mem_eq]
      exact hframe₁ a ha

end Cslib.DataStructure.VanEmdeBoas.WordRAM
