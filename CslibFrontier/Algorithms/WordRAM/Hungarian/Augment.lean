/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.Hungarian.MemLayout

/-!
# Augmenting-path application and row-mate scatter (`augmentCode`)

Internal `O(n)` subroutine flipping an augmenting path in `colMate` and rebuilding `rowMate`.
-/

public section

namespace Cslib.Algorithms.WordRAM.Hungarian

open Cslib.WordRAM
open Cslib.Algorithms.Lean.MaxFlow
open Reg

/-- Augmenting-path walk body: rematch column `idx2` to `bestRow[idx2]` and advance to its previous
matched column `rowMate[bestRow[idx2]]`. -/
private def augBody : Code .standard 28 := ram[
  addr ← baseBestRow + idx2; val ← *addr;
  addr ← baseRowMate + val; val2 ← *addr;
  addr ← baseColMate + idx2; *addr ← val;
  idx2 ← val2 ]

/-- Apply augmenting path ending at `rj1` to `colMate`. -/
private def augCode : Code .standard 28 :=
  .seq (ram[ idx2 ← rj1 ]) (.loop (.lt idx2 rn) augBody)

/-- Scatter `colMate` into `rowMate` after clearing `rowMate` to `n`. -/
private def scatterRowMateBody : Code .standard 28 := ram[
  addr ← baseColMate + idx; val ← *addr;
  if val < rn then [ addr ← baseRowMate + val; *addr ← idx ] else [ tmp ← zero ];
  idx ← idx + one ]

/-- Rebuild `rowMate` from `colMate` in `O(n)` instructions. -/
private def rebuildRowMateCode : Code .standard 28 :=
  .seq (fillConst baseRowMate rn)
    (.seq (ram[ idx ← #0 ]) (.loop (.lt idx rn) scatterRowMateBody))

/-- Augment matching along `rj1`'s tree path, rebuild `rowMate`, and set `augmented := 1`. -/
def augmentCode : Code .standard 28 :=
  .seq augCode (.seq rebuildRowMateCode (ram[ augmented ← #1 ]))

private theorem exec_augCode {w n bC M : ℕ} {c : Fin n × Fin n → ℤ} {W : ℕ} {r j₁ : Fin n}
    {s : HgState n} {bestRow : Fin n → Fin n}
    (hSI : HgStepInv c W r s bestRow) (x : Data 28)
    (hb : BaseRegs n bC M x) (hSM : StepMem bC s bestRow x.mem)
    (hrj1 : x.regs rj1 = j₁.val)
    (hfit : Fits w (bC + n * n + 8 * n + 2)) :
    ∃ y, ExecWithin w augCode x y (9 * n + 3) ∧
      (∀ i : Fin 28, i.val < 21 → y.regs i = x.regs i) ∧
      (∀ j : Fin n, y.mem (bC + n * n + 2 * n + j.val) =
        encodeOptFin (vget (hgApplyEdges s.mate (vget s.path j₁)) j)) ∧
      (∀ a, ¬(bC + n * n + 2 * n ≤ a ∧ a < bC + n * n + 3 * n) → y.mem a = x.mem a) := by
  let dC := bC + n * n + 2 * n
  let I (y : Data 28) : Prop :=
    (∀ i : Fin 28, i.val < 21 → y.regs i = x.regs i) ∧
      (∀ a, ¬(dC ≤ a ∧ a < dC + n) → y.mem a = x.mem a) ∧
      ((y.regs idx2 = n ∧ ∀ j : Fin n, y.mem (dC + j.val) =
          encodeOptFin (vget (hgApplyEdges s.mate (vget s.path j₁)) j)) ∨
       ∃ (j : Fin n) (pref : List (Fin n × Fin n)),
         y.regs idx2 = j.val ∧
         vget s.path j₁ = pref ++ vget s.path j ∧
         ∀ k : Fin n, y.mem (dC + k.val) = encodeOptFin (vget (hgApplyEdges s.mate pref) k))
  let rank (y : Data 28) : ℕ :=
    if h : y.regs idx2 < n then (vget s.path ⟨y.regs idx2, h⟩).length else 0
  have hstepBody (y : Data 28) (hy : I y) (hc : (Cond.lt idx2 rn).Holds y) :
      ∃ z, ExecWithin w augBody y z 7 ∧ I z ∧ rank z < rank y := by
    obtain ⟨hr, hf, hstate⟩ := hy
    have hby : BaseRegs n bC M y := hb.of_eq fun i hi => hr i (by omega)
    have hlt : y.regs idx2 < n := by simpa only [Cond.holds_lt, hby.hrn] using hc
    rcases hstate with ⟨heqn, _⟩ | ⟨j, pref, hj_eq, hpath_eq, hcol_pref⟩
    · omega
    have hj_fin : (⟨y.regs idx2, hlt⟩ : Fin n) = j := Fin.ext hj_eq
    let u := bestRow j
    have hbest_j : y.mem (bC + n * n + 6 * n + y.regs idx2) = u.val := by
      rw [hf _ (by simp only [dC]; omega), hj_eq]
      exact hSM.hbest j
    have hf1 : Fits w (bC + n * n + 6 * n + y.regs idx2) := hfit.of_le (by omega)
    have hf2 : Fits w (bC + n * n + 7 * n + 1 + u.val) := hfit.of_le (by have := u.isLt; omega)
    have hf3 : Fits w (dC + y.regs idx2) := hfit.of_le (by simp only [dC]; omega)
    have hcol_upd : ∀ k : Fin n,
        Function.update y.mem (dC + j.val) u.val (dC + k.val) =
          encodeOptFin (vget (vset (hgApplyEdges s.mate pref) j (some u)) k) := by
      intro k
      by_cases hkj : k = j
      · subst hkj
        simp [encodeOptFin]
      · have hne : dC + k.val ≠ dC + j.val := fun h => hkj (Fin.ext (by omega))
        rw [Function.update_of_ne hne, hcol_pref k, vget_vset_ne _ _ (Ne.symm hkj)]
    by_cases hex : ∃ j' : Fin n, vget s.mate j' = some u
    · obtain ⟨j', hj'⟩ := hex
      have hrow_u : y.mem (bC + n * n + 7 * n + 1 + u.val) = j'.val := by
        rw [hf _ (by simp only [dC]; have := u.isLt; omega)]
        exact hSM.hrow_some j' u hj'
      have hp_cons := hSI.path_eq_cons (j := j) hj'
      have hstep : ∃ z, ExecWithin w augBody y z 7 ∧
          z.mem = Function.update y.mem (dC + j.val) u.val ∧
          (∀ i : Fin 28, i.val < 21 → z.regs i = x.regs i) ∧
          z.regs idx2 = j'.val := by
        refine WP.exists_execWithin ?_
        unfold augBody
        wram_exec [hby.hbaseBestRow, hby.hbaseRowMate, hby.hbaseColMate,
          hbest_j, hrow_u, hf1, hf2, hf3]
        exact ⟨by wram_simp [dC, hj_eq], fun i hi => by wram_simp [hr i hi], by wram_simp⟩
      obtain ⟨z, he, hmz, hrz, hiz⟩ := hstep
      refine ⟨z, he, ⟨hrz, fun a ha => ?_, .inr ⟨j', pref ++ [(u, j)], hiz, ?_, ?_⟩⟩, ?_⟩
      · rw [hmz, Function.update_of_ne (by have := j.isLt; omega)]
        exact hf a ha
      · rw [hpath_eq, hp_cons, List.append_assoc, List.singleton_append]
      · intro k
        rw [hmz, hcol_upd k]
        simp [hgApplyEdges, List.foldl_append]
      · simp only [rank, hlt, hj_fin, hiz, j'.isLt, dite_true, Fin.eta, hp_cons, List.length_cons]
        omega
    · have hfree : ∀ j' : Fin n, vget s.mate j' ≠ some u := fun j' h => hex ⟨j', h⟩
      have hrow_u : y.mem (bC + n * n + 7 * n + 1 + u.val) = n := by
        rw [hf _ (by simp only [dC]; have := u.isLt; omega)]
        exact hSM.hrow_none u hfree
      have hp_sing := hSI.path_eq_singleton (j := j) hfree
      have hstep : ∃ z, ExecWithin w augBody y z 7 ∧
          z.mem = Function.update y.mem (dC + j.val) u.val ∧
          (∀ i : Fin 28, i.val < 21 → z.regs i = x.regs i) ∧
          z.regs idx2 = n := by
        refine WP.exists_execWithin ?_
        unfold augBody
        wram_exec [hby.hbaseBestRow, hby.hbaseRowMate, hby.hbaseColMate,
          hbest_j, hrow_u, hf1, hf2, hf3]
        exact ⟨by wram_simp [dC, hj_eq], fun i hi => by wram_simp [hr i hi], by wram_simp⟩
      obtain ⟨z, he, hmz, hrz, hiz⟩ := hstep
      refine ⟨z, he, ⟨hrz, fun a ha => ?_, .inl ⟨hiz, fun k => ?_⟩⟩, ?_⟩
      · rw [hmz, Function.update_of_ne (by have := j.isLt; omega)]
        exact hf a ha
      · rw [hmz, hcol_upd k, hpath_eq, hp_sing]
        simp only [hgApplyEdges, List.foldl_append, List.foldl_cons, List.foldl_nil]
        rfl
      · simp only [rank, hlt, hj_fin, hiz, lt_self_iff_false, dite_true, dite_false, hp_sing,
          List.length_singleton]
        omega
  have hsetup : ∃ y₀,
      ExecWithin w (ram[ idx2 ← rj1 ] : Code .standard 28) x y₀ 1 ∧ I y₀ ∧ rank y₀ ≤ n := by
    refine WP.exists_execWithin ?_
    wram_exec [hrj1]
    refine ⟨⟨fun i hi => by wram_simp, fun _ _ => rfl,
        .inr ⟨j₁, [], by wram_simp, rfl, fun k => hSM.hcol k⟩⟩, ?_⟩
    simp only [rank]
    have hidx2 : (x.set idx2 j₁.val).regs idx2 = j₁.val := by wram_simp
    rw [dite_eq_left (by rw [hidx2]; exact j₁.isLt)]
    have hfin : (⟨(x.set idx2 j₁.val).regs idx2, by rw [hidx2]; exact j₁.isLt⟩ : Fin n) = j₁ :=
      Fin.ext hidx2
    rw [hfin]
    exact hSI.length_path_le j₁
  obtain ⟨y₀, hs₀, hI₀, hrank₀⟩ := hsetup
  obtain ⟨y, hl, hIy, hcy⟩ := ExecWithin.loop_invariant (cond := .lt idx2 rn) (body := augBody)
    I rank (T := 7) hstepBody hI₀
  obtain ⟨hr, hf, hstate⟩ := hIy
  have hby : BaseRegs n bC M y := hb.of_eq fun i hi => hr i (by omega)
  rcases hstate with ⟨_, hcol_final⟩ | ⟨j, _, hj_eq, _, _⟩
  · refine ⟨y, (hs₀.seq hl).mono ?_, hr, hcol_final,
      fun a ha => hf a (by simp only [dC]; omega)⟩
    have := Nat.mul_le_mul_right 9 hrank₀
    omega
  · simp only [Cond.holds_lt, hj_eq, hby.hrn] at hcy
    exact absurd j.isLt hcy

private theorem exec_rebuildRowMateCode {w n bC M : ℕ} {mate : Vector (Option (Fin n)) n}
    (hM : IsMatching (fun _ => true) (mateMatching mate)) (x : Data 28)
    (hb : BaseRegs n bC M x)
    (hcol : ∀ j : Fin n, x.mem (bC + n * n + 2 * n + j.val) = encodeOptFin (vget mate j))
    (hfit : Fits w (bC + n * n + 8 * n + 2)) :
    ∃ y, ExecWithin w rebuildRowMateCode x y (13 * n + 6) ∧
      (∀ i : Fin 28, i.val < 21 → y.regs i = x.regs i) ∧
      (∀ j i : Fin n, vget mate j = some i → y.mem (bC + n * n + 7 * n + 1 + i.val) = j.val) ∧
      (∀ i : Fin n, (∀ j : Fin n, vget mate j ≠ some i) →
        y.mem (bC + n * n + 7 * n + 1 + i.val) = n) ∧
      (∀ a, ¬(bC + n * n + 7 * n + 1 ≤ a ∧ a < bC + n * n + 8 * n + 1) → y.mem a = x.mem a) := by
  let bRM := bC + n * n + 7 * n + 1
  obtain ⟨y₁, he₁, hr₁, hrm₁, hf₁⟩ := exec_fillConst baseRowMate rn (by decide) (by decide) x hb
    (by rw [hb.hbaseRowMate]; omega) hfit
  let P (k : ℕ) (y : Data 28) : Prop :=
    (∀ i : Fin 28, i.val < 21 → y.regs i = x.regs i) ∧
      (∀ a, ¬(bRM ≤ a ∧ a < bRM + n) → y.mem a = x.mem a) ∧
      (∀ j : Fin n, j.val < k → ∀ i : Fin n, vget mate j = some i → y.mem (bRM + i.val) = j.val) ∧
      (∀ i : Fin n, (∀ j : Fin n, j.val < k → vget mate j ≠ some i) → y.mem (bRM + i.val) = n)
  have hbody (y : Data 28) (hy : P (y.regs idx) y) (hlt : y.regs idx < n) :
      ∃ z, ExecWithin w scatterRowMateBody y z 6 ∧ P (y.regs idx + 1) z ∧
        z.regs idx = y.regs idx + 1 := by
    obtain ⟨hr, hf, hsome, hnone⟩ := hy
    let j₀ : Fin n := ⟨y.regs idx, hlt⟩
    have hby : BaseRegs n bC M y := hb.of_eq fun i hi => hr i (by omega)
    have hcol_j₀ : y.mem (bC + n * n + 2 * n + y.regs idx) = encodeOptFin (vget mate j₀) := by
      rw [hf _ (by simp only [bRM]; omega)]
      exact hcol j₀
    have hf1 : Fits w (bC + n * n + 2 * n + y.regs idx) := hfit.of_le (by omega)
    have hf2 : Fits w (y.regs idx + 1) := hfit.of_le (by omega)
    refine WP.exists_execWithin ?_
    unfold scatterRowMateBody
    cases hmj : vget mate j₀ with
    | none =>
      have henc : encodeOptFin (vget mate j₀) = n := by simp [hmj, encodeOptFin]
      wram_exec [hby.hbaseColMate, hby.hrn, hby.hzero, hby.hone, hcol_j₀, henc, hf1, hf2]
      refine ⟨⟨fun i hi => by wram_simp [hr i hi], hf, fun j hj i hm => ?_,
        fun i hall => ?_⟩, by wram_simp⟩
      · by_cases hjj : j = j₀
        · subst hjj; rw [hmj] at hm; cases hm
        · have : j.val ≠ y.regs idx := fun h => hjj (Fin.ext h)
          exact hsome j (by omega) i hm
      · exact hnone i fun j hj => hall j (by omega)
    | some i₀ =>
      have henc : encodeOptFin (vget mate j₀) = i₀.val := by simp [hmj, encodeOptFin]
      have hi₀_lt : i₀.val < n := i₀.isLt
      have hf3 : Fits w (bC + n * n + 7 * n + 1 + i₀.val) := hfit.of_le (by omega)
      wram_exec [hby.hbaseColMate, hby.hbaseRowMate, hby.hrn, hby.hzero, hby.hone,
        hcol_j₀, henc, hi₀_lt, hf1, hf2, hf3]
      refine ⟨⟨fun i hi => by wram_simp [hr i hi], fun a ha => ?_,
        fun j hj i hm => ?_, fun i hall => ?_⟩, by wram_simp⟩
      · change Function.update y.mem (bRM + i₀.val) (y.regs idx) a = x.mem a
        rw [Function.update_of_ne (by omega)]
        exact hf a ha
      · change Function.update y.mem (bRM + i₀.val) (y.regs idx) (bRM + i.val) = j.val
        by_cases hii : i = i₀
        · subst hii
          have hjj : j = j₀ := hM.2.1 i (j) (j₀)
            (mem_mateMatching.mpr hm) (mem_mateMatching.mpr hmj)
          subst hjj
          exact Function.update_self _ _ _
        · have hne : bRM + i.val ≠ bRM + i₀.val := fun h => hii (Fin.ext (by omega))
          have hjj : j ≠ j₀ := fun h => by
            subst h
            rw [hmj] at hm
            exact hii (Option.some.inj hm).symm
          have hj_ne : j.val ≠ y.regs idx := fun h => hjj (Fin.ext h)
          rw [Function.update_of_ne hne]
          exact hsome j (by omega) i hm
      · change Function.update y.mem (bRM + i₀.val) (y.regs idx) (bRM + i.val) = n
        have hii : i ≠ i₀ := fun h => by subst h; exact hall j₀ (Nat.lt_succ_self _) hmj
        have hne : bRM + i.val ≠ bRM + i₀.val := fun h => hii (Fin.ext (by omega))
        rw [Function.update_of_ne hne]
        exact hnone i fun j hj => hall j (by omega)
  obtain ⟨y₃, hl₃, hr₃, hf₃, hsome₃, hnone₃⟩ := exec_forLoop P
    (fun y hy => (hy.1 rn (by decide)).trans hb.hrn) hbody (x := y₁)
    ⟨fun i hi => by wram_simp [hr₁ i hi],
      fun a ha => hf₁ a (by rw [hb.hbaseRowMate]; simp only [bRM] at ha; omega),
      fun _ hj => by omega,
      fun i _ => by
        have := hrm₁ i.val i.isLt
        rwa [hb.hbaseRowMate, hb.hrn] at this⟩
  exact ⟨y₃, (he₁.seq hl₃).mono (by omega), hr₃,
    fun j i hm => hsome₃ j j.isLt i hm,
    fun i hall => hnone₃ i (fun j _ => hall j),
    fun a ha => hf₃ a (by simp only [bRM]; omega)⟩

theorem exec_augmentCode {w n bC M W : ℕ} {C : Fin n × Fin n → ℕ} {r j₁ : Fin n}
    {s : HgState n} {bestRow : Fin n → Fin n}
    (hSI : HgStepInv (fun p => (C p : ℤ)) W r s bestRow)
    (hj₁ : vget s.used j₁ = false) (hz : vget s.minv j₁ = 0) (hfree : vget s.mate j₁ = none)
    (x : Data 28) (hb : BaseRegs n bC M x) (hSM : StepMem bC s bestRow x.mem)
    (hrj1 : x.regs rj1 = j₁.val)
    (hfit : Fits w (bC + n * n + 8 * n + 2 * W + 2)) :
    ∃ y, ExecWithin w augmentCode x y (22 * n + 10) ∧
      (∀ i : Fin 28, i.val < 17 → y.regs i = x.regs i) ∧
      y.regs augmented = 1 ∧
      OuterMem bC s.y s.z (hgApplyEdges s.mate (vget s.path j₁)) y.mem ∧
      (∀ a, ¬(bC + n * n + 2 * n ≤ a ∧ a < bC + n * n + 3 * n) ∧
        ¬(bC + n * n + 7 * n + 1 ≤ a ∧ a < bC + n * n + 8 * n + 1) → y.mem a = x.mem a) := by
  have hfit_a : Fits w (bC + n * n + 8 * n + 2) := hfit.of_le (by omega)
  obtain ⟨hOB', _⟩ := hgOuterBound_augment hSI hj₁ hz hfree
  obtain ⟨y₁, he₁, hr₁, hcol₁, hf₁⟩ := exec_augCode hSI x hb hSM hrj1 hfit_a
  have hb₁ : BaseRegs n bC M y₁ := hb.of_eq fun i hi => hr₁ i (by omega)
  obtain ⟨y₂, he₂, hr₂, hsome₂, hnone₂, hf₂⟩ :=
    exec_rebuildRowMateCode hOB'.matching y₁ hb₁ hcol₁ hfit_a
  have hstep₃ : ∃ y₃,
      ExecWithin w (ram[ augmented ← #1 ] : Code .standard 28) y₂ y₃ 1 ∧
      y₃ = y₂.set augmented 1 := by
    refine WP.exists_execWithin ?_
    wram_exec [hfit.of_le (show 1 ≤ _ by omega)]
    rfl
  obtain ⟨y₃, he₃, rfl⟩ := hstep₃
  have hout : ∀ a, ¬(bC + n * n + 2 * n ≤ a ∧ a < bC + n * n + 3 * n) ∧
      ¬(bC + n * n + 7 * n + 1 ≤ a ∧ a < bC + n * n + 8 * n + 1) → y₂.mem a = x.mem a :=
    fun a ⟨ha1, ha2⟩ => (hf₂ a ha2).trans (hf₁ a ha1)
  refine ⟨_, (he₁.seq (he₂.seq he₃)).mono (by omega),
    fun i hi => ?_, by wram_simp,
    ⟨fun i => (hout _ (by have := i.isLt; omega)).trans (hSM.hy i),
     fun j => (hout _ (by have := j.isLt; omega)).trans (hSM.hnz j),
     fun j => (hf₂ _ (by have := j.isLt; omega)).trans (hcol₁ j),
     hsome₂, hnone₂⟩,
    hout⟩
  have h2 := hr₂ i (by omega)
  have h1 := hr₁ i (by omega)
  wram_simp [h2, h1]


end Cslib.Algorithms.WordRAM.Hungarian
