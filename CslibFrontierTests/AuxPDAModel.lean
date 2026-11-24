/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Complexity.Classes.LogCFL
import CslibFrontier.Computability.Machines.AuxPDA.Surface

/-!
# Tests for the native `AuxPDA` machine model, counting form, surface realizability, and `LogCFL`

Checked witnesses exercising:
1. A concrete 1-state, 0-work-tape `CountingAuxPDA` deciding the non-regular Dyck-1 balanced
   parentheses language (`false` = `(`, `true` = `)`) with a unique accepting branch on members and
   zero on nonmembers (`dyck1 ∈ UAuxPDA encBits`, `dyck1 ∈ LogCFL encBits`).
2. Stack height uncharged to work space: a concrete computation path reaching stack height `3` on
   `((()))` with `0` work-tape space, plus clock-boundary witnesses (`fuel = w.length` vs
   `w.length + 1`).
3. A concrete ambiguous `CountingAuxPDA` with `2` accepting branches on `[]` (passes `AuxPDA`
   acceptance, fails `UAuxPDA` uniqueness `f a ≤ 1`).
4. Empty-stack pop / stack underflow boundary: `StackOp.pop.apply? [] = none`, `step? = none`,
   no `AuxPDA.Step`, failure of `HaltsWithin`, and `acceptCount = 0`.
5. Concrete surface-pair realizability decomposition on `()()` (`[false, true, false, true]`):
   matched `pushPop` witnesses for each `()` pair and `trans` / `realizable_decomp` split at the
   intermediate empty-stack surface configuration.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.AuxPDAModel

open Turing Turing.AuxPDA Turing.CountingAuxPDA Turing.MultiTapeTM Cslib.Complexity

/-! ## 1. Unambiguous `AuxPDA` for Dyck-1 balanced parentheses (`UAuxPDA` and `LogCFL`) -/

/-- Balance checker for Dyck-1 (`false` = open `(`, `true` = close `)`). -/
private def dyck1Balance : ℕ → List Bool → Bool
  | depth, [] => depth == 0
  | depth, false :: rest => dyck1Balance (depth + 1) rest
  | 0, true :: _ => false
  | depth + 1, true :: rest => dyck1Balance depth rest

/-- The Dyck-1 language of balanced binary parenthesis words (`false` = `(`, `true` = `)`). -/
private def dyck1 : Set (List Bool) := {w | dyck1Balance 0 w = true}

private abbrev dyck1PushAct : AuxPDA.Action 0 Bool Unit Unit :=
  ⟨{ inputTape := 1, workTapes := Fin.elim0, output := none, state := some () }, .push ()⟩

private abbrev dyck1PopAct : AuxPDA.Action 0 Bool Unit Unit :=
  ⟨{ inputTape := 1, workTapes := Fin.elim0, output := none, state := some () }, .pop⟩

private abbrev dyck1HaltAct (b : Bool) : AuxPDA.Action 0 Bool Unit Unit :=
  ⟨{ inputTape := 0, workTapes := Fin.elim0, output := some b, state := none }, .stay⟩

private def dyck1Tr : Option Bool → Option Unit → List (AuxPDA.Action 0 Bool Unit Unit)
  | some false, _ => [dyck1PushAct]
  | some true, some () => [dyck1PopAct]
  | some true, none => [dyck1HaltAct false]
  | none, none => [dyck1HaltAct true]
  | none, some () => [dyck1HaltAct false]

/-- Single-state, zero-work-tape `CountingAuxPDA` deciding `dyck1` unambiguously:
* on `some false` (`(`): move input head right and push `()`;
* on `some true` (`)`) with nonempty stack: move input head right and pop;
* on `some true` (`)`) with empty stack: halt rejecting (`[false]`);
* on `none` (right endmarker): halt accepting (`[true]`) iff stack is empty. -/
private def dyck1Machine : CountingAuxPDA 0 Bool Unit Unit where
  q₀ := ()
  tr _ inp _ top := dyck1Tr inp top

private def dyck1Cfg (w : List Bool) (pos : Fin (w.length + 2)) (stack : List Unit) :
    AuxPDA.Cfg 0 Bool Unit Unit w :=
  ⟨⟨some (), pos, Fin.elim0, Fin.elim0, []⟩, stack⟩

private lemma dyck1Cfg_init (w : List Bool) :
    dyck1Machine.toAuxPDA.initCfg w = dyck1Cfg w ⟨1, by omega⟩ [] := by
  refine AuxPDA.Cfg.ext (Turing.Cfg.ext_zero_tapes rfl ?_ rfl) rfl
  ext
  change (1 : ℕ) % (w.length + 2) = 1
  exact Nat.mod_eq_of_lt (by omega)

private lemma haltsWithin_singleton_of_eq {M : CountingAuxPDA 0 Bool Unit Unit}
    {w : List Bool} {fuel : ℕ} {c c' : AuxPDA.Cfg 0 Bool Unit Unit w}
    {act : AuxPDA.Action 0 Bool Unit Unit}
    (hact : M.actions c = [act]) (happly : act.apply? c = some c')
    (hnext : M.HaltsWithin fuel c') : M.HaltsWithin (fuel + 1) c := by
  refine .step (by simp [hact]) (fun idx => ?_) (fun idx nextCfg h => ?_)
  · have h0 : idx.val = 0 := by have := idx.isLt; simp [hact] at this; omega
    simp [hact, h0, happly]
  · have h0 : idx.val = 0 := by have := idx.isLt; simp [hact] at this; omega
    simp only [hact, h0, List.getElem_cons_zero, happly, Option.some.injEq] at h
    exact h ▸ hnext

private lemma acceptCount_singleton_of_eq {M : CountingAuxPDA 0 Bool Unit Unit}
    {w : List Bool} {fuel : ℕ} {c c' : AuxPDA.Cfg 0 Bool Unit Unit w}
    {act : AuxPDA.Action 0 Bool Unit Unit}
    (hstate : c.tapes.state = some ()) (hact : M.actions c = [act])
    (happly : act.apply? c = some c') :
    M.acceptCount (fuel + 1) c = M.acceptCount fuel c' := by
  rw [CountingAuxPDA.acceptCount, CountingAuxPDA.branchCount_succ _ _ _ _ () hstate]
  have hlen : (M.actions c).length = 1 := by rw [hact]; rfl
  rw [Finset.sum_eq_single ⟨0, by omega⟩]
  · have h0 : (M.actions c)[0]'(by omega) = act := by simp [hact]
    rw [h0, happly]
    rfl
  · intro j _ hj
    exfalso
    apply hj
    ext
    omega
  · intro h
    exact absurd (Finset.mem_univ _) h

private lemma acceptCount_of_halted {M : CountingAuxPDA 0 Bool Unit Unit}
    {w : List Bool} {fuel : ℕ} {c : AuxPDA.Cfg 0 Bool Unit Unit w} (hh : c.Halted) :
    M.acceptCount fuel c = if c.tapes.output == [true] then 1 else 0 := by
  rw [CountingAuxPDA.acceptCount, CountingAuxPDA.branchCount, M.branches_of_halted hh,
    Finset.filter_singleton]
  simp only [CountingAuxPDA.runBranch, Option.any_some, beq_iff_eq]
  split_ifs <;> simp

private lemma dyck1_actions_eq {w : List Bool} {pos : Fin (w.length + 2)} {stack : List Unit}
    {sym : Option Bool} (hinp : (dyck1Cfg w pos stack).tapes.inputSymbol = sym) :
    dyck1Machine.actions (dyck1Cfg w pos stack) = dyck1Tr sym stack.head? := by
  cases hinp
  rfl

private lemma dyck1_halts_and_count (w : List Bool) :
    ∀ (rest : List Bool) (i : ℕ) (hi : i + rest.length = w.length),
      w.drop i = rest → ∀ (stack : List Unit),
      dyck1Machine.HaltsWithin (rest.length + 1) (dyck1Cfg w ⟨i + 1, by omega⟩ stack) ∧
      dyck1Machine.acceptCount (rest.length + 1) (dyck1Cfg w ⟨i + 1, by omega⟩ stack) =
        if dyck1Balance stack.length rest then 1 else 0 := by
  intro rest
  induction rest with
  | nil =>
    intro i hi _ stack
    have hiEq : i = w.length := by simp only [List.length_nil, add_zero] at hi; exact hi
    have hinp : (dyck1Cfg w ⟨i + 1, by omega⟩ stack).tapes.inputSymbol = none :=
      Turing.inputSymbol_eq_none_of_boundary (.inr (by simp [dyck1Cfg, hiEq]))
    cases stack with
    | nil =>
      have hact := dyck1_actions_eq hinp
      dsimp only [List.head?, dyck1Tr] at hact
      refine ⟨haltsWithin_singleton_of_eq hact rfl (.halt rfl), ?_⟩
      rw [List.length_nil, acceptCount_singleton_of_eq rfl hact rfl,
        acceptCount_of_halted (by rfl)]
      rfl
    | cons _ _ =>
      have hact := dyck1_actions_eq hinp
      dsimp only [List.head?, dyck1Tr] at hact
      refine ⟨haltsWithin_singleton_of_eq hact rfl (.halt rfl), ?_⟩
      rw [List.length_nil, acceptCount_singleton_of_eq rfl hact rfl,
        acceptCount_of_halted (by rfl)]
      rfl
  | cons b rest ih =>
    intro i hi hdrop stack
    have hilt : i < w.length := by simp at hi; omega
    have hwi : w[i] = b := by
      have h := congrArg List.head? hdrop
      simpa [List.head?_drop, hilt] using h
    have hinp : (dyck1Cfg w ⟨i + 1, by omega⟩ stack).tapes.inputSymbol = some b := by
      have h := Turing.inputSymbolInner (cfg := (dyck1Cfg w ⟨i + 1, by omega⟩ stack).tapes) i
        (by simp [dyck1Cfg]; omega) hilt
      simpa [hwi] using h
    have hmove : Turing.moveInputPos (⟨i + 1, by omega⟩ : Fin (w.length + 2)) 1 =
        ⟨(i + 1) + 1, by omega⟩ := by
      simpa using Turing.moveInputPos_pos_of_ne_right (⟨i + 1, by omega⟩ : Fin (w.length + 2))
        (by simp; omega)
    have hdrop' : w.drop (i + 1) = rest := by
      have := congrArg List.tail hdrop
      simpa [List.tail_drop] using this
    cases b with
    | false =>
      have hact := dyck1_actions_eq hinp
      dsimp only [dyck1Tr] at hact
      have hnextCfg : dyck1PushAct.apply? (dyck1Cfg w ⟨i + 1, by omega⟩ stack) =
          some (dyck1Cfg w ⟨(i + 1) + 1, by omega⟩ (() :: stack)) :=
        AuxPDA.Action.apply?_eq_some_iff.mpr
          ⟨() :: stack, rfl, AuxPDA.Cfg.ext (Turing.Cfg.ext_zero_tapes rfl hmove.symm rfl) rfl⟩
      obtain ⟨hH, hC⟩ := ih (i + 1) (by simp at hi; omega) hdrop' (() :: stack)
      refine ⟨haltsWithin_singleton_of_eq hact hnextCfg hH, ?_⟩
      rw [List.length_cons, acceptCount_singleton_of_eq rfl hact hnextCfg]
      exact hC
    | true =>
      cases stack with
      | nil =>
        have hact := dyck1_actions_eq hinp
        dsimp only [List.head?, dyck1Tr] at hact
        refine ⟨haltsWithin_singleton_of_eq hact rfl (.halt rfl), ?_⟩
        rw [List.length_cons, acceptCount_singleton_of_eq rfl hact rfl,
          acceptCount_of_halted (by rfl)]
        rfl
      | cons _ restStack =>
        have hact := dyck1_actions_eq hinp
        dsimp only [List.head?, dyck1Tr] at hact
        have hnextCfg : dyck1PopAct.apply? (dyck1Cfg w ⟨i + 1, by omega⟩ (() :: restStack)) =
            some (dyck1Cfg w ⟨(i + 1) + 1, by omega⟩ restStack) :=
          AuxPDA.Action.apply?_eq_some_iff.mpr
            ⟨restStack, rfl, AuxPDA.Cfg.ext (Turing.Cfg.ext_zero_tapes rfl hmove.symm rfl) rfl⟩
        obtain ⟨hH, hC⟩ := ih (i + 1) (by simp at hi; omega) hdrop' restStack
        refine ⟨haltsWithin_singleton_of_eq hact hnextCfg hH, ?_⟩
        rw [List.length_cons, acceptCount_singleton_of_eq rfl hact hnextCfg]
        exact hC

/-- Concrete non-regular language witness: `dyck1 ∈ UAuxPDA encBits`. -/
private theorem dyck1_mem_UAuxPDA : dyck1 ∈ UAuxPDA encBits := by
  refine ⟨0, Unit, Unit, inferInstance, inferInstance, dyck1Machine, 0,
    fun w => w.length + 1, fun w => if dyck1Balance 0 w then 1 else 0,
    PolyBounded.of_forall_le 1 1 fun w => by simp [encBits_apply], fun w => ?_,
    fun w => by dsimp only; split_ifs <;> omega,
    fun w => by dsimp only; simp only [dyck1, Set.mem_ofPred_eq]; split_ifs <;> simp [*]⟩
  obtain ⟨hH, hC⟩ := dyck1_halts_and_count w w 0 (by simp) (by simp) []
  rw [← dyck1Cfg_init w] at hH hC
  exact ⟨AuxPDA.runsInSpace_zero_tapes _ _ _, hH, hC.symm⟩

/-- `dyck1 ∈ LogCFL encBits` follows from `UAuxPDA_subset_LogCFL`. -/
example : dyck1 ∈ LogCFL encBits := UAuxPDA_subset_LogCFL dyck1_mem_UAuxPDA

/-- Balanced and unbalanced words under `dyck1`. -/
example :
    [false, false, true, true] ∈ dyck1 ∧
    [false, true, false, true] ∈ dyck1 ∧
    [true, false] ∉ dyck1 ∧
    [false] ∉ dyck1 := by
  simp [dyck1, dyck1Balance]

/-! ## 2. Space-vs-stack and clock boundaries -/

/-- On `((()))`, `dyck1Machine` pushes to stack height `3` while using `0` work-tape space. -/
example :
    let w : List Bool := [false, false, false, true, true, true]
    ∃ p : dyck1Machine.toAuxPDA.ComputationPath w,
      p.last.stack.length = 3 ∧ p.space = 0 := by
  intro w
  have hwlen : w.length = 6 := rfl
  let s0 := dyck1Cfg w ⟨1, by omega⟩ []
  let s1 := dyck1Cfg w ⟨2, by omega⟩ [()]
  let s2 := dyck1Cfg w ⟨3, by omega⟩ [(), ()]
  let s3 := dyck1Cfg w ⟨4, by omega⟩ [(), (), ()]
  have hpush (i : ℕ) (hi : i < 3) (st : List Unit) :
      dyck1Machine.toAuxPDA.Step
        (dyck1Cfg w ⟨i + 1, by omega⟩ st)
        (dyck1Cfg w ⟨i + 2, by omega⟩ (() :: st)) := by
    refine ⟨dyck1PushAct, ?_, ?_⟩
    · have hi' : (dyck1Cfg w ⟨i + 1, by omega⟩ st).tapes.inputSymbol = some false := by
        have h := Turing.inputSymbolInner (cfg := (dyck1Cfg w ⟨i + 1, by omega⟩ st).tapes) i
          (by simp [dyck1Cfg]; omega) (by omega)
        have hwi : w[i]'(by omega) = false := by interval_cases i <;> rfl
        simpa [hwi] using h
      change dyck1PushAct ∈ dyck1Machine.tr ()
        (dyck1Cfg w ⟨i + 1, by omega⟩ st).tapes.inputSymbol _ _
      rw [hi']
      simp [dyck1Machine, dyck1Tr]
    · have hm : Turing.moveInputPos (⟨i + 1, by omega⟩ : Fin (w.length + 2)) 1 =
          ⟨i + 2, by omega⟩ := by
        simpa using Turing.moveInputPos_pos_of_ne_right
          (⟨i + 1, by omega⟩ : Fin (w.length + 2)) (by simp [hwlen]; omega)
      exact AuxPDA.Action.apply?_eq_some_iff.mpr
        ⟨() :: st, rfl, AuxPDA.Cfg.ext (Turing.Cfg.ext_zero_tapes rfl hm.symm rfl) rfl⟩
  let r3 : dyck1Machine.toAuxPDA.RunPath w :=
    { length := 3
      toFun := ![s0, s1, s2, s3]
      step := fun i => by
        fin_cases i
        · exact hpush 0 (by decide) []
        · exact hpush 1 (by decide) [()]
        · exact hpush 2 (by decide) [(), ()] }
  refine ⟨⟨r3, (dyck1Cfg_init w).symm⟩, rfl, ?_⟩
  simp [AuxPDA.ComputationPath.space, AuxPDA.RunPath.space]

/-- Clock boundary on `w = [false, true]`: `fuel = 2` is one step short of halting (count `0` and
`¬HaltsWithin 2`), whereas `fuel = 3` halts with `acceptCount = 1`. -/
example :
    let w : List Bool := [false, true]
    dyck1Machine.acceptCount 2 (dyck1Machine.toAuxPDA.initCfg w) = 0 ∧
    ¬dyck1Machine.HaltsWithin 2 (dyck1Machine.toAuxPDA.initCfg w) ∧
    dyck1Machine.HaltsWithin 3 (dyck1Machine.toAuxPDA.initCfg w) ∧
    dyck1Machine.acceptCount 3 (dyck1Machine.toAuxPDA.initCfg w) = 1 := by
  intro w
  obtain ⟨hH3, hC3⟩ := dyck1_halts_and_count w w 0 rfl rfl []
  rw [← dyck1Cfg_init w] at hH3 hC3
  have hinp0 : (dyck1Cfg w ⟨1, by decide⟩ []).tapes.inputSymbol = some false :=
    Turing.inputSymbolInner (cfg := (dyck1Cfg w ⟨1, by decide⟩ []).tapes) 0 rfl (by decide)
  have hinp1 : (dyck1Cfg w ⟨2, by decide⟩ [()]).tapes.inputSymbol = some true :=
    Turing.inputSymbolInner (cfg := (dyck1Cfg w ⟨2, by decide⟩ [()]).tapes) 1 rfl (by decide)
  have hinp2 : (dyck1Cfg w ⟨3, by decide⟩ []).tapes.inputSymbol = none :=
    Turing.inputSymbol_eq_none_of_boundary (.inr rfl)
  have hact0 : dyck1Machine.actions (dyck1Cfg w ⟨1, by decide⟩ []) = [dyck1PushAct] :=
    dyck1_actions_eq hinp0
  have hact1 : dyck1Machine.actions (dyck1Cfg w ⟨2, by decide⟩ [()]) = [dyck1PopAct] :=
    dyck1_actions_eq hinp1
  have hact2 : dyck1Machine.actions (dyck1Cfg w ⟨3, by decide⟩ []) = [dyck1HaltAct true] :=
    dyck1_actions_eq hinp2
  have hnext0 : dyck1PushAct.apply? (dyck1Cfg w ⟨1, by decide⟩ []) =
      some (dyck1Cfg w ⟨2, by decide⟩ [()]) :=
    AuxPDA.Action.apply?_eq_some_iff.mpr
      ⟨[()], rfl, AuxPDA.Cfg.ext (Turing.Cfg.ext_zero_tapes rfl (by decide) rfl) rfl⟩
  have hnext1 : dyck1PopAct.apply? (dyck1Cfg w ⟨2, by decide⟩ [()]) =
      some (dyck1Cfg w ⟨3, by decide⟩ []) :=
    AuxPDA.Action.apply?_eq_some_iff.mpr
      ⟨[], rfl, AuxPDA.Cfg.ext (Turing.Cfg.ext_zero_tapes rfl (by decide) rfl) rfl⟩
  have hstep0 : dyck1Machine.step? (dyck1Cfg w ⟨1, by decide⟩ []) 0 =
      some (dyck1Cfg w ⟨2, by decide⟩ [()]) := by
    rw [CountingAuxPDA.step?, hact0]
    exact hnext0
  have hstep1 : dyck1Machine.step? (dyck1Cfg w ⟨2, by decide⟩ [()]) 0 =
      some (dyck1Cfg w ⟨3, by decide⟩ []) := by
    rw [CountingAuxPDA.step?, hact1]
    exact hnext1
  have hstep2 : dyck1Machine.step? (dyck1Cfg w ⟨3, by decide⟩ []) 0 =
      some ⟨(dyck1HaltAct true).tape.apply (dyck1Cfg w ⟨3, by decide⟩ []).tapes, []⟩ := by
    rw [CountingAuxPDA.step?, hact2]
    rfl
  have hrun3 :
      ∃ f, dyck1Machine.runBranch (dyck1Machine.toAuxPDA.initCfg w) [0, 0, 0] = some f := by
    rw [dyck1Cfg_init w]
    refine ⟨⟨(dyck1HaltAct true).tape.apply (dyck1Cfg w ⟨3, by decide⟩ []).tapes, []⟩, ?_⟩
    rw [CountingAuxPDA.runBranch, hstep0]
    dsimp only [Bind.bind, Option.bind]
    rw [CountingAuxPDA.runBranch, hstep1]
    dsimp only [Bind.bind, Option.bind]
    rw [CountingAuxPDA.runBranch, hstep2]
    rfl
  have hnotH2 : ¬dyck1Machine.HaltsWithin 2 (dyck1Machine.toAuxPDA.initCfg w) := by
    intro h2
    obtain ⟨f, hf⟩ := hrun3
    have hlen := h2.length_le hf
    simp at hlen
  have hcount2 : dyck1Machine.acceptCount 2 (dyck1Machine.toAuxPDA.initCfg w) = 0 := by
    rw [dyck1Cfg_init w, acceptCount_singleton_of_eq rfl hact0 hnext0,
      acceptCount_singleton_of_eq rfl hact1 hnext1]
    simp [CountingAuxPDA.acceptCount, CountingAuxPDA.branchCount, CountingAuxPDA.branches,
      dyck1Cfg]
  have hH3' : dyck1Machine.HaltsWithin 3 (dyck1Machine.toAuxPDA.initCfg w) := hH3
  have hC3' : dyck1Machine.acceptCount 3 (dyck1Machine.toAuxPDA.initCfg w) = 1 := hC3
  exact ⟨hcount2, hnotH2, hH3', hC3'⟩

/-! ## 3. Concrete ambiguous `AuxPDA` witness (2 accepting branches) -/

/-- A counting `AuxPDA` with two distinct accepting transitions from the initial state. -/
private def ambiguousMachine : CountingAuxPDA 0 Bool Unit Unit where
  q₀ := ()
  tr _ _ _ _ := [dyck1HaltAct true, dyck1HaltAct true]

/-- `ambiguousMachine` accepts `[]` nondeterministically, yet has `acceptCount = 2` (failing the
unambiguous `f a ≤ 1` bound of `UAuxPDA`). -/
example :
    ambiguousMachine.toAuxPDA.Accepts [] ∧
    ambiguousMachine.HaltsWithin 1 (ambiguousMachine.toAuxPDA.initCfg []) ∧
    ambiguousMachine.acceptCount 1 (ambiguousMachine.toAuxPDA.initCfg []) = 2 := by
  let init : AuxPDA.Cfg 0 Bool Unit Unit [] := ambiguousMachine.toAuxPDA.initCfg []
  have hact : ambiguousMachine.actions init = [dyck1HaltAct true, dyck1HaltAct true] := rfl
  have hH : ambiguousMachine.HaltsWithin 1 init := by
    refine .step (by simp [hact]) (fun idx => ?_) (fun idx nextCfg heq => ?_)
    · have hi : idx.val = 0 ∨ idx.val = 1 := by
        have := idx.isLt; simp [hact] at this; omega
      rcases hi with h0 | h1
      · simp [hact, h0, AuxPDA.Action.apply?]
      · simp [hact, h1, AuxPDA.Action.apply?]
    · have hi : idx.val = 0 ∨ idx.val = 1 := by
        have := idx.isLt; simp [hact] at this; omega
      rcases hi with h0 | h1
      · simp only [hact, h0, List.getElem_cons_zero, AuxPDA.Action.apply?,
          AuxPDA.StackOp.apply?_stay, Option.map_some, Option.some.injEq] at heq
        subst heq; exact .halt rfl
      · simp only [hact, h1, List.getElem_cons_succ, List.getElem_cons_zero, AuxPDA.Action.apply?,
          AuxPDA.StackOp.apply?_stay, Option.map_some, Option.some.injEq] at heq
        subst heq; exact .halt rfl
  have hC : ambiguousMachine.acceptCount 1 init = 2 := by
    rw [CountingAuxPDA.acceptCount, CountingAuxPDA.branchCount_succ _ _ _ _ () rfl]
    have hlen : (ambiguousMachine.actions init).length = 2 := by rw [hact]; rfl
    have hsum : (∑ _j : Fin (ambiguousMachine.actions init).length, 1) = 2 := by simp [hlen]
    refine (Finset.sum_congr rfl fun j _ => ?_).trans hsum
    have hj : j.val = 0 ∨ j.val = 1 := by omega
    rcases hj with h0 | h1
    · have he : (ambiguousMachine.actions init)[j.val] = dyck1HaltAct true := by simp [hact, h0]
      rw [he]
      exact acceptCount_of_halted (M := ambiguousMachine) (fuel := 0) (by rfl)
    · have he : (ambiguousMachine.actions init)[j.val] = dyck1HaltAct true := by simp [hact, h1]
      rw [he]
      exact acceptCount_of_halted (M := ambiguousMachine) (fuel := 0) (by rfl)
  have hAcc : ambiguousMachine.toAuxPDA.Accepts [] := by
    have hpos : 0 < ambiguousMachine.acceptCount 1 init := by omega
    obtain ⟨p, hp, hh, hout⟩ := (hH.branchCount_pos_iff (· == [true])).mp hpos
    exact ⟨⟨p, hp⟩, hh, beq_iff_eq.mp hout⟩
  exact ⟨hAcc, hH, hC⟩

/-! ## 4. Empty-stack pop / stack underflow boundary -/

/-- A machine whose only transition attempts `StackOp.pop` on an empty stack. -/
private def underflowMachine : CountingAuxPDA 0 Bool Unit Unit where
  q₀ := ()
  tr _ _ _ _ :=
    [⟨{ inputTape := 0, workTapes := Fin.elim0, output := some true, state := none }, .pop⟩]

/-- Empty-stack pop returns `none` in `StackOp.apply?` and `step?`, admits no `AuxPDA.Step`,
fails `HaltsWithin`, and contributes `0` accepting branches. -/
example :
    let init := underflowMachine.toAuxPDA.initCfg []
    (StackOp.pop : StackOp Unit).apply? [] = none ∧
    underflowMachine.step? init 0 = none ∧
    (∀ c', ¬underflowMachine.toAuxPDA.Step init c') ∧
    ¬underflowMachine.HaltsWithin 1 init ∧
    underflowMachine.acceptCount 1 init = 0 := by
  intro init
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · simp [CountingAuxPDA.step?, CountingAuxPDA.actions, underflowMachine, init,
      AuxPDA.Action.apply?]
  · intro c' hstep
    simp only [AuxPDA.Step, CountingAuxPDA.toAuxPDA, underflowMachine, init, AuxPDA.initCfg,
      AuxPDA.Cfg.init, Turing.Cfg.init, List.mem_singleton] at hstep
    obtain ⟨act, rfl, hact⟩ := hstep
    simp [AuxPDA.Action.apply?] at hact
  · intro hH
    cases hH with
    | halt hh => simp [init, AuxPDA.Cfg.Halted, Turing.Cfg.Halted] at hh
    | step _ hvalid _ =>
      have hv := hvalid ⟨0, by simp [CountingAuxPDA.actions, underflowMachine, init]⟩
      simp [CountingAuxPDA.actions, underflowMachine, init, AuxPDA.Action.apply?] at hv
  · rw [CountingAuxPDA.acceptCount, CountingAuxPDA.branchCount_succ _ _ _ _ () rfl]
    simp [CountingAuxPDA.actions, underflowMachine, init, AuxPDA.Action.apply?]

/-! ## 5. Surface-pair realizability decomposition on `()()` -/

private lemma dyck1_realizable_pair (w : List Bool) (i : ℕ) (hi : i + 1 < w.length)
    (h0 : w[i] = false) (h1 : w[i + 1] = true) :
    dyck1Machine.toAuxPDA.Realizable w
      (dyck1Cfg w ⟨i + 1, by omega⟩ []).surface
      (dyck1Cfg w ⟨i + 3, by omega⟩ []).surface 2 := by
  let sMid := (dyck1Cfg w ⟨i + 2, by omega⟩ [()]).surface
  refine .pushPop (γ := ()) (s' := sMid) (s'' := sMid) ?_ (.refl sMid) ?_
  · refine ⟨(), dyck1PushAct, rfl, ?_, rfl, ?_⟩
    · have hi0 : (dyck1Cfg w ⟨i + 1, by omega⟩ []).surface.inputSymbol = some false := by
        rw [Cfg.surface_inputSymbol]
        simpa [h0] using Turing.inputSymbolInner
          (cfg := (dyck1Cfg w ⟨i + 1, by omega⟩ []).tapes) i (by simp [dyck1Cfg]; omega)
          (by omega)
      change dyck1PushAct ∈ dyck1Machine.tr ()
        (dyck1Cfg w ⟨i + 1, by omega⟩ []).surface.inputSymbol _ _
      rw [hi0]
      simp [dyck1Machine, dyck1Tr]
    · have hm : Turing.moveInputPos (⟨i + 1, by omega⟩ : Fin (w.length + 2)) 1 =
          ⟨i + 2, by omega⟩ := by
        simpa using Turing.moveInputPos_pos_of_ne_right
          (⟨i + 1, by omega⟩ : Fin (w.length + 2)) (by simp; omega)
      exact SurfaceCfg.ext hm.symm (Turing.Storage.ext rfl (funext fun j => j.elim0)
        (funext fun j => j.elim0)) rfl rfl
  · refine ⟨rfl, (), dyck1PopAct, rfl, ?_, rfl, ?_⟩
    · have hi1 : sMid.inputSymbol = some true := by
        rw [Cfg.surface_inputSymbol]
        simpa [h1] using Turing.inputSymbolInner
          (cfg := (dyck1Cfg w ⟨i + 2, by omega⟩ [()]).tapes) (i + 1) (by simp [dyck1Cfg]; omega)
          (by omega)
      change dyck1PopAct ∈ dyck1Machine.tr () sMid.inputSymbol _ (some ())
      rw [hi1]
      simp [dyck1Machine, dyck1Tr]
    · have hm : Turing.moveInputPos (⟨i + 2, by omega⟩ : Fin (w.length + 2)) 1 =
          ⟨i + 3, by omega⟩ := by
        simpa using Turing.moveInputPos_pos_of_ne_right
          (⟨i + 2, by omega⟩ : Fin (w.length + 2)) (by simp; omega)
      exact SurfaceCfg.ext hm.symm (Turing.Storage.ext rfl (funext fun j => j.elim0)
        (funext fun j => j.elim0)) rfl rfl

example :
    let w : List Bool := [false, true, false, true]
    let s0 := (dyck1Cfg w ⟨1, by decide⟩ []).surface
    let s2 := (dyck1Cfg w ⟨3, by decide⟩ []).surface
    let s4 := (dyck1Cfg w ⟨5, by decide⟩ []).surface
    dyck1Machine.toAuxPDA.Realizable w s0 s2 2 ∧
    dyck1Machine.toAuxPDA.Realizable w s2 s4 2 ∧
    dyck1Machine.toAuxPDA.Realizable w s0 s4 4 := by
  intro w s0 s2 s4
  have hReal02 : dyck1Machine.toAuxPDA.Realizable w s0 s2 2 :=
    dyck1_realizable_pair w 0 (by decide) rfl rfl
  have hReal24 : dyck1Machine.toAuxPDA.Realizable w s2 s4 2 :=
    dyck1_realizable_pair w 2 (by decide) rfl rfl
  have hReal04 : dyck1Machine.toAuxPDA.Realizable w s0 s4 4 :=
    (realizable_decomp (by decide : 2 ≤ 4)).mpr (.inr ⟨s2, 2, 2, by decide, by decide, rfl,
      hReal02, hReal24⟩)
  exact ⟨hReal02, hReal24, hReal04⟩

end CslibFrontierTests.AuxPDAModel
