/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Circuit.Boolean.SemiUnbounded.AuxPDACompiler

/-!
# Tests for the normal-form `AuxPDA → LayeredSemiUnboundedCircuit` compiler

Checked witnesses exercising:
1. Bounded-space surface enumeration (`BoundedSurfaceCfg`, `boundedSurfaceEquivFin`,
   `boundedSurfaceCard_le_surfaceCfgBound`) and the `Turing.window s` boundary for
   `applyBoundedTapes?` (stepping inside `[-1, 1]` returns `some`; stepping to `2 ∉ [-1, 1]`
   returns `none`).
2. Concrete push-pop `AuxPDA` (`dyck1AuxPDA`, recognizing balanced Dyck-1 parentheses with `false`
   = `(` and `true` = `)`):
   * compiled through `compileAuxPDA` to a strictly normal-form `LayeredSemiUnboundedCircuit`
     (`InNormalForm`),
   * `Eval outputGate ↔ Accepts` verified on accepting words (`[]`, `[false, true]`,
     `[false, false, true, true]`) and rejecting words (`[true]`, `[false]`, `[true, false]`),
   * `compileAuxPDA_exists_minIsolating_seed` (Work Package 1) and
     `WeightGenerator.generatedGateWeight_certified` (Work Package 2) instantiated directly on
     the compiled circuit,
   * computable `DecidableRel (compileAuxPDA …).orChild` exercised directly on `dyck1Circuit`.
3. End-to-end `LogCFL.exists_normalForm_circuit_family_certified` instantiated on `dyck1`.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.AuxPDACircuitCompiler

open Turing Turing.AuxPDA Turing.MultiTapeTM Cslib.Complexity
open Cslib.Circuits.Boolean Cslib.Circuits.Boolean.LayeredSemiUnboundedCircuit
open Cslib.Circuits.Boolean.AuxPDACompiler
open Cslib.Code.JustesenFamily Cslib.Reachability.Hoza

/-! ## 1. Window boundary witness for `BoundedSurfaceCfg` and `applyBoundedTapes?` -/

/-- A 1-tape bounded surface configuration with head at the right boundary `+1 ∈ window 1`:
moving left stays inside `[-1, 1]` (`isSome`), while moving right leaves `[-1, 1]` (`none`). -/
example :
    let b : BoundedSurfaceCfg 1 Unit Unit [] 1 :=
      { inputPos := ⟨1, by decide⟩
        state := some ()
        workTapes := fun _ _ => none
        workTapePos := fun _ => ⟨1, by decide⟩
        topSym := none
        outputSummary := .empty }
    let moveRight : Turing.Action 1 Bool Unit :=
      { inputTape := 0, workTapes := fun _ => (some (some true), 1), output := none,
        state := some () }
    let moveLeft : Turing.Action 1 Bool Unit :=
      { inputTape := 0, workTapes := fun _ => (some (some true), -1), output := none,
        state := some () }
    applyBoundedTapes? moveRight b none = none ∧
    (applyBoundedTapes? moveLeft b none).isSome = true := by
  intro b moveRight moveLeft
  refine ⟨?_, ?_⟩
  · unfold applyBoundedTapes?
    split_ifs with h
    · exfalso
      have h0 := h 0
      simp [b, moveRight, Turing.mem_window] at h0
    · rfl
  · unfold applyBoundedTapes?
    split_ifs with h
    · rfl
    · exfalso
      apply h
      intro i
      fin_cases i
      simp [b, moveLeft, Turing.mem_window]

/-! ## 2. Concrete Dyck-1 `AuxPDA` compiled to a normal-form semi-unbounded circuit -/

private def unitEquivFin1 : Unit ≃ Fin 1 where
  toFun _ := ⟨0, by decide⟩
  invFun _ := ()
  left_inv _ := rfl
  right_inv i := by fin_cases i; rfl

private def dyck1Balance : ℕ → List Bool → Bool
  | depth, [] => depth == 0
  | depth, false :: rest => dyck1Balance (depth + 1) rest
  | 0, true :: _ => false
  | depth + 1, true :: rest => dyck1Balance depth rest

private abbrev pushAct : AuxPDA.Action 0 Bool Unit Unit :=
  ⟨{ inputTape := 1, workTapes := Fin.elim0, output := none, state := some () }, .push ()⟩

private abbrev popAct : AuxPDA.Action 0 Bool Unit Unit :=
  ⟨{ inputTape := 1, workTapes := Fin.elim0, output := none, state := some () }, .pop⟩

private abbrev haltAct (b : Bool) : AuxPDA.Action 0 Bool Unit Unit :=
  ⟨{ inputTape := 0, workTapes := Fin.elim0, output := some b, state := none }, .stay⟩

private def dyck1Tr : Option Bool → Option Unit → List (AuxPDA.Action 0 Bool Unit Unit)
  | some false, _ => [pushAct]
  | some true, some () => [popAct]
  | some true, none => [haltAct false]
  | none, none => [haltAct true]
  | none, some () => [haltAct false]

private def dyck1Counting : CountingAuxPDA 0 Bool Unit Unit where
  q₀ := ()
  tr _ inp _ top := dyck1Tr inp top

private abbrev dyck1AuxPDA : AuxPDA 0 Bool Unit Unit := dyck1Counting.toAuxPDA

private instance (q : Unit) (inp : Option Bool) (work : Fin 0 → Option Bool)
    (top : Option Unit) (act : AuxPDA.Action 0 Bool Unit Unit) :
    Decidable (dyck1AuxPDA.Tr q inp work top act) := by
  change Decidable (act ∈ dyck1Tr inp top)
  infer_instance

private def dyck1Cfg (w : List Bool) (pos : Fin (w.length + 2)) (stack : List Unit) :
    AuxPDA.Cfg 0 Bool Unit Unit w :=
  ⟨⟨some (), pos, Fin.elim0, Fin.elim0, []⟩, stack⟩

private lemma dyck1Cfg_init (w : List Bool) :
    dyck1AuxPDA.initCfg w = dyck1Cfg w ⟨1, by omega⟩ [] := by
  refine AuxPDA.Cfg.ext (Turing.Cfg.ext_zero_tapes rfl ?_ rfl) rfl
  ext
  change (1 : ℕ) % (w.length + 2) = 1
  exact Nat.mod_eq_of_lt (by omega)

private lemma haltsWithin_singleton_of_eq {w : List Bool} {fuel : ℕ}
    {c c' : AuxPDA.Cfg 0 Bool Unit Unit w} {act : AuxPDA.Action 0 Bool Unit Unit}
    (hact : dyck1Counting.actions c = [act]) (happly : act.apply? c = some c')
    (hnext : dyck1Counting.HaltsWithin fuel c') : dyck1Counting.HaltsWithin (fuel + 1) c := by
  refine .step (by simp [hact]) (fun idx => ?_) (fun idx nextCfg h => ?_)
  · have h0 : idx.val = 0 := by have := idx.isLt; simp [hact] at this; omega
    simp [hact, h0, happly]
  · have h0 : idx.val = 0 := by have := idx.isLt; simp [hact] at this; omega
    simp only [hact, h0, List.getElem_cons_zero, happly, Option.some.injEq] at h
    exact h ▸ hnext

private lemma acceptCount_singleton_of_eq {w : List Bool} {fuel : ℕ}
    {c c' : AuxPDA.Cfg 0 Bool Unit Unit w} {act : AuxPDA.Action 0 Bool Unit Unit}
    (hstate : c.tapes.state = some ()) (hact : dyck1Counting.actions c = [act])
    (happly : act.apply? c = some c') :
    dyck1Counting.acceptCount (fuel + 1) c = dyck1Counting.acceptCount fuel c' := by
  rw [CountingAuxPDA.acceptCount, CountingAuxPDA.branchCount_succ _ _ _ _ () hstate]
  have hlen : (dyck1Counting.actions c).length = 1 := by rw [hact]; rfl
  rw [Finset.sum_eq_single ⟨0, by omega⟩]
  · have h0 : (dyck1Counting.actions c)[0]'(by omega) = act := by simp [hact]
    rw [h0, happly]
    rfl
  · intro j _ hj; exfalso; apply hj; ext; omega
  · intro h; exact absurd (Finset.mem_univ _) h

private lemma acceptCount_of_halted {w : List Bool} {fuel : ℕ}
    {c : AuxPDA.Cfg 0 Bool Unit Unit w} (hh : c.Halted) :
    dyck1Counting.acceptCount fuel c = if c.tapes.output == [true] then 1 else 0 := by
  rw [CountingAuxPDA.acceptCount, CountingAuxPDA.branchCount,
    dyck1Counting.branches_of_halted hh, Finset.filter_singleton]
  simp only [CountingAuxPDA.runBranch, Option.any_some, beq_iff_eq]
  split_ifs <;> simp

private lemma dyck1_halts_and_count (w : List Bool) :
    ∀ (rest : List Bool) (i : ℕ) (hi : i + rest.length = w.length),
      w.drop i = rest → ∀ (stack : List Unit),
      dyck1Counting.HaltsWithin (rest.length + 1) (dyck1Cfg w ⟨i + 1, by omega⟩ stack) ∧
      dyck1Counting.acceptCount (rest.length + 1) (dyck1Cfg w ⟨i + 1, by omega⟩ stack) =
        if dyck1Balance stack.length rest then 1 else 0 := by
  intro rest
  induction rest with
  | nil =>
    intro i hi _ stack
    have hiEq : i = w.length := by simp only [List.length_nil, add_zero] at hi; exact hi
    have hinp : (dyck1Cfg w ⟨i + 1, by omega⟩ stack).tapes.inputSymbol = none :=
      Turing.inputSymbol_eq_none_of_boundary (.inr (by simp [dyck1Cfg, hiEq]))
    have hact : dyck1Counting.actions (dyck1Cfg w ⟨i + 1, by omega⟩ stack) =
        dyck1Tr none stack.head? := by
      change dyck1Tr (dyck1Cfg w ⟨i + 1, by omega⟩ stack).tapes.inputSymbol stack.head? = _
      rw [hinp]
    cases stack with
    | nil =>
      refine ⟨haltsWithin_singleton_of_eq hact rfl (.halt rfl), ?_⟩
      rw [List.length_nil, acceptCount_singleton_of_eq rfl hact rfl, acceptCount_of_halted rfl]
      rfl
    | cons _ _ =>
      refine ⟨haltsWithin_singleton_of_eq hact rfl (.halt rfl), ?_⟩
      rw [List.length_nil, acceptCount_singleton_of_eq rfl hact rfl, acceptCount_of_halted rfl]
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
    have hact : dyck1Counting.actions (dyck1Cfg w ⟨i + 1, by omega⟩ stack) =
        dyck1Tr (some b) stack.head? := by
      change dyck1Tr (dyck1Cfg w ⟨i + 1, by omega⟩ stack).tapes.inputSymbol stack.head? = _
      rw [hinp]
    have hmove : Turing.moveInputPos (⟨i + 1, by omega⟩ : Fin (w.length + 2)) 1 =
        ⟨(i + 1) + 1, by omega⟩ := by
      simpa using Turing.moveInputPos_pos_of_ne_right (⟨i + 1, by omega⟩ : Fin (w.length + 2))
        (by simp; omega)
    have hdrop' : w.drop (i + 1) = rest := by
      have := congrArg List.tail hdrop
      simpa [List.tail_drop] using this
    cases b with
    | false =>
      have hnextCfg : pushAct.apply? (dyck1Cfg w ⟨i + 1, by omega⟩ stack) =
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
        refine ⟨haltsWithin_singleton_of_eq hact rfl (.halt rfl), ?_⟩
        rw [List.length_cons, acceptCount_singleton_of_eq rfl hact rfl, acceptCount_of_halted rfl]
        rfl
      | cons _ restStack =>
        have hnextCfg : popAct.apply? (dyck1Cfg w ⟨i + 1, by omega⟩ (() :: restStack)) =
            some (dyck1Cfg w ⟨(i + 1) + 1, by omega⟩ restStack) :=
          AuxPDA.Action.apply?_eq_some_iff.mpr
            ⟨restStack, rfl, AuxPDA.Cfg.ext (Turing.Cfg.ext_zero_tapes rfl hmove.symm rfl) rfl⟩
        obtain ⟨hH, hC⟩ := ih (i + 1) (by simp at hi; omega) hdrop' restStack
        refine ⟨haltsWithin_singleton_of_eq hact hnextCfg hH, ?_⟩
        rw [List.length_cons, acceptCount_singleton_of_eq rfl hact hnextCfg]
        exact hC

private lemma dyck1_decides :
    dyck1AuxPDA.DecidesInTimeAndSpace encBits {w | dyck1Balance 0 w = true}
      (fun _ => 0) (fun w => w.length + 1) := by
  have hcounts : dyck1Counting.CountsInTimeAndSpace encBits
      (fun w => if dyck1Balance 0 w then 1 else 0) (fun _ => 0) (fun w => w.length + 1) := by
    intro w
    obtain ⟨hH, hC⟩ := dyck1_halts_and_count w w 0 (by simp) (by simp) []
    rw [← dyck1Cfg_init w] at hH hC
    exact ⟨AuxPDA.runsInSpace_zero_tapes _ _ _, hH, hC.symm⟩
  exact hcounts.decidesInTimeAndSpace fun w => by
    simp only [Set.mem_ofPred_eq]
    split_ifs <;> simp [*]

/-- Compiled normal-form circuit for `dyck1AuxPDA` on word `w`. -/
private abbrev dyck1Circuit (w : List Bool) :=
  compileAuxPDA dyck1AuxPDA unitEquivFin1 unitEquivFin1 w 0 (w.length + 1)

private abbrev dyck1Out (w : List Bool) :=
  compiledOutputGate 1 1 0 w.length 0 (w.length + 1)

/-- For every word `w`, the compiled `dyck1AuxPDA` circuit is strictly in `InNormalForm`, agrees
exactly with `dyck1Balance 0 w = true` and `dyck1AuxPDA.Accepts w`, and admits a min-isolating
Justesen seed. -/
private theorem dyck1Circuit_spec (w : List Bool) :
    (dyck1Circuit w).InNormalForm ∧
    ((dyck1Circuit w).Eval (dyck1Out w) ↔ dyck1AuxPDA.Accepts w) ∧
    ((dyck1Circuit w).Eval (dyck1Out w) ↔ dyck1Balance 0 w = true) ∧
    (∃ seed, (dyck1Circuit w).IsMinIsolating ((dyck1Circuit w).generatedGateWeight seed)) := by
  obtain ⟨hs, ht, hacc⟩ := dyck1_decides w
  have heval := compileAuxPDA_eval_iff dyck1AuxPDA unitEquivFin1 unitEquivFin1 w hs ht
  exact ⟨compileAuxPDA_inNormalForm dyck1AuxPDA unitEquivFin1 unitEquivFin1 w 0 (w.length + 1),
    heval, heval.trans hacc.symm,
    compileAuxPDA_exists_minIsolating_seed dyck1AuxPDA unitEquivFin1 unitEquivFin1 w 0
      (w.length + 1)⟩

/-- Concrete accepting and rejecting witnesses through the compiled normal-form circuit:
accepts `[]`, `()`, `(())`, and rejects `)`, `(`, `)(`. -/
example :
    (dyck1Circuit []).Eval (dyck1Out []) ∧
    (dyck1Circuit [false, true]).Eval (dyck1Out [false, true]) ∧
    (dyck1Circuit [false, false, true, true]).Eval (dyck1Out [false, false, true, true]) ∧
    ¬(dyck1Circuit [true]).Eval (dyck1Out [true]) ∧
    ¬(dyck1Circuit [false]).Eval (dyck1Out [false]) ∧
    ¬(dyck1Circuit [true, false]).Eval (dyck1Out [true, false]) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (dyck1Circuit_spec []).2.2.1.mpr (by decide)
  · exact (dyck1Circuit_spec [false, true]).2.2.1.mpr (by decide)
  · exact (dyck1Circuit_spec [false, false, true, true]).2.2.1.mpr (by decide)
  · intro h; exact absurd ((dyck1Circuit_spec [true]).2.2.1.mp h) (by decide)
  · intro h; exact absurd ((dyck1Circuit_spec [false]).2.2.1.mp h) (by decide)
  · intro h; exact absurd ((dyck1Circuit_spec [true, false]).2.2.1.mp h) (by decide)

/-- Computable `DecidableRel` on `(dyck1Circuit w).orChild` synthesizes cleanly and agrees with
`(dyck1Circuit w).orChild`. -/
example (w : List Bool)
    (g c : Fin (compiledGateCount 1 1 0 w.length 0 (w.length + 1))) :
    decide ((dyck1Circuit w).orChild g c) = true ↔ (dyck1Circuit w).orChild g c :=
  decide_eq_true_iff

/-! ## 3. End-to-end `LogCFL` certification witness on `dyck1` -/

example :
    ∃ (N : List Bool → ℕ)
      (C : ∀ w, LayeredSemiUnboundedCircuit (Fin (N w)))
      (out : ∀ w, Fin (N w)),
      PolyBounded (fun w => (encBits w).length) N ∧
      (∀ w, (C w).InNormalForm) ∧
      (∀ w, dyck1Balance 0 w = true ↔ (C w).Eval (out w)) ∧
      (∀ w, ∃ seed, (C w).IsMinIsolating ((C w).generatedGateWeight seed)) := by
  have hmem : {w | dyck1Balance 0 w = true} ∈ LogCFL encBits :=
    ⟨0, Unit, Unit, inferInstance, inferInstance, dyck1AuxPDA, 0, fun w => w.length + 1,
      PolyBounded.of_forall_le 1 1 fun w => by simp [encBits_apply],
      dyck1_decides.mono (fun _ => by simp) (fun _ => le_rfl)⟩
  obtain ⟨N, C, out, -, -, -, -, -, -, -, -, -, hpoly, hnorm, heval, -, hiso, -, -⟩ :=
    LogCFL.exists_normalForm_circuit_family_certified hmem
  exact ⟨N, C, out, hpoly, hnorm, heval, hiso⟩

end CslibFrontierTests.AuxPDACircuitCompiler
