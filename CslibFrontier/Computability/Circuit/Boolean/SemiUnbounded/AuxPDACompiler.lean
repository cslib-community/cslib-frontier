/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.SemiUnbounded.BalancedCircuit
public import CslibFrontier.Computability.Circuit.Boolean.SemiUnbounded.WeightGenerator
public import CslibFrontier.Computability.Machines.AuxPDA.BoundedSurface
public import CslibFrontier.Computability.Complexity.Classes.LogCFL

import CslibFrontier.Foundations.Data.Nat.Log
import Mathlib.Tactic.Ring

/-!
# Normal-form `AuxPDA → LayeredSemiUnboundedCircuit` compiler

This module implements Work Package 4 of cslib-frontier #7920: compiling any finite-state,
finite-stack-alphabet binary auxiliary pushdown automaton (`Turing.AuxPDA`) running within work
space `s` and all-branches time `t` on an input `w` into a strictly alternating AND-first-layer
normal-form layered semi-unbounded circuit (`LayeredSemiUnboundedCircuit (Fin N)`):

1. Normalize the machine via `Turing.AuxPDA.withEmptyStackHalt` so every accepting computation
   halts with an empty stack within `2 * t + 1` steps while preserving work space `s`.
2. Index all bounded-space surface configurations in `Turing.window s` onto `Fin S` via
   `Turing.AuxPDA.boundedSurfaceEquivFin` (`S = poly(n)` for `s = O(log n)`).
3. Compile bounded-space surface realizability via `Cslib.Circuits.Boolean.balancedCircuitFin`
   with `R = roundsForSize (4 * t + 3) = 6 * (Nat.log2 (4 * t + 3) + 1)` rounds (the balanced
   tree-contraction construction after Ruzzo (1980) and Venkateswaran (1991); locator not verified
   against primary PDF).

The compiled circuit:
* satisfies `LayeredSemiUnboundedCircuit.InNormalForm` unconditionally
  (`compileAuxPDA_inNormalForm`);
* satisfies `Eval outputGate ↔ M.Accepts input` under `M.RunsInSpace input s` and
  `M.RunsInTime input t`, with soundness needing neither bound (`compileAuxPDA_eval_sound`,
  `compileAuxPDA_eval_iff`);
* has polynomial gate count `N = poly(n)` and logarithmic AND-depth `O(log N)` whenever
  `s(n) = O(log n)` and `t(n) = poly(n)` (`compileAuxPDA_gateCount_polynomiallyBounded`,
  `compileAuxPDA_andLevel_le_log_gateCount`);
* feeds directly into Work Package 1's `exists_generatedGateWeight_isMinIsolating` and Work
  Package 2's `WeightGenerator.generatedGateWeight_certified` with zero stand-in hypotheses
  (`compileAuxPDA_exists_minIsolating_seed`, `LogCFL.exists_normalForm_circuit_family_certified`);
* provides a computable `DecidableRel` instance (`instDecidableOrChildCompileAuxPDA`) on the
  compiled circuit's `orChild` relation whenever `M.Tr` is decidable.

This is original formalization for Work Package 4 of cslib-frontier #7920 (not a registered cited
result). Native `ComputableInSpace` multi-tape Turing-machine witnesses for the gate-query
callback, unambiguous double-counting scans (`WeightCheck`/`WeightEval`), and the uniform
`LogCFL = UAuxPDA = coUAuxPDA` endpoint remain tracked in #7920.

## Main definitions

* `Cslib.Circuits.Boolean.AuxPDACompiler.compiledSurfaceCount`,
  `Cslib.Circuits.Boolean.AuxPDACompiler.compiledRounds`,
  `Cslib.Circuits.Boolean.AuxPDACompiler.compiledGateCount`: exact surface, round, and gate counts.
* `Cslib.Circuits.Boolean.AuxPDACompiler.compileAuxPDA`,
  `Cslib.Circuits.Boolean.AuxPDACompiler.compiledOutputGate`: the compiled normal-form circuit on
  `Fin N` and its output gate.

## Main results

* `Cslib.Circuits.Boolean.AuxPDACompiler.compileAuxPDA_inNormalForm`: strict normal form.
* `Cslib.Circuits.Boolean.AuxPDACompiler.compileAuxPDA_eval_sound`,
  `Cslib.Circuits.Boolean.AuxPDACompiler.compileAuxPDA_eval_iff`: exact acceptance equivalence.
* `Cslib.Circuits.Boolean.AuxPDACompiler.compileAuxPDA_andLevel_le_log_gateCount`,
  `Cslib.Circuits.Boolean.AuxPDACompiler.compileAuxPDA_gateCount_polynomiallyBounded`: logarithmic
  AND-depth and polynomial circuit size.
* `Cslib.Circuits.Boolean.AuxPDACompiler.compileAuxPDA_exists_minIsolating_seed`: direct
  instantiation of Work Package 1's min-isolation theorem.
* `Cslib.Circuits.Boolean.AuxPDACompiler.LogCFL.exists_normalForm_circuit_family_certified`:
  end-to-end Work Package 1 + 2 + 3 + 4 normal-form compilation and weight-generator certification
  for every language in `Cslib.Complexity.LogCFL`.

## References

* [W. M. Hoza, *Nondeterministic and Unambiguous Logarithmic Space*][Hoza2026NLUL]
* [K. Reinhardt, E. Allender, *Making Nondeterminism Unambiguous*][ReinhardtAllender2000]
-/

@[expose] public section

open _root_.Turing _root_.Turing.AuxPDA _root_.Turing.MultiTapeTM Cslib.Complexity
open Cslib.Circuits.Boolean.LayeredSemiUnboundedCircuit
open Cslib.Code.JustesenFamily Cslib.Reachability.Hoza

namespace Cslib.Circuits.Boolean.AuxPDACompiler

/-! ### Bounded-space realizability trees from concrete `SameHeightRun`s -/

section BoundedRealTree

variable {k : ℕ} {StackSym State : Type*} {input : List Bool} {s : ℕ}

/-- Transport a `RealTree` along a bijection on vertices. -/
private def realTreeMap {V V' : Type*} {stay : V → V → Prop}
    {pushPop : V → V → V → V → Prop} {stay' : V' → V' → Prop}
    {pushPop' : V' → V' → V' → V' → Prop}
    (f : V → V')
    (hstay : ∀ {u v}, stay u v → stay' (f u) (f v))
    (hpp : ∀ {u u' v' v}, pushPop u u' v' v → pushPop' (f u) (f u') (f v') (f v)) :
    {u v : V} → RealTree stay pushPop u v → RealTree stay' pushPop' (f u) (f v)
  | _, _, .refl u => .refl (f u)
  | _, _, .stay h => .stay (hstay h)
  | _, _, .pushPop h sub => .pushPop (hpp h) (realTreeMap f hstay hpp sub)
  | _, _, .trans l r => .trans (realTreeMap f hstay hpp l) (realTreeMap f hstay hpp r)

private lemma realTreeMap_size {V V' : Type*} {stay : V → V → Prop}
    {pushPop : V → V → V → V → Prop} {stay' : V' → V' → Prop}
    {pushPop' : V' → V' → V' → V' → Prop}
    (f : V → V')
    (hstay : ∀ {u v}, stay u v → stay' (f u) (f v))
    (hpp : ∀ {u u' v' v}, pushPop u u' v' v → pushPop' (f u) (f u') (f v') (f v))
    {u v : V} (T : RealTree stay pushPop u v) :
    (realTreeMap f hstay hpp T).size = T.size := by
  induction T <;> simp_all [realTreeMap, RealTree.size]

private lemma realTree_cast {V : Type*} {stay : V → V → Prop}
    {pushPop : V → V → V → V → Prop} {u v : V} (u' v' : V) (hu : u = u') (hv : v = v')
    (T : RealTree stay pushPop u v) :
    ∃ T' : RealTree stay pushPop u' v', T'.size = T.size := by
  subst hu hv; exact ⟨T, rfl⟩

/-- Every bounded realizability tree lifts to an `AuxPDA.Realizable` witness. -/
theorem realTree_toRealizable {M : AuxPDA k Bool StackSym State}
    {u v : BoundedSurfaceCfg k StackSym State input s}
    (T : RealTree (M.BoundedStayStep (input := input) (s := s))
      (M.BoundedPushPopStep (input := input) (s := s)) u v) :
    ∃ d, M.Realizable input u.toSurface v.toSurface d := by
  induction T with
  | refl u => exact ⟨0, .refl u.toSurface⟩
  | stay h => exact ⟨1, .stay h⟩
  | pushPop h _ ih =>
    obtain ⟨γ, hp, hq⟩ := h
    obtain ⟨d, hd⟩ := ih
    exact ⟨d + 2, .pushPop hp hd hq⟩
  | trans _ _ ihl ihr =>
    obtain ⟨d₁, h₁⟩ := ihl
    obtain ⟨d₂, h₂⟩ := ihr
    exact ⟨d₁ + d₂, .trans h₁ h₂⟩

private lemma stayStep_of_sameHeightRun_length_one {M : AuxPDA k Bool StackSym State}
    (p : M.RunPath input) (hlen : p.length = 1) (hsame : SameHeightRun p) :
    M.StayStep p.head.surface p.last.surface := by
  have hstep : M.Step p.head p.last := by
    have hs : M.Step (p ⟨0, by omega⟩) (p ⟨1, by omega⟩) := p.step ⟨0, by omega⟩
    rwa [show p ⟨1, by omega⟩ = p.last from congrArg p (Fin.ext (by change 1 = p.length; omega))]
      at hs
  cases hq : p.head.tapes.state with
  | none => exact .inl ⟨hq, congrArg Cfg.surface ((AuxPDA.step_of_halt hq).mp hstep)⟩
  | some q =>
    simp only [Step, hq] at hstep
    obtain ⟨act, htr, hact⟩ := hstep
    obtain ⟨stack', hstack, hpLast⟩ := Action.apply?_eq_some_iff.mp hact
    have hlenEq := hsame.1
    cases hop : act.stackOp with
    | stay =>
      rw [hop, StackOp.apply?_stay, Option.some.injEq] at hstack
      subst hstack
      exact .inr ⟨q, act, hq, htr, hop,
        hpLast.symm ▸ surface_apply_eq_applySurfaceTapes act.tape p.head p.head.stack⟩
    | push γ =>
      rw [hop, StackOp.apply?_push, Option.some.injEq] at hstack
      subst hstack; simp [hpLast] at hlenEq
    | pop =>
      cases hst : p.head.stack with
      | nil => simp [hop, hst] at hstack
      | cons _ _ =>
        rw [hop, hst, StackOp.apply?_pop_cons, Option.some.injEq] at hstack
        subst hstack; simp [hpLast, hst] at hlenEq

private lemma exists_boundedRealTree_of_sameHeightRun {M : AuxPDA k Bool StackSym State} (d : ℕ) :
    ∀ (p : M.RunPath input), p.length = d → SameHeightRun p →
      (hfits : ∀ c ∈ p, c.surface.storage.FitsIn (fun _ => s)) →
      ∃ T : RealTree (M.BoundedStayStep (input := input) (s := s))
          (M.BoundedPushPopStep (input := input) (s := s))
          (BoundedSurfaceCfg.ofSurface p.head.surface (hfits p.head p.head_mem))
          (BoundedSurfaceCfg.ofSurface p.last.surface (hfits p.last p.last_mem)),
        T.size ≤ max 1 (2 * d - 1) := by
  induction d using Nat.strong_induction_on with
  | ind d ih =>
    intro p hlen hsame hfits
    match d with
    | 0 =>
      obtain ⟨T, hT⟩ := realTree_cast _
        (BoundedSurfaceCfg.ofSurface p.last.surface (hfits p.last p.last_mem)) rfl
        (BoundedSurfaceCfg.toSurface_injective
          (by simp [show p.last = p.head from congrArg p (Fin.ext hlen)]))
        (.refl (BoundedSurfaceCfg.ofSurface p.head.surface (hfits p.head p.head_mem)))
      exact ⟨T, hT.le.trans (le_max_left 1 _)⟩
    | 1 =>
      refine ⟨.stay ?_, ?_⟩
      · unfold BoundedStayStep
        simpa only [BoundedSurfaceCfg.toSurface_ofSurface] using
          stayStep_of_sameHeightRun_length_one p hlen hsame
      · rfl
    | d' + 2 =>
      rcases sameHeightRun_split_ge_two p hlen hsame with
        ⟨j, hjpos, hjlt, h1, h2⟩ |
        ⟨γ, pmid, hmidLen, hmidSame, hmidSub, hmidHeadStack, hpush, hpopFn⟩
      · have hfits1 : ∀ c ∈ p.take j, c.surface.storage.FitsIn (fun _ => s) := fun c ⟨i, hi⟩ =>
          hfits c ⟨Fin.castLE j.isLt i, hi⟩
        have hfits2 : ∀ c ∈ p.drop j, c.surface.storage.FitsIn (fun _ => s) :=
          fun c ⟨⟨iv, hiv⟩, hi⟩ => by
            dsimp only [RelSeries.drop] at hiv hi
            exact hfits c ⟨⟨iv + j.val, by omega⟩, hi⟩
        obtain ⟨T₁, hsz₁⟩ := ih j.val (by omega) (p.take j) rfl h1 hfits1
        obtain ⟨T₂, hsz₂⟩ := ih (p.length - j.val) (by omega) (p.drop j)
          (RelSeries.drop_length p j) h2 hfits2
        obtain ⟨T₁', hsz₁'⟩ := realTree_cast
          (BoundedSurfaceCfg.ofSurface p.head.surface (hfits p.head p.head_mem))
          (BoundedSurfaceCfg.ofSurface (p.drop j).head.surface (hfits2 _ (p.drop j).head_mem))
          (BoundedSurfaceCfg.toSurface_injective (by simp [RelSeries.head_take]))
          (BoundedSurfaceCfg.toSurface_injective
            (by simp [RelSeries.last_take, RelSeries.head_drop])) T₁
        obtain ⟨T₂', hsz₂'⟩ := realTree_cast _
          (BoundedSurfaceCfg.ofSurface p.last.surface (hfits p.last p.last_mem)) rfl
          (BoundedSurfaceCfg.toSurface_injective (by simp [RelSeries.last_drop])) T₂
        exact ⟨.trans T₁' T₂', by simp only [RealTree.size]; omega⟩
      · have hfitsMid : ∀ c ∈ pmid, c.surface.storage.FitsIn (fun _ => s) := fun c hc =>
          hfits c (hmidSub c hc)
        obtain ⟨Tmid, hszMid⟩ := ih d' (by omega) pmid hmidLen hmidSame hfitsMid
        obtain ⟨-, hpop⟩ := hpopFn (hmidSame.last_stack_eq.trans hmidHeadStack)
        refine ⟨.pushPop ⟨γ, ?_, ?_⟩ Tmid, ?_⟩
        · unfold BoundedPushStep; simpa only [BoundedSurfaceCfg.toSurface_ofSurface] using hpush
        · unfold BoundedPopStep
          rw [BoundedSurfaceCfg.toSurface_ofSurface, BoundedSurfaceCfg.toSurface_ofSurface]
          exact hpop
        · simp only [RealTree.size]; omega

/-- Every configuration along a computation path of a space-`s`-bounded `AuxPDA` fits in
`Turing.window s`. -/
private lemma computationPath_mem_fitsIn {M : AuxPDA k Bool StackSym State}
    (hs : M.RunsInSpace input s) (p : M.ComputationPath input) :
    ∀ c ∈ p.toRunPath, c.surface.storage.FitsIn (fun _ => s) := by
  rintro c ⟨i, rfl⟩
  let pi : M.ComputationPath input :=
    ⟨p.toRunPath.take i, by rw [RelSeries.head_take]; exact p.head_eq⟩
  have hle : ∀ j, pi.spaceUsedByTape j ≤ s := fun j =>
    (Finset.single_le_sum (fun m _ => Nat.zero_le _) (Finset.mem_univ j)).trans (hs pi)
  exact RelSeries.last_take p.toRunPath i ▸ Turing.Storage.FitsIn_mono hle pi.storage_fitsIn

private lemma accepts_of_boundedRealTree {M : AuxPDA k Bool StackSym State}
    {v : BoundedSurfaceCfg k StackSym (Option State) input s}
    (hv : v.IsAcceptingEmpty)
    (T : RealTree (M.withEmptyStackHalt.BoundedStayStep (input := input) (s := s))
      (M.withEmptyStackHalt.BoundedPushPopStep (input := input) (s := s))
      (initBoundedSurface M.withEmptyStackHalt input s) v) :
    M.Accepts input := by
  obtain ⟨d, hd⟩ := realTree_toRealizable T
  rw [toSurface_initBoundedSurface] at hd
  exact withEmptyStackHalt_accepts_iff.mp <|
    (accepts_iff_exists_realizable_of_emptyStackHalt withEmptyStackHalt_halted_stack_nil).mpr
      ⟨v.toSurface, d, hv.1, hv.2, hd⟩

/-- **Bounded realizability tree characterization of `AuxPDA` acceptance**: under work space `s`
and all-branches time `t`, `M` accepts `input` iff `M.withEmptyStackHalt` has a bounded
realizability tree of size at most `4 * t + 3` from `initBoundedSurface` to an empty-stack
accepting bounded surface configuration. -/
theorem accepts_iff_exists_boundedRealTree {M : AuxPDA k Bool StackSym State} {t : ℕ}
    (hs : M.RunsInSpace input s) (ht : M.RunsInTime input t) :
    M.Accepts input ↔
      ∃ (v : BoundedSurfaceCfg k StackSym (Option State) input s),
        v.IsAcceptingEmpty ∧
        ∃ T : RealTree (M.withEmptyStackHalt.BoundedStayStep (input := input) (s := s))
            (M.withEmptyStackHalt.BoundedPushPopStep (input := input) (s := s))
            (initBoundedSurface M.withEmptyStackHalt input s) v,
          T.size ≤ 4 * t + 3 := by
  refine ⟨fun hacc => ?_, fun ⟨v, hvAcc, T, _⟩ => accepts_of_boundedRealTree hvAcc T⟩
  obtain ⟨p, hhalt, hout⟩ := withEmptyStackHalt_accepts_iff.mpr hacc
  have hs' := withEmptyStackHalt_runsInSpace hs
  have ht' := withEmptyStackHalt_runsInTime ht
  obtain ⟨q, hqLen, hqHalt, hqOut⟩ :
      ∃ q : M.withEmptyStackHalt.ComputationPath input,
        q.length ≤ 2 * t + 1 ∧ q.last.Halted ∧ q.last.tapes.output = [true] := by
    by_cases hle : p.length ≤ 2 * t + 1
    · exact ⟨p, hle, hhalt, hout⟩
    · let j : Fin (p.length + 1) := ⟨2 * t + 1, by omega⟩
      let q : M.withEmptyStackHalt.ComputationPath input :=
        ⟨p.toRunPath.take j, by rw [RelSeries.head_take]; exact p.head_eq⟩
      have hqHalt : q.last.Halted := ht' q (by simp [q, ComputationPath.time, RunPath.time, j])
      have hlastEq : p.last = q.last := by
        simpa [q, RelSeries.last_take] using RunPath.last_eq_of_halted p.toRunPath j
          (by simpa [q, RelSeries.last_take] using hqHalt)
      exact ⟨q, by simp [q, j], hqHalt, hlastEq ▸ hout⟩
  have hstack : q.last.stack = [] := withEmptyStackHalt_halted_stack_nil q hqHalt
  have hsame : SameHeightRun q.toRunPath :=
    ⟨by simp [hstack, q.head_eq], fun _ => by simp [q.head_eq]⟩
  have hfits := computationPath_mem_fitsIn hs' q
  obtain ⟨T, hsz⟩ := exists_boundedRealTree_of_sameHeightRun q.length q.toRunPath rfl hsame hfits
  let v := BoundedSurfaceCfg.ofSurface q.toRunPath.last.surface
    (hfits q.toRunPath.last q.toRunPath.last_mem)
  obtain ⟨T', hsz'⟩ := realTree_cast (initBoundedSurface M.withEmptyStackHalt input s) v
    (BoundedSurfaceCfg.toSurface_injective (by simp [q.head_eq]; rfl)) rfl T
  refine ⟨v, ⟨?_, by change q.last.stack.head? = none; simp [hstack]⟩, T', by omega⟩
  change v.toSurface.IsAccepting
  rw [BoundedSurfaceCfg.toSurface_ofSurface, Cfg.isAccepting_surface_iff]
  exact ⟨hqHalt, hqOut⟩

end BoundedRealTree

/-! ### Normal-form `AuxPDA → LayeredSemiUnboundedCircuit (Fin N)` compiler -/

section Compiler

/-- Number of bounded surface configurations of `M.withEmptyStackHalt` on inputs of length `n` in
space `s`. -/
def compiledSurfaceCount (mStack mState k n s : ℕ) : ℕ :=
  boundedSurfaceCard mStack (mState + 1) k n s

/-- Number of balanced-contraction rounds for an `AuxPDA` time bound `t`. -/
def compiledRounds (t : ℕ) : ℕ :=
  roundsForSize (4 * t + 3)

/-- Total number of gates in the compiled normal-form semi-unbounded circuit. -/
def compiledGateCount (mStack mState k n s t : ℕ) : ℕ :=
  balancedGateCount (compiledSurfaceCount mStack mState k n s) (compiledRounds t)

variable {k mStack mState : ℕ} {StackSym State : Type*}

/-- Bijection between bounded surface configurations of `M.withEmptyStackHalt` and
`Fin (compiledSurfaceCount mStack mState k input.length s)`. -/
def drainSurfaceEquivFin (eStack : StackSym ≃ Fin mStack) (eState : State ≃ Fin mState)
    (input : List Bool) (s : ℕ) :
    BoundedSurfaceCfg k StackSym (Option State) input s ≃
      Fin (compiledSurfaceCount mStack mState k input.length s) :=
  boundedSurfaceEquivFin eStack ((Equiv.optionCongr eState).trans (finSuccEquiv mState).symm)
    input s

/-- Compile an `AuxPDA` (together with finite encodings of its stack alphabet and state set, input
word, work-space bound `s`, and time bound `t`) into an alternating AND-first-layer normal-form
`LayeredSemiUnboundedCircuit` on `Fin (compiledGateCount …)`. -/
def compileAuxPDA (M : AuxPDA k Bool StackSym State)
    (eStack : StackSym ≃ Fin mStack) (eState : State ≃ Fin mState)
    (input : List Bool) (s t : ℕ) :
    LayeredSemiUnboundedCircuit (Fin (compiledGateCount mStack mState k input.length s t)) :=
  let e := drainSurfaceEquivFin (k := k) eStack eState input s
  let M' := M.withEmptyStackHalt
  balancedCircuitFin
    (e (initBoundedSurface M' input s))
    (fun v => (e.symm v).IsAcceptingEmpty)
    (fun u v => M'.BoundedStayStep (e.symm u) (e.symm v))
    (fun u u' v' v => M'.BoundedPushPopStep (e.symm u) (e.symm u') (e.symm v') (e.symm v))
    (compiledRounds t)

/-- The output gate index of `compileAuxPDA`. -/
def compiledOutputGate (mStack mState k n s t : ℕ) :
    Fin (compiledGateCount mStack mState k n s t) :=
  balancedOutputGate (compiledSurfaceCount mStack mState k n s) (compiledRounds t)

/-- `compileAuxPDA` is unconditionally in strict alternating AND-first-layer normal form
(`InNormalForm`), so Work Package 1 (`exists_generatedGateWeight_isMinIsolating`) and Work Package 2
(`generatedGateWeight_certified`) apply directly. -/
theorem compileAuxPDA_inNormalForm (M : AuxPDA k Bool StackSym State)
    (eStack : StackSym ≃ Fin mStack) (eState : State ≃ Fin mState)
    (input : List Bool) (s t : ℕ) :
    (compileAuxPDA M eStack eState input s t).InNormalForm :=
  balancedCircuitFin_inNormalForm _ _ _ _ _

/-- **Soundness of `compileAuxPDA`** (no space or time hypothesis needed): if the compiled output
gate evaluates to `true`, then `M` accepts `input`. -/
theorem compileAuxPDA_eval_sound (M : AuxPDA k Bool StackSym State)
    (eStack : StackSym ≃ Fin mStack) (eState : State ≃ Fin mState)
    (input : List Bool) (s t : ℕ)
    (h : (compileAuxPDA M eStack eState input s t).Eval
      (compiledOutputGate mStack mState k input.length s t)) :
    M.Accepts input := by
  obtain ⟨v, hvAcc, ⟨T⟩⟩ := balancedCircuitFin_eval_output_sound h
  have Tsurf := realTreeMap (drainSurfaceEquivFin (k := k) eStack eState input s).symm id id T
  rw [Equiv.symm_apply_apply] at Tsurf
  exact accepts_of_boundedRealTree hvAcc Tsurf

/-- **Exact acceptance equivalence for `compileAuxPDA`**: under `M.RunsInSpace input s` and
`M.RunsInTime input t`, the compiled normal-form circuit evaluates to `true` at its output gate
iff `M` accepts `input`. -/
theorem compileAuxPDA_eval_iff (M : AuxPDA k Bool StackSym State)
    (eStack : StackSym ≃ Fin mStack) (eState : State ≃ Fin mState)
    (input : List Bool) {s t : ℕ}
    (hs : M.RunsInSpace input s) (ht : M.RunsInTime input t) :
    (compileAuxPDA M eStack eState input s t).Eval
      (compiledOutputGate mStack mState k input.length s t) ↔ M.Accepts input := by
  refine ⟨compileAuxPDA_eval_sound M eStack eState input s t, fun hacc => ?_⟩
  let e := drainSurfaceEquivFin (k := k) eStack eState input s
  obtain ⟨v, hvAcc, T, hsz⟩ := (accepts_iff_exists_boundedRealTree hs ht).mp hacc
  exact balancedCircuitFin_eval_output_complete (sz := 4 * t + 3) le_rfl
    (by simpa only [e, Equiv.symm_apply_apply] using hvAcc)
    (realTreeMap e
      (fun h => by simpa only [e, Equiv.symm_apply_apply] using h)
      (fun h => by simpa only [e, Equiv.symm_apply_apply] using h) T)
    (by rwa [realTreeMap_size])

/-! ### Logarithmic AND-depth and polynomial size bounds -/

/-- Every gate of `compileAuxPDA` has AND-level at most `compiledRounds t + 2`. -/
theorem compileAuxPDA_andLevel_le (M : AuxPDA k Bool StackSym State)
    (eStack : StackSym ≃ Fin mStack) (eState : State ≃ Fin mState)
    (input : List Bool) (s t : ℕ)
    (g : Fin (compiledGateCount mStack mState k input.length s t)) :
    (compileAuxPDA M eStack eState input s t).andLevel g ≤ compiledRounds t + 2 :=
  balancedCircuitFin_andLevel_le _ _ _ _ _ g

/-- Explicit logarithmic AND-depth constant for a polynomial time bound `t ≤ A * (n + 1) ^ D`. -/
def depthConstant (A D : ℕ) : ℕ :=
  6 * (Nat.log2 (4 * A + 3) + 1) + 6 * D + 8

/-- **Logarithmic AND-depth in terms of circuit size `N`**: whenever
`t ≤ A * (input.length + 1) ^ D`, every gate of `compileAuxPDA` has
`andLevel g ≤ depthConstant A D * (Nat.log2 N + 1)`. -/
theorem compileAuxPDA_andLevel_le_log_gateCount (M : AuxPDA k Bool StackSym State)
    (eStack : StackSym ≃ Fin mStack) (eState : State ≃ Fin mState)
    (input : List Bool) (s t A D : ℕ) (ht : t ≤ A * (input.length + 1) ^ D)
    (g : Fin (compiledGateCount mStack mState k input.length s t)) :
    (compileAuxPDA M eStack eState input s t).andLevel g ≤
      depthConstant A D * (Nat.log2 (compiledGateCount mStack mState k input.length s t) + 1) := by
  let N := compiledGateCount mStack mState k input.length s t
  let L := Nat.log2 N + 1
  let B := Nat.log2 (4 * A + 3) + 1
  have hSge : input.length + 2 ≤ compiledSurfaceCount mStack mState k input.length s :=
    input_length_add_two_le_boundedSurfaceCard mStack (mState + 1) k input.length s
  have hNge : compiledSurfaceCount mStack mState k input.length s + 3 ≤ N :=
    le_balancedGateCount _ _
  have hltN : N < 2 ^ L := Nat.lt_log2_self
  have hn1lt : input.length + 1 < 2 ^ L := by omega
  have hAlt : 4 * A + 3 < 2 ^ B := Nat.lt_log2_self
  have h1lePow : 1 ≤ (input.length + 1) ^ D := Nat.one_le_pow _ _ (Nat.succ_pos _)
  have h4t3 : 4 * t + 3 < 2 ^ (B + D * L) := calc
    4 * t + 3 ≤ (4 * A + 3) * (input.length + 1) ^ D := by nlinarith
    _ < 2 ^ B * (2 ^ L) ^ D :=
        (Nat.mul_lt_mul_of_pos_right hAlt (by positivity)).trans_le
          (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hn1lt.le D))
    _ = 2 ^ (B + D * L) := by rw [← pow_mul, ← pow_add, Nat.mul_comm L D]
  have hlogLe : Nat.log2 (4 * t + 3) ≤ B + D * L := by
    rw [Nat.log2_eq_log_two]
    exact Nat.le_of_lt_succ (Nat.log_lt_of_lt_pow (by omega) (by rw [pow_succ']; omega))
  refine (compileAuxPDA_andLevel_le M eStack eState input s t g).trans ?_
  unfold compiledRounds roundsForSize depthConstant
  have : 1 ≤ L := Nat.succ_pos _
  dsimp only [B, L, N] at hlogLe this ⊢
  nlinarith

/-- **Polynomial compiled gate count in logarithmic space and polynomial time**: when
`s(n) = c * (Nat.log2 n + 1)` and `t(n) = A * (n + 1) ^ D`, `compiledGateCount` is polynomially
bounded in `n`. -/
theorem compileAuxPDA_gateCount_polynomiallyBounded (mStack mState k c A D : ℕ) :
    Cslib.PolynomiallyBounded fun n =>
      compiledGateCount mStack mState k n (c * (Nat.log2 n + 1)) (A * (n + 1) ^ D) := by
  open Cslib.PolynomiallyBounded in
  have hS : Cslib.PolynomiallyBounded fun n =>
      compiledSurfaceCount mStack mState k n (c * (Nat.log2 n + 1)) :=
    boundedSurfaceCard_log_polynomiallyBounded mStack (mState + 1) k c
  have hR : Cslib.PolynomiallyBounded fun n => compiledRounds (A * (n + 1) ^ D) := by
    refine ((Cslib.PolynomiallyBounded.const 6).mul
      (((Cslib.PolynomiallyBounded.const 4).mul ((Cslib.PolynomiallyBounded.const A).mul
        ((Cslib.PolynomiallyBounded.id.add (Cslib.PolynomiallyBounded.const 1)).pow D))).add
          (Cslib.PolynomiallyBounded.const 4))).mono_of_le fun n => ?_
    unfold compiledRounds roundsForSize
    rw [Nat.log2_eq_log_two]
    exact Nat.mul_le_mul_left 6 (Nat.succ_le_succ (Nat.log_le_self 2 _))
  exact (((Cslib.PolynomiallyBounded.const 6).mul
    (hR.add (Cslib.PolynomiallyBounded.const 1))).mul
      ((hS.add (Cslib.PolynomiallyBounded.const 1)).pow 6)).mono_of_le
        fun n => balancedGateCount_le _ _

/-! ### Direct bridge to Work Packages 1 & 2 (`MinIsolation` and `WeightGenerator`) -/

/-- **Direct Work Package 1 bridge**: every compiled `AuxPDA` circuit admits a min-isolating
Justesen seed of length `O(log N)`. -/
theorem compileAuxPDA_exists_minIsolating_seed (M : AuxPDA k Bool StackSym State)
    (eStack : StackSym ≃ Fin mStack) (eState : State ≃ Fin mState)
    (input : List Bool) (s t : ℕ) :
    ∃ seed,
      (compileAuxPDA M eStack eState input s t).IsMinIsolating
        ((compileAuxPDA M eStack eState input s t).generatedGateWeight seed) :=
  (compileAuxPDA M eStack eState input s t).exists_generatedGateWeight_isMinIsolating
    (compileAuxPDA_inNormalForm M eStack eState input s t)

/-- **End-to-end Work Package 1 + 2 + 3 + 4 certification for `LogCFL`**: every language
`A ∈ LogCFL enc` compiles to a family of strictly normal-form layered semi-unbounded circuits
`C a : LayeredSemiUnboundedCircuit (Fin (N a))` with polynomially bounded size `N a`, logarithmic
AND-depth `O(log (N a))`, exact acceptance `a ∈ A ↔ (C a).Eval (out a)`, a min-isolating Justesen
seed of length `O(log (N a))` on every instance, polynomial gate weights, and one fixed native
deterministic multi-tape Turing machine evaluating every generated gate weight in logarithmic
workspace `O(log (N a))`. -/
theorem LogCFL.exists_normalForm_circuit_family_certified {α : Type} {enc : α ↪ List Bool}
    {A : Set α} (hA : A ∈ LogCFL enc) :
    ∃ (N : α → ℕ)
      (C : ∀ a, LayeredSemiUnboundedCircuit (Fin (N a)))
      (out : ∀ a, Fin (N a))
      (depthFactor seedFactor spaceFactor weightDegree : ℕ)
      (time : WeightGenerator.Input → ℕ) (kw : ℕ) (StateW : Type) (_ : Finite StateW)
      (tm : MultiTapeTM kw Bool StateW),
      PolyBounded (fun a => (enc a).length) N ∧
      (∀ a, (C a).InNormalForm) ∧
      (∀ a, a ∈ A ↔ (C a).Eval (out a)) ∧
      (∀ a, codeLength (N a) 0 ≤ seedFactor * (Nat.log2 (N a) + 1)) ∧
      (∀ a, ∃ seed, (C a).IsMinIsolating ((C a).generatedGateWeight seed)) ∧
      (∀ a (g : Fin (N a)), (C a).andLevel g ≤ depthFactor * (Nat.log2 (N a) + 1)) ∧
      (∀ a (seed : Fin (codeLength (N a) 0) → Bool) (g : Fin (N a)),
        let input := WeightGenerator.canonicalInput (C a) seed g
        (C a).generatedGateWeight seed g < 6 ^ ((C a).andLevel g + codeLength (N a) 0) ∧
        (C a).generatedGateWeight seed g < (2 * (N a + 1)) ^ weightDegree ∧
        tm.ComputesInTimeAndSpace (WeightGenerator.encInput input)
          (encNat ((C a).generatedGateWeight seed g))
          (time input) (spaceFactor * (depthFactor + 1) * (Nat.log2 (N a) + 1))) := by
  classical
  rcases hA with ⟨k, StackSym, State, hfinStack, hfinState, M, cs, t, hpolyT, hdec⟩
  cases nonempty_fintype StackSym; cases nonempty_fintype State
  let eStack := Fintype.equivFin StackSym
  let eState := Fintype.equivFin State
  obtain ⟨At, Dt, htLe⟩ := hpolyT.exists_le
  let sFn (n : ℕ) := cs * (Nat.log2 n + 1)
  let tFn (n : ℕ) := At * (n + 1) ^ Dt
  let N (a : α) := compiledGateCount (Fintype.card StackSym) (Fintype.card State) k
    (enc a).length (sFn (enc a).length) (tFn (enc a).length)
  let C (a : α) := compileAuxPDA M eStack eState (enc a) (sFn (enc a).length) (tFn (enc a).length)
  let out (a : α) := compiledOutputGate (Fintype.card StackSym) (Fintype.card State) k
    (enc a).length (sFn (enc a).length) (tFn (enc a).length)
  let df := depthConstant At Dt
  obtain ⟨sf, spf, wdFn, time, kw, StateW, hfinW, tm, hcert⟩ :=
    WeightGenerator.generatedGateWeight_certified
  have hdepth (a : α) (g : Fin (N a)) : (C a).andLevel g ≤ df * (Nat.log2 (N a) + 1) :=
    compileAuxPDA_andLevel_le_log_gateCount M eStack eState (enc a) _ _ At Dt le_rfl g
  refine ⟨N, C, out, df, sf, spf, wdFn df, time, kw, StateW, hfinW, tm,
    PolyBounded.of_polynomiallyBounded _
      (compileAuxPDA_gateCount_polynomiallyBounded _ _ k cs At Dt),
    fun a => compileAuxPDA_inNormalForm M eStack eState (enc a) _ _,
    fun a => let ⟨hs, ht, hacc⟩ := hdec a
      hacc.trans (compileAuxPDA_eval_iff M eStack eState (enc a) hs (ht.mono (htLe a))).symm,
    fun a => (hcert (N a)).1,
    fun a => (hcert (N a)).2.1 (C a) (compileAuxPDA_inNormalForm M eStack eState (enc a) _ _),
    hdepth, fun a seed g => (hcert (N a)).2.2 df (C a) seed g (hdepth a g)⟩

/-! ### Computable `orChild` decidability on `compileAuxPDA` -/

/-- Computable decidability of the `orChild` relation of `compileAuxPDA` whenever `M.Tr` is
decidable over finite `StackSym` and `State`. -/
instance instDecidableOrChildCompileAuxPDA {StackSym State : Type}
    [Fintype StackSym] [Fintype State] [DecidableEq StackSym] [DecidableEq State]
    (M : AuxPDA k Bool StackSym State)
    [∀ q inp work top act, Decidable (M.Tr q inp work top act)]
    (eStack : StackSym ≃ Fin mStack) (eState : State ≃ Fin mState)
    (input : List Bool) (s t : ℕ) :
    DecidableRel (compileAuxPDA M eStack eState input s t).orChild :=
  let e := drainSurfaceEquivFin (k := k) eStack eState input s
  let M' := M.withEmptyStackHalt
  letI : ∀ q inp work top act, Decidable (M'.Tr q inp work top act) := inferInstance
  letI : ∀ u v, Decidable (M'.BoundedStayStep (input := input) (s := s) u v) := inferInstance
  letI : ∀ u u' v' v, Decidable (M'.BoundedPushPopStep (input := input) (s := s) u u' v' v) :=
    inferInstance
  instDecidableOrChildBalancedCircuitFin (e (initBoundedSurface M' input s))
    (fun v => (e.symm v).IsAcceptingEmpty)
    (fun u v => M'.BoundedStayStep (e.symm u) (e.symm v))
    (fun u u' v' v => M'.BoundedPushPopStep (e.symm u) (e.symm u') (e.symm v') (e.symm v))
    (compiledRounds t)

end Compiler

end Cslib.Circuits.Boolean.AuxPDACompiler
