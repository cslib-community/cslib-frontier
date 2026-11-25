/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.SingleTape.HeadRange
public import CslibFrontier.Computability.Machines.Turing.TM2.Reverse.Transfer
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString

/-!
# Single-tape space bounds from finite stack machines

The standard Mathlib stack-machine compiler preserves polynomial stack space. The bound includes
all elementary single-tape moves, and its terminal configuration stores the canonical source
output with the head back at the stack-bottom marker.

## Main results

* `Turing.FinTM2.outputs_toTM0`: the path uses a finite control type.
* `Turing.TM2Computable.toTM0_bool`: the canonical true output characterizes Boolean acceptance.
* `Cslib.Complexity.mem_PSPACE_exists_boundedTM0`: standard PSPACE machines have such realizations.
-/

public section

attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.σFin

open Relation StateTransition

namespace Turing

private theorem evalsTo_reaches {α : Type*} {f : α → Option α} {a b : α}
    (h : EvalsTo f a (some b)) : Reaches f a b := by
  obtain ⟨n, hn⟩ := h
  induction n generalizing b with
  | zero => exact Option.some.inj hn ▸ .refl
  | succ n ih =>
    rw [Function.iterate_succ_apply'] at hn
    change ((fun o : Option α => o.bind f)^[n] (some a)).bind f = some b at hn
    rcases he : (fun o : Option α => o.bind f)^[n] (some a) with _ | c <;>
      simp only [he, Option.bind_none, Option.bind_some, reduceCtorEq] at hn
    exact (ih he).tail hn

private theorem reachable_index {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
    {M : Λ → TM2.Stmt Γ Λ σ} {c d : TM2.Cfg Γ Λ σ} (h : TM2.Reaches M c d) :
    ∃ n, (TM2.stepTotal M)^[n] c = d := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | tail _ hs ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, by rw [Function.iterate_succ_apply', hn, TM2.stepTotal_of_step, hs]; rfl⟩

namespace FinTM2

variable (tm : FinTM2)

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime

/-- Finite set of program-counter and register states used by the standard single-tape compiler. -/
noncomputable def toTM0States : Finset (TM1to0.Λ' (TM2to1.tr tm.m)) :=
  TM1to0.trStmts (TM2to1.tr tm.m) (TM2to1.trSupp tm.m Finset.univ)

/-- The standard single-tape compiler only uses its finite set of translated statements. -/
theorem toTM0_supports :
    letI : Inhabited tm.Λ := ⟨tm.main⟩
    TM0.Supports (TM1to0.tr (TM2to1.tr tm.m)) (↑(toTM0States tm) : Set _) := by
  let : Inhabited tm.Λ := ⟨tm.main⟩
  classical
  have hs : TM2.Supports tm.m Finset.univ := by
    refine ⟨Finset.mem_univ _, fun l _ => ?_⟩
    generalize tm.m l = q
    induction q with
    | push k f q ih | peek k f q ih | pop k f q ih | load f q ih => exact ih
    | branch f q r ihq ihr => exact ⟨ihq, ihr⟩
    | goto f => exact fun _ => Finset.mem_univ _
    | halt => trivial
  exact TM1to0.tr_supports (TM2to1.tr tm.m) (TM2to1.tr_supports tm.m hs)

/-- The finite control of a compiled stack machine, obtained by restricting to translated
substatements and register values. -/
abbrev TM0Control := ↥(↑(toTM0States tm) : Set (TM1to0.Λ' (TM2to1.tr tm.m)))

noncomputable instance : Fintype (TM0Control tm) := by
  classical
  infer_instance

noncomputable instance : Inhabited (TM0Control tm) :=
  letI : Inhabited tm.Λ := ⟨tm.main⟩
  ⟨⟨default, (toTM0_supports tm).1⟩⟩

/-- The standard Mathlib compiler with its finite program-counter support as the control type. -/
noncomputable def toTM0 : TM0.Machine (TM2to1.Γ' tm.K tm.Γ) (TM0Control tm) :=
  letI : Inhabited tm.Λ := ⟨tm.main⟩
  TM0.restrict (TM1to0.tr (TM2to1.tr tm.m)) (toTM0_supports tm)

/-- The canonical halted control belongs to the compiler's finite support. -/
theorem halt_mem_toTM0States :
    (none, tm.initialState) ∈ toTM0States tm := by
  classical
  exact Finset.mem_product.mpr ⟨Finset.none_mem_insertNone, Finset.mem_univ _⟩

/-- Canonical halted configuration of the finite-control compiler. -/
@[expose] def toTM0Halt (output : List (tm.Γ tm.k₁)) :
    TM0.Cfg (TM2to1.Γ' tm.K tm.Γ) (TM0Control tm) :=
  ⟨⟨(none, tm.initialState), halt_mem_toTM0States tm⟩,
    Tape.mk₁ (TM2to1.trInit tm.k₁ output)⟩

instance [∀ k, Finite (tm.Γ k)] : Finite (TM2to1.Γ' tm.K tm.Γ) := by
  let _ : ∀ k, Fintype (tm.Γ k) := fun k => Fintype.ofFinite (tm.Γ k)
  infer_instance

private theorem initList_eq :
    letI : Inhabited tm.Λ := ⟨tm.main⟩
    ∀ input : List (tm.Γ tm.k₀), initList tm input = TM2.init tm.k₀ input := by
  intro input; unfold initList TM2.init; congr 1; funext k
  by_cases hk : k = tm.k₀
  · subst k; simp
  · simp only [hk, dite_false, Function.update_of_ne hk]

private theorem haltList_eq (output : List (tm.Γ tm.k₁)) :
    haltList tm output =
      (⟨none, tm.initialState, Function.update (fun _ => []) tm.k₁ output⟩ :
        TM2.Cfg tm.Γ tm.Λ tm.σ) := by
  unfold haltList; congr 1; funext k
  by_cases hk : k = tm.k₁
  · subst k; simp
  · simp only [hk, dite_false, Function.update_of_ne hk]

/-- Mathlib's compiler takes every bounded stack-machine computation to a native single-tape
path of width `B + headOverhead tm.m + 2`, independently of its runtime. -/
private theorem outputs_reachesWithin (input : List (tm.Γ tm.k₀)) (output : List (tm.Γ tm.k₁))
    (h : TM2Outputs tm input (some output)) (B : ℕ)
    (hB : ∀ n k, (((TM2.stepTotal tm.m)^[n] (initList tm input)).stk k).length ≤ B) :
    letI : Inhabited tm.Λ := ⟨tm.main⟩
    HeadPosition.ReachesWithin (TM1to0.tr (TM2to1.tr tm.m))
      (-1) (B + TM2to1.headOverhead tm.m)
      ⟨TM0.init (TM2to1.trInit tm.k₀ input), 0⟩
      ⟨⟨(none, tm.initialState), Tape.mk₁ (TM2to1.trInit tm.k₁ output)⟩, 0⟩ := by
  let : Inhabited tm.Λ := ⟨tm.main⟩
  apply TM2to1.tr_reachesWithin_halt tm.m tm.k₀ tm.k₁ input output
  · change TM2.Reaches tm.m (TM2.init tm.k₀ input)
      ⟨none, tm.initialState, Function.update (fun _ => []) tm.k₁ output⟩
    rw [← initList_eq tm input, ← haltList_eq tm output]
    exact evalsTo_reaches h
  · intro e he k
    rw [← initList_eq tm input] at he
    obtain ⟨n, rfl⟩ := reachable_index he
    exact hB n k

/-- A bounded source computation is simulated by a finite-control native single-tape machine
inside the same linear window, with a canonical halting target. -/
theorem outputs_toTM0 (input : List (tm.Γ tm.k₀)) (output : List (tm.Γ tm.k₁))
    (h : TM2Outputs tm input (some output)) (B : ℕ)
    (hB : ∀ n k, (((TM2.stepTotal tm.m)^[n] (initList tm input)).stk k).length ≤ B) :
    HeadPosition.ReachesWithin (toTM0 tm) (-1) (B + TM2to1.headOverhead tm.m)
      ⟨TM0.init (TM2to1.trInit tm.k₀ input), 0⟩ ⟨toTM0Halt tm output, 0⟩ := by
  let : Inhabited tm.Λ := ⟨tm.main⟩
  obtain ⟨d, hd, hp⟩ := (outputs_reachesWithin tm input output h B hB).restrict (toTM0_supports tm)
    ⟨TM0.init (TM2to1.trInit tm.k₀ input), 0⟩
    (by simp only [TM0.init, HeadPosition.liftCfg_mk]; rfl)
  have he : HeadPosition.liftCfg ⟨toTM0Halt tm output, 0⟩ =
      (⟨⟨(none, tm.initialState), Tape.mk₁ (TM2to1.trInit tm.k₁ output)⟩, 0⟩ :
        HeadPosition.Cfg (TM2to1.Γ' tm.K tm.Γ) (TM1to0.Λ' (TM2to1.tr tm.m))) := by
    simp only [toTM0Halt, HeadPosition.liftCfg_mk]
  exact HeadPosition.liftCfg_injective (hd.trans he.symm) ▸ hp

/-- Every canonical output configuration halts immediately. -/
theorem toTM0Halt_terminal (output : List (tm.Γ tm.k₁)) :
    TM0.step (toTM0 tm) (toTM0Halt tm output) = none := by
  let : Inhabited tm.Λ := ⟨tm.main⟩
  have hs : (HeadPosition.step (toTM0 tm) ⟨toTM0Halt tm output, 0⟩).map
      HeadPosition.liftCfg = none := by
    simpa only [toTM0, toTM0Halt, HeadPosition.liftCfg_mk, HeadPosition.step, TM1to0.tr,
      Option.map_none] using HeadPosition.step_liftCfg (TM1to0.tr (TM2to1.tr tm.m))
        (toTM0_supports tm) ⟨toTM0Halt tm output, 0⟩
  simpa only [Option.map_eq_none_iff.mp hs, Option.map_none] using
    (HeadPosition.step_native (toTM0 tm) ⟨toTM0Halt tm output, 0⟩).symm

/-- Constructing the compiler's initial multiplexed tape is polynomial-time under finite
alphabet encodings. -/
private theorem computableInPolyTime_trInit [∀ k, Finite (tm.Γ k)] (k : tm.K) :
    Turing.MultiTapeTM.ComputableInPolyTime (TM2to1.trInit k)
      (Turing.MultiTapeTM.encList (Turing.MultiTapeTM.encFinite (tm.Γ k)))
      (Turing.MultiTapeTM.encList (Turing.MultiTapeTM.encFinite (TM2to1.Γ' tm.K tm.Γ))) := by
  let encΓ := encFinite (TM2to1.Γ' tm.K tm.Γ)
  have hlist := (map (of_finite
      (fun a : tm.Γ k => (false, Function.update (fun _ => none) k (some a)))
      (encIn := encFinite (tm.Γ k)) (encOut := encΓ))).comp (listReverse (encFinite (tm.Γ k)))
  have hh := (of_finite (fun a : TM2to1.Γ' tm.K tm.Γ => (true, a.2))
      (encIn := encΓ) (encOut := encΓ)).comp (listHeadDWithInput hlist (const default))
  convert (cons encΓ).comp (hh.prod ((listTail encΓ).comp hlist)) using 1
  funext input
  let L : List (TM2to1.Γ' tm.K tm.Γ) :=
    input.reverse.map fun a => (false, Function.update (fun _ => none) k (some a))
  change (true, L.headI.2) :: L.tail = (true, (L.headD default).2) :: L.tail
  cases L <;> rfl

/-- Canonical one-symbol outputs retain the identity of their output symbol. -/
theorem toTM0Halt_singleton_injective {a b : tm.Γ tm.k₁}
    (h : toTM0Halt tm [a] = toTM0Halt tm [b]) : a = b := by
  have he := congrArg (fun c => c.Tape.head.2 tm.k₁) h
  change (Function.update (fun k => (none : Option (tm.Γ k))) tm.k₁ (some a)) tm.k₁ =
    (Function.update (fun k => (none : Option (tm.Γ k))) tm.k₁ (some b)) tm.k₁ at he
  simpa only [Function.update_self, Option.some.injEq] using he

end FinTM2

namespace TM2Computable

variable {α : Type} {ea : α → List Bool} {f : α → Bool}

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime

/-- Reading the source binary input and constructing its single-tape initial word takes
polynomial time. -/
theorem computableInPolyTime_toTM0Input {encIn : α ↪ List Bool}
    (h : TM2Computable encIn Turing.MultiTapeTM.encBool f) [∀ k, Finite (h.tm.Γ k)] :
    Turing.MultiTapeTM.ComputableInPolyTime
      (fun a => TM2to1.trInit h.tm.k₀ (List.map h.inputAlphabet.symm (encIn a))) encIn
      (Turing.MultiTapeTM.encList
        (Turing.MultiTapeTM.encFinite (TM2to1.Γ' h.tm.K h.tm.Γ))) := by
  have hi : ComputableInPolyTime (fun a => encIn a) encIn encBits := of_eq fun _ => rfl
  have hm := (map (of_finite h.inputAlphabet.symm
      (encIn := encBool) (encOut := encFinite (h.tm.Γ h.tm.k₀)))).comp (bitsToList.comp hi)
  exact h.tm.computableInPolyTime_trInit h.tm.k₀ |>.comp hm

/-- A Boolean stack-machine computation with bounded stacks gives a finite single-tape decider:
the actual output is reached inside the linear stack-space window, and native reachability of
the canonical true output is equivalent to the computed Boolean being true. -/
theorem toTM0_bool (h : TM2Computable ea Turing.MultiTapeTM.encBool f) {space : α → ℕ}
    (hs : h.StacksBounded space) :
    (∀ a, HeadPosition.ReachesWithin (h.tm.toTM0) (-1)
      (space a + TM2to1.headOverhead h.tm.m)
      ⟨TM0.init (TM2to1.trInit h.tm.k₀ (List.map h.inputAlphabet.symm (ea a))), 0⟩
      ⟨h.tm.toTM0Halt [h.outputAlphabet.symm (f a)], 0⟩) ∧
    (∀ a, f a = true ↔ TM0.Reaches h.tm.toTM0
      (TM0.init (TM2to1.trInit h.tm.k₀ (List.map h.inputAlphabet.symm (ea a))))
      (h.tm.toTM0Halt [h.outputAlphabet.symm true])) := by
  have hp a : HeadPosition.ReachesWithin (h.tm.toTM0) (-1)
      (space a + TM2to1.headOverhead h.tm.m)
      ⟨TM0.init (TM2to1.trInit h.tm.k₀ (List.map h.inputAlphabet.symm (ea a))), 0⟩
      ⟨h.tm.toTM0Halt [h.outputAlphabet.symm (f a)], 0⟩ :=
    h.tm.outputs_toTM0 _ _ (h.outputsFun a) (space a) (hs a)
  refine ⟨hp, fun a => ⟨fun ha => ?_, fun hr => ?_⟩⟩
  · simpa only [ha] using (hp a).native
  · have he := Part.mem_unique
      (StateTransition.mem_eval.mpr ⟨(hp a).native, h.tm.toTM0Halt_terminal _⟩)
      (StateTransition.mem_eval.mpr ⟨hr, h.tm.toTM0Halt_terminal _⟩)
    exact h.outputAlphabet.symm.injective (FinTM2.toTM0Halt_singleton_injective h.tm he)

end TM2Computable

end Turing

namespace Cslib.Complexity

open Turing Turing.MultiTapeTM

/-- Every standard PSPACE language has a fixed finite-control, finite-alphabet single-tape
machine whose accepting computation fits in a polynomial-width window. The target is the
canonical true halt configuration, the computed Boolean characterizes membership, and the input
encoding is preserved. -/
theorem mem_PSPACE_exists_boundedTM0 {α : Type} {encIn : α ↪ List Bool} {A : Set α}
    (hA : A ∈ PSPACE encIn) :
    ∃ (f : α → Bool) (h : TM2Computable encIn encBool f), (∀ k, Finite (h.tm.Γ k)) ∧
      ∃ p : Polynomial ℕ,
        (∀ a, HeadPosition.ReachesWithin h.tm.toTM0 (-1)
          (p.eval (encIn a).length + TM2to1.headOverhead h.tm.m)
          ⟨TM0.init (TM2to1.trInit h.tm.k₀ (List.map h.inputAlphabet.symm (encIn a))), 0⟩
          ⟨h.tm.toTM0Halt [h.outputAlphabet.symm (f a)], 0⟩) ∧
        (∀ a, a ∈ A ↔ f a = true) ∧
        (∀ a, a ∈ A ↔ TM0.Reaches h.tm.toTM0
          (TM0.init (TM2to1.trInit h.tm.k₀ (List.map h.inputAlphabet.symm (encIn a))))
          (h.tm.toTM0Halt [h.outputAlphabet.symm true])) := by
  obtain ⟨f, h, hfinite, ⟨space, hspace, hs⟩, hf⟩ := mem_PSPACE_iff_tm2.mp hA
  obtain ⟨p, hp⟩ := hspace.exists_polynomial
  have hs' : h.StacksBounded (fun a => p.eval (encIn a).length) :=
    fun a n k => (hs a n k).trans (hp a)
  obtain ⟨hr, ht⟩ := h.toTM0_bool hs'
  exact ⟨f, h, hfinite, p, hr, hf, fun a => (hf a).trans (ht a)⟩

end Cslib.Complexity
