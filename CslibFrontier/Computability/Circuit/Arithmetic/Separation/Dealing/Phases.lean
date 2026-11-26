/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Dealing.Tables
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Interpreter.Picks
import CslibFrontier.Foundations.Data.List.Blocks
import CslibFrontier.Foundations.Logic.Function.FoldlUpdate

/-!
# The phases of the dealing program

The dealing program of [AnthropicVPVNP2026] runs in phases of two kinds. In a phase of picks, the
step of every index `i` picks an option from a fixed list and makes its assignments to the names
of `i` (`Codes.pickStep`); the sum over the states after the phase is a sum over all choices
(`sum_execAll_pickSteps`). In a deterministic phase, the step of every index writes one name
(`execAll_writeSteps`).

## Main definitions

* `Codes.pickStep`: a step that picks an option from a fixed list.

## Main results

* `sum_execAll_append`: the sum over the states after two lists of steps.
* `sum_execAll_pickSteps`: a phase of picks.
* `execAll_writeSteps`: a phase of steps that write one name each.

## References

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], Appendix J.3: the program `G` in the proof
of Theorem J.3 (p. 54). Ported from the source module `Nc.Dl.Phases`.
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Dealing

open Function Finset Interpreter Interpreter.Tree Cut

variable {F : Type} [CommSemiring F] {K A' E U0 U1 D pS : ℕ} {M : Moves F (K + K + A') E}
  {S : Type} [DecidableEq S] (C : Codes S M U0 U1 D pS) {m : ℕ}

/-- A step that picks one of the options `o a`, for `a` in `opts`, from a table that it reads at
the empty name. -/
@[expose] def Codes.pickStep {α : Type*} (opts : List α)
    (o : α → List (PlanName S M U0 U1 pS × Tree)) : DStep :=
  .pick (C.name .empty) (.cons (listT (opts.map fun a => optionTree C.name (o a))) .nil)

private theorem Codes.exec_pickStep {α : Type*} {st : PlanName S M U0 U1 pS → Tree}
    (hz : st .empty = .nil) (opts : List α) (o : α → List (PlanName S M U0 U1 pS × Tree)) :
    (C.pickStep opts o).exec m (extend C.name st fun _ => .nil) =
      opts.map fun a => extend C.name (assignAll st (o a)) fun _ => .nil := by
  rw [pickStep, exec_pick C.name_injective (opts := opts.map o), List.map_map]
  · rfl
  · simp [hz, path, tget, Function.comp_def]

/-- The sum over the states after two lists of steps, as a sum over the states after the
first. -/
theorem sum_execAll_append {B : Type} [CommRing B] (a b : List DStep) (σ : List Bool → Tree)
    (Φ : (List Bool → Tree) → B) : ((execAll m (a ++ b) σ).map Φ).sum =
      ((execAll m a σ).map fun σ' => ((execAll m b σ').map Φ).sum).sum := by
  rw [execAll_append, List.sum_map_flatMap]

omit [DecidableEq S] in
/-- **A phase of picks.** The step of the index `i` picks `a` from the list `opts i` and makes the
assignments `o i a`. For the choices `f`, the assignments of `o i (f i)` are to names `x` of `i`
(`own x = some i`), of the values `w f x`, and every name of `i` is assigned; the empty name
belongs to no index. The sum over the states after all steps is the sum over the choices from the
lists, at the states with the values `w f x` at the names of the indices. -/
theorem sum_execAll_pickSteps {B : Type} [CommRing B] {ι α : Type} [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α] {st : PlanName S M U0 U1 pS → Tree} (hz : st .empty = .nil)
    (opts : ι → List α) (hopts : ∀ i, (opts i).Nodup)
    (o : ι → α → List (PlanName S M U0 U1 pS × Tree)) (own : PlanName S M U0 U1 pS → Option ι)
    (w : (ι → α) → PlanName S M U0 U1 pS → Tree)
    (ho : ∀ f i, ∀ a ∈ o i (f i), own a.1 = some i ∧ a.2 = w f a.1)
    (hall : ∀ (f : ι → α) i x, own x = some i → ∃ a ∈ o i (f i), a.1 = x)
    (hz' : own .empty = none) (Φ : (List Bool → Tree) → B) :
    ((execAll m ((univ : Finset ι).toList.map fun i => C.pickStep (opts i) (o i))
        (extend C.name st fun _ => .nil)).map Φ).sum =
      ∑ f : ι → α, if ∀ i, f i ∈ opts i then
        Φ (extend C.name (fun x => if (own x).isSome then w f x else st x) fun _ => .nil)
      else 0 := by
  classical
  rcases isEmpty_or_nonempty (ι → α) with hf | hf
  · -- there is an index and no option
    obtain ⟨⟨i⟩, hα⟩ := isEmpty_fun.1 hf
    obtain ⟨j, l, hl⟩ := List.exists_cons_of_ne_nil (l := (univ : Finset ι).toList)
      (List.ne_nil_of_mem (mem_toList.2 (mem_univ i)))
    have : opts j = [] := List.eq_nil_iff_forall_not_mem.2 fun a => isEmptyElim a
    simp [hl, execAll, C.exec_pickStep hz, this]
  obtain ⟨f0⟩ := hf
  rw [execAll_choices (good := fun st : PlanName S M U0 U1 pS → Tree => st .empty = .nil)
    (fun i st hst => C.exec_pickStep hst _ _) (fun i st a _ hst => ?_) (nodup_toList _) hz f0,
    sum_funs _ hopts _ (nodup_toList _)]
  · refine sum_congr rfl fun f _ => if_congr (by simp) ?_ rfl
    congr 2
    funext x
    rw [foldl_assignAll (ho f) (hall f)]
    exact if_congr (by simp [Option.isSome_iff_exists]) rfl rfl
  · have h := ho (update f0 i a) i
    rw [update_self] at h
    rw [assignAll_apply fun b hb => (h b hb).2, ite_eq_right fun ⟨b, hb, e⟩ => by
      simpa [e, hz'] using (h b hb).1, hst]

/-- **A deterministic phase.** The step of every index `i` writes the value `v i` to the name
`g i`, as long as an invariant `good` of the steps still to come and of the state holds. After
the steps of a list of all indices, the names `g i` have the values `v i`. -/
theorem execAll_writeSteps {ι : Type} {s : List ι} (hs : ∀ i, i ∈ s) {step : ι → DStep}
    {g : ι → PlanName S M U0 U1 pS} (hg : Injective g) {v : ι → Tree}
    (good : List ι → (PlanName S M U0 U1 pS → Tree) → Prop) {st : PlanName S M U0 U1 pS → Tree}
    (h0 : good s st) (hstep : ∀ i rest st, good (i :: rest) st →
      (step i).exec m (extend C.name st fun _ => .nil) =
        [extend C.name (update st (g i) (v i)) fun _ => .nil] ∧ good rest (update st (g i) (v i))) :
    execAll m (s.map step) (extend C.name st fun _ => .nil) =
      [extend C.name (extend g v st) fun _ => .nil] := by
  rw [execAll_det (L := fun st => extend C.name st fun _ => .nil) good hstep h0,
    foldl_update_eq_extend hg v hs]

end Cslib.Circuits.Arithmetic.Separation.Dealing
