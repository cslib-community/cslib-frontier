/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.PriorityQueue.FibonacciHeap.Native.Domain
public import CslibFrontier.DataStructure.PriorityQueue.FibonacciHeap.Native.Source
public import CslibFrontier.Computability.WordRAM.Realization.WhileAbsorb
import CslibFrontier.DataStructure.Memory.RecordLink
import CslibFrontier.Tactic.Realize

/-!
# Native cascading-cut source

The native body reuses the existing cut certificate. Its parent subtraction is a charged pure
step, not free call wiring. The source equality preserves the original stop and mark branches.
The body domain concerns reached memory; a complete decrease-key certificate is separate.

## Main definitions

* `cascadeStepSafe`: native body entry conditions at the reached memory.

## Main results

* `realizes_cascadeStep`: the original source step, with uniform runtime capacity and layout.
* `cascade_whileSafe`, `cascadeSafe_of_cascading`: the original forest proves nontruncation.
* `realizes_cascade`: the complete source cascade through the shared native while rule.
-/

public section

namespace Cslib.DataStructure.PriorityQueue.FibonacciHeap.Native

open Cslib.WordRAM Cslib.WordRAM.Realization
open Cslib.DataStructure.PriorityQueue.WordRAM.FibonacciHeap

/-- The marked branch uses the existing cut's actual intermediate-state domain. All other
arithmetic overflow obligations remain part of the original admissible source history. -/
@[expose] def cascadeStepSafe (w : ℕ) (d : Fin 3 → ℕ) (s : Memory.State) : Prop :=
  Fits w (d 1 + (9 * d 0 + 5)) ∧ d 2 < d 0 ∧
    (s.mem (d 1 + d 0 + d 2) ≠ 0 → s.mem (d 1 + 6 * d 0 + d 2) ≠ 0 →
      cutSafe w ![d 0, d 1, d 2, s.mem (d 1 + d 0 + d 2) - 1] s)

private theorem realizes_cascadeStep_history : Realizes .exact
    (fun d : Fin 3 → ℕ => DataStructure.link (E := Memory.spec 0)
      ((layout (d 0) (d 1)).methods 0) (cascadeStep (d 2)))
    (.refl _) (WordEncoding.encode (α := Option ℕ))
    (fun w d s => cascadeStepSafe w d s ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
        (DataStructure.link (E := Memory.spec 0) ((layout (d 0) (d 1)).methods 0)
          (cascadeStep (d 2)))))
    (fun _ _ => 0) := by
  realize [realizes_cut]
  all_goals try first
    | exact h.1.1.of_le (by have := h.1.2.1; omega)
    | exact h.1.2.2 (by assumption) (by assumption)
    | omega
  have hv := h.2
  clear h
  simp only [DataStructure.link, cascadeStep, rd, wr, PFunctor.FreeM.liftM_bind,
    Record.Layout.lift_read, Record.Layout.lift_write, Record.lift_ite, layout] at hv
  simp_all only [StateTransitionSpec.clientHistory, StateTransitionSpec.runClient_lift_bind',
    StateTransitionSpec.validHistory_cons, StateTransitionSpec.stepFn,
    Memory.read, Memory.write, Memory.step_read, Memory.step_write,
    Memory.valid, ite_true, ite_false]

/-- The same original cascading-cut source step, without an added source-history hypothesis.
Its intrinsic admissibility premise supplies fitting values for the mark/count writes. -/
theorem realizes_cascadeStep : Realizes .exact
    (fun d : Fin 3 → ℕ => DataStructure.link (E := Memory.spec 0)
      ((layout (d 0) (d 1)).methods 0) (cascadeStep (d 2)))
    (.refl _) (WordEncoding.encode (α := Option ℕ)) cascadeStepSafe (fun _ _ => 0) :=
  realizes_cascadeStep_history.consequence_valid (fun _ _ _ _ _ hv h => ⟨h, hv⟩)

/-- The existing forest supplies the actual cut domain whenever the body reaches its cut
branch. No additional numeric parent or subtraction hypothesis is assumed. -/
theorem cascadeStepSafe_of_cascading {n K w base : ℕ} {s : IndexedMinPQ.State n}
    {mem : Memory.State} {v m z : Fin n} {ts : List (FHTree n)}
    (hfit : Fits w (base + (9 * n + 5))) (halloc : (layout n base).Inv mem)
    (h : Cascading n K s (view n ((layout n base).abs mem)) v m (some z) ts)
    (hz : z ∈ forestNodes ts) : cascadeStepSafe w ![n, base, z.val] mem := by
  refine ⟨hfit, z.isLt, fun hpz _ => ?_⟩
  have hpar_eq : (view n ((layout n base).abs mem)).par z = mem.mem (base + n + z.val) := by
    simp only [view, Record.Layout.abs, Cell.ok, z.isLt, ite_true, layout]
  obtain ⟨T, hT, hdesc⟩ := h.desc_of_par hz (hpar_eq ▸ hpz)
  obtain ⟨p, _, hpar⟩ := (h.valid T hT).1.par_of_mem_children z hdesc
  change cutSafe w ![n, base, z.val, mem.mem (base + n + z.val) - 1] mem
  rw [← hpar_eq, hpar, Nat.add_sub_cancel]
  exact cutSafe_of_cascading hfit halloc h hz hpar

/-- The original marked-node rank justifies the source cascade's finite while cutoff. The
valid-history premise is the certificate's intrinsic source admissibility condition, not an
extra heap model. All body domains are required at the actual reached memories. -/
theorem cascade_whileSafe {n K w base fuel : ℕ} {s : IndexedMinPQ.State n}
    {mem : Memory.State} {v m z : Fin n} {ts : List (FHTree n)}
    (hfit : Fits w (base + (9 * n + 5))) (halloc : (layout n base).Inv mem)
    (h : Cascading n K s (view n ((layout n base).abs mem)) v m (some z) ts)
    (hv : ∃ T ∈ ts, T.root = v)
    (hzv : ∀ T ∈ ts, z ∈ T.nodes → T.root ≠ v) (hz : z ∈ forestNodes ts)
    (hfuel : (view n ((layout n base).abs mem)).numMarked < fuel)
    (hvalid : (Memory.spec w).ValidHistory mem ((Memory.spec w).clientHistory mem
      (boundedWhile (fun (_ : Unit) (a : Option ℕ) => optionWords a 0 ≠ 0)
        (fun a : Unit × Option ℕ => DataStructure.link (E := Memory.spec 0)
          ((layout n base).methods 0) (cascadeStep (optionWords a.2 1))) () fuel (some z.val)))) :
    whileSafe (fun (_ : Unit) (a : Option ℕ) => optionWords a 0 ≠ 0)
      (fun a : Unit × Option ℕ => DataStructure.link (E := Memory.spec 0)
        ((layout n base).methods 0) (cascadeStep (optionWords a.2 1)))
      (fun w a mem => cascadeStepSafe w ![n, base, optionWords a.2 1] mem)
      w () fuel (some z.val) mem := by
  let I (a : Option ℕ) (mem : Memory.State) : Prop := (layout n base).Inv mem ∧
    (a = none ∨ ∃ (z : Fin n) (ts : List (FHTree n)), a = some z.val ∧
      Cascading n K s (view n ((layout n base).abs mem)) v m (some z) ts ∧
      (∃ T ∈ ts, T.root = v) ∧ (∀ T ∈ ts, z ∈ T.nodes → T.root ≠ v) ∧ z ∈ forestNodes ts)
  let rank (a : Option ℕ) (mem : Memory.State) : ℕ :=
    if a.isSome then (view n ((layout n base).abs mem)).numMarked + 1 else 0
  refine whileSafe_of_measure _ _ _ w () I rank ?_ ?_
    ⟨halloc, Or.inr ⟨z, ts, rfl, h, hv, hzv, hz⟩⟩ (by change _ + 1 ≤ fuel; omega) hvalid
  · rintro (_ | z) mem _ hr
    · simp [optionWords_none]
    · simp [rank] at hr
  · intro a mem hi _ _
    rcases hi.2 with rfl | ⟨cur, ts, rfl, hc, hv, hcv, hcur⟩
    · contradiction
    obtain ⟨hrec, hpost⟩ :=
      (Record.wp_iff _ _ _).mp (cascadeStep_progress (hfit.of_le (by omega)) hc hv hcv hcur)
    obtain ⟨_, hres, habs, hinv⟩ :=
      (Record.refinement (layout n base) w).simulates_client (cascadeStep cur) hi.1 hrec
    dsimp only [Record.refinement] at hres habs hinv
    rw [clientResult_width w, link_width] at hres
    rw [clientState_width w, link_width] at habs hinv
    rw [← hres, ← habs] at hpost
    simp only [optionWords_some, Matrix.cons_val_one, Matrix.cons_val_zero]
    rcases hpost with hn | ⟨p, ts', hn, hc', hv', hpv', hp', hlt⟩
    · exact ⟨cascadeStepSafe_of_cascading hfit hi.1 hc hcur,
        ⟨hinv, Or.inl hn⟩, by simp [rank, hn]⟩
    · exact ⟨cascadeStepSafe_of_cascading hfit hi.1 hc hcur,
        ⟨hinv, Or.inr ⟨p, ts', hn, hc', hv', hpv', hp'⟩⟩,
        by simp only [rank, hn, Option.isSome_some, ↓reduceIte]; omega⟩

/-- The native cascade's loop domain: every reached body has its genuine cut domain and the
original cutoff does not truncate a continuing branch. -/
@[expose] def cascadeSafe (w : ℕ) (d : Fin 3 → ℕ) (mem : Memory.State) : Prop :=
  Fits w (d 1 + (9 * d 0 + 5)) ∧ d 2 < d 0 ∧
    whileSafe (fun (_ : Unit) (a : Option ℕ) => optionWords a 0 ≠ 0)
      (fun a : Unit × Option ℕ => DataStructure.link (E := Memory.spec 0)
        ((layout (d 0) (d 1)).methods 0) (cascadeStep (optionWords a.2 1)))
      (fun w a mem => cascadeStepSafe w ![d 0, d 1, optionWords a.2 1] mem)
      w () (d 0 + 1) (some (d 2)) mem

/-- The complete original cascade, compiled with the shared native while rule. The cutoff is
only a proof bound: the emitted loop tests the pending tag and never executes a fuel counter. -/
theorem realizes_cascade : Realizes .exact
    (fun d : Fin 3 → ℕ => DataStructure.link (E := Memory.spec 0)
      ((layout (d 0) (d 1)).methods 0) (cascade (d 0 + 1) (d 2)))
    (.refl _) (WordEncoding.encode (α := Unit)) cascadeSafe (fun _ _ => 0) := by
  realize [realizes_cascadeStep] rewriting [link_cascade_eq_boundedWhile]
  all_goals first
    | exact h.1.of_le (by omega)
    | exact fun _ => h.2.2

/-- The original source proof supplies admissible history as well as the marked-node fuel
bound. Thus the native while domain follows from the existing forest and allocation invariant. -/
theorem cascadeSafe_of_cascading {n K w base : ℕ} {s : IndexedMinPQ.State n}
    {mem : Memory.State} {v m z : Fin n} {ts : List (FHTree n)}
    (hfit : Fits w (base + (9 * n + 5))) (halloc : (layout n base).Inv mem)
    (h : Cascading n K s (view n ((layout n base).abs mem)) v m (some z) ts)
    (hv : ∃ T ∈ ts, T.root = v)
    (hzv : ∀ T ∈ ts, z ∈ T.nodes → T.root ≠ v) (hz : z ∈ forestNodes ts) :
    cascadeSafe w ![n, base, z.val] mem := by
  have hfuel : (view n ((layout n base).abs mem)).numMarked < n + 1 :=
    h.numMarked ▸ Nat.lt_succ_of_le (markedCount_le_n _)
  have hrec := (Record.wp_iff _ _ _).mp
    (wp_cascade (hfit.of_le (by omega)) (n + 1) h hv hzv hz hfuel) |>.1
  have hval : (Memory.spec w).ValidHistory mem ((Memory.spec w).clientHistory mem
      (DataStructure.link (E := Memory.spec w) ((layout n base).methods w) (cascade (n + 1) z))) :=
    ((Record.refinement (layout n base) w).simulates_client (cascade (n + 1) z) halloc hrec).1
  rw [link_width, link_cascade_eq_boundedWhile] at hval
  exact ⟨hfit, z.isLt, cascade_whileSafe hfit halloc h hv hzv hz hfuel
    ((validHistory_bind w _ _ mem).mp hval).1⟩

end Cslib.DataStructure.PriorityQueue.FibonacciHeap.Native
