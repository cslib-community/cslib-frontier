/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Realization.Basic

/-!
# Reinterpreting faithfully encoded results

Changing a semantic result costs no native instructions only when its complete encoded word
vector stays identical. This rule covers adding a uniquely determined type-level operation tag;
it does not allow host computation to change runtime output words for free.

## Main results

* `Realizes.result`: preserve the native code under an explicit equality of result encodings.
-/

public section

namespace Cslib.WordRAM.Realization

open Cslib.DataStructure

variable {B : Basis} {δ α β : Type} {k l : ℕ}

private theorem runClient_result (w : ℕ) (p : Memory.Prog α) (f : α → β) (s : Memory.State) :
    (Memory.spec w).runClient s (p.bind fun a => .pure (f a)) =
      (f ((Memory.spec w).clientResult s p), (Memory.spec w).clientState s p,
        (Memory.spec w).clientHistory s p) := by
  rw [StateTransitionSpec.runClient_bind]
  simp only [StateTransitionSpec.runClient_pure, List.append_nil]

namespace Realizes

/-- Relabel results only if their entire faithfully encoded register vectors are unchanged.
All witnesses, native instructions, safety hypotheses and local-work charges are preserved. -/
theorem result {p : δ → Memory.Prog α} {input : δ ↪ (Fin k → ℕ)}
    {output : α ↪ (Fin l → ℕ)} {output' : β ↪ (Fin l → ℕ)}
    {safe : ℕ → δ → Memory.State → Prop} {work : δ → Memory.State → ℕ}
    (h : Realizes B p input output safe work) (f : δ → α → β)
    (hf : ∀ d a, output a = output' (f d a)) :
    Realizes B (fun d => (p d).bind fun a => .pure (f d a)) input output' safe work := by
  obtain ⟨n, C, emit, he⟩ := h
  refine ⟨n, C, emit, fun {r} frontier src tmp hi hd hfr hs => ?_⟩
  obtain ⟨hnw, hrun⟩ := he frontier src tmp hi hd hfr hs
  refine ⟨hnw, fun w d x hx hin hsafe hv => ?_⟩
  obtain ⟨y, hy, hm, hout, hframe⟩ := hrun w d x hx hin hsafe
    (by simpa only [StateTransitionSpec.clientHistory, runClient_result] using hv)
  exact ⟨y,
    by simpa only [memoryCost_bind, PFunctor.FreeM.pure_eq_pure, memoryCost_pure,
      Nat.add_zero] using hy,
    by simpa only [StateTransitionSpec.clientState, runClient_result] using hm,
    fun i => by simpa only [StateTransitionSpec.clientResult, runClient_result, ← hf] using hout i,
    hframe⟩

end Realizes

end Cslib.WordRAM.Realization
