/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.SharedFork
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.ExtendTapes
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.WorkTapePredicate

/-!
# A common finite controller for two work-tape verifiers

Two independently constructed alternating machines may use different numbers of tapes and states.
Both signs of a claim use the larger scratch block and the same two positions for the serialized
input and marker. The tape embedding and state tag preserve halting and acceptance step for step.
-/

public section

namespace Turing.MultiTapeATM.WorkTapeFamily

open MultiTapeTM

private theorem view_config {k K : ℕ} {S : Type} (s : S) (e : Fin (k + 2) ↪ Fin (K + 2))
    (he : e (Fin.natAdd k 0) = Fin.natAdd K 0) (host word : List Bool) :
    viewCfg e ((WorkTapePredicate.config host word).withState (some s)) =
      (WorkTapePredicate.config host word).withState (some s) := by
  apply Cfg.ext <;> try rfl
  funext i z
  by_cases hi : i = Fin.natAdd k 0
  · subst i
    simp [viewCfg, WorkTapePredicate.config, Cfg.withState, tapesCfg, he]
  · have hn : e i ≠ Fin.natAdd K 0 := by rw [← he]; exact e.injective.ne hi
    simp [viewCfg, WorkTapePredicate.config, Cfg.withState, tapesCfg, hi, hn]

/-- Both work-tape runners can be selected by a Boolean with one finite control type. Their
original input-dependent clocks are preserved exactly. -/
theorem exists_family (u : Bool → ℕ) (S : Bool → Type) [∀ b, Finite (S b)]
    (runner : (b : Bool) → MultiTapeATM (u b + 2) Bool (S b)) :
    ∃ (k : ℕ) (Q : Type) (_ : Finite Q) (family : Bool → MultiTapeATM (k + 2) Bool Q),
      ∀ (b : Bool) (host word : List Bool) (t : ℕ),
        let start := (WorkTapePredicate.config host word).withState (some (family b).toPTM.initial)
        let child := (WorkTapePredicate.config host word).withState (some (runner b).toPTM.initial)
        ((family b).HaltsWithin t start ↔ (runner b).HaltsWithin t child) ∧
          ((family b).AcceptsWithin t start ↔ (runner b).AcceptsWithin t child) := by
  classical
  let k := max (u false) (u true)
  have hle (b : Bool) : u b ≤ k := by
    cases b
    · exact Nat.le_max_left ..
    · exact Nat.le_max_right ..
  let e (b : Bool) : Fin (u b + 2) ↪ Fin (k + 2) :=
    (Fin.natAddEmb (k - u b)).trans
      (finCongr (show k - u b + (u b + 2) = k + 2 by have := hle b; omega)).toEmbedding
  have he (b : Bool) : e b (Fin.natAdd (u b) 0) = Fin.natAdd k 0 := by
    apply Fin.ext
    change k - u b + (u b + 0) = k + 0
    have := hle b
    omega
  let lifted := fun b => (runner b).extendTapes (e b)
  refine ⟨k, _, inferInstance, SharedFork.selected lifted, ?_⟩
  intro b host word t start child
  have hs := SharedFork.selected_spec lifted b (WorkTapePredicate.config host word) t
  have hv := view_config (runner b).toPTM.initial (e b) (he b) host word
  exact ⟨hs.1.trans (((runner b).haltsWithin_extendTapes_iff (e b) t _).trans (hv ▸ Iff.rfl)),
    hs.2.trans (((runner b).acceptsWithin_extendTapes_iff (e b) t _).trans (hv ▸ Iff.rfl))⟩

end Turing.MultiTapeATM.WorkTapeFamily
