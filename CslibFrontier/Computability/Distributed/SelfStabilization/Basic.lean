/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Foundations.Semantics.LTS.OmegaExecution

/-!
# Self-stabilizing labelled transition systems

This module formalizes self-stabilization over a general labelled transition system `Cslib.LTS`,
following [Dijkstra][Dijkstra1974] (p. 643, right column).

Given `lts : LTS State Label` and a target set `Legitimate : Set State` of legitimate
configurations, `SelfStabilizing lts Legitimate` requires:

1. *Closure* (`closed`): every transition from a legitimate state produces a legitimate state
   (requirement (2) on p. 643 of [Dijkstra][Dijkstra1974]);
2. *Deadlock-freedom* (`no_terminal`): no state is terminal (`∀ s, ¬ lts.IsTerminal s`), so at
   least one transition is enabled in every configuration (implying requirement (1) on p. 643);
3. *Worst-case finite convergence* (`converges`): `CorruptedStep lts Legitimate` is well-founded,
   ruling out infinite executions that remain outside `Legitimate` under any adversarial enabled
   schedule without fairness assumptions.

Source conditions (3) and (4) on p. 643 of [Dijkstra][Dijkstra1974]—that each privilege occurs in
some legitimate state (3) and that every pair of legitimate states is mutually reachable by a path
of transitions (4)—are requirements of Dijkstra's legitimate-state specification that lie outside
the scope of this generic `SelfStabilizing` predicate and are stated separately by concrete
protocol modules where applicable.

From `SelfStabilizing`, every infinite execution `lts.OmegaExecution ss μs` enters `Legitimate` at
some step `k₀` and remains in `Legitimate` at all steps `k ≥ k₀`
(`SelfStabilizing.eventually_legitimate`), and every initial state admits at least one infinite
execution (`SelfStabilizing.exists_omegaExecution`). Conversely, any infinite execution that never
visits `Legitimate` refutes `SelfStabilizing` (`not_selfStabilizing_of_omegaExecution`). We also
provide a worst-case step-bound constructor (`SelfStabilizing.of_mTr_bound`) and daemon-refinement
transfer from a larger transition relation to a deadlock-free sub-relation
(`SelfStabilizing.of_subLTS`).

## Main definitions

* `Cslib.Distributed.SelfStabilization.CorruptedStep`: transition step `s → s'` from an
  illegitimate state `s ∉ Legitimate`, oriented `(s', s)` for `WellFounded`.
* `Cslib.Distributed.SelfStabilization.SelfStabilizing`: closure, deadlock-freedom, and
  well-founded convergence to `Legitimate` ([Dijkstra][Dijkstra1974], p. 643).

## Main results

* `Cslib.Distributed.SelfStabilization.SelfStabilizing.mTr_mem`: multistep forward invariance of
  `Legitimate`.
* `Cslib.Distributed.SelfStabilization.SelfStabilizing.omegaExecution_mem_of_le`: persistence of
  `Legitimate` along infinite executions.
* `Cslib.Distributed.SelfStabilization.SelfStabilizing.eventually_legitimate`: every
  `LTS.OmegaExecution` eventually enters and forever stays in `Legitimate`.
* `Cslib.Distributed.SelfStabilization.SelfStabilizing.exists_omegaExecution`: deadlock-freedom
  yields an infinite execution starting from every configuration.
* `Cslib.Distributed.SelfStabilization.SelfStabilizing.of_mTr_bound`: uniform finite-horizon bound
  implies `SelfStabilizing`.
* `Cslib.Distributed.SelfStabilization.SelfStabilizing.of_subLTS`: daemon refinement from a
  transitions-superset LTS (such as a distributed daemon) to a deadlock-free sub-LTS (such as a
  central daemon).
* `Cslib.Distributed.SelfStabilization.not_selfStabilizing_of_omegaExecution`: an infinite
  execution avoiding `Legitimate` refutes `SelfStabilizing`.

## References

* [E. W. Dijkstra, *Self-stabilizing Systems in Spite of Distributed Control*][Dijkstra1974]
-/

public section

namespace Cslib.Distributed.SelfStabilization

open Cslib

universe u v w

/-- One transition step from an illegitimate configuration `s ∉ Legitimate` to `s'`, oriented as
`CorruptedStep lts Legitimate s' s` so that `WellFounded (CorruptedStep lts Legitimate)` expresses
the absence of infinite sequences of corrupted transitions `s₀ → s₁ → s₂ → ⋯` remaining outside
`Legitimate`. -/
@[expose] def CorruptedStep {State : Type u} {Label : Type v}
    (lts : LTS State Label) (Legitimate : Set State) (s' s : State) : Prop :=
  s ∉ Legitimate ∧ ∃ μ, lts.Tr s μ s'

/-- A labelled transition system `lts` is *self-stabilizing* with respect to `Legitimate`
([Dijkstra][Dijkstra1974], p. 643, right column) if `Legitimate` is closed under transitions, no
configuration is terminal, and corrupted transitions outside `Legitimate` are well-founded. -/
structure SelfStabilizing {State : Type u} {Label : Type v}
    (lts : LTS State Label) (Legitimate : Set State) : Prop where
  /-- Requirement (2) of [Dijkstra][Dijkstra1974] (p. 643): legitimate states are closed under
  every transition. -/
  closed : ∀ ⦃s⦄, s ∈ Legitimate → ∀ ⦃μ s'⦄, lts.Tr s μ s' → s' ∈ Legitimate
  /-- Deadlock-freedom ([Dijkstra][Dijkstra1974], p. 643): every state enables at least one
  transition. -/
  no_terminal : ∀ s, ¬ lts.IsTerminal s
  /-- Finite-step convergence ([Dijkstra][Dijkstra1974], p. 643): no infinite chain of steps
  remains outside `Legitimate`, under any adversarial scheduler without fairness assumptions. -/
  converges : WellFounded (CorruptedStep lts Legitimate)

namespace SelfStabilizing

section Basic

variable {State : Type u} {Label : Type v} {lts : LTS State Label} {Legitimate : Set State}

/-- Every configuration in a self-stabilizing LTS has at least one outgoing transition. -/
theorem exists_tr (h : SelfStabilizing lts Legitimate) (s : State) :
    ∃ μ s', lts.Tr s μ s' := by
  by_contra hno
  exact h.no_terminal s fun μ s' htr => hno ⟨μ, s', htr⟩

/-- `Legitimate` is closed under finite multistep transitions `LTS.MTr`. -/
theorem mTr_mem (h : SelfStabilizing lts Legitimate) {s s' : State} {μs : List Label}
    (hs : s ∈ Legitimate) (hmtr : lts.MTr s μs s') : s' ∈ Legitimate :=
  lts.mtrInv_of_trInv (fun _ _ _ htr hp => h.closed hp htr) s μs s' hmtr hs

/-- Once an infinite execution visits `Legitimate` at index `k₀`, every state at `k ≥ k₀` stays in
`Legitimate`. -/
theorem omegaExecution_mem_of_le (h : SelfStabilizing lts Legitimate)
    {ss : ωSequence State} {μs : ωSequence Label}
    (hexec : lts.OmegaExecution ss μs) {k₀ k : ℕ}
    (hk₀ : ss k₀ ∈ Legitimate) (hle : k₀ ≤ k) : ss k ∈ Legitimate :=
  h.mTr_mem hk₀ (hexec.extract_mTr hle)

/-- Every infinite execution of a self-stabilizing LTS reaches `Legitimate` in finitely many steps
and remains in `Legitimate` forever thereafter. -/
theorem eventually_legitimate (h : SelfStabilizing lts Legitimate)
    {ss : ωSequence State} {μs : ωSequence Label}
    (hexec : lts.OmegaExecution ss μs) :
    ∃ k₀, ∀ k ≥ k₀, ss k ∈ Legitimate := by
  by_contra hnot
  have hno_chain (x) (hacc : Acc (CorruptedStep lts Legitimate) x) : ∀ k, ss k = x → False := by
    induction hacc with
    | intro _ _ ih =>
      rintro k rfl
      exact ih (ss (k + 1)) ⟨fun hk => hnot ⟨k, fun m => h.omegaExecution_mem_of_le hexec hk⟩,
        μs k, hexec k⟩ (k + 1) rfl
  exact hno_chain (ss 0) (h.converges.apply (ss 0)) 0 rfl

/-- Because no state is terminal, every initial state `s₀` admits an infinite execution starting at
`s₀`. -/
theorem exists_omegaExecution (h : SelfStabilizing lts Legitimate) (s₀ : State) :
    ∃ (ss : ωSequence State) (μs : ωSequence Label),
      ss 0 = s₀ ∧ lts.OmegaExecution ss μs := by
  let f (k : ℕ) : State := (fun s => (h.exists_tr s).choose_spec.choose)^[k] s₀
  refine ⟨⟨f⟩, ⟨fun k => (h.exists_tr (f k)).choose⟩, rfl, fun k => ?_⟩
  change lts.Tr (f k) _ ((fun s => (h.exists_tr s).choose_spec.choose)^[k + 1] s₀)
  rw [Function.iterate_succ_apply']
  exact (h.exists_tr (f k)).choose_spec.choose_spec

/-- Uniform finite-horizon criterion: if `Legitimate` is closed under transitions, no state is
terminal, and every `B`-step execution ends in `Legitimate`, then `lts` is self-stabilizing. -/
theorem of_mTr_bound (B : ℕ)
    (hclosed : ∀ ⦃s⦄, s ∈ Legitimate → ∀ ⦃μ s'⦄, lts.Tr s μ s' → s' ∈ Legitimate)
    (hno_term : ∀ s, ¬ lts.IsTerminal s)
    (hbound : ∀ ⦃s₀ μs s'⦄, lts.MTr s₀ μs s' → B ≤ μs.length → s' ∈ Legitimate) :
    SelfStabilizing lts Legitimate := by
  have hacc (rem : ℕ) : ∀ s, (∃ s₀ μs, lts.MTr s₀ μs s ∧ B ≤ μs.length + rem) →
      Acc (CorruptedStep lts Legitimate) s := by
    induction rem with
    | zero =>
      rintro s ⟨_, _, hmtr, hlen⟩
      exact Acc.intro s fun _ ⟨hnot, _⟩ => (hnot (hbound hmtr (by omega))).elim
    | succ rem ih =>
      rintro s ⟨s₀, μs, hmtr, hlen⟩
      exact Acc.intro s fun s' ⟨_, μ, htr⟩ =>
        ih s' ⟨s₀, μs ++ [μ], hmtr.stepR lts htr, by simp; omega⟩
  exact ⟨hclosed, hno_term, ⟨fun s => hacc B s ⟨s, [], .refl, by omega⟩⟩⟩

end Basic

/-- Daemon refinement: if every transition of `sub` is realized by some transition of `sup` and
`sub` has no terminal states, then `SelfStabilizing sup Legitimate` implies
`SelfStabilizing sub Legitimate`. -/
theorem of_subLTS {State : Type u} {Label₁ : Type v} {Label₂ : Type w}
    {sub : LTS State Label₁} {sup : LTS State Label₂} {Legitimate : Set State}
    (hsup : SelfStabilizing sup Legitimate)
    (hsub_tr : ∀ ⦃s μ₁ s'⦄, sub.Tr s μ₁ s' → ∃ μ₂, sup.Tr s μ₂ s')
    (hno_term : ∀ s, ¬ sub.IsTerminal s) :
    SelfStabilizing sub Legitimate where
  closed _ hs _ _ htr :=
    let ⟨_, htr'⟩ := hsub_tr htr
    hsup.closed hs htr'
  no_terminal := hno_term
  converges := Subrelation.wf (fun ⟨hs, _, htr⟩ => ⟨hs, hsub_tr htr⟩) hsup.converges

end SelfStabilizing

/-- Any infinite execution that never visits `Legitimate` refutes `SelfStabilizing`. -/
theorem not_selfStabilizing_of_omegaExecution {State : Type u} {Label : Type v}
    {lts : LTS State Label} {Legitimate : Set State}
    {ss : ωSequence State} {μs : ωSequence Label}
    (hexec : lts.OmegaExecution ss μs) (hbad : ∀ k, ss k ∉ Legitimate) :
    ¬ SelfStabilizing lts Legitimate := by
  intro hss
  obtain ⟨k₀, hk₀⟩ := hss.eventually_legitimate hexec
  exact hbad k₀ (hk₀ k₀ le_rfl)

end Cslib.Distributed.SelfStabilization
