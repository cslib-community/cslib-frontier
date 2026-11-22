/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.Distributed.SelfStabilization.DijkstraRing

/-! Self-stabilizing transition systems and Dijkstra's `K`-state token ring (checked as a `module`
client with ordinary imports): `decide`-verified convergence from a 4-privilege corrupted
configuration on `Fin 4` (`K = 4`) under both the central daemon and the simultaneous atomic-subset
model followed by a full `4`-step round-robin token circulation, the `n = 4, K = 3`
(`(0, 2, 1, 0)`) synchronous atomic-subset 4-privilege cycle contrasted with central-daemon
stabilization (Note 1), the `n = 4, K = 2` (`8`-step) and `n = 5, K = 3` (`15`-step) central-daemon
non-stabilizing cycles, sharp `iff` instantiations, and concrete `2`-periodic symmetry persistence
and enabled-move impossibility steps on the composite anonymous ring `Fin (2 * 2)`. -/
set_option linter.privateModule false

namespace CslibFrontierTests.Distributed.SelfStabilization

open Cslib Cslib.Distributed.SelfStabilization

/-! ### `Fin 4, K = 4`: 4-privilege corrupted state converging to 1-token circulation -/

private def vec4 {K : ℕ} (a b c d : Fin K) : Fin 4 → Fin K
  | ⟨0, _⟩ => a
  | ⟨1, _⟩ => b
  | ⟨2, _⟩ => c
  | ⟨_ + 3, _⟩ => d

private def vec5 {K : ℕ} (a b c d e : Fin K) : Fin 5 → Fin K
  | ⟨0, _⟩ => a
  | ⟨1, _⟩ => b
  | ⟨2, _⟩ => c
  | ⟨3, _⟩ => d
  | ⟨_ + 4, _⟩ => e

private def runCentral {n K : ℕ} [NeZero n] [NeZero K]
    (s : Fin n → Fin K) (sched : List (Fin n)) : Fin n → Fin K :=
  sched.foldl dijkstraStep s

/-- Corrupted initial configuration `(0, 2, 1, 0)` on `Fin 4, K = 4` has all `4` machines
privileged (`s ∉ DijkstraLegitimate 4 4`), and stabilizes under adversarial central-daemon
scheduling `[0, 3, 0, 1, 2, 3]` to `(2, 2, 2, 2) ∈ DijkstraLegitimate 4 4`, after which the single
token visits `0, 1, 2, 3, 0` in round-robin order. -/
theorem fin4_k4_corrupted_central_converges :
    let s₀ : Fin 4 → Fin 4 := vec4 0 2 1 0
    let s_leg := runCentral s₀ [0, 3, 0, 1, 2, 3]
    (dijkstraPrivilegedSet s₀).card = 4 ∧
      dijkstraPrivilegedSet s_leg = {0} ∧
      dijkstraPrivilegedSet (dijkstraStep s_leg 0) = {1} ∧
      dijkstraPrivilegedSet (runCentral s_leg [0, 1]) = {2} ∧
      dijkstraPrivilegedSet (runCentral s_leg [0, 1, 2]) = {3} ∧
      dijkstraPrivilegedSet (runCentral s_leg [0, 1, 2, 3]) = {0} := by
  decide

/-- Distributed-daemon simultaneous multi-privilege trace on `Fin 4, K = 4` from `(0, 2, 1, 0)`:
firing `{0, 2}` simultaneously reaches `(1, 2, 2, 0)` (`2` privileges at `{1, 3}`), then firing
`{1, 3}` reaches `(1, 1, 2, 2)` (`1` privilege at `{2}`, legitimate in `2` distributed steps). -/
theorem fin4_k4_corrupted_dist_converges_two_steps :
    let s₀ : Fin 4 → Fin 4 := vec4 0 2 1 0
    let s₁ := dijkstraDistStep s₀ {0, 2}
    let s₂ := dijkstraDistStep s₁ {1, 3}
    dijkstraPrivilegedSet s₀ = {0, 1, 2, 3} ∧
      dijkstraPrivilegedSet s₁ = {1, 3} ∧
      dijkstraPrivilegedSet s₂ = {2} := by
  decide

/-- Checked multistep `MTr` execution and `dijkstraRing_token_circulates` on `Fin 4, K = 4`. -/
theorem fin4_k4_round_robin_mTr :
    let s_leg := dijkstraTokenConfig 4 4 0 2
    let s_end := runCentral s_leg [0, 1, 2, 3]
    (dijkstraRing 4 4).MTr s_leg [0, 1, 2, 3] s_end ∧
      dijkstraPrivilegedSet s_end = {0} ∧
      s_end = dijkstraTokenConfig 4 4 0 3 := by
  intro s_leg s_end
  have h0 : (dijkstraRing 4 4).Tr s_leg 0 (dijkstraStep s_leg 0) := ⟨by decide, rfl⟩
  have h1 : (dijkstraRing 4 4).Tr (runCentral s_leg [0]) 1 (runCentral s_leg [0, 1]) :=
    ⟨by decide, rfl⟩
  have h2 : (dijkstraRing 4 4).Tr (runCentral s_leg [0, 1]) 2 (runCentral s_leg [0, 1, 2]) :=
    ⟨by decide, rfl⟩
  have h3 : (dijkstraRing 4 4).Tr (runCentral s_leg [0, 1, 2]) 3 s_end :=
    ⟨by decide, rfl⟩
  have hmtr : (dijkstraRing 4 4).MTr s_leg [0, 1, 2, 3] s_end :=
    .stepL h0 (.stepL h1 (.stepL h2 (.stepL h3 .refl)))
  have hcirc := (dijkstraRing_token_circulates (by decide : 2 ≤ 4)
    (dijkstraPrivilegedSet_tokenConfig (by decide) 0 2) hmtr).1
  refine ⟨hmtr, hcirc, ?_⟩
  funext i
  revert i
  decide

/-! ### `n = 4, K = 3` (`(0, 2, 1, 0)`): distributed 3-cycle vs central stabilization (Note 1) -/

/-- On `n = 4, K = 3`, `(0, 2, 1, 0)` cycles with period `3` under synchronous distributed steps
`Finset.univ`, keeping all `4` privileges at every step and never entering `DijkstraLegitimate`. -/
theorem fin4_k3_dist_sync_cycle :
    let c₀ : Fin 4 → Fin 3 := vec4 0 2 1 0
    let c₁ := dijkstraDistStep c₀ Finset.univ
    let c₂ := dijkstraDistStep c₁ Finset.univ
    let c₃ := dijkstraDistStep c₂ Finset.univ
    (dijkstraPrivilegedSet c₀).card = 4 ∧
      (dijkstraPrivilegedSet c₁).card = 4 ∧
      (dijkstraPrivilegedSet c₂).card = 4 ∧
      (∀ i, c₃ i = c₀ i) := by
  decide

/-- On `n = 4, K = 3`, the distributed-daemon ring is NOT self-stabilizing, whereas the
central-daemon ring IS self-stabilizing (`n - 1 = 3 ≤ 3`, Note 1 of [Dijkstra1974], p. 644). -/
theorem fin4_k3_central_vs_distributed_dichotomy :
    SelfStabilizing (dijkstraRing 4 3) (DijkstraLegitimate 4 3) ∧
      ¬ SelfStabilizing (dijkstraDistRing 4 3) (DijkstraLegitimate 4 3) :=
  ⟨(dijkstraRing_selfStabilizing_iff (by decide) (by decide)).mpr (by decide),
    (dijkstraDistRing_selfStabilizing_iff (by decide) (by decide)).not.mpr (by decide)⟩

/-- Explicit `8`-step central-daemon non-stabilizing cycle on `n = 4, K = 2` from `(0, 0, 1, 0)`,
and `15`-step central-daemon non-stabilizing cycle on `n = 5, K = 3` from `(0, 0, 2, 1, 0)`. -/
theorem central_non_stabilizing_cycles_checked :
    let s42 : Fin 4 → Fin 2 := vec4 0 0 1 0
    let sched42 : List (Fin 4) := [0, 3, 2, 1, 0, 3, 2, 1]
    let s53 : Fin 5 → Fin 3 := vec5 0 0 2 1 0
    let sched53 : List (Fin 5) := [0, 4, 3, 2, 1, 0, 4, 3, 2, 1, 0, 4, 3, 2, 1]
    (∀ i, runCentral s42 sched42 i = s42 i) ∧
      (∀ k : Fin (sched42.length + 1),
        2 ≤ (dijkstraPrivilegedSet (runCentral s42 (sched42.take k.val))).card) ∧
      (∀ i, runCentral s53 sched53 i = s53 i) ∧
      (∀ k : Fin (sched53.length + 1),
        2 ≤ (dijkstraPrivilegedSet (runCentral s53 (sched53.take k.val))).card) := by
  decide

/-! ### General `Basic.lean` `SelfStabilizing` consequences on `dijkstraRing 4 4` -/

/-- Every initial state on `dijkstraRing 4 4` admits an infinite execution that eventually enters
and forever remains in `DijkstraLegitimate 4 4`. -/
theorem fin4_k4_exists_stabilizing_omegaExecution (s₀ : Fin 4 → Fin 4) :
    ∃ (ss : ωSequence (Fin 4 → Fin 4)) (μs : ωSequence (Fin 4)),
      ss 0 = s₀ ∧ (dijkstraRing 4 4).OmegaExecution ss μs ∧
        ∃ k₀, ∀ k ≥ k₀, ss k ∈ DijkstraLegitimate 4 4 := by
  have hss :=
    dijkstraRing_selfStabilizing_of_pred_le (n := 4) (K := 4) (by decide) (by decide) (by decide)
  obtain ⟨ss, μs, h0, hexec⟩ := hss.exists_omegaExecution s₀
  exact ⟨ss, μs, h0, hexec, hss.eventually_legitimate hexec⟩

/-! ### Composite anonymous ring `n = 4 = 2 * 2`: symmetry persistence and impossibility -/

private def sampleUniformRing : UniformRingProtocol (Fin 2) where
  privileged l s r := decide (l ≠ s ∨ s = r)
  step _ s _ := s + 1

/-- Concrete `2`-periodic configuration `(0, 1, 0, 1)` on `Fin (2 * 2)` has an even number (`4`) of
privileges, and stepping the independent coset `{0, 2}` one node at a time (`0` then `2`) under
the central daemon passes through a `3`-privilege intermediate state `(1, 1, 0, 1)` back to a
`2`-periodic configuration `(1, 1, 1, 1)` (`4` privileges), never visiting `UniquePrivilege`. -/
theorem composite_fin4_coset_sweep_checked :
    let u₀ : Fin (2 * 2) → Fin 2 := vec4 0 1 0 1
    let u₁ := Function.update u₀ 0 (sampleUniformRing.nextVal u₀ 0)
    let u₂ := Function.update u₁ 2 (sampleUniformRing.nextVal u₁ 2)
    sampleUniformRing.isPrivileged u₀ 0 = true ∧
      sampleUniformRing.isPrivileged u₁ 2 = true ∧
      (sampleUniformRing.privilegedSet u₀).card = 4 ∧
      (sampleUniformRing.privilegedSet u₁).card = 3 ∧
      (sampleUniformRing.privilegedSet u₂).card = 4 ∧
      (∀ i j : Fin (2 * 2), i.val % 2 = j.val % 2 → u₂ i = u₂ j) := by
  decide

/-- Enabled-move composite-ring symmetry steps on `Fin (2 * 2)`: no uniform deterministic ring
protocol satisfies `SelfStabilizing` to unique-privilege configurations under `π.centralLTS` or
`π.distLTS`, and synchronous simultaneous steps preserve `2`-periodicity with even privilege
count. -/
theorem composite_fin4_impossibility (π : UniformRingProtocol Bool) :
    (¬ SelfStabilizing (π.centralLTS (2 * 2)) (π.UniquePrivilege (2 * 2)) ∧
      ¬ SelfStabilizing (π.distLTS (2 * 2)) (π.UniquePrivilege (2 * 2))) ∧
    ∀ s : Fin (2 * 2) → Bool, IsRingPeriodic 2 s →
      2 ∣ (π.privilegedSet s).card ∧
        IsRingPeriodic 2 (fun j => if j ∈ (Finset.univ : Finset (Fin (2 * 2))) then
          π.nextVal s j else s j) :=
  ⟨⟨not_uniform_enabledMove_selfStabilizing_composite_ring
        (by decide) (by decide) π Set.Subset.rfl,
      not_uniform_distEnabledMove_selfStabilizing_composite_ring
        (by decide) (by decide) π Set.Subset.rfl⟩,
    fun _ hs =>
      ⟨π.card_privilegedSet_dvd_of_isRingPeriodic (by decide) (by decide) hs,
        π.isRingPeriodic_distStep (by decide) (by decide) hs fun _ _ _ => by simp⟩⟩

end CslibFrontierTests.Distributed.SelfStabilization
