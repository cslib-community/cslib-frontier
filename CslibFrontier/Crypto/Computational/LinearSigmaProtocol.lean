/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.DiffieHellman.SampleExp
public import CslibFrontier.Crypto.Protocols.SigmaProtocol.Computational
public import CslibFrontier.Crypto.Protocols.SigmaProtocol.Linear
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Probability.PMF

/-!
# Fair-coin commitment and special-HVZK transfer for linear Sigma protocols

In `SigmaProtocol.linear` ([BonehShoup2023], Sections 19.1 and 19.5.1–19.5.4), the honest prover
draws its commitment nonce from the exact uniform distribution on the witness module at the `PMF`
level. Over a `PrimeOrderGroupFamily`, a strict PPT machine with fair coins cannot sample `ZMod q`
with zero error when `q` is not a power of two; instead it samples `s ← F.sampleExp n d` and reads
`s mod q`, within statistical distance `1 / 2 ^ n` of uniform (`closeTo_uniform_sampleExp`).

This module equips any single-scalar `SigmaProtocol.linear` family over a `PrimeOrderGroupFamily`
with that fair-coin commitment sampler (`linearProbCommit`, `linearProbFamily`) and proves the
completeness and honest-verifier zero-knowledge transfer theorems once, consumed by both Schnorr's
protocol (`CslibFrontier.Crypto.Computational.SchnorrProtocol`) and the Chaum–Pedersen protocol
(`CslibFrontier.Crypto.Computational.ChaumPedersenProtocol`).

## Main definitions

* `Cslib.Crypto.PrimeOrderGroupFamily.linearProbCommit`: fair-coin commitment sampler `(ψ i y r, r)`
  using `sampleExp`.
* `Cslib.Crypto.PrimeOrderGroupFamily.linearProbFamily`: `SigmaProtocol.linear` over `ZMod q` with
  commitment law `linearProbCommit`.

## Main results

* `Cslib.Crypto.PrimeOrderGroupFamily.closeTo_transcript_linearProbFamily`: honest transcripts of
  `linearProbFamily` and `SigmaProtocol.linear` are within `1 / 2 ^ n` at every index, witness,
  statement and challenge.
* `Cslib.Crypto.PrimeOrderGroupFamily.linearProbFamily_complete`: completeness (Definition 19.3).
* `Cslib.Crypto.PrimeOrderGroupFamily.closeTo_transcript_linearProbFamily_simulator`: `2 / 2 ^ n`
  pointwise transcript closeness when the typed simulator is within `1 / 2 ^ n` of a perfect
  simulator.
* `Cslib.Crypto.PrimeOrderGroupFamily.advantage_chvzkGame_linearProbFamily_le`: `2 / 2 ^ n`
  distinguishing advantage bound in Attack Game 20.4 against arbitrary (even computationally
  unbounded) adversaries.
* `Cslib.Crypto.PrimeOrderGroupFamily.computationalSpecialHVZK_linearProbFamily`: transfer of
  Definition 20.6 (`ComputationalSpecialHVZK`) from `SigmaProtocol.linear` to `linearProbFamily`,
  preserving the simulator and acceptance error.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Sections 19.1, 19.4, 19.5 and 20.4.2.
-/

@[expose] public section

namespace Cslib.Crypto.PrimeOrderGroupFamily

open Probability Protocols Protocols.SigmaProtocol
open scoped ENNReal NNReal

variable (F : PrimeOrderGroupFamily)

/-- Fair-coin commitment sampler for `SigmaProtocol.linear` over a `PrimeOrderGroupFamily`: at
index `i = (n, d)`, draw `s ← F.sampleExp n d`, read `r = s mod q`, and return `(ψ i y r, r)`. -/
noncomputable def linearProbCommit {Y N : ℕ × F.Desc → Type}
    [∀ i, AddCommGroup (N i)] [∀ i, Module (ZMod (F.order i.2)) (N i)]
    (ψ : ∀ i, Y i → ZMod (F.order i.2) →ₗ[ZMod (F.order i.2)] N i)
    (i : ℕ × F.Desc) (_ : ZMod (F.order i.2)) (y : Y i) :
    ProbComp (N i × ZMod (F.order i.2)) :=
  (fun r : ZMod (F.order i.2) => (ψ i y r, r)) <$>
    ((Nat.cast : ℕ → ZMod (F.order i.2)) <$> F.sampleExp i.1 i.2)

/-- `SigmaProtocol.linear` over `ZMod q` with its commitment nonce sampled from fair coins by
`sampleExp` (`linearProbCommit`). -/
noncomputable def linearProbFamily {Y N C : ℕ × F.Desc → Type}
    [∀ i, AddCommGroup (N i)] [∀ i, Module (ZMod (F.order i.2)) (N i)] [∀ i, DecidableEq (N i)]
    (ψ : ∀ i, Y i → ZMod (F.order i.2) →ₗ[ZMod (F.order i.2)] N i)
    (u : ∀ i, Y i → N i) (ι : ∀ i : ℕ × F.Desc, C i ↪ ZMod (F.order i.2)) (i : ℕ × F.Desc) :
    SigmaProtocol (ZMod (F.order i.2)) (Y i) (N i) (C i) (ZMod (F.order i.2)) where
  State := ZMod (F.order i.2)
  commit x y := ProbComp.eval (F.linearProbCommit ψ i x y)
  respond x _ r c := r + ι i c • x
  verify y t c z := decide (ψ i y z = t + ι i c • u i y)

/-- The honest transcript of `linearProbFamily` is within statistical distance `1 / 2 ^ n` of the
ideal-nonce `SigmaProtocol.linear` transcript at every index `i = (n, d)`, witness, statement and
challenge. -/
theorem closeTo_transcript_linearProbFamily {Y N C : ℕ × F.Desc → Type}
    [∀ i, AddCommGroup (N i)] [∀ i, Module (ZMod (F.order i.2)) (N i)] [∀ i, DecidableEq (N i)]
    (ψ : ∀ i, Y i → ZMod (F.order i.2) →ₗ[ZMod (F.order i.2)] N i)
    (u : ∀ i, Y i → N i) (ι : ∀ i : ℕ × F.Desc, C i ↪ ZMod (F.order i.2))
    (i : ℕ × F.Desc) (x : ZMod (F.order i.2)) (y : Y i) (c : C i) :
    CloseTo ((linear (ψ i) (u i) (ι i)).transcript x y c)
      ((F.linearProbFamily ψ u ι i).transcript x y c) (1 / 2 ^ i.1 : ℝ≥0) := by
  rw [linear_transcript]
  have hrhs : (F.linearProbFamily ψ u ι i).transcript x y c =
      ((ProbComp.eval (F.sampleExp i.1 i.2)).map (Nat.cast : ℕ → ZMod (F.order i.2))).map
        fun r : ZMod (F.order i.2) => (ψ i y r, r + ι i c • x) := by
    simp only [SigmaProtocol.transcript, linearProbFamily, linearProbCommit, ProbComp.eval_map,
      PMF.map_comp, Function.comp_def]
  rw [hrhs]
  exact (F.closeTo_uniform_sampleExp i.1 i.2).map _

/-- Completeness of `linearProbFamily` ([BonehShoup2023], Theorem 19.12 with Definition 19.3). -/
theorem linearProbFamily_complete {Y N C : ℕ × F.Desc → Type}
    [∀ i, AddCommGroup (N i)] [∀ i, Module (ZMod (F.order i.2)) (N i)] [∀ i, DecidableEq (N i)]
    (ψ : ∀ i, Y i → ZMod (F.order i.2) →ₗ[ZMod (F.order i.2)] N i)
    (u : ∀ i, Y i → N i) (ι : ∀ i : ℕ × F.Desc, C i ↪ ZMod (F.order i.2)) (i : ℕ × F.Desc) :
    (F.linearProbFamily ψ u ι i).Complete fun x y => ψ i y x = u i y := by
  intro x y hxy c tz htz
  simp only [SigmaProtocol.transcript, linearProbFamily, linearProbCommit, ProbComp.eval_map,
    PMF.map_comp, PMF.mem_support_map_iff] at htz
  obtain ⟨s, -, rfl⟩ := htz
  change (linear (ψ i) (u i) (ι i)).Accepts y (ψ i y (s : ZMod (F.order i.2))) c
    ((s : ZMod (F.order i.2)) + ι i c • x)
  simp only [linear_accepts_iff, map_add, map_smul, hxy]

/-- When `sim` realizes a perfect simulator for `linear (ψ i) (u i) (ι i)` up to `1 / 2 ^ n`, its
output is within statistical distance `2 / 2 ^ n` of the honest transcript of `linearProbFamily`
on every valid pair and challenge. -/
theorem closeTo_transcript_linearProbFamily_simulator {Y N C : ℕ × F.Desc → Type}
    [∀ i, AddCommGroup (N i)] [∀ i, Module (ZMod (F.order i.2)) (N i)] [∀ i, DecidableEq (N i)]
    {ψ : ∀ i, Y i → ZMod (F.order i.2) →ₗ[ZMod (F.order i.2)] N i}
    {u : ∀ i, Y i → N i} {ι : ∀ i : ℕ × F.Desc, C i ↪ ZMod (F.order i.2)}
    {R : ∀ i, ZMod (F.order i.2) → Y i → Prop}
    {simulate : ∀ i, Y i → C i → PMF (N i × ZMod (F.order i.2))}
    {sim : Simulator (ℕ × F.Desc) Y N C (fun i => ZMod (F.order i.2))}
    (hS : ∀ i, (linear (ψ i) (u i) (ι i)).SpecialHVZK (R i) (simulate i))
    (hreal : SimulatorRealizedBy simulate sim (fun i => 1 / 2 ^ i.1))
    {i : ℕ × F.Desc} {x : ZMod (F.order i.2)} {y : Y i} (hxy : R i x y) (c : C i) :
    CloseTo ((F.linearProbFamily ψ u ι i).transcript x y c)
      (ProbComp.eval (sim i y c)) (2 / 2 ^ i.1) := by
  have hcoe : (((1 / 2 ^ i.1 : ℝ≥0)) : ℝ≥0∞) = 1 / 2 ^ i.1 := by
    rw [ENNReal.coe_div (pow_ne_zero _ two_ne_zero), ENNReal.coe_one, ENNReal.coe_pow,
      ENNReal.coe_ofNat]
  have htrans : CloseTo ((linear (ψ i) (u i) (ι i)).transcript x y c)
      ((F.linearProbFamily ψ u ι i).transcript x y c) (1 / 2 ^ i.1 : ℝ≥0∞) := by
    rw [← hcoe]
    exact F.closeTo_transcript_linearProbFamily ψ u ι i x y c
  have h12 := hreal.closeTo_transcript_of_closeTo (δP := fun i => 1 / 2 ^ i.1) hS hxy htrans
  have hadd : (1 / 2 ^ i.1 : ℝ≥0∞) + 1 / 2 ^ i.1 = 2 / 2 ^ i.1 := by
    rw [← ENNReal.add_div, one_add_one_eq_two]
  rwa [hadd] at h12

/-- When `sim` realizes a perfect simulator for `linear (ψ i) (u i) (ι i)` up to `1 / 2 ^ n`,
Attack Game 20.4 distinguishing advantage for `linearProbFamily` over `(setup m).map (m, ·)` is at
most `2 / 2 ^ n` against every adversary (including computationally unbounded ones). -/
theorem advantage_chvzkGame_linearProbFamily_le {Y N C : ℕ × F.Desc → Type} {σ : Type}
    [∀ i, AddCommGroup (N i)] [∀ i, Module (ZMod (F.order i.2)) (N i)] [∀ i, DecidableEq (N i)]
    [∀ i, Fintype (C i)] [∀ i, Nonempty (C i)]
    {ψ : ∀ i, Y i → ZMod (F.order i.2) →ₗ[ZMod (F.order i.2)] N i}
    {u : ∀ i, Y i → N i} {ι : ∀ i : ℕ × F.Desc, C i ↪ ZMod (F.order i.2)}
    {R : ∀ i, ZMod (F.order i.2) → Y i → Prop}
    {simulate : ∀ i, Y i → C i → PMF (N i × ZMod (F.order i.2))}
    {sim : Simulator (ℕ × F.Desc) Y N C (fun i => ZMod (F.order i.2))}
    (hS : ∀ i, (linear (ψ i) (u i) (ι i)).SpecialHVZK (R i) (simulate i))
    (hreal : SimulatorRealizedBy simulate sim (fun i => 1 / 2 ^ i.1))
    (setup : ℕ → PMF F.Desc)
    (A : CHVZKAdversary (ℕ × F.Desc) (fun i => ZMod (F.order i.2)) Y N C
      (fun i => ZMod (F.order i.2)) σ) (n : ℕ) :
    Game.advantage
      (chvzkRealGame (F.linearProbFamily ψ u ι) R (fun m => (setup m).map (m, ·)) A n)
      (chvzkSimGame R (fun m => (setup m).map (m, ·)) sim A n) ≤
      2 / 2 ^ n := by
  refine (hreal.advantage_chvzkGame_le_of_closeTo_transcript
    (P' := F.linearProbFamily ψ u ι) (εP := 1 / 2 ^ n) (εS := 1 / 2 ^ n) hS
    (fun i hi x y _ c => ?_) (fun i hi => ?_) A).trans_eq ?_
  · obtain ⟨d, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hi
    exact F.closeTo_transcript_linearProbFamily ψ u ι (n, d) x y c
  · obtain ⟨d, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hi
    dsimp only
    rw [ENNReal.coe_div (pow_ne_zero _ two_ne_zero), ENNReal.coe_one, ENNReal.coe_pow,
      ENNReal.coe_ofNat]
  · ext
    push_cast
    ring

/-- Transfer `ComputationalSpecialHVZK` from the ideal-nonce `SigmaProtocol.linear` family to the
fair-coin `linearProbFamily` over `(setup n).map (n, ·)`, preserving the simulator and acceptance
error. -/
theorem computationalSpecialHVZK_linearProbFamily {Y N C : ℕ × F.Desc → Type}
    [∀ i, AddCommGroup (N i)] [∀ i, Module (ZMod (F.order i.2)) (N i)] [∀ i, DecidableEq (N i)]
    [∀ i, Fintype (C i)] [∀ i, Nonempty (C i)]
    {ψ : ∀ i, Y i → ZMod (F.order i.2) →ₗ[ZMod (F.order i.2)] N i}
    {u : ∀ i, Y i → N i} {ι : ∀ i : ℕ × F.Desc, C i ↪ ZMod (F.order i.2)}
    {R : ∀ i, ZMod (F.order i.2) → Y i → Prop}
    {enc : Encoding (ℕ × F.Desc) Y N C (fun i => ZMod (F.order i.2))}
    {encW : ∀ i : ℕ × F.Desc, ZMod (F.order i.2) ↪ List Bool}
    {setup : ℕ → PMF F.Desc}
    {sim : Simulator (ℕ × F.Desc) Y N C (fun i => ZMod (F.order i.2))}
    {δ : ℕ × F.Desc → ℝ≥0∞}
    (h : ComputationalSpecialHVZK (fun i => linear (ψ i) (u i) (ι i)) R enc encW
      (fun n => (setup n).map (n, ·)) sim δ) :
    ComputationalSpecialHVZK (F.linearProbFamily ψ u ι) R enc encW
      (fun n => (setup n).map (n, ·)) sim δ := by
  refine h.of_closeTo_transcript (fun _ _ _ _ _ hacc => hacc)
    ⟨fun n => (1 / 2 : ℝ≥0) ^ n, negligible_geometric (by norm_num), ?_⟩
  intro n i hi x y _ c
  obtain ⟨d, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hi
  simpa only [one_div_pow] using F.closeTo_transcript_linearProbFamily ψ u ι (n, d) x y c

end Cslib.Crypto.PrimeOrderGroupFamily
