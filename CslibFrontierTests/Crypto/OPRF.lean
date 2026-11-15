/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Crypto.Protocols.OPRF.DiffieHellman
public import Mathlib.Algebra.Field.ZMod

/-!
# Diffie–Hellman oblivious pseudorandom functions: checked instances and hypothesis probes

An ordinary `module` client of `CslibFrontier.Crypto.Protocols.OPRF.DiffieHellman`
([BonehShoup2023], Section 11.6.3, pp. 454–456):

* In `ZMod 3` with generator `1`, the nonzero hashed inputs `2` and `1` induce the same `OPRF1`
  message distribution (`uniformOfFintype_bind_blind_of_ne_zero`).
* `h ≠ 0` is required in `uniformOfFintype_bind_blind_of_ne_zero`: in `ZMod 3`, `blind ρ 0` is
  always `0`, which `blind ρ 1` never is.
* Primality of `q` is required in `uniformOfFintype_bind_blind_of_ne_zero`: in `ZMod 4` with
  generator `1`, the input `2` is nonzero yet `blind ρ 2 = 2` for every unit `ρ`, whereas
  `blind ρ 1` can be `1`.
* `g` generating the group is required in `uniformOfFintype_bind_maskedBlind`: in `ZMod 2` with
  `g = 0`, `maskedBlind 0 1 τ 1` is always `1`, whereas `τ • 0` is always `0`.
* `d v ≠ 0` is required in `uniformOfFintype_bind_maskedUnblind_add_of_ne_zero`: in `ZMod 3`, an
  honest sender (`d = 0`) makes the receiver compute `k • h`, which `k • h + blind ρ g` never is.
-/

public section

namespace CslibFrontierTests.Crypto.OPRF

open Cslib Cslib.Probability Cslib.Crypto.Protocols.OPRF

/-- The hypotheses of `uniformOfFintype_bind_blind_of_ne_zero` hold in `ZMod 3` with generator `1`:
the nonzero inputs `2` and `1` give the sender of `OPRF1` the same view. -/
example (f : ZMod 3 → PMF Bool) :
    ((PMF.uniformOfFintype (ZMod 3)ˣ).bind fun ρ => f (blind ρ (2 : ZMod 3))) =
      (PMF.uniformOfFintype (ZMod 3)ˣ).bind fun ρ => f (blind ρ (1 : ZMod 3)) :=
  uniformOfFintype_bind_blind_of_ne_zero (g := (1 : ZMod 3)) (h := (2 : ZMod 3))
    (fun c => ⟨c, by simp⟩) (by decide) f

/-- `h ≠ 0` is needed in `uniformOfFintype_bind_blind_of_ne_zero`: the hashed input `0` is always
sent as `0`, which no nonzero input in `ZMod 3` is. -/
example :
    ((PMF.uniformOfFintype (ZMod 3)ˣ).bind fun ρ => PMF.pure (blind ρ (0 : ZMod 3))) ≠
      (PMF.uniformOfFintype (ZMod 3)ˣ).bind fun ρ => PMF.pure (blind ρ (1 : ZMod 3)) := by
  intro h
  have hmem : (0 : ZMod 3) ∈
      ((PMF.uniformOfFintype (ZMod 3)ˣ).bind fun ρ => PMF.pure (blind ρ (0 : ZMod 3))).support := by
    simp [blind]
  rw [h] at hmem
  simp [blind] at hmem

/-- Primality of `q` is needed in `uniformOfFintype_bind_blind_of_ne_zero`: in `ZMod 4` with
generator `1`, the input `2` is nonzero and is always sent as `2`, which the input `1` never is. -/
example : (2 : ZMod 4) ≠ 0 ∧ (Function.Surjective fun c : ZMod 4 => c • (1 : ZMod 4)) ∧
    ((PMF.uniformOfFintype (ZMod 4)ˣ).bind fun ρ => PMF.pure (blind ρ (2 : ZMod 4))) ≠
      (PMF.uniformOfFintype (ZMod 4)ˣ).bind fun ρ => PMF.pure (blind ρ (1 : ZMod 4)) := by
  refine ⟨by decide, fun c => ⟨c, by simp⟩, fun h => ?_⟩
  have key : ∀ x : ZMod 4, x * 2 ≠ 1 := by decide
  have hmem : (1 : ZMod 4) ∈
      ((PMF.uniformOfFintype (ZMod 4)ˣ).bind fun ρ => PMF.pure (blind ρ (1 : ZMod 4))).support := by
    simp only [PMF.mem_support_bind_iff, PMF.support_pure, Set.mem_singleton_iff]
    exact ⟨1, by simp, by simp [blind]⟩
  rw [← h] at hmem
  simp only [PMF.mem_support_bind_iff, PMF.support_pure, Set.mem_singleton_iff, blind,
    smul_eq_mul] at hmem
  obtain ⟨ρ, -, hρ⟩ := hmem
  exact key _ hρ.symm

/-- `g` must generate the group in `uniformOfFintype_bind_maskedBlind`: with `g = 0` in `ZMod 2`,
the message of `OPRF2` equals the blinded input rather than `τ • 0`. -/
example :
    ((PMF.uniformOfFintype (ZMod 2)).bind fun τ => PMF.pure (maskedBlind (0 : ZMod 2) 1 τ 1)) ≠
      (PMF.uniformOfFintype (ZMod 2)).bind fun τ => PMF.pure (τ • (0 : ZMod 2)) := by
  intro h
  have hmem : (1 : ZMod 2) ∈ ((PMF.uniformOfFintype (ZMod 2)).bind fun τ =>
      PMF.pure (maskedBlind (0 : ZMod 2) 1 τ 1)).support := by
    simp [maskedBlind, blind]
  rw [h] at hmem
  simp at hmem

/-- `d v ≠ 0` is needed in `uniformOfFintype_bind_maskedUnblind_add_of_ne_zero`: in `ZMod 3`, an
honest sender (`d = 0`) makes the receiver compute `k • h`, which `k • h + blind ρ g` never is. -/
example :
    ((PMF.uniformOfFintype (ZMod 3)ˣ).bind fun ρ => (PMF.uniformOfFintype (ZMod 3)).bind fun τ =>
        PMF.pure (maskedUnblind ((2 : ZMod 3) • (1 : ZMod 3)) ρ τ
          (respond (2 : ZMod 3) (maskedBlind (1 : ZMod 3) ρ τ (1 : ZMod 3)) + 0))) ≠
      (PMF.uniformOfFintype (ZMod 3)).bind fun _ => (PMF.uniformOfFintype (ZMod 3)ˣ).bind fun ρ =>
        PMF.pure ((2 : ZMod 3) • (1 : ZMod 3) + blind ρ (1 : ZMod 3)) := by
  intro h
  have hmem : (2 : ZMod 3) • (1 : ZMod 3) ∈
      ((PMF.uniformOfFintype (ZMod 3)ˣ).bind fun ρ => (PMF.uniformOfFintype (ZMod 3)).bind fun τ =>
        PMF.pure (maskedUnblind ((2 : ZMod 3) • (1 : ZMod 3)) ρ τ
          (respond (2 : ZMod 3) (maskedBlind (1 : ZMod 3) ρ τ (1 : ZMod 3)) + 0))).support := by
    simp only [add_zero, maskedUnblind_respond_maskedBlind]
    simp
  rw [h] at hmem
  simp [blind] at hmem

end CslibFrontierTests.Crypto.OPRF
