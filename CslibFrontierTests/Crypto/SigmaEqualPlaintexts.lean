/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test suite)

import CslibFrontier.Crypto.Protocols.SigmaProtocol.EqualPlaintexts

/-!
# Tests for the equal-plaintexts Sigma protocol

Checks `Cslib.Crypto.Protocols.SigmaProtocol.EqualPlaintexts`:

* Concrete accepting and rejecting conversations, relation checks, and special-soundness witness
  extraction over `ZMod 11` (`decide`).
* Re-encryption via `equalPlaintextsRelation_reencrypt` and honest acceptance via
  `equalPlaintexts_complete`.
* Necessity of the generator hypothesis in `exists_equalPlaintextsRelation_iff` on
  `ZMod 2 × ZMod 2` with `g = (1, 0)`.
* Soundness bound `1 / 11` via `equalPlaintexts_sound` for ciphertexts of distinct messages in
  `ZMod 11`.
* Completeness for a prover holding `(β₀, β₁, m)` via `equalPlaintextsRelation_sub` and
  `Complete.comap`.
-/

namespace CslibFrontierTests.Crypto.SigmaEqualPlaintexts

open Cslib Cslib.Interactive Cslib.Crypto.Protocols SigmaProtocol
open scoped ENNReal

/-- Concrete check over `ZMod 11`: with `g = 2`, public key `u = 3 • 2 = 6`, message `m = 5`,
and randomness `β₀ = 4`, `β₁ = 7`, the ciphertexts `(8, 7)` and `(3, 3)` satisfy
`equalPlaintextsRelation` with witness `β = 4 - 7 = 8`. -/
example : equalPlaintextsRelation (q := 11) (2 : ZMod 11) 8 (6, (8, 7), (3, 3)) := by
  simp only [equalPlaintextsRelation]
  decide

/-- Accepting conversation over `ZMod 11`: with commitment randomness `r = 5` giving commitment
`(10, 8)` and challenge `3`, response `z = 5 + 3 * 8 = 7` is accepted, while `z = 8` is
rejected. -/
example :
    (equalPlaintexts (Function.Embedding.refl (ZMod 11)) (2 : ZMod 11)).Accepts
      ((6 : ZMod 11), (8, 7), (3, 3)) (10, 8) 3 7 := by
  decide

example :
    ¬ (equalPlaintexts (Function.Embedding.refl (ZMod 11)) (2 : ZMod 11)).Accepts
      ((6 : ZMod 11), (8, 7), (3, 3)) (10, 8) 3 8 := by
  decide

/-- Witness extraction over `ZMod 11`: from accepting challenges `3` (response `7`) and `6`
(response `9`) at commitment `(10, 8)`, `equalPlaintexts_specialSoundness` certifies that
`linearExtract` returns a witness of `equalPlaintextsRelation`, which evaluates to `8`. -/
example :
    equalPlaintextsRelation (q := 11) (2 : ZMod 11)
      (linearExtract (Function.Embedding.refl (ZMod 11))
        (equalPlaintextsTriple (G := ZMod 11) (6, (8, 7), (3, 3)))
        ((10, 8) : ZMod 11 × ZMod 11) 3 (7 : ZMod 11) 6 9)
      ((6 : ZMod 11), (8, 7), (3, 3)) ∧
      linearExtract (Function.Embedding.refl (ZMod 11))
        (equalPlaintextsTriple (G := ZMod 11) (6, (8, 7), (3, 3)))
        ((10, 8) : ZMod 11 × ZMod 11) 3 (7 : ZMod 11) 6 9 = 8 := by
  have hne : (3 : ZMod 11) ≠ 6 := by decide
  have hacc₁ : (equalPlaintexts (Function.Embedding.refl (ZMod 11)) (2 : ZMod 11)).Accepts
      ((6 : ZMod 11), (8, 7), (3, 3)) (10, 8) 3 7 := by decide
  have hacc₂ : (equalPlaintexts (Function.Embedding.refl (ZMod 11)) (2 : ZMod 11)).Accepts
      ((6 : ZMod 11), (8, 7), (3, 3)) (10, 8) 6 9 := by decide
  have hex : linearExtract (Function.Embedding.refl (ZMod 11))
      (equalPlaintextsTriple (G := ZMod 11) (6, (8, 7), (3, 3)))
      ((10, 8) : ZMod 11 × ZMod 11) 3 (7 : ZMod 11) 6 9 = 8 := by decide +kernel
  have : Fact (Nat.Prime 11) := ⟨by decide⟩
  exact ⟨equalPlaintexts_specialSoundness ((6 : ZMod 11), (8, 7), (3, 3))
      ((10, 8) : ZMod 11 × ZMod 11) 3 7 6 9 hne hacc₁ hacc₂, hex⟩

/-- Re-encryption client: starting from `(8, 7)` under `u = 6` and re-encrypting with exponent
`β = 9` gives `(4, 6)` with witness `-9`, so every honest transcript of `equalPlaintexts` on
witness `-9` is accepting. -/
example (c : ZMod 11) :
    ∀ tz ∈ ((equalPlaintexts (Function.Embedding.refl (ZMod 11)) (2 : ZMod 11)).transcript (-9)
        (6, (8, 7), ((8 + (9 : ZMod 11) • 2), (7 + (9 : ZMod 11) • 6))) c).support,
      (equalPlaintexts (Function.Embedding.refl (ZMod 11)) (2 : ZMod 11)).Accepts
        (6, (8, 7), ((8 + (9 : ZMod 11) • 2), (7 + (9 : ZMod 11) • 6))) tz.1 c tz.2 :=
  equalPlaintexts_complete (-9) _ (equalPlaintextsRelation_reencrypt 2 6 (8, 7) 9) c

/-- Client of `equalPlaintexts_sound`: under `u = 3 • 2 = 6`, the ciphertexts `(8, 7)` (encrypting
`5`) and `(3, 4)` (encrypting `6`) do not encrypt the same message, so every unbounded prover makes
the interactive verifier accept with probability at most `1 / 11`. -/
example (α : Type)
    (P : ProbOracleComp OracleSpec.empty
      (ProverStrategy (ProbOracleComp OracleSpec.empty)
        (equalPlaintexts (Function.Embedding.refl (ZMod 11)) (2 : ZMod 11)).interactiveSpec α)) :
    (World.plain.eval
      ((equalPlaintexts (Function.Embedding.refl (ZMod 11))
        (2 : ZMod 11)).toInteractiveVerifier.execute (6, (8, 7), (3, 4)) P)).toOuterMeasure
      {r | ∃ x' ∈ Set.univ, r.output = some x'} ≤ 1 / (11 : ℝ≥0∞) := by
  have h62 : (6 * 2 : ZMod 11) = 1 := by decide
  have h26 : (2 * 6 : ZMod 11) = 1 := by decide
  have h86 : (8 * 6 : ZMod 11) = 4 := by decide
  have h36 : (3 * 6 : ZMod 11) = 7 := by decide
  have hneq : (7 : ZMod 11) - 4 * 6 ≠ 4 - 7 * 6 := by decide
  have hsurj : Function.Surjective fun β : ZMod 11 => β • (2 : ZMod 11) := fun y =>
    ⟨6 * y, by simp only [smul_eq_mul]; rw [mul_right_comm, h62, one_mul]⟩
  have hnot :
      (6, ((8, 7) : ZMod 11 × ZMod 11), ((3, 4) : ZMod 11 × ZMod 11)) ∉
        {y : ZMod 11 × (ZMod 11 × ZMod 11) × ZMod 11 × ZMod 11 |
          let (u, ct₀, ct₁) := y
          ∃ (m β₀ β₁ : ZMod 11),
            ct₀ = (β₀ • (2 : ZMod 11), β₀ • u + m) ∧
              ct₁ = (β₁ • (2 : ZMod 11), β₁ • u + m)} := by
    rintro ⟨m, β₀, β₁, h₀, h₁⟩
    have hβ₀ : β₀ = 4 := by
      have hv₀ : β₀ * 2 = 8 := by simpa only [smul_eq_mul] using (congrArg Prod.fst h₀).symm
      calc β₀ = (β₀ * 2) * 6 := by rw [mul_assoc, h26, mul_one]
        _ = 4 := by rw [hv₀, h86]
    have hβ₁ : β₁ = 7 := by
      have hv₁ : β₁ * 2 = 3 := by simpa only [smul_eq_mul] using (congrArg Prod.fst h₁).symm
      calc β₁ = (β₁ * 2) * 6 := by rw [mul_assoc, h26, mul_one]
        _ = 7 := by rw [hv₁, h36]
    have he₀ : (7 : ZMod 11) = 4 * 6 + m := by
      simpa only [hβ₀, smul_eq_mul] using congrArg Prod.snd h₀
    have he₁ : (4 : ZMod 11) = 7 * 6 + m := by
      simpa only [hβ₁, smul_eq_mul] using congrArg Prod.snd h₁
    have hm₀ : m = 7 - 4 * 6 := eq_sub_of_add_eq' he₀.symm
    have hm₁ : m = 4 - 7 * 6 := eq_sub_of_add_eq' he₁.symm
    exact hneq (hm₀.symm.trans hm₁)
  have : Fact (Nat.Prime 11) := ⟨by decide⟩
  have h := equalPlaintexts_sound (ι := Function.Embedding.refl (ZMod 11)) hsurj Set.univ
    (6, (8, 7), (3, 4)) hnot α P
  rw [ZMod.card] at h
  exact h

/-- Necessity of the generator hypothesis in `exists_equalPlaintextsRelation_iff`: in
`ZMod 2 × ZMod 2` with `g = (1, 0)`, the statement `(0, ((0, 1), 0), ((0, 1), 0))` has witness
`β = 0` of (20.2), yet neither ciphertext is an encryption because `(0, 1)` is no multiple of
`g`. -/
example :
    (∃ β : ZMod 2, equalPlaintextsRelation (G := ZMod 2 × ZMod 2) (1, 0) β
        (0, ((0, 1), 0), ((0, 1), 0))) ∧
      ¬ ∃ (m : ZMod 2 × ZMod 2) (β₀ β₁ : ZMod 2),
        (((0, 1), 0) : (ZMod 2 × ZMod 2) × (ZMod 2 × ZMod 2)) =
            (β₀ • ((1, 0) : ZMod 2 × ZMod 2), β₀ • (0 : ZMod 2 × ZMod 2) + m) ∧
          (((0, 1), 0) : (ZMod 2 × ZMod 2) × (ZMod 2 × ZMod 2)) =
            (β₁ • ((1, 0) : ZMod 2 × ZMod 2), β₁ • (0 : ZMod 2 × ZMod 2) + m) := by
  refine ⟨⟨0, by simp [equalPlaintextsRelation]⟩, ?_⟩
  rintro ⟨m, β₀, β₁, h₀, -⟩
  have h := congrArg (fun p => p.1.2) h₀
  simp at h

/-- Necessity of `[Fact q.Prime]` in `equalPlaintexts_specialSoundness` and
`equalPlaintexts_sound`: in `ZMod 4` with generator `g = 1` and `u = 1`, the statement
`(1, (0, 2), (0, 0))` has no witness in `equalPlaintextsRelation`, yet commitment `(0, 0)` with
response `0` is accepted at distinct challenges `0` and `2`, so `SpecialSoundness` fails. -/
example :
    Function.Surjective (fun β : ZMod 4 => β • (1 : ZMod 4)) ∧
      (¬ ∃ β : ZMod 4, equalPlaintextsRelation (1 : ZMod 4) β (1, (0, 2), (0, 0))) ∧
      (0 : ZMod 4) ≠ 2 ∧
      (equalPlaintexts (Function.Embedding.refl (ZMod 4)) (1 : ZMod 4)).Accepts
        (1, (0, 2), (0, 0)) (0, 0) 0 0 ∧
      (equalPlaintexts (Function.Embedding.refl (ZMod 4)) (1 : ZMod 4)).Accepts
        (1, (0, 2), (0, 0)) (0, 0) 2 0 := by
  refine ⟨fun y => ⟨y, by simp⟩, ?_⟩
  simp only [equalPlaintextsRelation]
  decide

/-- Completeness for a prover holding `(β₀, β₁, m)`: pulling back `equalPlaintexts` along
`(β₀, β₁, m) ↦ β₀ - β₁` yields a complete protocol for ciphertext pairs `(β₀ • g, β₀ • u + m)`
and `(β₁ • g, β₁ • u + m)` via `Complete.comap` and `equalPlaintextsRelation_sub`. -/
example {q : ℕ} [NeZero q] {G C : Type} [AddCommGroup G] [Module (ZMod q) G] [DecidableEq G]
    (ι : C ↪ ZMod q) (g : G) :
    ((equalPlaintexts ι g).comap
        (fun ((β₀, β₁, _) : ZMod q × ZMod q × G) (_ : G × (G × G) × G × G) => β₀ - β₁)
        id).Complete
      (fun ((β₀, β₁, m) : ZMod q × ZMod q × G) ((u, ct₀, ct₁) : G × (G × G) × G × G) =>
        ct₀ = (β₀ • g, β₀ • u + m) ∧ ct₁ = (β₁ • g, β₁ • u + m)) :=
  equalPlaintexts_complete.comap fun (β₀, β₁, m) (u, ct₀, ct₁) ⟨h₀, h₁⟩ => by
    rw [h₀, h₁]
    exact equalPlaintextsRelation_sub g u m β₀ β₁

end CslibFrontierTests.Crypto.SigmaEqualPlaintexts
