/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Crypto.Computational.KeyDerivation
import CslibFrontier.Crypto.Computational.ElGamal.KDF
import CslibFrontier.Crypto.Computational.ElGamal.KeyDerivation
import CslibFrontier.Crypto.Game.HiddenBit
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Tactic.PPT

/-!
# Tests for the key-derivation security game

Clients of `CslibFrontier.Crypto.Computational.KeyDerivation` and
`CslibFrontier.Crypto.Computational.ElGamal.KeyDerivation` under module encapsulation:

* with no side information, the identity derivation of a key drawn from `key` is `Secure` for every
  `key`;
* `not_secure_const`: a constant derivation is not `Secure` for a uniform one-bit key;
* side information matters: the identity derivation of a uniform bit that is also published is not
  `Secure`;
* Attack Game 11.3 as printed (`F : X × Y → Z` on independent uniform `x` and `y` with `info =
  Prod.fst` and `derive = F`) unfolds `realOutput` and `idealOutput` to the textbook experiments;
* `secureKDF_linearHashKDF` transports through `secureKDF_iff_keyDerivation` to an unconditional
  instance of `KeyDerivation.Secure`.
-/

public section

namespace CslibFrontierTests.Crypto.KeyDerivation

open Cslib Probability Cslib.Crypto Cslib.Crypto.KeyDerivation Turing.MultiTapeTM
open scoped NNReal

/-- Nonvacuity: with no side information, the identity derivation of a key drawn from `key` is
secure, for every `key`. -/
example {Z : Type} (encU : Unit ↪ List Bool) (encZ : Z ↪ List Bool) (key : ℕ → PMF Z) :
    Secure encU encZ key (fun _ => ()) id key := fun D _ =>
  negligible_zero.congr fun n => by
    simp [realGame, idealGame, realOutput, idealOutput, Game.advantage]

/-- A constant derivation is not secure for a uniform one-bit key. -/
theorem not_secure_const : ¬ Secure encUnit encBool (fun _ => PMF.pure ()) id (fun _ => false)
    (fun _ => PMF.uniformOfFintype Bool) := by
  intro h
  have hD : Distinguisher.IsPPT encUnit encBool (fun _ _ z => pure z) := by
    unfold Distinguisher.IsPPT
    ppt
  refine not_negligible_const (c := 1 / 2) (by norm_num) ((h _ hD).congr fun n => ?_)
  have h1 : realGame (fun _ => PMF.pure ()) id (fun _ => false) (fun _ _ z => pure z) n =
      PMF.pure false := by simp [realGame, realOutput]
  have h2 : idealGame (fun _ => PMF.pure ()) (id : Unit → Unit)
      (fun _ => PMF.uniformOfFintype Bool) (fun _ _ z => pure z) n = PMF.uniformOfFintype Bool := by
    simp [idealGame, idealOutput]
  rw [h1, h2]
  apply NNReal.eq
  rw [Game.coe_guessingAdvantage]
  simp

/-- Side information matters: the identity derivation of a uniform bit that is also published is
not secure, although without the side information it is (first example). -/
example : ¬ Secure encBool encBool (fun _ => PMF.uniformOfFintype Bool) id id
    (fun _ => PMF.uniformOfFintype Bool) := by
  intro h
  have hD : Distinguisher.IsPPT encBool encBool (fun _ x z => pure (x == z)) := by
    unfold Distinguisher.IsPPT
    ppt
  refine not_negligible_const (c := 1 / 2) (by norm_num) ((h _ hD).congr fun n => ?_)
  have h1 : realGame (fun _ => PMF.uniformOfFintype Bool) id id (fun _ x z => pure (x == z)) n =
      PMF.pure true := by simp [realGame, realOutput]
  have h2 : idealGame (fun _ => PMF.uniformOfFintype Bool) (id : Bool → Bool)
      (fun _ => PMF.uniformOfFintype Bool) (fun _ x z => pure (x == z)) n =
      PMF.uniformOfFintype Bool := by
    simpa only [idealGame, idealOutput, id_eq, ProbComp.eval_pure, PMF.map, Function.comp_def,
      Bool.beq_comm] using Game.uniform_bool_bind_map_beq_const (PMF.uniformOfFintype Bool)
  rw [h1, h2]
  apply NNReal.eq
  rw [Game.coe_guessingAdvantage]
  simp
  norm_num

/-- Attack Game 11.3 as printed: `F : X × Y → Z`, independent uniform `x` and `y`, and the
adversary sees `x`. It is the instance `info = Prod.fst`, `derive = F`. -/
example {X Y Z : Type} [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y] (F : X × Y → Z)
    (D : X → Z → PMF Bool) :
    realOutput (do
        let x ← PMF.uniformOfFintype X
        let y ← PMF.uniformOfFintype Y
        return (x, y)) Prod.fst F D =
      (PMF.uniformOfFintype X).bind fun x => (PMF.uniformOfFintype Y).bind fun y =>
        D x (F (x, y)) := by
  simp only [realOutput, pmf_norm]

example {X Y Z : Type} [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y] [Fintype Z] [Nonempty Z]
    (D : X → Z → PMF Bool) :
    idealOutput (do
        let x ← PMF.uniformOfFintype X
        let y ← PMF.uniformOfFintype Y
        return (x, y)) Prod.fst (PMF.uniformOfFintype Z) D =
      (PMF.uniformOfFintype X).bind fun x => (PMF.uniformOfFintype Z).bind fun z => D x z := by
  simp only [idealOutput, pmf_norm, PMF.bind_const]

/-- `secureKDF_linearHashKDF` yields an instance of `KeyDerivation.Secure` through
`secureKDF_iff_keyDerivation`. -/
example (F : PrimeOrderGroupFamily) {setup : ℕ → PMF F.Desc} {keyLen bound : F.Desc → ℕ}
    {msgLen qMin : ℕ → ℕ} (h : F.LinearHashKDFConditions setup keyLen bound msgLen qMin) :
    Secure F.withSeed.encCDHInput encBits
      (F.withSeed.kdfSecret (F.seededSetup setup (F.linearHashSeedLen msgLen bound))) Sigma.fst
      (fun s => F.linearHashKDF keyLen bound
        (s.1.groupParameters, F.withSeed.encode s.1.groupParameters s.2))
      (fun n => Cslib.BitString.uniformList (msgLen n)) :=
  (F.withSeed.secureKDF_iff_keyDerivation _ _ _).mp (F.secureKDF_linearHashKDF h)

end CslibFrontierTests.Crypto.KeyDerivation
