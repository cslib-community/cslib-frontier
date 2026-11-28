/-
Copyright (c) 2026 Samuel Schlesinger, Phillipp Schoppmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Phillipp Schoppmann
-/

module

import CslibFrontier.Crypto.Protocols.SecretSharing.Shamir.Feldman
import CslibFrontier.Crypto.Protocols.SecretSharing.Shamir.Pedersen
import Mathlib.Algebra.Field.ZMod

/-!
# Concrete Tests and Counterexamples for Feldman and Pedersen VSS

Exercises `Feldman` and `Pedersen` on `(n = 4, t = 2)` Shamir sharing over `ZMod 7` (with
evaluation points `1, 2, 3, 4` and group `ZMod 7`, generator `g = 2`,
Pedersen base `h = 5 = 6 * 2`):

1. **Feldman VSS (`q = 7, t = 2, n = 4`):** honest share verification, rejecting a tampered share,
   unique degree-`≤ 2` polynomial extraction from `3` verified shares (`J = {0, 1, 2}`), and
   cross-coalition consistency between `{0, 1, 2}` and `{1, 2, 3}`.
2. **Pedersen VSS (`q = 7, t = 2, n = 4`):** honest share verification, rejecting a tampered share,
   the honest dealing as a `Pedersen.Dealing` restricted to a coalition,
   perfect hiding across distinct secrets (`a₀ = 3` vs `a₁ = 5`) for an unauthorized coalition
   `I = {0, 2}` (`|I| = 2 ≤ 2`), and explicit discrete-log extraction `extractDLog = 6`
   (`6 • 2 = 5` in `ZMod 7`) from two inconsistent authorized share sets opening to `3 ≠ 5`.
3. **Boundary / necessity check (`g = 0`):** shows why `g ≠ 0` is needed for Feldman polynomial
   uniqueness (`2 ≠ 3` both verify when `g = 0`).
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.VSS

open Finset Cslib.Probability
open Cslib.Crypto.Protocols.SecretSharing
open Cslib.Crypto.Protocols.SecretSharing.Shamir

private local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

private def params4 : Params (ZMod 7) (Fin 4) where
  threshold := 2
  threshold_lt_card := by decide
  point i := (i.val + 1 : ZMod 7)
  point_injective := by decide
  point_nonzero := by decide

private def g7 : ZMod 7 := 2
private def h7 : ZMod 7 := 5 -- `6 • 2 = 5 (mod 7)`

private def ra7 : Randomness params4 := ![1, 4] -- `f(X) = 3 + X + 4 X^2`
private def rb7 : Randomness params4 := ![2, 3] -- `g_poly(X) = 1 + 2 X + 3 X^2`

/-! ### 1. Feldman VSS checks -/

private def feldC : Fin 3 → ZMod 7 := Feldman.commit params4 g7 ra7 3

example (i : Fin 4) : Feldman.verifyShare params4 g7 feldC i (share params4 ra7 3 i) :=
  Feldman.verifyShare_commit params4 g7 ra7 3 i

example : ¬ Feldman.verifyShare params4 g7 feldC 0 (share params4 ra7 3 0 + 1) := by
  have hv := Feldman.verifyShare_commit params4 g7 ra7 3 0
  intro hbad
  have heq : (share params4 ra7 3 0 + 1) • g7 = share params4 ra7 3 0 • g7 :=
    hbad.trans hv.symm
  have h0 : (1 : ZMod 7) • g7 = 0 := by
    apply add_left_cancel (a := share params4 ra7 3 0 • g7)
    rw [← add_smul, add_zero, heq]
  exact absurd h0 (by decide)

example :
    ∃! f : _root_.Polynomial (ZMod 7),
      f.degree < (params4.threshold + 1 : WithBot ℕ) ∧
      feldC = Feldman.commitPoly params4.threshold g7 f ∧
      (∀ i : Fin 4, ∀ s : ZMod 7,
        Feldman.verifyShare params4 g7 feldC i s ↔ s = f.eval (params4.point i)) := by
  refine Feldman.existsUnique_poly_of_verified params4 (by decide : g7 ≠ 0) feldC
    (J := {0, 1, 2}) (by unfold authorized params4; decide)
    (fun j => share params4 ra7 3 j.1)
    (fun j => Feldman.verifyShare_commit params4 g7 ra7 3 j.1)

example :
    let J₁ : Finset (Fin 4) := {0, 1, 2}
    let J₂ : Finset (Fin 4) := {1, 2, 3}
    reconstruct params4 J₁ (fun j : J₁ => share params4 ra7 3 j.1) =
      reconstruct params4 J₂ (fun j : J₂ => share params4 ra7 3 j.1) :=
  Feldman.reconstruct_eq_of_verified params4 (by decide : g7 ≠ 0) feldC
    (by unfold authorized params4; decide) (by unfold authorized params4; decide)
    (fun j => share params4 ra7 3 j.1) (fun j => share params4 ra7 3 j.1)
    (fun j => Feldman.verifyShare_commit params4 g7 ra7 3 j.1)
    (fun j => Feldman.verifyShare_commit params4 g7 ra7 3 j.1)

/-! ### 2. Pedersen VSS checks: completeness, perfect hiding, and discrete-log extraction -/

private def pedC : Fin 3 → ZMod 7 := Pedersen.commit params4 g7 h7 ra7 3 rb7 1

example (i : Fin 4) :
    Pedersen.verifyShare params4 g7 h7 pedC i (share params4 ra7 3 i) (share params4 rb7 1 i) :=
  Pedersen.verifyShare_commit params4 g7 h7 ra7 3 rb7 1 i

/- The honest dealing as a `Pedersen.Dealing`; restricting it to the coalition `{0, 2}` keeps the
commitments and each member's `Share`, which verifies through its named `value` and `blinding`. -/
private noncomputable def pedDealing :
    Pedersen.Dealing (ZMod 7) (ZMod 7) (Fin 4) params4.threshold where
  commitments := pedC
  shares i := ⟨share params4 ra7 3 i, share params4 rb7 1 i⟩

example (i : ({0, 2} : Finset (Fin 4))) :
    let d := pedDealing.restrict {0, 2}
    Pedersen.verifyShare params4 g7 h7 d.commitments i.1 (d.shares i).value (d.shares i).blinding :=
  Pedersen.verifyShare_commit params4 g7 h7 ra7 3 rb7 1 i.1

example :
    ¬ Pedersen.verifyShare params4 g7 h7 pedC 1
      (share params4 ra7 3 1 + 1) (share params4 rb7 1 1) := by
  have hv := Pedersen.verifyShare_commit params4 g7 h7 ra7 3 rb7 1 1
  intro hbad
  have heq :
      (share params4 ra7 3 1 + 1) • g7 + share params4 rb7 1 1 • h7 =
        share params4 ra7 3 1 • g7 + share params4 rb7 1 1 • h7 :=
    hbad.trans hv.symm
  have heq' :
      (share params4 ra7 3 1 • g7 + share params4 rb7 1 1 • h7) + (1 : ZMod 7) • g7 =
        (share params4 ra7 3 1 • g7 + share params4 rb7 1 1 • h7) + 0 := by
    rw [add_zero]
    conv_rhs => rw [← heq, add_smul]
    abel
  have h0 : (1 : ZMod 7) • g7 = 0 := add_left_cancel heq'
  exact absurd h0 (by decide)

example :
    Pedersen.coalitionViewDist params4 g7 h7 ({0, 2} : Finset (Fin 4)) 3 =
      Pedersen.coalitionViewDist params4 g7 h7 ({0, 2} : Finset (Fin 4)) 5 :=
  Pedersen.coalitionViewDist_eq params4 ⟨6, by decide, by decide⟩ ({0, 2} : Finset (Fin 4))
    (by decide) 3 5

/- Two inconsistent authorized share sets opening to `3 ≠ 5` against `pedC` yield discrete-log
witness `6` solving `6 • g7 = h7` (`6 * 2 = 5 (mod 7)`).
Shifting the constant terms `a` by `+ 2` and `b` by `+ 2` (`2 • 2 + 2 • 5 = 14 ≡ 0`), while
keeping all non-constant coefficients `ra7, rb7` unchanged, yields `a₂ = 5, b₂ = 3` with
`(share ra7 5 x) • 2 + (share rb7 3 x) • 5 = (share ra7 3 x) • 2 + (share rb7 1 x) • 5`. -/
example :
    let J₁ : Finset (Fin 4) := {0, 1, 2}
    let J₂ : Finset (Fin 4) := {1, 2, 3}
    let σ₁ : J₁ → ZMod 7 := fun j => share params4 ra7 3 j.1
    let τ₁ : J₁ → ZMod 7 := fun j => share params4 rb7 1 j.1
    let σ₂ : J₂ → ZMod 7 := fun j => share params4 ra7 5 j.1
    let τ₂ : J₂ → ZMod 7 := fun j => share params4 rb7 3 j.1
    reconstruct params4 J₁ σ₁ ≠ reconstruct params4 J₂ σ₂ ∧
      Pedersen.extractDLog (reconstruct params4 J₁ σ₁) (reconstruct params4 J₁ τ₁)
        (reconstruct params4 J₂ σ₂) (reconstruct params4 J₂ τ₂) = 6 ∧
      Pedersen.extractDLog (reconstruct params4 J₁ σ₁) (reconstruct params4 J₁ τ₁)
        (reconstruct params4 J₂ σ₂) (reconstruct params4 J₂ τ₂) • g7 = h7 := by
  intro J₁ J₂ σ₁ τ₁ σ₂ τ₂
  have h1 : ∀ j : J₁, Pedersen.verifyShare params4 g7 h7 pedC j.1 (σ₁ j) (τ₁ j) := fun j =>
    Pedersen.verifyShare_commit params4 g7 h7 ra7 3 rb7 1 j.1
  have h2 : ∀ j : J₂, Pedersen.verifyShare params4 g7 h7 pedC j.1 (σ₂ j) (τ₂ j) := by
    intro j
    unfold Pedersen.verifyShare
    dsimp only [pedC]
    rw [Pedersen.evalCommit_commit]
    have hs : σ₂ j = share params4 ra7 3 j.1 + 2 := by
      dsimp only [σ₂]
      rw [show (5 : ZMod 7) = 3 + 2 from rfl, share_add_const]
    have ht : τ₂ j = share params4 rb7 1 j.1 + 2 := by
      dsimp only [τ₂]
      rw [show (3 : ZMod 7) = 1 + 2 from rfl, share_add_const]
    rw [hs, ht, add_smul, add_smul]
    have hzero : (2 : ZMod 7) • g7 + (2 : ZMod 7) • h7 = 0 := by decide
    calc share params4 ra7 3 j.1 • g7 + (2 : ZMod 7) • g7 +
          (share params4 rb7 1 j.1 • h7 + (2 : ZMod 7) • h7)
        = (share params4 ra7 3 j.1 • g7 + share params4 rb7 1 j.1 • h7) +
            ((2 : ZMod 7) • g7 + (2 : ZMod 7) • h7) := by abel
      _ = share params4 ra7 3 j.1 • g7 + share params4 rb7 1 j.1 • h7 := by rw [hzero, add_zero]
  have hr1 : reconstruct params4 J₁ σ₁ = 3 :=
    reconstruct_share_eq_secret params4 ra7 3 (by unfold authorized params4; decide)
  have hr2 : reconstruct params4 J₂ σ₂ = 5 :=
    reconstruct_share_eq_secret params4 ra7 5 (by unfold authorized params4; decide)
  have ht1 : reconstruct params4 J₁ τ₁ = 1 :=
    reconstruct_share_eq_secret params4 rb7 1 (by unfold authorized params4; decide)
  have ht2 : reconstruct params4 J₂ τ₂ = 3 :=
    reconstruct_share_eq_secret params4 rb7 3 (by unfold authorized params4; decide)
  have hne : reconstruct params4 J₁ σ₁ ≠ reconstruct params4 J₂ σ₂ := by
    rw [hr1, hr2]; decide
  have hex := Pedersen.extractDLog_smul_eq_of_reconstruct_ne params4 (by decide : g7 ≠ 0)
    pedC (by unfold authorized params4; decide) (by unfold authorized params4; decide)
    σ₁ τ₁ σ₂ τ₂ h1 h2 hne
  refine ⟨hne, ?_, hex.2⟩
  rw [hr1, hr2, ht1, ht2]
  unfold Pedersen.extractDLog
  rw [show (3 - 1 : ZMod 7)⁻¹ = (4 : ZMod 7) from inv_eq_of_mul_eq_one_right (by decide)]
  decide

/-! ### 3. Boundary check: `g ≠ 0` is necessary for Feldman share uniqueness -/

example :
    Feldman.verifyShare params4 (0 : ZMod 7) (fun _ => 0) 0 2 ∧
    Feldman.verifyShare params4 (0 : ZMod 7) (fun _ => 0) 0 3 ∧
    (2 : ZMod 7) ≠ 3 := by
  decide

end CslibFrontierTests.Crypto.VSS
