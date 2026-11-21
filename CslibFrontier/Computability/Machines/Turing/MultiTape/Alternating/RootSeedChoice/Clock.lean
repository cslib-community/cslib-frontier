/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.RootSeedChoice.Game
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Envelope

/-!
# Uniform clock for the branch that guesses and verifies a root seed

Decoding the coefficient fields and preparing both count inputs take linear time on the raw root
schedule plus polynomial time on the metadata. This bound remains uniform over every legal play
because all four coefficient fields are sized from short public parameters.
-/

public section

namespace Turing.MultiTapeATM.RootSeedChoice

open Cslib MultiTapeTM RootBalanceRequest RootPackingBalance

/-- The terminal clock for reading all choices, installing the seed, and running a rank query. -/
@[expose] def terminalTime (c d A D : ℕ) (x : Input) : ℕ :=
  let y := RootSeedInstall.install x
  let p := (prepare y).2
  (encInput x).length + c * ((rootQuery x).raw.length + shortSize x ^ d + 1) + 8 +
    A * ((selected y).raw.length +
      (RootPredecessorQuery.shortSize (selected y) + p.count.size + p.query.width.size + 1) ^ D + 1)

private theorem terminal_bound (c d A D : ℕ) : ∃ B e, ∀ x : Input,
    terminalTime c d A D x ≤ B * ((rootQuery x).raw.length + shortSize x ^ e + 1) := by
  let paramsSize (x : Input) := RootPredecessorQuery.shortSize (selected x) +
    (prepare x).2.count.size + (prepare x).2.query.width.size + 1
  have hm : PolyBounded shortSize paramsSize := by
    apply PolyBounded.of_forall_le 4 1
    intro x
    have h := shortSize_selected_le x
    have hp := parameter_sizes x
    simp only [paramsSize, shortSize, pow_one]
    omega
  let small (x : Input) := 8 * (shortSize x + 2) + c * (shortSize x ^ d + 1) + 8 +
    A * (paramsSize (RootSeedInstall.install x) ^ D + 1)
  have hs : PolyBounded shortSize small := by
    apply PolyBounded.add
    · apply PolyBounded.add _ (.const 8)
      exact ((PolyBounded.const 8).mul (PolyBounded.self.add (.const 2))).add
        ((PolyBounded.const c).mul ((PolyBounded.self.pow d).add (.const 1)))
    · exact (PolyBounded.const A).mul
        (((hm.comp RootSeedInstall.install_size).pow D).add (.const 1))
  obtain ⟨B, e, h⟩ := hs.exists_le_linear_add_pow (fun x => (rootQuery x).raw.length) (8 + c + A)
    (fun x => by simp [shortSize])
  refine ⟨B, e, fun x => le_trans ?_ (h x)⟩
  have hr : (selected (RootSeedInstall.install x)).raw = (rootQuery x).raw := rfl
  simp only [terminalTime, hr]
  dsimp only [small, paramsSize]
  have hlen := length_encInput_le x
  rw [Nat.add_mul, Nat.add_mul]
  simp only [Nat.mul_add, Nat.mul_one]
  omega

/-- One bound covers all completed plays, independent of the chosen seed and challenges. -/
theorem terminal_clock (c d A D : ℕ) : ∃ C E, ∀ (p : Public) (word : List Bool),
    word.length = (flags p).length →
      terminalTime c d A D (p, word) ≤ C * (p.1.raw.length + Initialize.shortSize p ^ E + 1) := by
  obtain ⟨B, e, hb⟩ := terminal_bound c d A D
  have hp := (PolyBounded.const B).mul (((PolyBounded.self.add flags_size).pow e).add (.const 1))
  obtain ⟨C, E, h⟩ := hp.exists_le_linear_add_pow (fun p => p.1.raw.length) B
    (fun p => by simp [Initialize.shortSize])
  refine ⟨C, E, fun p word hw => (hb (p, word)).trans (le_trans ?_ (h p))⟩
  have hz : shortSize (p, word) = Initialize.shortSize p + (flags p).length := by
    dsimp [shortSize, Initialize.shortSize, rootQuery, edgeCount]
    omega
  rw [hz, ← Nat.mul_add]
  apply Nat.mul_le_mul_left
  simp only [Nat.add_assoc, le_refl]

/-- Combine the physical initializer, all player moves, and the terminal clock. -/
theorem game_clock (A d B e : ℕ) : ∃ C E, ∀ p : Public,
    A * (p.1.raw.length + Initialize.shortSize p ^ d + 1) +
        (B * (p.1.raw.length + Initialize.shortSize p ^ e + 1) + 2 * (flags p).length + 1) ≤
      C * (p.1.raw.length + Initialize.shortSize p ^ E + 1) := by
  have hp := (((PolyBounded.const A).mul ((PolyBounded.self.pow d).add (.const 1))).add
    ((PolyBounded.const B).mul ((PolyBounded.self.pow e).add (.const 1)))).add
      (((PolyBounded.const 2).mul flags_size).add (.const 1))
  obtain ⟨C, E, h⟩ := hp.exists_le_linear_add_pow (fun p => p.1.raw.length) (A + B)
    (fun p => by simp [Initialize.shortSize])
  refine ⟨C, E, fun p => le_trans ?_ (h p)⟩
  rw [Nat.add_mul]
  simp only [Nat.mul_add, Nat.mul_one]
  omega

end Turing.MultiTapeATM.RootSeedChoice
