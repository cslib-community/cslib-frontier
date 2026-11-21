/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.RootSeedChoice.Game

/-!
# A claimed output bit and a shared seed on the root request

The two public index fields retain the requested bit number and claim. The rank terminal
overwrites both when selecting a challenged edge and candidate. The contraction continuation
receives the original bit number and claim with the chosen coefficients installed.
-/

public section

namespace Turing.MultiTapeATM.RootSeedChoice

open Cslib MultiTapeTM MultiTapePTM QuantifiedWord RootPackingBalance
open RootBalanceRequest (Public)
open RootPredecessorGraph (vertexCount edgeCount inputOfIndices)

/-- The query asks whether the numbered output bit equals the supplied claim. -/
@[expose] def queryPublic (k q copies σ a : ℕ)
    (seed : BalancedSchedules.SeededLabels.Seed (vertexCount k q copies) (6 * a))
    (bit : ℕ) (claim : Bool) : Public :=
  (inputOfIndices k q copies σ a seed bit claim.toNat, edgeCount k q copies)

/-- The coefficient decoder preserves the output query on every branch, even for short words. -/
theorem exists_installed_query (k q copies σ a bit : ℕ) (claim : Bool) (choices : List Bool) :
    let U := vertexCount k q copies
    let p := queryPublic k q copies σ a (zeroSeed U a) bit claim
    ∃ seed, (RootSeedInstall.install (p, choices)).1 =
      queryPublic k q copies σ a seed bit claim := by
  let p := queryPublic k q copies σ a (zeroSeed _ _) bit claim
  let c := (SeedChoice.install (p.1.context, choices)).1
  obtain ⟨h₀, h₁, h₂, h₃⟩ := SeedChoice.install_coefficients_lt p.1.context choices
  let c₀ : Fin (2 ^ SeedChoice.width p.1.context) := ⟨c.c0, h₀⟩
  let c₁ : Fin (2 ^ SeedChoice.width p.1.context) := ⟨c.c1, h₁⟩
  let c₂ : Fin (2 ^ SeedChoice.width p.1.context) := ⟨c.c2, h₂⟩
  let c₃ : Fin (2 ^ SeedChoice.width p.1.context) := ⟨c.c3, h₃⟩
  exact ⟨![c₀, c₁, c₂, c₃], rfl⟩

private theorem plays_and_const (v : List Bool → Prop) (C : Prop) (pre rest : List Bool) :
    plays (fun w => v w ∧ C) pre rest ↔ plays v pre rest ∧ C := by
  induction rest generalizing pre with
  | nil => rfl
  | cons b bs ih =>
    cases b <;> simp only [plays, Bool.false_eq_true, ↓reduceIte, ih]
    · exact exists_and_right
    · constructor
      · exact fun h => ⟨fun x => (h x).1, (h false).2⟩
      · exact fun h x => ⟨h.1 x, h.2⟩

/-- The later universal fork tests the exact same seed for balance and for the claimed bit.
This holds for either sign and any requested bit number. -/
theorem plays_iff_balanced_and {k q copies : ℕ} {S : Type} (M : MultiTapePTM k Bool S)
    (input : List Bool) (b σ : ℕ) (code : BlockLetter k S b → Fin copies → Bool)
    (a bit : ℕ) (claim : Bool) (post : Public → Prop) :
    let U := vertexCount k q copies
    let p := queryPublic k q copies σ a (zeroSeed U a) bit claim
    plays (fun choices =>
      let x := RootSeedInstall.install (p, choices)
      terminalValue k x ∧ post x.1) [] (flags p) ↔
      ∃ seed, PacketPacking.Seeded.Balanced U a (explicitVertexEquiv k q copies).toEmbedding
        (RootPredecessorGraph.rowOf M input b σ code) (RootPredecessorGraph.colOf k q copies) seed ∧
          post (queryPublic k q copies σ a seed bit claim) := by
  let p := queryPublic k q copies σ a (zeroSeed _ _) bit claim
  let rest := rankFlags (Nat.clog 2 p.2)
  let v := fun choices => let x := RootSeedInstall.install (p, choices)
                          terminalValue k x ∧ post x.1
  change plays v [] (seedFlags (vertexCount k q copies) a ++ rest) ↔ _
  rw [plays_seedFlags]
  apply exists_congr
  intro seed
  let w := SeedChoice.word seed
  let seeded := queryPublic k q copies σ a seed bit claim
  have hw (tail : List Bool) : RootSeedInstall.install (p, w ++ tail) = (seeded, tail) :=
    RootSeedInstall.install_word p seed tail
  have h := plays_append_prefix v w [] rest
  simp only [List.append_nil, List.nil_append] at h ⊢
  exact h.trans (by
    simp only [v, hw, plays_and_const]
    exact and_congr_left' (plays_iff_balanced M input b σ code a seed))

end Turing.MultiTapeATM.RootSeedChoice
