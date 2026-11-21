/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.CountingSimulation.RootSeedCoupledTime
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.RootPackingBalance.InitializeWork

/-!
# Eliminating the balanced-seed assumption for a contraction continuation

The schedule and public query are already present on one work tape, while the original source
input stays on its read-only tape. Under the packing variance inequality there is an accepting
seed choice for each correct bit claim. A contraction continuation needs to be correct only on
balanced seeds. Every seed must still obey its all-branch halting bound.
-/

public section

namespace Cslib.Complexity.CountingSimulation

open _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.MultiTapePTM _root_.Turing.MultiTapeATM
open RootSeedChoice RootPackingBalance

/-- A prepared root call for a fixed source graph and contraction continuation. Every
possible seed is clocked. The claimed bit need only be computed correctly for balanced seeds. -/
@[expose] def RunsRootContraction {W K k states : ℕ} {Q R State : Type}
    (src : Fin W) (atm : MultiTapeATM W Bool Q) (i j : Fin K) (right : MultiTapeATM K Bool R)
    (M : MultiTapePTM k Bool State) (st : State ≃ Fin states)
    (input : List Bool) (t σ a bit : ℕ) (claim : Bool) (budget C : ℕ) : Prop :=
  let q := numBlocks t
  let m := rootCopies k states t
  let U := rootVertices k states t
  let expected := (blockNetworkOf M st (input, t, σ)).2.contraction.testBit bit = claim
  let p := queryPublic k q m σ a (zeroSeed U a) bit claim
  let raw := RootBalanceRequest.encPublic p
  (∀ seed, let word := queryPublic k q m σ a seed bit claim
    let cfg := continuationStart i j right input word
    let balanced := PacketPacking.Seeded.Balanced U a (explicitVertexEquiv k q m).toEmbedding
      (RootPredecessorGraph.rowOf M input (blockLength t) σ (letterCode st))
      (RootPredecessorGraph.colOf k q m) seed
    right.HaltsWithin budget cfg ∧ (balanced → (right.AcceptsWithin budget cfg ↔ expected))) →
  ∀ (pos : ℕ), pos ≤ raw.length →
  let cfg := SharedWordFork.start src atm input raw pos
  let time := C * (t / (Nat.log 2 (t + 2)).sqrt + 2) + budget
  atm.HaltsWithin time cfg ∧ (atm.AcceptsWithin time cfg ↔ expected)

/-- Compose a balance check and a contraction continuation on the actual read-only source input.
The externally queried bit is tested with either claimed value and the setup cost is additive. -/
theorem exists_root_contraction_fork (k states : ℕ) {K : ℕ} {R : Type} [Finite R]
    (i j : Fin K) (hij : i ≠ j) (right : MultiTapeATM K Bool R) :
    ∃ (W : ℕ) (src : Fin W) (Q : Type) (_ : Finite Q) (atm : MultiTapeATM W Bool Q) (C : ℕ),
      ∀ {State : Type} (M : MultiTapePTM k Bool State) (st : State ≃ Fin states)
        (input : List Bool) (t σ a bit : ℕ) (claim : Bool) (budget : ℕ)
        (_hb : bit ≤ 2 * (t + 2))
        (_hsize : 2 * (2 * (3 * k + 1) * rootCopies k states t) * (64 ^ (2 * a)) ^ 2 ≤
          rootEdges k states t),
        RunsRootContraction src atm i j right M st input t σ a bit claim budget C := by
  obtain ⟨H, tape, T, hT, game, B, e, hg⟩ := exists_coupled_game k i j hij right
  obtain ⟨f, hd⟩ := exists_flags_inO
  obtain ⟨W, src, Q, hQ, atm, A, d, hi⟩ := Initialize.exists_prepend_work hd tape game
  obtain ⟨F, D, hFD⟩ := game_clock A d B e
  obtain ⟨C, hC⟩ := query_clock_le_div_sqrt_log k states F D
  refine ⟨W, src, Q, hQ, atm, C, ?_⟩
  intro State M st input t σ a bit claim budget hb hsize
  unfold RunsRootContraction
  dsimp only
  intro hright pos hpos
  let q := numBlocks t
  let m := rootCopies k states t
  let p := queryPublic k q m σ a (zeroSeed _ _) bit claim
  let post := fun p' => right.AcceptsWithin budget (continuationStart i j right input p')
  obtain ⟨hh, hv⟩ := hg M input input (blockLength t) σ (letterCode st) a bit claim budget post
    (fun s => ⟨(hright s).1, Iff.rfl⟩)
  obtain ⟨hh', hv'⟩ := hi input p pos hpos _ hh
  have hc : 0 < m := Nat.mul_pos (by omega) (one_le_blockLength t)
  have ha : 64 ^ a ≤ rootEdges k states t := by
    have hm : 0 < 2 * (2 * (3 * k + 1) * m) := by positivity
    have hg : 64 ^ a ≤ 64 ^ (2 * a) := Nat.pow_le_pow_right (by decide) (by omega)
    have hs : 64 ^ (2 * a) ≤ (64 ^ (2 * a)) ^ 2 := by
      simpa only [pow_one] using Nat.pow_le_pow_right (n := 64 ^ (2 * a))
        (Nat.pow_pos (by decide : 0 < 64)) (by decide : 1 ≤ 2)
    exact hg.trans (hs.trans ((Nat.le_mul_of_pos_left _ hm).trans hsize))
  have hbound := (hFD p).trans (hC t σ a bit claim ha hb)
  let part (c exp : ℕ) := c * (p.1.raw.length + Initialize.shortSize p ^ exp + 1)
  have hclock : part A d + (part B e + budget) ≤
      C * (t / (Nat.log 2 (t + 2)).sqrt + 2) + budget := by
    change part A d + (part B e + 2 * (flags p).length + 1) ≤ _ at hbound
    omega
  refine ⟨hh'.mono hclock, ⟨?_, ?_⟩⟩
  · intro acc
    obtain ⟨s, hs, hv⟩ := hv.mp (hv'.mp (acc.of_halted_stepCoins hh'))
    exact ((hright s).2 hs).mp hv
  · intro claim_ok
    obtain ⟨s, hs⟩ := RootPredecessorGraph.exists_balanced_seed M input (blockLength t) σ
      (letterCode st) a hc hsize
    exact (hv'.mpr (hv.mpr ⟨s, hs, ((hright s).2 hs).mpr claim_ok⟩)).mono hclock

end Cslib.Complexity.CountingSimulation
