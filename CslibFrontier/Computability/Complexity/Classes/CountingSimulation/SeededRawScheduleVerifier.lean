/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.CountingSimulation.OuterRootLeafChild
public import CslibFrontier.Computability.Complexity.Classes.CountingSimulation.OuterRootLeafClock
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.OuterRootLeafRunner

/-!
# Native outer counting with a shared seeded contraction continuation

A single fixed alternating machine verifies padded accepting-count bits from the prepared
carry-save root. Every branch retains the source input. Its only remaining contraction
hypothesis concerns the continuation on seeded root queries.
-/

public section

namespace Cslib.Complexity.CountingSimulation

open _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.MultiTapePTM _root_.Turing.MultiTapeATM
open Cslib.BitString Circuits.Boolean.CarrySaveQuery
open OuterRootLeaf OuterRootLeafRequest

/-- A physical leaf family checks contraction bits at every legal outer clock and on the full
controller domain, including malformed movements, the carry component and padded index words. -/
theorem exists_seeded_contraction_leaf (k states : ℕ) {K : ℕ} {R : Type} [Finite R]
    (i j : Fin K) (hij : i ≠ j) (right : MultiTapeATM K Bool R) :
    ∃ (a : ℕ) (Q : Type) (_ : Finite Q) (leaf : Bool → Bool → MultiTapeATM (a + 12) Bool Q)
      (C t₀ : ℕ), ∀ {State : Type} (M : MultiTapePTM k Bool State) (st : State ≃ Fin states)
        (input : List Bool) {t : ℕ}, t₀ ≤ t → ∀ budget,
        ChecksSeededContractions i j right M st input t budget →
        let n := 2 ^ (2 * (k + 1) * numBlocks t)
        let w := paddedTime t + 1
        let time := C * (t / (Nat.log 2 (t + 2)).sqrt + 2) + budget
        let size := CarrySaveCountingRoot.sizeBudget n w
        let scratch := CarrySaveLeaf.scratch a (RootBalanceRequest.encPublic
          (outerRootTemplate k states t)) (encNat n) (encNat w)
        CarrySaveStream.LeafBound leaf time size input scratch ∧
          CarrySaveStream.LeafCorrect (RawScheduleSum.contractionLeaf M st input t)
            leaf time size input scratch := by
  obtain ⟨W, src, S, hS, root, B, t₀, hr⟩ :=
    exists_scheduled_root_contraction_fork k states i j hij right
  obtain ⟨a, Q, hQ, leaf, A, d, hleaf⟩ := OuterRootLeafRunner.exists_runner k src root
  obtain ⟨F, hF⟩ := exists_setup_clock k states d
  let C := A * (F + 1) + B
  refine ⟨a, Q, hQ, leaf, C, max 2 t₀, ?_⟩
  intro State M st input t ht budget hseed n w time size scratch
  have hr₀ := hr M st input t ((Nat.le_max_right _ _).trans ht)
  have hd := Nat.succ_le_succ (numBlocks_le_div_sqrt_log_add_one t)
  let rootTime := B * (t / (Nat.log 2 (t + 2)).sqrt + 2) + budget
  have hs (height bits path unary : List Bool) (frontier : ℤ) (status carry claim : Bool)
      (hlen : height.length + bits.length + path.length ≤ size) :
      let cfg := (CarrySaveStream.config (scratch := scratch) (input := input)
        height bits path unary frontier status).withState (some (leaf carry claim).toPTM.initial)
      (leaf carry claim).HaltsWithin time cfg ∧ (lsbValue bits < w →
        ((leaf carry claim).AcceptsWithin time cfg ↔
          value (RawScheduleSum.contractionLeaf M st input t) ⟨path, 0, carry, lsbValue bits⟩ =
            claim)) := by
    intro cfg
    let x := source k states t path carry bits
    have child := child_spec src root i j right M st input t budget B
      (fun s b c => hr₀ s b c budget) hseed path bits carry claim
    obtain ⟨hh, ha⟩ := hleaf input x height unary frontier status claim rootTime
      (fun hg => (child hg).1)
    have hf := hF ((Nat.le_max_left _ _).trans ht) path bits carry
      (show bits.length + path.length ≤ size by omega)
    let z := path.length + 2 * (encInput x).length + 9 + longSize x + shortSize x ^ d
    change z ≤ F * (numBlocks t + 1) at hf
    have hz : z + 1 ≤ (F + 1) * (t / (Nat.log 2 (t + 2)).sqrt + 2) := by
      rw [Nat.add_mul, Nat.one_mul]
      have hm : F * (numBlocks t + 1) ≤ F * (t / (Nat.log 2 (t + 2)).sqrt + 2) :=
        Nat.mul_le_mul_left _ hd
      omega
    have hclock : A * (z + 1) + rootTime ≤ time := by
      dsimp only [time, C, rootTime]
      rw [Nat.add_mul, Nat.mul_assoc]
      have := Nat.mul_le_mul_left A hz
      omega
    refine ⟨hh.mono hclock, fun hb => ?_⟩
    have bridge : (leaf carry claim).AcceptsWithin time cfg ↔
        (leaf carry claim).AcceptsWithin (A * (z + 1) + rootTime) cfg :=
      ⟨fun h => h.of_halted_stepCoins hh, fun h => h.mono hclock⟩
    refine bridge.trans (ha.trans ?_)
    cases hg : active (data k x) with
    | false =>
      rw [value_inactive M st input t path bits carry hb hg]
      cases claim <;> simp
    | true => exact (child hg).2 hb
  exact ⟨fun h b p u f s c v _ hl => (hs h b p u f s c v hl).1,
    fun h b p u f s c v _ hl hb => (hs h b p u f s c v hl).2 hb⟩

/-- From the protected outer root a single native ATM verifies either sign of each padded
accepting-count bit. The seeded contraction time appears once in the all-branch bound. -/
theorem exists_seeded_count_verifier (k states : ℕ) {K : ℕ} {R : Type} [Finite R]
    (i j : Fin K) (hij : i ≠ j) (right : MultiTapeATM K Bool R) :
    ∃ (a r q : ℕ) (Q : Type) (_ : Finite Q)
      (atm : MultiTapeATM (CarryLookaheadCountingLayout.size a r q) Bool Q) (C t₀ : ℕ),
      ∀ {State : Type} [Finite State] (M : MultiTapePTM k Bool State) (st : State ≃ Fin states)
        (input : List Bool) {t : ℕ}, t₀ ≤ t → ∀ budget,
        ChecksSeededContractions i j right M st input t budget →
        ∀ (bit : Fin (paddedTime t + 1)) (claim : Bool),
        let context := RootBalanceRequest.encPublic (outerRootTemplate k states t)
        let cfg := CarryLookaheadCounting.initial a r q input context
          (2 ^ (2 * (k + 1) * numBlocks t)) (paddedTime t + 1) bit.val claim
        let start := cfg.withState (some atm.toPTM.initial)
        let time := C * (t / (Nat.log 2 (t + 2)).sqrt + 2) + budget
        atm.HaltsWithin time start ∧ (atm.AcceptsWithin time start ↔
          (M.acceptCount input (paddedTime t)).testBit bit.val = claim) := by
  obtain ⟨a, S, hS, leaf, A, t₀, hl⟩ := exists_seeded_contraction_leaf k states i j hij right
  obtain ⟨r, q, Q, hQ, atm, B, hv⟩ :=
    RawScheduleSum.exists_count_verifier_of_contraction_leaf (k := k) leaf
  refine ⟨a, r, q, Q, hQ, atm, B + A, max 2 t₀, ?_⟩
  intro State _ M st input t ht budget hs bit claim ctx cfg start time
  obtain ⟨hh, ha⟩ := hl M st input ((Nat.le_max_right _ _).trans ht) budget hs
  obtain ⟨hhalt, hacc⟩ := hv M st input ctx ((Nat.le_max_left _ _).trans ht) _ hh ha bit claim
  have hc : B * (numBlocks t + 1) + (A * (t / (Nat.log 2 (t + 2)).sqrt + 2) + budget) ≤
      time := by
    dsimp only [time]
    rw [Nat.add_mul]
    have hm : B * (numBlocks t + 1) ≤ B * (t / (Nat.log 2 (t + 2)).sqrt + 2) :=
      Nat.mul_le_mul_left _ (Nat.succ_le_succ (numBlocks_le_div_sqrt_log_add_one t))
    omega
  exact ⟨hhalt.mono hc, ⟨fun h => hacc.mp (h.of_halted_stepCoins hhalt),
    fun h => (hacc.mpr h).mono hc⟩⟩

end Cslib.Complexity.CountingSimulation
