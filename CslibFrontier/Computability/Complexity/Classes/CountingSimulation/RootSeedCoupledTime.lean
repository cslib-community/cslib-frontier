/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.CountingSimulation.RootSeedTime
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.RootSeedChoice.Coupled

/-!
# Root packing and an output-bit continuation in square-root-logarithmic overhead

The external request retains both the output bit number and its sign. For a bit of the source
acceptance count, the binary bit index increases the short metadata by at most a logarithmic
amount. Verifying that the chosen seed is balanced before relying on the continuation costs
a constant multiple of the block bound on every branch.
-/

public section

namespace Cslib.Complexity.CountingSimulation

open _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.MultiTapePTM _root_.Turing.MultiTapeATM
open RootSeedChoice RootPackingBalance

private theorem query_size (k q m σ a bit : ℕ) (claim : Bool)
    (s : BalancedSchedules.SeededLabels.Seed (RootPredecessorGraph.vertexCount k q m) (6 * a)) :
    Initialize.shortSize (queryPublic k q m σ a s bit claim) ≤
      Initialize.shortSize (graphPublic k q m σ a s) + 2 * bit.size + 1 := by
  cases claim <;>
    simp only [queryPublic, graphPublic, Initialize.shortSize, RootPredecessorQuery.shortSize,
      RootPredecessorGraph.inputOfIndices, SeededPredecessor.encContext_apply,
      SeededPredecessor.encContextFields, length_encPair, encNat_apply, Nat.size_eq_bits_len,
      Bool.toNat_false, Bool.toNat_true, Nat.size_zero, Nat.size_one] <;> omega

/-- A source output-bit request, before its contraction continuation starts, fits the target
clock uniformly for both possible bit values. -/
theorem query_clock_le_div_sqrt_log (k states C D : ℕ) : ∃ K, ∀ (t σ a bit : ℕ)
    (claim : Bool) (_ha : 64 ^ a ≤ rootEdges k states t) (_hb : bit ≤ 2 * (t + 2)),
    let U := rootVertices k states t
    let q := numBlocks t
    let m := rootCopies k states t
    let p := queryPublic k q m σ a (zeroSeed U a) bit claim
    C * (p.1.raw.length + Initialize.shortSize p ^ D + 1) ≤
      K * (t / (Nat.log 2 (t + 2)).sqrt + 2) := by
  obtain ⟨A, hA⟩ := zero_indices_clock_le_numBlocks k states 1 D
  obtain ⟨B, hB⟩ := exists_size_pow_le_numBlocks D
  let K := C * (A + 8 ^ D * (A + B) + 1)
  refine ⟨K, fun t σ a bit claim ha hb => ?_⟩
  let U := rootVertices k states t
  let q := numBlocks t
  let m := rootCopies k states t
  let s := zeroSeed U a
  let p := queryPublic k q m σ a s bit claim
  let orig := graphPublic k q m σ a s
  let size := Initialize.shortSize orig
  let z := (t + 2).size + 1
  let n := q + 1
  have ho := hA t σ a ha s
  change 1 * (p.1.raw.length + size ^ D + 1) ≤ A * n at ho
  rw [one_mul] at ho
  have hz := hB t
  change z ^ D ≤ B * n at hz
  have hlen := query_size k q m σ a bit claim s
  have hi : bit.size ≤ (t + 2).size + 2 := by
    have hn := (Nat.size_le_size hb).trans (Nat.size_mul_le 2 (t + 2))
    have htwo : (2 : ℕ).size = 2 := by decide
    omega
  have hmain : Initialize.shortSize p ≤ 8 * max size z := by
    change Initialize.shortSize p ≤ size + 2 * bit.size + 1 at hlen
    have := Nat.le_max_left size z
    have := Nat.le_max_right size z
    dsimp only [z] at *
    omega
  have hp := Nat.pow_le_pow_left hmain D
  rw [Nat.mul_pow] at hp
  have hmax : max size z ^ D ≤ (A + B) * n := by
    rw [Nat.add_mul]
    rcases le_total size z with hl | hl
    · rw [max_eq_right hl]
      omega
    · rw [max_eq_left hl]
      omega
  change C * (p.1.raw.length + Initialize.shortSize p ^ D + 1) ≤ _
  calc
    _ ≤ C * (A * n + 8 ^ D * ((A + B) * n) + n) := by
      apply Nat.mul_le_mul_left
      exact Nat.add_le_add (Nat.add_le_add (by omega) (hp.trans (Nat.mul_le_mul_left _ hmax)))
        (Nat.succ_le_succ (Nat.zero_le _))
    _ = K * n := by dsimp only [K]; ring
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.succ_le_succ (numBlocks_le_div_sqrt_log_add_one t))

/-- A single finite ATM checks a seed and hands its indexed bit query to a supplied native
continuation, for positive and negative claims with the continuation's own time added once. -/
theorem exists_rootSeed_coupled_div_sqrt_log (k states : ℕ) {K : ℕ} {R : Type} [Finite R]
    (i j : Fin K) (hij : i ≠ j) (right : MultiTapeATM K Bool R) :
    ∃ (W : ℕ) (Q : Type) (_ : Finite Q) (atm : MultiTapeATM W Bool Q) (C : ℕ),
      ∀ {State : Type} (M : MultiTapePTM k Bool State) (st : State ≃ Fin states)
        (input : List Bool) (t σ a bit : ℕ) (claim : Bool)
        (_ha : 64 ^ a ≤ rootEdges k states t) (_hb : bit ≤ 2 * (t + 2))
        (budget : ℕ) (post : RootBalanceRequest.Public → Prop),
        let U := rootVertices k states t
        let q := numBlocks t
        let m := rootCopies k states t
        let p := queryPublic k q m σ a (zeroSeed U a) bit claim
        let raw := RootBalanceRequest.encPublic p
        (∀ s, let seeded := queryPublic k q m σ a s bit claim
          let cfg := continuationStart i j right raw seeded
          right.HaltsWithin budget cfg ∧ (right.AcceptsWithin budget cfg ↔ post seeded)) →
        let cfg := atm.toPTM.toNTM.initCfg raw
        let time := C * (t / (Nat.log 2 (t + 2)).sqrt + 2) + budget
        atm.HaltsWithin time cfg ∧ (atm.AcceptsWithin time cfg ↔
          ∃ s, PacketPacking.Seeded.Balanced U a (explicitVertexEquiv k q m).toEmbedding
            (RootPredecessorGraph.rowOf M input (blockLength t) σ (letterCode st))
            (RootPredecessorGraph.colOf k q m) s ∧ post (queryPublic k q m σ a s bit claim)) := by
  obtain ⟨W, Q, hQ, atm, C, D, h⟩ := exists_coupled k i j hij right
  obtain ⟨B, hb⟩ := query_clock_le_div_sqrt_log k states C D
  refine ⟨W, Q, hQ, atm, B, ?_⟩
  intro State M st input t σ a bit claim ha hbit budget post
  dsimp only
  intro hright
  obtain ⟨hh, hv⟩ := h M input (blockLength t) σ (letterCode st) a bit claim budget post hright
  have ht := Nat.add_le_add_right (hb t σ a bit claim ha hbit) budget
  exact ⟨hh.mono ht, ⟨fun hx => hv.mp (hx.of_halted_stepCoins hh), fun hx => (hv.mpr hx).mono ht⟩⟩

end Cslib.Complexity.CountingSimulation
