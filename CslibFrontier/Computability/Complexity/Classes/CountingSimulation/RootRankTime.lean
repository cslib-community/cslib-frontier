/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.CountingSimulation.BlockNetworks
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.RootRankInput
import CslibFrontier.Foundations.Data.Nat.BinarySize

/-!
# Root packing rank at the source clock

Use the same logarithmic blocks and Boolean letter code as the count-preserving block-network
reduction. A schedule has one row per block. All four seed coefficients, both half-edge
indices, the universe and the count precision have logarithmic encoded length. Thus the
external-input rank machine runs in time linear in the number of blocks, uniformly over
the source clock, represented schedule, seed and genuine bit claim.
-/

public section

namespace Cslib.Complexity.CountingSimulation

open _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.MultiTapePTM _root_.Turing.MultiTapeATM
open RootPredecessorGraph (graphInput edgeCount vertexCount)
open Cslib.Circuits.Boolean.CarryLookahead.Query

private theorem pow_succ_le_const_pow (d n : ℕ) :
    (n + 1) ^ d ≤ (d + 1) ^ d * 2 ^ n := by
  let q := n / (d + 1)
  have hq := Nat.div_add_mod n (d + 1)
  have hr : n % (d + 1) < d + 1 := Nat.mod_lt _ (by omega)
  have h : n + 1 ≤ (d + 1) * (q + 1) := by
    dsimp [q]
    rw [Nat.mul_add, Nat.mul_one]
    omega
  calc
    _ ≤ ((d + 1) * (q + 1)) ^ d := Nat.pow_le_pow_left h _
    _ ≤ ((d + 1) * 2 ^ q) ^ d :=
      Nat.pow_le_pow_left (Nat.mul_le_mul_left _ (Nat.lt_two_pow_self (n := q))) d
    _ = (d + 1) ^ d * 2 ^ (q * d) := by rw [Nat.mul_pow, Nat.pow_mul]
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right two_pos (by
      have hb := Nat.mul_div_le n (d + 1)
      dsimp [q]
      nlinarith [Nat.mul_succ (n / (d + 1)) d]))

private theorem blockLength_le_size (t : ℕ) : blockLength t ≤ (t + 2).size :=
  Nat.clog_le_of_le_pow (Nat.lt_size_self _).le

/-- Any fixed power of the binary clock length fits in a constant times the number of blocks.
This allows arbitrary fixed degrees in the short arithmetic of a native endpoint or rank query. -/
theorem exists_size_pow_le_numBlocks (d : ℕ) :
    ∃ c, ∀ t, ((t + 2).size + 1) ^ d ≤ c * (numBlocks t + 1) := by
  refine ⟨4 * (d + 2) ^ (d + 1), fun t => ?_⟩
  let z := (t + 2).size
  have hz : 0 < z := Nat.size_pos.mpr (by omega)
  have hpred : 2 ^ (z - 1) ≤ t + 2 := Nat.lt_size.mp (by change z - 1 < z; omega)
  have hpow : 2 ^ z ≤ 2 * (t + 2) := by
    rw [← Nat.sub_add_cancel (show 1 ≤ z by omega), Nat.pow_succ]
    omega
  have hp := pow_succ_le_const_pow (d + 1) z
  have ht : t ≤ numBlocks t * (z + 1) :=
    (le_paddedTime t).trans (Nat.mul_le_mul_left _ (by have := blockLength_le_size t; omega))
  refine Nat.le_of_mul_le_mul_right (c := z + 1) ?_ (by omega)
  calc
    _ = (z + 1) ^ (d + 1) := (Nat.pow_succ _ _).symm
    _ ≤ (d + 2) ^ (d + 1) * (2 * (t + 2)) := hp.trans (Nat.mul_le_mul_left _ hpow)
    _ ≤ (d + 2) ^ (d + 1) * (4 * ((numBlocks t + 1) * (z + 1))) := by
      apply Nat.mul_le_mul_left
      nlinarith
    _ = _ := by ring

/-- The standard block count also meets the requested square-root-logarithmic scale. -/
theorem numBlocks_le_div_sqrt_log_add_one (t : ℕ) :
    numBlocks t ≤ t / (Nat.log 2 (t + 2)).sqrt + 1 := by
  let b := blockLength t
  have hb : 0 < b := one_le_blockLength t
  have hs : 0 < (Nat.log 2 (t + 2)).sqrt := by
    have hl := Nat.log_pos one_lt_two (show 2 ≤ t + 2 by omega)
    exact Nat.sqrt_pos.mpr hl
  have hd : (Nat.log 2 (t + 2)).sqrt ≤ b :=
    (Nat.sqrt_le_self _).trans (Nat.log_le_clog _ _)
  have hc : numBlocks t ≤ t / b + 1 := by
    apply (Nat.ceilDiv_le_iff hb).mpr
    have hr := Nat.mod_lt t hb
    have he := Nat.div_add_mod t b
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (t / b)]
    omega
  exact hc.trans (Nat.succ_le_succ (Nat.div_le_div_left hd hs))

/-- Uniform encoded size of the actual rank query after choosing the graph's four seed
coefficients. The bound holds for every genuine edge and all seeds of the specified type. -/
private theorem graph_size (k q m σ a w : ℕ)
    (seed : BalancedSchedules.SeededLabels.Seed (vertexCount k q m) (6 * a))
    (e : Fin (edgeCount k q m)) :
    RootPredecessorQuery.shortSize (graphInput k q m σ a seed e e) +
        (edgeCount k q m).size + w.size + 1 ≤
      200 * ((2 * (k + 1)).size + q.size + m.size + (vertexCount k q m).size +
        (edgeCount k q m).size + a + w.size + 1) := by
  let U := vertexCount k q m
  have ht : Nat.clog 2 (max U 2) ≤ U.size + 2 := by
    have h := Nat.clog_le_of_le_pow (Nat.lt_size_self (max U 2)).le
    rcases le_total U 2 with hU | hU
    · rw [max_eq_right hU]
      have : Nat.clog 2 2 = 1 := by decide
      omega
    · rw [max_eq_left hU] at h ⊢
      omega
  have hs (i : Fin 4) : (seed i).val.size ≤ 3 * (U.size + 6 * a + 3) := by
    have hv : (seed i).val.size ≤ Probability.trinomialDeg U (6 * a) :=
      Nat.size_le.mpr (seed i).isLt
    have hd := Probability.trinomialDeg_le_three_mul U (6 * a)
    omega
  have h₀ := hs 0
  have h₁ := hs 1
  have h₂ := hs 2
  have h₃ := hs 3
  have he := Nat.size_le_size e.isLt.le
  have hr := Nat.size_mul_le (2 * (k + 1)) q
  simp only [RootPredecessorQuery.shortSize, graphInput, RootPredecessorGraph.inputOfIndices,
    ScheduleBits.length_rows, List.length_ofFn, SeededPredecessor.encContext_apply,
    SeededPredecessor.encContextFields, length_encPair, encNat_apply, Nat.size_eq_bits_len,
    encUnary_apply, List.length_replicate]
  dsimp only [U] at h₀ h₁ h₂ h₃
  omega

/-- Number of Boolean copies in the selected block-network reduction. -/
abbrev rootCopies (k states t : ℕ) := letterBits k states (blockLength t)

/-- Number of half-edges in the selected root graph. -/
abbrev rootEdges (k states t : ℕ) := edgeCount k (numBlocks t) (rootCopies k states t)

/-- Size of the tagged vertex universe of the selected root graph. -/
abbrev rootVertices (k states t : ℕ) := vertexCount k (numBlocks t) (rootCopies k states t)

/-- The root rank query's entire arithmetic record has logarithmic size in the source clock.
The label hypothesis is the packing restriction on the number of radix-64 words. -/
private theorem selected_size (k states : ℕ) :
    ∃ A, ∀ (t σ a : ℕ)
      (seed : BalancedSchedules.SeededLabels.Seed (rootVertices k states t) (6 * a))
        (e : Fin (rootEdges k states t)), 64 ^ a ≤ rootEdges k states t →
      let arg := graphInput k (numBlocks t) (rootCopies k states t) σ a seed e e
      RootPredecessorQuery.shortSize arg + (rootEdges k states t).size +
          (Nat.clog 2 (rootEdges k states t + 1)).size + 1 ≤ A * ((t + 2).size + 1) := by
  let F := (2 * (k + 1)).size + (states + k + 4).size + (3 * k + 1).size + (3 * k + 2).size + 10
  refine ⟨3000 * (F + 1), ?_⟩
  intro t σ a seed e ha
  dsimp only
  let q := numBlocks t
  let m := rootCopies k states t
  let n := rootEdges k states t
  let U := rootVertices k states t
  let z := (t + 2).size
  have hq : q ≤ t := (Nat.ceilDiv_le_iff (one_le_blockLength t)).mpr
    (Nat.le_mul_of_pos_right _ (one_le_blockLength t))
  have hqs : q.size ≤ z := Nat.size_le_size (by omega)
  have hms : m.size ≤ (states + k + 4).size + z :=
    (Nat.size_mul_le _ _).trans (Nat.add_le_add_left
      ((Nat.size_le_self _).trans (blockLength_le_size t)) _)
  have nh₁ := Nat.size_mul_le q (3 * k + 1)
  have nh₂ := Nat.size_mul_le (q * (3 * k + 1)) m
  have nh₃ := Nat.size_mul_le 2 (q * (3 * k + 1) * m)
  have htwo : (2 : ℕ).size = 2 := by decide
  have hns : n.size ≤ 2 * z + F := by
    change (2 * (q * (3 * k + 1) * m)).size ≤ _
    dsimp only [F]
    omega
  have uh₁ := Nat.size_mul_le q (3 * k + 2)
  have uh₂ := Nat.size_add_le (q * (3 * k + 2)) (q * (3 * k + 1) * m)
  have hus : U.size ≤ 3 * z + F := by
    change (q * (3 * k + 2) + q * (3 * k + 1) * m).size ≤ _
    dsimp only [F]
    omega
  have has : a < n.size := Nat.lt_size.mpr ((Nat.pow_le_pow_left (by decide : 2 ≤ 64) a).trans ha)
  have hw : (Nat.clog 2 (n + 1)).size ≤ n.size :=
    (Nat.size_le_self _).trans (Nat.clog_le_of_le_pow (Nat.lt_size_self n))
  have hg := graph_size k q m σ a (Nat.clog 2 (n + 1)) seed e
  apply hg.trans
  change 200 * ((2 * (k + 1)).size + q.size + m.size + U.size + n.size +
    a + (Nat.clog 2 (n + 1)).size + 1) ≤ 3000 * (F + 1) * (z + 1)
  have hf : (2 * (k + 1)).size + (states + k + 4).size ≤ F := by dsimp [F]; omega
  rw [show 3000 * (F + 1) * (z + 1) = 3000 * (F * z) + 3000 * F + 3000 * z + 3000 by ring]
  omega

/-- With both indices initialized to zero, the context and edge-count fields fit the same
short arithmetic budget. This form applies before an edge is chosen by a balance verifier. -/
theorem zero_indices_clock_le_numBlocks (k states C D : ℕ) :
    ∃ K, ∀ (t σ a : ℕ) (_ha : 64 ^ a ≤ rootEdges k states t)
      (seed : BalancedSchedules.SeededLabels.Seed (rootVertices k states t) (6 * a)),
      let n := rootEdges k states t
      let arg := RootPredecessorGraph.inputOfIndices k (numBlocks t) (rootCopies k states t)
        σ a seed 0 0
      C * (arg.raw.length + (RootPredecessorQuery.shortSize arg + n.size + 1) ^ D + 1) ≤
        K * (numBlocks t + 1) := by
  obtain ⟨A, hA⟩ := selected_size k states
  obtain ⟨B, hB⟩ := exists_size_pow_le_numBlocks D
  refine ⟨C * (2 * (k + 1) + A ^ D * B + 1), ?_⟩
  intro t σ a ha seed
  let n := rootEdges k states t
  let e : Fin n := ⟨0, (Nat.pow_pos (by decide : 0 < 64)).trans_le ha⟩
  let arg := graphInput k (numBlocks t) (rootCopies k states t) σ a seed e e
  have hm := hA t σ a seed e ha
  have hsmall : RootPredecessorQuery.shortSize arg + n.size + 1 ≤ A * ((t + 2).size + 1) := by
    exact (by omega : RootPredecessorQuery.shortSize arg + n.size + 1 ≤
      RootPredecessorQuery.shortSize arg + n.size + (Nat.clog 2 (n + 1)).size + 1).trans hm
  have hp := Nat.pow_le_pow_left hsmall D
  rw [Nat.mul_pow] at hp
  have hs := hp.trans (Nat.mul_le_mul_left _ (hB t))
  change C * (arg.raw.length + (RootPredecessorQuery.shortSize arg + n.size + 1) ^ D + 1) ≤ _
  have hl : arg.raw.length = 2 * (k + 1) * numBlocks t := by
    simp [arg, graphInput, RootPredecessorGraph.inputOfIndices]
  rw [hl, Nat.mul_assoc C]
  apply Nat.mul_le_mul_left
  nlinarith

/-- With the source reduction's standard logarithmic blocks and Boolean letter code, each
root packing-rank bit is decidable from its encoded request by a single finite alternating
machine in time proportional to the number of blocks. -/
theorem exists_rootRank_evaluator_numBlocks (k states : ℕ) :
    ∃ (tapes : ℕ) (Q : Type) (_ : Finite Q) (atm : MultiTapeATM tapes Bool Q) (K : ℕ),
      ∀ {State : Type} (M : MultiTapePTM k Bool State) (st : State ≃ Fin states)
        (input : List Bool) (t σ a : ℕ) (_ha : 64 ^ a ≤ rootEdges k states t)
        (seed : BalancedSchedules.SeededLabels.Seed (rootVertices k states t) (6 * a))
        (e : Fin (rootEdges k states t)) (bit : Fin (Nat.clog 2 (rootEdges k states t + 1)))
        (claim : Bool),
        let q := numBlocks t
        let m := rootCopies k states t
        let arg := graphInput k q m σ a seed e e
        let n := rootEdges k states t
        let params : CountingInput.Input := ⟨n, ⟨Nat.clog 2 (n + 1), bit.val, claim⟩⟩
        let start := atm.toPTM.toNTM.initCfg
          (CarryLookaheadCountingPair.encInput (RootPredecessorContext.word arg, params))
        let time := K * (numBlocks t + 1)
        atm.HaltsWithin time start ∧ (atm.AcceptsWithin time start ↔
          (PacketPacking.Seeded.rank (rootVertices k states t) a
            (explicitVertexEquiv k q m).toEmbedding
            (RootPredecessorGraph.rowOf M input (blockLength t) σ (letterCode st))
            (RootPredecessorGraph.colOf k q m) seed e).testBit bit.val = claim) := by
  obtain ⟨u, Q, hQ, atm, C, D, h⟩ := RootRankInput.exists_classRank_evaluator k
  obtain ⟨A, hA⟩ := selected_size k states
  obtain ⟨B, hB⟩ := exists_size_pow_le_numBlocks D
  refine ⟨u, Q, hQ, atm, C * (2 * (k + 1) + A ^ D * B + 1), ?_⟩
  intro State M st input t σ a ha seed e bit claim
  let arg := graphInput k (numBlocks t) (rootCopies k states t) σ a seed e e
  let n := rootEdges k states t
  let w := Nat.clog 2 (n + 1)
  obtain ⟨hh, hv⟩ := h M input (blockLength t) σ (letterCode st) seed e w bit claim
  have hl : arg.raw.length = 2 * (k + 1) * numBlocks t := by
    simp [arg, graphInput, RootPredecessorGraph.inputOfIndices]
  have hp := Nat.pow_le_pow_left (hA t σ a seed e ha) D
  rw [Nat.mul_pow] at hp
  have hs : (RootPredecessorQuery.shortSize arg + n.size + w.size + 1) ^ D ≤
      A ^ D * B * (numBlocks t + 1) := hp.trans (by
    rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ (hB t))
  have ht : C * (arg.raw.length +
      (RootPredecessorQuery.shortSize arg + n.size + w.size + 1) ^ D + 1)
      ≤ C * (2 * (k + 1) + A ^ D * B + 1) * (numBlocks t + 1) := by
    rw [hl, Nat.mul_assoc C]
    apply Nat.mul_le_mul_left
    nlinarith
  refine ⟨hh.mono ht, ?_⟩
  exact ⟨fun hacc => hv.mp (hacc.of_halted_stepCoins hh), fun hb => (hv.mpr hb).mono ht⟩

end Cslib.Complexity.CountingSimulation
