/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Reachability.DoubleCounting.Controller
import Mathlib.Tactic.Linarith

/-!
# Scalar bounds for arbitrary controller replies

These are bounds for the actual list-valued controller handlers, independent of graph
correctness or exact expected tallies. A list entry is a successful branch; an empty callback
list rejects. Every finite prefix uses the same handlers as `scanNextRound`, including prefixes
that later reject or set the tie flag. The bounds concern retained scalar registers at the
callback boundary, not the workspace or duration of a callback. Native realization remains
part of #6747.

## Main results

* `predecessor_prefix_le`: at most one increment per predecessor tested.
* `scanVertex_prefix_bounds`: at most one count and `k + 1` sum contribution per vertex.
* `scanNextRound_bounds`: arbitrary replies increase a round's count by at most `n` and its
  length sum by at most `n * (k + 1)`.
* `RoundCall.bounds` and `RoundCall.prefix_bounds`: radius/fuel conservation and quadratic
  count/cubic sum bounds throughout the reachable controller call tree.

`RoundCall.result_mem` connects this proof-level call relation to the original controller
without defining another executable dispatch.

The arbitrary index maps in the prefix lemmas include the increasing initial segment
`fun i => ⟨i.val, i.isLt.trans_le hj⟩` for `hj : j ≤ n`. Thus the current loop index is at most
`n`, and each queried index is strictly below `n`. No transcript is retained by these bounds.
See `CslibFrontierTests.DoubleCountingControllerBounds` for rejection and tie clients.
-/

public section
namespace Cslib.DoubleCounting

private theorem foldlM_rank_le {α : Type} (rank : α → ℕ) (d j : ℕ)
    (f : α → Fin j → List α) (a b : α)
    (hstep : ∀ a i b, b ∈ f a i → rank b ≤ rank a + d)
    (hb : b ∈ Fin.foldlM j f a) : rank b ≤ rank a + j * d := by
  induction j generalizing a b with
  | zero =>
    simp only [Fin.foldlM_zero, List.pure_def, List.mem_singleton] at hb
    subst b
    simp
  | succ j ih =>
    simp only [Fin.foldlM_succ_last, List.bind_eq_flatMap, List.mem_flatMap] at hb
    obtain ⟨c, hc, hb⟩ := hb
    have hprefix := ih (fun a i => f a i.castSucc) a c
      (fun a i b h => hstep a i.castSucc b h) hc
    have hlast := hstep c (Fin.last j) b hb
    nlinarith

private theorem predecessorStep_le {n : ℕ} (edge : Fin n → Fin n → List Bool)
    (member : Fin n → List Bool) (v u : Fin n) (c b : ℕ)
    (hb : b ∈ predecessorStep edge member v c u) : b ≤ c + 1 := by
  simp only [predecessorStep, List.bind_eq_flatMap, List.mem_flatMap] at hb
  obtain ⟨e, _, hb⟩ := hb
  cases e with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, List.pure_def, List.mem_singleton] at hb
    omega
  | true =>
    simp only [↓reduceIte, List.mem_flatMap] at hb
    obtain ⟨hit, _, hb⟩ := hb
    cases hit <;> simp_all

/-- Every successful predecessor prefix, even one whose continuation later rejects, stores
at most its initial count plus the number of tested indices. Replies may be arbitrary. -/
theorem predecessor_prefix_le {n j : ℕ} (edge : Fin n → Fin n → List Bool)
    (member : Fin n → List Bool) (v : Fin n) (index : Fin j → Fin n) (c b : ℕ)
    (hb : b ∈ Fin.foldlM j (fun c i => predecessorStep edge member v c (index i)) c) :
    b ≤ c + j := by
  simpa using foldlM_rank_le id 1 j _ c b
    (fun c i b h => predecessorStep_le edge member v (index i) c b h) hb

private theorem scanVertex_le {n : ℕ} (edge : Fin n → Fin n → List Bool)
    (member : Fin n → List Bool) (k : ℕ) (a b : RoundUpdate) (v : Fin n)
    (hb : b ∈ scanVertex edge member k a v) :
    b.tally.count ≤ a.tally.count + 1 ∧
      b.tally.lengthSum ≤ a.tally.lengthSum + (k + 1) := by
  simp only [scanVertex, List.bind_eq_flatMap, List.mem_flatMap] at hb
  obtain ⟨hit, _, hb⟩ := hb
  cases hit with
  | true =>
    simp only [↓reduceIte, List.pure_def, List.mem_singleton] at hb
    subst b
    simp
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, List.mem_flatMap] at hb
    obtain ⟨p, _, hb⟩ := hb
    simp only [List.pure_def, List.mem_singleton] at hb
    subst b
    unfold RoundUpdate.addVertex
    split <;> simp

/-- All scalar outer-loop prefixes are bounded without assuming correct membership, absence
of ties, or eventual success. The index map can select the increasing initial segment. -/
theorem scanVertex_prefix_bounds {n j : ℕ} (edge : Fin n → Fin n → List Bool)
    (member : Fin n → List Bool) (k : ℕ) (index : Fin j → Fin n) (a b : RoundUpdate)
    (hb : b ∈ Fin.foldlM j (fun a i => scanVertex edge member k a (index i)) a) :
    b.tally.count ≤ a.tally.count + j ∧
      b.tally.lengthSum ≤ a.tally.lengthSum + j * (k + 1) := by
  constructor
  · simpa using foldlM_rank_le (fun a : RoundUpdate => a.tally.count) 1 j _ a b
      (fun a i b h => (scanVertex_le edge member k a b (index i) h).1) hb
  · exact foldlM_rank_le (fun a : RoundUpdate => a.tally.lengthSum) (k + 1) j _ a b
      (fun a i b h => (scanVertex_le edge member k a b (index i) h).2) hb

/-- The actual round scan satisfies the same bounds, also when its tie flag is set. -/
theorem scanNextRound_bounds {n : ℕ} (edge : Fin n → Fin n → List Bool)
    (member : MembershipScan List n) (k : ℕ) (t : Tally) (a : RoundUpdate)
    (ha : a ∈ scanNextRound edge member k t) :
    a.tally.count ≤ t.count + n ∧ a.tally.lengthSum ≤ t.lengthSum + n * (k + 1) :=
by
  apply scanVertex_prefix_bounds edge (member k t) k id ⟨t, false⟩ a
  simpa only [scanNextRound, id_eq] using ha

/-- Reachable recursive calls of the existing controller, starting with its actual fuel and
initial tally. This is a proof-level call relation, not another controller implementation. -/
inductive RoundCall {n : ℕ} (edge : Fin n → Fin n → List Bool)
    (member : MembershipScan List n) : ℕ → ℕ → Tally → Prop where
  /-- The initial call. -/
  | initial : RoundCall edge member n 0 ⟨1, 0⟩
  /-- Exactly the recursive branch of `runRounds`; tied and stable rounds do not recurse. -/
  | next {fuel k t a} : RoundCall edge member (fuel + 1) k t →
      a ∈ scanNextRound edge member k t → a.bad = false → a.tally.count ≠ t.count →
      RoundCall edge member fuel (k + 1) a.tally

/-- Agreement with actual dispatch: every result at a reachable call is a result of the
original controller. List membership here forgets multiplicity only for this reachability fact. -/
theorem RoundCall.result_mem {n fuel k : ℕ} {edge : Fin n → Fin n → List Bool}
    {member : MembershipScan List n} {t : Tally} (h : RoundCall edge member fuel k t)
    (target : Fin n) {result : Option ControllerVerdict}
    (hr : result ∈ runRounds edge member target fuel k t) :
    result ∈ runController edge member target := by
  induction h with
  | initial => exact hr
  | next h ha hbad hcount ih =>
    apply ih
    simp only [runRounds, runRoundsWith, List.bind_eq_flatMap, List.mem_flatMap]
    refine ⟨_, ha, ?_⟩
    simpa only [hbad, Bool.false_eq_true, ↓reduceIte, beq_iff_eq,
      hcount, runRounds] using hr

/-- All reachable round boundaries, including those before a later rejection, have bounded
radius and scalar registers for arbitrary replies. The sum bound is deliberately conservative. -/
theorem RoundCall.bounds {n fuel k : ℕ} {edge : Fin n → Fin n → List Bool}
    {member : MembershipScan List n} {t : Tally} (h : RoundCall edge member fuel k t) :
    fuel + k = n ∧ t.count ≤ 1 + k * n ∧ t.lengthSum ≤ n * k * k := by
  induction h with
  | initial => simp
  | @next fuel k t a h ha _ _ ih =>
    obtain ⟨hc, hs⟩ := scanNextRound_bounds _ _ k t a ha
    obtain ⟨hf, ht, hl⟩ := ih
    refine ⟨by omega, ?_, ?_⟩ <;> nlinarith

/-- At every vertex prefix of an active controller round the radius, loop index, count and
sum are polynomially bounded, including tied prefixes and prefixes of rejecting branches.
Together with `predecessor_prefix_le`, all retained numeric registers have polynomial bounds
sufficient for binary logarithmic-length encodings. No callee workspace is asserted. -/
theorem RoundCall.prefix_bounds {n fuel k j : ℕ} {edge : Fin n → Fin n → List Bool}
    {member : MembershipScan List n} {t : Tally} (h : RoundCall edge member fuel k t)
    (hactive : 0 < fuel) (hj : j ≤ n) (index : Fin j → Fin n) (a : RoundUpdate)
    (ha : a ∈ Fin.foldlM j (fun a i => scanVertex edge (member k t) k a (index i))
      ⟨t, false⟩) :
    k < n ∧ j ≤ n ∧ a.tally.count ≤ 1 + n * n ∧ a.tally.lengthSum ≤ n * n * n := by
  obtain ⟨hf, hc, hs⟩ := h.bounds
  obtain ⟨hac, has⟩ := scanVertex_prefix_bounds edge (member k t) k index ⟨t, false⟩ a ha
  have hk : k + 1 ≤ n := by omega
  have hm : j * (k + 1) ≤ n * (k + 1) := Nat.mul_le_mul_right _ hj
  have hsum : a.tally.lengthSum ≤ n * (k + 1) * (k + 1) := by nlinarith
  have hprod := Nat.mul_le_mul (Nat.mul_le_mul_left n hk) hk
  refine ⟨by omega, hj, ?_, hsum.trans hprod⟩
  nlinarith

end Cslib.DoubleCounting
