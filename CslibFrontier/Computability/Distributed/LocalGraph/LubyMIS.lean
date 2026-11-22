/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.LubyMIS
public import CslibFrontier.Computability.Distributed.LocalGraph.Basic
public import CslibFrontier.Languages.Probabilistic.Rational
public import CslibFrontier.Languages.Probabilistic.SampleEach
import CslibFrontier.Probability.PMF.Bool
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.ToReal
import CslibFrontier.Probability.PMF.Union
import CslibFrontier.Probability.Product
import CslibFrontier.Tactic.SuppCases
import Mathlib.Tactic.Linarith

/-!
# Luby's Randomized Maximal Independent Set Protocols in the `LOCAL` Model

Randomized synchronous `LOCAL` maximal independent set (`MIS`) protocols on finite simple graphs
`G : SimpleGraph V` (steps towards `#7505` and `#3270`, after [Luby][Luby1986],
[Alon, Babai and Itai][AlonBabaiItai1986], and [Wattenhofer][Wattenhofer2016] Chapter 7).

Both variants reuse `Cslib.Algorithms.Lean.LubyMIS.State`, `liveGraph`, `liveEdges`, `init`, and
`Invariant` directly instead of duplicating the MIS state representation:

1. **Variant A — Two-round synchronous `LOCAL` random-priority Luby (`priorityProtocol`,
   `localPriorityMIS`):** implements each phase of `Cslib.Algorithms.Lean.LubyMIS` as two
   synchronous broadcast `LOCAL` rounds (even rounds exchange `(live, rank)` to identify local
   minima; odd rounds broadcast `joining` to update `chosen` and deactivate `joining` nodes and
   their neighbors). We prove exact `2 * k`-round state simulation
   (`priorityProtocol_state_two_mul`) and exact `PMF` law equality
   `ProbComp.eval (localPriorityRun G k) = ProbComp.eval (LubyMIS.run G k)`
   (`eval_localPriorityRun`) and `ProbComp.eval (localPriorityMIS G k) = ProbComp.eval
   (LubyMIS.lubyMIS G k)` (`eval_localPriorityMIS`), transporting unconditional independence,
   `2 |V|`-round Las Vegas `MIS` termination, single-phase half-edge removal, and
   `2 ((c + 2) ⌈log₂ n⌉ + 1)`-round `1 - n ^ (-c)` high-probability termination to `LOCAL`.
2. **Variant B — Degree-weighted coin-flip Luby (`liveDegreeProtocol`, `coinResolveProtocol`,
   `localCoinPhase`, `localCoinRun`, `localCoinLubyMIS`):** following Algorithm 7.6 ("Fast MIS")
   of [Wattenhofer][Wattenhofer2016], §7.2, pp. 73–76 (presenting the Monte Carlo algorithm of
   [Luby][Luby1986], with the good-edge orientation argument also in
   [Alon, Babai and Itai][AlonBabaiItai1986], Lemma 4.4, p. 572), each live vertex `v` learns its
   live degree `d_H(v)` in `1` `LOCAL` round (`liveDegreeProtocol`), independently flips `true` with
   probability `1 / (2 d_H(v))` when `d_H(v) ≥ 1` and `1` when `d_H(v) = 0` (`localMarkProb`), and
   resolves conflicts and neighbor deletion in `2` `LOCAL` rounds (`coinResolveProtocol`), breaking
   degree ties by injective node identifiers. (By contrast, Procedure `IN(H)` of
   `[AlonBabaiItai1986]`, §3, p. 570, marks vertices with probability `1 / d_H(v)` and resolves
   marked edges via randomized `d_H(u) / (d_H(u) + d_H(v))` erasure.) We prove exact end-to-end
   program equality `localCoinPhase = coinPhase`, `localCoinRun = coinRun`, and
   `localCoinLubyMIS = coinLubyMIS`, together with:
   * unconditional `Invariant` preservation (`invariant_coinStep`) and independence on every support
     trajectory (`isIndepSet_of_mem_support_localCoinLubyMIS`);
   * single-phase positive progress probability `≥ 1 / (2 |V|)` strictly shrinking `s.live` on any
     nonempty live set (`inv_two_mul_card_le_prob_live_lt`);
   * joining probability `≥ 1 / (4 d_H(v))` (after Lemma 7.7 of `[Wattenhofer2016]`), good-vertex
     removal probability `≥ 1 / 36` (after Lemma 7.8), good-edge density `≥ |E(H)| / 2` (after
     Lemmas 7.9–7.10 and `[AlonBabaiItai1986]` Lemma 4.4), single-phase expected edge contraction
     `≤ (71 / 72) |E(H)|` (after Theorem 7.11, `seventyTwo_mul_expect_liveEdges_coinPhase_le`), and
     `50 (c + 2) ⌈log₂ n⌉ + 1`-phase (`3 (50 (c + 2) ⌈log₂ n⌉ + 1)`-round) `1 - n ^ (-c)`
     high-probability `MIS` convergence
     (`toOuterMeasure_not_maximal_localCoinLubyMIS_le_inv_pow`).

Pairwise-independent PRAM derandomization (`[Luby1986]`), Alon–Babai–Itai's `1 / d_H(v)` +
randomized edge-erasure variant (`[AlonBabaiItai1986]`), and expected stopping time (`O(log n)`
expected phases via stopping times) remain open under `#7505` and `#3270`.

## Main definitions

* `Cslib.Distributed.LocalGraph.priorityProtocol`, `localPriorityRun`, `localPriorityMIS`:
  two-round-per-phase synchronous `LOCAL` random-priority Luby protocol and its `ProbComp` runners.
* `Cslib.Distributed.LocalGraph.higherPriority`, `markProb`, `sampleMarks`, `coinJoiners`,
  `coinStep`, `coinPhase`, `coinRun`, `coinLubyMIS`: degree-weighted coin-flip Luby phase and
  multi-phase `ProbComp` specification.
* `Cslib.Distributed.LocalGraph.liveDegreeProtocol`, `coinResolveProtocol`, `localMarkProb`,
  `localCoinPhase`, `localCoinRun`, `localCoinLubyMIS`: `1 + 2 = 3`-round synchronous `LOCAL`
  broadcast protocols and multi-phase `LOCAL` `ProbComp` runners executing degree-weighted Luby.

## Main results

* `Cslib.Distributed.LocalGraph.priorityProtocol_state_two_mul`, `eval_localPriorityRun`,
  `eval_localPriorityMIS`, `isIndepSet_of_mem_support_localPriorityMIS`,
  `maximal_of_mem_support_localPriorityMIS`,
  `toOuterMeasure_not_maximal_localPriorityMIS_le_inv_pow`: `LOCAL` simulation and `O(log n)`-round
  w.h.p. `MIS` guarantees for Variant A.
* `Cslib.Distributed.LocalGraph.liveDegreeProtocol_run`, `coinResolveProtocol_run`,
  `localCoinPhase_eq_coinPhase`, `eval_localCoinRun`, `eval_localCoinLubyMIS`: end-to-end
  `3`-round-per-phase `LOCAL` simulation of degree-weighted Luby.
* `Cslib.Distributed.LocalGraph.invariant_coinStep`, `isIndepSet_of_mem_support_coinLubyMIS`,
  `isIndepSet_of_mem_support_localCoinLubyMIS`, `inv_two_mul_card_le_prob_live_lt`: unconditional
  independence and positive single-phase progress for Variant B.
* `Cslib.Distributed.LocalGraph.one_div_four_deg_le_prob_coinJoiners`,
  `one_div_36_le_prob_removed_of_isGoodVertex`,
  `seventyTwo_mul_expect_liveEdges_coinPhase_le`,
  `toOuterMeasure_not_maximal_coinLubyMIS_le_inv_pow`,
  `toOuterMeasure_not_maximal_localCoinLubyMIS_le_inv_pow`: expected `(1 / 72) |E|` edge removal and
  `O(log n)`-round high-probability `MIS` convergence for Variant B.

## References

* [M. Luby, *A simple parallel algorithm for the maximal independent set problem*][Luby1986]
* [N. Alon, L. Babai and A. Itai, *A fast and simple randomized parallel algorithm for the maximal
  independent set problem*][AlonBabaiItai1986], §§3–4, pp. 569–572
* [R. Wattenhofer, *Principles of Distributed Computing*][Wattenhofer2016], §7.2–7.3, pp. 73–79
-/

public section

namespace Cslib.Distributed.LocalGraph

open Cslib.Algorithms.Lean Cslib.Probability Finset
open scoped ENNReal

/-! ### Variant A: Two-round-per-phase synchronous `LOCAL` random-priority Luby -/

/-- Per-node state for the two-round-per-phase `LOCAL` implementation of random-priority Luby. -/
structure PriorityNodeState where
  /-- Per-phase priority values held locally by this node. -/
  ranks : ℕ → ℕ
  /-- Whether this node has joined the independent set. -/
  chosen : Bool
  /-- Whether this node remains live (neither chosen nor adjacent to a chosen node). -/
  live : Bool
  /-- Whether this node won the priority comparison in the first round of the current phase. -/
  joining : Bool

/-- One-hop broadcast message for `priorityProtocol`. -/
structure PriorityMsg where
  /-- Sender's `live` flag at the start of the round. -/
  live : Bool
  /-- Sender's priority for the current phase (`r / 2`). -/
  rank : ℕ
  /-- Sender's `joining` flag computed in the even round of the current phase. -/
  joining : Bool
  deriving @[expose] DecidableEq

/-- Deterministic two-round-per-phase `BroadcastProtocol` executing random-priority Luby from
locally supplied per-phase priorities `ranks : ℕ → ℕ`.

* In round `2 p`, every node broadcasts `(live, ranks p, false)` and sets `joining = true` iff it is
  live and strictly precedes every live neighbor's priority in phase `p`.
* In round `2 p + 1`, every node broadcasts `joining`, adds itself to `chosen` if `joining = true`,
  and deactivates itself (`live := false`) if it or any neighbor joined. -/
@[expose] def priorityProtocol : BroadcastProtocol (ℕ → ℕ) PriorityNodeState PriorityMsg Bool where
  init ranks := { ranks := ranks, chosen := false, live := true, joining := false }
  send r s := { live := s.live, rank := s.ranks (r / 2), joining := s.joining }
  recv r s msgs :=
    if r % 2 = 0 then
      let won := s.live && decide (∀ m ∈ msgs, m.live = true → s.ranks (r / 2) < m.rank)
      { s with joining := won }
    else
      let noNbrJoined := decide (∀ m ∈ msgs, m.joining = false)
      { s with
        chosen := s.chosen || s.joining
        live := s.live && !s.joining && noNbrJoined
        joining := false }
  output s := s.chosen

section VariantA

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Iterated centralized `LubyMIS.step` along an arbitrary sequence of rankings `σs`. -/
@[expose] def foldPriorityStep (σs : ℕ → LubyMIS.Ranking V) : ℕ → LubyMIS.State V
  | 0 => LubyMIS.init
  | p + 1 => LubyMIS.step G (foldPriorityStep σs p) (σs p)

private theorem foldPriorityStep_congr {σs₁ σs₂ : ℕ → LubyMIS.Ranking V} :
    ∀ {k : ℕ}, (∀ p < k, σs₁ p = σs₂ p) → foldPriorityStep G σs₁ k = foldPriorityStep G σs₂ k
  | 0, _ => rfl
  | k + 1, h => by
    simp only [foldPriorityStep]
    rw [foldPriorityStep_congr fun p hp => h p (Nat.lt_succ_of_lt hp), h k (Nat.lt_succ_self k)]

omit [DecidableEq V] in
private theorem priorityProtocol_state_succ (x : V → ℕ → ℕ) (r : ℕ) (u : V) :
    priorityProtocol.state G x (r + 1) u =
      let s := priorityProtocol.state G x r u
      let msgs := (G.neighborFinset u).val.map fun w =>
        let sw := priorityProtocol.state G x r w
        ({ live := sw.live, rank := sw.ranks (r / 2), joining := sw.joining } : PriorityMsg)
      if r % 2 = 0 then
        let won := s.live && decide (∀ m ∈ msgs, m.live = true → s.ranks (r / 2) < m.rank)
        { s with joining := won }
      else
        { s with
          chosen := s.chosen || s.joining
          live := s.live && !s.joining && decide (∀ m ∈ msgs, m.joining = false)
          joining := false } := rfl

omit [DecidableEq V] in
private theorem priorityProtocol_ranks (x : V → ℕ → ℕ) (r : ℕ) (u : V) :
    (priorityProtocol.state G x r u).ranks = x u := by
  induction r generalizing u with
  | zero => rfl
  | succ r ih =>
    rw [priorityProtocol_state_succ]
    dsimp only
    split_ifs <;> exact ih u

/-- After `2 * p` synchronous `LOCAL` rounds of `priorityProtocol` on per-phase rankings `σs`, the
distributed `(chosen, live)` flags match `foldPriorityStep G σs p` at every vertex. -/
theorem priorityProtocol_state_two_mul (σs : ℕ → LubyMIS.Ranking V) (p : ℕ) (u : V) :
    ((priorityProtocol.state G (fun v q => (σs q v).val) (2 * p) u).chosen = true ↔
      u ∈ (foldPriorityStep G σs p).chosen) ∧
    ((priorityProtocol.state G (fun v q => (σs q v).val) (2 * p) u).live = true ↔
      u ∈ (foldPriorityStep G σs p).live) := by
  set x : V → ℕ → ℕ := fun v q => (σs q v).val
  induction p generalizing u with
  | zero =>
    simp [foldPriorityStep, LubyMIS.init, priorityProtocol]
  | succ p ih =>
    have heven_mod : (2 * p) % 2 = 0 := Nat.mul_mod_right 2 p
    have heven_div : (2 * p) / 2 = p := Nat.mul_div_right p two_pos
    have hodd_mod : (2 * p + 1) % 2 ≠ 0 := by omega
    -- Characterize `joining` after round `2 * p`.
    have hjoin : ∀ w,
        (priorityProtocol.state G x (2 * p + 1) w).joining = true ↔
          w ∈ LubyMIS.joiners G (foldPriorityStep G σs p) (σs p) := by
      intro w
      rw [priorityProtocol_state_succ]
      dsimp only
      simp only [heven_mod, ↓reduceIte, heven_div, Bool.and_eq_true, decide_eq_true_eq,
        Multiset.mem_map, Finset.mem_val, SimpleGraph.mem_neighborFinset,
        priorityProtocol_ranks G x (2 * p) w, (ih w).2, LubyMIS.mem_joiners]
      refine and_congr_right fun _ => ⟨fun h z hz hadj => ?_, fun h m hm hmlive => ?_⟩
      · have hlt := h _ ⟨z, hadj, rfl⟩ ((ih z).2.2 hz)
        rw [priorityProtocol_ranks G x (2 * p) z] at hlt
        exact Fin.lt_def.2 hlt
      · obtain ⟨z, hadj, rfl⟩ := hm
        dsimp only at hmlive ⊢
        rw [priorityProtocol_ranks G x (2 * p) z]
        have hz : z ∈ (foldPriorityStep G σs p).live := (ih z).2.1 hmlive
        exact Fin.lt_def.1 (h z hz hadj)
    have hchosen_mid : ∀ w,
        (priorityProtocol.state G x (2 * p + 1) w).chosen =
          (priorityProtocol.state G x (2 * p) w).chosen := by
      intro w
      rw [priorityProtocol_state_succ]
      dsimp only
      simp only [heven_mod, ↓reduceIte]
    have hlive_mid : ∀ w,
        (priorityProtocol.state G x (2 * p + 1) w).live =
          (priorityProtocol.state G x (2 * p) w).live := by
      intro w
      rw [priorityProtocol_state_succ]
      dsimp only
      simp only [heven_mod, ↓reduceIte]
    -- Advance through round `2 * p + 1` to `2 * (p + 1) = (2 * p + 1) + 1`.
    have hstep2 : 2 * (p + 1) = (2 * p + 1) + 1 := by omega
    rw [hstep2, priorityProtocol_state_succ, foldPriorityStep]
    dsimp only
    simp only [hodd_mod, ↓reduceIte, hchosen_mid u, hlive_mid u]
    constructor
    · simp only [Bool.or_eq_true, (ih u).1, hjoin u, LubyMIS.step_chosen, mem_union]
    · simp only [Bool.and_eq_true, decide_eq_true_eq, Multiset.mem_map, Finset.mem_val,
        SimpleGraph.mem_neighborFinset, (ih u).2, LubyMIS.mem_step_live, and_assoc]
      refine and_congr_right fun _ => ?_
      have hnot_join : ((! (priorityProtocol.state G x (2 * p + 1) u).joining) = true) ↔
          u ∉ LubyMIS.joiners G (foldPriorityStep G σs p) (σs p) := by
        rw [Bool.not_eq_true', ← Bool.not_eq_true, hjoin u]
      rw [hnot_join]
      refine and_congr_right fun _ => ⟨fun h z hz hadj => ?_, fun h m hm => ?_⟩
      · have hzf : (priorityProtocol.state G x (2 * p + 1) z).joining = false :=
          h _ ⟨z, hadj.symm, rfl⟩
        exact ((hjoin z).2 hz).symm.trans hzf |> Bool.true_eq_false.mp
      · obtain ⟨z, hadj, rfl⟩ := hm
        dsimp only
        rw [← Bool.not_eq_true, hjoin z]
        exact fun hzj => h z hzj hadj.symm

/-- Sample `k` independent uniform vertex rankings and pack them into `ℕ → LubyMIS.Ranking V`. -/
private noncomputable def sampleRankings : ℕ → ProbComp (ℕ → LubyMIS.Ranking V)
  | 0 => pure fun _ => Fintype.equivFin V
  | k + 1 => do
    let σs ← sampleRankings k
    let σ ← ProbComp.uniform (LubyMIS.Ranking V)
    return Function.update σs k σ

/-- Randomized `2 * k`-round `LOCAL` execution of random-priority Luby, returning the global
`(chosen, live)` `LubyMIS.State V` read off from `priorityProtocol.state` at round `2 * k`. -/
noncomputable def localPriorityRun (k : ℕ) : ProbComp (LubyMIS.State V) := do
  let σs ← sampleRankings (V := V) k
  let st := priorityProtocol.state G (fun v q => (σs q v).val) (2 * k)
  return { chosen := univ.filter fun u => (st u).chosen = true
           live := univ.filter fun u => (st u).live = true }

/-- Randomized `2 * k`-round `LOCAL` execution of random-priority Luby, returning the set of
vertices whose `priorityProtocol` output after `2 * k` synchronous rounds is `true`. -/
noncomputable def localPriorityMIS (k : ℕ) : ProbComp (Finset V) :=
  LubyMIS.State.chosen <$> localPriorityRun G k

/-- Running `priorityProtocol` for `2 * k` synchronous `LOCAL` rounds under fresh per-phase
rankings has the exact same state `PMF` as `LubyMIS.run G k`. -/
theorem eval_localPriorityRun (k : ℕ) :
    ProbComp.eval (localPriorityRun G k) = ProbComp.eval (LubyMIS.run G k) := by
  have hst_eq : ∀ σs : ℕ → LubyMIS.Ranking V,
      ({ chosen := univ.filter fun u =>
           (priorityProtocol.state G (fun v q => (σs q v).val) (2 * k) u).chosen = true
         live := univ.filter fun u =>
           (priorityProtocol.state G (fun v q => (σs q v).val) (2 * k) u).live = true } :
        LubyMIS.State V) = foldPriorityStep G σs k := by
    intro σs
    cases h : foldPriorityStep G σs k with
    | mk ch lv =>
      congr 1 <;> ext u <;> simp only [mem_filter, mem_univ, true_and]
      · simpa only [h] using (priorityProtocol_state_two_mul G σs k u).1
      · simpa only [h] using (priorityProtocol_state_two_mul G σs k u).2
  have hdef : localPriorityRun G k =
      (fun σs => foldPriorityStep G σs k) <$> sampleRankings (V := V) k := by
    simp only [localPriorityRun, bind_pure_comp, hst_eq]
  rw [hdef]
  clear hst_eq hdef
  induction k with
  | zero =>
    rw [sampleRankings, LubyMIS.run_zero, map_pure, foldPriorityStep]
  | succ k ih =>
    rw [LubyMIS.run_succ, ProbComp.eval_bind, ← ih]
    simp only [sampleRankings, ProbComp.eval_map, ProbComp.eval_bind, _root_.PMF.bind_map,
      _root_.PMF.map_bind, LubyMIS.eval_phase, ProbComp.eval_uniform]
    congr 1 with σs : 1
    congr 1 with σ : 1
    rw [ProbComp.eval_pure, _root_.PMF.pure_map]
    simp only [Function.comp_apply, foldPriorityStep]
    have heq : foldPriorityStep G (Function.update σs k σ) k = foldPriorityStep G σs k :=
      foldPriorityStep_congr G fun p hp => Function.update_of_ne (Nat.ne_of_lt hp) _ _
    rw [heq, Function.update_self]

/-- Running `priorityProtocol` for `2 * k` synchronous `LOCAL` rounds under fresh per-phase
rankings has the exact same output `PMF` as `LubyMIS.lubyMIS G k`. -/
theorem eval_localPriorityMIS (k : ℕ) :
    ProbComp.eval (localPriorityMIS G k) = ProbComp.eval (LubyMIS.lubyMIS G k) := by
  rw [localPriorityMIS, ProbComp.eval_map, eval_localPriorityRun, LubyMIS.eval_lubyMIS]

/-- Step towards `#7505` and `#3270` (not the cited endpoint, after [Luby][Luby1986] and Lemma 7.14
of [Wattenhofer][Wattenhofer2016], §7.3, p. 78): after `2 * k` synchronous `LOCAL` rounds of
`localPriorityRun`, the expected number of live edges is at most `|E(G)| / 2 ^ k`. -/
theorem two_pow_mul_expect_liveEdges_localPriorityRun_le (k : ℕ) :
    2 ^ k * ∑' t, ProbComp.eval (localPriorityRun G k) t * (LubyMIS.liveEdges G t : ℝ≥0∞) ≤
      G.edgeFinset.card := by
  rw [eval_localPriorityRun]
  exact LubyMIS.two_pow_mul_expect_liveEdges_run_le G k

/-- Step towards `#7505` and `#3270` (not the cited endpoint, after [Luby][Luby1986] and
[Wattenhofer][Wattenhofer2016], §7.3): after `2 * k` synchronous `LOCAL` rounds, every support
outcome of `localPriorityMIS G k` is an independent set of `G`. -/
theorem isIndepSet_of_mem_support_localPriorityMIS {k : ℕ} {S : Finset V}
    (hS : S ∈ (ProbComp.eval (localPriorityMIS G k)).support) :
    G.IsIndepSet (S : Set V) :=
  LubyMIS.isIndepSet_of_mem_support_lubyMIS G (eval_localPriorityMIS G k ▸ hS)

/-- Step towards `#7505` and `#3270` (not the cited endpoint, after [Luby][Luby1986] and
[Wattenhofer][Wattenhofer2016], §7.3): after `2 * k` synchronous `LOCAL` rounds with
`Fintype.card V ≤ k`, every support outcome of `localPriorityMIS G k` is a maximal independent set
of `G`. -/
theorem maximal_of_mem_support_localPriorityMIS {k : ℕ} (hk : Fintype.card V ≤ k) {S : Finset V}
    (hS : S ∈ (ProbComp.eval (localPriorityMIS G k)).support) :
    Maximal G.IsIndepSet (S : Set V) :=
  LubyMIS.maximal_of_mem_support_lubyMIS G hk (eval_localPriorityMIS G k ▸ hS)

/-- Step towards `#7505` and `#3270` (not the cited endpoint, after [Luby][Luby1986] and
Corollary 7.18 of [Wattenhofer][Wattenhofer2016], §7.3, p. 79): after
`2 * ((c + 2) ⌈log₂ |V|⌉ + 1)` synchronous `LOCAL` rounds, `localPriorityMIS` fails to output a
maximal independent set with probability at most `|V| ^ (-c)`. -/
theorem toOuterMeasure_not_maximal_localPriorityMIS_le_inv_pow (c : ℕ) :
    (ProbComp.eval (localPriorityMIS G ((c + 2) * Nat.clog 2 (Fintype.card V) + 1))).toOuterMeasure
        {S | ¬ Maximal G.IsIndepSet (S : Set V)} ≤ ((Fintype.card V : ℝ≥0∞) ^ c)⁻¹ :=
  eval_localPriorityMIS G ((c + 2) * Nat.clog 2 (Fintype.card V) + 1) ▸
    LubyMIS.toOuterMeasure_not_maximal_lubyMIS_le_inv_pow G c

end VariantA

/-! ### Variant B: Degree-weighted coin-flip Luby (`1 / (2 d(v))` marking) -/

section VariantB

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Priority comparison of [Wattenhofer][Wattenhofer2016], §7.2, Algorithm 7.6: `w` outranks `u`
when `w` has strictly larger live degree, or equal live degree and strictly larger identifier. -/
@[expose] def higherPriority (s : LubyMIS.State V) (uid : V → ℕ) (u w : V) : Prop :=
  let d := (LubyMIS.liveGraph G s.live).degree
  d u < d w ∨ (d u = d w ∧ uid u < uid w)

instance (s : LubyMIS.State V) (uid : V → ℕ) : DecidableRel (higherPriority G s uid) :=
  fun _ _ => inferInstanceAs (Decidable (_ ∨ (_ ∧ _)))

private theorem higherPriority_asymm {s : LubyMIS.State V} {uid : V → ℕ} {u w : V}
    (h : higherPriority G s uid u w) : ¬ higherPriority G s uid w u := by
  unfold higherPriority at h ⊢
  dsimp only at h ⊢
  omega

private theorem higherPriority_total {s : LubyMIS.State V} {uid : V → ℕ}
    (huid : Function.Injective uid) {u w : V} (hne : u ≠ w) :
    higherPriority G s uid u w ∨ higherPriority G s uid w u := by
  have huid_ne : uid u ≠ uid w := fun h => hne (huid h)
  unfold higherPriority
  dsimp only
  omega

private theorem degree_le_of_higherPriority {s : LubyMIS.State V} {uid : V → ℕ} {u w : V}
    (h : higherPriority G s uid u w) :
    (LubyMIS.liveGraph G s.live).degree u ≤ (LubyMIS.liveGraph G s.live).degree w := by
  unfold higherPriority at h
  dsimp only at h
  omega

/-- Degree-weighted marking probability of Algorithm 7.6 ([Wattenhofer][Wattenhofer2016], §7.2):
`0` for non-live vertices, `1` for isolated live vertices (`d_H(v) = 0`), and `1 / (2 d_H(v))` for
live vertices with `d_H(v) ≥ 1`. -/
@[expose] def markProb (s : LubyMIS.State V) (v : V) : ℚ :=
  if v ∈ s.live then
    let d := (LubyMIS.liveGraph G s.live).degree v
    if d = 0 then 1 else 1 / (2 * (d : ℚ))
  else 0

theorem markProb_nonneg (s : LubyMIS.State V) (v : V) : 0 ≤ markProb G s v := by
  unfold markProb
  dsimp only
  split_ifs with hv hd
  · exact zero_le_one
  · positivity
  · exact le_rfl

theorem markProb_le_one (s : LubyMIS.State V) (v : V) : markProb G s v ≤ 1 := by
  unfold markProb
  dsimp only
  split_ifs with hv hd
  · exact le_rfl
  · have hd1 : (1 : ℚ) ≤ (LubyMIS.liveGraph G s.live).degree v := by
      exact_mod_cast Nat.pos_of_ne_zero hd
    exact div_le_one_of_le₀ (by linarith) (by positivity)
  · exact zero_le_one

/-- Sample independent degree-weighted Bernoulli marks across all vertices via
`ProbComp.sampleEach` and `ProbComp.bernoulliRat`. -/
noncomputable def sampleMarks (s : LubyMIS.State V) : ProbComp (V → Bool) :=
  ProbComp.sampleEach fun v => ProbComp.bernoulliRat (markProb G s v)

/-- Live vertices that marked themselves and have no marked live neighbor of higher `(d_H, uid)`
priority. -/
@[expose] def coinJoiners (s : LubyMIS.State V) (uid : V → ℕ) (m : V → Bool) : Finset V :=
  {v ∈ s.live |
    m v = true ∧ ∀ w ∈ s.live, G.Adj v w → higherPriority G s uid v w → m w = false}

/-- Deterministic state update of one degree-weighted Luby phase for mark vector `m`. -/
@[expose] def coinStep (s : LubyMIS.State V) (uid : V → ℕ) (m : V → Bool) : LubyMIS.State V where
  chosen := s.chosen ∪ coinJoiners G s uid m
  live := {v ∈ s.live | v ∉ coinJoiners G s uid m ∧ ∀ u ∈ coinJoiners G s uid m, ¬ G.Adj u v}

/-- One randomized phase of degree-weighted Luby (`[Wattenhofer2016]`, Algorithm 7.6). -/
noncomputable def coinPhase (uid : V → ℕ) (s : LubyMIS.State V) : ProbComp (LubyMIS.State V) := do
  let m ← sampleMarks G s
  return coinStep G s uid m

/-- Iterate `k` randomized phases of degree-weighted Luby from `LubyMIS.init`. -/
noncomputable def coinRun (uid : V → ℕ) (k : ℕ) : ProbComp (LubyMIS.State V) :=
  OracleComp.iterate k (coinPhase G uid) LubyMIS.init

/-- Output independent set chosen after `k` phases of degree-weighted Luby. -/
noncomputable def coinLubyMIS (uid : V → ℕ) (k : ℕ) : ProbComp (Finset V) :=
  LubyMIS.State.chosen <$> coinRun G uid k

theorem mem_coinJoiners {s : LubyMIS.State V} {uid : V → ℕ} {m : V → Bool} {v : V} :
    v ∈ coinJoiners G s uid m ↔
      v ∈ s.live ∧ m v = true ∧
        ∀ w ∈ s.live, G.Adj v w → higherPriority G s uid v w → m w = false := by
  simp only [coinJoiners, mem_filter]

theorem coinStep_chosen (s : LubyMIS.State V) (uid : V → ℕ) (m : V → Bool) :
    (coinStep G s uid m).chosen = s.chosen ∪ coinJoiners G s uid m := rfl

theorem mem_coinStep_live {s : LubyMIS.State V} {uid : V → ℕ} {m : V → Bool} {v : V} :
    v ∈ (coinStep G s uid m).live ↔
      v ∈ s.live ∧ v ∉ coinJoiners G s uid m ∧ ∀ u ∈ coinJoiners G s uid m, ¬ G.Adj u v := by
  simp only [coinStep, mem_filter]

theorem coinStep_live_subset (s : LubyMIS.State V) (uid : V → ℕ) (m : V → Bool) :
    (coinStep G s uid m).live ⊆ s.live :=
  fun _ hv => ((mem_coinStep_live G).1 hv).1

theorem eval_coinPhase (uid : V → ℕ) (s : LubyMIS.State V) :
    ProbComp.eval (coinPhase G uid s) =
      (ProbComp.eval (sampleMarks G s)).map (coinStep G s uid) := by
  rw [coinPhase, ProbComp.eval_bind]
  rfl

/-! #### Three-round synchronous `LOCAL` realization of one degree-weighted phase -/

/-- One-round `BroadcastProtocol` in which every node broadcasts its `live` bit and counts its live
neighbors (`d_H(u)`). -/
@[expose] def liveDegreeProtocol : BroadcastProtocol Bool (Bool × ℕ) Bool ℕ where
  init live := (live, 0)
  send _ s := s.1
  recv _ s msgs := (s.1, (msgs.filter (· = true)).card)
  output s := if s.1 then s.2 else 0

/-- In `1` synchronous broadcast round, `liveDegreeProtocol` computes
`(LubyMIS.liveGraph G s.live).degree u` at every vertex `u`. -/
theorem liveDegreeProtocol_run (s : LubyMIS.State V) (u : V) :
    liveDegreeProtocol.run G (fun v => decide (v ∈ s.live)) 1 u =
      (LubyMIS.liveGraph G s.live).degree u := by
  change (if decide (u ∈ s.live) = true then
      ((((G.neighborFinset u).val.map fun w => decide (w ∈ s.live)).filter
        (· = true)).card)
    else 0) = (LubyMIS.liveGraph G s.live).degree u
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  by_cases hu : u ∈ s.live
  · simp only [hu, decide_true, ↓reduceIte, Multiset.filter_map, Function.comp_def,
      decide_eq_true_eq, ← Finset.filter_val, Multiset.card_map, ← Finset.card_def]
    refine congrArg Finset.card ?_
    ext w
    simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset,
      LubyMIS.liveGraph_adj, hu, true_and]
  · simp only [hu, decide_false, Bool.false_eq_true, ↓reduceIte]
    symm
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro w hw
    exact hu ((SimpleGraph.mem_neighborFinset _ _ _).1 hw).2.1

/-- Per-node input to the 2-round conflict-resolution and deactivation `BroadcastProtocol`. -/
structure CoinResolveInput where
  /-- Node identifier for tie-breaking. -/
  uid : ℕ
  /-- Whether the node was already chosen before this phase. -/
  chosen : Bool
  /-- Whether the node is live at the start of this phase. -/
  live : Bool
  /-- Live degree `d_H(u)` learned from `liveDegreeProtocol`. -/
  liveDeg : ℕ
  /-- Local degree-weighted coin flip `m u`. -/
  marked : Bool
  deriving @[expose] DecidableEq

/-- Per-node state for `coinResolveProtocol`. -/
structure CoinResolveState where
  /-- Node identifier. -/
  uid : ℕ
  /-- Current `chosen` bit. -/
  chosen : Bool
  /-- Current `live` bit. -/
  live : Bool
  /-- Live degree `d_H(u)` at the start of the phase. -/
  liveDeg : ℕ
  /-- Local mark bit `m u`. -/
  marked : Bool
  /-- Whether this node won Step 2 (`u ∈ coinJoiners`). -/
  joining : Bool
  deriving @[expose] DecidableEq

/-- One-hop broadcast message for `coinResolveProtocol`. -/
structure CoinResolveMsg where
  /-- Sender's UID. -/
  uid : ℕ
  /-- Sender's `live` bit. -/
  live : Bool
  /-- Sender's `liveDeg`. -/
  liveDeg : ℕ
  /-- Sender's `marked` bit. -/
  marked : Bool
  /-- Sender's `joining` bit. -/
  joining : Bool
  deriving @[expose] DecidableEq

/-- Per-node output `(chosen, live)` after the 2-round conflict-resolution protocol. -/
structure CoinResolveOutput where
  /-- Updated `chosen` bit. -/
  chosen : Bool
  /-- Updated `live` bit. -/
  live : Bool
  deriving @[expose] DecidableEq

/-- Two-round `BroadcastProtocol` executing Steps 2–3 of Algorithm 7.6:
Round `0` exchanges `(uid, live, liveDeg, marked)` to determine `joining`; Round `1` exchanges
`joining` to update `(chosen, live)`. -/
@[expose] def coinResolveProtocol :
    BroadcastProtocol CoinResolveInput CoinResolveState CoinResolveMsg CoinResolveOutput where
  init inp :=
    { uid := inp.uid
      chosen := inp.chosen
      live := inp.live
      liveDeg := inp.liveDeg
      marked := inp.marked
      joining := false }
  send _ st :=
    { uid := st.uid
      live := st.live
      liveDeg := st.liveDeg
      marked := st.marked
      joining := st.joining }
  recv r st msgs :=
    if r = 0 then
      let won := st.live && st.marked && decide (∀ msg ∈ msgs,
        msg.live = true →
          (st.liveDeg < msg.liveDeg ∨ (st.liveDeg = msg.liveDeg ∧ st.uid < msg.uid)) →
            msg.marked = false)
      { st with joining := won }
    else
      let noNbrJoined := decide (∀ msg ∈ msgs, msg.joining = false)
      { st with
        chosen := st.chosen || st.joining
        live := st.live && !st.joining && noNbrJoined }
  output st := { chosen := st.chosen, live := st.live }

omit [DecidableEq V] in
private theorem coinResolveProtocol_state_succ (inp : V → CoinResolveInput) (r : ℕ) (u : V) :
    coinResolveProtocol.state G inp (r + 1) u =
      let st := coinResolveProtocol.state G inp r u
      let msgs := (G.neighborFinset u).val.map fun w =>
        let sw := coinResolveProtocol.state G inp r w
        ({ uid := sw.uid, live := sw.live, liveDeg := sw.liveDeg,
           marked := sw.marked, joining := sw.joining } : CoinResolveMsg)
      if r = 0 then
        { st with joining := st.live && st.marked && decide (∀ msg ∈ msgs,
            msg.live = true →
              (st.liveDeg < msg.liveDeg ∨ (st.liveDeg = msg.liveDeg ∧ st.uid < msg.uid)) →
                msg.marked = false) }
      else
        { st with
          chosen := st.chosen || st.joining
          live := st.live && !st.joining && decide (∀ msg ∈ msgs, msg.joining = false) } := rfl

/-- Running `coinResolveProtocol` for `2` synchronous `LOCAL` rounds from the locally computed live
degrees and coin flips `m` produces the exact `(chosen, live)` state `coinStep G s uid m`. -/
theorem coinResolveProtocol_run (s : LubyMIS.State V) (uid : V → ℕ) (m : V → Bool) (u : V) :
    let inp : V → CoinResolveInput := fun v =>
      { uid := uid v
        chosen := decide (v ∈ s.chosen)
        live := decide (v ∈ s.live)
        liveDeg := liveDegreeProtocol.run G (fun w => decide (w ∈ s.live)) 1 v
        marked := m v }
    ((coinResolveProtocol.run G inp 2 u).chosen = true ↔ u ∈ (coinStep G s uid m).chosen) ∧
    ((coinResolveProtocol.run G inp 2 u).live = true ↔ u ∈ (coinStep G s uid m).live) := by
  intro inp
  have h0_eq : ∀ w, coinResolveProtocol.state G inp 0 w =
      { uid := uid w
        chosen := decide (w ∈ s.chosen)
        live := decide (w ∈ s.live)
        liveDeg := (LubyMIS.liveGraph G s.live).degree w
        marked := m w
        joining := false } := fun w => by
    change coinResolveProtocol.init (inp w) = _
    dsimp only [coinResolveProtocol, inp]
    rw [liveDegreeProtocol_run]
  have hjoin : ∀ w,
      (coinResolveProtocol.state G inp 1 w).joining = true ↔
        w ∈ coinJoiners G s uid m := by
    intro w
    change (coinResolveProtocol.state G inp (0 + 1) w).joining = true ↔ _
    rw [coinResolveProtocol_state_succ]
    dsimp only
    simp only [↓reduceIte, h0_eq, Bool.and_eq_true, decide_eq_true_eq, Multiset.mem_map,
      Finset.mem_val, SimpleGraph.mem_neighborFinset, mem_coinJoiners, and_assoc]
    refine and_congr_right fun _ => and_congr_right fun _ =>
      ⟨fun h z hz hadj hprio => ?_, fun h msg hmsg hmlive hprio => ?_⟩
    · exact h _ ⟨z, hadj, rfl⟩ (decide_eq_true hz) hprio
    · obtain ⟨z, hadj, rfl⟩ := hmsg
      dsimp only at hmlive hprio ⊢
      exact h z (of_decide_eq_true hmlive) hadj hprio
  have hst2 : coinResolveProtocol.run G inp 2 u =
      { chosen := (coinResolveProtocol.state G inp (1 + 1) u).chosen
        live := (coinResolveProtocol.state G inp (1 + 1) u).live } := rfl
  rw [hst2, coinResolveProtocol_state_succ]
  have h1_chosen : (coinResolveProtocol.state G inp 1 u).chosen = decide (u ∈ s.chosen) := rfl
  have h1_live : (coinResolveProtocol.state G inp 1 u).live = decide (u ∈ s.live) := rfl
  dsimp only
  simp only [Nat.one_ne_zero, ↓reduceIte, h1_chosen, h1_live]
  constructor
  · simp only [Bool.or_eq_true, decide_eq_true_eq, hjoin u, coinStep_chosen, mem_union]
  · simp only [Bool.and_eq_true, decide_eq_true_eq, Multiset.mem_map, Finset.mem_val,
      SimpleGraph.mem_neighborFinset, mem_coinStep_live, and_assoc]
    refine and_congr_right fun _ => ?_
    have hnot_join : ((! (coinResolveProtocol.state G inp 1 u).joining) = true) ↔
        u ∉ coinJoiners G s uid m := by
      rw [Bool.not_eq_true', ← Bool.not_eq_true, hjoin u]
    rw [hnot_join]
    refine and_congr_right fun _ => ⟨fun h z hz hadj => ?_, fun h msg hmsg => ?_⟩
    · have hzf : (coinResolveProtocol.state G inp 1 z).joining = false :=
        h _ ⟨z, hadj.symm, rfl⟩
      exact ((hjoin z).2 hz).symm.trans hzf |> Bool.true_eq_false.mp
    · obtain ⟨z, hadj, rfl⟩ := hmsg
      dsimp only
      rw [← Bool.not_eq_true, hjoin z]
      exact fun hzj => h z hzj hadj.symm

/-- Local marking probability computed by a node solely from its own `live` bit and its locally
discovered `liveDeg` (`0` if non-live, `1` if `liveDeg = 0`, and `1 / (2 * liveDeg)` otherwise). -/
@[expose] def localMarkProb (live : Bool) (liveDeg : ℕ) : ℚ :=
  if live then
    if liveDeg = 0 then 1 else 1 / (2 * (liveDeg : ℚ))
  else 0

/-- One `3`-round synchronous `LOCAL` phase of degree-weighted Luby:
1. `1` broadcast round (`liveDegreeProtocol`) in which each node learns `liveDeg`;
2. independent local Bernoulli coin flips with probability `localMarkProb`;
3. `2` broadcast rounds (`coinResolveProtocol`) updating `(chosen, live)`. -/
noncomputable def localCoinPhase (uid : V → ℕ) (s : LubyMIS.State V) :
    ProbComp (LubyMIS.State V) := do
  let liveDeg := liveDegreeProtocol.run G (fun v => decide (v ∈ s.live)) 1
  let m ← ProbComp.sampleEach fun v =>
    ProbComp.bernoulliRat (localMarkProb (decide (v ∈ s.live)) (liveDeg v))
  let out := coinResolveProtocol.run G
    (fun v =>
      { uid := uid v
        chosen := decide (v ∈ s.chosen)
        live := decide (v ∈ s.live)
        liveDeg := liveDeg v
        marked := m v }) 2
  return { chosen := univ.filter fun u => (out u).chosen = true
           live := univ.filter fun u => (out u).live = true }

/-- Iterate `k` synchronous `3`-round `LOCAL` phases (`3 * k` communication rounds in total) of
degree-weighted Luby from `LubyMIS.init`. -/
noncomputable def localCoinRun (uid : V → ℕ) (k : ℕ) : ProbComp (LubyMIS.State V) :=
  OracleComp.iterate k (localCoinPhase G uid) LubyMIS.init

/-- Output independent set chosen after `k` synchronous `3`-round `LOCAL` phases (`3 * k`
communication rounds) of degree-weighted Luby. -/
noncomputable def localCoinLubyMIS (uid : V → ℕ) (k : ℕ) : ProbComp (Finset V) :=
  LubyMIS.State.chosen <$> localCoinRun G uid k

/-- Each `3`-round `LOCAL` phase `localCoinPhase G uid s` equals `coinPhase G uid s` as a
`ProbComp` program. -/
theorem localCoinPhase_eq_coinPhase (uid : V → ℕ) (s : LubyMIS.State V) :
    localCoinPhase G uid s = coinPhase G uid s := by
  have hprob : (fun v =>
      ProbComp.bernoulliRat
        (localMarkProb (decide (v ∈ s.live))
          (liveDegreeProtocol.run G (fun w => decide (w ∈ s.live)) 1 v))) =
      fun v => ProbComp.bernoulliRat (markProb G s v) := by
    funext v
    congr 1
    rw [liveDegreeProtocol_run]
    unfold localMarkProb markProb
    by_cases hv : v ∈ s.live <;> simp [hv]
  have hout : ∀ m : V → Bool,
      ({ chosen := univ.filter fun u =>
           (coinResolveProtocol.run G
             (fun v =>
               { uid := uid v
                 chosen := decide (v ∈ s.chosen)
                 live := decide (v ∈ s.live)
                 liveDeg := liveDegreeProtocol.run G (fun w => decide (w ∈ s.live)) 1 v
                 marked := m v }) 2 u).chosen = true
         live := univ.filter fun u =>
           (coinResolveProtocol.run G
             (fun v =>
               { uid := uid v
                 chosen := decide (v ∈ s.chosen)
                 live := decide (v ∈ s.live)
                 liveDeg := liveDegreeProtocol.run G (fun w => decide (w ∈ s.live)) 1 v
                 marked := m v }) 2 u).live = true } :
        LubyMIS.State V) = coinStep G s uid m := by
    intro m
    cases h : coinStep G s uid m with
    | mk ch lv =>
      congr 1 <;> ext u <;> simp only [mem_filter, mem_univ, true_and]
      · simpa only [h] using (coinResolveProtocol_run G s uid m u).1
      · simpa only [h] using (coinResolveProtocol_run G s uid m u).2
  dsimp only [localCoinPhase, coinPhase, sampleMarks]
  rw [hprob]
  congr 1 with m : 1
  rw [hout m]

/-- `k` synchronous `3`-round `LOCAL` phases `localCoinRun G uid k` equal `coinRun G uid k`. -/
theorem localCoinRun_eq_coinRun (uid : V → ℕ) (k : ℕ) :
    localCoinRun G uid k = coinRun G uid k := by
  simp only [localCoinRun, coinRun, funext (localCoinPhase_eq_coinPhase G uid)]

/-- Law equality between `localCoinRun` (`3 * k` synchronous `LOCAL` rounds) and `coinRun`. -/
theorem eval_localCoinRun (uid : V → ℕ) (k : ℕ) :
    ProbComp.eval (localCoinRun G uid k) = ProbComp.eval (coinRun G uid k) :=
  congrArg ProbComp.eval (localCoinRun_eq_coinRun G uid k)

/-- Law equality between `localCoinLubyMIS` (`3 * k` synchronous `LOCAL` rounds) and
`coinLubyMIS`. -/
theorem eval_localCoinLubyMIS (uid : V → ℕ) (k : ℕ) :
    ProbComp.eval (localCoinLubyMIS G uid k) = ProbComp.eval (coinLubyMIS G uid k) := by
  simp only [localCoinLubyMIS, coinLubyMIS, localCoinRun_eq_coinRun]

/-! #### Unconditional `Invariant` preservation and positive single-phase progress -/

/-- For injective `uid`, `coinStep` preserves `LubyMIS.Invariant G` under every mark vector
`m : V → Bool`. -/
theorem invariant_coinStep {s : LubyMIS.State V} (hs : LubyMIS.Invariant G s) {uid : V → ℕ}
    (huid : Function.Injective uid) (m : V → Bool) :
    LubyMIS.Invariant G (coinStep G s uid m) := by
  refine ⟨?_, ?_, ?_⟩
  · intro u hu v hv huv hadj
    rw [mem_coe, coinStep_chosen, mem_union] at hu hv
    rcases hu with hu | hu <;> rcases hv with hv | hv
    · exact hs.isIndepSet hu hv huv hadj
    · exact (hs.disjoint v ((mem_coinJoiners G).1 hv).1 u hu).1 hadj
    · exact (hs.disjoint u ((mem_coinJoiners G).1 hu).1 v hv).1 hadj.symm
    · obtain ⟨hul, hum, hup⟩ := (mem_coinJoiners G).1 hu
      obtain ⟨hvl, hvm, hvp⟩ := (mem_coinJoiners G).1 hv
      rcases higherPriority_total G huid huv with hp | hp
      · exact Bool.false_ne_true ((hup v hvl hadj hp).symm.trans hvm)
      · exact Bool.false_ne_true ((hvp u hul hadj.symm hp).symm.trans hum)
  · intro v hv u hu
    rw [mem_coinStep_live] at hv
    rw [coinStep_chosen, mem_union] at hu
    rcases hu with hu | hu
    · exact hs.disjoint v hv.1 u hu
    · exact ⟨hv.2.2 u hu, fun huv => hv.2.1 (huv ▸ hu)⟩
  · intro v hv
    rw [mem_coinStep_live] at hv
    simp only [not_and, not_forall, not_not] at hv
    rw [coinStep_chosen, mem_union]
    by_cases hL : v ∈ s.live
    · by_cases hJ : v ∈ coinJoiners G s uid m
      · exact Or.inl (Or.inr hJ)
      · obtain ⟨u, hu, hadj⟩ := hv hL hJ
        exact Or.inr ⟨u, mem_union_right _ hu, hadj⟩
    · rcases hs.dominated v hL with hv' | ⟨u, hu, hadj⟩
      · exact Or.inl (Or.inl hv')
      · exact Or.inr ⟨u, mem_union_left _ hu, hadj⟩

/-- Every reachable state of `coinRun` satisfies `LubyMIS.Invariant G`. -/
theorem invariant_of_mem_support_coinRun {uid : V → ℕ} (huid : Function.Injective uid)
    {k : ℕ} {s : LubyMIS.State V} (hs : s ∈ (ProbComp.eval (coinRun G uid k)).support) :
    LubyMIS.Invariant G s :=
  ProbComp.iterate_invariant k (coinPhase G uid) LubyMIS.init (fun _ s => LubyMIS.Invariant G s)
    (LubyMIS.invariant_init G)
    (fun _ _ s hinv next hnext => by
      supp_cases hnext [eval_coinPhase] with ⟨m, _, rfl⟩
      exact invariant_coinStep G hinv huid m) s hs

/-- Step towards `#7505` and `#3270` (not the cited endpoint, after [Luby][Luby1986] and Algorithm
7.6 of [Wattenhofer][Wattenhofer2016], §7.2, p. 73): after any number of phases `k`, every support
outcome of `coinLubyMIS G uid k` is an independent set of `G`. -/
theorem isIndepSet_of_mem_support_coinLubyMIS {uid : V → ℕ} (huid : Function.Injective uid)
    {k : ℕ} {S : Finset V} (hS : S ∈ (ProbComp.eval (coinLubyMIS G uid k)).support) :
    G.IsIndepSet (S : Set V) := by
  supp_cases hS [coinLubyMIS] with ⟨s, hs, rfl⟩
  exact (invariant_of_mem_support_coinRun G huid hs).isIndepSet

/-- Step towards `#7505` and `#3270` (not the cited endpoint, after [Luby][Luby1986] and Algorithm
7.6 of [Wattenhofer][Wattenhofer2016], §7.2, p. 73): after `k` synchronous `3`-round `LOCAL` phases
(`3 * k` rounds), every support outcome of `localCoinLubyMIS G uid k` is an independent set of `G`.
-/
theorem isIndepSet_of_mem_support_localCoinLubyMIS {uid : V → ℕ} (huid : Function.Injective uid)
    {k : ℕ} {S : Finset V} (hS : S ∈ (ProbComp.eval (localCoinLubyMIS G uid k)).support) :
    G.IsIndepSet (S : Set V) :=
  isIndepSet_of_mem_support_coinLubyMIS G huid (eval_localCoinLubyMIS G uid k ▸ hS)

/-! #### Product-coin independence helpers and single-phase progress -/

private theorem toOuterMeasure_eq_map_true {α : Type*} (μ : _root_.PMF α) (E : α → Bool) :
    μ.toOuterMeasure {a | E a = true} = (μ.map E) true := by
  rw [_root_.PMF.toOuterMeasure_apply, _root_.PMF.map_apply]
  refine tsum_congr fun a => ?_
  by_cases h : E a = true <;> simp [h]

private theorem eval_sampleMarks (s : LubyMIS.State V) :
    ProbComp.eval (sampleMarks G s) =
      PMF.pi fun v => ProbComp.eval (ProbComp.bernoulliRat (markProb G s v)) :=
  ProbComp.eval_sampleEach _

private theorem toReal_eval_markCoin_true (s : LubyMIS.State V) (v : V) :
    (ProbComp.eval (ProbComp.bernoulliRat (markProb G s v)) true).toReal =
      (markProb G s v : ℝ) :=
  ProbComp.toReal_eval_bernoulliRat_true_of_mem_Icc (markProb_nonneg G s v) (markProb_le_one G s v)

private theorem pi_map_of_update_eq {γ : Type*} (p : V → _root_.PMF Bool) (v : V)
    (r : _root_.PMF Bool) (g : (V → Bool) → γ)
    (hg : ∀ m b, g (Function.update m v b) = g m) :
    (PMF.pi (Function.update p v r)).map g = (PMF.pi p).map g := by
  let proj : (V → Bool) → (V → Bool) := fun m j => if j = v then false else m j
  have hproj_eq : ∀ m, proj m = Function.update m v false := by
    intro m
    funext j
    by_cases hj : j = v
    · subst hj; simp [proj]
    · simp [proj, hj]
  have hg_comp : g ∘ proj = g := by
    funext m
    simp only [Function.comp_apply, hproj_eq, hg]
  have hpi_proj : ∀ q : _root_.PMF Bool,
      (PMF.pi (Function.update p v q)).map proj =
        PMF.pi (Function.update p v (_root_.PMF.pure false)) := by
    intro q
    rw [← PMF.pi_map (Function.update p v q) (fun j b => if j = v then false else b)]
    congr 1 with j : 1
    by_cases hj : j = v
    · subst hj
      simp only [Function.update_self, ↓reduceIte]
      exact _root_.PMF.map_const _ false
    · simp only [Function.update_of_ne hj, hj, ↓reduceIte]
      exact _root_.PMF.map_id _
  calc (PMF.pi (Function.update p v r)).map g
      = ((PMF.pi (Function.update p v r)).map proj).map g := by
        rw [_root_.PMF.map_comp, hg_comp]
    _ = (PMF.pi (Function.update p v (_root_.PMF.pure false))).map g := by rw [hpi_proj r]
    _ = ((PMF.pi (Function.update p v (p v))).map proj).map g := by rw [hpi_proj (p v)]
    _ = (PMF.pi p).map g := by
        rw [_root_.PMF.map_comp, hg_comp, Function.update_eq_self]

private theorem pi_map_and_true_of_update_eq (p : V → _root_.PMF Bool) (v : V)
    (g : (V → Bool) → Bool) (hg : ∀ m b, g (Function.update m v b) = g m) :
    ((PMF.pi p).map fun m => m v && g m) true = p v true * ((PMF.pi p).map g) true := by
  conv_lhs => rw [← PMF.pi_bind_update p v, _root_.PMF.map_bind, _root_.PMF.bind_apply]
  rw [tsum_bool]
  have hfalse : ((PMF.pi (Function.update p v (_root_.PMF.pure false))).map
      fun m => m v && g m) true = 0 := by
    have hcongr : (PMF.pi (Function.update p v (_root_.PMF.pure false))).map
        (fun m => m v && g m) =
        (PMF.pi (Function.update p v (_root_.PMF.pure false))).map
          (Function.const (V → Bool) false) := by
      refine PMF.map_congr_on_support _ _ _ fun m hm => ?_
      have hmv := (PMF.mem_support_pi_iff _ _).1 hm v
      simp only [Function.update_self, _root_.PMF.mem_support_pure_iff] at hmv
      simp [hmv]
    rw [hcongr, _root_.PMF.map_const, _root_.PMF.pure_apply]
    simp
  have htrue : ((PMF.pi (Function.update p v (_root_.PMF.pure true))).map
      fun m => m v && g m) true = ((PMF.pi p).map g) true := by
    have hcongr : (PMF.pi (Function.update p v (_root_.PMF.pure true))).map
        (fun m => m v && g m) =
        (PMF.pi (Function.update p v (_root_.PMF.pure true))).map g := by
      refine PMF.map_congr_on_support _ _ _ fun m hm => ?_
      have hmv := (PMF.mem_support_pi_iff _ _).1 hm v
      simp only [Function.update_self, _root_.PMF.mem_support_pure_iff] at hmv
      simp [hmv]
    rw [hcongr, pi_map_of_update_eq p v (_root_.PMF.pure true) g hg]
  rw [hfalse, htrue, mul_zero, zero_add]

/-- Step towards `#7505` and `#3270` (not the cited endpoint, after [Luby][Luby1986] and Algorithm
7.6 of [Wattenhofer][Wattenhofer2016], §7.2, p. 73): whenever `s.live` is nonempty, a single phase
of `coinPhase G uid s` strictly reduces `s.live.card` with probability at least `1 / (2 |V|)`
(since the highest-`(d_H, uid)` live vertex joins whenever it marks itself). -/
theorem inv_two_mul_card_le_prob_live_lt {s : LubyMIS.State V} (hs : s.live.Nonempty)
    (uid : V → ℕ) :
    (1 : ℝ) / (2 * Fintype.card V) ≤
      ((ProbComp.eval (coinPhase G uid s)).toOuterMeasure
        {t | t.live.card < s.live.card}).toReal := by
  let H := LubyMIS.liveGraph G s.live
  let M := s.live.sup uid + 1
  obtain ⟨v, hv_live, hv_max⟩ := s.live.exists_max_image (fun w => H.degree w * M + uid w) hs
  have hv_top : ∀ w ∈ s.live, ¬ higherPriority G s uid v w := by
    intro w hw hprio
    have hle : H.degree w * M + uid w ≤ H.degree v * M + uid v := hv_max w hw
    have huv_le : uid v < M := Nat.lt_succ_of_le (Finset.le_sup hv_live)
    unfold higherPriority at hprio
    dsimp only [H] at hprio hle
    rcases hprio with hlt | ⟨heq, hult⟩
    · have hmul : ((LubyMIS.liveGraph G s.live).degree v + 1) * M ≤
          (LubyMIS.liveGraph G s.live).degree w * M := Nat.mul_le_mul_right M hlt
      rw [Nat.add_mul, Nat.one_mul] at hmul
      omega
    · rw [heq] at hle
      omega
  -- If `m v = true`, `v` joins `coinJoiners` and `(coinStep G s uid m).live.card < s.live.card`.
  have hshrink : ∀ m : V → Bool, m v = true →
      (coinStep G s uid m).live.card < s.live.card := by
    intro m hmv
    have hvJ : v ∈ coinJoiners G s uid m :=
      (mem_coinJoiners G).2 ⟨hv_live, hmv, fun w hw _ hprio => absurd hprio (hv_top w hw)⟩
    refine Finset.card_lt_card ⟨coinStep_live_subset G s uid m, fun hsub => ?_⟩
    exact ((mem_coinStep_live G).1 (hsub hv_live)).2.1 hvJ
  have hmono :
      ((ProbComp.eval (sampleMarks G s)).toOuterMeasure {m | m v = true}).toReal ≤
        ((ProbComp.eval (coinPhase G uid s)).toOuterMeasure
          {t | t.live.card < s.live.card}).toReal := by
    rw [eval_coinPhase, _root_.PMF.toOuterMeasure_map_apply]
    refine PMF.toOuterMeasure_toReal_mono _ fun m hm => ?_
    exact hshrink m hm
  refine le_trans ?_ hmono
  rw [toOuterMeasure_eq_map_true, eval_sampleMarks, PMF.pi_map_eval, toReal_eval_markCoin_true]
  have hcard_one : (1 : ℝ) ≤ Fintype.card V := by
    have : 1 ≤ Fintype.card V := Fintype.card_pos_iff.2 ⟨v⟩
    exact_mod_cast this
  unfold markProb
  dsimp only
  simp only [hv_live, ↓reduceIte]
  split_ifs with hd0
  · rw [Rat.cast_one]
    exact div_le_one_of_le₀ (by linarith) (by positivity)
  · push_cast
    have hdeg_le : ((LubyMIS.liveGraph G s.live).degree v : ℝ) ≤ Fintype.card V := by
      exact_mod_cast (LubyMIS.liveGraph G s.live).degree_lt_card_verts v |>.le
    have hd_pos : (0 : ℝ) < (LubyMIS.liveGraph G s.live).degree v := by
      exact_mod_cast Nat.pos_of_ne_zero hd0
    exact one_div_le_one_div_of_le (by positivity) (by linarith)

/-! #### Expected edge removal (`≥ |E(H)| / 72`, after `[Wattenhofer2016]` §7.2) -/

/-- Step towards `#7505` and `#3270` (not the cited endpoint, after Lemma 7.7 of
[Wattenhofer][Wattenhofer2016], §7.2, pp. 73–74): every live vertex `v ∈ s.live` with live degree
`d_H(v) ≥ 1` joins `coinJoiners` with probability at least `1 / (4 d_H(v))`. -/
theorem one_div_four_deg_le_prob_coinJoiners {s : LubyMIS.State V} {uid : V → ℕ} {v : V}
    (hv : v ∈ s.live) (hdeg : 1 ≤ (LubyMIS.liveGraph G s.live).degree v) :
    (1 : ℝ) / (4 * (LubyMIS.liveGraph G s.live).degree v) ≤
      ((ProbComp.eval (sampleMarks G s)).toOuterMeasure
        {m | v ∈ coinJoiners G s uid m}).toReal := by
  let H := LubyMIS.liveGraph G s.live
  let p : V → _root_.PMF Bool := fun u =>
    ProbComp.eval (ProbComp.bernoulliRat (markProb G s u))
  set highNbrs : Finset V := (H.neighborFinset v).filter (higherPriority G s uid v)
  let anyHigh : (V → Bool) → Bool := fun m => decide (∃ w ∈ highNbrs, m w = true)
  let quiet : (V → Bool) → Bool := fun m => !anyHigh m
  have hv_not_high : v ∉ highNbrs := by
    intro hmem
    exact H.loopless.irrefl v ((H.mem_neighborFinset v v).1 (Finset.mem_of_mem_filter v hmem))
  have hquiet_upd : ∀ m b, quiet (Function.update m v b) = quiet m := by
    intro m b
    simp only [quiet, anyHigh]
    congr 2
    exact propext (exists_congr fun w => and_congr_right fun hw => by
      have hwv : w ≠ v := fun h => hv_not_high (h ▸ hw)
      rw [Function.update_of_ne hwv])
  -- Equivalence between `v ∈ coinJoiners` and `m v && quiet m = true`.
  have hevent_eq : {m : V → Bool | v ∈ coinJoiners G s uid m} =
      {m : V → Bool | (m v && quiet m) = true} := by
    ext m
    simp only [Set.mem_ofPred_eq, mem_coinJoiners, hv, true_and, Bool.and_eq_true, quiet, anyHigh,
      Bool.not_eq_true', decide_eq_false_iff_not, not_exists, not_and, Bool.not_eq_true]
    refine and_congr_right fun _ => ⟨fun h w hw => ?_, fun h w hwl hadj hprio => ?_⟩
    · obtain ⟨hnbr, hprio⟩ := Finset.mem_filter.1 hw
      have hadj := (H.mem_neighborFinset v w).1 hnbr
      exact h w hadj.2.2 hadj.1 hprio
    · exact h w (Finset.mem_filter.2 ⟨(H.mem_neighborFinset v w).2 ⟨hadj, hv, hwl⟩, hprio⟩)
  rw [hevent_eq, toOuterMeasure_eq_map_true, eval_sampleMarks,
    pi_map_and_true_of_update_eq p v quiet hquiet_upd, ENNReal.toReal_mul]
  -- Compute `(p v true).toReal = 1 / (2 * H.degree v)`.
  have hpv : (p v true).toReal = (1 : ℝ) / (2 * H.degree v) := by
    dsimp only [p]
    rw [toReal_eval_markCoin_true]
    unfold markProb
    dsimp only
    have hne0 : (LubyMIS.liveGraph G s.live).degree v ≠ 0 := by omega
    simp only [hv, hne0, ↓reduceIte]
    push_cast
    rfl
  -- Bound `((PMF.pi p).map anyHigh true).toReal ≤ 1 / 2` by the union bound over `highNbrs`.
  have hany_le : (((PMF.pi p).map anyHigh) true).toReal ≤ 1 / 2 := by
    have hub := PMF.map_true_le_sum (PMF.pi p) highNbrs
      (E := anyHigh) (F := fun w m => m w) (fun m _ hm => by simpa [anyHigh] using hm)
    have hsum_ne_top : (∑ w ∈ highNbrs, ((PMF.pi p).map fun m => m w) true) ≠ ⊤ :=
      ENNReal.sum_ne_top.2 fun w _ => _root_.PMF.apply_ne_top _ _
    have hreal := (ENNReal.toReal_mono hsum_ne_top hub).trans_eq
      (ENNReal.toReal_sum fun w _ => _root_.PMF.apply_ne_top _ _)
    refine hreal.trans ?_
    have hterm : ∀ w ∈ highNbrs,
        (((PMF.pi p).map fun m => m w) true).toReal ≤ (1 : ℝ) / (2 * H.degree v) := by
      intro w hw
      rw [PMF.pi_map_eval]
      dsimp only [p]
      rw [toReal_eval_markCoin_true]
      obtain ⟨hnbr, hprio⟩ := Finset.mem_filter.1 hw
      have hadj : H.Adj v w := (H.mem_neighborFinset v w).1 hnbr
      have hwl : w ∈ s.live := hadj.2.2
      have hdw_ge : H.degree v ≤ H.degree w := degree_le_of_higherPriority G hprio
      have hdw_ne : (LubyMIS.liveGraph G s.live).degree w ≠ 0 := by
        dsimp only [H] at hdw_ge; omega
      unfold markProb
      dsimp only
      simp only [hwl, hdw_ne, ↓reduceIte]
      push_cast
      have hdv_pos : (0 : ℝ) < H.degree v := by exact_mod_cast hdeg
      have hdw_le_r : (H.degree v : ℝ) ≤ H.degree w := by exact_mod_cast hdw_ge
      have h2dv_pos : (0 : ℝ) < 2 * H.degree v := by positivity
      exact one_div_le_one_div_of_le h2dv_pos (by dsimp only [H] at hdw_le_r ⊢; linarith)
    have hcard_le : (highNbrs.card : ℝ) ≤ H.degree v := by
      have hc : highNbrs.card ≤ H.degree v :=
        (Finset.card_filter_le _ _).trans_eq (SimpleGraph.card_neighborFinset_eq_degree H v)
      exact_mod_cast hc
    have hdv_pos : (0 : ℝ) < H.degree v := by exact_mod_cast hdeg
    calc ∑ w ∈ highNbrs, (((PMF.pi p).map fun m => m w) true).toReal
        ≤ ∑ _w ∈ highNbrs, (1 : ℝ) / (2 * H.degree v) := Finset.sum_le_sum hterm
      _ = (highNbrs.card : ℝ) * ((1 : ℝ) / (2 * H.degree v)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (H.degree v : ℝ) * ((1 : ℝ) / (2 * H.degree v)) :=
          mul_le_mul_of_nonneg_right hcard_le (by positivity)
      _ = 1 / 2 := by
          have hne : (H.degree v : ℝ) ≠ 0 := ne_of_gt hdv_pos
          field_simp [hne]
  have hquiet_ge : (1 / 2 : ℝ) ≤ (((PMF.pi p).map quiet) true).toReal := by
    have hcomp : (((PMF.pi p).map quiet) true).toReal +
        (((PMF.pi p).map anyHigh) true).toReal = 1 := by
      have heq_false : ((PMF.pi p).map quiet) true = ((PMF.pi p).map anyHigh) false := by
        rw [_root_.PMF.map_apply, _root_.PMF.map_apply]
        refine tsum_congr fun m => ?_
        dsimp only [quiet]
        by_cases hb : anyHigh m = true <;> simp [hb]
      rw [heq_false, add_comm]
      exact PMF.toReal_true_add_toReal_false _
    linarith
  rw [hpv]
  have hdv_pos : (0 : ℝ) < H.degree v := by exact_mod_cast hdeg
  calc (1 : ℝ) / (4 * H.degree v)
      = ((1 : ℝ) / (2 * H.degree v)) * (1 / 2) := by ring
    _ ≤ ((1 : ℝ) / (2 * H.degree v)) * (((PMF.pi p).map quiet) true).toReal :=
        mul_le_mul_of_nonneg_left hquiet_ge (by positivity)

omit [Fintype V] in
/-- Second-order inclusion–exclusion (Bonferroni) lower bound for finite distributions:
`Pr[∃ u ∈ S, E u] ≥ ∑_{u ∈ S} Pr[E u] - ∑_{u ∈ S} ∑_{w ∈ S.erase u} Pr[E u ∧ E w]`. -/
private theorem bonferroni_toReal {α : Type} [Finite α] (μ : _root_.PMF α) (S : Finset V)
    (E : V → α → Bool) :
    (∑ u ∈ S, ((μ.map (E u)) true).toReal) -
        ∑ u ∈ S, ∑ w ∈ S.erase u, ((μ.map fun a => E u a && E w a) true).toReal ≤
      ((μ.map fun a => decide (∃ u ∈ S, E u a = true)) true).toReal := by
  let _ := Fintype.ofFinite α
  have hind : ∀ B : α → Bool,
      ((μ.map B) true).toReal = ∑ a : α, (μ a).toReal * if B a = true then 1 else 0 := by
    intro B
    rw [← toOuterMeasure_eq_map_true, PMF.toOuterMeasure_toReal_eq_sum_ite]
    simp only [Set.mem_ofPred_eq]
  simp_rw [hind]
  have hswap1 : ∑ u ∈ S, ∑ a : α, (μ a).toReal * (if E u a = true then (1 : ℝ) else 0) =
      ∑ a : α, (μ a).toReal * ∑ u ∈ S, if E u a = true then (1 : ℝ) else 0 := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => (Finset.mul_sum _ _ _).symm
  have hswap2 :
      (∑ u ∈ S, ∑ w ∈ S.erase u,
        ∑ a : α, (μ a).toReal * (if (E u a && E w a) = true then (1 : ℝ) else 0)) =
        ∑ a : α, (μ a).toReal *
          ∑ u ∈ S, ∑ w ∈ S.erase u, if (E u a && E w a) = true then (1 : ℝ) else 0 := by
    calc _ = ∑ u ∈ S, ∑ a : α, (μ a).toReal *
            ∑ w ∈ S.erase u, if (E u a && E w a) = true then (1 : ℝ) else 0 := by
          refine Finset.sum_congr rfl fun u _ => ?_
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun a _ => (Finset.mul_sum _ _ _).symm
      _ = _ := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun a _ => (Finset.mul_sum _ _ _).symm
  rw [hswap1, hswap2, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [← mul_sub]
  refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
  -- Pointwise check in terms of `k = |{u ∈ S | E u a = true}|`.
  set T := S.filter fun u => E u a = true
  have hsum1 : (∑ u ∈ S, if E u a = true then (1 : ℝ) else 0) = T.card := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hsum2 : (∑ u ∈ S, ∑ w ∈ S.erase u, if (E u a && E w a) = true then (1 : ℝ) else 0) =
      (T.card : ℝ) * ((T.card : ℝ) - 1) := by
    have houter :
        (∑ u ∈ S, ∑ w ∈ S.erase u, if (E u a && E w a) = true then (1 : ℝ) else 0) =
          ∑ u ∈ T, ((T.erase u).card : ℝ) := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun u _ => ?_
      by_cases heu : E u a = true
      · rw [ite_eq_left heu]
        have hinner : (∑ w ∈ S.erase u, if (E u a && E w a) = true then (1 : ℝ) else 0) =
            ∑ w ∈ (S.erase u).filter (fun w => E w a = true), (1 : ℝ) := by
          rw [← Finset.sum_filter]
          refine Finset.sum_congr ?_ fun _ _ => rfl
          ext w
          simp [heu]
        rw [hinner, Finset.sum_const, nsmul_eq_mul, mul_one]
        refine congrArg Nat.cast (congrArg Finset.card ?_)
        ext w
        simp [T, Finset.mem_erase, Finset.mem_filter, and_assoc]
      · rw [ite_eq_right heu]
        exact Finset.sum_eq_zero fun w _ => by simp [heu]
    rw [houter]
    rcases T.eq_empty_or_nonempty with hTe | hTne
    · simp [hTe]
    · have hk1 : 1 ≤ T.card := hTne.card_pos
      have hcard_er : ∀ u ∈ T, ((T.erase u).card : ℝ) = (T.card : ℝ) - 1 := by
        intro u hu
        rw [Finset.card_erase_of_mem hu, Nat.cast_sub hk1, Nat.cast_one]
      rw [Finset.sum_congr rfl hcard_er, Finset.sum_const, nsmul_eq_mul]
  rw [hsum1, hsum2]
  rcases T.eq_empty_or_nonempty with hTe | ⟨u₀, hu₀⟩
  · have hno : ¬ ∃ u ∈ S, E u a = true := by
      rintro ⟨u, huS, huE⟩
      have : u ∈ T := Finset.mem_filter.2 ⟨huS, huE⟩
      simp [hTe] at this
    simp [hTe, hno]
  · obtain ⟨huS, huE⟩ := Finset.mem_filter.1 hu₀
    have hex : decide (∃ u ∈ S, E u a = true) = true := decide_eq_true ⟨u₀, huS, huE⟩
    rw [ite_eq_left hex]
    have hk1 : (1 : ℝ) ≤ T.card := by
      have : 1 ≤ T.card := Finset.card_pos.2 ⟨u₀, hu₀⟩
      exact_mod_cast this
    nlinarith [sq_nonneg ((T.card : ℝ) - 1)]

omit [Fintype V] [DecidableEq V] in
private theorem exists_subset_sum_mem_Icc {N : Finset V} {wt : V → ℝ}
    (h0 : ∀ w ∈ N, 0 ≤ wt w) (h6 : ∀ w ∈ N, wt w ≤ 1 / 6)
    (hsum : 1 / 6 ≤ ∑ w ∈ N, wt w) :
    ∃ S ⊆ N, 1 / 6 ≤ ∑ u ∈ S, wt u ∧ ∑ u ∈ S, wt u ≤ 1 / 3 := by
  classical
  induction N using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty] at hsum
    linarith
  | insert a N' ha ih =>
    rw [Finset.sum_insert ha] at hsum
    by_cases hN' : 1 / 6 ≤ ∑ w ∈ N', wt w
    · obtain ⟨S, hSN', hlow, hhigh⟩ := ih
        (fun w hw => h0 w (Finset.mem_insert_of_mem hw))
        (fun w hw => h6 w (Finset.mem_insert_of_mem hw)) hN'
      exact ⟨S, hSN'.trans (Finset.subset_insert a N'), hlow, hhigh⟩
    · refine ⟨insert a N', Subset.rfl, ?_, ?_⟩
      · rw [Finset.sum_insert ha]
        exact hsum
      · rw [Finset.sum_insert ha]
        have ha6 := h6 a (Finset.mem_insert_self a N')
        linarith

/-- A vertex `v` is **good** in state `s` ([Wattenhofer][Wattenhofer2016], §7.2, Lemma 7.8) if
`∑_{w ∈ N_H(v)} 1 / (2 d_H(w)) ≥ 1 / 6`. -/
@[expose] def isGoodVertex (s : LubyMIS.State V) (v : V) : Prop :=
  let H := LubyMIS.liveGraph G s.live
  (1 / 6 : ℝ) ≤ ∑ w ∈ H.neighborFinset v, (1 : ℝ) / (2 * H.degree w)

/-- Step towards `#7505` and `#3270` (not the cited endpoint, after Lemma 7.8 of
[Wattenhofer][Wattenhofer2016], §7.2, pp. 74–75, presenting [Luby][Luby1986]): every good vertex `v`
is removed from the live set (`v ∉ (coinStep G s uid m).live`) in one phase with probability at
least `1 / 36`. -/
theorem one_div_36_le_prob_removed_of_isGoodVertex {s : LubyMIS.State V} {uid : V → ℕ} {v : V}
    (hgood : isGoodVertex G s v) :
    (1 / 36 : ℝ) ≤
      ((ProbComp.eval (sampleMarks G s)).toOuterMeasure
        {m | v ∉ (coinStep G s uid m).live}).toReal := by
  let H := LubyMIS.liveGraph G s.live
  let p : V → _root_.PMF Bool := fun u =>
    ProbComp.eval (ProbComp.bernoulliRat (markProb G s u))
  -- Any neighbor `w ∈ H.neighborFinset v` is live and has `1 ≤ H.degree w`.
  have hnbr_live_deg : ∀ w ∈ H.neighborFinset v, w ∈ s.live ∧ 1 ≤ H.degree w := by
    intro w hw
    have hadj := (H.mem_neighborFinset v w).1 hw
    refine ⟨hadj.2.2, ?_⟩
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    exact Finset.card_pos.2 ⟨v, (H.mem_neighborFinset w v).2 hadj.symm⟩
  -- Split on whether some live neighbor `w` has `H.degree w ≤ 2`.
  by_cases hlow_deg : ∃ w ∈ H.neighborFinset v, H.degree w ≤ 2
  · obtain ⟨w, hw_nbr, hdw2⟩ := hlow_deg
    obtain ⟨hw_live, hdw1⟩ := hnbr_live_deg w hw_nbr
    have hadj_vw : G.Adj v w := ((H.mem_neighborFinset v w).1 hw_nbr).1
    have hjoin_w := one_div_four_deg_le_prob_coinJoiners G (uid := uid) hw_live hdw1
    have hmono :
        ((ProbComp.eval (sampleMarks G s)).toOuterMeasure
          {m | w ∈ coinJoiners G s uid m}).toReal ≤
          ((ProbComp.eval (sampleMarks G s)).toOuterMeasure
            {m | v ∉ (coinStep G s uid m).live}).toReal :=
      PMF.toOuterMeasure_toReal_mono _ fun m hm hvl =>
        ((mem_coinStep_live G).1 hvl).2.2 w hm hadj_vw.symm
    have hdw_r : (H.degree w : ℝ) ≤ 2 := by exact_mod_cast hdw2
    have hdw_pos : (0 : ℝ) < H.degree w := by exact_mod_cast hdw1
    have h18 : (1 / 8 : ℝ) ≤ (1 : ℝ) / (4 * H.degree w) := by
      have h8 : (4 * (H.degree w : ℝ)) ≤ 8 := by linarith
      have hpos8 : (0 : ℝ) < 4 * H.degree w := by positivity
      exact one_div_le_one_div_of_le hpos8 h8
    dsimp only [H] at h18
    linarith
  · push Not at hlow_deg
    let wt : V → ℝ := fun w => (1 : ℝ) / (2 * H.degree w)
    have hwt0 : ∀ w ∈ H.neighborFinset v, 0 ≤ wt w := fun w _ => by
      dsimp only [wt]; positivity
    have hwt6 : ∀ w ∈ H.neighborFinset v, wt w ≤ 1 / 6 := by
      intro w hw
      have hd3 : 3 ≤ H.degree w := hlow_deg w hw
      have hd3_r : (3 : ℝ) ≤ H.degree w := by exact_mod_cast hd3
      dsimp only [wt]
      exact one_div_le_one_div_of_le (by norm_num) (by linarith)
    obtain ⟨S, hSN, hS_low, hS_high⟩ := exists_subset_sum_mem_Icc hwt0 hwt6 hgood
    -- Apply Bonferroni to `E u m := decide (u ∈ coinJoiners G s uid m)` on `S`.
    let E : V → (V → Bool) → Bool := fun u m => decide (u ∈ coinJoiners G s uid m)
    have hbonf := bonferroni_toReal (ProbComp.eval (sampleMarks G s)) S E
    have hsub_rem :
        (((ProbComp.eval (sampleMarks G s)).map
          fun m => decide (∃ u ∈ S, E u m = true)) true).toReal ≤
          ((ProbComp.eval (sampleMarks G s)).toOuterMeasure
            {m | v ∉ (coinStep G s uid m).live}).toReal := by
      rw [← toOuterMeasure_eq_map_true]
      refine PMF.toOuterMeasure_toReal_mono _ fun m hm hvl => ?_
      simp only [Set.mem_ofPred_eq, decide_eq_true_eq] at hm
      obtain ⟨u, huS, huE⟩ := hm
      have huJ : u ∈ coinJoiners G s uid m := of_decide_eq_true huE
      have hadj : G.Adj v u := ((H.mem_neighborFinset v u).1 (hSN huS)).1
      exact ((mem_coinStep_live G).1 hvl).2.2 u huJ hadj.symm
    -- Lower-bound the linear sum `∑_{u ∈ S} Pr[u ∈ coinJoiners] ≥ (1 / 2) ∑_{u ∈ S} wt u`.
    have hlin : (1 / 2 : ℝ) * ∑ u ∈ S, wt u ≤
        ∑ u ∈ S, (((ProbComp.eval (sampleMarks G s)).map (E u)) true).toReal := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun u hu => ?_
      obtain ⟨hul, hud⟩ := hnbr_live_deg u (hSN hu)
      rw [← toOuterMeasure_eq_map_true]
      have hsub_eq :
          {m : V → Bool | E u m = true} = {m : V → Bool | u ∈ coinJoiners G s uid m} := by
        ext m; simp [E]
      rw [hsub_eq]
      have h4 := one_div_four_deg_le_prob_coinJoiners G (uid := uid) hul hud
      have hhalf :
          (1 / 2 : ℝ) * wt u = (1 : ℝ) / (4 * (LubyMIS.liveGraph G s.live).degree u) := by
        dsimp only [wt, H]; ring
      linarith
    -- Upper-bound the quadratic sum by `(∑_{u ∈ S} wt u) ^ 2` via pairwise independence of marks.
    have hquad :
        (∑ u ∈ S, ∑ w ∈ S.erase u,
          (((ProbComp.eval (sampleMarks G s)).map fun m => E u m && E w m) true).toReal) ≤
          (∑ u ∈ S, wt u) ^ 2 := by
      have hpair : ∀ u ∈ S, ∀ w ∈ S.erase u,
          (((ProbComp.eval (sampleMarks G s)).map fun m => E u m && E w m) true).toReal ≤
            wt u * wt w := by
        intro u hu w hw
        have hwu : w ≠ u := (Finset.mem_erase.1 hw).1
        have hmono_mark :
            ((ProbComp.eval (sampleMarks G s)).map fun m => E u m && E w m) true ≤
              ((ProbComp.eval (sampleMarks G s)).map fun m => m u && m w) true := by
          refine PMF.map_true_mono _ fun m _ hm => ?_
          simp only [Bool.and_eq_true, E, decide_eq_true_eq, mem_coinJoiners] at hm ⊢
          exact ⟨hm.1.2.1, hm.2.2.1⟩
        have hreal := ENNReal.toReal_mono (_root_.PMF.apply_ne_top _ _) hmono_mark
        refine hreal.trans_eq ?_
        rw [eval_sampleMarks,
          pi_map_and_true_of_update_eq p u (fun m => m w)
            (fun m b => Function.update_of_ne hwu b m),
          PMF.pi_map_eval, ENNReal.toReal_mul]
        obtain ⟨hul, hud⟩ := hnbr_live_deg u (hSN hu)
        obtain ⟨hwl, hwd⟩ := hnbr_live_deg w (hSN (Finset.mem_of_mem_erase hw))
        have hpu : (p u true).toReal = wt u := by
          dsimp only [p, wt, H]
          rw [toReal_eval_markCoin_true]
          unfold markProb
          dsimp only [H] at hud ⊢
          have hu0 : (LubyMIS.liveGraph G s.live).degree u ≠ 0 := by omega
          simp only [hul, hu0, ↓reduceIte]
          push_cast; rfl
        have hpw : (p w true).toReal = wt w := by
          dsimp only [p, wt, H]
          rw [toReal_eval_markCoin_true]
          unfold markProb
          dsimp only [H] at hwd ⊢
          have hw0 : (LubyMIS.liveGraph G s.live).degree w ≠ 0 := by omega
          simp only [hwl, hw0, ↓reduceIte]
          push_cast; rfl
        rw [hpu, hpw]
      calc (∑ u ∈ S, ∑ w ∈ S.erase u,
              (((ProbComp.eval (sampleMarks G s)).map fun m => E u m && E w m) true).toReal)
          ≤ ∑ u ∈ S, ∑ w ∈ S.erase u, wt u * wt w :=
            Finset.sum_le_sum fun u hu => Finset.sum_le_sum fun w hw => hpair u hu w hw
        _ ≤ ∑ u ∈ S, ∑ w ∈ S, wt u * wt w := by
            refine Finset.sum_le_sum fun u hu => ?_
            exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset u S)
              fun w hw _ => mul_nonneg (hwt0 u (hSN hu)) (hwt0 w (hSN hw))
        _ = (∑ u ∈ S, wt u) ^ 2 := by
            rw [sq, Finset.sum_mul]
            exact Finset.sum_congr rfl fun u _ => (Finset.mul_sum _ _ _).symm
    -- Combine: `(1/2) X - X^2 ≥ 1/36` on `X ∈ [1/6, 1/3]`.
    have halg : (1 / 36 : ℝ) ≤ (1 / 2 : ℝ) * (∑ u ∈ S, wt u) - (∑ u ∈ S, wt u) ^ 2 := by
      nlinarith
    linarith

/-- Directed in-neighbors of `v` under the orientation toward higher `(d_H, uid)` priority. -/
private def inNbrs (s : LubyMIS.State V) (uid : V → ℕ) (L : Finset V) (v : V) : Finset V :=
  ((LubyMIS.liveGraph G L).neighborFinset v).filter fun w => higherPriority G s uid w v

/-- Directed out-neighbors of `v` under the orientation toward higher `(d_H, uid)` priority. -/
private def outNbrs (s : LubyMIS.State V) (uid : V → ℕ) (L : Finset V) (v : V) : Finset V :=
  ((LubyMIS.liveGraph G L).neighborFinset v).filter fun w => higherPriority G s uid v w

private theorem card_inNbrs_add_outNbrs (s : LubyMIS.State V) {uid : V → ℕ}
    (huid : Function.Injective uid) (L : Finset V) (v : V) :
    (inNbrs G s uid L v).card + (outNbrs G s uid L v).card =
      (LubyMIS.liveGraph G L).degree v := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have hdisj : Disjoint (inNbrs G s uid L v) (outNbrs G s uid L v) := by
    refine Finset.disjoint_left.2 fun w hwin hwout => ?_
    exact higherPriority_asymm G (Finset.mem_filter.1 hwin).2 (Finset.mem_filter.1 hwout).2
  have hunion : inNbrs G s uid L v ∪ outNbrs G s uid L v =
      (LubyMIS.liveGraph G L).neighborFinset v := by
    ext w
    simp only [inNbrs, outNbrs, Finset.mem_union, Finset.mem_filter]
    refine ⟨fun h => h.elim And.left And.left, fun hnbr => ?_⟩
    have hadj := ((LubyMIS.liveGraph G L).mem_neighborFinset v w).1 hnbr
    have hne : w ≠ v := fun h => (LubyMIS.liveGraph G L).loopless.irrefl v (h ▸ hadj)
    rcases higherPriority_total G huid hne with hp | hp
    · exact Or.inl ⟨hnbr, hp⟩
    · exact Or.inr ⟨hnbr, hp⟩
  rw [← Finset.card_union_of_disjoint hdisj, hunion]

private theorem sum_card_outNbrs_eq_sum_card_inNbrs (s : LubyMIS.State V) (uid : V → ℕ)
    (L : Finset V) :
    (∑ v : V, (outNbrs G s uid L v).card) = ∑ v : V, (inNbrs G s uid L v).card := by
  have hout : ∀ u : V, (outNbrs G s uid L u).card =
      ∑ w : V, if (LubyMIS.liveGraph G L).Adj u w ∧ higherPriority G s uid u w then 1 else 0 := by
    intro u
    rw [Finset.sum_boole, Nat.cast_id]
    refine congrArg Finset.card ?_
    ext w
    simp [outNbrs, SimpleGraph.mem_neighborFinset]
  have hin : ∀ v : V, (inNbrs G s uid L v).card =
      ∑ u : V, if (LubyMIS.liveGraph G L).Adj v u ∧ higherPriority G s uid u v then 1 else 0 := by
    intro v
    rw [Finset.sum_boole, Nat.cast_id]
    refine congrArg Finset.card ?_
    ext u
    simp [inNbrs, SimpleGraph.mem_neighborFinset]
  simp_rw [hout, hin]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun u _ => ?_
  simp only [(LubyMIS.liveGraph G L).adj_comm u v]

private theorem sum_card_inNbrs_eq_liveEdges (s : LubyMIS.State V) {uid : V → ℕ}
    (huid : Function.Injective uid) (t : LubyMIS.State V) :
    (∑ v : V, (inNbrs G s uid t.live v).card) = LubyMIS.liveEdges G t := by
  have h2 : 2 * ∑ v : V, (inNbrs G s uid t.live v).card = 2 * LubyMIS.liveEdges G t := by
    calc 2 * ∑ v : V, (inNbrs G s uid t.live v).card
        = (∑ v : V, (inNbrs G s uid t.live v).card) +
            ∑ v : V, (outNbrs G s uid t.live v).card := by
          rw [sum_card_outNbrs_eq_sum_card_inNbrs, two_mul]
      _ = ∑ v : V, ((inNbrs G s uid t.live v).card + (outNbrs G s uid t.live v).card) :=
          (Finset.sum_add_distrib).symm
      _ = ∑ v : V, (LubyMIS.liveGraph G t.live).degree v :=
          Finset.sum_congr rfl fun v _ => card_inNbrs_add_outNbrs G s huid t.live v
      _ = 2 * LubyMIS.liveEdges G t := by
          rw [LubyMIS.liveEdges, SimpleGraph.sum_degrees_eq_twice_card_edges]
  omega

/-- Helper step towards `#7505` and `#3270` (after Lemma 7.10 of [Wattenhofer][Wattenhofer2016],
§7.2, p. 75): every vertex `v` that is not good has `2 * indeg(v) ≤ outdeg(v)`. -/
private theorem two_mul_inNbrs_le_outNbrs_of_not_good {s : LubyMIS.State V} {uid : V → ℕ}
    (huid : Function.Injective uid) {v : V} (hbad : ¬ isGoodVertex G s v) :
    2 * (inNbrs G s uid s.live v).card ≤ (outNbrs G s uid s.live v).card := by
  let H := LubyMIS.liveGraph G s.live
  have hpart : (inNbrs G s uid s.live v).card + (outNbrs G s uid s.live v).card = H.degree v :=
    card_inNbrs_add_outNbrs G s huid s.live v
  suffices h3 : 3 * (inNbrs G s uid s.live v).card ≤ H.degree v by omega
  rcases Nat.eq_zero_or_pos (H.degree v) with hd0 | hd_pos
  · omega
  · by_contra hgt
    push Not at hgt
    apply hbad
    unfold isGoodVertex
    have hterm : ∀ w ∈ inNbrs G s uid s.live v,
        (1 : ℝ) / (2 * H.degree v) ≤ (1 : ℝ) / (2 * H.degree w) := by
      intro w hw
      obtain ⟨hnbr, hprio⟩ := Finset.mem_filter.1 hw
      have hadj := (H.mem_neighborFinset v w).1 hnbr
      have hdw_pos : 1 ≤ H.degree w := by
        rw [← SimpleGraph.card_neighborFinset_eq_degree]
        exact Finset.card_pos.2 ⟨v, (H.mem_neighborFinset w v).2 hadj.symm⟩
      have hdw_le : H.degree w ≤ H.degree v := degree_le_of_higherPriority G hprio
      have hdw_pos_r : (0 : ℝ) < H.degree w := by exact_mod_cast hdw_pos
      have hdw_le_r : (H.degree w : ℝ) ≤ H.degree v := by exact_mod_cast hdw_le
      have h2dw_pos : (0 : ℝ) < 2 * H.degree w := by positivity
      exact one_div_le_one_div_of_le h2dw_pos (by linarith)
    have hsub : inNbrs G s uid s.live v ⊆ H.neighborFinset v := Finset.filter_subset _ _
    have hsum_ge :
        ((inNbrs G s uid s.live v).card : ℝ) * ((1 : ℝ) / (2 * H.degree v)) ≤
          ∑ w ∈ H.neighborFinset v, (1 : ℝ) / (2 * H.degree w) := by
      calc ((inNbrs G s uid s.live v).card : ℝ) * ((1 : ℝ) / (2 * H.degree v))
          = ∑ _w ∈ inNbrs G s uid s.live v, (1 : ℝ) / (2 * H.degree v) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ w ∈ inNbrs G s uid s.live v, (1 : ℝ) / (2 * H.degree w) :=
            Finset.sum_le_sum hterm
        _ ≤ ∑ w ∈ H.neighborFinset v, (1 : ℝ) / (2 * H.degree w) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
    have hgt_r : (H.degree v : ℝ) < 3 * (inNbrs G s uid s.live v).card := by exact_mod_cast hgt
    have hdv_pos_r : (0 : ℝ) < H.degree v := by exact_mod_cast hd_pos
    have h16 : (1 / 6 : ℝ) ≤
        ((inNbrs G s uid s.live v).card : ℝ) * ((1 : ℝ) / (2 * H.degree v)) := by
      rw [mul_one_div, le_div_iff₀ (by positivity)]
      linarith
    dsimp only [H] at hsum_ge h16
    linarith

/-- Helper step towards `#7505` and `#3270` (after Lemma 7.9 of [Wattenhofer][Wattenhofer2016],
§7.2, p. 75, and Lemma 4.4 of [Alon, Babai and Itai][AlonBabaiItai1986], p. 572): at least half of
all live edges are directed into good vertices. -/
private theorem liveEdges_le_two_mul_sum_good_inNbrs {s : LubyMIS.State V} {uid : V → ℕ}
    (huid : Function.Injective uid) :
    open scoped Classical in
    LubyMIS.liveEdges G s ≤
      2 * ∑ v ∈ univ.filter (isGoodVertex G s), (inNbrs G s uid s.live v).card := by
  classical
  set goodSet := univ.filter (isGoodVertex G s)
  set badSet := univ.filter (fun v => ¬ isGoodVertex G s v)
  have hsplit : (∑ v : V, (inNbrs G s uid s.live v).card) =
      (∑ v ∈ goodSet, (inNbrs G s uid s.live v).card) +
        ∑ v ∈ badSet, (inNbrs G s uid s.live v).card := by
    simpa only [goodSet, badSet] using
      (Finset.sum_filter_add_sum_filter_not univ (isGoodVertex G s)
        (fun v => (inNbrs G s uid s.live v).card)).symm
  have hbad_le : 2 * ∑ v ∈ badSet, (inNbrs G s uid s.live v).card ≤ LubyMIS.liveEdges G s := by
    calc 2 * ∑ v ∈ badSet, (inNbrs G s uid s.live v).card
        = ∑ v ∈ badSet, 2 * (inNbrs G s uid s.live v).card := Finset.mul_sum _ _ _
      _ ≤ ∑ v ∈ badSet, (outNbrs G s uid s.live v).card :=
          Finset.sum_le_sum fun v hv =>
            two_mul_inNbrs_le_outNbrs_of_not_good G huid (Finset.mem_filter.1 hv).2
      _ ≤ ∑ v : V, (outNbrs G s uid s.live v).card :=
          Finset.sum_le_univ_sum_of_nonneg fun _ => Nat.zero_le _
      _ = LubyMIS.liveEdges G s := by
          rw [sum_card_outNbrs_eq_sum_card_inNbrs, sum_card_inNbrs_eq_liveEdges G s huid s]
  have htot := sum_card_inNbrs_eq_liveEdges G s huid s
  omega

/-- Step towards `#7505` and `#3270` (not the cited endpoint, after Theorem 7.11 of
[Wattenhofer][Wattenhofer2016], §7.2, pp. 75–76, presenting [Luby][Luby1986]): one phase of
degree-weighted coin-flip Luby with injective identifier tie-breaking leaves at most `71 / 72` of
the live edges in expectation (`72 · E[liveEdges'] ≤ 71 · liveEdges`). -/
theorem seventyTwo_mul_expect_liveEdges_coinPhase_le {uid : V → ℕ}
    (huid : Function.Injective uid) (s : LubyMIS.State V) :
    72 * ∑' t, ProbComp.eval (coinPhase G uid s) t * (LubyMIS.liveEdges G t : ℝ≥0∞) ≤
      71 * (LubyMIS.liveEdges G s : ℝ≥0∞) := by
  classical
  -- Prove the contraction in `ℝ` first, then convert to `ℝ≥0∞`.
  have hreal :
      (∑ m : V → Bool,
        (ProbComp.eval (sampleMarks G s) m).toReal *
          (LubyMIS.liveEdges G (coinStep G s uid m) : ℝ)) ≤
        (71 / 72 : ℝ) * LubyMIS.liveEdges G s := by
    -- Express `liveEdges (coinStep ...)` via `inNbrs` and bound vertex-by-vertex.
    have hpt : ∀ m : V → Bool,
        (LubyMIS.liveEdges G (coinStep G s uid m) : ℝ) ≤
          ∑ v : V, if v ∈ (coinStep G s uid m).live then
            ((inNbrs G s uid s.live v).card : ℝ) else 0 := by
      intro m
      rw [← sum_card_inNbrs_eq_liveEdges G s huid (coinStep G s uid m), Nat.cast_sum]
      refine Finset.sum_le_sum fun v _ => ?_
      by_cases hvl : v ∈ (coinStep G s uid m).live
      · rw [ite_eq_left hvl]
        have hsub : inNbrs G s uid (coinStep G s uid m).live v ⊆ inNbrs G s uid s.live v := by
          intro w hw
          obtain ⟨hnbr, hp⟩ := Finset.mem_filter.1 hw
          have hadj := ((LubyMIS.liveGraph G _).mem_neighborFinset v w).1 hnbr
          refine Finset.mem_filter.2 ⟨((LubyMIS.liveGraph G s.live).mem_neighborFinset v w).2
            ⟨hadj.1, coinStep_live_subset G s uid m hadj.2.1,
              coinStep_live_subset G s uid m hadj.2.2⟩, hp⟩
        exact_mod_cast Finset.card_le_card hsub
      · rw [ite_eq_right hvl]
        have hempty : inNbrs G s uid (coinStep G s uid m).live v = ∅ := by
          rw [Finset.eq_empty_iff_forall_notMem]
          intro w hw
          have hnbr := (Finset.mem_filter.1 hw).1
          exact hvl (((LubyMIS.liveGraph G _).mem_neighborFinset v w).1 hnbr).2.1
        simp [hempty]
    have hstep1 :
        (∑ m : V → Bool,
          (ProbComp.eval (sampleMarks G s) m).toReal *
            (LubyMIS.liveEdges G (coinStep G s uid m) : ℝ)) ≤
          ∑ v : V, ((inNbrs G s uid s.live v).card : ℝ) *
            ((ProbComp.eval (sampleMarks G s)).toOuterMeasure
              {m | v ∈ (coinStep G s uid m).live}).toReal := by
      calc _ ≤ ∑ m : V → Bool, (ProbComp.eval (sampleMarks G s) m).toReal *
                ∑ v : V, if v ∈ (coinStep G s uid m).live then
                  ((inNbrs G s uid s.live v).card : ℝ) else 0 :=
            Finset.sum_le_sum fun m _ =>
              mul_le_mul_of_nonneg_left (hpt m) ENNReal.toReal_nonneg
        _ = ∑ v : V, ∑ m : V → Bool, (ProbComp.eval (sampleMarks G s) m).toReal *
              (if v ∈ (coinStep G s uid m).live then
                ((inNbrs G s uid s.live v).card : ℝ) else 0) := by
            simp_rw [Finset.mul_sum]
            exact Finset.sum_comm
        _ = ∑ v : V, ((inNbrs G s uid s.live v).card : ℝ) *
              ((ProbComp.eval (sampleMarks G s)).toOuterMeasure
                {m | v ∈ (coinStep G s uid m).live}).toReal := by
            refine Finset.sum_congr rfl fun v _ => ?_
            rw [PMF.toOuterMeasure_toReal_eq_sum_ite, Finset.mul_sum]
            refine Finset.sum_congr rfl fun m _ => ?_
            by_cases hm_in : v ∈ (coinStep G s uid m).live
            · simp only [Set.mem_ofPred_eq, hm_in, ↓reduceIte, mul_one]
              ring
            · simp only [Set.mem_ofPred_eq, hm_in, ↓reduceIte, mul_zero]
    refine hstep1.trans ?_
    -- Split `V` into `goodSet` (survival `≤ 35 / 36`) and `badSet` (survival `≤ 1`).
    set goodSet := univ.filter (isGoodVertex G s)
    set badSet := univ.filter (fun v => ¬ isGoodVertex G s v)
    have hsplit_exp :
        (∑ v : V, ((inNbrs G s uid s.live v).card : ℝ) *
          ((ProbComp.eval (sampleMarks G s)).toOuterMeasure
            {m | v ∈ (coinStep G s uid m).live}).toReal) =
        (∑ v ∈ goodSet, ((inNbrs G s uid s.live v).card : ℝ) *
          ((ProbComp.eval (sampleMarks G s)).toOuterMeasure
            {m | v ∈ (coinStep G s uid m).live}).toReal) +
        (∑ v ∈ badSet, ((inNbrs G s uid s.live v).card : ℝ) *
          ((ProbComp.eval (sampleMarks G s)).toOuterMeasure
            {m | v ∈ (coinStep G s uid m).live}).toReal) := by
      simpa only [goodSet, badSet] using
        (Finset.sum_filter_add_sum_filter_not univ (isGoodVertex G s) _).symm
    have hgood_bound :
        (∑ v ∈ goodSet, ((inNbrs G s uid s.live v).card : ℝ) *
          ((ProbComp.eval (sampleMarks G s)).toOuterMeasure
            {m | v ∈ (coinStep G s uid m).live}).toReal) ≤
          (35 / 36 : ℝ) * ∑ v ∈ goodSet, ((inNbrs G s uid s.live v).card : ℝ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun v hv => ?_
      have hg : isGoodVertex G s v := (Finset.mem_filter.1 hv).2
      have hrem := one_div_36_le_prob_removed_of_isGoodVertex G (uid := uid) hg
      have hcomp := PMF.toOuterMeasure_toReal_add_compl
        (ProbComp.eval (sampleMarks G s)) {m | v ∈ (coinStep G s uid m).live}
      have hcompl_eq : ({m : V → Bool | v ∈ (coinStep G s uid m).live})ᶜ =
          {m : V → Bool | v ∉ (coinStep G s uid m).live} := rfl
      rw [hcompl_eq] at hcomp
      have hsurv : ((ProbComp.eval (sampleMarks G s)).toOuterMeasure
          {m | v ∈ (coinStep G s uid m).live}).toReal ≤ 35 / 36 := by linarith
      calc ((inNbrs G s uid s.live v).card : ℝ) *
            ((ProbComp.eval (sampleMarks G s)).toOuterMeasure
              {m | v ∈ (coinStep G s uid m).live}).toReal
          ≤ ((inNbrs G s uid s.live v).card : ℝ) * (35 / 36) :=
            mul_le_mul_of_nonneg_left hsurv (Nat.cast_nonneg _)
        _ = (35 / 36 : ℝ) * (inNbrs G s uid s.live v).card := mul_comm _ _
    have hbad_bound :
        (∑ v ∈ badSet, ((inNbrs G s uid s.live v).card : ℝ) *
          ((ProbComp.eval (sampleMarks G s)).toOuterMeasure
            {m | v ∈ (coinStep G s uid m).live}).toReal) ≤
          ∑ v ∈ badSet, ((inNbrs G s uid s.live v).card : ℝ) := by
      refine Finset.sum_le_sum fun v _ => ?_
      calc ((inNbrs G s uid s.live v).card : ℝ) *
            ((ProbComp.eval (sampleMarks G s)).toOuterMeasure
              {m | v ∈ (coinStep G s uid m).live}).toReal
          ≤ ((inNbrs G s uid s.live v).card : ℝ) * 1 :=
            mul_le_mul_of_nonneg_left (PMF.toOuterMeasure_toReal_le_one _ _) (Nat.cast_nonneg _)
        _ = (inNbrs G s uid s.live v).card := mul_one _
    have htot_split :
        (∑ v ∈ goodSet, ((inNbrs G s uid s.live v).card : ℝ)) +
          ∑ v ∈ badSet, ((inNbrs G s uid s.live v).card : ℝ) = LubyMIS.liveEdges G s := by
      rw [← Nat.cast_sum, ← Nat.cast_sum, ← Nat.cast_add]
      have h := Finset.sum_filter_add_sum_filter_not univ (isGoodVertex G s)
        (fun v => (inNbrs G s uid s.live v).card)
      simpa only [goodSet, badSet, sum_card_inNbrs_eq_liveEdges G s huid s] using
        congrArg (Nat.cast (R := ℝ)) h
    have hhalf_good :
        (LubyMIS.liveEdges G s : ℝ) ≤
          2 * ∑ v ∈ goodSet, ((inNbrs G s uid s.live v).card : ℝ) := by
      have hnat := liveEdges_le_two_mul_sum_good_inNbrs G (s := s) huid
      exact_mod_cast hnat
    linarith
  -- Transfer the finite expectation inequality from `ℝ` to `ℝ≥0∞`.
  rw [eval_coinPhase, PMF.tsum_map_mul, tsum_fintype]
  have hne_top :
      (72 * ∑ m : V → Bool,
        ProbComp.eval (sampleMarks G s) m *
          (LubyMIS.liveEdges G (coinStep G s uid m) : ℝ≥0∞)) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofNat_ne_top
      (ENNReal.sum_ne_top.2 fun m _ =>
        ENNReal.mul_ne_top (_root_.PMF.apply_ne_top _ _) (ENNReal.natCast_ne_top _))
  have hrhs_ne_top : (71 * (LubyMIS.liveEdges G s : ℝ≥0∞)) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofNat_ne_top (ENNReal.natCast_ne_top _)
  rw [← ENNReal.toReal_le_toReal hne_top hrhs_ne_top]
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofNat, ENNReal.toReal_mul, ENNReal.toReal_ofNat,
    ENNReal.toReal_natCast,
    ENNReal.toReal_sum fun m _ =>
      ENNReal.mul_ne_top (_root_.PMF.apply_ne_top _ _) (ENNReal.natCast_ne_top _)]
  have hsum_cast :
      (∑ x : V → Bool,
        (ProbComp.eval (sampleMarks G s) x *
          (LubyMIS.liveEdges G (coinStep G s uid x) : ℝ≥0∞)).toReal) =
      ∑ x : V → Bool,
        (ProbComp.eval (sampleMarks G s) x).toReal *
          (LubyMIS.liveEdges G (coinStep G s uid x) : ℝ) := by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_natCast]
  rw [hsum_cast]
  linarith

/-! #### Multi-phase geometric contraction and `O(log n)`-phase w.h.p. `MIS` convergence -/

theorem coinRun_zero (uid : V → ℕ) :
    coinRun G uid 0 = pure (LubyMIS.init : LubyMIS.State V) := by
  simp only [coinRun, OracleComp.iterate_zero]

theorem coinRun_succ (uid : V → ℕ) (k : ℕ) :
    coinRun G uid (k + 1) = coinRun G uid k >>= coinPhase G uid := by
  simp only [coinRun, OracleComp.iterate_succ]

/-- Step towards `#7505` and `#3270` (not the cited endpoint, after Theorem 7.11 of
[Wattenhofer][Wattenhofer2016], §7.2, pp. 75–76, presenting [Luby][Luby1986]): after `k` phases of
`coinRun`, `(72 ^ k) · E[liveEdges_k] ≤ (71 ^ k) · |E(G)|`. -/
theorem seventyTwo_pow_mul_expect_liveEdges_coinRun_le {uid : V → ℕ}
    (huid : Function.Injective uid) (k : ℕ) :
    (72 : ℝ≥0∞) ^ k * ∑' t, ProbComp.eval (coinRun G uid k) t * (LubyMIS.liveEdges G t : ℝ≥0∞) ≤
      (71 : ℝ≥0∞) ^ k * G.edgeFinset.card := by
  induction k with
  | zero =>
    rw [pow_zero, pow_zero, one_mul, one_mul, coinRun_zero, ProbComp.eval_pure,
      tsum_eq_single LubyMIS.init
        (fun t ht => by rw [_root_.PMF.pure_apply, ite_eq_right ht, zero_mul]),
      _root_.PMF.pure_apply, ite_eq_left rfl, one_mul, LubyMIS.liveEdges_init]
  | succ k ih =>
    rw [coinRun_succ, ProbComp.eval_bind, PMF.tsum_bind_mul]
    calc (72 : ℝ≥0∞) ^ (k + 1) * ∑' a, ProbComp.eval (coinRun G uid k) a *
          ∑' t, ProbComp.eval (coinPhase G uid a) t * (LubyMIS.liveEdges G t : ℝ≥0∞)
        = (72 : ℝ≥0∞) ^ k * ∑' a, ProbComp.eval (coinRun G uid k) a *
          (72 * ∑' t, ProbComp.eval (coinPhase G uid a) t * (LubyMIS.liveEdges G t : ℝ≥0∞)) := by
          rw [pow_succ, mul_assoc, ← ENNReal.tsum_mul_left]
          congr 1
          refine tsum_congr fun a => ?_
          ring
      _ ≤ (72 : ℝ≥0∞) ^ k * ∑' a, ProbComp.eval (coinRun G uid k) a *
            (71 * (LubyMIS.liveEdges G a : ℝ≥0∞)) := by
          refine mul_le_mul_right ?_ _
          exact tsum_le_tsum fun a =>
            mul_le_mul_right (seventyTwo_mul_expect_liveEdges_coinPhase_le G huid a) _
      _ = 71 * ((72 : ℝ≥0∞) ^ k * ∑' a, ProbComp.eval (coinRun G uid k) a *
            (LubyMIS.liveEdges G a : ℝ≥0∞)) := by
          rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
          refine tsum_congr fun a => ?_
          ring
      _ ≤ 71 * ((71 : ℝ≥0∞) ^ k * G.edgeFinset.card) := mul_le_mul_right ih 71
      _ = (71 : ℝ≥0∞) ^ (k + 1) * G.edgeFinset.card := by
          rw [pow_succ', mul_assoc]

/-- When no live edges remain (`liveEdges G s = 0`), every live vertex has live degree `0`, marks
itself with probability `1` on every outcome in the support of `sampleMarks G s`, joins
`coinJoiners`, and leaves `(coinStep G s uid m).live = ∅`. -/
private theorem live_coinStep_eq_empty_of_liveEdges_eq_zero {s : LubyMIS.State V}
    (h0 : LubyMIS.liveEdges G s = 0) (uid : V → ℕ) {m : V → Bool}
    (hm : m ∈ (ProbComp.eval (sampleMarks G s)).support) :
    (coinStep G s uid m).live = ∅ := by
  have hedge_empty : (LubyMIS.liveGraph G s.live).edgeFinset = ∅ :=
    Finset.card_eq_zero.1 h0
  have hno_adj : ∀ u ∈ s.live, ∀ w ∈ s.live, ¬ G.Adj u w := by
    intro u hu w hw hadj
    have hmem : s(u, w) ∈ (LubyMIS.liveGraph G s.live).edgeFinset :=
      (SimpleGraph.mem_edgeFinset).2 ⟨hadj, hu, hw⟩
    rw [hedge_empty] at hmem
    exact Finset.notMem_empty _ hmem
  have hdeg0 : ∀ v ∈ s.live, (LubyMIS.liveGraph G s.live).degree v = 0 := by
    intro v hv
    rw [← SimpleGraph.card_neighborFinset_eq_degree, Finset.card_eq_zero,
      Finset.eq_empty_iff_forall_notMem]
    intro w hw
    have hadj := ((LubyMIS.liveGraph G s.live).mem_neighborFinset v w).1 hw
    exact hno_adj v hv w hadj.2.2 hadj.1
  -- Every live vertex `v` has `markProb G s v = 1`, hence `m v = true`.
  have hmv_true : ∀ v ∈ s.live, m v = true := by
    intro v hv
    rw [eval_sampleMarks] at hm
    have hv_supp := (PMF.mem_support_pi_iff _ _).1 hm v
    have hprob1 : markProb G s v = 1 := by
      unfold markProb
      simp [hv, hdeg0 v hv]
    rw [hprob1] at hv_supp
    by_contra hfalse
    have hmf : m v = false := Bool.eq_false_iff.2 hfalse
    rw [hmf] at hv_supp
    have h1 : (ProbComp.eval (ProbComp.bernoulliRat 1) true).toReal = 1 := by
      simpa using ProbComp.toReal_eval_bernoulliRat_true_of_mem_Icc
        (zero_le_one : (0 : ℚ) ≤ 1) le_rfl
    have hsum := PMF.toReal_true_add_toReal_false (ProbComp.eval (ProbComp.bernoulliRat 1))
    have h0_real : (ProbComp.eval (ProbComp.bernoulliRat 1) false).toReal = 0 := by linarith
    have hne0 := (_root_.PMF.mem_support_iff _ _).1 hv_supp
    have hpos := ENNReal.toReal_pos hne0 (_root_.PMF.apply_ne_top _ _)
    linarith
  refine Finset.eq_empty_iff_forall_notMem.2 fun v hv => ?_
  obtain ⟨hL, hnotJ, -⟩ := (mem_coinStep_live G).1 hv
  exact hnotJ ((mem_coinJoiners G).2
    ⟨hL, hmv_true v hL, fun w hw hadj _ => absurd hadj (hno_adj v hL w hw)⟩)

/-- Step towards `#7505` and `#3270` (not the cited endpoint, after Theorem 7.11 of
[Wattenhofer][Wattenhofer2016], §7.2, pp. 75–76, presenting [Luby][Luby1986]): after `k + 1` phases
of `coinRun`, some vertex remains live with probability at most `(71 / 72) ^ k · |E(G)|`. -/
theorem seventyTwo_pow_mul_toOuterMeasure_live_nonempty_coinRun_le {uid : V → ℕ}
    (huid : Function.Injective uid) (k : ℕ) :
    (72 : ℝ≥0∞) ^ k *
        (ProbComp.eval (coinRun G uid (k + 1))).toOuterMeasure {s | s.live.Nonempty} ≤
      (71 : ℝ≥0∞) ^ k * G.edgeFinset.card := by
  refine le_trans ?_ (seventyTwo_pow_mul_expect_liveEdges_coinRun_le G huid k)
  rw [coinRun_succ, ProbComp.eval_bind, _root_.PMF.toOuterMeasure_bind_apply]
  gcongr with a
  rcases Nat.eq_zero_or_pos (LubyMIS.liveEdges G a) with h0 | hpos
  · rw [h0, Nat.cast_zero, eval_coinPhase, _root_.PMF.toOuterMeasure_map_apply]
    refine le_of_eq ((_root_.PMF.toOuterMeasure_apply_eq_zero_iff _ _).2 ?_)
    refine Set.disjoint_left.2 fun m hsupp hpre => ?_
    simp only [Set.mem_preimage, Set.mem_ofPred_eq,
      live_coinStep_eq_empty_of_liveEdges_eq_zero G h0 uid hsupp,
      Finset.not_nonempty_empty] at hpre
  · exact (PMF.toOuterMeasure_le_one _ _).trans (Nat.one_le_cast.2 hpos)

private theorem two_mul_71_pow_50_le_72_pow_50 : 2 * 71 ^ 50 ≤ 72 ^ 50 := by decide

/-- Step towards `#7505` and `#3270` (not the cited endpoint, after Theorem 7.11 of
[Wattenhofer][Wattenhofer2016], §7.2, pp. 75–76, presenting [Luby][Luby1986]): since
`2 · 71 ^ 50 ≤ 72 ^ 50`, every `50` phases at least halve the expected live edges; after
`50 * (c + 2) * ⌈log₂ |V|⌉ + 1` phases, `coinLubyMIS` fails to output a maximal independent set
with probability at most `|V| ^ (-c)`. -/
theorem toOuterMeasure_not_maximal_coinLubyMIS_le_inv_pow {uid : V → ℕ}
    (huid : Function.Injective uid) (c : ℕ) :
    (ProbComp.eval
        (coinLubyMIS G uid (50 * (c + 2) * Nat.clog 2 (Fintype.card V) + 1))).toOuterMeasure
        {S | ¬ Maximal G.IsIndepSet (S : Set V)} ≤ ((Fintype.card V : ℝ≥0∞) ^ c)⁻¹ := by
  set M := (c + 2) * Nat.clog 2 (Fintype.card V)
  have hk_eq : 50 * (c + 2) * Nat.clog 2 (Fintype.card V) = 50 * M := by ring
  rw [hk_eq, coinLubyMIS, ProbComp.eval_map, _root_.PMF.toOuterMeasure_map_apply]
  have hsub :
      (LubyMIS.State.chosen ⁻¹' {S : Finset V | ¬ Maximal G.IsIndepSet (S : Set V)}) ∩
        (ProbComp.eval (coinRun G uid (50 * M + 1))).support ⊆ {s | s.live.Nonempty} := by
    rintro s ⟨hs, hsupp⟩
    simp only [Set.mem_preimage, Set.mem_ofPred_eq,
      (invariant_of_mem_support_coinRun G huid hsupp).maximal_iff] at hs ⊢
    exact nonempty_iff_ne_empty.2 hs
  refine (_root_.PMF.toOuterMeasure_mono _ hsub).trans ?_
  have hmarkov := seventyTwo_pow_mul_toOuterMeasure_live_nonempty_coinRun_le G huid (50 * M)
  -- Compare `(71 ^ 50) ^ M` vs `(72 ^ 50) ^ M` via `2 * 71 ^ 50 ≤ 72 ^ 50`.
  have hpow_nat : 2 ^ M * 71 ^ (50 * M) ≤ 72 ^ (50 * M) := by
    calc 2 ^ M * 71 ^ (50 * M)
        = (2 * 71 ^ 50) ^ M := by rw [mul_pow, ← pow_mul]
      _ ≤ (72 ^ 50) ^ M := Nat.pow_le_pow_left two_mul_71_pow_50_le_72_pow_50 M
      _ = 72 ^ (50 * M) := (pow_mul 72 50 M).symm
  have hpow_enn : (2 : ℝ≥0∞) ^ M * (71 : ℝ≥0∞) ^ (50 * M) ≤ (72 : ℝ≥0∞) ^ (50 * M) := by
    exact_mod_cast hpow_nat
  have hedges : (G.edgeFinset.card : ℝ≥0∞) ≤ (2 : ℝ≥0∞) ^ (2 * Nat.clog 2 (Fintype.card V)) := by
    have hnat : G.edgeFinset.card ≤ 2 ^ (2 * Nat.clog 2 (Fintype.card V)) :=
      calc G.edgeFinset.card ≤ (Fintype.card V).choose 2 := G.card_edgeFinset_le_card_choose_two
        _ ≤ Fintype.card V ^ 2 := Nat.choose_le_pow _ _
        _ ≤ (2 ^ Nat.clog 2 (Fintype.card V)) ^ 2 :=
            Nat.pow_le_pow_left (Nat.le_pow_clog one_lt_two _) 2
        _ = 2 ^ (2 * Nat.clog 2 (Fintype.card V)) := by rw [← pow_mul, mul_comm]
    exact_mod_cast hnat
  set P := (ProbComp.eval (coinRun G uid (50 * M + 1))).toOuterMeasure {s | s.live.Nonempty}
  have h71_pos : (71 : ℝ≥0∞) ^ (50 * M) ≠ 0 := pow_ne_zero _ (by norm_num)
  have h71_top : (71 : ℝ≥0∞) ^ (50 * M) ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top
  -- Multiply `hmarkov` and cancel `(71 : ℝ≥0∞) ^ (50 * M)`.
  have h2P : (2 : ℝ≥0∞) ^ M * P ≤ G.edgeFinset.card := by
    have hmul : ((2 : ℝ≥0∞) ^ M * P) * (71 : ℝ≥0∞) ^ (50 * M) ≤
        (G.edgeFinset.card : ℝ≥0∞) * (71 : ℝ≥0∞) ^ (50 * M) := by
      calc ((2 : ℝ≥0∞) ^ M * P) * (71 : ℝ≥0∞) ^ (50 * M)
          = ((2 : ℝ≥0∞) ^ M * (71 : ℝ≥0∞) ^ (50 * M)) * P := by ring
        _ ≤ (72 : ℝ≥0∞) ^ (50 * M) * P := mul_le_mul_left hpow_enn P
        _ ≤ (71 : ℝ≥0∞) ^ (50 * M) * G.edgeFinset.card := hmarkov
        _ = (G.edgeFinset.card : ℝ≥0∞) * (71 : ℝ≥0∞) ^ (50 * M) := mul_comm _ _
    exact (ENNReal.mul_le_mul_iff_left h71_pos h71_top).1 hmul
  -- Split `M = 2 * clog + c * clog`.
  have hM_split : M = 2 * Nat.clog 2 (Fintype.card V) + c * Nat.clog 2 (Fintype.card V) := by
    dsimp only [M]; ring
  have h2c_pos : (2 : ℝ≥0∞) ^ (2 * Nat.clog 2 (Fintype.card V)) ≠ 0 :=
    pow_ne_zero _ two_ne_zero
  have h2c_top : (2 : ℝ≥0∞) ^ (2 * Nat.clog 2 (Fintype.card V)) ≠ ⊤ :=
    ENNReal.pow_ne_top ENNReal.ofNat_ne_top
  have hP_le_2 : P ≤ ((2 : ℝ≥0∞) ^ (c * Nat.clog 2 (Fintype.card V)))⁻¹ := by
    have hle1 : (2 : ℝ≥0∞) ^ (c * Nat.clog 2 (Fintype.card V)) * P ≤ 1 := by
      have hmul2 :
          ((2 : ℝ≥0∞) ^ (c * Nat.clog 2 (Fintype.card V)) * P) *
            (2 : ℝ≥0∞) ^ (2 * Nat.clog 2 (Fintype.card V)) ≤
          1 * (2 : ℝ≥0∞) ^ (2 * Nat.clog 2 (Fintype.card V)) := by
        calc ((2 : ℝ≥0∞) ^ (c * Nat.clog 2 (Fintype.card V)) * P) *
              (2 : ℝ≥0∞) ^ (2 * Nat.clog 2 (Fintype.card V))
            = (2 : ℝ≥0∞) ^ M * P := by
              rw [hM_split, pow_add]
              ring
          _ ≤ G.edgeFinset.card := h2P
          _ ≤ 1 * (2 : ℝ≥0∞) ^ (2 * Nat.clog 2 (Fintype.card V)) := by
              rw [one_mul]; exact hedges
      exact (ENNReal.mul_le_mul_iff_left h2c_pos h2c_top).1 hmul2
    have h2cc_pos : (2 : ℝ≥0∞) ^ (c * Nat.clog 2 (Fintype.card V)) ≠ 0 :=
      pow_ne_zero _ two_ne_zero
    have h2cc_top : (2 : ℝ≥0∞) ^ (c * Nat.clog 2 (Fintype.card V)) ≠ ⊤ :=
      ENNReal.pow_ne_top ENNReal.ofNat_ne_top
    rw [mul_comm, ← ENNReal.le_div_iff_mul_le (Or.inl h2cc_pos) (Or.inl h2cc_top),
      ENNReal.div_eq_inv_mul, mul_one] at hle1
    exact hle1
  refine hP_le_2.trans (ENNReal.inv_le_inv.2 ?_)
  rw [mul_comm, pow_mul]
  gcongr
  exact_mod_cast Nat.le_pow_clog one_lt_two _

/-- Step towards `#7505` and `#3270` (not the cited endpoint, after Theorem 7.11 of
[Wattenhofer][Wattenhofer2016], §7.2, pp. 75–76, presenting [Luby][Luby1986]): after
`50 * (c + 2) * ⌈log₂ |V|⌉ + 1` synchronous `3`-round `LOCAL` phases
(`3 * (50 * (c + 2) * ⌈log₂ |V|⌉ + 1)` communication rounds), `localCoinLubyMIS` fails to output a
maximal independent set with probability at most `|V| ^ (-c)`. -/
theorem toOuterMeasure_not_maximal_localCoinLubyMIS_le_inv_pow {uid : V → ℕ}
    (huid : Function.Injective uid) (c : ℕ) :
    (ProbComp.eval
        (localCoinLubyMIS G uid (50 * (c + 2) * Nat.clog 2 (Fintype.card V) + 1))).toOuterMeasure
        {S | ¬ Maximal G.IsIndepSet (S : Set V)} ≤ ((Fintype.card V : ℝ≥0∞) ^ c)⁻¹ := by
  rw [eval_localCoinLubyMIS]
  exact toOuterMeasure_not_maximal_coinLubyMIS_le_inv_pow G huid c

end VariantB

end Cslib.Distributed.LocalGraph
