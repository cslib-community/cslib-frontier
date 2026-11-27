/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/
module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Languages.Probabilistic.Notation
public import CslibFrontier.Languages.Probabilistic.Semantics
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Languages.Probabilistic.RandomPermutation.ExtPermsCard
import CslibFrontier.Probability.PMF.UniformSubset
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Fintype.Perm
import Mathlib.Logic.Equiv.List
import Mathlib.Probability.ProbabilityMassFunction.Monad
import CslibFrontier.Tactic.FinIndex

/-! # Wang–Ren Relocation Data Structure for Client-Preprocessing PIR

This file formalizes the relocation data structure of [Wang and Ren][WangRen2025]
(ePrint 2024/1845, version of 2024-11-10, Section 3, pp. 12–17), which forms the core state-update
primitive in their single-server client-preprocessing PIR scheme (see
`CslibFrontier.Crypto.Protocols.PIR.Preprocessing.Basic` and
`CslibFrontier.Crypto.Protocols.PIR.Preprocessing.Piano` for the surrounding preprocessing PIR
hierarchy).

Given $m$ logical elements placed into $m' \ge m$ physical positions using a permutation
$\pi : \text{Fin } m' \simeq \text{Fin } m'$ and a history $C$ of relocated physical positions
([WangRen2025], Constructions 3.4 and 3.5, p. 14), the data structure maintains a directed
relocation graph ([WangRen2025], Definition 3.6, p. 15) supporting:
* `access s c`: returns the logical element (if any) currently stored at physical position $c$,
  by walking backward along `inEdge?` to the start of the chain.
* `locate s e hm`: returns the current physical position of logical element $e \in \text{Fin } m$,
  by walking forward along `outEdge?` to the end of the chain starting at $\pi(e)$.
* `relocate s c`: appends $c$ to the relocation history $C$, adding a directed edge from $c$ to
  $\pi(m + |C|)$.

## Main definitions and results

* `RelocationState`, `init`, `inEdge?`, `outEdge?`, `startOfChain`, `endOfChain`, `access`,
  `locate`, `relocate`: Construction 3.5 ([WangRen2025], p. 14).
* `hasEdge`, `inEdge?_perm_castLE_eq_none`, `outEdge?_eq_none_iff_not_mem`,
  `outEdge?_eq_some_iff_inEdge?_eq_some`, `outEdge?_walk_eq_none`, `inEdge?_walk_eq_none`,
  `startOfChain_endOfChain`, `endOfChain_startOfChain`, `access_eq_some_iff`: graph structure of
  relocation chains ([WangRen2025], Definition 3.6, Facts 3.7–3.8, Lemma 3.9, Corollary 3.10,
  Facts 3.11–3.12, p. 15).
* `existsUnique_access_eq` ([WangRen2025], Lemma 3.13, p. 15): for every valid state $s$ and
  element $e \in \text{Fin } m$, there is a unique unconsumed position $c \notin C$ with
  `access s c = some e`.
* `access_eq_some_iff_locate_eq`, `access_locate`, `locate_injective` ([WangRen2025],
  Lemma 3.14, p. 15): `locate` and `access` are mutually inverse on unconsumed positions.
* `locate_relocate_of_ne`, `locate_relocate_self_eq`, `locate_relocate`,
  `relocate_destination_empty` ([WangRen2025], Lemma 3.15, p. 16): relocating $c \notin C$ leaves
  the positions of all elements not at $c$ unchanged, and moves any element at $c$ to an
  unconsumed position that was empty prior to the relocation.
* `realExperiment`, `idealExperiment`, `eval_realExperiment_eq_idealExperiment`
  ([WangRen2025], Experiments 3.1 and 3.2, p. 13; Lemma 3.16, pp. 16–17): when $\pi$ is sampled
  uniformly at random, for any sequence of $Q \le m' - m$ distinct relocated positions fixed in
  advance, the real and ideal relocation experiments have identical output distributions.

Together, Lemmas 3.13–3.16 above are the correctness and perfect-security part of [WangRen2025]
Theorem 3.3 (p. 13) for Construction 3.5 with an ideal uniformly random permutation and fixed
relocation positions. This is not Theorem 3.3 in full: its efficiency bullets are not formalized.

## Modelling notes

* **Explicit fuel and history representation:** Construction 3.4's hash map is an implementation
  device for $O(1)$ expected-time lookup of the relocation history $C$; we represent $C$ directly
  as `history : List (Fin m')` (oldest first) and bound `startOfChain` / `endOfChain` by
  `s.history.length + 1` steps, proving in `outEdge?_walk_eq_none` and `inEdge?_walk_eq_none`
  that every chain terminates within `s.history.length` steps.
* **0-indexed history:** We follow Definition 3.6 (p. 15) in 0-indexing $C$: the $t$-th relocation
  (for $0 \le t < |C|$) adds the directed edge $C[t] \to \pi(m + t)$. The proof of Lemma 3.16
  (p. 16) counts relocations from 1 ("in the first t relocations, only P(0), P(1), ...,
  P(m + t − 1) are accessed") and then treats $P(m + t)$ as the fresh node of the $t$-th
  relocation; with the 0-indexed history of Definition 3.6 that node is $P(m + t - 1)$. The
  off-by-one does not affect the argument.
* **Experiment 3.1 output typo:** The pseudocode of Experiment 3.1 ([WangRen2025], p. 13) reads
  "Output (DS.Access(0), DS.Access(1), . . . , DS.Access(m − 1))." That tuple lists the elements
  at positions $0, \ldots, m - 1$, not the positions of the elements. Experiment 3.2 (p. 13)
  reads "Output the position of each element in \[m\] in A.", and the proof of Lemma 3.16 (p. 16)
  says "For 3.1, we see that the initial positions are (P (0), P (1), . . . , P (m − 1))". We
  follow Experiment 3.2 and the proof: `realExperiment` outputs `fun e => locate s₀ e hm`, the
  positions of the elements, as the paper's DS.Locate would.
* **Experiment 3.2 output on an empty queried cell:** The pseudocode of Experiment 3.2
  ([WangRen2025], p. 13) reads "Find a random position c′ ∈ \[m′\] satisfying A\[c′\] = ⊥.",
  then "Update A\[c′\] ← A\[ci\] and A\[ci\] ← ∅.", then "If A\[c′\] ≠ ⊥, output c′.
  Otherwise, output ⊥." If $c_i$ is empty and the sampled destination is $c' = c_i$ itself, the
  second update leaves $A[c'] = ∅ \ne ⊥$, so the literal pseudocode outputs $c'$ for an empty
  query. The proof of Lemma 3.16 (p. 16) instead says "For the t-th position ct , no element
  resides in position ct , then the output of both Experiments 3.1 and 3.2 will be ⊥." We follow
  the proof: `idealUpdate` decides the output from the content of $c$ before the update, so an
  empty query outputs `none` even when it selects itself as destination.
* **Fixed relocation positions:** As in Experiments 3.1 and 3.2, the relocated positions
  $c_1, \ldots, c_Q$ are fixed in advance (`c : Fin Q → Fin m'`). They must be distinct
  (Section 3.1, p. 12: "each time is called on a distinct position") and $Q \le m' - m$. An
  adaptive choice of positions is not modelled.
* **Deterministic correctness and exact security:** There is no error parameter $\varepsilon$:
  correctness holds deterministically for every permutation and valid history (matching
  Definition 2.1's probability-1 requirement). Security is perfect (information-theoretic): the
  output laws are exactly equal,
  `(realExperiment m m' Q c hm).eval = (idealExperiment m m' Q c hm).eval`, with no adversary,
  no computational assumption and no advantage bound.
* **Scope:** This module covers Section 3's correctness and perfect security for an ideal
  uniformly random permutation and fixed relocation positions (Theorem 3.3 without its
  expected/amortized running-time bounds). Not formalized: the efficiency analysis (Theorem 3.3's
  bullets, Appendix A), the small-domain PRP instantiation (Section 2.2), the PIR scheme of
  Section 4 (Construction 4.2, Theorem 4.1) and the `ST = Ω(nw)` lower bounds (Appendix B).
-/

public section

open Cslib Cslib.Probability Cslib.RandomPermutation
open scoped ENNReal

namespace Cslib.Crypto.Protocols.PIR.Preprocessing.Relocation

/-! ### Construction 3.5: Relocation Data Structure -/

/-- State of the Wang–Ren relocation data structure ([WangRen2025], Constructions 3.4 and 3.5,
p. 14): a permutation `perm` on `Fin m'` together with the ordered list `history` of relocated
physical positions (oldest first). -/
structure RelocationState (m m' : ℕ) where
  /-- Underlying permutation on physical positions `Fin m'`. -/
  perm : Equiv.Perm (Fin m')
  /-- Ordered list of physical positions relocated so far (`C` in [WangRen2025]). -/
  history : List (Fin m')

namespace RelocationState

/-- A relocation state is valid if all relocated positions in `history` are distinct and
the number of relocations does not exceed the number of spare positions `m' - m`
([WangRen2025], Section 3.1, p. 12). -/
@[expose] def Valid {m m' : ℕ} (s : RelocationState m m') : Prop :=
  s.history.Nodup ∧ m + s.history.length ≤ m'

end RelocationState

/-- Initialize the relocation data structure with permutation `perm` and empty history
([WangRen2025], Construction 3.5, `DS.Init`, p. 14). -/
@[expose] def init {m m' : ℕ} (perm : Equiv.Perm (Fin m')) : RelocationState m m' := ⟨perm, []⟩

/-- The initial relocation state is valid whenever `m ≤ m'`. -/
theorem valid_init {m m' : ℕ} (perm : Equiv.Perm (Fin m')) (hm : m ≤ m') :
    (init (m := m) perm).Valid :=
  ⟨List.nodup_nil, by simp [init, hm]⟩

/-- Backward edge lookup in the relocation graph ([WangRen2025], Construction 3.5, `DS.InEdge`,
p. 14): if `perm.symm c ≥ m` and `perm.symm c - m < history.length`, returns
`history[perm.symm c - m]`. -/
@[expose] def inEdge? {m m' : ℕ} (s : RelocationState m m') (c : Fin m') : Option (Fin m') :=
  let p := (s.perm.symm c).val
  if m ≤ p then s.history[p - m]? else none

/-- Forward edge lookup in the relocation graph ([WangRen2025], Construction 3.5, `DS.OutEdge`,
p. 14): if `c` appears at index `idx` in `history` and `m + idx < m'`, returns
`perm ⟨m + idx, _⟩`. -/
@[expose] def outEdge? {m m' : ℕ} (s : RelocationState m m') (c : Fin m') : Option (Fin m') :=
  match s.history.idxOf? c with
  | some idx =>
    if h : m + idx < m' then some (s.perm ⟨m + idx, h⟩) else none
  | none => none

/-- Bounded walk along a partial transition function `step` for at most `fuel` steps. -/
@[expose] def walk {α : Type} (step : α → Option α) : ℕ → α → α
  | 0, c => c
  | fuel + 1, c =>
    match step c with
    | some c' => walk step fuel c'
    | none => c

/-- Walk backward along `inEdge?` to the start of the relocation chain containing `c`
([WangRen2025], Construction 3.5, `DS.StartOfChain`, p. 14). -/
@[expose] def startOfChain {m m' : ℕ} (s : RelocationState m m') (c : Fin m') : Fin m' :=
  walk (inEdge? s) (s.history.length + 1) c

/-- Walk forward along `outEdge?` to the end of the relocation chain starting at `c`
([WangRen2025], Construction 3.5, `DS.EndOfChain`, p. 14). -/
@[expose] def endOfChain {m m' : ℕ} (s : RelocationState m m') (c : Fin m') : Fin m' :=
  walk (outEdge? s) (s.history.length + 1) c

/-- Return the logical element (if any) whose chain currently ends at or passes through `c`
([WangRen2025], Construction 3.5, `DS.Access`, p. 14). -/
@[expose] def access {m m' : ℕ} (s : RelocationState m m') (c : Fin m') : Option (Fin m) :=
  let i := s.perm.symm (startOfChain s c)
  if h : i.val < m then some ⟨i.val, h⟩ else none

/-- Return the current physical position of logical element `e` ([WangRen2025],
Construction 3.5, `DS.Locate`, p. 14). -/
@[expose] def locate {m m' : ℕ} (s : RelocationState m m') (e : Fin m)
    (hm : m ≤ m') : Fin m' :=
  endOfChain s (s.perm (Fin.castLE hm e))

/-- Relocate physical position `c` by appending it to `history` ([WangRen2025],
Construction 3.5, `DS.Relocate`, p. 14). -/
@[expose] def relocate {m m' : ℕ} (s : RelocationState m m') (c : Fin m') : RelocationState m m' :=
  { s with history := s.history ++ [c] }

/-! ### General Walk Lemmas -/

private theorem walk_of_step_eq_none {α : Type} {step : α → Option α} {c : α} (h : step c = none) :
    ∀ k, walk step k c = c
  | 0 => rfl
  | _ + 1 => by simp [walk, h]

private theorem walk_add {α : Type} (step : α → Option α) (a b : ℕ) (c : α) :
    walk step (a + b) c = walk step b (walk step a c) := by
  induction a generalizing c with
  | zero => simp [walk]
  | succ a ih =>
    rw [Nat.succ_add, walk, walk]
    cases h : step c with
    | some c' => exact ih c'
    | none => exact (walk_of_step_eq_none h b).symm

private theorem walk_inv_walk {α : Type} {f g : α → Option α}
    (hfg : ∀ x y, f x = some y ↔ g y = some x) {c : α} (hc : g c = none) (k : ℕ) :
    walk g k (walk f k c) = c := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [walk_add f k 1 c]
    generalize walk f k c = x at ih ⊢
    cases hf : f x with
    | some y =>
      have hg : g y = some x := (hfg x y).mp hf
      simp [walk, hf, hg, ih]
    | none =>
      rw [walk_of_step_eq_none hf 1, walk_add g k 1 x, ih, walk_of_step_eq_none hc 1]

private theorem step_walk_eq_none_of_le {α : Type} {step : α → Option α} {c : α} {k r : ℕ}
    (hkr : k ≤ r) (hk : step (walk step k c) = none) :
    walk step r c = walk step k c := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkr
  rw [walk_add, walk_of_step_eq_none hk]

private theorem step_walk_eq_some_of_le {α : Type} {step : α → Option α} {c : α} {k r : ℕ}
    (hkr : k ≤ r) (hr : step (walk step r c) ≠ none) :
    step (walk step k c) = some (walk step (k + 1) c) := by
  cases hk : step (walk step k c) with
  | some y =>
    rw [walk_add step k 1 c]
    simp [walk, hk]
  | none => exact absurd (step_walk_eq_none_of_le hkr hk ▸ hk) hr

private theorem walk_injective_of_step_ne_none {α : Type} {f g : α → Option α}
    (hfg : ∀ x y, f x = some y ↔ g y = some x) {c : α} (hc : g c = none) {r : ℕ}
    (hr : f (walk f r c) ≠ none) :
    ∀ i j : ℕ, i ≤ r + 1 → j ≤ r + 1 → walk f i c = walk f j c → i = j := by
  have hstep : ∀ k ≤ r, g (walk f (k + 1) c) = some (walk f k c) := fun k hkr =>
    (hfg _ _).mp (step_walk_eq_some_of_le hkr hr)
  intro i
  induction i with
  | zero =>
    rintro (_ | j) _ _ heq
    · rfl
    · exact nomatch (heq.symm ▸ hstep j (by omega)).symm.trans hc
  | succ i ih =>
    rintro (_ | j) hi hj heq
    · exact nomatch (heq ▸ hstep i (by omega)).symm.trans hc
    · have h := (heq ▸ hstep i (by omega)).symm.trans (hstep j (by omega))
      exact congrArg Nat.succ (ih j (by omega) (by omega) (Option.some.inj h))

private theorem step_walk_eq_none_of_walk_mem {α : Type} {f g : α → Option α} {H : Finset α}
    (hfg : ∀ x y, f x = some y ↔ g y = some x) {c : α} (hc : g c = none) {k : ℕ}
    (hk : H.card ≤ k) (d : ℕ) (hd : d ≤ 1)
    (hmem : f (walk f k c) ≠ none → ∀ i ≤ k, walk f (i + d) c ∈ H) :
    f (walk f k c) = none := by
  by_contra hne
  have hinj := walk_injective_of_step_ne_none hfg hc hne
  let emb : Fin (k + 1) ↪ H :=
    ⟨fun i => ⟨walk f (i.val + d) c, hmem hne i.val (Nat.le_of_lt_succ i.isLt)⟩,
      fun i j h => by
        have := hinj (i.val + d) (j.val + d) (by omega) (by omega) (Subtype.ext_iff.mp h)
        omega⟩
  have hcard := Fintype.card_le_of_embedding emb
  simp only [Fintype.card_fin, Fintype.card_coe] at hcard
  omega

private theorem walk_eq_of_walk_ne {α : Type} {f f' : α → Option α} {c : α}
    (hfc : f c = none) (hff' : ∀ x ≠ c, f' x = f x) :
    ∀ (k : ℕ) (x : α), walk f k x ≠ c → walk f' k x = walk f k x
  | 0, _, _ => rfl
  | k + 1, x, hne => by
    have hxc : x ≠ c := fun h => hne (h ▸ walk_of_step_eq_none hfc (k + 1))
    rw [walk, walk, hff' x hxc]
    cases hf : f x with
    | some y => exact walk_eq_of_walk_ne hfc hff' k y (by simpa [walk, hf] using hne)
    | none => rfl

private theorem exists_walk_eq_of_walk_eq {α : Type} {f f' : α → Option α} {c u : α}
    (hf'c : f' c = some u) (hff' : ∀ x ≠ c, f' x = f x) :
    ∀ (k : ℕ) (x : α), walk f k x = c →
      ∃ a ≤ k, ∀ b, walk f' (b + (a + 1)) x = walk f' b u
  | k, x, hkx => by
    classical
    by_cases hxc : x = c
    · subst hxc
      exact ⟨0, Nat.zero_le k, fun b => by rw [Nat.add_zero, walk, hf'c]⟩
    · cases k with
      | zero => exact absurd hkx hxc
      | succ k' =>
        cases hf : f x with
        | none =>
          simp only [walk, hf] at hkx
          exact absurd hkx hxc
        | some y =>
          have hky : walk f k' y = c := by simpa [walk, hf] using hkx
          obtain ⟨a', ha', ih⟩ := exists_walk_eq_of_walk_eq hf'c hff' k' y hky
          refine ⟨a' + 1, Nat.succ_le_succ ha', fun b => ?_⟩
          rw [← Nat.add_assoc, walk, hff' x hxc, hf]
          exact ih b

/-! ### Relocation Graph Edges and Chains (Definition 3.6, Facts 3.7–3.12, Lemma 3.9) -/

/-- Directed edge relation in the relocation graph ([WangRen2025], Definition 3.6, p. 15):
`u` was relocated at step `t` to `s.perm ⟨m + t, _⟩ = v`. -/
def hasEdge {m m' : ℕ} (s : RelocationState m m') (u v : Fin m') : Prop :=
  ∃ (t : ℕ) (ht : t < s.history.length) (hm : m + t < m'),
    s.history[t] = u ∧ s.perm ⟨m + t, hm⟩ = v

private theorem idxOf?_getElem_of_nodup {α : Type} [BEq α] [LawfulBEq α] {l : List α}
    (hnd : l.Nodup) {t : ℕ} (ht : t < l.length) :
    l.idxOf? l[t] = some t := by
  rw [List.idxOf?_eq_some_iff]
  refine ⟨ht, rfl, fun j hj hjeq => ?_⟩
  have := (hnd.getElem_inj_iff (hi := hj.trans ht) (hj := ht)).mp hjeq
  omega

/-- `inEdge? s v = some u` iff there is a directed edge from `u` to `v` in the relocation graph
([WangRen2025], Definition 3.6 and Lemma 3.9, p. 15). -/
theorem inEdge?_eq_some_iff {m m' : ℕ} (s : RelocationState m m') (u v : Fin m') :
    inEdge? s v = some u ↔ hasEdge s u v := by
  simp only [inEdge?, hasEdge]
  split_ifs with hp
  · rw [List.getElem?_eq_some_iff]
    refine ⟨fun ⟨ht, h⟩ => ?_, fun ⟨t, ht, _, h1, h2⟩ =>
      ⟨by simpa [← h2] using ht, by simpa [← h2] using h1⟩⟩
    have hlt := (Nat.add_sub_of_le hp).trans_lt (s.perm.symm v).isLt
    exact ⟨(s.perm.symm v).val - m, ht, hlt, h,
      s.perm.eq_symm_apply.mp (Fin.ext (Nat.add_sub_of_le hp))⟩
  · exact iff_of_false (by simp) fun ⟨_, _, _, _, h⟩ => hp (by simp [← h])

/-- When `s.history.Nodup`, `outEdge? s u = some v` iff there is a directed edge from `u` to `v`
in the relocation graph ([WangRen2025], Definition 3.6 and Lemma 3.9, p. 15). -/
theorem outEdge?_eq_some_iff {m m' : ℕ} {s : RelocationState m m'} (hnd : s.history.Nodup)
    (u v : Fin m') :
    outEdge? s u = some v ↔ hasEdge s u v := by
  simp only [outEdge?, hasEdge]
  cases hidx : s.history.idxOf? u with
  | none =>
    dsimp only
    simp only [reduceCtorEq, false_iff]
    rintro ⟨t, ht, _, rfl, _⟩
    exact List.idxOf?_eq_none_iff.mp hidx (List.getElem_mem ht)
  | some idx =>
    dsimp only
    obtain ⟨hlt, rfl, _⟩ := List.idxOf?_eq_some_iff.mp hidx
    have hti {t : ℕ} (ht : t < s.history.length) (heq : s.history[t] = s.history[idx]) :
        idx = t := (hnd.getElem_inj_iff (hi := hlt) (hj := ht)).mp heq.symm
    split_ifs with hmt
    · refine ⟨fun h => ⟨idx, hlt, hmt, rfl, Option.some.inj h⟩, ?_⟩
      rintro ⟨t, ht, _, heq, rfl⟩
      cases hti ht heq
      rfl
    · exact iff_of_false (by simp) fun ⟨t, ht, hmt', heq, _⟩ => hmt (hti ht heq ▸ hmt')

/-- **Lemma 3.9** of [WangRen2025] (p. 15): when `s.history.Nodup`, `outEdge?` and `inEdge?` are
mutually inverse partial functions, so every node has at most one out-edge and at most one
in-edge. -/
theorem outEdge?_eq_some_iff_inEdge?_eq_some {m m' : ℕ} {s : RelocationState m m'}
    (hnd : s.history.Nodup) (u v : Fin m') :
    outEdge? s u = some v ↔ inEdge? s v = some u := by
  rw [outEdge?_eq_some_iff hnd, inEdge?_eq_some_iff]

private theorem mem_history_of_outEdge?_eq_some {m m' : ℕ} {s : RelocationState m m'}
    {u v : Fin m'} (h : outEdge? s u = some v) : u ∈ s.history := by
  by_contra hnot
  simp [outEdge?, List.idxOf?_eq_none_iff.mpr hnot] at h

private theorem mem_history_of_inEdge?_eq_some {m m' : ℕ} {s : RelocationState m m'}
    (hnd : s.history.Nodup) {u v : Fin m'} (h : inEdge? s u = some v) : v ∈ s.history :=
  mem_history_of_outEdge?_eq_some ((outEdge?_eq_some_iff_inEdge?_eq_some hnd v u).mpr h)

/-- **Fact 3.8** of [WangRen2025] (p. 15): any unconsumed position `u ∉ s.history` has no
out-edge. -/
theorem outEdge?_eq_none_of_not_mem {m m' : ℕ} {s : RelocationState m m'} {u : Fin m'}
    (hu : u ∉ s.history) : outEdge? s u = none := by
  simp [outEdge?, List.idxOf?_eq_none_iff.mpr hu]

/-- **Fact 3.8** of [WangRen2025] (p. 15): in a valid state, a position has no out-edge iff it has
not been relocated (`u ∉ s.history`). -/
theorem outEdge?_eq_none_iff_not_mem {m m' : ℕ} {s : RelocationState m m'} (hv : s.Valid)
    {u : Fin m'} : outEdge? s u = none ↔ u ∉ s.history := by
  refine ⟨fun h hu => ?_, outEdge?_eq_none_of_not_mem⟩
  obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hu
  have hmt : m + t < m' := by have := hv.2; omega
  simp [outEdge?, idxOf?_getElem_of_nodup hv.1 ht, hmt] at h

private theorem inEdge?_eq_none_of_symm_lt {m m' : ℕ} (s : RelocationState m m') {c : Fin m'}
    (hc : (s.perm.symm c).val < m) : inEdge? s c = none := by
  have : ¬ m ≤ (s.perm.symm c).val := by omega
  simp [inEdge?, this]

/-- **Fact 3.7** of [WangRen2025] (p. 15): for every logical element `e ∈ Fin m`, the initial
position `s.perm (Fin.castLE hm e)` has no in-edge. -/
theorem inEdge?_perm_castLE_eq_none {m m' : ℕ} (s : RelocationState m m') (e : Fin m)
    (hm : m ≤ m') : inEdge? s (s.perm (Fin.castLE hm e)) = none := by
  apply inEdge?_eq_none_of_symm_lt
  simp [e.isLt]

/-- Any position `c` with `m + s.history.length ≤ (s.perm.symm c).val` has no in-edge. -/
theorem inEdge?_eq_none_of_le_symm {m m' : ℕ} (s : RelocationState m m') {c : Fin m'}
    (hc : m + s.history.length ≤ (s.perm.symm c).val) : inEdge? s c = none := by
  simp only [inEdge?]
  split_ifs with hp
  · exact List.getElem?_eq_none (by omega)
  · rfl

/-- If `inEdge? s c = none` and `m ≤ (s.perm.symm c).val`, then
`m + s.history.length ≤ (s.perm.symm c).val`. -/
theorem le_symm_of_inEdge?_eq_none {m m' : ℕ} {s : RelocationState m m'} {c : Fin m'}
    (hc : inEdge? s c = none) (hm : m ≤ (s.perm.symm c).val) :
    m + s.history.length ≤ (s.perm.symm c).val := by
  simp only [inEdge?, hm, ↓reduceIte, List.getElem?_eq_none_iff] at hc
  omega

/-- **Corollary 3.10** of [WangRen2025] (p. 15, forward direction): starting from a node `c` with
no in-edge, walking forward along `outEdge?` for `k ≥ s.history.length` steps reaches a node with
no out-edge. -/
theorem outEdge?_walk_eq_none {m m' : ℕ} {s : RelocationState m m'} (hnd : s.history.Nodup)
    {c : Fin m'} (hc : inEdge? s c = none) {k : ℕ} (hk : s.history.length ≤ k) :
    outEdge? s (walk (outEdge? s) k c) = none :=
  step_walk_eq_none_of_walk_mem (H := s.history.toFinset)
    (outEdge?_eq_some_iff_inEdge?_eq_some hnd) hc
    (le_trans (List.toFinset_card_le s.history) hk) 0 (by omega) fun hne _ hi =>
      List.mem_toFinset.mpr (mem_history_of_outEdge?_eq_some (step_walk_eq_some_of_le hi hne))

/-- **Corollary 3.10** of [WangRen2025] (p. 15, backward direction): starting from a node `c` with
no out-edge, walking backward along `inEdge?` for `k ≥ s.history.length` steps reaches a node with
no in-edge. -/
theorem inEdge?_walk_eq_none {m m' : ℕ} {s : RelocationState m m'} (hnd : s.history.Nodup)
    {c : Fin m'} (hc : outEdge? s c = none) {k : ℕ} (hk : s.history.length ≤ k) :
    inEdge? s (walk (inEdge? s) k c) = none :=
  step_walk_eq_none_of_walk_mem (H := s.history.toFinset)
    (fun x y => (outEdge?_eq_some_iff_inEdge?_eq_some hnd y x).symm) hc
    (le_trans (List.toFinset_card_le s.history) hk) 1 le_rfl fun hne _ hi =>
      List.mem_toFinset.mpr (mem_history_of_inEdge?_eq_some hnd (step_walk_eq_some_of_le hi hne))

private theorem walk_outEdge?_eq_endOfChain {m m' : ℕ} {s : RelocationState m m'}
    (hnd : s.history.Nodup) {c : Fin m'} (hc : inEdge? s c = none) {k : ℕ}
    (hk : s.history.length ≤ k) :
    walk (outEdge? s) k c = endOfChain s c := by
  have h0 := outEdge?_walk_eq_none hnd hc (le_rfl : s.history.length ≤ s.history.length)
  rw [endOfChain, step_walk_eq_none_of_le hk h0,
    step_walk_eq_none_of_le (Nat.le_succ s.history.length) h0]

private theorem outEdge?_endOfChain_eq_none {m m' : ℕ} {s : RelocationState m m'}
    (hnd : s.history.Nodup) {c : Fin m'} (hc : inEdge? s c = none) :
    outEdge? s (endOfChain s c) = none :=
  outEdge?_walk_eq_none hnd hc (Nat.le_succ _)

/-- **Corollary 3.10** of [WangRen2025] (p. 15): in a valid state, the end of any chain starting at
a node `c` with `inEdge? s c = none` lies outside `s.history`. -/
theorem endOfChain_not_mem_history {m m' : ℕ} {s : RelocationState m m'} (hv : s.Valid)
    {c : Fin m'} (hc : inEdge? s c = none) : endOfChain s c ∉ s.history :=
  (outEdge?_eq_none_iff_not_mem hv).mp (outEdge?_endOfChain_eq_none hv.1 hc)

/-- **Facts 3.11 and 3.12** of [WangRen2025] (p. 15): if `inEdge? s c = none`, walking forward to
`endOfChain s c` and then backward via `startOfChain s` returns `c`. -/
theorem startOfChain_endOfChain {m m' : ℕ} {s : RelocationState m m'} (hnd : s.history.Nodup)
    {c : Fin m'} (hc : inEdge? s c = none) : startOfChain s (endOfChain s c) = c :=
  walk_inv_walk (outEdge?_eq_some_iff_inEdge?_eq_some hnd) hc (s.history.length + 1)

/-- Walking backward to `startOfChain s c` from a node `c` with `outEdge? s c = none` reaches a
node with no in-edge. -/
theorem inEdge?_startOfChain_eq_none {m m' : ℕ} {s : RelocationState m m'} (hnd : s.history.Nodup)
    {c : Fin m'} (hc : outEdge? s c = none) : inEdge? s (startOfChain s c) = none :=
  inEdge?_walk_eq_none hnd hc (Nat.le_succ _)

/-- **Facts 3.11 and 3.12** of [WangRen2025] (p. 15): if `outEdge? s c = none`, walking backward to
`startOfChain s c` and then forward via `endOfChain s` returns `c`. -/
theorem endOfChain_startOfChain {m m' : ℕ} {s : RelocationState m m'} (hnd : s.history.Nodup)
    {c : Fin m'} (hc : outEdge? s c = none) : endOfChain s (startOfChain s c) = c :=
  walk_inv_walk (fun x y => (outEdge?_eq_some_iff_inEdge?_eq_some hnd y x).symm) hc
    (s.history.length + 1)

/-- **Fact 3.12** of [WangRen2025] (p. 15): `access s c = some e` iff the chain containing `c`
starts at `s.perm (Fin.castLE hm e)`. -/
theorem access_eq_some_iff {m m' : ℕ} (s : RelocationState m m') (c : Fin m') (e : Fin m)
    (hm : m ≤ m') :
    access s c = some e ↔ s.perm (Fin.castLE hm e) = startOfChain s c := by
  simp only [access]
  split_ifs with hlt
  · refine ⟨fun h => Option.some.inj h ▸ s.perm.apply_symm_apply (startOfChain s c), fun h => ?_⟩
    exact congrArg some (Fin.ext (by simpa using congrArg (fun x => (s.perm.symm x).val) h.symm))
  · exact ⟨False.elim, fun h => hlt (by simp [← congrArg (fun x => (s.perm.symm x).val) h])⟩

/-- **Fact 3.12** of [WangRen2025] (p. 15): `access s c = none` iff the chain containing `c`
starts at `s.perm i` for some `i ≥ m`. -/
theorem access_eq_none_iff {m m' : ℕ} (s : RelocationState m m') (c : Fin m') :
    access s c = none ↔ m ≤ (s.perm.symm (startOfChain s c)).val := by
  simp only [access, dite_eq_right_iff, reduceCtorEq, imp_false, not_lt]

/-! ### Lemmas 3.13 and 3.14: Correctness of Access and Locate -/

/-- For any valid state `s` and logical element `e`, `access s (locate s e hm) = some e`
([WangRen2025], Lemma 3.13 / Lemma 3.14, p. 15). -/
theorem access_locate {m m' : ℕ} {s : RelocationState m m'} (hv : s.Valid) (e : Fin m)
    (hm : m ≤ m') :
    access s (locate s e hm) = some e := by
  rw [access_eq_some_iff s _ e hm, locate,
    startOfChain_endOfChain hv.1 (inEdge?_perm_castLE_eq_none s e hm)]

/-- For any valid state `s`, `locate s` is injective on `Fin m` ([WangRen2025], Lemma 3.14,
p. 15). -/
theorem locate_injective {m m' : ℕ} {s : RelocationState m m'} (hv : s.Valid)
    (hm : m ≤ m') :
    Function.Injective (fun e => locate s e hm) := fun e₁ e₂ h =>
  Option.some.inj
    ((access_locate hv e₁ hm).symm.trans ((congrArg (access s) h).trans (access_locate hv e₂ hm)))

/-- For any valid state `s` and logical element `e`, `locate s e hm` is an unconsumed physical
position (`locate s e hm ∉ s.history`). -/
theorem locate_not_mem_history {m m' : ℕ} {s : RelocationState m m'} (hv : s.Valid)
    (e : Fin m) (hm : m ≤ m') :
    locate s e hm ∉ s.history :=
  endOfChain_not_mem_history hv (inEdge?_perm_castLE_eq_none s e hm)

/-- **Lemma 3.14** of [WangRen2025] (p. 15): for any valid state `s`, unconsumed position
`c ∉ s.history`, and logical element `e`, `access s c = some e ↔ locate s e hm = c`. -/
theorem access_eq_some_iff_locate_eq {m m' : ℕ} {s : RelocationState m m'} (hv : s.Valid)
    {c : Fin m'} (hc : c ∉ s.history) (e : Fin m) (hm : m ≤ m') :
    access s c = some e ↔ locate s e hm = c := by
  refine ⟨fun h => ?_, fun h => h ▸ access_locate hv e hm⟩
  rw [locate, (access_eq_some_iff s c e hm).mp h,
    endOfChain_startOfChain hv.1 (outEdge?_eq_none_of_not_mem hc)]

/-- **Lemma 3.13** of [WangRen2025] (p. 15): for any valid state `s` and logical element
`e ∈ Fin m`, there exists a unique unconsumed physical position `c ∉ s.history` such that
`access s c = some e`. -/
theorem existsUnique_access_eq {m m' : ℕ} {s : RelocationState m m'} (hv : s.Valid)
    (e : Fin m) :
    ∃! c : Fin m', c ∉ s.history ∧ access s c = some e :=
  have hm : m ≤ m' := Nat.le_of_add_right_le hv.2
  ⟨locate s e hm, ⟨locate_not_mem_history hv e hm, access_locate hv e hm⟩,
    fun _ ⟨hc, hacc⟩ => ((access_eq_some_iff_locate_eq hv hc e hm).mp hacc).symm⟩

/-! ### Lemma 3.15: Correctness of Relocation -/

/-- Relocating an unconsumed position `c ∉ s.history` when `m + s.history.length < m'` preserves
`RelocationState.Valid`. -/
theorem valid_relocate {m m' : ℕ} {s : RelocationState m m'} (hv : s.Valid) {c : Fin m'}
    (hc : c ∉ s.history) (hlen : m + s.history.length < m') :
    (relocate s c).Valid := by
  refine ⟨List.nodup_append.mpr ⟨hv.1, List.nodup_singleton c,
    fun _ ha _ hb h => hc (List.mem_singleton.mp hb ▸ h ▸ ha)⟩, ?_⟩
  simp only [relocate, List.length_append, List.length_singleton]
  omega

private theorem hasEdge_relocate_iff {m m' : ℕ} (s : RelocationState m m') (c x y : Fin m')
    (hlen : m + s.history.length < m') :
    hasEdge (relocate s c) x y ↔
      hasEdge s x y ∨ (x = c ∧ s.perm ⟨m + s.history.length, hlen⟩ = y) := by
  simp only [hasEdge, relocate, List.length_append, List.length_singleton]
  constructor
  · rintro ⟨t, ht, hmt, hx, hy⟩
    by_cases hlt : t < s.history.length
    · rw [List.getElem_append_left hlt] at hx
      exact Or.inl ⟨t, hlt, hmt, hx, hy⟩
    · obtain rfl : t = s.history.length := by omega
      simp only [List.getElem_append_right le_rfl, Nat.sub_self, List.getElem_cons_zero] at hx
      exact Or.inr ⟨hx.symm, hy⟩
  · rintro (⟨t, ht, hmt, rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨t, by omega, hmt, List.getElem_append_left ht, rfl⟩
    · exact ⟨s.history.length, by omega, hlen, by simp [List.getElem_append_right le_rfl], rfl⟩

private theorem outEdge?_relocate_self {m m' : ℕ} {s : RelocationState m m'} (hv : s.Valid)
    {c : Fin m'} (hc : c ∉ s.history) (hlen : m + s.history.length < m') :
    outEdge? (relocate s c) c = some (s.perm ⟨m + s.history.length, hlen⟩) := by
  rw [outEdge?_eq_some_iff (valid_relocate hv hc hlen).1, hasEdge_relocate_iff s c c _ hlen]
  exact Or.inr ⟨rfl, rfl⟩

private theorem outEdge?_relocate_of_ne {m m' : ℕ} {s : RelocationState m m'} (hv : s.Valid)
    {c x : Fin m'} (hc : c ∉ s.history) (hlen : m + s.history.length < m') (hxc : x ≠ c) :
    outEdge? (relocate s c) x = outEdge? s x := by
  ext y
  rw [outEdge?_eq_some_iff (valid_relocate hv hc hlen).1, outEdge?_eq_some_iff hv.1,
    hasEdge_relocate_iff s c x y hlen]
  simp [hxc]

private theorem inEdge?_relocate_of_ne {m m' : ℕ} (s : RelocationState m m') (c : Fin m')
    (hlen : m + s.history.length < m') {y : Fin m'}
    (hy : y ≠ s.perm ⟨m + s.history.length, hlen⟩) :
    inEdge? (relocate s c) y = inEdge? s y := by
  ext x
  rw [inEdge?_eq_some_iff, inEdge?_eq_some_iff, hasEdge_relocate_iff s c x y hlen]
  simp [hy.symm]

private theorem endOfChain_relocate_of_ne {m m' : ℕ} {s : RelocationState m m'} (hv : s.Valid)
    {c v₀ : Fin m'} (hc : c ∉ s.history) (hlen : m + s.history.length < m')
    (hv₀ : inEdge? s v₀ = none) (hne : endOfChain s v₀ ≠ c) :
    endOfChain (relocate s c) v₀ = endOfChain s v₀ := by
  have hlen' : (relocate s c).history.length + 1 = s.history.length + 2 := by simp [relocate]
  have hw : walk (outEdge? s) (s.history.length + 2) v₀ = endOfChain s v₀ :=
    walk_outEdge?_eq_endOfChain hv.1 hv₀ (by omega)
  rw [endOfChain, hlen',
    walk_eq_of_walk_ne (outEdge?_eq_none_of_not_mem hc)
      (fun x hxc => outEdge?_relocate_of_ne hv hc hlen hxc) _ v₀ (hw ▸ hne),
    hw]

private theorem endOfChain_relocate_of_eq {m m' : ℕ} {s : RelocationState m m'} (hv : s.Valid)
    {c v₀ : Fin m'} (hc : c ∉ s.history) (hlen : m + s.history.length < m')
    (hv₀ : inEdge? s v₀ = none) (hv₀_ne : v₀ ≠ s.perm ⟨m + s.history.length, hlen⟩)
    (heq : endOfChain s v₀ = c) :
    endOfChain (relocate s c) v₀ = endOfChain s (s.perm ⟨m + s.history.length, hlen⟩) := by
  let u := s.perm ⟨m + s.history.length, hlen⟩
  have hu_in : inEdge? s u = none := inEdge?_eq_none_of_le_symm s (by simp [u])
  have hu_ne_c : endOfChain s u ≠ c := by
    intro huc
    have := congrArg (startOfChain s) (huc.trans heq.symm)
    rw [startOfChain_endOfChain hv.1 hu_in, startOfChain_endOfChain hv.1 hv₀] at this
    exact hv₀_ne this.symm
  obtain ⟨a, _, ha⟩ := exists_walk_eq_of_walk_eq
    (outEdge?_relocate_self hv hc hlen)
    (fun x hxc => outEdge?_relocate_of_ne hv hc hlen hxc)
    (s.history.length + 1) v₀ heq
  have hv' : (relocate s c).Valid := valid_relocate hv hc hlen
  have hv₀' : inEdge? (relocate s c) v₀ = none := by
    rw [inEdge?_relocate_of_ne s c hlen hv₀_ne, hv₀]
  have hstab : walk (outEdge? (relocate s c)) ((s.history.length + 1) + (a + 1)) v₀ =
      endOfChain (relocate s c) v₀ :=
    walk_outEdge?_eq_endOfChain hv'.1 hv₀' (by
      simp only [relocate, List.length_append, List.length_singleton]; omega)
  rw [← hstab, ha (s.history.length + 1)]
  exact walk_eq_of_walk_ne (outEdge?_eq_none_of_not_mem hc)
    (fun x hxc => outEdge?_relocate_of_ne hv hc hlen hxc)
    (s.history.length + 1) u hu_ne_c

/-- **Lemma 3.15 (i)** of [WangRen2025] (p. 16): relocating an unconsumed physical position `c`
leaves `locate` unchanged for every logical element `e` not currently located at `c`. -/
theorem locate_relocate_of_ne {m m' : ℕ} {s : RelocationState m m'} (hv : s.Valid)
    {c : Fin m'} (hc : c ∉ s.history) (hlen : m + s.history.length < m')
    {e : Fin m} (hm : m ≤ m') (hne : locate s e hm ≠ c) :
    locate (relocate s c) e hm = locate s e hm :=
  endOfChain_relocate_of_ne hv hc hlen (inEdge?_perm_castLE_eq_none s e hm) hne

/-- **Lemma 3.15 (ii)** of [WangRen2025] (p. 16, explicit destination formula): if
`locate s e hm = c`, then relocating `c` moves `e` to
`endOfChain s (s.perm ⟨m + s.history.length, hlen⟩)`. -/
theorem locate_relocate_self_eq {m m' : ℕ} {s : RelocationState m m'} (hv : s.Valid)
    {c : Fin m'} (hc : c ∉ s.history) (hlen : m + s.history.length < m')
    {e : Fin m} (hm : m ≤ m') (heq : locate s e hm = c) :
    locate (relocate s c) e hm = endOfChain s (s.perm ⟨m + s.history.length, hlen⟩) := by
  refine endOfChain_relocate_of_eq hv hc hlen (inEdge?_perm_castLE_eq_none s e hm) ?_ heq
  intro h
  have := s.perm.injective h
  fin_index

/-- Combined one-step equation for `locate (relocate s c) e hm` ([WangRen2025], Lemma 3.15,
p. 16). -/
theorem locate_relocate {m m' : ℕ} {s : RelocationState m m'} (hv : s.Valid)
    {c : Fin m'} (hc : c ∉ s.history) (hlen : m + s.history.length < m')
    (e : Fin m) (hm : m ≤ m') :
    locate (relocate s c) e hm =
      if locate s e hm = c then
        endOfChain s (s.perm ⟨m + s.history.length, hlen⟩)
      else
        locate s e hm := by
  split_ifs with heq
  · exact locate_relocate_self_eq hv hc hlen hm heq
  · exact locate_relocate_of_ne hv hc hlen hm heq

private theorem access_endOfChain_perm_add_eq_none {m m' : ℕ} {s : RelocationState m m'}
    (hnd : s.history.Nodup) (hlen : m + s.history.length < m') :
    access s (endOfChain s (s.perm ⟨m + s.history.length, hlen⟩)) = none := by
  let u := s.perm ⟨m + s.history.length, hlen⟩
  have hu_in : inEdge? s u = none := inEdge?_eq_none_of_le_symm s (by simp [u])
  simp only [access, startOfChain_endOfChain hnd hu_in, u, Equiv.symm_apply_apply]
  have : ¬ m + s.history.length < m := by omega
  simp [this]

/-- **Lemma 3.15 (ii, Part b)** of [WangRen2025] (p. 16): if `locate s e hm = c`, then the new
position `c' = locate (relocate s c) e hm` was empty prior to the relocation
(`access s c' = none`). -/
theorem access_locate_relocate_self_eq_none {m m' : ℕ} {s : RelocationState m m'} (hv : s.Valid)
    {c : Fin m'} (hc : c ∉ s.history) (hlen : m + s.history.length < m')
    {e : Fin m} (hm : m ≤ m') (heq : locate s e hm = c) :
    access s (locate (relocate s c) e hm) = none := by
  rw [locate_relocate_self_eq hv hc hlen hm heq]
  exact access_endOfChain_perm_add_eq_none hv.1 hlen

/-- **Lemma 3.15 (ii)** of [WangRen2025] (p. 16): if `locate s e hm = c`, then after relocating
`c`, the element `e` is moved to an unconsumed position `c' ∉ (relocate s c).history` that was
empty prior to the relocation (`access s c' = none`). -/
theorem relocate_destination_empty {m m' : ℕ} {s : RelocationState m m'} (hv : s.Valid)
    {c : Fin m'} (hc : c ∉ s.history) (hlen : m + s.history.length < m')
    {e : Fin m} (hm : m ≤ m') (heq : locate s e hm = c) :
    locate (relocate s c) e hm ∉ (relocate s c).history ∧
      access s (locate (relocate s c) e hm) = none :=
  ⟨locate_not_mem_history (valid_relocate hv hc hlen) e hm,
    access_locate_relocate_self_eq_none hv hc hlen hm heq⟩

/-! ### Ideal Relocation Process and Security Experiments (Experiments 3.1–3.2, Lemma 3.16) -/

/-- State of a physical cell in the ideal relocation process ([WangRen2025], Experiment 3.2,
p. 13): either occupied by a logical element `e`, available as an `empty` slot, or `consumed` by
a previous relocation. -/
inductive IdealCell (m : ℕ) where
  /-- Cell currently holds logical element `e`. -/
  | elem (e : Fin m)
  /-- Cell is currently empty and available as a relocation destination. -/
  | empty
  /-- Cell has been relocated in a prior step and cannot be reused. -/
  | consumed
  deriving DecidableEq

/-- Initialize the ideal array from an injective placement `emb : Fin m ↪ Fin m'`
([WangRen2025], Experiment 3.2, p. 13). -/
def initIdealArray {m m' : ℕ} (emb : Fin m ↪ Fin m') (p : Fin m') : IdealCell m :=
  match (List.finRange m).find? (fun e => emb e == p) with
  | some e => .elem e
  | none => .empty

/-- The set of currently empty physical positions in an ideal array `A`. -/
def emptyPositions {m m' : ℕ} (A : Fin m' → IdealCell m) : Finset (Fin m') :=
  Finset.univ.filter (fun p => A p = .empty)

/-- Pure array update when relocating position `c` to destination `c'` in the ideal experiment
([WangRen2025], Experiment 3.2, p. 13). The output is read from `A c` before the update, as in the
proof of Lemma 3.16 (p. 16): an empty `c` outputs `none` even when `c' = c`, where the literal
pseudocode would test the updated cell, which then holds `∅`, and output `c'`. -/
@[expose] def idealUpdate {m m' : ℕ} (A : Fin m' → IdealCell m) (c c' : Fin m') :
    (Fin m' → IdealCell m) × Option (Fin m') :=
  let A' := Function.update (Function.update A c' (A c)) c .consumed
  let out := match A c with
    | .elem _ => some c'
    | _ => none
  (A', out)

/-- One step of the ideal relocation experiment ([WangRen2025], Experiment 3.2, p. 13): sample
`c'` uniformly from `emptyPositions A`, move the contents of `c` to `c'`, mark `c` as consumed,
and output `some c'` if `c` held a logical element (`none` otherwise). -/
noncomputable def idealStep {m m' : ℕ} (A : Fin m' → IdealCell m) (c : Fin m') :
    ProbComp ((Fin m' → IdealCell m) × Option (Fin m')) :=
  if h : (emptyPositions A).Nonempty then
    have : Nonempty (emptyPositions A) := h.to_subtype
    do
      let c' ← $ᵗ (emptyPositions A)
      pure (idealUpdate A c c'.val)
  else
    pure (A, none)

/-- Run a sequence of ideal relocation steps on `A` ([WangRen2025], Experiment 3.2, p. 13). -/
noncomputable def idealRunSteps {m m' : ℕ} (A : Fin m' → IdealCell m) :
    List (Fin m') → ProbComp ((Fin m' → IdealCell m) × List (Option (Fin m')))
  | [] => pure (A, [])
  | c :: cs => do
    let (A₁, out) ← idealStep A c
    let (A₂, outs) ← idealRunSteps A₁ cs
    pure (A₂, out :: outs)

/-- One step of the real relocation experiment ([WangRen2025], Experiment 3.1, p. 13): relocate
`c` and output `some (locate (relocate s c) e hm)` if `access s c = some e` (`none` otherwise). -/
@[expose] def realStep {m m' : ℕ} (s : RelocationState m m') (c : Fin m')
    (hm : m ≤ m') :
    RelocationState m m' × Option (Fin m') :=
  let s' := relocate s c
  let out := (access s c).map (fun e => locate s' e hm)
  (s', out)

/-- Run a sequence of real relocation steps on `s` ([WangRen2025], Experiment 3.1, p. 13). -/
@[expose] def realRunSteps {m m' : ℕ} (s : RelocationState m m') :
    List (Fin m') → (hm : m ≤ m') → RelocationState m m' × List (Option (Fin m'))
  | [], _ => (s, [])
  | c :: cs, hm =>
    let (s₁, out) := realStep s c hm
    let (s₂, outs) := realRunSteps s₁ cs hm
    (s₂, out :: outs)

/-- Observable output of the relocation security experiments ([WangRen2025], Experiments 3.1
and 3.2, p. 13): the initial positions of all $m$ logical elements together with the destination
outputs of each relocation step. -/
structure RelocationOutput (m m' : ℕ) where
  /-- Initial physical position of each logical element `e ∈ Fin m`. -/
  initPositions : Fin m → Fin m'
  /-- Output of each relocation query (`some c'` if occupied, `none` if empty). -/
  stepOutputs : List (Option (Fin m'))
  deriving DecidableEq

/-- Real relocation experiment ([WangRen2025], Experiment 3.1, p. 13): sample a uniform
permutation `perm` on `Fin m'`, record the initial positions of all elements in `Fin m`, and run
`realRunSteps` on the query sequence `c`, which is fixed in advance. The initial output is the
element positions (`locate`), not the tuple of `access` values that the paper literally writes;
see the module docstring. -/
@[expose] noncomputable def realExperiment (m m' Q : ℕ) (c : Fin Q → Fin m')
    (hm : m ≤ m') : ProbComp (RelocationOutput m m') := do
  let perm ← $ᵗ (Equiv.Perm (Fin m'))
  let s₀ := init (m := m) perm
  let (_, outs) := realRunSteps s₀ (List.ofFn c) hm
  pure ⟨fun e => locate s₀ e hm, outs⟩

/-- Ideal relocation experiment ([WangRen2025], Experiment 3.2, p. 13): sample a uniform
injective placement `emb : Fin m ↪ Fin m'` and run `idealRunSteps` on the query sequence `c`. -/
noncomputable def idealExperiment (m m' Q : ℕ) (c : Fin Q → Fin m')
    (hm : m ≤ m') : ProbComp (RelocationOutput m m') :=
  have : Nonempty (Fin m ↪ Fin m') := ⟨Fin.castLEEmb hm⟩
  do
    let emb ← $ᵗ (Fin m ↪ Fin m')
    let (_, outs) ← idealRunSteps (initIdealArray emb) (List.ofFn c)
    pure ⟨emb, outs⟩

/-! ### Uniform Permutation and Prefix-Conditioning Lemmas -/

private theorem card_extPerms_ofFn_mul_card_embedding {m m' : ℕ} (hm : m ≤ m')
    (emb : Fin m ↪ Fin m') :
    (extPerms (List.ofFn fun i => (Fin.castLEEmb hm i, emb i))).card *
      Fintype.card (Fin m ↪ Fin m') = Fintype.card (Equiv.Perm (Fin m')) := by
  rw [Fintype.card_perm, ← sum_card_extPerms_ofFn (Fin.castLEEmb hm),
    Finset.sum_congr rfl fun e _ => card_extPerms_ofFn_eq (Fin.castLEEmb hm) e emb]
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]

private theorem uniformOfFintype_perm_map_castLEEmb {m m' : ℕ} (hm : m ≤ m') :
    have : Nonempty (Fin m ↪ Fin m') := ⟨Fin.castLEEmb hm⟩
    (PMF.uniformOfFintype (Equiv.Perm (Fin m'))).map
      (fun π : Equiv.Perm (Fin m') => (Fin.castLEEmb hm).trans π.toEmbedding) =
      PMF.uniformOfFintype (Fin m ↪ Fin m') := by
  intro
  ext emb
  have hiff (π : Equiv.Perm (Fin m')) :
      emb = (Fin.castLEEmb hm).trans π.toEmbedding ↔
        π ∈ extPerms (List.ofFn fun i => (Fin.castLEEmb hm i, emb i)) := by
    simp [extPerms_ofFn_eq, DFunLike.ext_iff, eq_comm]
  simp only [PMF.map_apply, PMF.uniformOfFintype_apply, hiff, tsum_fintype, ← Finset.sum_filter,
    Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  have hcard : ((extPerms (List.ofFn fun i => (Fin.castLEEmb hm i, emb i))).card : ℝ≥0∞) *
      (Fintype.card (Fin m ↪ Fin m') : ℝ≥0∞) = (Fintype.card (Equiv.Perm (Fin m')) : ℝ≥0∞) := by
    exact_mod_cast card_extPerms_ofFn_mul_card_embedding hm emb
  have hC0 : ((extPerms (List.ofFn fun i => (Fin.castLEEmb hm i, emb i))).card : ℝ≥0∞) ≠ 0 :=
    fun h => Nat.cast_ne_zero.mpr Fintype.card_ne_zero (by rwa [h, zero_mul, eq_comm] at hcard)
  have hCtop :=
    ENNReal.natCast_ne_top (extPerms (List.ofFn fun i => (Fin.castLEEmb hm i, emb i))).card
  rw [← hcard, ENNReal.mul_inv (Or.inl hC0) (Or.inl hCtop), ← mul_assoc,
    ENNReal.mul_inv_cancel hC0 hCtop, one_mul]

private theorem uniformOfFintype_perm_bind_swap {α : Type} {m' k : ℕ} (hk : k < m')
    (f : Equiv.Perm (Fin m') → Fin m' → PMF α)
    (hf : ∀ π₁ π₂ : Equiv.Perm (Fin m'),
      (∀ i : Fin m', i.val < k → π₁ i = π₂ i) → f π₁ = f π₂)
    (j : {j : Fin m' // k ≤ j.val}) :
    (PMF.uniformOfFintype (Equiv.Perm (Fin m'))).bind (fun π => f π (π j.val)) =
      (PMF.uniformOfFintype (Equiv.Perm (Fin m'))).bind (fun π => f π (π ⟨k, hk⟩)) := by
  let τ : Equiv.Perm (Fin m') := Equiv.swap ⟨k, hk⟩ j.val
  rw [← PMF.uniformOfFintype_bind_equiv (Equiv.mulRight τ)]
  congr 1; ext π
  have hpre : ∀ i : Fin m', i.val < k → (π * τ) i = π i := by
    intro i hi
    have hik : i ≠ ⟨k, hk⟩ := Fin.ne_of_lt hi
    have hij : i ≠ j.val := by
      have := j.property
      exact Fin.ne_of_lt (by omega : i < j.val)
    simp [τ, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hik hij]
  change (f (π * τ) ((π * τ) j.val)) _ = _
  rw [hf (π * τ) π hpre]
  simp [τ, Equiv.Perm.mul_apply]

private theorem uniformOfFintype_perm_bind_prefix {α : Type} {m' k : ℕ} (hk : k < m')
    (f : Equiv.Perm (Fin m') → Fin m' → PMF α)
    (hf : ∀ π₁ π₂ : Equiv.Perm (Fin m'),
      (∀ i : Fin m', i.val < k → π₁ i = π₂ i) → f π₁ = f π₂) :
    have : Nonempty {j : Fin m' // k ≤ j.val} := ⟨⟨⟨k, hk⟩, le_rfl⟩⟩
    (PMF.uniformOfFintype (Equiv.Perm (Fin m'))).bind (fun π => f π (π ⟨k, hk⟩)) =
      (PMF.uniformOfFintype (Equiv.Perm (Fin m'))).bind (fun π =>
        (PMF.uniformOfFintype {j : Fin m' // k ≤ j.val}).bind (fun j => f π (π j.val))) := by
  intro
  rw [PMF.bind_comm (PMF.uniformOfFintype (Equiv.Perm (Fin m')))]
  simp_rw [uniformOfFintype_perm_bind_swap hk f hf, PMF.bind_const]

/-! ### State-to-Ideal-Array Coupling -/

/-- Map a relocation state `s` to its induced ideal array view: consumed positions map to
`.consumed`, positions holding element `e` map to `.elem e`, and all other positions map to
`.empty`. -/
@[expose] def stateToIdealArray {m m' : ℕ} (s : RelocationState m m') (p : Fin m') : IdealCell m :=
  if p ∈ s.history then
    .consumed
  else
    match access s p with
    | some e => .elem e
    | none => .empty

private theorem initIdealArray_eq_elem_iff {m m' : ℕ} (emb : Fin m ↪ Fin m') (p : Fin m')
    (e : Fin m) :
    initIdealArray emb p = .elem e ↔ emb e = p := by
  simp only [initIdealArray]
  cases h : (List.finRange m).find? (fun x => emb x == p) with
  | none =>
    exact ⟨(fun h' => nomatch h'), fun hep => by
      simpa [hep] using List.find?_eq_none.mp h e (List.mem_finRange e)⟩
  | some e' =>
    have he' : emb e' = p := by simpa using List.find?_some h
    exact ⟨fun h' => IdealCell.elem.inj h' ▸ he',
      fun h' => congrArg IdealCell.elem (emb.injective (he'.trans h'.symm))⟩

private theorem stateToIdealArray_init {m m' : ℕ} (perm : Equiv.Perm (Fin m')) (hm : m ≤ m') :
    stateToIdealArray (init (m := m) perm) =
      initIdealArray ((Fin.castLEEmb hm).trans perm.toEmbedding) := by
  let emb : Fin m ↪ Fin m' := (Fin.castLEEmb hm).trans perm.toEmbedding
  ext p
  have hstart : startOfChain (init (m := m) perm) p = p := by
    simp [startOfChain, init, walk, inEdge?]
  have hiff (e : Fin m) : access (init (m := m) perm) p = some e ↔ emb e = p := by
    rw [access_eq_some_iff (init (m := m) perm) p e hm, hstart]
    rfl
  have hp : p ∉ (init (m := m) perm).history := by simp [init]
  simp only [stateToIdealArray, hp, ↓reduceIte]
  cases hacc : access (init (m := m) perm) p with
  | some e => exact ((initIdealArray_eq_elem_iff emb p e).mpr ((hiff e).mp hacc)).symm
  | none =>
    simp only [initIdealArray]
    cases hfind : (List.finRange m).find? (fun e => emb e == p) with
    | none => rfl
    | some e =>
      exact absurd ((hiff e).mpr (by simpa using List.find?_some hfind)) (by simp [hacc])

private theorem locate_init {m m' : ℕ} (perm : Equiv.Perm (Fin m')) (hm : m ≤ m') :
    (fun e => locate (init (m := m) perm) e hm) =
      ⇑((Fin.castLEEmb hm).trans perm.toEmbedding) := by
  ext e
  simp [locate, init, endOfChain, walk, outEdge?]

/-- In a valid state `s`, a physical position `p` is empty in `stateToIdealArray s` iff
`p ∉ s.history` and the chain ending at `p` starts at `s.perm j` for some spare index
`j ≥ m + s.history.length`. -/
theorem mem_emptyPositions_stateToIdealArray_iff {m m' : ℕ} {s : RelocationState m m'}
    (hv : s.Valid) (p : Fin m') :
    p ∈ emptyPositions (stateToIdealArray s) ↔
      p ∉ s.history ∧ m + s.history.length ≤ (s.perm.symm (startOfChain s p)).val := by
  rw [emptyPositions, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and, stateToIdealArray]
  split_ifs with hp
  · simp [hp]
  · cases hacc : access s p with
    | some e =>
      simp only [hp, not_false_eq_true, true_and, reduceCtorEq, false_iff, not_le]
      exact Nat.lt_of_not_ge fun hle =>
        nomatch hacc.symm.trans ((access_eq_none_iff s p).mpr (le_trans (Nat.le_add_right _ _) hle))
    | none =>
      simp only [hp, not_false_eq_true, true_and, true_iff]
      exact le_symm_of_inEdge?_eq_none
        (inEdge?_startOfChain_eq_none hv.1 (outEdge?_eq_none_of_not_mem hp))
        ((access_eq_none_iff s p).mp hacc)

/-- Bijection between spare indices `j ≥ m + s.history.length` and empty positions in
`stateToIdealArray s`, given by `j ↦ endOfChain s (s.perm j)` ([WangRen2025], proof of
Lemma 3.16, p. 17). -/
private def stepEquiv {m m' : ℕ} (s : RelocationState m m') (hv : s.Valid) :
    {j : Fin m' // m + s.history.length ≤ j.val} ≃ emptyPositions (stateToIdealArray s) where
  toFun j := ⟨endOfChain s (s.perm j.val), by
    have hin : inEdge? s (s.perm j.val) = none :=
      inEdge?_eq_none_of_le_symm s (by simp [j.property])
    rw [mem_emptyPositions_stateToIdealArray_iff hv]
    refine ⟨endOfChain_not_mem_history hv hin, ?_⟩
    rw [startOfChain_endOfChain hv.1 hin, Equiv.symm_apply_apply]
    exact j.property⟩
  invFun w := ⟨s.perm.symm (startOfChain s w.val),
    ((mem_emptyPositions_stateToIdealArray_iff hv w.val).mp w.property).2⟩
  left_inv j := by
    ext
    have hin : inEdge? s (s.perm j.val) = none :=
      inEdge?_eq_none_of_le_symm s (by simp [j.property])
    simp [startOfChain_endOfChain hv.1 hin]
  right_inv w := by
    ext
    have hnot : w.val ∉ s.history :=
      ((mem_emptyPositions_stateToIdealArray_iff hv w.val).mp w.property).1
    simp [endOfChain_startOfChain hv.1 (outEdge?_eq_none_of_not_mem hnot)]

private theorem access_relocate_endOfChain_perm_add {m m' : ℕ} {s : RelocationState m m'}
    (hv : s.Valid) {c : Fin m'} (hc : c ∉ s.history) (hlen : m + s.history.length < m')
    (hm : m ≤ m') :
    let c' := endOfChain s (s.perm ⟨m + s.history.length, hlen⟩)
    c' ≠ c → access (relocate s c) c' = access s c := by
  intro c' hc'c
  have hv' : (relocate s c).Valid := valid_relocate hv hc hlen
  have hc'_not_mem : c' ∉ s.history :=
    endOfChain_not_mem_history hv (inEdge?_eq_none_of_le_symm s (by simp))
  have hc'_not_mem' : c' ∉ (relocate s c).history := by simp [relocate, hc'_not_mem, hc'c]
  refine Option.ext fun e => ?_
  rw [access_eq_some_iff_locate_eq hv' hc'_not_mem' e hm,
    access_eq_some_iff_locate_eq hv hc e hm]
  refine ⟨fun h => ?_, locate_relocate_self_eq hv hc hlen hm⟩
  by_contra hne
  have heq : locate s e hm = c' := (locate_relocate_of_ne hv hc hlen hm hne).symm.trans h
  exact nomatch
    (heq ▸ access_locate hv e hm).symm.trans (access_endOfChain_perm_add_eq_none hv.1 hlen)

private theorem access_relocate_of_ne {m m' : ℕ} {s : RelocationState m m'} (hv : s.Valid)
    {c p : Fin m'} (hc : c ∉ s.history) (hp : p ∉ s.history)
    (hlen : m + s.history.length < m') (hpc : p ≠ c)
    (hpc' : p ≠ endOfChain s (s.perm ⟨m + s.history.length, hlen⟩)) (hm : m ≤ m') :
    access (relocate s c) p = access s p := by
  have hv' : (relocate s c).Valid := valid_relocate hv hc hlen
  have hp' : p ∉ (relocate s c).history := by simp [relocate, hp, hpc]
  refine Option.ext fun e => ?_
  rw [access_eq_some_iff_locate_eq hv' hp' e hm, access_eq_some_iff_locate_eq hv hp e hm]
  refine ⟨fun h => ?_, fun h => (locate_relocate_of_ne hv hc hlen hm (h ▸ hpc)).trans h⟩
  by_contra hne
  have heq_c : locate s e hm = c := by
    by_contra hnec
    exact hne ((locate_relocate_of_ne hv hc hlen hm hnec).symm.trans h)
  exact hpc' (h.symm.trans (locate_relocate_self_eq hv hc hlen hm heq_c))

private theorem stateToIdealArray_relocate {m m' : ℕ} {s : RelocationState m m'} (hv : s.Valid)
    {c : Fin m'} (hc : c ∉ s.history) (hlen : m + s.history.length < m')
    (hm : m ≤ m') :
    let c' := endOfChain s (s.perm ⟨m + s.history.length, hlen⟩)
    (stateToIdealArray (relocate s c), (realStep s c hm).2) =
      idealUpdate (stateToIdealArray s) c c' := by
  intro c'
  have hc'_not_mem : c' ∉ s.history :=
    endOfChain_not_mem_history hv (inEdge?_eq_none_of_le_symm s (by simp))
  refine Prod.ext (funext fun p => ?_) ?_
  · by_cases hpc : p = c
    · subst hpc
      simp [stateToIdealArray, relocate, idealUpdate]
    · by_cases hp_mem : p ∈ s.history
      · have hpc' : p ≠ c' := fun h => hc'_not_mem (h ▸ hp_mem)
        simp [stateToIdealArray, relocate, idealUpdate, hp_mem, hpc, hpc']
      · have hp_not_mem' : p ∉ (relocate s c).history := by simp [relocate, hp_mem, hpc]
        by_cases hpc' : p = c'
        · subst hpc'
          have hacc : access (relocate s c) c' = access s c :=
            access_relocate_endOfChain_perm_add hv hc hlen hm hpc
          simp [stateToIdealArray, idealUpdate, hp_not_mem', hc, hpc, hacc]
        · have hacc := access_relocate_of_ne hv hc hp_mem hlen hpc hpc' hm
          simp [stateToIdealArray, idealUpdate, hp_not_mem', hp_mem, hpc, hpc', hacc]
  · simp only [realStep, idealUpdate, stateToIdealArray, hc, ↓reduceIte]
    cases hacc : access s c with
    | none => rfl
    | some e =>
      simp only [Option.map_some, Option.some.injEq]
      exact locate_relocate_self_eq hv hc hlen hm
        ((access_eq_some_iff_locate_eq hv hc e hm).mp hacc)

/-! ### Prefix-Invariance of Real Runs -/

private theorem hasEdge_congr {m m' : ℕ} {π₁ π₂ : Equiv.Perm (Fin m')} {hist : List (Fin m')}
    (hpre : ∀ i : Fin m', i.val < m + hist.length → π₁ i = π₂ i) :
    hasEdge (m := m) ⟨π₁, hist⟩ = hasEdge (m := m) ⟨π₂, hist⟩ := by
  ext u v
  simp only [hasEdge]
  refine exists_congr fun t => exists_congr fun _ =>
    exists_congr fun hmt => and_congr_right fun _ => ?_
  rw [hpre ⟨m + t, hmt⟩ (by dsimp; omega)]

private theorem inEdge?_congr {m m' : ℕ} {π₁ π₂ : Equiv.Perm (Fin m')} {hist : List (Fin m')}
    (hpre : ∀ i : Fin m', i.val < m + hist.length → π₁ i = π₂ i) :
    inEdge? (m := m) ⟨π₁, hist⟩ = inEdge? (m := m) ⟨π₂, hist⟩ := by
  ext v u
  rw [inEdge?_eq_some_iff, inEdge?_eq_some_iff, hasEdge_congr hpre]

private theorem outEdge?_congr {m m' : ℕ} {π₁ π₂ : Equiv.Perm (Fin m')} {hist : List (Fin m')}
    (hpre : ∀ i : Fin m', i.val < m + hist.length → π₁ i = π₂ i) :
    outEdge? (m := m) ⟨π₁, hist⟩ = outEdge? (m := m) ⟨π₂, hist⟩ := by
  funext u
  simp only [outEdge?]
  cases hidx : hist.idxOf? u with
  | none => rfl
  | some idx =>
    have hlt : idx < hist.length := (List.idxOf?_eq_some_iff.mp hidx).1
    exact dite_congr rfl (fun hmt => congrArg some (hpre ⟨m + idx, hmt⟩ (by dsimp; omega)))
      fun _ => rfl

private theorem startOfChain_congr {m m' : ℕ} {π₁ π₂ : Equiv.Perm (Fin m')}
    {hist : List (Fin m')} (hpre : ∀ i : Fin m', i.val < m + hist.length → π₁ i = π₂ i) :
    startOfChain (m := m) ⟨π₁, hist⟩ = startOfChain (m := m) ⟨π₂, hist⟩ := by
  funext c; simp only [startOfChain, inEdge?_congr hpre]

private theorem endOfChain_congr {m m' : ℕ} {π₁ π₂ : Equiv.Perm (Fin m')} {hist : List (Fin m')}
    (hpre : ∀ i : Fin m', i.val < m + hist.length → π₁ i = π₂ i) :
    endOfChain (m := m) ⟨π₁, hist⟩ = endOfChain (m := m) ⟨π₂, hist⟩ := by
  funext c; simp only [endOfChain, outEdge?_congr hpre]

private theorem locate_congr {m m' : ℕ} {π₁ π₂ : Equiv.Perm (Fin m')} {hist : List (Fin m')}
    (hpre : ∀ i : Fin m', i.val < m + hist.length → π₁ i = π₂ i)
    (e : Fin m) (hm : m ≤ m') :
    locate ⟨π₁, hist⟩ e hm = locate ⟨π₂, hist⟩ e hm := by
  simp only [locate, endOfChain_congr hpre]
  rw [hpre (Fin.castLE hm e) (by simp; omega)]

private theorem access_congr {m m' : ℕ} {π₁ π₂ : Equiv.Perm (Fin m')} {hist : List (Fin m')}
    (hpre : ∀ i : Fin m', i.val < m + hist.length → π₁ i = π₂ i) (hm : m ≤ m') :
    access (m := m) ⟨π₁, hist⟩ = access ⟨π₂, hist⟩ := by
  ext c e
  rw [access_eq_some_iff _ c e hm, access_eq_some_iff _ c e hm,
    startOfChain_congr hpre, hpre (Fin.castLE hm e) (by simp; omega)]

private theorem stateToIdealArray_congr {m m' : ℕ} {π₁ π₂ : Equiv.Perm (Fin m')}
    {hist : List (Fin m')} (hpre : ∀ i : Fin m', i.val < m + hist.length → π₁ i = π₂ i)
    (hm : m ≤ m') :
    stateToIdealArray (m := m) ⟨π₁, hist⟩ = stateToIdealArray ⟨π₂, hist⟩ := by
  ext p; simp only [stateToIdealArray, access_congr hpre hm]

private theorem realRunSteps_fst {m m' : ℕ} (s : RelocationState m m') (cs : List (Fin m'))
    (hm : m ≤ m') :
    (realRunSteps s cs hm).1 = { s with history := s.history ++ cs } := by
  induction cs generalizing s with
  | nil => simp [realRunSteps]
  | cons c cs ih =>
    simp only [realRunSteps, realStep, relocate, ih, List.append_assoc, List.singleton_append]

private theorem realRunSteps_append {m m' : ℕ} (s : RelocationState m m') (cs₁ cs₂ : List (Fin m'))
    (hm : m ≤ m') :
    realRunSteps s (cs₁ ++ cs₂) hm =
      let (s₁, outs₁) := realRunSteps s cs₁ hm
      let (s₂, outs₂) := realRunSteps s₁ cs₂ hm
      (s₂, outs₁ ++ outs₂) := by
  induction cs₁ generalizing s with
  | nil => simp [realRunSteps]
  | cons c cs₁ ih => simp [realRunSteps, ih]

private theorem realRunSteps_snd_congr {m m' : ℕ} {π₁ π₂ : Equiv.Perm (Fin m')}
    (hist cs : List (Fin m')) (hm : m ≤ m')
    (hpre : ∀ i : Fin m', i.val < m + (hist.length + cs.length) → π₁ i = π₂ i) :
    (realRunSteps ⟨π₁, hist⟩ cs hm).2 = (realRunSteps ⟨π₂, hist⟩ cs hm).2 := by
  induction cs generalizing hist with
  | nil => rfl
  | cons c cs ih =>
    have hlen : (hist ++ [c]).length = hist.length + 1 := List.length_append ..
    simp only [List.length_cons] at hpre
    have hacc := access_congr (m := m) (hist := hist) (fun i hi => hpre i (by omega)) hm
    have hih := ih (hist ++ [c]) fun i hi => hpre i (by omega)
    simp only [realRunSteps, realStep, relocate, hacc, hih]
    exact congrArg (· :: _) (Option.map_congr fun e _ =>
      locate_congr (fun i hi => hpre i (by omega)) e hm)

/-! ### Lemma 3.16 and Theorem 3.3: Perfect Security and Main Guarantee -/

private theorem eval_idealRunSteps_append {m m' : ℕ} (A : Fin m' → IdealCell m)
    (cs₁ cs₂ : List (Fin m')) :
    (idealRunSteps A (cs₁ ++ cs₂)).eval =
      (idealRunSteps A cs₁).eval.bind fun (A₁, outs₁) =>
        (idealRunSteps A₁ cs₂).eval.map fun (A₂, outs₂) => (A₂, outs₁ ++ outs₂) := by
  induction cs₁ generalizing A with
  | nil =>
    simp only [idealRunSteps, List.nil_append, ProbComp.eval_pure, PMF.pure_bind, Prod.mk.eta]
    exact (PMF.map_id _).symm
  | cons c cs₁ ih =>
    simp [idealRunSteps, ih, PMF.bind_bind, PMF.map_bind, PMF.bind_map, PMF.map_comp,
      Function.comp_def]

private theorem eval_idealRunSteps_snoc {m m' : ℕ} (A : Fin m' → IdealCell m) (cs : List (Fin m'))
    (c : Fin m') :
    (idealRunSteps A (cs ++ [c])).eval =
      (idealRunSteps A cs).eval.bind fun (A₁, outs) =>
        (idealStep A₁ c).eval.map fun (A₂, out) => (A₂, outs ++ [out]) := by
  rw [eval_idealRunSteps_append]
  simp [idealRunSteps, PMF.map_comp, Function.comp_def]

private theorem eval_idealStep_stateToIdealArray {m m' : ℕ} (s : RelocationState m m')
    (hv : s.Valid) (c : Fin m') (hlen : m + s.history.length < m') :
    have : Nonempty {j : Fin m' // m + s.history.length ≤ j.val} :=
      ⟨⟨⟨m + s.history.length, hlen⟩, le_rfl⟩⟩
    (idealStep (stateToIdealArray s) c).eval =
      (PMF.uniformOfFintype {j : Fin m' // m + s.history.length ≤ j.val}).map fun j =>
        idealUpdate (stateToIdealArray s) c (endOfChain s (s.perm j.val)) := by
  intro
  let w := stepEquiv s hv ⟨⟨m + s.history.length, hlen⟩, le_rfl⟩
  have hne : (emptyPositions (stateToIdealArray s)).Nonempty := ⟨w.val, w.property⟩
  have : Nonempty (emptyPositions (stateToIdealArray s)) := ⟨w⟩
  simp only [idealStep, hne, ↓reduceDIte, ProbComp.eval_bind, ProbComp.eval_uniform,
    ProbComp.eval_pure, PMF.map]
  exact (PMF.uniformOfFintype_bind_bijective (stepEquiv s hv).bijective fun _ => rfl).symm

private noncomputable def realJointPMF (m m' : ℕ) (cs : List (Fin m')) (hm : m ≤ m') :
    PMF ((Fin m' → IdealCell m) × (Fin m → Fin m') × List (Option (Fin m'))) :=
  (PMF.uniformOfFintype (Equiv.Perm (Fin m'))).map fun perm =>
    let s₀ := init (m := m) perm
    let (s, outs) := realRunSteps s₀ cs hm
    (stateToIdealArray s, fun e => locate s₀ e hm, outs)

private noncomputable def idealJointPMF (m m' : ℕ) (cs : List (Fin m')) (hm : m ≤ m') :
    PMF ((Fin m' → IdealCell m) × (Fin m → Fin m') × List (Option (Fin m'))) :=
  letI : Nonempty (Fin m ↪ Fin m') := ⟨Fin.castLEEmb hm⟩
  (PMF.uniformOfFintype (Fin m ↪ Fin m')).bind fun emb =>
    (idealRunSteps (initIdealArray emb) cs).eval.map fun (A, outs) =>
      (A, ⇑emb, outs)

private theorem realRunSteps_snoc_stateToIdealArray {m m' : ℕ} (perm : Equiv.Perm (Fin m'))
    {cs : List (Fin m')} {c : Fin m'} (hnd_cs : cs.Nodup) (hc : c ∉ cs)
    (hlt : m + cs.length < m') (hm : m ≤ m') :
    (let s₀ := init (m := m) perm
     let x := realRunSteps s₀ (cs ++ [c]) hm
     (stateToIdealArray x.1, (fun e => locate s₀ e hm), x.2)) =
    (let s : RelocationState m m' := ⟨perm, cs⟩
     let outs := (realRunSteps (init (m := m) perm) cs hm).2
     let u := perm ⟨m + cs.length, hlt⟩
     let y := idealUpdate (stateToIdealArray s) c (endOfChain s u)
     (y.1, (fun e => locate (init (m := m) perm) e hm), outs ++ [y.2])) := by
  have hfst : (realRunSteps (init (m := m) perm) cs hm).1 = ⟨perm, cs⟩ := by
    simpa [init] using realRunSteps_fst (init (m := m) perm) cs hm
  obtain ⟨h₁, h₂⟩ :=
    Prod.mk.inj (stateToIdealArray_relocate (s := ⟨perm, cs⟩) ⟨hnd_cs, hlt.le⟩ hc hlt hm)
  simp only [realRunSteps_append (init (m := m) perm) cs [c] hm, hfst, realRunSteps, h₂]
  exact Prod.ext h₁ rfl

private theorem realJointPMF_eq_idealJointPMF {m m' : ℕ} (cs : List (Fin m')) (hm : m ≤ m')
    (hnd : cs.Nodup) (hlen : m + cs.length ≤ m') :
    realJointPMF m m' cs hm = idealJointPMF m m' cs hm := by
  induction cs using List.reverseRecOn with
  | nil =>
    have : Nonempty (Fin m ↪ Fin m') := ⟨Fin.castLEEmb hm⟩
    simp only [realJointPMF, idealJointPMF, realRunSteps, idealRunSteps,
      stateToIdealArray_init _ hm, locate_init _ hm, ProbComp.eval_pure, PMF.pure_map,
      ← Function.comp_def, PMF.bind_pure_comp]
    rw [← uniformOfFintype_perm_map_castLEEmb hm, PMF.map_comp]
    rfl
  | append_singleton cs c ih =>
    rw [List.nodup_append] at hnd
    obtain ⟨hnd_cs, _, hdisj⟩ := hnd
    have hc : c ∉ cs := fun hmc => hdisj c hmc c (List.mem_singleton_self c) rfl
    have hlt : m + cs.length < m' := by
      simp only [List.length_append, List.length_singleton] at hlen; omega
    have hideal : idealJointPMF m m' (cs ++ [c]) hm =
        (idealJointPMF m m' cs hm).bind fun (A, initPos, outs) =>
          (idealStep A c).eval.map fun (A', out) => (A', initPos, outs ++ [out]) := by
      simp only [idealJointPMF, eval_idealRunSteps_snoc, PMF.bind_bind, PMF.map_bind,
        PMF.bind_map, PMF.map_comp, Function.comp_def]
    rw [hideal, ← ih hnd_cs (Nat.le_of_lt hlt)]
    simp only [realJointPMF, PMF.bind_map, Function.comp_def]
    rw [← PMF.bind_pure_comp]
    simp only [Function.comp_def, realRunSteps_snoc_stateToIdealArray _ hnd_cs hc hlt hm]
    let f : Equiv.Perm (Fin m') → Fin m' →
        PMF ((Fin m' → IdealCell m) × (Fin m → Fin m') × List (Option (Fin m'))) :=
      fun perm u =>
        let s : RelocationState m m' := ⟨perm, cs⟩
        let outs := (realRunSteps (init (m := m) perm) cs hm).2
        let y := idealUpdate (stateToIdealArray s) c (endOfChain s u)
        PMF.pure (y.1, (fun e => locate (init (m := m) perm) e hm), outs ++ [y.2])
    have hf : ∀ π₁ π₂ : Equiv.Perm (Fin m'),
        (∀ i : Fin m', i.val < m + cs.length → π₁ i = π₂ i) → f π₁ = f π₂ := by
      intro π₁ π₂ hpre
      ext u
      have hloc : (fun e => locate (init (m := m) π₁) e hm) =
          (fun e => locate (init (m := m) π₂) e hm) :=
        funext fun e => locate_congr (fun i hi => hpre i (by simp at hi; omega)) e hm
      simp only [f, stateToIdealArray_congr hpre hm, endOfChain_congr hpre, hloc]
      simp only [init, realRunSteps_snd_congr [] cs hm (by simpa using hpre)]
    change (PMF.uniformOfFintype (Equiv.Perm (Fin m'))).bind
      (fun perm => f perm (perm ⟨m + cs.length, hlt⟩)) = _
    rw [uniformOfFintype_perm_bind_prefix hlt f hf]
    congr 1; ext perm
    have hfst : (realRunSteps (init (m := m) perm) cs hm).1 = ⟨perm, cs⟩ := by
      simpa [init] using realRunSteps_fst (init (m := m) perm) cs hm
    have hv : (⟨perm, cs⟩ : RelocationState m m').Valid := ⟨hnd_cs, Nat.le_of_lt hlt⟩
    rw [hfst, eval_idealStep_stateToIdealArray ⟨perm, cs⟩ hv c hlt,
      PMF.map_comp, ← PMF.bind_pure_comp]
    rfl

/-- **Lemma 3.16** of [WangRen2025] (pp. 16–17), perfect security: assuming `hm : m ≤ m'`, for any
sequence of `Q ≤ m' - m` distinct relocated physical positions `c : Fin Q → Fin m'` fixed in
advance, the real relocation experiment (Experiment 3.1, with an ideal uniformly random permutation)
and the ideal relocation experiment (Experiment 3.2) have exactly equal output laws. The hypothesis
`hm : m ≤ m'` is required alongside `hQ : Q ≤ m' - m` because `m' - m` is truncated subtraction in
`ℕ`. This is an information-theoretic statement; the paper's PRP instantiation and adaptive choices
of positions are not covered. -/
theorem eval_realExperiment_eq_idealExperiment {m m' Q : ℕ} {c : Fin Q → Fin m'}
    (hc : Function.Injective c) (hQ : Q ≤ m' - m) (hm : m ≤ m') :
    (realExperiment m m' Q c hm).eval = (idealExperiment m m' Q c hm).eval := by
  have hnd : (List.ofFn c).Nodup := List.nodup_ofFn.mpr hc
  have hlen : m + (List.ofFn c).length ≤ m' := by
    simp only [List.length_ofFn]; omega
  simpa [realJointPMF, idealJointPMF, realExperiment, idealExperiment,
    PMF.map_comp, PMF.map_bind, Function.comp_def, PMF.bind_pure_comp] using
    congrArg (PMF.map fun (_, initPos, outs) => RelocationOutput.mk initPos outs)
      (realJointPMF_eq_idealJointPMF (List.ofFn c) hm hnd hlen)

end Cslib.Crypto.Protocols.PIR.Preprocessing.Relocation

end
