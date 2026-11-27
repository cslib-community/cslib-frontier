/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.AhoCorasick.TrieModel
public import Mathlib.Data.Finset.Card

/-!
# Pure BFS Automaton Model and Root-Loop Specification

Defines the pure breadth-first automaton state `PBFS` (`delta`, `fail`, `outHead`, `outNext`,
FIFO `queue`), the linked output-chain walker `followOut`, the `TablesInv` queue-push lemma, and
the depth-1 root-loop specification `rootLoop_spec`.

## Main definitions

* `Cslib.Algorithms.WordRAM.AhoCorasick.followOut`: walk a linked `outNext` chain collecting state
  depths.
* `Cslib.Algorithms.WordRAM.AhoCorasick.PBFS`, `PBFS.build`: pure state and breadth-first builder
  for failure links, deterministic transitions, and output chains.
* `Cslib.Algorithms.WordRAM.AhoCorasick.TablesInv`, `RootLoopInv`: table and root-loop invariants.

## Main results

* `Cslib.Algorithms.WordRAM.AhoCorasick.tablesInv_push`: table preservation under pushing a new
  BFS node.
* `Cslib.Algorithms.WordRAM.AhoCorasick.rootStep_spec`,
  `Cslib.Algorithms.WordRAM.AhoCorasick.rootLoop_spec`: correctness of the depth-1 root pass.
-/

public section

namespace Cslib.Algorithms.WordRAM.AhoCorasick

open Cslib.Algorithms.Lean.AhoCorasick

/-! ## Pure BFS failure, next-move, and output-link construction -/

theorem parent_unique {σ : ℕ} {T : PTrie} (hT : TreeInv σ T)
    {u₁ c₁ u₂ c₂ : ℕ} (hu₁ : u₁ < T.numStates) (hc₁ : c₁ < σ)
    (hu₂ : u₂ < T.numStates) (hc₂ : c₂ < σ)
    (hpos : 0 < T.trie u₁ c₁) (heq : T.trie u₁ c₁ = T.trie u₂ c₂) :
    u₁ = u₂ ∧ c₁ = c₂ := by
  obtain ⟨_, hs₁⟩ := (hT.trie_spec u₁ hu₁ c₁ hc₁).resolve_left hpos.ne'
  obtain ⟨_, hs₂⟩ := (hT.trie_spec u₂ hu₂ c₂ hc₂).resolve_left (heq ▸ hpos).ne'
  rw [heq] at hs₁
  have hinj := List.append_inj' (hs₁.symm.trans hs₂) rfl
  exact ⟨hT.str_inj u₁ hu₁ u₂ hu₂ hinj.1, List.head_eq_of_cons_eq hinj.2⟩

/-- Fuel-bounded walker collecting state depths along a linked `outNext` chain stopping at `0`. -/
@[expose] def followOut (depth outNext : ℕ → ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | k + 1, q => if q = 0 then [] else depth q :: followOut depth outNext k (outNext q)

theorem followOut_zero_right (depth outNext : ℕ → ℕ) :
    ∀ k, followOut depth outNext k 0 = []
  | 0 => rfl
  | _ + 1 => rfl

theorem followOut_pos (depth outNext : ℕ → ℕ) {k q : ℕ} (hq : 0 < q) :
    followOut depth outNext (k + 1) q = depth q :: followOut depth outNext k (outNext q) := by
  simp only [followOut, hq.ne', ↓reduceIte]

theorem followOut_congr_on {depth outNext outNext' : ℕ → ℕ} {D : Finset ℕ}
    (hclosed : ∀ x ∈ D, 0 < x → outNext x ∈ D)
    (heq : ∀ x ∈ D, outNext' x = outNext x) :
    ∀ k, ∀ q ∈ D, followOut depth outNext' k q = followOut depth outNext k q
  | 0, _, _ => rfl
  | k + 1, q, hq => by
    rcases Nat.eq_zero_or_pos q with rfl | hpos
    · simp only [followOut_zero_right]
    · rw [followOut_pos _ _ hpos, followOut_pos _ _ hpos, heq q hq,
        followOut_congr_on hclosed heq k (outNext q) (hclosed q hq hpos)]

theorem followOut_fuel_eq {depth outNext : ℕ → ℕ} {D : Finset ℕ}
    (hstep : ∀ x ∈ D, 0 < x → outNext x ∈ D ∧ (outNext x = 0 ∨ depth (outNext x) < depth x)) :
    ∀ k₁ k₂, ∀ q ∈ D, (q = 0 ∨ depth q < k₁) → (q = 0 ∨ depth q < k₂) →
      followOut depth outNext k₁ q = followOut depth outNext k₂ q
  | 0, _, _, _, .inl rfl, _ => (followOut_zero_right _ _ _).symm
  | 0, _, _, _, .inr hlt, _ => absurd hlt (Nat.not_lt_zero _)
  | _ + 1, 0, _, _, _, .inl rfl => followOut_zero_right _ _ _
  | _ + 1, 0, _, _, _, .inr hlt => absurd hlt (Nat.not_lt_zero _)
  | k₁ + 1, m + 1, q, hq, h₁, h₂ => by
    rcases Nat.eq_zero_or_pos q with rfl | hpos
    · rfl
    · obtain ⟨hmem', hdec⟩ := hstep q hq hpos
      have hk₁ := h₁.resolve_left hpos.ne'
      have hk₂ := h₂.resolve_left hpos.ne'
      rw [followOut_pos _ _ hpos, followOut_pos _ _ hpos, followOut_fuel_eq hstep k₁ m
        (outNext q) hmem' (hdec.imp_right fun _ => by omega) (hdec.imp_right fun _ => by omega)]

/-- Pure breadth-first construction state for failure links, `delta`, output chains, and queue. -/
structure PBFS where
  /-- Deterministic next-move transition table `delta u c`. -/
  delta : ℕ → ℕ → ℕ
  /-- Failure-link table `fail u`. -/
  fail : ℕ → ℕ
  /-- Head of the linked output chain for state `u` (`0` if no matches). -/
  outHead : ℕ → ℕ
  /-- Next-entry link of the output chain starting from `u` (`0` at tail). -/
  outNext : ℕ → ℕ
  /-- Explicit FIFO queue buffer storing discovered nonzero trie states. -/
  queue : ℕ → ℕ
  /-- Index of the next state to dequeue from `queue`. -/
  qHead : ℕ
  /-- Number of enqueued nonzero states (`queue[0..qTail)`). -/
  qTail : ℕ

/-- Finset of all trie states discovered so far (`{0} ∪ queue[0..qTail)`). -/
@[expose] def PBFS.disc (B : PBFS) : Finset ℕ :=
  insert 0 ((Finset.range B.qTail).image B.queue)

/-- Finset of trie states already expanded up to queue position `h` (`{0} ∪ queue[0..h)`). -/
@[expose] def PBFS.expAt (B : PBFS) (h : ℕ) : Finset ℕ :=
  insert 0 ((Finset.range h).image B.queue)

/-- Initial all-zero `PBFS` state with an empty FIFO queue. -/
@[expose] def PBFS.init : PBFS where
  delta _ _ := 0
  fail _ := 0
  outHead _ := 0
  outNext _ := 0
  queue _ := 0
  qHead := 0
  qTail := 0

/-- Single root-level alphabet step processing symbol `a` from root `0`. -/
@[expose] def PBFS.rootStep (T : PTrie) (B : PBFS) (a : ℕ) : PBFS :=
  let s := T.trie 0 a
  if 0 < s then
    { delta := fun u c => if u = 0 ∧ c = a then s else B.delta u c
      fail := Function.update B.fail s 0
      outHead := Function.update B.outHead s (if 0 < T.isTerm s then s else 0)
      outNext := Function.update B.outNext s 0
      queue := Function.update B.queue B.qTail s
      qHead := B.qHead
      qTail := B.qTail + 1 }
  else
    { B with delta := fun u c => if u = 0 ∧ c = a then 0 else B.delta u c }

/-- Depth-1 BFS sweep iterating `PBFS.rootStep` across `k` symbols starting at `a`. -/
@[expose] def PBFS.rootLoop (T : PTrie) : ℕ → ℕ → PBFS → PBFS
  | 0, _, B => B
  | k + 1, a, B => PBFS.rootLoop T k (a + 1) (PBFS.rootStep T B a)

/-- Inner BFS step processing symbol `a` out of dequeued state `r` with failure link `fr`. -/
@[expose] def PBFS.innerStep (T : PTrie) (r fr : ℕ) (B : PBFS) (a : ℕ) : PBFS :=
  let s := T.trie r a
  let df := B.delta fr a
  if 0 < s then
    let oh := B.outHead df
    { delta := fun u c => if u = r ∧ c = a then s else B.delta u c
      fail := Function.update B.fail s df
      outHead := Function.update B.outHead s (if 0 < T.isTerm s then s else oh)
      outNext := Function.update B.outNext s oh
      queue := Function.update B.queue B.qTail s
      qHead := B.qHead
      qTail := B.qTail + 1 }
  else
    { B with delta := fun u c => if u = r ∧ c = a then df else B.delta u c }

/-- Inner BFS loop iterating `PBFS.innerStep` across `k` symbols starting at `a`. -/
@[expose] def PBFS.innerLoop (T : PTrie) (r fr : ℕ) : ℕ → ℕ → PBFS → PBFS
  | 0, _, B => B
  | k + 1, a, B => PBFS.innerLoop T r fr k (a + 1) (PBFS.innerStep T r fr B a)

/-- Fuel-bounded outer BFS queue expansion loop over alphabet size `σ`. -/
@[expose] def PBFS.outerLoop (T : PTrie) (σ : ℕ) : ℕ → PBFS → PBFS
  | 0, B => B
  | fuel + 1, B =>
    if B.qHead < B.qTail then
      let r := B.queue B.qHead
      let fr := B.fail r
      let B₁ := { B with qHead := B.qHead + 1 }
      let B₂ := PBFS.innerLoop T r fr σ 0 B₁
      PBFS.outerLoop T σ fuel B₂
    else B

/-- Full pure breadth-first automaton builder on trie `T` and alphabet size `σ`. -/
@[expose] def PBFS.build (T : PTrie) (σ : ℕ) : PBFS :=
  PBFS.outerLoop T σ T.numStates (PBFS.rootLoop T σ 0 PBFS.init)

theorem card_disc {B : PBFS}
    (hq_pos : ∀ i < B.qTail, 0 < B.queue i)
    (hq_inj : ∀ i < B.qTail, ∀ j < B.qTail, B.queue i = B.queue j → i = j) :
    B.disc.card = B.qTail + 1 := by
  dsimp only [PBFS.disc]
  have h0 : 0 ∉ (Finset.range B.qTail).image B.queue := fun h => by
    obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp h
    exact (hq_pos i (Finset.mem_range.mp hi)).ne' heq
  rw [Finset.card_insert_of_notMem h0, Finset.card_image_of_injOn
    (fun i hi j hj => hq_inj i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj)),
    Finset.card_range]

theorem mem_disc_lt {N : ℕ} {B : PBFS} (hN : 1 ≤ N)
    (hq_pos : ∀ i < B.qTail, 0 < B.queue i ∧ B.queue i < N) {x : ℕ} (hx : x ∈ B.disc) :
    x < N := by
  simp only [PBFS.disc, Finset.mem_insert, Finset.mem_image, Finset.mem_range] at hx
  rcases hx with rfl | ⟨i, hi, rfl⟩
  exacts [hN, (hq_pos i hi).2]

theorem qTail_lt_numStates {N : ℕ} {B : PBFS} (hN : 1 ≤ N)
    (hq_pos : ∀ i < B.qTail, 0 < B.queue i ∧ B.queue i < N)
    (hq_inj : ∀ i < B.qTail, ∀ j < B.qTail, B.queue i = B.queue j → i = j) :
    B.qTail < N := by
  have hle := Finset.card_le_card fun x hx => Finset.mem_range.2 (mem_disc_lt hN hq_pos hx)
  rw [card_disc (fun i hi => (hq_pos i hi).1) hq_inj, Finset.card_range] at hle
  omega

theorem qTail_succ_lt_numStates {N s : ℕ} {B : PBFS} (hN : 1 ≤ N)
    (hq_pos : ∀ i < B.qTail, 0 < B.queue i ∧ B.queue i < N)
    (hq_inj : ∀ i < B.qTail, ∀ j < B.qTail, B.queue i = B.queue j → i = j)
    (hs_lt : s < N) (hs_not : s ∉ B.disc) :
    B.qTail + 1 < N := by
  have hle := Finset.card_le_card (Finset.insert_subset (Finset.mem_range.2 hs_lt)
    fun x hx => Finset.mem_range.2 (mem_disc_lt hN hq_pos hx))
  rw [Finset.card_insert_of_notMem hs_not,
    card_disc (fun i hi => (hq_pos i hi).1) hq_inj, Finset.card_range] at hle
  omega

/-- Invariant capturing failure-link and linked output-chain correctness on all discovered
states `B.disc`. -/
structure TablesInv (P : List (List ℕ)) (T : PTrie) (B : PBFS) : Prop where
  zero_vals : B.fail 0 = 0 ∧ B.outHead 0 = 0 ∧ B.outNext 0 = 0
  fail_spec : ∀ x ∈ B.disc, 0 < x → B.fail x ∈ B.disc ∧ T.strOf (B.fail x) = failure P (T.strOf x)
  outHead_spec : ∀ x ∈ B.disc, B.outHead x ∈ B.disc ∧ T.depth (B.outHead x) ≤ T.depth x
  outNext_spec : ∀ x ∈ B.disc, 0 < x →
    B.outNext x ∈ B.disc ∧ (B.outNext x = 0 ∨ T.depth (B.outNext x) < T.depth x)
  follow_spec : ∀ x ∈ B.disc,
    followOut T.depth B.outNext T.numStates (B.outHead x) =
      (output P (T.strOf x)).map List.length

theorem tablesInv_push {P : List (List ℕ)} {σ : ℕ} {T : PTrie}
    (hT : TreeInv σ T)
    (hterm : ∀ u < T.numStates,
      T.isTerm u = if T.strOf u ≠ [] ∧ T.strOf u ∈ P then 1 else 0)
    {B B' : PBFS} (htab : TablesInv P T B)
    (hq_pos : ∀ i < B.qTail, 0 < B.queue i ∧ B.queue i < T.numStates)
    {s df : ℕ} (hs_pos : 0 < s) (hs_lt : s < T.numStates) (hs_not : s ∉ B.disc)
    (hdf_disc : df ∈ B.disc) (hdf_str : T.strOf df = failure P (T.strOf s))
    (hdisc' : B'.disc = insert s B.disc)
    (hfail' : B'.fail = Function.update B.fail s df)
    (houtHead' : B'.outHead =
      Function.update B.outHead s (if 0 < T.isTerm s then s else B.outHead df))
    (houtNext' : B'.outNext = Function.update B.outNext s (B.outHead df)) :
    TablesInv P T B' := by
  have hdf_lt : df < T.numStates := mem_disc_lt hT.one_le hq_pos hdf_disc
  have hs_str_ne : T.strOf s ≠ [] := hT.str_ne_nil s hs_pos hs_lt
  have hdf_depth_lt : T.depth df < T.depth s := by
    rw [hT.depth_eq df hdf_lt, hT.depth_eq s hs_lt, hdf_str]
    exact length_failure_lt P hs_str_ne
  obtain ⟨hoh_disc, hoh_depth⟩ := htab.outHead_spec df hdf_disc
  have hoh_lt : B.outHead df < T.numStates := mem_disc_lt hT.one_le hq_pos hoh_disc
  have hne_s {x : ℕ} (hx : x ∈ B.disc) : x ≠ s := ne_of_mem_of_not_mem hx hs_not
  have hcongr : ∀ k, ∀ q ∈ B.disc,
      followOut T.depth B'.outNext k q = followOut T.depth B.outNext k q :=
    followOut_congr_on (fun x hx hxp => (htab.outNext_spec x hx hxp).1) fun x hx => by
      rw [houtNext', Function.update_of_ne (hne_s hx)]
  refine ⟨?_, fun x hx hxp => ?_, fun x hx => ?_, fun x hx hxp => ?_, fun x hx => ?_⟩
  · simpa only [hfail', houtHead', houtNext', Function.update_of_ne hs_pos.ne] using
      htab.zero_vals
  · rw [hdisc'] at hx ⊢
    rcases Finset.mem_insert.mp hx with rfl | hx_old
    · simpa only [hfail', Function.update_self] using ⟨Finset.mem_insert_of_mem hdf_disc, hdf_str⟩
    · simpa only [hfail', Function.update_of_ne (hne_s hx_old)] using
        (htab.fail_spec x hx_old hxp).imp_left Finset.mem_insert_of_mem
  · rw [hdisc'] at hx ⊢
    rcases Finset.mem_insert.mp hx with rfl | hx_old
    · rw [houtHead', Function.update_self]
      split_ifs
      exacts [⟨Finset.mem_insert_self _ _, le_rfl⟩, ⟨Finset.mem_insert_of_mem hoh_disc, by omega⟩]
    · simpa only [houtHead', Function.update_of_ne (hne_s hx_old)] using
        (htab.outHead_spec x hx_old).imp_left Finset.mem_insert_of_mem
  · rw [hdisc'] at hx ⊢
    rcases Finset.mem_insert.mp hx with rfl | hx_old
    · simpa only [houtNext', Function.update_self] using
        ⟨Finset.mem_insert_of_mem hoh_disc, Or.inr (hoh_depth.trans_lt hdf_depth_lt)⟩
    · simpa only [houtNext', Function.update_of_ne (hne_s hx_old)] using
        (htab.outNext_spec x hx_old hxp).imp_left Finset.mem_insert_of_mem
  · rcases Finset.mem_insert.mp (hdisc' ▸ hx) with hxs | hx_old
    · subst x
      have hterm_s : T.isTerm s = if T.strOf s ∈ P then 1 else 0 := by
        simpa [hs_str_ne] using hterm s hs_lt
      rw [houtHead', Function.update_self, hterm_s, output_eq_of_ne_nil P hs_str_ne,
        List.map_append, ← hdf_str]
      by_cases hmemP : T.strOf s ∈ P <;> simp only [hmemP, ↓reduceIte]
      · simp only [Nat.zero_lt_one, ↓reduceIte, List.map_cons, List.map_nil, List.singleton_append]
        have hs_depth_le := depth_le_self hT s hs_lt
        obtain ⟨m, hN⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hT.one_le)
        rw [hN, followOut_pos _ _ hs_pos, houtNext', Function.update_self, ← houtNext',
          hcongr m (B.outHead df) hoh_disc, ← hT.depth_eq s hs_lt,
          followOut_fuel_eq (fun y hy hyp => htab.outNext_spec y hy hyp) m T.numStates
            (B.outHead df) hoh_disc (Or.inr (by omega))
            (Or.inr (lt_of_le_of_lt (depth_le_self hT _ hoh_lt) hoh_lt)),
          htab.follow_spec df hdf_disc]
      · simpa only [lt_self_iff_false, ↓reduceIte, List.map_nil, List.nil_append,
          hcongr T.numStates (B.outHead df) hoh_disc] using htab.follow_spec df hdf_disc
    · rw [houtHead', Function.update_of_ne (hne_s hx_old),
        hcongr T.numStates (B.outHead x) (htab.outHead_spec x hx_old).1,
        htab.follow_spec x hx_old]

theorem disc_push_queue (B : PBFS) (s : ℕ) :
    PBFS.disc { B with queue := Function.update B.queue B.qTail s, qTail := B.qTail + 1 } =
      insert s B.disc := by
  ext x
  simp only [PBFS.disc, Finset.range_add_one, Finset.image_insert, Function.update_self]
  rw [Finset.image_congr (fun i hi => Function.update_of_ne (Finset.mem_range.1 hi).ne s B.queue)]
  simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_range]
  tauto

/-- Loop invariant maintained after processing the first `a` symbols during `PBFS.rootLoop`. -/
structure RootLoopInv (P : List (List ℕ)) (σ : ℕ) (T : PTrie) (a : ℕ) (B : PBFS) :
    Prop where
  qHead_zero : B.qHead = 0
  q_bounds : ∀ i < B.qTail, 0 < B.queue i ∧ B.queue i < T.numStates ∧ T.depth (B.queue i) = 1
  q_inj : ∀ i < B.qTail, ∀ j < B.qTail, B.queue i = B.queue j → i = j
  disc_iff : ∀ w < T.numStates, w ∈ B.disc ↔ w = 0 ∨ ∃ c < a, T.trie 0 c = w
  delta_zero : ∀ c < a, B.delta 0 c ∈ B.disc ∧ T.strOf (B.delta 0 c) = nextMove P [] c
  tables : TablesInv P T B

theorem rootStep_spec {P : List (List ℕ)} {σ : ℕ} {T : PTrie}
    (hT : TreeInv σ T)
    (hchar : ∀ u < T.numStates, ∀ a < σ, IsNode P (T.strOf u ++ [a]) ↔ 0 < T.trie u a)
    (hterm : ∀ u < T.numStates,
      T.isTerm u = if T.strOf u ≠ [] ∧ T.strOf u ∈ P then 1 else 0)
    {a : ℕ} (ha : a < σ) {B : PBFS} (hinv : RootLoopInv P σ T a B) :
    RootLoopInv P σ T (a + 1) (PBFS.rootStep T B a) := by
  have htrie_iff := hchar 0 hT.one_le a ha
  rw [hT.str_zero, List.nil_append] at htrie_iff
  set s := T.trie 0 a
  by_cases hs_pos : 0 < s
  · have hs_lt : s < T.numStates := hT.trie_lt 0 hT.one_le a ha
    obtain ⟨_, hs_str⟩ := (hT.trie_spec 0 hT.one_le a ha).resolve_left hs_pos.ne'
    rw [hT.str_zero, List.nil_append] at hs_str
    have hs_depth : T.depth s = 1 := by simp [hT.depth_eq s hs_lt, s, hs_str]
    have hs_not : s ∉ B.disc := fun hmem => by
      rcases (hinv.disc_iff s hs_lt).mp hmem with hs0 | ⟨c, hca, htc⟩
      · exact hs_pos.ne' hs0
      · exact hca.ne
          (parent_unique hT hT.one_le ha hT.one_le (hca.trans ha) hs_pos htc.symm).2.symm
    have hdisc' : (PBFS.rootStep T B a).disc = insert s B.disc := by
      simp only [PBFS.rootStep, s, hs_pos, ↓reduceIte]
      exact disc_push_queue B s
    have hnode_a : IsNode P [a] := htrie_iff.mpr hs_pos
    have hfail_s : T.strOf 0 = failure P (T.strOf s) := by
      rw [hT.str_zero, hs_str, failure_eq_nil_of_length_le_one P (by simp)]
    obtain ⟨-, h0_oh, -⟩ := hinv.tables.zero_vals
    refine
      { qHead_zero := by simp only [PBFS.rootStep, s, hs_pos, ↓reduceIte, hinv.qHead_zero]
        q_bounds := fun i hi => by
          simp only [PBFS.rootStep, s, hs_pos, ↓reduceIte] at hi ⊢
          rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hlt | rfl
          · exact (Function.update_of_ne hlt.ne s B.queue).symm ▸ hinv.q_bounds i hlt
          · rw [Function.update_self]
            exact ⟨hs_pos, hs_lt, hs_depth⟩
        q_inj := fun i hi j hj hij => by
          simp only [PBFS.rootStep, s, hs_pos, ↓reduceIte] at hi hj hij
          have hold : ∀ k < B.qTail, B.queue k ≠ s := fun k hk h => hs_not
            (h ▸ Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_range.2 hk)))
          rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hil | rfl <;>
            rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hjl | rfl
          · exact hinv.q_inj i hil j hjl
              (by simpa only [Function.update_of_ne hil.ne, Function.update_of_ne hjl.ne] using hij)
          · exact absurd (by simpa only [Function.update_of_ne hil.ne, Function.update_self]
              using hij) (hold i hil)
          · exact absurd (by simpa only [Function.update_self, Function.update_of_ne hjl.ne]
              using hij.symm) (hold j hjl)
          · rfl
        disc_iff := fun w hw => by
          rw [hdisc', Finset.mem_insert, hinv.disc_iff w hw, Nat.exists_lt_succ_right,
            @eq_comm _ w s]
          exact or_left_comm.trans (or_congr_right or_comm)
        delta_zero := fun c hc => by
          rw [hdisc']
          simp only [PBFS.rootStep, s, hs_pos, ↓reduceIte]
          rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hc) with hlt | rfl
          · simp only [true_and, hlt.ne, ↓reduceIte]
            exact (hinv.delta_zero c hlt).imp_left Finset.mem_insert_of_mem
          · simp only [and_self, ↓reduceIte]
            exact ⟨Finset.mem_insert_self s _, by
              rw [hs_str, nextMove_of_isNode hnode_a, List.nil_append]⟩
        tables := tablesInv_push hT hterm hinv.tables
          (fun i hi => (hinv.q_bounds i hi).imp_right And.left)
          hs_pos hs_lt hs_not (Finset.mem_insert_self 0 _) hfail_s hdisc'
          (by simp only [PBFS.rootStep, s, hs_pos, ↓reduceIte])
          (by simp only [PBFS.rootStep, s, hs_pos, ↓reduceIte, h0_oh])
          (by simp only [PBFS.rootStep, s, hs_pos, ↓reduceIte, h0_oh]) }
  · dsimp only [PBFS.rootStep]
    simp only [s, hs_pos, ↓reduceIte]
    have hs0 : s = 0 := by omega
    have hnot_node : ¬IsNode P ([] ++ [a]) := by
      simpa only [List.nil_append] using mt htrie_iff.mp hs_pos
    refine
      { qHead_zero := hinv.qHead_zero
        q_bounds := hinv.q_bounds
        q_inj := hinv.q_inj
        disc_iff := fun w hw => by
          change w ∈ B.disc ↔ _
          rw [hinv.disc_iff w hw, Nat.exists_lt_succ_right, ← or_assoc]
          exact Iff.symm (or_iff_left_of_imp fun h => Or.inl (h.symm.trans hs0))
        delta_zero := fun c hc => by
          change (if 0 = 0 ∧ c = a then 0 else B.delta 0 c) ∈ B.disc ∧ _
          rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hc) with hlt | rfl
          · simp only [true_and, hlt.ne, ↓reduceIte]
            exact hinv.delta_zero c hlt
          · simp only [and_self, ↓reduceIte]
            exact ⟨Finset.mem_insert_self 0 _,
              hT.str_zero.trans (nextMove_of_not_isNode_of_eq_nil hnot_node rfl).symm⟩
        tables := ⟨hinv.tables.zero_vals, hinv.tables.fail_spec, hinv.tables.outHead_spec,
          hinv.tables.outNext_spec, hinv.tables.follow_spec⟩ }

theorem rootLoop_spec {P : List (List ℕ)} {σ : ℕ} {T : PTrie}
    (hT : TreeInv σ T)
    (hchar : ∀ u < T.numStates, ∀ a < σ, IsNode P (T.strOf u ++ [a]) ↔ 0 < T.trie u a)
    (hterm : ∀ u < T.numStates,
      T.isTerm u = if T.strOf u ≠ [] ∧ T.strOf u ∈ P then 1 else 0) :
    ∀ k a B, a + k ≤ σ → RootLoopInv P σ T a B →
      RootLoopInv P σ T (a + k) (PBFS.rootLoop T k a B)
  | 0, a, B, _, hinv => by simpa only [PBFS.rootLoop, Nat.add_zero] using hinv
  | k + 1, a, B, hle, hinv => by
    simpa only [PBFS.rootLoop, Nat.succ_add, Nat.add_succ] using
      rootLoop_spec hT hchar hterm k (a + 1) (PBFS.rootStep T B a) (by omega)
        (rootStep_spec hT hchar hterm (by omega) hinv)

end Cslib.Algorithms.WordRAM.AhoCorasick
