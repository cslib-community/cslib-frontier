/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.AhoCorasick.BFSModel

/-!
# Correctness of the Pure Breadth-First Aho–Corasick Automaton

Proves that `PBFS.build (PTrie.build P) σ` satisfies `AutomatonInv`: `fail`, deterministic
next-move table `delta`, and linked output chains `(outHead, outNext)` agree with the reference
Aho–Corasick failure/output specification from `Cslib.Algorithms.Lean.AhoCorasick`.

## Main definitions

* `Cslib.Algorithms.WordRAM.AhoCorasick.BFSInv`, `InnerLoopInv`: outer and inner BFS loop
  invariants.
* `Cslib.Algorithms.WordRAM.AhoCorasick.AutomatonInv`: completed automaton invariant relating
  `delta`, `fail`, `outHead`, `outNext`, and `followOut` to `failure` and `out`.

## Main results

* `Cslib.Algorithms.WordRAM.AhoCorasick.innerStep_spec`,
  `Cslib.Algorithms.WordRAM.AhoCorasick.outerStep_spec`: inner and outer BFS induction steps.
* `Cslib.Algorithms.WordRAM.AhoCorasick.rootLoopInv_init`,
  `Cslib.Algorithms.WordRAM.AhoCorasick.bfsInv_rootLoop`: transition from depth-1 pass to `BFSInv`.
* `Cslib.Algorithms.WordRAM.AhoCorasick.build_bfs_spec`: end-to-end purity certificate.
-/

public section

namespace Cslib.Algorithms.WordRAM.AhoCorasick

open Cslib.Algorithms.Lean.AhoCorasick

/-- Outer breadth-first loop invariant linking queue monotonicity, expanded nodes, `delta`, and
`TablesInv`. -/
structure BFSInv (P : List (List ℕ)) (σ : ℕ) (T : PTrie) (B : PBFS) : Prop where
  qHead_le : B.qHead ≤ B.qTail
  q_bounds : ∀ i < B.qTail, 0 < B.queue i ∧ B.queue i < T.numStates
  q_inj : ∀ i < B.qTail, ∀ j < B.qTail, B.queue i = B.queue j → i = j
  disc_iff : ∀ w < T.numStates,
    w ∈ B.disc ↔ w = 0 ∨ ∃ u ∈ B.expAt B.qHead, ∃ c < σ, T.trie u c = w
  q_mono : ∀ i j, i ≤ j → j < B.qTail → T.depth (B.queue i) ≤ T.depth (B.queue j)
  q_depth_ub : ∀ j < B.qTail, B.qHead < B.qTail →
    T.depth (B.queue j) ≤ T.depth (B.queue B.qHead) + 1
  lt_depth_mem_exp : ∀ v < T.numStates, B.qHead < B.qTail →
    T.depth v < T.depth (B.queue B.qHead) → v ∈ B.expAt B.qHead
  delta_spec : ∀ u ∈ B.expAt B.qHead, ∀ c < σ,
    B.delta u c ∈ B.disc ∧ T.strOf (B.delta u c) = nextMove P (T.strOf u) c
  tables : TablesInv P T B

/-- Inner loop invariant while scanning characters `0..a-1` of dequeued state `r`. -/
structure InnerLoopInv (P : List (List ℕ)) (σ : ℕ) (T : PTrie)
    (qHead₀ r fr a : ℕ) (B : PBFS) : Prop where
  qHead_eq : B.qHead = qHead₀ + 1
  qHead_le : B.qHead ≤ B.qTail
  r_eq : B.queue qHead₀ = r
  q_bounds : ∀ i < B.qTail, 0 < B.queue i ∧ B.queue i < T.numStates
  q_inj : ∀ i < B.qTail, ∀ j < B.qTail, B.queue i = B.queue j → i = j
  disc_iff : ∀ w < T.numStates,
    w ∈ B.disc ↔ w = 0 ∨ (∃ u ∈ B.expAt qHead₀, ∃ c < σ, T.trie u c = w) ∨
      (∃ c < a, T.trie r c = w)
  q_mono : ∀ i j, i ≤ j → j < B.qTail → T.depth (B.queue i) ≤ T.depth (B.queue j)
  q_depth_ub : ∀ j < B.qTail, T.depth (B.queue j) ≤ T.depth r + 1
  lt_depth_mem_exp : ∀ v < T.numStates, T.depth v < T.depth r → v ∈ B.expAt qHead₀
  le_depth_mem_disc : ∀ v < T.numStates, T.depth v ≤ T.depth r → v ∈ B.disc
  delta_exp : ∀ u ∈ B.expAt qHead₀, ∀ c < σ,
    B.delta u c ∈ B.disc ∧ T.strOf (B.delta u c) = nextMove P (T.strOf u) c
  delta_r : ∀ c < a, B.delta r c ∈ B.disc ∧ T.strOf (B.delta r c) = nextMove P (T.strOf r) c
  fr_mem : fr ∈ B.expAt qHead₀
  fr_str : T.strOf fr = failure P (T.strOf r)
  tables : TablesInv P T B

private theorem expAt_congr {B B' : PBFS} {h : ℕ} (heq : ∀ i < h, B'.queue i = B.queue i) :
    B'.expAt h = B.expAt h := by
  ext x
  simp only [PBFS.expAt, Finset.mem_insert, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro (rfl | ⟨i, hi, hq⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨i, hi, (heq i hi).symm.trans hq⟩
  · rintro (rfl | ⟨i, hi, hq⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨i, hi, (heq i hi).trans hq⟩

theorem innerStep_spec {P : List (List ℕ)} {σ : ℕ} {T : PTrie}
    (hT : TreeInv σ T)
    (hchar : ∀ u < T.numStates, ∀ a < σ, IsNode P (T.strOf u ++ [a]) ↔ 0 < T.trie u a)
    (hterm : ∀ u < T.numStates,
      T.isTerm u = if T.strOf u ≠ [] ∧ T.strOf u ∈ P then 1 else 0)
    {qHead₀ r fr a : ℕ} (ha : a < σ) {B : PBFS}
    (hinv : InnerLoopInv P σ T qHead₀ r fr a B) :
    InnerLoopInv P σ T qHead₀ r fr (a + 1) (PBFS.innerStep T r fr B a) := by
  have hqh_eq := hinv.qHead_eq
  have hqh_le := hinv.qHead_le
  have hqh_lt : qHead₀ < B.qTail := by omega
  obtain ⟨hr_pos, hr_lt⟩ := by
    have h := hinv.q_bounds qHead₀ hqh_lt
    rwa [hinv.r_eq] at h
  have hr_ne_nil : T.strOf r ≠ [] := hT.str_ne_nil r hr_pos hr_lt
  have hr_not_exp : r ∉ B.expAt qHead₀ := by
    simp only [PBFS.expAt, Finset.mem_insert, Finset.mem_image, Finset.mem_range, not_or,
      not_exists, not_and]
    refine ⟨by omega, fun i hi hqi => ?_⟩
    have := hinv.q_inj i (lt_trans hi hqh_lt) qHead₀ hqh_lt (hqi.trans hinv.r_eq.symm)
    omega
  have hr_ne_fr : r ≠ fr := fun h => hr_not_exp (h ▸ hinv.fr_mem)
  obtain ⟨hdf_disc_raw, hdf_str_raw⟩ := hinv.delta_exp fr hinv.fr_mem a ha
  set df := B.delta fr a
  have hdf_lt : df < T.numStates := mem_disc_lt hT.one_le hinv.q_bounds hdf_disc_raw
  have hdf_fail_ra : T.strOf df = failure P (T.strOf r ++ [a]) := by
    rw [hdf_str_raw, hinv.fr_str, failure_append_singleton P hr_ne_nil a]
  have htrie_iff := hchar r hr_lt a ha
  dsimp only [PBFS.innerStep]
  set s := T.trie r a
  by_cases hs_pos : 0 < s
  · simp only [hs_pos, ↓reduceIte]
    have hs_lt : s < T.numStates := hT.trie_lt r hr_lt a ha
    rcases hT.trie_spec r hr_lt a ha with h0 | ⟨_, hs_str⟩
    · omega
    · have hs_depth : T.depth s = T.depth r + 1 := by
        rw [hT.depth_eq s hs_lt, hs_str, List.length_append, List.length_singleton,
          ← hT.depth_eq r hr_lt]
      have hs_not : s ∉ B.disc := by
        intro hmem
        rcases (hinv.disc_iff s hs_lt).mp hmem with hs0 | ⟨u, hu_exp, c, hc, htuc⟩ | ⟨c, hca, htrc⟩
        · omega
        · have hu_lt : u < T.numStates := by
            simp only [PBFS.expAt, Finset.mem_insert, Finset.mem_image, Finset.mem_range] at hu_exp
            rcases hu_exp with rfl | ⟨i, hi, rfl⟩
            · exact hT.one_le
            · exact (hinv.q_bounds i (lt_trans hi hqh_lt)).2
          have ⟨hru, _⟩ := parent_unique hT hr_lt ha hu_lt hc hs_pos htuc.symm
          exact hr_not_exp (hru ▸ hu_exp)
        · have ⟨_, hca_eq⟩ :=
            parent_unique hT hr_lt ha hr_lt (lt_trans hca ha) hs_pos htrc.symm
          omega
      set oh := B.outHead df
      set B' : PBFS :=
        { delta := fun u c => if u = r ∧ c = a then s else B.delta u c
          fail := Function.update B.fail s df
          outHead := Function.update B.outHead s (if 0 < T.isTerm s then s else oh)
          outNext := Function.update B.outNext s oh
          queue := Function.update B.queue B.qTail s
          qHead := B.qHead
          qTail := B.qTail + 1 }
      have hdisc' : B'.disc = insert s B.disc := disc_push_queue B s
      have hexp' : B'.expAt qHead₀ = B.expAt qHead₀ :=
        expAt_congr fun i hi => Function.update_of_ne (by omega) _ _
      have hnode_ra : IsNode P (T.strOf r ++ [a]) := htrie_iff.mpr hs_pos
      refine
        { qHead_eq := hinv.qHead_eq
          qHead_le := by dsimp only [B']; omega
          r_eq := by
            dsimp only [B']
            rw [Function.update_of_ne (by omega)]
            exact hinv.r_eq
          q_bounds := fun i hi => by
            dsimp only [B'] at hi ⊢
            rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hlt | rfl
            · rw [Function.update_of_ne (by omega)]; exact hinv.q_bounds i hlt
            · rw [Function.update_self]; exact ⟨hs_pos, hs_lt⟩
          q_inj := fun i hi j hj hij => by
            dsimp only [B'] at hi hj hij
            rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hil | rfl <;>
              rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hjl | rfl
            · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)] at hij
              exact hinv.q_inj i hil j hjl hij
            · rw [Function.update_of_ne (by omega), Function.update_self] at hij
              exfalso; apply hs_not; rw [← hij]
              exact Finset.mem_insert_of_mem
                (Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hil, rfl⟩)
            · rw [Function.update_self, Function.update_of_ne (by omega)] at hij
              exfalso; apply hs_not; rw [hij]
              exact Finset.mem_insert_of_mem
                (Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hjl, rfl⟩)
            · rfl
          disc_iff := fun w hw => by
            rw [hdisc', hexp', Finset.mem_insert, hinv.disc_iff w hw]
            constructor
            · rintro (rfl | rfl | hexp | ⟨c, hca, htc⟩)
              · exact Or.inr (Or.inr ⟨a, Nat.lt_succ_self a, rfl⟩)
              · exact Or.inl rfl
              · exact Or.inr (Or.inl hexp)
              · exact Or.inr (Or.inr ⟨c, Nat.lt_succ_of_lt hca, htc⟩)
            · rintro (rfl | hexp | ⟨c, hca, htc⟩)
              · exact Or.inr (Or.inl rfl)
              · exact Or.inr (Or.inr (Or.inl hexp))
              · rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hca) with hlt | rfl
                · exact Or.inr (Or.inr (Or.inr ⟨c, hlt, htc⟩))
                · exact Or.inl htc.symm
          q_mono := fun i j hij hj => by
            dsimp only [B'] at hj ⊢
            rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hjl | rfl
            · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
              exact hinv.q_mono i j hij hjl
            · rcases Nat.lt_or_eq_of_le hij with hil | rfl
              · rw [Function.update_of_ne (by omega), Function.update_self, hs_depth]
                exact hinv.q_depth_ub i hil
              · exact Nat.le_refl _
          q_depth_ub := fun j hj => by
            dsimp only [B'] at hj ⊢
            rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hjl | rfl
            · rw [Function.update_of_ne (by omega)]; exact hinv.q_depth_ub j hjl
            · rw [Function.update_self, hs_depth]
          lt_depth_mem_exp := fun v hv hdv => by
            rw [hexp']; exact hinv.lt_depth_mem_exp v hv hdv
          le_depth_mem_disc := fun v hv hdv => by
            rw [hdisc']; exact Finset.mem_insert_of_mem (hinv.le_depth_mem_disc v hv hdv)
          delta_exp := fun u hu c hc => by
            change u ∈ B'.expAt qHead₀ at hu
            rw [hexp'] at hu
            rw [hdisc']
            dsimp only [B']
            have hur : ¬(u = r ∧ c = a) := fun h => hr_not_exp (h.1 ▸ hu)
            simp only [hur, ↓reduceIte]
            obtain ⟨h1, h2⟩ := hinv.delta_exp u hu c hc
            exact ⟨Finset.mem_insert_of_mem h1, h2⟩
          delta_r := fun c hc => by
            rw [hdisc']
            dsimp only [B']
            rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hc) with hlt | rfl
            · have hne : c ≠ a := by omega
              simp only [true_and, hne, ↓reduceIte]
              obtain ⟨h1, h2⟩ := hinv.delta_r c hlt
              exact ⟨Finset.mem_insert_of_mem h1, h2⟩
            · simp only [and_self, ↓reduceIte]
              refine ⟨Finset.mem_insert_self s _, ?_⟩
              rw [hs_str, nextMove_of_isNode hnode_ra]
          fr_mem := by
            rw [hexp']; exact hinv.fr_mem
          fr_str := hinv.fr_str
          tables := tablesInv_push hT hterm hinv.tables hinv.q_bounds
            hs_pos hs_lt hs_not hdf_disc_raw (hs_str ▸ hdf_fail_ra) hdisc' rfl rfl rfl }
  · simp only [hs_pos, ↓reduceIte]
    have hs0 : s = 0 := by omega
    have hnot_node : ¬IsNode P (T.strOf r ++ [a]) := mt htrie_iff.mp hs_pos
    refine
      { qHead_eq := hinv.qHead_eq
        qHead_le := hinv.qHead_le
        r_eq := hinv.r_eq
        q_bounds := hinv.q_bounds
        q_inj := hinv.q_inj
        disc_iff := fun w hw => by
          change w ∈ B.disc ↔ _
          rw [hinv.disc_iff w hw]
          constructor
          · rintro (rfl | hexp | ⟨c, hca, htc⟩)
            · exact Or.inl rfl
            · exact Or.inr (Or.inl hexp)
            · exact Or.inr (Or.inr ⟨c, Nat.lt_succ_of_lt hca, htc⟩)
          · rintro (rfl | hexp | ⟨c, hca, htc⟩)
            · exact Or.inl rfl
            · exact Or.inr (Or.inl hexp)
            · rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hca) with hlt | rfl
              · exact Or.inr (Or.inr ⟨c, hlt, htc⟩)
              · exact Or.inl (htc.symm.trans hs0)
        q_mono := hinv.q_mono
        q_depth_ub := hinv.q_depth_ub
        lt_depth_mem_exp := hinv.lt_depth_mem_exp
        le_depth_mem_disc := hinv.le_depth_mem_disc
        delta_exp := fun u hu c hc => by
          change (if u = r ∧ c = a then df else B.delta u c) ∈ B.disc ∧ _
          have hur : ¬(u = r ∧ c = a) := fun h => hr_not_exp (h.1 ▸ hu)
          simp only [hur, ↓reduceIte]
          exact hinv.delta_exp u hu c hc
        delta_r := fun c hc => by
          change (if r = r ∧ c = a then df else B.delta r c) ∈ B.disc ∧ _
          rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hc) with hlt | rfl
          · have hne : c ≠ a := by omega
            simp only [true_and, hne, ↓reduceIte]
            exact hinv.delta_r c hlt
          · simp only [and_self, ↓reduceIte]
            refine ⟨hdf_disc_raw, ?_⟩
            rw [hdf_str_raw, hinv.fr_str, nextMove_of_not_isNode hnot_node hr_ne_nil]
        fr_mem := hinv.fr_mem
        fr_str := hinv.fr_str
        tables := ⟨hinv.tables.zero_vals, hinv.tables.fail_spec, hinv.tables.outHead_spec,
          hinv.tables.outNext_spec, hinv.tables.follow_spec⟩ }

private theorem innerLoop_spec {P : List (List ℕ)} {σ : ℕ} {T : PTrie}
    (hT : TreeInv σ T)
    (hchar : ∀ u < T.numStates, ∀ a < σ, IsNode P (T.strOf u ++ [a]) ↔ 0 < T.trie u a)
    (hterm : ∀ u < T.numStates,
      T.isTerm u = if T.strOf u ≠ [] ∧ T.strOf u ∈ P then 1 else 0)
    (qHead₀ r fr : ℕ) :
    ∀ k a B, a + k ≤ σ → InnerLoopInv P σ T qHead₀ r fr a B →
      InnerLoopInv P σ T qHead₀ r fr (a + k) (PBFS.innerLoop T r fr k a B)
  | 0, a, B, _, hinv => by simpa only [PBFS.innerLoop, Nat.add_zero] using hinv
  | k + 1, a, B, hle, hinv => by
    have hstep := innerStep_spec hT hchar hterm (by omega) hinv
    have ih :=
      innerLoop_spec hT hchar hterm qHead₀ r fr k (a + 1) (PBFS.innerStep T r fr B a)
        (by omega) hstep
    rwa [Nat.add_right_comm, ← PBFS.innerLoop] at ih

private theorem le_depth_mem_disc_of_bfsInv {P : List (List ℕ)} {σ : ℕ} {T : PTrie}
    (hT : TreeInv σ T) {B : PBFS} (hinv : BFSInv P σ T B) (hlt : B.qHead < B.qTail) :
    ∀ v < T.numStates, T.depth v ≤ T.depth (B.queue B.qHead) → v ∈ B.disc := by
  intro v hv hdv
  rcases Nat.eq_zero_or_pos v with rfl | hv_pos
  · exact Finset.mem_insert_self 0 _
  · obtain ⟨u, huv, c, hc, htuc, hstr⟩ := hT.parent_exists v hv_pos hv
    have hu_lt : u < T.numStates := lt_trans huv hv
    have hdu : T.depth u < T.depth (B.queue B.qHead) := by
      rw [hT.depth_eq v hv, hstr, List.length_append, List.length_singleton,
        ← hT.depth_eq u hu_lt] at hdv
      omega
    have hu_exp := hinv.lt_depth_mem_exp u hu_lt hlt hdu
    exact (hinv.disc_iff v hv).mpr (Or.inr ⟨u, hu_exp, c, hc, htuc⟩)

private theorem expAt_succ (B : PBFS) (h : ℕ) :
    B.expAt (h + 1) = insert (B.queue h) (B.expAt h) := by
  ext x
  simp only [PBFS.expAt, Finset.mem_insert, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro (rfl | ⟨i, hi, rfl⟩)
    · exact Or.inr (Or.inl rfl)
    · rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hlt | rfl
      · exact Or.inr (Or.inr ⟨i, hlt, rfl⟩)
      · exact Or.inl rfl
  · rintro (rfl | rfl | ⟨i, hi, rfl⟩)
    · exact Or.inr ⟨h, Nat.lt_succ_self h, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨i, Nat.lt_succ_of_lt hi, rfl⟩

theorem innerLoopInv_of_bfsInv {P : List (List ℕ)} {σ : ℕ} {T : PTrie}
    (hT : TreeInv σ T) {B : PBFS} (hinv : BFSInv P σ T B) (hlt : B.qHead < B.qTail) :
    InnerLoopInv P σ T B.qHead (B.queue B.qHead) (B.fail (B.queue B.qHead)) 0
      { B with qHead := B.qHead + 1 } := by
  set qh := B.qHead
  set r := B.queue qh
  set fr := B.fail r
  obtain ⟨hr_pos, hr_lt⟩ := hinv.q_bounds qh hlt
  have hr_disc : r ∈ B.disc :=
    Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨qh, Finset.mem_range.mpr hlt, rfl⟩)
  obtain ⟨hfr_disc, hfr_str⟩ := hinv.tables.fail_spec r hr_disc hr_pos
  have hfr_lt : fr < T.numStates := mem_disc_lt hT.one_le hinv.q_bounds hfr_disc
  have hfr_depth : T.depth fr < T.depth r := by
    rw [hT.depth_eq fr hfr_lt, hT.depth_eq r hr_lt, hfr_str]
    exact length_failure_lt P (hT.str_ne_nil r hr_pos hr_lt)
  have hfr_exp : fr ∈ B.expAt qh := hinv.lt_depth_mem_exp fr hfr_lt hlt hfr_depth
  exact
    { qHead_eq := rfl
      qHead_le := by dsimp only; omega
      r_eq := rfl
      q_bounds := hinv.q_bounds
      q_inj := hinv.q_inj
      disc_iff := fun w hw => by
        change w ∈ B.disc ↔ _
        rw [hinv.disc_iff w hw]
        simp only [Nat.not_lt_zero, false_and, exists_false, or_false]
        rfl
      q_mono := hinv.q_mono
      q_depth_ub := fun j hj => hinv.q_depth_ub j hj hlt
      lt_depth_mem_exp := fun v hv hdv => hinv.lt_depth_mem_exp v hv hlt hdv
      le_depth_mem_disc := le_depth_mem_disc_of_bfsInv hT hinv hlt
      delta_exp := hinv.delta_spec
      delta_r := fun _ hc => absurd hc (Nat.not_lt_zero _)
      fr_mem := hfr_exp
      fr_str := hfr_str
      tables := ⟨hinv.tables.zero_vals, hinv.tables.fail_spec, hinv.tables.outHead_spec,
        hinv.tables.outNext_spec, hinv.tables.follow_spec⟩ }

theorem outerStep_spec {P : List (List ℕ)} {σ : ℕ} {T : PTrie}
    (hT : TreeInv σ T)
    (hchar : ∀ u < T.numStates, ∀ a < σ, IsNode P (T.strOf u ++ [a]) ↔ 0 < T.trie u a)
    (hterm : ∀ u < T.numStates,
      T.isTerm u = if T.strOf u ≠ [] ∧ T.strOf u ∈ P then 1 else 0)
    {B : PBFS} (hinv : BFSInv P σ T B) (hlt : B.qHead < B.qTail) :
    let r := B.queue B.qHead
    let fr := B.fail r
    let B₂ := PBFS.innerLoop T r fr σ 0 { B with qHead := B.qHead + 1 }
    BFSInv P σ T B₂ ∧ B₂.qHead = B.qHead + 1 := by
  set qh := B.qHead
  set r := B.queue qh
  set fr := B.fail r
  set B₁ : PBFS := { B with qHead := qh + 1 }
  have hInner₀ : InnerLoopInv P σ T qh r fr 0 B₁ := innerLoopInv_of_bfsInv hT hinv hlt
  have hInner := innerLoop_spec hT hchar hterm qh r fr σ 0 B₁ (by omega) hInner₀
  rw [Nat.zero_add] at hInner
  set B₂ := PBFS.innerLoop T r fr σ 0 B₁
  have hexp₂ : B₂.expAt B₂.qHead = insert r (B₂.expAt qh) := by
    rw [hInner.qHead_eq, expAt_succ, hInner.r_eq]
  change BFSInv P σ T B₂ ∧ B₂.qHead = B.qHead + 1
  refine ⟨?_, hInner.qHead_eq⟩
  refine
    { qHead_le := hInner.qHead_le
      q_bounds := hInner.q_bounds
      q_inj := hInner.q_inj
      disc_iff := fun w hw => by
        rw [hexp₂, hInner.disc_iff w hw]
        constructor
        · rintro (rfl | ⟨u, hu, c, hc, ht⟩ | ⟨c, hc, ht⟩)
          · exact Or.inl rfl
          · exact Or.inr ⟨u, Finset.mem_insert_of_mem hu, c, hc, ht⟩
          · exact Or.inr ⟨r, Finset.mem_insert_self r _, c, hc, ht⟩
        · rintro (rfl | ⟨u, hu, c, hc, ht⟩)
          · exact Or.inl rfl
          · rcases Finset.mem_insert.mp hu with rfl | hu'
            · exact Or.inr (Or.inr ⟨c, hc, ht⟩)
            · exact Or.inr (Or.inl ⟨u, hu', c, hc, ht⟩)
      q_mono := hInner.q_mono
      q_depth_ub := fun j hj hlt₂ => by
        have hge : T.depth r ≤ T.depth (B₂.queue B₂.qHead) := by
          rw [← hInner.r_eq]
          exact hInner.q_mono qh B₂.qHead (by rw [hInner.qHead_eq]; omega) hlt₂
        have hub := hInner.q_depth_ub j hj
        omega
      lt_depth_mem_exp := fun v hv hlt₂ hdv => by
        have hub := hInner.q_depth_ub B₂.qHead hlt₂
        rcases lt_or_ge (T.depth v) (T.depth r) with hlt_r | hge_r
        · rw [hexp₂]; exact Finset.mem_insert_of_mem (hInner.lt_depth_mem_exp v hv hlt_r)
        · have hdv_le : T.depth v ≤ T.depth r := by omega
          have hv_disc := hInner.le_depth_mem_disc v hv hdv_le
          simp only [PBFS.disc, Finset.mem_insert, Finset.mem_image, Finset.mem_range] at hv_disc
          rcases hv_disc with rfl | ⟨i, hi, rfl⟩
          · exact Finset.mem_insert_self 0 _
          · have hi_lt : i < B₂.qHead := by
              by_contra hge
              have hmono := hInner.q_mono B₂.qHead i (by omega) hi
              omega
            exact Finset.mem_insert_of_mem
              (Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi_lt, rfl⟩)
      delta_spec := fun u hu c hc => by
        rw [hexp₂] at hu
        rcases Finset.mem_insert.mp hu with rfl | hu'
        · exact hInner.delta_r c hc
        · exact hInner.delta_exp u hu' c hc
      tables := hInner.tables }

private theorem outerLoop_spec {P : List (List ℕ)} {σ : ℕ} {T : PTrie}
    (hT : TreeInv σ T)
    (hchar : ∀ u < T.numStates, ∀ a < σ, IsNode P (T.strOf u ++ [a]) ↔ 0 < T.trie u a)
    (hterm : ∀ u < T.numStates,
      T.isTerm u = if T.strOf u ≠ [] ∧ T.strOf u ∈ P then 1 else 0) :
    ∀ fuel B, BFSInv P σ T B → T.numStates ≤ B.qHead + fuel →
      BFSInv P σ T (PBFS.outerLoop T σ fuel B) ∧
        (PBFS.outerLoop T σ fuel B).qHead = (PBFS.outerLoop T σ fuel B).qTail
  | 0, B, hinv, hfuel => by
    have hqt : B.qTail < T.numStates := qTail_lt_numStates hT.one_le hinv.q_bounds hinv.q_inj
    have hge : ¬(B.qHead < B.qTail) := by omega
    have hle := hinv.qHead_le
    exact ⟨hinv, by omega⟩
  | fuel + 1, B, hinv, hfuel => by
    dsimp only [PBFS.outerLoop]
    split_ifs with hlt
    · obtain ⟨hinv₂, hqh₂⟩ := outerStep_spec hT hchar hterm hinv hlt
      exact outerLoop_spec hT hchar hterm fuel _ hinv₂ (by omega)
    · have hle := hinv.qHead_le
      exact ⟨hinv, by omega⟩

/-- Post-condition invariant of the completed breadth-first Aho–Corasick automaton `PBFS.build`. -/
structure AutomatonInv (P : List (List ℕ)) (σ : ℕ) (T : PTrie) (B : PBFS) : Prop where
  qHead_eq_qTail : B.qHead = B.qTail
  qTail_lt : B.qTail < T.numStates
  fail_zero : B.fail 0 = 0
  fail_spec : ∀ u < T.numStates, 0 < u →
    B.fail u < T.numStates ∧
      T.strOf (B.fail u) = failure P (T.strOf u) ∧
      T.depth (B.fail u) < T.depth u
  delta_spec : ∀ u < T.numStates, ∀ a < σ,
    B.delta u a < T.numStates ∧ T.strOf (B.delta u a) = nextMove P (T.strOf u) a
  outHead_zero : B.outHead 0 = 0
  outHead_spec : ∀ u < T.numStates,
    B.outHead u < T.numStates ∧ T.depth (B.outHead u) ≤ T.depth u
  outNext_spec : ∀ q < T.numStates, 0 < q →
    B.outNext q < T.numStates ∧ (B.outNext q = 0 ∨ T.depth (B.outNext q) < T.depth q)
  follow_spec : ∀ u < T.numStates,
    followOut T.depth B.outNext T.numStates (B.outHead u) =
      (output P (T.strOf u)).map List.length

theorem rootLoopInv_init {P : List (List ℕ)} {σ : ℕ} {T : PTrie} (hT : TreeInv σ T) :
    RootLoopInv P σ T 0 PBFS.init := by
  have hinit_disc : PBFS.init.disc = {0} := by
    simp only [PBFS.init, PBFS.disc, Finset.range_zero, Finset.image_empty]
    rfl
  exact
    { qHead_zero := rfl
      q_bounds := fun _ hi => absurd hi (Nat.not_lt_zero _)
      q_inj := fun _ hi => absurd hi (Nat.not_lt_zero _)
      disc_iff := fun w _ => by
        rw [hinit_disc]
        simp only [Finset.mem_singleton, Nat.not_lt_zero, false_and, exists_false, or_false]
      delta_zero := fun _ hc => absurd hc (Nat.not_lt_zero _)
      tables :=
        { zero_vals := ⟨rfl, rfl, rfl⟩
          fail_spec := fun x hx _ => by
            rw [hinit_disc, Finset.mem_singleton] at hx
            omega
          outHead_spec := fun x hx => by
            rw [hinit_disc] at hx ⊢
            rw [Finset.mem_singleton] at hx
            subst hx
            exact ⟨Finset.mem_singleton_self 0, Nat.le_refl _⟩
          outNext_spec := fun x hx _ => by
            rw [hinit_disc, Finset.mem_singleton] at hx
            omega
          follow_spec := fun x hx => by
            rw [hinit_disc, Finset.mem_singleton] at hx
            subst hx
            rw [hT.str_zero, output_nil, List.map_nil]
            exact followOut_zero_right _ _ _ } }

theorem bfsInv_rootLoop {P : List (List ℕ)} {σ : ℕ} {T : PTrie} (hT : TreeInv σ T)
    (hchar : ∀ u < T.numStates, ∀ a < σ, IsNode P (T.strOf u ++ [a]) ↔ 0 < T.trie u a)
    (hterm : ∀ u < T.numStates, T.isTerm u = if T.strOf u ≠ [] ∧ T.strOf u ∈ P then 1 else 0) :
    let B₀ := PBFS.rootLoop T σ 0 PBFS.init
    BFSInv P σ T B₀ ∧ B₀.qHead = 0 := by
  have hRoot := rootLoop_spec hT hchar hterm σ 0 PBFS.init (by omega) (rootLoopInv_init hT)
  rw [Nat.zero_add] at hRoot
  set B₀ := PBFS.rootLoop T σ 0 PBFS.init
  have hexp₀ : B₀.expAt B₀.qHead = {0} := by
    rw [hRoot.qHead_zero]
    simp only [PBFS.expAt, Finset.range_zero, Finset.image_empty]
    rfl
  refine ⟨?_, hRoot.qHead_zero⟩
  exact
    { qHead_le := by rw [hRoot.qHead_zero]; exact Nat.zero_le _
      q_bounds := fun i hi => ⟨(hRoot.q_bounds i hi).1, (hRoot.q_bounds i hi).2.1⟩
      q_inj := hRoot.q_inj
      disc_iff := fun w hw => by
        rw [hexp₀, hRoot.disc_iff w hw]
        simp only [Finset.mem_singleton, exists_eq_left]
      q_mono := fun i j hij hj => by
        rw [(hRoot.q_bounds i (lt_of_le_of_lt hij hj)).2.2, (hRoot.q_bounds j hj).2.2]
      q_depth_ub := fun j hj _ => by
        rw [(hRoot.q_bounds j hj).2.2]
        omega
      lt_depth_mem_exp := fun v hv hlt hdv => by
        rw [hexp₀, Finset.mem_singleton]
        rw [hRoot.qHead_zero] at hlt hdv
        rw [(hRoot.q_bounds 0 hlt).2.2, hT.depth_eq v hv] at hdv
        have hv_nil : T.strOf v = [] := List.eq_nil_of_length_eq_zero (by omega)
        exact hT.str_inj v hv 0 hT.one_le (hv_nil.trans hT.str_zero.symm)
      delta_spec := fun u hu c hc => by
        rw [hexp₀, Finset.mem_singleton] at hu
        subst hu
        obtain ⟨h1, h2⟩ := hRoot.delta_zero c hc
        rw [hT.str_zero]
        exact ⟨h1, h2⟩
      tables := hRoot.tables }

theorem build_bfs_spec (P : List (List ℕ)) (σ : ℕ)
    (hvalid : ∀ p ∈ P, ∀ a ∈ p, a < σ) :
    AutomatonInv P σ (PTrie.build P) (PBFS.build (PTrie.build P) σ) := by
  obtain ⟨hT, _, _, _, hterm⟩ := build_trie_spec P σ hvalid
  have hchar := trie_char_pos_iff P σ hvalid
  set T := PTrie.build P
  set B₀ := PBFS.rootLoop T σ 0 PBFS.init
  obtain ⟨hBFS₀, hqh₀⟩ := bfsInv_rootLoop hT hchar hterm
  have hOuter := outerLoop_spec hT hchar hterm T.numStates B₀ hBFS₀ (by omega)
  change BFSInv P σ T (PBFS.build T σ) ∧
    (PBFS.build T σ).qHead = (PBFS.build T σ).qTail at hOuter
  obtain ⟨hFinal, hqh_eq⟩ := hOuter
  set B := PBFS.build T σ
  have hexp_eq_disc : B.expAt B.qHead = B.disc := by
    dsimp only [PBFS.expAt, PBFS.disc]
    rw [hqh_eq]
  have hall_disc : ∀ w < T.numStates, w ∈ B.disc := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw
      rcases Nat.eq_zero_or_pos w with rfl | hpos
      · exact Finset.mem_insert_self 0 _
      · obtain ⟨u, huw, c, hc, htuc, _⟩ := hT.parent_exists w hpos hw
        have hu_disc : u ∈ B.disc := ih u huw (lt_trans huw hw)
        have hu_exp : u ∈ B.expAt B.qHead := hexp_eq_disc.symm ▸ hu_disc
        exact (hFinal.disc_iff w hw).mpr (Or.inr ⟨u, hu_exp, c, hc, htuc⟩)
  refine
    { qHead_eq_qTail := hqh_eq
      qTail_lt := qTail_lt_numStates hT.one_le hFinal.q_bounds hFinal.q_inj
      fail_zero := hFinal.tables.zero_vals.1
      fail_spec := fun u hu hup => by
        obtain ⟨hf_d, hf_s⟩ := hFinal.tables.fail_spec u (hall_disc u hu) hup
        have hf_lt := mem_disc_lt hT.one_le hFinal.q_bounds hf_d
        refine ⟨hf_lt, hf_s, ?_⟩
        rw [hT.depth_eq _ hf_lt, hT.depth_eq u hu, hf_s]
        exact length_failure_lt P (hT.str_ne_nil u hup hu)
      delta_spec := fun u hu a ha => by
        have hu_exp : u ∈ B.expAt B.qHead := hexp_eq_disc.symm ▸ hall_disc u hu
        obtain ⟨hd_d, hd_s⟩ := hFinal.delta_spec u hu_exp a ha
        exact ⟨mem_disc_lt hT.one_le hFinal.q_bounds hd_d, hd_s⟩
      outHead_zero := hFinal.tables.zero_vals.2.1
      outHead_spec := fun u hu => by
        obtain ⟨h1, h2⟩ := hFinal.tables.outHead_spec u (hall_disc u hu)
        exact ⟨mem_disc_lt hT.one_le hFinal.q_bounds h1, h2⟩
      outNext_spec := fun q hq hqp => by
        obtain ⟨h1, h2⟩ := hFinal.tables.outNext_spec q (hall_disc q hq) hqp
        exact ⟨mem_disc_lt hT.one_le hFinal.q_bounds h1, h2⟩
      follow_spec := fun u hu => hFinal.tables.follow_spec u (hall_disc u hu) }

end Cslib.Algorithms.WordRAM.AhoCorasick
