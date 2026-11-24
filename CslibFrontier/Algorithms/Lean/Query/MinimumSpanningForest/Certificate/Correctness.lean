/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Query.MinimumSpanningForest.Certificate.Procedure

/-!
# Correctness of the certificate procedure

The correctness half of §3.3 of [Khanna, Putterman and Song][KhannaPuttermanSong2026]
(pp. 16–18) for the program `Cslib.Query.Certificate.certificate`: Claim 3.5, Claim 3.6 and
Lemma 3.7. These are steps in the proof of [KhannaPuttermanSong2026] Theorem 4.1 (#8325), not
results of their own.

Throughout, the weights `w` are injective, the comparisons are answered by their oracle
`LEQuery.keyOracle w`, and the exact minimum spanning forest subroutine is correct
(`Cslib.Query.Certificate.Config.ExactMsf`). Nothing is assumed of the schedule or the
estimator: the estimate is forced to *find* on edges that are not projectable by the program
itself.

## Main definitions

* `Cslib.Query.Certificate.Result.Sound`: the returned forest is an acyclic set of admissible
  edges of the call, and each rejected edge carries the index of its first invalid projection.
* `Cslib.Query.Certificate.Snapshot.Invariant`: what holds at the start of every round.
* `Cslib.Query.Certificate.prefSeq`: the true preferred actions of an edge at the start of each
  round of a call (p. 13 and p. 17).
* `Cslib.Query.Certificate.HasError`, `Cslib.Query.Certificate.errors`: an edge has an *error* in
  a call when its round is bad for it (Definition 3.4) or the action used in its round differs
  from its true preference (p. 17).

## Main results

* `Cslib.Query.Certificate.sound_certificate`: **Claim 3.5** (p. 17), with the invariant of the
  state: every edge of the returned forest is admissible, and the forest is an acyclic set of
  edges of the call. Along the way `Cslib.Query.Certificate.invariant_snapshot` maintains M6's
  `Cslib.Query.Certificate.State.Invariant` at every round: the forest update of line 19 by
  `Cslib.Query.Certificate.invariant_afterRound`, and the end of a block by
  `Cslib.Query.Certificate.invariant_blockEnd`.
* `Cslib.Query.Certificate.joins_snapshot_mono`, `Cslib.Query.Certificate.exists_spoke_snapshot_le`,
  `Cslib.Query.Certificate.spoke_snapshot_of_same_block`: threshold connectivity only grows, spokes
  only get lighter, and spokes are constant within a block.
* `Cslib.Query.Certificate.joins_afterRound_of_supported_child`: **Claim 3.6** (p. 17).
* `Cslib.Query.Certificate.supported_or_rejected_of_forall_not_hasError` and, at the root,
  `Cslib.Query.Certificate.supported_certificate_root_of_forall_not_hasError`: **Lemma 3.7**, first
  claim (p. 18).
* `Cslib.Query.Certificate.hasError_of_mem_absorbed`: **Lemma 3.7**, second claim: an edge
  rejected below a call whose first invalid projection is the one made in this call has an error
  in this call.
* `Cslib.Query.Certificate.card_unsupported_add_sum_absorbed_le`: the counting consequence used in
  §3.6 (pp. 23–24): the unsupported root edges and the rejected edges (each counted once, in the
  call that absorbs it) number at most the errors over all calls.
* `Cslib.Query.Certificate.card_roundInput_le`, `Cslib.Query.Certificate.card_blockInput_le`: the
  inputs of the exact minimum spanning forest calls (§3.6, p. 24).

## The points the paper leaves loose

* **Spokes are supported.** Claim 3.6 uses that every spoke is joined to its portal through the
  forest by edges no heavier than it (p. 17: "spokes can only arise from declared edges"). This is
  a field of M6's `Cslib.Query.Certificate.State.Invariant`, preserved by every forest update.
* **Rejected edges enter `F` at their first invalid level.** An edge of R″ has an extended
  record whose first invalid entry is the new one, so it is admissible for the call
  (`Cslib.Query.Certificate.admissible_of_append_eq_some`), as Claim 3.5 needs.
* **Monotonicity.** Threshold connectivity of the forest only grows (Fact 2.5), and spokes are
  never removed and only get lighter (M6's `Cslib.Query.Certificate.spoke_batch_le`). The proof of
  Lemma 3.7 uses only these; the shape `P…PF…F` of the preferences within a block (p. 17) is not
  needed. In the *project* case the proof uses "some later round of the block prefers project",
  which is what a good last-but-not-last *project* round gives; in the *find* case it uses "some
  later block has a round that prefers find", which is what a good *find* round gives.
* **Rejected edges are supported at the root.** An edge absorbed at level `ℓ` is supported there,
  and its projections above level `ℓ` are valid, so Claim 3.6 carries the support up to the root
  without further assumptions. So the unsupported root edges and the rejected edges are disjoint,
  and their numbers add up to at most the number of errors.

## References

* [S. Khanna, A. Putterman and J. Song, *A Deterministic Linear Time Algorithm for Minimum
  Spanning Tree*][KhannaPuttermanSong2026], §3.3, pp. 16–18, and §3.6, pp. 22–24.
-/

public section

namespace Cslib.Query.Certificate

open Finset Multigraph

variable {V E W : Type} [DecidableEq V] [DecidableEq E] [LinearOrder W]

variable (cfg : Config V E) (w : E → W)

/-- The exact minimum spanning forest subroutine of `cfg` is correct for the weights `w`. -/
@[expose] def Config.ExactMsf : Prop :=
  ∀ (ends : E → Sym2 V) (S : Finset E),
    (cfg.msfSub ends S).eval (LEQuery.keyOracle w) = msf ends w S

/-- The result of a call on `inst` is **sound**: its forest is an acyclic set of admissible edges
of the call (Claim 3.5, p. 17), and its rejected edges are edges of the call, each with the index
of its first invalid projection. -/
structure Result.Sound (inst : Instance V E) (res : Result E) : Prop where
  /-- The forest consists of edges of the call. -/
  forest_subset : res.forest ⊆ inst.edges
  /-- The forest is acyclic. -/
  forest_acyclic : IsAcyclic inst.ends ↑res.forest
  /-- Every forest edge is admissible (Claim 3.5). -/
  forest_admissible : ∀ f ∈ res.forest, Admissible w (inst.record f) f
  /-- The rejected edges are edges of the call. -/
  rejected_subset : res.rejected ⊆ inst.edges
  /-- A rejected edge carries the index of its first invalid projection. -/
  firstInvalid_rejected : ∀ e ∈ res.rejected,
    firstInvalid w (inst.record e) e = some (res.invalidAt e)

/-- The invariant of the snapshots of a call on `inst`. -/
structure Snapshot.Invariant (inst : Instance V E) (s : Snapshot V E) : Prop where
  /-- M6's invariant of the state, for the admissibility of the call. -/
  state : s.state.Invariant w fun e => Admissible w (inst.record e) e
  /-- The forest consists of edges of the call. -/
  forest_subset : s.state.forest ⊆ inst.edges
  /-- The spokes are edges of the call. -/
  spoke_mem : ∀ v x, s.state.spoke v = some x → x ∈ inst.edges
  /-- The batch consists of edges of the call. -/
  batch_subset : s.batch ⊆ inst.edges
  /-- The rejected edges are edges of the call. -/
  rejected_subset : s.rejected ⊆ inst.edges
  /-- A rejected edge carries the index of its first invalid projection. -/
  firstInvalid_rejected : ∀ e ∈ s.rejected,
    firstInvalid w (inst.record e) e = some (s.invalidAt e)

variable {cfg w}

omit [DecidableEq V] [DecidableEq E] in
theorem Result.sound_empty (inst : Instance V E) : Result.Sound w inst Result.empty where
  forest_subset := by simp
  forest_acyclic := by simpa using isAcyclic_empty
  forest_admissible := by simp
  rejected_subset := by simp
  firstInvalid_rejected := by simp

/-- **The child is well formed**: its vertices are the portals, and the projected ends of a
projectable edge are portals. -/
theorem wellFormed_instanceChild {inst : Instance V E} (hwf : inst.WellFormed)
    {st : State V E} {adm : E → Prop} (hst : st.Invariant w adm) {S : Finset E}
    (hS : S ⊆ inst.edges) (hproj : ∀ e ∈ S, Projectable st e) :
    (inst.child st S).WellFormed where
  ends_mem e he v hv := by
    simp only [Instance.child_ends, Sym2.mem_map] at hv
    obtain ⟨x, hx, rfl⟩ := hv
    obtain ⟨sx, hsx⟩ := Option.isSome_iff_exists.1 ((hproj e he).isSome_spoke hx)
    exact hst.proj_mem_portals x sx hsx
  length_record e he := by
    have := hwf.length_record e (hS he)
    have := inst.level.pos
    simp only [Instance.child_record, List.length_append, List.length_singleton,
      Instance.child_level, PNat.add_coe, PNat.one_coe]
    omega
  card_record_le e he P hP := by
    simp only [Instance.child_record, List.mem_append, List.mem_singleton] at hP
    rcases hP with hP | rfl
    · exact hwf.card_record_le e (hS he) P hP
    · exact card_spokes_le st e

variable (cfg w)

/-- The child edges of round `i` are edges of the call and are projectable. -/
theorem child_edges_subset (inst : Instance V E) (i : ℕ) :
    (child cfg (LEQuery.keyOracle w) inst i).edges ⊆ inst.edges := fun e he => by
  rw [edges_child, mem_filter, acting, mem_filter] at he
  exact he.1.1

theorem projectable_of_mem_child_edges {inst : Instance V E} {i : ℕ} {e : E}
    (he : e ∈ (child cfg (LEQuery.keyOracle w) inst i).edges) :
    Projectable (snapshot cfg (LEQuery.keyOracle w) inst i).state e := by
  rw [edges_child, mem_filter] at he
  exact projectable_of_maskAction_eq_project he.2

variable {cfg w}

/-- **The forest update of a round preserves the invariant** (Algorithm 1, line 19), given a
sound child result: `F ← msf (F ∪ F' ∪ R'')` is an acyclic set of edges of the call, admissible
because child-admissible edges are admissible here and the edges of R″ are admissible up to
their invalid projection made here; every spoke stays supported (Fact 2.5); and the rejected
edges propagated up keep their first invalid index. It mirrors M6's
`Cslib.Query.Certificate.State.Invariant.batch` for line 21. -/
theorem invariant_afterRound (hw : Function.Injective w) (hmsf : cfg.ExactMsf w)
    {inst : Instance V E} (hwf : inst.WellFormed) {i : ℕ}
    (hs : (snapshot cfg (LEQuery.keyOracle w) inst i).Invariant w inst)
    (hc : (childResult cfg (LEQuery.keyOracle w) inst i).Sound w
      (child cfg (LEQuery.keyOracle w) inst i)) :
    (afterRound cfg (LEQuery.keyOracle w) inst i).Invariant w inst := by
  set s := snapshot cfg (LEQuery.keyOracle w) inst i
  set res := childResult cfg (LEQuery.keyOracle w) inst i
  have hends : s.state.ends = inst.ends := ends_snapshot cfg (LEQuery.keyOracle w) inst i
  have hce := child_edges_subset cfg w inst i
  have hAbs : absorbed cfg (LEQuery.keyOracle w) inst i ⊆ res.rejected := filter_subset _ _
  have hRI : roundInput cfg (LEQuery.keyOracle w) inst i ⊆ inst.edges := by
    refine union_subset (union_subset hs.forest_subset (hc.forest_subset.trans hce)) ?_
    exact hAbs.trans (hc.rejected_subset.trans hce)
  have hF : (afterRound cfg (LEQuery.keyOracle w) inst i).state.forest =
      msf inst.ends w (roundInput cfg (LEQuery.keyOracle w) inst i) :=
    hmsf _ _
  have hFsub : (afterRound cfg (LEQuery.keyOracle w) inst i).state.forest ⊆
      roundInput cfg (LEQuery.keyOracle w) inst i := by
    rw [hF]; exact msf_subset w
  have hst := hs.state
  refine ⟨⟨?_, ?_, ?_, hst.portals_subset, hst.mem_vertices_of_spoke, hst.mem_ends_spoke,
    ?_, ?_⟩, hFsub.trans hRI, hs.spoke_mem, ?_, ?_, ?_⟩
  · intro f hf v hv
    have := hwf.ends_mem f (hRI (hFsub hf))
    simp only [afterRound] at hv ⊢
    rw [hends] at hv
    rw [vertices_snapshot]
    exact this v hv
  · simp only [afterRound]
    rw [hends, hmsf]
    exact isAcyclic_msf w hw
  · intro f hf
    have hf' := hFsub hf
    simp only [roundInput, mem_union] at hf'
    rcases hf' with (hf' | hf') | hf'
    · exact hst.forest_adm f hf'
    · exact (hc.forest_admissible f hf').of_append
    · have h1 := hc.firstInvalid_rejected f (hAbs hf')
      simp only [absorbed, mem_filter] at hf'
      rw [hf'.2] at h1
      exact admissible_of_append_eq_some h1
  · intro v x hx
    have hx' : s.state.spoke v = some x := hx
    have h := hst.proj_mem_portals v x hx'
    rw [State.proj_of_spoke_eq_some hx]
    rw [State.proj_of_spoke_eq_some hx'] at h
    exact h
  · intro v x hx
    have h := hst.spoke_supported v x hx
    simp only [afterRound]
    rw [hmsf, hends]
    rw [hends] at h
    rw [supported_msf_iff]
    have hsub : (s.state.forest : Set E) ⊆ ↑(roundInput cfg (LEQuery.keyOracle w) inst i) :=
      fun f hf => mem_union_left _ (mem_union_left _ hf)
    exact h.mono hsub
  · simp only [afterRound]
    refine union_subset hs.batch_subset ?_
    exact (filter_subset _ _).trans (filter_subset _ _)
  · simp only [afterRound]
    exact union_subset hs.rejected_subset (sdiff_subset.trans (hc.rejected_subset.trans hce))
  · intro e he
    simp only [afterRound, mergeInvalid] at he ⊢
    split
    · rename_i h
      exact hs.firstInvalid_rejected e h
    · rename_i h
      rcases mem_union.1 he with h' | h'
      · exact absurd h' h
      · obtain ⟨hr, hna⟩ := mem_sdiff.1 h'
        have h1 := hc.firstInvalid_rejected e hr
        refine firstInvalid_of_append_eq_some h1 fun heq => hna ?_
        exact mem_filter.2 ⟨hr, heq⟩

/-- The end of a block preserves the invariant (lines 20–21, by M6's
`Cslib.Query.Certificate.State.Invariant.batch`), and the recomputed first invalid indices of the
newly rejected edges are correct. -/
theorem invariant_blockEnd (hw : Function.Injective w) (hmsf : cfg.ExactMsf w)
    {inst : Instance V E} (hwf : inst.WellFormed) {s : Snapshot V E}
    (hs : s.Invariant w inst) (hvx : s.state.vertices = inst.vertices)
    (hends : s.state.ends = inst.ends) :
    ((blockEnd cfg inst s).eval (LEQuery.keyOracle w)).Invariant w inst := by
  have htest : ∀ e, (admissibilityTest (inst.record e) e).eval (LEQuery.keyOracle w) =
      decide (Admissible w (inst.record e) e) := fun e => eval_admissibilityTest w _ e
  have hB : ∀ e ∈ s.batch, ∀ v ∈ s.state.ends e, v ∈ s.state.vertices := fun e he v hv => by
    rw [hends] at hv
    rw [hvx]
    exact hwf.ends_mem e (hs.batch_subset he) v hv
  set br := (batch (fun e => admissibilityTest (inst.record e) e) (cfg.msfSub inst.ends)
    (levelR cfg.γ inst.level) s.state s.batch).eval (LEQuery.keyOracle w) with hbr
  have hmsf' : (cfg.msfSub inst.ends (s.state.forest ∪ br.declared)).eval (LEQuery.keyOracle w) =
      msf s.state.ends w (s.state.forest ∪ br.declared) := by
    rw [hends]; exact hmsf _ _
  have hD : br.declared ⊆ s.batch := declared_subset_batch hw htest
  have hR : br.rejected ⊆ s.batch := rejected_subset_batch hw htest
  rw [eval_blockEnd]
  refine ⟨?_, ?_, ?_, by simp, ?_, ?_⟩
  · exact hs.state.batch hw htest hB hmsf'
  · simp only
    rw [forest_batch, hmsf']
    exact (msf_subset w).trans (union_subset hs.forest_subset (hD.trans hs.batch_subset))
  · intro v x hx
    rcases spoke_batch_eq_or_mem_declared hw htest hx with h | h
    · exact hs.spoke_mem v x h
    · exact hs.batch_subset (hD h)
  · exact union_subset hs.rejected_subset (hR.trans hs.batch_subset)
  · intro e he
    simp only [mergeInvalid]
    by_cases h : e ∈ s.rejected
    · simp only [h, ↓reduceIte]
      exact hs.firstInvalid_rejected e h
    · simp only [h, ↓reduceIte]
      have hr : e ∈ br.rejected := (mem_union.1 he).resolve_left h
      rw [eval_invalidIndices _ _ (mem_toList.2 hr), eval_findInvalid]
      have hna := not_adm_of_mem_rejected_batch hw htest hr
      rcases hk : firstInvalid w (inst.record e) e with _ | k
      · exact absurd (firstInvalid_eq_none_iff.1 hk) hna
      · rfl

/-- The invariant at every round, given sound results from smaller calls. -/
private theorem invariant_snapshot_of (hw : Function.Injective w) (hmsf : cfg.ExactMsf w)
    {inst : Instance V E} (hwf : inst.WellFormed)
    (ih : ∀ c : Instance V E, #c.vertices < #inst.vertices → c.WellFormed →
      ((certificate cfg c).eval (LEQuery.keyOracle w)).Sound w c) (i : ℕ) :
    (snapshot cfg (LEQuery.keyOracle w) inst i).Invariant w inst ∧
      ((childResult cfg (LEQuery.keyOracle w) inst i).Sound w
        (child cfg (LEQuery.keyOracle w) inst i)) := by
  have hchild : ∀ j, (snapshot cfg (LEQuery.keyOracle w) inst j).Invariant w inst →
      (childResult cfg (LEQuery.keyOracle w) inst j).Sound w
        (child cfg (LEQuery.keyOracle w) inst j) := fun j hj => by
    have hwfc : (child cfg (LEQuery.keyOracle w) inst j).WellFormed :=
      wellFormed_instanceChild hwf hj.state
        (child_edges_subset cfg w inst j) fun e he => projectable_of_mem_child_edges cfg w he
    simp only [childResult, childCall]
    split
    · exact ih _ ‹_› hwfc
    · exact Result.sound_empty _
  suffices h : (snapshot cfg (LEQuery.keyOracle w) inst i).Invariant w inst from ⟨h, hchild i h⟩
  induction i with
  | zero =>
    rw [snapshot_zero]
    exact ⟨State.invariant_init _ _ _ _, by simp, by simp, by simp, by simp, by simp⟩
  | succ i ihi =>
    have ha := invariant_afterRound hw hmsf hwf ihi (hchild i ihi)
    rw [snapshot_succ]
    split
    · exact invariant_blockEnd hw hmsf hwf ha (by simp [afterRound]) (by simp [afterRound])
    · exact ha

/-- A step in the proof of Theorem 4.1 of [KhannaPuttermanSong2026] (#8325):
**Claim 3.5** (§3.3, p. 17). Every edge of the forest returned by a call is admissible, and the
forest is an acyclic set of edges of the call; the rejected edges are edges of the call, each with
the index of its first invalid projection. -/
theorem sound_certificate (hw : Function.Injective w) (hmsf : cfg.ExactMsf w)
    (inst : Instance V E) (hwf : inst.WellFormed) :
    ((certificate cfg inst).eval (LEQuery.keyOracle w)).Sound w inst := by
  induction h : #inst.vertices using Nat.strong_induction_on generalizing inst with
  | _ n ih =>
    subst h
    have ih' : ∀ c : Instance V E, #c.vertices < #inst.vertices → c.WellFormed →
        ((certificate cfg c).eval (LEQuery.keyOracle w)).Sound w c :=
      fun c hc hwfc => ih _ hc c hwfc rfl
    rw [eval_certificate]
    split
    · exact Result.sound_empty _
    · have hs := (invariant_snapshot_of hw hmsf hwf ih' (levelT cfg.γ inst.level ^ 2)).1
      refine ⟨hs.forest_subset, ?_, hs.state.forest_adm, hs.rejected_subset,
        hs.firstInvalid_rejected⟩
      have := hs.state.forest_acyclic
      rwa [ends_snapshot] at this

/-- **The invariant holds at the start of every round** of a call on a well-formed instance:
M6's invariant of the state, for the admissibility of the call, and the edges it holds are edges
of the call. -/
theorem invariant_snapshot (hw : Function.Injective w) (hmsf : cfg.ExactMsf w)
    {inst : Instance V E} (hwf : inst.WellFormed) (i : ℕ) :
    (snapshot cfg (LEQuery.keyOracle w) inst i).Invariant w inst :=
  (invariant_snapshot_of hw hmsf hwf (fun c _ hc => sound_certificate hw hmsf c hc) i).1

/-- The child result of every round is sound. -/
theorem sound_childResult (hw : Function.Injective w) (hmsf : cfg.ExactMsf w)
    {inst : Instance V E} (hwf : inst.WellFormed) (i : ℕ) :
    (childResult cfg (LEQuery.keyOracle w) inst i).Sound w
      (child cfg (LEQuery.keyOracle w) inst i) :=
  (invariant_snapshot_of hw hmsf hwf (fun c _ hc => sound_certificate hw hmsf c hc) i).2

/-- The child of every round is well formed. -/
theorem wellFormed_child (hw : Function.Injective w) (hmsf : cfg.ExactMsf w)
    {inst : Instance V E} (hwf : inst.WellFormed) (i : ℕ) :
    (child cfg (LEQuery.keyOracle w) inst i).WellFormed :=
  wellFormed_instanceChild hwf (invariant_snapshot hw hmsf hwf i).state
    (child_edges_subset cfg w inst i)
    fun _ he => projectable_of_mem_child_edges cfg w he

/-! ### Monotonicity along the rounds -/

section Monotone

/-- No block ends between two rounds of the same block. -/
private theorem mod_ne_zero_of_same_block {t i j m : ℕ} (hij : j / t = i / t) (hm : i ≤ m)
    (hmj : m + 1 ≤ j) : (m + 1) % t ≠ 0 := by
  intro h
  rcases Nat.eq_zero_or_pos t with ht | ht
  · rw [ht, Nat.mod_zero] at h; omega
  have h1 : (m + 1) / t = m / t + 1 := by
    rw [Nat.succ_div]; simp [Nat.dvd_iff_mod_eq_zero, h]
  have h2 : i / t ≤ m / t := Nat.div_le_div_right hm
  have h3 : (m + 1) / t ≤ j / t := Nat.div_le_div_right hmj
  omega

variable (cfg) in
/-- **Spokes do not change within a block** (p. 17), for every oracle. -/
theorem spoke_snapshot_of_same_block (o : {ι : Type} → LEQuery E ι → ι) (inst : Instance V E)
    {i j : ℕ} (hij : i ≤ j) (hblock : j / levelT cfg.γ inst.level = i / levelT cfg.γ inst.level) :
    (snapshot cfg o inst j).state.spoke = (snapshot cfg o inst i).state.spoke := by
  induction j, hij using Nat.le_induction with
  | base => rfl
  | succ m hm ih =>
    have hne := mod_ne_zero_of_same_block hblock hm le_rfl
    have hm' : m / levelT cfg.γ inst.level = i / levelT cfg.γ inst.level :=
      le_antisymm (hblock ▸ Nat.div_le_div_right (Nat.le_succ m)) (Nat.div_le_div_right hm)
    rw [snapshot_succ]
    simp only [hne, ↓reduceIte]
    exact ih hm'

/-- Threshold connectivity of the forest only grows from one snapshot to the next (Fact 2.5). -/
private theorem joins_snapshot_succ (hmsf : cfg.ExactMsf w) {inst : Instance V E} {i : ℕ}
    {k : W} {u v : V}
    (h : Joins inst.ends {f | f ∈ (afterRound cfg (LEQuery.keyOracle w) inst i).state.forest ∧
      w f ≤ k} u v) :
    Joins inst.ends {f | f ∈ (snapshot cfg (LEQuery.keyOracle w) inst (i + 1)).state.forest ∧
      w f ≤ k} u v := by
  rw [snapshot_succ]
  split
  · simp only [eval_blockEnd]
    rw [forest_batch]
    have he : (afterRound cfg (LEQuery.keyOracle w) inst i).state.ends = inst.ends := by
      simp [afterRound]
    rw [hmsf]
    exact joins_msf_of_joins w (X := ↑(afterRound cfg (LEQuery.keyOracle w) inst i).state.forest)
      (by simp) h
  · exact h

private theorem joins_afterRound (hmsf : cfg.ExactMsf w) {inst : Instance V E} {i : ℕ}
    {k : W} {u v : V}
    (h : Joins inst.ends {f | f ∈ (snapshot cfg (LEQuery.keyOracle w) inst i).state.forest ∧
      w f ≤ k} u v) :
    Joins inst.ends {f | f ∈ (afterRound cfg (LEQuery.keyOracle w) inst i).state.forest ∧
      w f ≤ k} u v := by
  simp only [afterRound]
  rw [hmsf]
  refine joins_msf_of_joins w (X := ↑(snapshot cfg (LEQuery.keyOracle w) inst i).state.forest)
    ?_ h
  intro f hf
  exact mem_coe.2 (mem_union_left _ (mem_union_left _ hf))

/-- **Threshold connectivity of the forest only grows** along the rounds (Fact 2.5, p. 17: "the
connectivity in `F` only improves as the rounds progress"). -/
theorem joins_snapshot_mono (hmsf : cfg.ExactMsf w) {inst : Instance V E} {i j : ℕ}
    (hij : i ≤ j) {k : W} {u v : V}
    (h : Joins inst.ends {f | f ∈ (snapshot cfg (LEQuery.keyOracle w) inst i).state.forest ∧
      w f ≤ k} u v) :
    Joins inst.ends {f | f ∈ (snapshot cfg (LEQuery.keyOracle w) inst j).state.forest ∧
      w f ≤ k} u v := by
  induction j, hij using Nat.le_induction with
  | base => exact h
  | succ m _ ih => exact joins_snapshot_succ hmsf (joins_afterRound hmsf ih)

/-- The forest after round `i` is joined at every threshold by every later snapshot's forest. -/
theorem joins_snapshot_of_afterRound (hmsf : cfg.ExactMsf w) {inst : Instance V E} {i j : ℕ}
    (hij : i < j) {k : W} {u v : V}
    (h : Joins inst.ends {f | f ∈ (afterRound cfg (LEQuery.keyOracle w) inst i).state.forest ∧
      w f ≤ k} u v) :
    Joins inst.ends {f | f ∈ (snapshot cfg (LEQuery.keyOracle w) inst j).state.forest ∧
      w f ≤ k} u v :=
  joins_snapshot_mono hmsf hij (joins_snapshot_succ hmsf h)

/-- **Spokes are never removed and only get lighter** along the rounds (p. 18: "`p(e')` can only
decrease"). -/
theorem exists_spoke_snapshot_le {inst : Instance V E} {i j : ℕ} (hij : i ≤ j) {v : V} {x : E}
    (hx : (snapshot cfg (LEQuery.keyOracle w) inst i).state.spoke v = some x) :
    ∃ x', (snapshot cfg (LEQuery.keyOracle w) inst j).state.spoke v = some x' ∧ w x' ≤ w x := by
  induction j, hij using Nat.le_induction with
  | base => exact ⟨x, hx, le_rfl⟩
  | succ m _ ih =>
    obtain ⟨y, hy, hyx⟩ := ih
    rw [snapshot_succ]
    split
    · simp only [eval_blockEnd]
      obtain ⟨z, hz, hzy⟩ := spoke_batch_le (w := w)
        (test := fun e => admissibilityTest (inst.record e) e) (msfSub := cfg.msfSub inst.ends)
        (r := levelR cfg.γ inst.level) (B := (afterRound cfg (LEQuery.keyOracle w) inst m).batch)
        (st := (afterRound cfg (LEQuery.keyOracle w) inst m).state) (v := v) hy
      exact ⟨z, hz, hzy.trans hyx⟩
    · exact ⟨y, hy, hyx⟩

variable (cfg) in
/-- The rejected edges only grow along the rounds, for every oracle. -/
theorem rejected_snapshot_mono (o : {ι : Type} → LEQuery E ι → ι) (inst : Instance V E)
    {i j : ℕ} (hij : i ≤ j) :
    (snapshot cfg o inst i).rejected ⊆ (snapshot cfg o inst j).rejected := by
  induction j, hij using Nat.le_induction with
  | base => exact subset_rfl
  | succ m _ ih =>
    refine ih.trans ?_
    rw [snapshot_succ]
    split
    · simp only [eval_blockEnd, afterRound]
      exact subset_union_left.trans subset_union_left
    · exact subset_union_left

variable (cfg) in
/-- The rejected edges after round `i` remain rejected. -/
theorem rejected_afterRound_subset (o : {ι : Type} → LEQuery E ι → ι) (inst : Instance V E)
    {i j : ℕ} (hij : i < j) :
    (afterRound cfg o inst i).rejected ⊆ (snapshot cfg o inst j).rejected := by
  refine Subset.trans ?_ (rejected_snapshot_mono cfg o inst hij)
  rw [snapshot_succ]
  split
  · simp only [eval_blockEnd]
    exact subset_union_left
  · exact subset_rfl

end Monotone

/-! ### Claim 3.6 -/

omit [DecidableEq V] [DecidableEq E] in
/-- Raising the threshold keeps vertices joined. -/
private theorem joins_le_mono {ends : E → Sym2 V} {F : Set E} {k k' : W} (hk : k ≤ k') {a b : V}
    (h : Joins ends {f | f ∈ F ∧ w f ≤ k} a b) : Joins ends {f | f ∈ F ∧ w f ≤ k'} a b :=
  h.mono (by rintro f ⟨hf, hfw⟩; exact ⟨hf, hfw.trans hk⟩)

omit [DecidableEq V] [DecidableEq E] [LinearOrder W] in
private theorem joins_of_ends_eq {ends : E → Sym2 V} {S : Set E} {f : E} (hf : f ∈ S) {a b : V}
    (h : ends f = s(a, b)) : Joins ends S a b :=
  Joins.of_mem hf h

omit [DecidableEq E] in
/-- A vertex is joined to its portal by forest edges no heavier than its spoke. -/
private theorem joins_proj {st : State V E} {adm : E → Prop} (hst : st.Invariant w adm) {x : V}
    {sx : E} (hx : st.spoke x = some sx) :
    Joins st.ends {f | f ∈ st.forest ∧ w f ≤ w sx} x (st.proj x) :=
  (supported_iff w (hst.ends_spoke hx)).1 (hst.spoke_supported x sx hx)

/-- A step in the proof of Theorem 4.1 of [KhannaPuttermanSong2026] (#8325):
**Claim 3.6** (§3.3, p. 17). Let `e` with ends `u, v` be projected in round `i`, with spokes
`σ(u) = su` and `σ(v) = sv`. If the child's forest supports the projected edge, then after the round
the forest edges of weight at most `max (w e) (p e)`, where `p e = max (w su) (w sv)`, join `u` and
`v`. -/
theorem joins_afterRound_of_supported_child (hw : Function.Injective w) (hmsf : cfg.ExactMsf w)
    {inst : Instance V E} (hwf : inst.WellFormed) {i : ℕ} {e : E}
    (hsup : Supported (child cfg (LEQuery.keyOracle w) inst i).ends w
      ↑(childResult cfg (LEQuery.keyOracle w) inst i).forest e)
    {u v : V} (huv : inst.ends e = s(u, v)) {su sv : E}
    (hu : (snapshot cfg (LEQuery.keyOracle w) inst i).state.spoke u = some su)
    (hv : (snapshot cfg (LEQuery.keyOracle w) inst i).state.spoke v = some sv) :
    Joins inst.ends {f | f ∈ (afterRound cfg (LEQuery.keyOracle w) inst i).state.forest ∧
      w f ≤ max (w e) (max (w su) (w sv))} u v := by
  set st := (snapshot cfg (LEQuery.keyOracle w) inst i).state with hst_def
  have hinv := (invariant_snapshot hw hmsf hwf i).state
  have hends : st.ends = inst.ends := ends_snapshot cfg _ inst i
  have hc := sound_childResult hw hmsf hwf i
  set K := max (w e) (max (w su) (w sv))
  set T : Set E := {f | f ∈ roundInput cfg (LEQuery.keyOracle w) inst i ∧ w f ≤ K}
  -- a vertex is joined to its portal by `T` when its spoke is no heavier than `K`
  have hport : ∀ x sx, st.spoke x = some sx → w sx ≤ K → Joins inst.ends T x (st.proj x) := by
    intro x sx hsx hK
    have := joins_proj hinv hsx
    rw [hends] at this
    refine this.mono ?_
    rintro f ⟨hf, hfw⟩
    exact ⟨mem_union_left _ (mem_union_left _ hf), hfw.trans hK⟩
  -- the child's path, lifted through the spokes
  have hchild_ends : (child cfg (LEQuery.keyOracle w) inst i).ends e = s(st.proj u, st.proj v) := by
    rw [ends_child, huv, Sym2.map_mk]
  have hpath := (supported_iff w hchild_ends).1 hsup
  have hlift : Joins inst.ends T (st.proj u) (st.proj v) := by
    refine Joins.lift (S := {f | f ∈ (childResult cfg (LEQuery.keyOracle w) inst i).forest ∧
      w f ≤ w e}) id ?_ hpath
    rintro f ⟨hf, hfe⟩ a b hab
    obtain ⟨⟨x, y⟩, hxy⟩ := Quot.exists_rep (inst.ends f)
    have hxy' : inst.ends f = s(x, y) := hxy.symm
    have hcf : (child cfg (LEQuery.keyOracle w) inst i).ends f = s(st.proj x, st.proj y) := by
      rw [ends_child, hxy', Sym2.map_mk]
    -- the spokes at the ends of `f` exist and are no heavier than `f`, since `f` is projected and
    -- admissible in the child
    have hfc : f ∈ (child cfg (LEQuery.keyOracle w) inst i).edges := hc.forest_subset hf
    have hpr := projectable_of_mem_child_edges cfg w hfc
    have hadm := hc.forest_admissible f hf
    have hlast : spokes st f ∈ (child cfg (LEQuery.keyOracle w) inst i).record f := by
      rw [record_child]; exact List.mem_append_right _ (List.mem_singleton_self _)
    have hspk : ∀ z ∈ inst.ends f, ∃ sz, st.spoke z = some sz ∧ w sz ≤ K := fun z hz => by
      have hz' : z ∈ st.ends f := hends ▸ hz
      obtain ⟨sz, hsz⟩ := Option.isSome_iff_exists.1 (hpr.isSome_spoke hz')
      exact ⟨sz, hsz, ((hadm.le hlast (mem_spokes.2 ⟨z, hz', hsz⟩)).trans hfe).trans
        (le_max_left _ _)⟩
    have hfT : f ∈ T := ⟨mem_union_left _ (mem_union_right _ hf), hfe.trans (le_max_left _ _)⟩
    obtain ⟨sx, hsx, hsxK⟩ := hspk x (by rw [hxy']; exact Sym2.mem_mk_left x y)
    obtain ⟨sy, hsy, hsyK⟩ := hspk y (by rw [hxy']; exact Sym2.mem_mk_right x y)
    have hxyT : Joins inst.ends T (st.proj x) (st.proj y) :=
      ((hport x sx hsx hsxK).symm.trans (joins_of_ends_eq hfT hxy')).trans (hport y sy hsy hsyK)
    rw [hcf] at hab
    rcases Sym2.eq_iff.1 hab.symm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hxyT
    · exact hxyT.symm
  have hu' := hport u su hu ((le_max_left _ _).trans (le_max_right _ _))
  have hv' := hport v sv hv ((le_max_right _ _).trans (le_max_right _ _))
  have hT : Joins inst.ends T u v := (hu'.trans hlift).trans hv'.symm
  simp only [afterRound]
  rw [hmsf]
  exact joins_msf_of_joins w (X := ↑(roundInput cfg (LEQuery.keyOracle w) inst i)) subset_rfl hT

/-- An edge of R″ is supported by the forest after its round: it is an input of the round's
exact minimum spanning forest call. -/
theorem supported_afterRound_of_mem_absorbed (hmsf : cfg.ExactMsf w) {inst : Instance V E}
    {i : ℕ} {e : E} (he : e ∈ absorbed cfg (LEQuery.keyOracle w) inst i) {u v : V}
    (huv : inst.ends e = s(u, v)) :
    Joins inst.ends {f | f ∈ (afterRound cfg (LEQuery.keyOracle w) inst i).state.forest ∧
      w f ≤ w e} u v := by
  simp only [afterRound]
  rw [hmsf]
  exact joins_msf_of_mem w (mem_union_right _ he) huv

/-- The invariant after every round. -/
theorem invariant_afterRound_of_wellFormed (hw : Function.Injective w) (hmsf : cfg.ExactMsf w)
    {inst : Instance V E} (hwf : inst.WellFormed) (i : ℕ) :
    (afterRound cfg (LEQuery.keyOracle w) inst i).Invariant w inst :=
  invariant_afterRound hw hmsf hwf (invariant_snapshot hw hmsf hwf i)
    (sound_childResult hw hmsf hwf i)

/-! ### Errors -/

variable (cfg w) in
/-- The **true preferred actions** of `e` at the start of the rounds of the call on `inst`
(p. 13 and p. 17): the sequence `(a_i(e))_i` of the history (Definition 3.8, p. 18). -/
noncomputable def prefSeq (inst : Instance V E) (e : E) (j : ℕ) : Action :=
  pref w (snapshot cfg (LEQuery.keyOracle w) inst j).state e

variable (cfg w) in
/-- An **error** occurs for `e` in the call on `inst` (p. 17) when its scheduled round is bad for
it (Definition 3.4) or the action used for it in that round differs from its true preference. -/
def HasError (inst : Instance V E) (e : E) : Prop :=
  BadRound (levelT cfg.γ inst.level) (prefSeq cfg w inst e) (cfg.sched inst e) ∨
    estimate cfg (LEQuery.keyOracle w) inst (cfg.sched inst e) e ≠
      prefSeq cfg w inst e (cfg.sched inst e)

variable (cfg w) in
open scoped Classical in
/-- The edges of the call on `inst` with an error in it. -/
noncomputable def errors (inst : Instance V E) : Finset E :=
  {e ∈ inst.edges | HasError cfg w inst e}

/-- The true preference sequence of `e` is its preference at the start of each round. -/
theorem prefSeq_eq (inst : Instance V E) (e : E) (j : ℕ) :
    prefSeq cfg w inst e j = pref w (snapshot cfg (LEQuery.keyOracle w) inst j).state e := by
  rw [prefSeq]

/-- An error is a bad scheduled round or a wrong action in it. -/
theorem hasError_iff {inst : Instance V E} {e : E} :
    HasError cfg w inst e ↔
      BadRound (levelT cfg.γ inst.level) (prefSeq cfg w inst e) (cfg.sched inst e) ∨
        estimate cfg (LEQuery.keyOracle w) inst (cfg.sched inst e) e ≠
          prefSeq cfg w inst e (cfg.sched inst e) := by
  rw [HasError]

theorem mem_errors {inst : Instance V E} {e : E} :
    e ∈ errors cfg w inst ↔ e ∈ inst.edges ∧ HasError cfg w inst e := by
  classical
  simp [errors]

omit [DecidableEq V] [DecidableEq E] in
theorem mem_acting_sched {inst : Instance V E} {e : E} (he : e ∈ inst.edges) :
    e ∈ acting cfg inst (cfg.sched inst e) :=
  mem_filter.2 ⟨he, rfl⟩

omit [DecidableEq V] [DecidableEq E] in
theorem sched_eq_of_mem_acting {inst : Instance V E} {e : E} {i : ℕ}
    (he : e ∈ acting cfg inst i) : (cfg.sched inst e : ℕ) = i :=
  (mem_filter.1 he).2

/-- The result of a call with an edge is read off its last snapshot. -/
private theorem eval_certificate_of_ne {inst : Instance V E} (hS : inst.edges ≠ ∅) :
    (certificate cfg inst).eval (LEQuery.keyOracle w) =
      ⟨(snapshot cfg (LEQuery.keyOracle w) inst (levelT cfg.γ inst.level ^ 2)).state.forest,
        (snapshot cfg (LEQuery.keyOracle w) inst (levelT cfg.γ inst.level ^ 2)).rejected,
        (snapshot cfg (LEQuery.keyOracle w) inst (levelT cfg.γ inst.level ^ 2)).invalidAt⟩ := by
  rw [eval_certificate]
  simp [hS]

/-- A round with a find preference makes an edge supported once both spokes are no heavier than
it: either the spokes meet at a portal, or the forest joins the ends below the spokes. -/
private theorem joins_of_prefersFind (hw : Function.Injective w) (hmsf : cfg.ExactMsf w)
    {inst : Instance V E} (hwf : inst.WellFormed) {j : ℕ} {e : E} {u v : V}
    (huv : inst.ends e = s(u, v)) {su sv : E}
    (hu : (snapshot cfg (LEQuery.keyOracle w) inst j).state.spoke u = some su)
    (hv : (snapshot cfg (LEQuery.keyOracle w) inst j).state.spoke v = some sv)
    (hle : max (w su) (w sv) ≤ w e)
    (hpf : PrefersFind w (snapshot cfg (LEQuery.keyOracle w) inst j).state e) :
    Joins inst.ends {f | f ∈ (snapshot cfg (LEQuery.keyOracle w) inst j).state.forest ∧
      w f ≤ w e} u v := by
  have hends := ends_snapshot cfg (LEQuery.keyOracle w) inst j
  have hinv := (invariant_snapshot hw hmsf hwf j).state
  rw [prefersFind_iff (by rw [hends]; exact huv) hu hv] at hpf
  rcases hpf with hp | hj
  · have h1 := joins_le_mono ((le_max_left _ _).trans hle) (joins_proj hinv hu)
    have h2 := joins_le_mono ((le_max_right _ _).trans hle) (joins_proj hinv hv)
    rw [hends] at h1 h2
    rw [← hp] at h2
    exact h1.trans h2.symm
  · rw [hends] at hj
    exact joins_le_mono hle hj

/-- **The *find* case of Lemma 3.7** (p. 18): an edge without error in this call, sent to the
batch and not rejected, is supported by the forest at the end of the call. Lemma 3.2 makes it
supported after the batch or gives it spokes no heavier than it; in the latter case, its round
being good, some later block has a round where it prefers *find*, and there the spokes, which
only got lighter, make it supported. -/
private theorem joins_final_of_find (hw : Function.Injective w) (hmsf : cfg.ExactMsf w)
    {inst : Instance V E} (hwf : inst.WellFormed) {e : E} (he : e ∈ inst.edges)
    (hne : ¬HasError cfg w inst e)
    (hrej : e ∉ (snapshot cfg (LEQuery.keyOracle w) inst (levelT cfg.γ inst.level ^ 2)).rejected)
    (hfind : estimate cfg (LEQuery.keyOracle w) inst (cfg.sched inst e) e = .find)
    {u v : V} (huv : inst.ends e = s(u, v)) :
    Joins inst.ends {f | f ∈ (snapshot cfg (LEQuery.keyOracle w) inst
      (levelT cfg.γ inst.level ^ 2)).state.forest ∧ w f ≤ w e} u v := by
  set t := levelT cfg.γ inst.level with ht_def
  set i : ℕ := (cfg.sched inst e : ℕ) with hi_def
  have hiT : i < t ^ 2 := (cfg.sched inst e).2
  have ht0 : 0 < t := by
    rcases Nat.eq_zero_or_pos t with h | h
    · rw [h] at hiT; simp at hiT
    · exact h
  have hb : i / t < t := Nat.div_lt_of_lt_mul (by rw [sq] at hiT; exact hiT)
  set i' := i / t * t + (t - 1) with hi'_def
  have hlt := Nat.lt_div_mul_add (a := i) ht0
  have hii' : i ≤ i' := by omega
  have hi'blk : i' / t = i / t := by
    rw [hi'_def, add_comm, Nat.add_mul_div_right _ _ ht0, Nat.div_eq_of_lt (by omega), zero_add]
  have h1 : i' + 1 = (i / t + 1) * t := by rw [hi'_def, add_mul, one_mul]; omega
  have hend : (i' + 1) % t = 0 := by
    rw [h1]
    exact Nat.mul_mod_left _ _
  have hi'T : i' + 1 ≤ t ^ 2 := by
    rw [h1, sq]; exact Nat.mul_le_mul_right _ hb
  -- `e` is in the batch of its block
  have hfinds : e ∈ finds cfg (LEQuery.keyOracle w) inst i :=
    mem_filter.2 ⟨mem_acting_sched he, hfind⟩
  have hB : e ∈ (afterRound cfg (LEQuery.keyOracle w) inst i').batch := by
    rw [batch_afterRound, mem_biUnion]
    refine ⟨i, mem_Icc.2 ⟨?_, hii'⟩, hfinds⟩
    rw [← ht_def, hi'blk]
    exact Nat.div_mul_le_self i t
  have hsucc := snapshot_succ cfg (LEQuery.keyOracle w) inst i'
  rw [← ht_def] at hsucc
  simp only [hend, ↓reduceIte, eval_blockEnd] at hsucc
  have hinvA := invariant_afterRound_of_wellFormed hw hmsf hwf i'
  have hendsA : (afterRound cfg (LEQuery.keyOracle w) inst i').state.ends = inst.ends := by
    simp [afterRound]
  have hvA : (afterRound cfg (LEQuery.keyOracle w) inst i').state.vertices = inst.vertices := by
    simp [afterRound]
  have htest : ∀ e, (admissibilityTest (inst.record e) e).eval (LEQuery.keyOracle w) =
      decide (Admissible w (inst.record e) e) := fun e => eval_admissibilityTest w _ e
  have hBv : ∀ f ∈ (afterRound cfg (LEQuery.keyOracle w) inst i').batch,
      ∀ x ∈ (afterRound cfg (LEQuery.keyOracle w) inst i').state.ends f,
        x ∈ (afterRound cfg (LEQuery.keyOracle w) inst i').state.vertices := fun f hf x hx => by
    rw [hendsA] at hx; rw [hvA]; exact hwf.ends_mem f (hinvA.batch_subset hf) x hx
  have hmsf' := fun D => (hmsf (afterRound cfg (LEQuery.keyOracle w) inst i').state.ends
    ((afterRound cfg (LEQuery.keyOracle w) inst i').state.forest ∪ D))
  rw [hendsA] at hmsf'
  have hr : 0 < levelR cfg.γ inst.level := by
    simp only [levelR]; rw [← ht_def]; positivity
  -- not rejected by the batch, since rejected edges stay rejected
  have heR : e ∉ (batchResult cfg (LEQuery.keyOracle w) inst i').rejected := fun h => by
    refine hrej (rejected_snapshot_mono cfg _ inst hi'T ?_)
    rw [hsucc]
    exact mem_union_right _ h
  have hmono : ∀ j, i' + 1 ≤ j → j ≤ t ^ 2 →
      Joins inst.ends {f | f ∈ (snapshot cfg (LEQuery.keyOracle w) inst j).state.forest ∧
        w f ≤ w e} u v →
      Joins inst.ends {f | f ∈ (snapshot cfg (LEQuery.keyOracle w) inst (t ^ 2)).state.forest ∧
        w f ≤ w e} u v := fun j _ hj h => joins_snapshot_mono hmsf hj h
  rcases supported_or_spokes_batch hw htest hr hBv (by rw [hendsA]; exact hmsf' _) hB heR
      (by rw [hendsA]; exact huv) with hsup | ⟨su, sv, hsu, hsv, hle⟩
  · -- supported after the batch
    refine hmono (i' + 1) le_rfl hi'T ?_
    rw [hsucc]
    have := (supported_iff w (by rw [hendsA]; exact huv)).1 hsup
    rwa [hendsA] at this
  · -- spokes no heavier than `e`: a later block prefers *find*
    have hpref : estimate cfg (LEQuery.keyOracle w) inst i e = prefSeq cfg w inst e i := by
      by_contra h; exact hne (Or.inr h)
    have hbad : ¬BadRound t (prefSeq cfg w inst e) i := fun h => hne (Or.inl h)
    have hpi : prefSeq cfg w inst e i = .find := hpref ▸ hfind
    simp only [BadRound, not_or, not_and, hpi, reduceCtorEq, false_implies, true_and,
      not_forall] at hbad
    obtain ⟨j, hjT, hblk, hj⟩ := hbad
    have hjf : prefSeq cfg w inst e j = .find := by
      cases h : prefSeq cfg w inst e j
      · rfl
      · exact absurd h hj
    have hij : i' + 1 ≤ j := by
      have : (i / t + 1) * t ≤ j := (Nat.le_div_iff_mul_le ht0).1 hblk
      rw [hi'_def]; rw [add_mul, one_mul] at this; omega
    have hsu0 : (snapshot cfg (LEQuery.keyOracle w) inst (i' + 1)).state.spoke u = some su := by
      rw [hsucc]; exact hsu
    have hsv0 : (snapshot cfg (LEQuery.keyOracle w) inst (i' + 1)).state.spoke v = some sv := by
      rw [hsucc]; exact hsv
    obtain ⟨su', hsu', hsu'le⟩ := exists_spoke_snapshot_le hij hsu0
    obtain ⟨sv', hsv', hsv'le⟩ := exists_spoke_snapshot_le hij hsv0
    have hle' : max (w su') (w sv') ≤ w e := (max_le_max hsu'le hsv'le).trans hle
    exact hmono j hij hjT.le (joins_of_prefersFind hw hmsf hwf huv hsu' hsv' hle'
      (pref_eq_find_iff.1 hjf))

/-- A good round with a *project* preference is followed in its block by a round preferring
*project*. -/
private theorem exists_project_of_not_hasError {inst : Instance V E} {e : E}
    (hne : ¬HasError cfg w inst e)
    (hproj : estimate cfg (LEQuery.keyOracle w) inst (cfg.sched inst e) e = .project) :
    ∃ j, (cfg.sched inst e : ℕ) < j ∧
      j / levelT cfg.γ inst.level = (cfg.sched inst e : ℕ) / levelT cfg.γ inst.level ∧
      prefSeq cfg w inst e j = .project := by
  have hpref : estimate cfg (LEQuery.keyOracle w) inst (cfg.sched inst e) e =
      prefSeq cfg w inst e (cfg.sched inst e) := by
    by_contra h; exact hne (Or.inr h)
  have hbad : ¬BadRound (levelT cfg.γ inst.level) (prefSeq cfg w inst e) (cfg.sched inst e) :=
    fun h => hne (Or.inl h)
  have hpi : prefSeq cfg w inst e (cfg.sched inst e) = .project := hpref ▸ hproj
  simp only [BadRound, not_or, not_and, hpi, reduceCtorEq, false_implies, and_true,
    not_forall, true_implies] at hbad
  obtain ⟨j, hij, hblk, hj⟩ := hbad
  refine ⟨j, hij, hblk, ?_⟩
  cases h : prefSeq cfg w inst e j
  · exact absurd h hj
  · rfl

/-- A round after round `i` in its block prefers *find* for an edge whose ends the forest after
round `i` joins below its spokes. -/
private theorem prefSeq_eq_find_of_joins (hmsf : cfg.ExactMsf w)
    {inst : Instance V E} {i j : ℕ} (hij : i < j)
    (hblk : j / levelT cfg.γ inst.level = i / levelT cfg.γ inst.level) {e : E} {u v : V}
    (huv : inst.ends e = s(u, v)) {su sv : E}
    (hu : (snapshot cfg (LEQuery.keyOracle w) inst i).state.spoke u = some su)
    (hv : (snapshot cfg (LEQuery.keyOracle w) inst i).state.spoke v = some sv)
    (hJ : Joins inst.ends {f | f ∈ (afterRound cfg (LEQuery.keyOracle w) inst i).state.forest ∧
      w f ≤ max (w su) (w sv)} u v) :
    prefSeq cfg w inst e j = .find := by
  have hsp := spoke_snapshot_of_same_block cfg (LEQuery.keyOracle w) inst hij.le hblk
  have hends := ends_snapshot cfg (LEQuery.keyOracle w) inst j
  rw [prefSeq, pref_eq_find_iff,
    prefersFind_iff (by rw [hends]; exact huv) (by rw [hsp]; exact hu) (by rw [hsp]; exact hv)]
  right
  rw [hends]
  exact joins_snapshot_of_afterRound hmsf hij hJ

/-- **The *project* case of Lemma 3.7** (p. 18): an edge without error in this call, projected,
and either rejected below with its first invalid projection made here, or supported by the
child's forest, is supported by the forest at the end of the call, unless it is rejected. -/
private theorem joins_final_of_project (hw : Function.Injective w) (hmsf : cfg.ExactMsf w)
    {inst : Instance V E} (hwf : inst.WellFormed) {e : E} (he : e ∈ inst.edges)
    (hne : ¬HasError cfg w inst e)
    (hrej : e ∉ (snapshot cfg (LEQuery.keyOracle w) inst (levelT cfg.γ inst.level ^ 2)).rejected)
    (hproj : estimate cfg (LEQuery.keyOracle w) inst (cfg.sched inst e) e = .project)
    (hchild : e ∈ (childResult cfg (LEQuery.keyOracle w) inst (cfg.sched inst e)).rejected ∨
      Supported (child cfg (LEQuery.keyOracle w) inst (cfg.sched inst e)).ends w
        ↑(childResult cfg (LEQuery.keyOracle w) inst (cfg.sched inst e)).forest e)
    {u v : V} (huv : inst.ends e = s(u, v)) :
    Joins inst.ends {f | f ∈ (snapshot cfg (LEQuery.keyOracle w) inst
      (levelT cfg.γ inst.level ^ 2)).state.forest ∧ w f ≤ w e} u v := by
  have hiT : (cfg.sched inst e : ℕ) < levelT cfg.γ inst.level ^ 2 := (cfg.sched inst e).2
  rcases hchild with hr | hsup
  · by_cases habs : e ∈ absorbed cfg (LEQuery.keyOracle w) inst (cfg.sched inst e)
    · exact joins_snapshot_of_afterRound hmsf hiT
        (supported_afterRound_of_mem_absorbed hmsf habs huv)
    · refine absurd (rejected_afterRound_subset cfg _ inst hiT ?_) hrej
      exact mem_union_right _ (mem_sdiff.2 ⟨hr, habs⟩)
  · have hec : e ∈ (child cfg (LEQuery.keyOracle w) inst (cfg.sched inst e)).edges :=
      mem_filter.2 ⟨mem_acting_sched he, hproj⟩
    have hpr := projectable_of_mem_child_edges cfg w hec
    have hends := ends_snapshot cfg (LEQuery.keyOracle w) inst (cfg.sched inst e)
    have huv' : (snapshot cfg (LEQuery.keyOracle w) inst (cfg.sched inst e)).state.ends e =
        s(u, v) := by rw [hends]; exact huv
    obtain ⟨su, sv, hsu, hsv, -⟩ := hpr.exists_spokes huv'
    have hJ := joins_afterRound_of_supported_child hw hmsf hwf hsup huv hsu hsv
    by_cases hp : max (w su) (w sv) ≤ w e
    · rw [max_eq_left hp] at hJ
      exact joins_snapshot_of_afterRound hmsf hiT hJ
    · -- the projection is invalid, so the rest of the block prefers *find*: the round was bad
      obtain ⟨j, hij, hblk, hj⟩ := exists_project_of_not_hasError hne hproj
      rw [max_eq_right (not_le.1 hp).le] at hJ
      rw [prefSeq_eq_find_of_joins hmsf hij hblk huv hsu hsv hJ] at hj
      cases hj

omit [DecidableEq V] [DecidableEq E] in
/-- A call with an edge of a well-formed instance has a vertex. -/
private theorem vertices_nonempty {inst : Instance V E} (hwf : inst.WellFormed) {e : E}
    (he : e ∈ inst.edges) : inst.vertices.Nonempty := by
  obtain ⟨⟨u, v⟩, huv⟩ := Quot.exists_rep (inst.ends e)
  exact ⟨u, hwf.ends_mem e he u (by rw [← huv]; exact Sym2.mem_mk_left u v)⟩

/-- A step in the proof of Theorem 4.1 of [KhannaPuttermanSong2026] (#8325):
**Lemma 3.7, first claim** (§3.3, p. 18), for any call. An edge with no error in this call or in any
call below it that receives its projection is rejected by the call or supported by the call's
forest. -/
theorem supported_or_rejected_of_forall_not_hasError (hw : Function.Injective w)
    (hmsf : cfg.ExactMsf w) (inst : Instance V E) (hwf : inst.WellFormed) {e : E}
    (he : e ∈ inst.edges)
    (hne : ∀ c ∈ calls cfg (LEQuery.keyOracle w) inst, e ∈ c.edges → ¬HasError cfg w c e) :
    e ∈ ((certificate cfg inst).eval (LEQuery.keyOracle w)).rejected ∨
      Supported inst.ends w ↑((certificate cfg inst).eval (LEQuery.keyOracle w)).forest e := by
  induction h : #inst.vertices using Nat.strong_induction_on generalizing inst with
  | _ n ih =>
    subst h
    have hS : inst.edges ≠ ∅ := ne_empty_of_mem he
    have hX := vertices_nonempty hwf he
    rw [eval_certificate_of_ne hS]
    by_cases hrej : e ∈ (snapshot cfg (LEQuery.keyOracle w) inst
      (levelT cfg.γ inst.level ^ 2)).rejected
    · exact Or.inl hrej
    right
    obtain ⟨⟨u, v⟩, huv⟩ := Quot.exists_rep (inst.ends e)
    have huv' : inst.ends e = s(u, v) := huv.symm
    rw [supported_iff w huv']
    have hne0 := hne inst (self_mem_calls cfg _ inst) he
    rcases hact : estimate cfg (LEQuery.keyOracle w) inst (cfg.sched inst e) e
    · exact joins_final_of_find hw hmsf hwf he hne0 hrej hact huv'
    · refine joins_final_of_project hw hmsf hwf he hne0 hrej hact ?_ huv'
      have hiT : (cfg.sched inst e : ℕ) < levelT cfg.γ inst.level ^ 2 := (cfg.sched inst e).2
      have hlt := card_child_vertices_lt cfg (LEQuery.keyOracle w) inst hX hiT
      have hec : e ∈ (child cfg (LEQuery.keyOracle w) inst (cfg.sched inst e)).edges :=
        mem_filter.2 ⟨mem_acting_sched he, hact⟩
      have := ih _ hlt _ (wellFormed_child hw hmsf hwf _) hec
        (fun c hc => hne c (mem_calls_of_mem_calls_child cfg _ hS hiT hlt hc)) rfl
      rwa [childResult, childCall_child cfg _ inst hX hiT]

/-- The root returns no rejected edge: its records are empty, so all its edges are admissible. -/
theorem rejected_certificate_root (hw : Function.Injective w) (hmsf : cfg.ExactMsf w)
    {X : Finset V} {ends : E → Sym2 V} {S : Finset E} (hS : ∀ e ∈ S, ∀ v ∈ ends e, v ∈ X) :
    ((certificate cfg (Instance.root X ends S)).eval (LEQuery.keyOracle w)).rejected = ∅ := by
  have hs := sound_certificate hw hmsf _ (Instance.wellFormed_root hS)
  refine eq_empty_of_forall_notMem fun e he => ?_
  have := hs.firstInvalid_rejected e he
  simp [firstInvalid_nil] at this

/-- A step in the proof of Theorem 4.1 of [KhannaPuttermanSong2026] (#8325):
**Lemma 3.7, first claim** (§3.3, p. 18). In the root instance, an edge for which no error occurs,
in any call of the recursion that receives its projection, is supported by the returned forest. -/
theorem supported_certificate_root_of_forall_not_hasError (hw : Function.Injective w)
    (hmsf : cfg.ExactMsf w) {X : Finset V} {ends : E → Sym2 V} {S : Finset E}
    (hS : ∀ e ∈ S, ∀ v ∈ ends e, v ∈ X) {e : E} (he : e ∈ S)
    (hne : ∀ c ∈ calls cfg (LEQuery.keyOracle w) (Instance.root X ends S), e ∈ c.edges →
      ¬HasError cfg w c e) :
    Supported ends w
      ↑((certificate cfg (Instance.root X ends S)).eval (LEQuery.keyOracle w)).forest e := by
  rcases supported_or_rejected_of_forall_not_hasError hw hmsf _ (Instance.wellFormed_root hS) he
    hne with h | h
  · simp [rejected_certificate_root hw hmsf hS] at h
  · exact h

/-- A step in the proof of Theorem 4.1 of [KhannaPuttermanSong2026] (#8325):
**Lemma 3.7, second claim** (§3.3, p. 18). An edge rejected below a call whose first invalid
projection is the one made in this call (an edge of R″) has an error in this call. Its projection
being invalid, the forest joins its ends below its heavier spoke after the round, so the rest of the
block prefers *find*: the round was bad, or the estimate was wrong. -/
theorem hasError_of_mem_absorbed (hw : Function.Injective w) (hmsf : cfg.ExactMsf w)
    {inst : Instance V E} (hwf : inst.WellFormed) {i : ℕ} {e : E}
    (he : e ∈ absorbed cfg (LEQuery.keyOracle w) inst i) : HasError cfg w inst e := by
  have hc := sound_childResult hw hmsf hwf i
  have hr : e ∈ (childResult cfg (LEQuery.keyOracle w) inst i).rejected := (mem_filter.1 he).1
  have hec := hc.rejected_subset hr
  have hec' := hec
  rw [edges_child, mem_filter] at hec'
  have hsched := sched_eq_of_mem_acting hec'.1
  have hproj : estimate cfg (LEQuery.keyOracle w) inst (cfg.sched inst e) e = .project := by
    rw [hsched]; exact hec'.2
  by_contra hne
  obtain ⟨j, hij, hblk, hj⟩ := exists_project_of_not_hasError hne hproj
  rw [hsched] at hij hblk
  -- the projection made here is invalid
  have hinv := hc.firstInvalid_rejected e hr
  rw [(mem_filter.1 he).2, record_child] at hinv
  obtain ⟨s, hs, hlt⟩ := exists_lt_of_append_eq_some hinv
  have hpr := projectable_of_mem_child_edges cfg w hec
  obtain ⟨⟨u, v⟩, huv⟩ := Quot.exists_rep (inst.ends e)
  have huv' : inst.ends e = s(u, v) := huv.symm
  have hends := ends_snapshot cfg (LEQuery.keyOracle w) inst i
  have huv'' : (snapshot cfg (LEQuery.keyOracle w) inst i).state.ends e = s(u, v) := by
    rw [hends]; exact huv'
  obtain ⟨su, sv, hsu, hsv, -⟩ := hpr.exists_spokes huv''
  have hsmax : w e ≤ max (w su) (w sv) := by
    rw [spokes_eq huv'', hsu, hsv] at hs
    simp only [Option.toFinset_some, mem_union, mem_singleton] at hs
    rcases hs with rfl | rfl
    · exact hlt.le.trans (le_max_left _ _)
    · exact hlt.le.trans (le_max_right _ _)
  have hJ := joins_le_mono hsmax (supported_afterRound_of_mem_absorbed hmsf he huv')
  rw [prefSeq_eq_find_of_joins hmsf hij hblk huv' hsu hsv hJ] at hj
  cases hj

/-! ### Counting -/

/-- The edges of R″ of the different rounds are disjoint: each lies in its round's acting
edges. -/
theorem absorbed_subset_acting (hw : Function.Injective w) (hmsf : cfg.ExactMsf w)
    {inst : Instance V E} (hwf : inst.WellFormed) (i : ℕ) :
    absorbed cfg (LEQuery.keyOracle w) inst i ⊆ acting cfg inst i := fun e he => by
  have hec := (sound_childResult hw hmsf hwf i).rejected_subset (mem_filter.1 he).1
  rw [edges_child, mem_filter] at hec
  exact hec.1

omit [DecidableEq V] [DecidableEq E] in
/-- The acting edges of different rounds are disjoint. -/
theorem pairwiseDisjoint_acting (inst : Instance V E) (I : Finset ℕ) :
    (I : Set ℕ).PairwiseDisjoint (acting cfg inst) := by
  intro i _ j _ hij
  exact disjoint_left.2 fun e hi hj =>
    hij ((sched_eq_of_mem_acting hi).symm.trans (sched_eq_of_mem_acting hj))

/-- **One level of the counting** behind §3.6 (pp. 23–24). In a call, the unsupported edges that
are not rejected, together with the edges of the sets R″, number at most the errors of the
call plus the unsupported, unrejected edges of its children. -/
private theorem card_unsupported_add_sum_absorbed_le_step (hw : Function.Injective w)
    (hmsf : cfg.ExactMsf w) {inst : Instance V E} (hwf : inst.WellFormed)
    (hS : inst.edges ≠ ∅) :
    #(unsupported inst.ends w ↑((certificate cfg inst).eval (LEQuery.keyOracle w)).forest
        (inst.edges \ ((certificate cfg inst).eval (LEQuery.keyOracle w)).rejected)) +
      ∑ i ∈ range (levelT cfg.γ inst.level ^ 2), #(absorbed cfg (LEQuery.keyOracle w) inst i) ≤
    #(errors cfg w inst) + ∑ i ∈ range (levelT cfg.γ inst.level ^ 2),
      #(unsupported (child cfg (LEQuery.keyOracle w) inst i).ends w
        ↑(childResult cfg (LEQuery.keyOracle w) inst i).forest
        ((child cfg (LEQuery.keyOracle w) inst i).edges \
          (childResult cfg (LEQuery.keyOracle w) inst i).rejected)) := by
  set T := levelT cfg.γ inst.level ^ 2
  set U := unsupported inst.ends w ↑((certificate cfg inst).eval (LEQuery.keyOracle w)).forest
    (inst.edges \ ((certificate cfg inst).eval (LEQuery.keyOracle w)).rejected)
  set A := (range T).biUnion (absorbed cfg (LEQuery.keyOracle w) inst)
  set Uc := (range T).biUnion fun i => unsupported (child cfg (LEQuery.keyOracle w) inst i).ends w
    ↑(childResult cfg (LEQuery.keyOracle w) inst i).forest
    ((child cfg (LEQuery.keyOracle w) inst i).edges \
      (childResult cfg (LEQuery.keyOracle w) inst i).rejected)
  have hdisjA : ((range T : Finset ℕ) : Set ℕ).PairwiseDisjoint
      (absorbed cfg (LEQuery.keyOracle w) inst) :=
    (pairwiseDisjoint_acting inst (range T)).mono fun i =>
      absorbed_subset_acting hw hmsf hwf i
  have hA : #A = ∑ i ∈ range T, #(absorbed cfg (LEQuery.keyOracle w) inst i) :=
    card_biUnion hdisjA
  have hres := eval_certificate_of_ne (cfg := cfg) (w := w) hS
  -- an edge of R″ is supported by the final forest
  have hsupA : ∀ e ∈ A, Supported inst.ends w
      ↑((certificate cfg inst).eval (LEQuery.keyOracle w)).forest e := fun e he => by
    obtain ⟨i, hi, he⟩ := mem_biUnion.1 he
    obtain ⟨⟨u, v⟩, huv⟩ := Quot.exists_rep (inst.ends e)
    rw [supported_iff w huv.symm, hres]
    exact joins_snapshot_of_afterRound hmsf (mem_range.1 hi)
      (supported_afterRound_of_mem_absorbed hmsf he huv.symm)
  have hdisj : Disjoint U A := disjoint_left.2 fun e heU heA =>
    ((mem_unsupported w).1 heU).2 (hsupA e heA)
  have hsub : U ∪ A ⊆ errors cfg w inst ∪ Uc := by
    intro e he
    rcases mem_union.1 he with heU | heA
    · obtain ⟨he', hns⟩ := (mem_unsupported w).1 heU
      obtain ⟨heS, hnr⟩ := mem_sdiff.1 he'
      by_cases herr : HasError cfg w inst e
      · exact mem_union_left _ (mem_errors.2 ⟨heS, herr⟩)
      refine mem_union_right _ ?_
      obtain ⟨⟨u, v⟩, huv⟩ := Quot.exists_rep (inst.ends e)
      have huv' : inst.ends e = s(u, v) := huv.symm
      rw [hres] at hnr hns
      rw [supported_iff w huv'] at hns
      have hiT : (cfg.sched inst e : ℕ) < T := (cfg.sched inst e).2
      rcases hact : estimate cfg (LEQuery.keyOracle w) inst (cfg.sched inst e) e
      · exact absurd (joins_final_of_find hw hmsf hwf heS herr hnr hact huv') hns
      · refine mem_biUnion.2 ⟨cfg.sched inst e, mem_range.2 hiT, ?_⟩
        refine (mem_unsupported w).2 ⟨mem_sdiff.2 ⟨mem_filter.2 ⟨mem_acting_sched heS, hact⟩,
          fun hr => hns ?_⟩, fun hsup => hns ?_⟩
        · exact joins_final_of_project hw hmsf hwf heS herr hnr hact (Or.inl hr) huv'
        · exact joins_final_of_project hw hmsf hwf heS herr hnr hact (Or.inr hsup) huv'
    · obtain ⟨i, -, hei⟩ := mem_biUnion.1 heA
      refine mem_union_left _ (mem_errors.2 ⟨?_, hasError_of_mem_absorbed hw hmsf hwf hei⟩)
      exact (mem_filter.1 (absorbed_subset_acting hw hmsf hwf i hei)).1
  calc #U + ∑ i ∈ range T, #(absorbed cfg (LEQuery.keyOracle w) inst i)
      = #(U ∪ A) := by rw [card_union_of_disjoint hdisj, hA]
    _ ≤ #(errors cfg w inst ∪ Uc) := card_le_card hsub
    _ ≤ #(errors cfg w inst) + #Uc := card_union_le _ _
    _ ≤ _ := Nat.add_le_add_left card_biUnion_le _

/-- A step in the proof of Theorem 4.1 of [KhannaPuttermanSong2026] (#8325):
**the counting consequence of Lemma 3.7** (§3.6, pp. 23–24), for any call. The edges of the call
that are neither rejected nor supported by its forest, together with the edges of all the sets R″ of
the calls below it (the rejected edges, each counted once, in the call that absorbs it), number at
most the errors over all these calls. -/
theorem card_unsupported_add_sum_absorbed_le_of_wellFormed (hw : Function.Injective w)
    (hmsf : cfg.ExactMsf w) (inst : Instance V E) (hwf : inst.WellFormed) :
    #(unsupported inst.ends w ↑((certificate cfg inst).eval (LEQuery.keyOracle w)).forest
        (inst.edges \ ((certificate cfg inst).eval (LEQuery.keyOracle w)).rejected)) +
      ((calls cfg (LEQuery.keyOracle w) inst).map fun c =>
        ∑ i ∈ range (levelT cfg.γ c.level ^ 2), #(absorbed cfg (LEQuery.keyOracle w) c i)).sum ≤
    ((calls cfg (LEQuery.keyOracle w) inst).map fun c => #(errors cfg w c)).sum := by
  induction h : #inst.vertices using Nat.strong_induction_on generalizing inst with
  | _ n ih =>
    subst h
    by_cases hS : inst.edges = ∅
    · rw [calls_eq]
      simp only [hS, ↓reduceIte, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        add_zero]
      have h1 : ∀ R : Finset E, unsupported inst.ends w
          ↑((certificate cfg inst).eval (LEQuery.keyOracle w)).forest (∅ \ R) = ∅ := fun R =>
        eq_empty_of_forall_notMem fun e he => by simpa using ((mem_unsupported w).1 he).1
      have h2 : ∀ i, absorbed cfg (LEQuery.keyOracle w) inst i = ∅ := fun i =>
        eq_empty_of_forall_notMem fun e he => by
          have := (mem_filter.1 (absorbed_subset_acting hw hmsf hwf i he)).1
          rw [hS] at this; simp at this
      rw [h1]
      simp [h2]
    · obtain ⟨e, he⟩ := nonempty_iff_ne_empty.2 hS
      have hX := vertices_nonempty hwf he
      rw [sum_map_calls cfg _ _ inst hX hS, sum_map_calls cfg _ _ inst hX hS]
      have hstep := card_unsupported_add_sum_absorbed_le_step hw hmsf hwf hS
      have hch : ∀ i ∈ range (levelT cfg.γ inst.level ^ 2),
          #(unsupported (child cfg (LEQuery.keyOracle w) inst i).ends w
            ↑(childResult cfg (LEQuery.keyOracle w) inst i).forest
            ((child cfg (LEQuery.keyOracle w) inst i).edges \
              (childResult cfg (LEQuery.keyOracle w) inst i).rejected)) +
          ((calls cfg (LEQuery.keyOracle w) (child cfg (LEQuery.keyOracle w) inst i)).map fun c =>
            ∑ i ∈ range (levelT cfg.γ c.level ^ 2),
              #(absorbed cfg (LEQuery.keyOracle w) c i)).sum ≤
          ((calls cfg (LEQuery.keyOracle w) (child cfg (LEQuery.keyOracle w) inst i)).map
            fun c => #(errors cfg w c)).sum := fun i hi => by
        have hiT := mem_range.1 hi
        have hlt := card_child_vertices_lt cfg (LEQuery.keyOracle w) inst hX hiT
        have := ih _ hlt _ (wellFormed_child hw hmsf hwf i) rfl
        rwa [childResult, childCall_child cfg _ inst hX hiT]
      have hsum := sum_le_sum hch
      rw [sum_add_distrib] at hsum
      omega

/-- A step in the proof of Theorem 4.1 of [KhannaPuttermanSong2026] (#8325):
**the counting consequence of Lemma 3.7** (§3.6, pp. 23–24), at the root. The root edges unsupported
by the returned forest, plus the rejected edges (each counted once, in the call whose R″ absorbs
it), number at most the errors over all calls of the recursion. The sizes of the sets R″ are the
rejected edges entering the exact minimum spanning forest calls (p. 24). -/
theorem card_unsupported_add_sum_absorbed_le (hw : Function.Injective w) (hmsf : cfg.ExactMsf w)
    {X : Finset V} {ends : E → Sym2 V} {S : Finset E} (hS : ∀ e ∈ S, ∀ v ∈ ends e, v ∈ X) :
    #(unsupported ends w
        ↑((certificate cfg (Instance.root X ends S)).eval (LEQuery.keyOracle w)).forest S) +
      ((calls cfg (LEQuery.keyOracle w) (Instance.root X ends S)).map fun c =>
        ∑ i ∈ range (levelT cfg.γ c.level ^ 2), #(absorbed cfg (LEQuery.keyOracle w) c i)).sum ≤
    ((calls cfg (LEQuery.keyOracle w) (Instance.root X ends S)).map
      fun c => #(errors cfg w c)).sum := by
  have := card_unsupported_add_sum_absorbed_le_of_wellFormed hw hmsf _
    (Instance.wellFormed_root hS)
  rwa [rejected_certificate_root hw hmsf hS, sdiff_empty] at this

/-! ### The inputs of the exact minimum spanning forest calls -/

/-- **The input of a round's exact call** (§3.6, p. 24): the old forest and the child's forest,
each of at most `n - 1` edges, and the edges of R″. -/
theorem card_roundInput_le (hw : Function.Injective w) (hmsf : cfg.ExactMsf w)
    {inst : Instance V E} (hwf : inst.WellFormed) (i : ℕ) :
    #(roundInput cfg (LEQuery.keyOracle w) inst i) ≤
      2 * (#inst.vertices - 1) + #(absorbed cfg (LEQuery.keyOracle w) inst i) := by
  have hinv := invariant_snapshot hw hmsf hwf i
  have hF := hinv.state.card_forest_le
  rw [vertices_snapshot] at hF
  have hc := sound_childResult hw hmsf hwf i
  have hwfc := wellFormed_child hw hmsf hwf i
  have hF' := hc.forest_acyclic.card_le fun f hf => hwfc.ends_mem f (hc.forest_subset hf)
  have hP : #(child cfg (LEQuery.keyOracle w) inst i).vertices ≤ #inst.vertices := by
    rw [vertices_child]
    have := card_le_card hinv.state.portals_subset
    rwa [vertices_snapshot] at this
  have h1 := card_union_le ((snapshot cfg (LEQuery.keyOracle w) inst i).state.forest ∪
    (childResult cfg (LEQuery.keyOracle w) inst i).forest)
    (absorbed cfg (LEQuery.keyOracle w) inst i)
  have h2 := card_union_le (snapshot cfg (LEQuery.keyOracle w) inst i).state.forest
    (childResult cfg (LEQuery.keyOracle w) inst i).forest
  simp only [roundInput]
  omega

/-- **The input of a block's exact call** (§3.6, p. 24): the old forest, of at most `n - 1`
edges, and the declared edges, at most `r² n`. -/
theorem card_blockInput_le (hw : Function.Injective w) (hmsf : cfg.ExactMsf w)
    {inst : Instance V E} (hwf : inst.WellFormed) (i : ℕ) :
    #((afterRound cfg (LEQuery.keyOracle w) inst i).state.forest ∪
        (batchResult cfg (LEQuery.keyOracle w) inst i).declared) ≤
      (#inst.vertices - 1) + levelR cfg.γ inst.level ^ 2 * #inst.vertices := by
  have hinv := invariant_afterRound_of_wellFormed hw hmsf hwf i
  have hF := hinv.state.card_forest_le
  have hv : (afterRound cfg (LEQuery.keyOracle w) inst i).state.vertices = inst.vertices := by
    simp [afterRound]
  rw [hv] at hF
  have hD := card_declared_batch_le (w := w) (r := levelR cfg.γ inst.level)
    (test := fun e => admissibilityTest (inst.record e) e) (msfSub := cfg.msfSub inst.ends)
    (st := (afterRound cfg (LEQuery.keyOracle w) inst i).state)
    (B := (afterRound cfg (LEQuery.keyOracle w) inst i).batch) hw
    (fun e => eval_admissibilityTest w _ e)
  rw [hv] at hD
  have := card_union_le (afterRound cfg (LEQuery.keyOracle w) inst i).state.forest
    (batchResult cfg (LEQuery.keyOracle w) inst i).declared
  simp only [batchResult] at this ⊢
  omega

end Cslib.Query.Certificate
