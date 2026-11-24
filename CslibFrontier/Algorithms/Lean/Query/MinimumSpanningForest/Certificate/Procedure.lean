/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Query.MinimumSpanningForest.Certificate.Batch
public import CslibFrontier.Algorithms.Lean.Query.MinimumSpanningForest.Certificate.Instance

/-!
# The certificate procedure as a comparison program

Algorithm 1 of [Khanna, Putterman and Song][KhannaPuttermanSong2026] (§3.1, p. 14) as a program
`Cslib.Query.Certificate.certificate cfg inst` in `FreeM (LEQuery E)`, generic over the schedule,
the preference estimator and the exact minimum spanning forest subroutine bundled in
`cfg : Cslib.Query.Certificate.Config V E`, and over the constant `γ` of the parameters
`t = γ d³`, `r = 8 t³` (p. 12).

A call on an instance with edges runs `t²` rounds (`Cslib.Query.Certificate.runRounds`), threading
a `Cslib.Query.Certificate.Snapshot`: the state of M6 (`Cslib.Query.Certificate.State`: portals,
spokes and forest), the batch `B` of the current block, the rejected edges `R` and, for each of
them, the index of its first invalid projection. Round `i` (`Cslib.Query.Certificate.roundStep`,
lines 9–19):

1. the acting edges `A` are those scheduled in round `i` (`Cslib.Query.Certificate.acting`);
2. the estimator estimates their preferred actions; the estimate is forced to *find* on edges that
   are not projectable (`Cslib.Query.Certificate.maskAction`);
3. edges estimated *find* join `B`; the others are projected to the child instance on the portals
   (`Cslib.Query.Certificate.Instance.child`), which is solved recursively, giving `F'` and `R'`;
4. `R''` is the set of edges of `R'` whose first invalid projection is the one made in this call,
   that is, whose first invalid index equals the length of their record here;
5. `F ← msfSub (F ∪ F' ∪ R'')`, and `R ← R ∪ (R' \ R'')`.

The last round of a block (`(i + 1) % t = 0`) ends with the batch processing of M6
(`Cslib.Query.Certificate.blockEnd`, lines 20–21), whose admissibility test is
`Cslib.Query.Certificate.admissibilityTest` on the records of the instance. The batch reports the
rejected edges without their first invalid level; the block end recomputes it for each rejected
edge by scanning its record once more (`Cslib.Query.Certificate.invalidIndices`, at most
`2 (k + 1)` comparisons for an edge whose first invalid index is `k`, by
`Cslib.Query.Certificate.countQueries_findInvalid_le_of_eq_some`). From then on the index is
carried as data, so that propagating a rejected edge up the recursion costs no comparison.

The recursion is well founded on the number of vertices. A child is called only when it has fewer
vertices than its parent (`Cslib.Query.Certificate.childCall`), a guard that never fires on a call
with an edge: the portals number at most `n / (4t²)`
(`Cslib.Query.Certificate.card_child_vertices_lt`).

## The run

The run of a call is exposed through the evaluation of the program's own prefixes, rather than a
separate pure reimplementation: `Cslib.Query.Certificate.snapshot o cfg inst i` is the snapshot at
the start of round `i` under the oracle `o`, the value of the first `i` rounds. A pure reference
semantics would have to reimplement the batch procedure, which M6 provides only as a program, and
would duplicate every step of Algorithm 1; with this choice there is nothing to keep in agreement,
`Cslib.Query.Certificate.snapshot_succ` is the one-round equation, and
`Cslib.Query.Certificate.eval_certificate` reads the result off the last snapshot. From the
snapshots, `Cslib.Query.Certificate.estimate`, `Cslib.Query.Certificate.child`,
`Cslib.Query.Certificate.childResult`, `Cslib.Query.Certificate.absorbed` (`R''`),
`Cslib.Query.Certificate.roundInput`, `Cslib.Query.Certificate.afterRound` and
`Cslib.Query.Certificate.batchResult` give every intermediate value of a round. The calls of the
whole recursion, in preorder, are `Cslib.Query.Certificate.calls`.

## Structural facts (every oracle)

* `Cslib.Query.Certificate.four_mul_sum_card_child_vertices_le`: the children of a call on `n`
  vertices have at most `t² · 2nt / r = n / 4` vertices in total (§3.6, p. 22).
* `Cslib.Query.Certificate.card_child_vertices_lt`: so each has fewer than `n`, and the guard never
  fires.
* `Cslib.Query.Certificate.sum_card_finds_add_card_child_edges`: every edge of a call acts in
  exactly one round and either joins that round's batch share or enters that round's child, so
  each edge enters at most one batch and at most one child (§3.6, pp. 22–23).
* `Cslib.Query.Certificate.batch_afterRound`: the batch of a block is the union of the *find*
  edges of its rounds.
* `Cslib.Query.Certificate.not_isDiag_child_ends`: projected edges are not self-loops.

## References

* [S. Khanna, A. Putterman and J. Song, *A Deterministic Linear Time Algorithm for Minimum
  Spanning Tree*][KhannaPuttermanSong2026], §3.1, pp. 12–14, and §3.6, pp. 22–24.
-/

public section

namespace Cslib.Query.Certificate

open Finset Multigraph

variable {V E : Type} [DecidableEq V] [DecidableEq E]

/-- The result of a call: the forest `F` and the rejected edges `R` (line 22), with, for each
rejected edge, the index in its record of its first invalid projection. -/
structure Result (E : Type) where
  /-- The forest `F`. -/
  forest : Finset E
  /-- The rejected edges `R`, to be propagated to the level of their first invalid projection. -/
  rejected : Finset E
  /-- The index of the first invalid projection of each rejected edge. -/
  invalidAt : E → ℕ

/-- The result of a call without edges (lines 1–2). -/
@[expose, simps]
def Result.empty : Result E := ⟨∅, ∅, fun _ => 0⟩

/-- The snapshot of a call at the start of a round. -/
structure Snapshot (V E : Type) where
  /-- The portals, spokes and forest. -/
  state : State V E
  /-- The batch `B` of the current block. -/
  batch : Finset E
  /-- The rejected edges `R` so far. -/
  rejected : Finset E
  /-- The index of the first invalid projection of each rejected edge. -/
  invalidAt : E → ℕ

/-- The snapshot at the start of the first round (lines 3–4). -/
@[expose, simps]
def Snapshot.init (inst : Instance V E) : Snapshot V E :=
  ⟨State.init inst.vertices inst.ends, ∅, ∅, fun _ => 0⟩

variable (cfg : Config V E)

/-- The edges acting in round `i` (line 9). -/
@[expose] def acting (inst : Instance V E) (i : ℕ) : Finset E :=
  {e ∈ inst.edges | (cfg.sched inst e : ℕ) = i}

/-- The first-invalid indices of the old rejected edges `R`, and the new ones elsewhere. -/
@[expose] def mergeInvalid (R : Finset E) (old new : E → ℕ) : E → ℕ :=
  fun e => if e ∈ R then old e else new e

/-- The first invalid index of each edge of the list, by a scan of its record. -/
@[expose] noncomputable def invalidIndices (inst : Instance V E) :
    List E → FreeM (LEQuery E) (E → ℕ)
  | [] => pure fun _ => 0
  | e :: l => do
    let k ← findInvalid e (inst.record e)
    let f ← invalidIndices inst l
    pure (Function.update f e (k.getD 0))

/-- **The end of a block** (lines 20–21): process the batch with the admissibility test of the
instance and `r = 8 t³`, record the first invalid index of each newly rejected edge, and empty
the batch. -/
@[expose] noncomputable def blockEnd (inst : Instance V E) (s : Snapshot V E) :
    FreeM (LEQuery E) (Snapshot V E) := do
  let br ← batch (fun e => admissibilityTest (inst.record e) e) (cfg.msfSub inst.ends)
    (levelR cfg.γ inst.level) s.state s.batch
  let lv ← invalidIndices inst br.rejected.toList
  pure ⟨br.state, ∅, s.rejected ∪ br.rejected, mergeInvalid s.rejected s.invalidAt lv⟩

/-- **Round `i`** (lines 9–19), with the recursive call `rec`, followed by the end of the block
when `i` is its last round. -/
@[expose] noncomputable def roundStep (rec : Instance V E → FreeM (LEQuery E) (Result E))
    (inst : Instance V E) (i : ℕ) (s : Snapshot V E) : FreeM (LEQuery E) (Snapshot V E) := do
  let st := s.state
  let A := acting cfg inst i
  let a ← cfg.est inst st A
  let act := maskAction st a
  let res ← rec (inst.child st {e ∈ A | act e = .project})
  let R'' := {e ∈ res.rejected | res.invalidAt e = (inst.record e).length}
  let F ← cfg.msfSub inst.ends (st.forest ∪ res.forest ∪ R'')
  let s' : Snapshot V E :=
    ⟨{ st with forest := F }, s.batch ∪ {e ∈ A | act e = .find}, s.rejected ∪ (res.rejected \ R''),
      mergeInvalid s.rejected s.invalidAt res.invalidAt⟩
  if (i + 1) % levelT cfg.γ inst.level = 0 then blockEnd cfg inst s' else pure s'

/-- The first `i` rounds of a call, with the recursive call `rec`. -/
@[expose] noncomputable def runRounds (rec : Instance V E → FreeM (LEQuery E) (Result E))
    (inst : Instance V E) : ℕ → FreeM (LEQuery E) (Snapshot V E)
  | 0 => pure (Snapshot.init inst)
  | i + 1 => do
    let s ← runRounds rec inst i
    roundStep cfg rec inst i s

/-- **The certificate procedure** (Algorithm 1, p. 14): a call returns at once when it has no edge
(lines 1–2), and otherwise runs its `t²` rounds and returns the forest and the rejected edges
(line 22). A child is solved only when it has fewer vertices than the call, which always holds
(`Cslib.Query.Certificate.card_child_vertices_lt`). -/
noncomputable def certificate (inst : Instance V E) : FreeM (LEQuery E) (Result E) :=
  if inst.edges = ∅ then pure Result.empty else do
    let s ← runRounds cfg (fun c => if _h : #c.vertices < #inst.vertices then certificate c
      else pure Result.empty) inst (levelT cfg.γ inst.level ^ 2)
    pure ⟨s.state.forest, s.rejected, s.invalidAt⟩
termination_by #inst.vertices

/-- The recursive call of a call `inst` on a child `c`, guarded by `#c.vertices < #inst.vertices`.
-/
@[expose] noncomputable def childCall (inst c : Instance V E) : FreeM (LEQuery E) (Result E) :=
  if _h : #c.vertices < #inst.vertices then certificate cfg c else pure Result.empty

theorem certificate_eq (inst : Instance V E) :
    certificate cfg inst = if inst.edges = ∅ then pure Result.empty else
      (do
        let s ← runRounds cfg (childCall cfg inst) inst (levelT cfg.γ inst.level ^ 2)
        pure ⟨s.state.forest, s.rejected, s.invalidAt⟩) := by
  rw [certificate]
  rfl

/-! ### The run of a call -/

variable (o : {ι : Type} → LEQuery E ι → ι)

/-- The snapshot at the start of round `i` of the call on `inst` (for `i ≤ t²`; the snapshot `t²`
is the final one). -/
@[expose] noncomputable def snapshot (inst : Instance V E) (i : ℕ) : Snapshot V E :=
  (runRounds cfg (childCall cfg inst) inst i).eval o

/-- The actions used in round `i`: the estimate, forced to *find* on edges that are not
projectable. -/
@[expose] noncomputable def estimate (inst : Instance V E) (i : ℕ) : E → Action :=
  maskAction (snapshot cfg o inst i).state
    ((cfg.est inst (snapshot cfg o inst i).state (acting cfg inst i)).eval o)

/-- The edges of round `i` sent to the batch. -/
@[expose] noncomputable def finds (inst : Instance V E) (i : ℕ) : Finset E :=
  {e ∈ acting cfg inst i | estimate cfg o inst i e = .find}

/-- The child instance of round `i`. -/
@[expose] noncomputable def child (inst : Instance V E) (i : ℕ) : Instance V E :=
  inst.child (snapshot cfg o inst i).state
    {e ∈ acting cfg inst i | estimate cfg o inst i e = .project}

/-- The result of the child call of round `i`. -/
@[expose] noncomputable def childResult (inst : Instance V E) (i : ℕ) : Result E :=
  (childCall cfg inst (child cfg o inst i)).eval o

/-- The set `R''` of round `i` (line 18): the edges rejected by the child whose first invalid
projection is the one made in this call. -/
@[expose] noncomputable def absorbed (inst : Instance V E) (i : ℕ) : Finset E :=
  {e ∈ (childResult cfg o inst i).rejected |
    (childResult cfg o inst i).invalidAt e = (inst.record e).length}

/-- The input `F ∪ F' ∪ R''` of the exact minimum spanning forest call of round `i` (line 19). -/
@[expose] noncomputable def roundInput (inst : Instance V E) (i : ℕ) : Finset E :=
  (snapshot cfg o inst i).state.forest ∪ (childResult cfg o inst i).forest ∪ absorbed cfg o inst i

/-- The snapshot after round `i`, before the end of its block. -/
@[expose] noncomputable def afterRound (inst : Instance V E) (i : ℕ) : Snapshot V E :=
  ⟨{ (snapshot cfg o inst i).state with
      forest := (cfg.msfSub inst.ends (roundInput cfg o inst i)).eval o },
    (snapshot cfg o inst i).batch ∪ finds cfg o inst i,
    (snapshot cfg o inst i).rejected ∪
      ((childResult cfg o inst i).rejected \ absorbed cfg o inst i),
    mergeInvalid (snapshot cfg o inst i).rejected (snapshot cfg o inst i).invalidAt
      (childResult cfg o inst i).invalidAt⟩

/-- The batch processing run after round `i`, when `i` is the last round of its block. -/
@[expose] noncomputable def batchResult (inst : Instance V E) (i : ℕ) : BatchResult V E :=
  (batch (fun e => admissibilityTest (inst.record e) e) (cfg.msfSub inst.ends)
    (levelR cfg.γ inst.level) (afterRound cfg o inst i).state
    (afterRound cfg o inst i).batch).eval o

omit [DecidableEq V] in
theorem eval_invalidIndices (inst : Instance V E) {l : List E} {e : E} (he : e ∈ l) :
    (invalidIndices inst l).eval o e = ((findInvalid e (inst.record e)).eval o).getD 0 := by
  induction l with
  | nil => cases he
  | cons e' l ih =>
    simp only [invalidIndices, FreeM.eval_bind, FreeM.eval_pure]
    by_cases h : e = e'
    · subst h
      simp
    · rw [Function.update_of_ne h]
      exact ih ((List.mem_cons.1 he).resolve_left h)

omit [DecidableEq V] in
/-- **The cost of recomputing the first invalid levels**: one scan per rejected edge. -/
theorem countQueries_invalidIndices (inst : Instance V E) (l : List E) :
    (invalidIndices inst l).countQueries o =
      (l.map fun e => (findInvalid e (inst.record e)).countQueries o).sum := by
  induction l with
  | nil => simp [invalidIndices]
  | cons e l ih => simp [invalidIndices, ih]

/-- The snapshot after the end of a block. -/
theorem eval_blockEnd (inst : Instance V E) (s : Snapshot V E) :
    (blockEnd cfg inst s).eval o =
      ⟨((batch (fun e => admissibilityTest (inst.record e) e) (cfg.msfSub inst.ends)
          (levelR cfg.γ inst.level) s.state s.batch).eval o).state, ∅,
        s.rejected ∪ ((batch (fun e => admissibilityTest (inst.record e) e) (cfg.msfSub inst.ends)
          (levelR cfg.γ inst.level) s.state s.batch).eval o).rejected,
        mergeInvalid s.rejected s.invalidAt ((invalidIndices inst
          ((batch (fun e => admissibilityTest (inst.record e) e) (cfg.msfSub inst.ends)
          (levelR cfg.γ inst.level) s.state s.batch).eval o).rejected.toList).eval o)⟩ := by
  simp [blockEnd]

@[simp] theorem snapshot_zero (inst : Instance V E) :
    snapshot cfg o inst 0 = Snapshot.init inst := by
  simp [snapshot, runRounds]

/-- **One round**: the snapshot at the start of round `i + 1` is the one after round `i`, followed
by the end of the block when `i` is its last round. -/
theorem snapshot_succ (inst : Instance V E) (i : ℕ) :
    snapshot cfg o inst (i + 1) =
      if (i + 1) % levelT cfg.γ inst.level = 0 then
        (blockEnd cfg inst (afterRound cfg o inst i)).eval o
      else afterRound cfg o inst i := by
  simp only [snapshot, runRounds, FreeM.eval_bind, roundStep]
  split <;> rfl

/-- The result of a call is read off its last snapshot. -/
theorem eval_certificate (inst : Instance V E) :
    (certificate cfg inst).eval o =
      if inst.edges = ∅ then Result.empty else
        ⟨(snapshot cfg o inst (levelT cfg.γ inst.level ^ 2)).state.forest,
          (snapshot cfg o inst (levelT cfg.γ inst.level ^ 2)).rejected,
          (snapshot cfg o inst (levelT cfg.γ inst.level ^ 2)).invalidAt⟩ := by
  rw [certificate_eq]
  split <;> simp [snapshot]

/-- **The calls of the recursion** rooted at `inst`, in preorder: the call itself, then the calls
rooted at its children, round by round. -/
noncomputable def calls (inst : Instance V E) : List (Instance V E) :=
  if inst.edges = ∅ then [inst] else
    inst :: (List.range (levelT cfg.γ inst.level ^ 2)).flatMap fun i =>
      if _h : #(child cfg o inst i).vertices < #inst.vertices then calls (child cfg o inst i)
      else []
termination_by #inst.vertices

theorem calls_eq (inst : Instance V E) :
    calls cfg o inst = if inst.edges = ∅ then [inst] else
      inst :: (List.range (levelT cfg.γ inst.level ^ 2)).flatMap fun i =>
        if #(child cfg o inst i).vertices < #inst.vertices then calls cfg o (child cfg o inst i)
        else [] := by
  rw [calls]
  simp only [dite_eq_ite]

theorem self_mem_calls (inst : Instance V E) : inst ∈ calls cfg o inst := by
  rw [calls_eq]
  split <;> simp

/-- The calls rooted at a child are calls of the recursion. -/
theorem mem_calls_of_mem_calls_child {inst c : Instance V E} {i : ℕ}
    (hS : inst.edges ≠ ∅) (hi : i < levelT cfg.γ inst.level ^ 2)
    (hlt : #(child cfg o inst i).vertices < #inst.vertices)
    (hc : c ∈ calls cfg o (child cfg o inst i)) : c ∈ calls cfg o inst := by
  rw [calls_eq]
  simp only [hS, ↓reduceIte, List.mem_cons, List.mem_flatMap, List.mem_range]
  exact Or.inr ⟨i, hi, by simpa [hlt] using hc⟩

/-! ### Structural facts -/

/-- The vertex set and the ends of the state never change. -/
theorem vertices_ends_snapshot (inst : Instance V E) (i : ℕ) :
    (snapshot cfg o inst i).state.vertices = inst.vertices ∧
      (snapshot cfg o inst i).state.ends = inst.ends := by
  induction i with
  | zero => simp only [snapshot_zero]; exact ⟨rfl, rfl⟩
  | succ i ih =>
    rw [snapshot_succ]
    split
    · simp only [eval_blockEnd, vertices_batch, ends_batch]
      exact ih
    · exact ih

@[simp] theorem vertices_snapshot (inst : Instance V E) (i : ℕ) :
    (snapshot cfg o inst i).state.vertices = inst.vertices :=
  (vertices_ends_snapshot cfg o inst i).1

@[simp] theorem ends_snapshot (inst : Instance V E) (i : ℕ) :
    (snapshot cfg o inst i).state.ends = inst.ends :=
  (vertices_ends_snapshot cfg o inst i).2

/-- The portals at the start of round `i` number at most `2n / r` per block completed. -/
theorem card_portals_snapshot_mul_le (inst : Instance V E) (i : ℕ) :
    #(snapshot cfg o inst i).state.portals * levelR cfg.γ inst.level ≤
      2 * #inst.vertices * (i / levelT cfg.γ inst.level) := by
  induction i with
  | zero => simp
  | succ i ih =>
    have hih : #(afterRound cfg o inst i).state.portals * levelR cfg.γ inst.level ≤
        2 * #inst.vertices * (i / levelT cfg.γ inst.level) := by
      simpa [afterRound] using ih
    rw [snapshot_succ]
    split
    · rename_i hi
      simp only [eval_blockEnd]
      rw [portals_batch]
      have hP := card_newPortals_batch_mul_le
        (test := fun e => admissibilityTest (inst.record e) e) (msfSub := cfg.msfSub inst.ends)
        (r := levelR cfg.γ inst.level) (st := (afterRound cfg o inst i).state)
        (B := (afterRound cfg o inst i).batch) o
      have hv : (afterRound cfg o inst i).state.vertices = inst.vertices := by
        simp [afterRound]
      rw [hv] at hP
      have ht : 0 < levelT cfg.γ inst.level := by
        rcases Nat.eq_zero_or_pos (levelT cfg.γ inst.level) with h | h
        · rw [h, Nat.mod_zero] at hi
          omega
        · exact h
      have hdiv : (i + 1) / levelT cfg.γ inst.level = i / levelT cfg.γ inst.level + 1 := by
        rw [Nat.succ_div]
        simp [Nat.dvd_iff_mod_eq_zero, hi]
      have hU := Nat.mul_le_mul_right (levelR cfg.γ inst.level)
        (card_union_le (afterRound cfg o inst i).state.portals
          ((batch (fun e => admissibilityTest (inst.record e) e) (cfg.msfSub inst.ends)
            (levelR cfg.γ inst.level) (afterRound cfg o inst i).state
            (afterRound cfg o inst i).batch).eval o).newPortals)
      rw [add_mul] at hU
      rw [hdiv, mul_add, mul_one]
      omega
    · exact hih.trans (Nat.mul_le_mul_left _ (Nat.div_le_div_right (Nat.le_succ i)))

/-- The vertices of the child of round `i` are the portals at the start of the round. -/
@[simp] theorem vertices_child (inst : Instance V E) (i : ℕ) :
    (child cfg o inst i).vertices = (snapshot cfg o inst i).state.portals := rfl

/-- **The children are small** (§3.6, p. 22): the children of a call on `n` vertices have at most
`t² · 2nt / r = n / 4` vertices in total, for every oracle. -/
theorem four_mul_sum_card_child_vertices_le (inst : Instance V E) :
    4 * ∑ i ∈ range (levelT cfg.γ inst.level ^ 2), #(child cfg o inst i).vertices ≤
      #inst.vertices := by
  set t := levelT cfg.γ inst.level
  rcases Nat.eq_zero_or_pos t with ht | ht
  · simp [ht]
  have hr : levelR cfg.γ inst.level = 8 * t ^ 3 := rfl
  have key : ∀ i ∈ range (t ^ 2), #(child cfg o inst i).vertices * (8 * t ^ 3) ≤
      2 * #inst.vertices * t := fun i hi => by
    have h := card_portals_snapshot_mul_le cfg o inst i
    rw [hr] at h
    rw [vertices_child]
    refine h.trans (Nat.mul_le_mul_left _ ?_)
    have := mem_range.1 hi
    exact (Nat.div_lt_of_lt_mul (by rw [sq] at this; exact this)).le
  have hsum := sum_le_sum key
  rw [← sum_mul, sum_const, card_range, smul_eq_mul] at hsum
  set S := ∑ i ∈ range (t ^ 2), #(child cfg o inst i).vertices
  have h8 : 0 < 2 * t ^ 3 := by positivity
  refine Nat.le_of_mul_le_mul_right ?_ h8
  calc 4 * S * (2 * t ^ 3) = S * (8 * t ^ 3) := by ring
    _ ≤ t ^ 2 * (2 * #inst.vertices * t) := hsum
    _ = #inst.vertices * (2 * t ^ 3) := by ring

/-- **The guard never fires** on a call with a vertex: each child has fewer vertices. -/
theorem card_child_vertices_lt (inst : Instance V E) (hX : inst.vertices.Nonempty) {i : ℕ}
    (hi : i < levelT cfg.γ inst.level ^ 2) :
    #(child cfg o inst i).vertices < #inst.vertices := by
  have h := four_mul_sum_card_child_vertices_le cfg o inst
  have hle := single_le_sum (f := fun i => #(child cfg o inst i).vertices)
    (fun _ _ => Nat.zero_le _) (mem_range.2 hi)
  have := hX.card_pos
  omega

/-- A call with a vertex solves each of its children. -/
theorem childCall_child (inst : Instance V E) (hX : inst.vertices.Nonempty) {i : ℕ}
    (hi : i < levelT cfg.γ inst.level ^ 2) :
    childCall cfg inst (child cfg o inst i) = certificate cfg (child cfg o inst i) := by
  simp only [childCall, card_child_vertices_lt cfg o inst hX hi, ↓reduceDIte]

omit [DecidableEq V] [DecidableEq E] in
/-- A sum over the concatenation of lists indexed by the rounds is a sum over the rounds. -/
theorem sum_map_flatMap_range {α M : Type*} [AddCommMonoid M] (f : α → M)
    (g : ℕ → List α) (n : ℕ) :
    (((List.range n).flatMap g).map f).sum = ∑ i ∈ range n, ((g i).map f).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.map_append, List.sum_append, ih,
      sum_range_succ]
    simp

/-- **Sums over the calls of the recursion**: a call with an edge and a vertex contributes itself
and the calls rooted at its children. -/
theorem sum_map_calls {M : Type*} [AddCommMonoid M] (f : Instance V E → M) (inst : Instance V E)
    (hX : inst.vertices.Nonempty) (hS : inst.edges ≠ ∅) :
    ((calls cfg o inst).map f).sum =
      f inst + ∑ i ∈ range (levelT cfg.γ inst.level ^ 2),
        ((calls cfg o (child cfg o inst i)).map f).sum := by
  rw [calls_eq]
  simp only [hS, ↓reduceIte, List.map_cons, List.sum_cons, sum_map_flatMap_range]
  congr 1
  refine sum_congr rfl fun i hi => ?_
  simp only [card_child_vertices_lt cfg o inst hX (mem_range.1 hi), ↓reduceIte]

@[simp] theorem ends_child (inst : Instance V E) (i : ℕ) (e : E) :
    (child cfg o inst i).ends e =
      Sym2.map (snapshot cfg o inst i).state.proj (inst.ends e) := by
  simp [child]

@[simp] theorem record_child (inst : Instance V E) (i : ℕ) (e : E) :
    (child cfg o inst i).record e =
      inst.record e ++ [spokes (snapshot cfg o inst i).state e] := rfl

@[simp] theorem level_child (inst : Instance V E) (i : ℕ) :
    (child cfg o inst i).level = inst.level + 1 := rfl

/-- The child of round `i` receives the edges of the round estimated *project*. -/
theorem edges_child (inst : Instance V E) (i : ℕ) :
    (child cfg o inst i).edges = {e ∈ acting cfg inst i | estimate cfg o inst i e = .project} :=
  rfl

/-- **Projected edges are not self-loops.** -/
theorem not_isDiag_child_ends (inst : Instance V E) (i : ℕ) {e : E}
    (he : e ∈ (child cfg o inst i).edges) : ¬((child cfg o inst i).ends e).IsDiag := by
  rw [edges_child, mem_filter] at he
  exact (projectable_of_maskAction_eq_project he.2).not_isDiag

omit [DecidableEq V] [DecidableEq E] in
/-- Every edge acts in exactly one round. -/
theorem sum_card_acting (inst : Instance V E) :
    ∑ i ∈ range (levelT cfg.γ inst.level ^ 2), #(acting cfg inst i) = #inst.edges := by
  rw [card_eq_sum_card_fiberwise (f := fun e => (cfg.sched inst e : ℕ))
    (t := range (levelT cfg.γ inst.level ^ 2)) (fun e _ => mem_range.2 (cfg.sched inst e).2)]
  rfl

/-- **Each edge enters at most one batch and at most one child** (§3.6, pp. 22–23): the edges sent
to the batch and to the child, over all rounds, are exactly the edges of the call. -/
theorem sum_card_finds_add_card_child_edges (inst : Instance V E) :
    ∑ i ∈ range (levelT cfg.γ inst.level ^ 2),
      (#(finds cfg o inst i) + #(child cfg o inst i).edges) = #inst.edges := by
  rw [← sum_card_acting cfg inst]
  refine sum_congr rfl fun i _ => ?_
  rw [edges_child, finds, ← card_union_of_disjoint]
  · congr 1
    ext e
    simp only [mem_union, mem_filter]
    cases estimate cfg o inst i e <;> simp
  · exact disjoint_filter.2 fun e _ h1 h2 => by rw [h1] at h2; cases h2

/-- **The batch of a block** is the union of the edges sent to it by its rounds so far: at the
start of round `i`, the rounds of its block before `i`. -/
theorem batch_snapshot (inst : Instance V E) (i : ℕ) :
    (snapshot cfg o inst i).batch =
      (Ico (i / levelT cfg.γ inst.level * levelT cfg.γ inst.level) i).biUnion
        (finds cfg o inst) := by
  set t := levelT cfg.γ inst.level
  induction i with
  | zero => simp
  | succ i ih =>
    rw [snapshot_succ]
    split
    · rename_i hi
      simp only [eval_blockEnd]
      have : (i + 1) / t * t = i + 1 := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hi)
      rw [this]
      simp
    · rename_i hi
      have hdiv : (i + 1) / t = i / t := by
        rcases Nat.eq_zero_or_pos t with ht | ht
        · simp [ht]
        · rw [Nat.succ_div]
          simp only [Nat.dvd_iff_mod_eq_zero, add_eq_left, ite_eq_right_iff, one_ne_zero,
            imp_false]
          exact hi
      simp only [afterRound, ih, hdiv]
      have hle : i / t * t ≤ i := Nat.div_mul_le_self i t
      rw [Nat.Ico_succ_right_eq_insert_Ico hle, biUnion_insert, union_comm]

/-- The batch processed at the end of the block of round `i` is the union of the edges sent to it
by the rounds of the block. -/
theorem batch_afterRound (inst : Instance V E) (i : ℕ) :
    (afterRound cfg o inst i).batch =
      (Icc (i / levelT cfg.γ inst.level * levelT cfg.γ inst.level) i).biUnion
        (finds cfg o inst) := by
  simp only [afterRound, batch_snapshot]
  rw [← insert_right_Ico (Nat.div_mul_le_self i _), biUnion_insert, union_comm]

end Cslib.Query.Certificate
