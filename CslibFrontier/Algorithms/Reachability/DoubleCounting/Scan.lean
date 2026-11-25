/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Reachability.DoubleCounting
import Mathlib.Algebra.BigOperators.Fin
import CslibFrontier.Foundations.Control.Monad.Clock

/-!
# Streaming bounded membership scans

A branch supplies one choice per vertex in increasing order. A selection supplies only the
successive destinations of its walk, with the source implicit. The end of that segment is
the stop choice. The replay reads each destination once with a finite read-only edge callback.
The branch and its segments are proof-level replay data. The scanner keeps only a vertex
cursor, a current walk vertex, a remaining edge budget, a tally and one membership bit.

## Main results

* `Cslib.DoubleCounting.Scan.runM_eq_some_iff`: exact replay success and membership.
* `Cslib.DoubleCounting.Scan.successfulBranches`: bijection with passing transcripts for an
  exact supplied tally.
* `Cslib.DoubleCounting.Scan.prefix_registers_le`: bounds on the count and sum after any
  checked prefix.
* `Cslib.DoubleCounting.Scan.tallyM_clock`: a uniform callback clock, including rejecting runs.

To use `Cslib.DoubleCounting.Scan.runM`, supply skip/select, destination-read, and adjacency
actions alongside the source, target, round index and expected tally. Use `none` for the walk's
end marker. The scan returns `none` on rejection and `some false` for a successful negative
membership test. Callback providers are responsible for the adjacency and choice encodings.
The clock counts callback actions. The prefix bounds describe the abstract registers.

## References

* [Reinhardt and Allender, *Making Nondeterminism Unambiguous*, Figure 1][ReinhardtAllender2000]
-/

public section

namespace Cslib.DoubleCounting.Scan

variable {N : ℕ} {m : Type → Type*}

/-- Replay choices, indexed by the vertex being scanned. A selected segment contains the
destinations of its edges in order, without the initial source. -/
abbrev Branch (N : ℕ) := Transcript (Fin N)

/-- Destination budgets, independent of edge validity and the terminal tally. -/
@[expose] def Bounded (k : ℕ) (b : Branch N) : Prop :=
  ∀ v vs, b v = some vs → vs.length ≤ k

/-- Recover the full vertex lists for the transcript contract. -/
@[expose] def transcript (source : Fin N) (branch : Branch N) : Transcript (Fin N) :=
  fun v => (branch v).map (source :: ·)

/-- Passing typed transcripts already meet the destination budget. -/
theorem bounded_of_passes (source : Fin N) (k : ℕ) (b : Branch N)
    {R : Fin N → Fin N → Prop} (h : Passes R source k (transcript source b)) :
    Bounded k b := by
  intro v vs hv
  simpa [guessedLength, transcript, hv] using
    (h.1 v (source :: vs) (by simp [transcript, hv])).2

/-- Check one walk by reading its next destination or end marker. The read-only edge callback
is invoked once per attempted edge, provided there is still budget. -/
@[expose] def walkM [Monad m] (next : m (Option (Fin N))) (edge : Fin N → Fin N → m Bool)
    (target : Fin N) : ℕ → Fin N → m (Option ℕ)
  | fuel, current => do
    match ← next with
    | none => return if current = target then some fuel else none
    | some v =>
      match fuel with
      | 0 => return none
      | fuel + 1 => if ← edge current v then walkM next edge target fuel v else return none

/-- Replay the next destination from a segment, or its end marker. -/
@[expose] def readNext : StateM (List (Fin N)) (Option (Fin N)) := fun
  | [] => (none, [])
  | v :: vs => (some v, vs)

private def walk (edge : Fin N → Fin N → Bool) (target : Fin N)
    (fuel : ℕ) (current : Fin N) (tail : List (Fin N)) : Option ℕ :=
  (walkM readNext (fun u v => pure (edge u v)) target fuel current tail).1

private theorem walk_end (edge : Fin N → Fin N → Bool) (target current : Fin N) (fuel : ℕ) :
    walk edge target fuel current [] = if current = target then some fuel else none := by
  rw [walk, walkM]; rfl

private theorem walk_exhausted (edge : Fin N → Fin N → Bool) (target current v : Fin N)
    (tail : List (Fin N)) : walk edge target 0 current (v :: tail) = none := by
  rw [walk, walkM]; rfl

private theorem walk_next (edge : Fin N → Fin N → Bool) (target current v : Fin N)
    (fuel : ℕ) (tail : List (Fin N)) :
    walk edge target (fuel + 1) current (v :: tail) =
      if edge current v then walk edge target fuel v tail else none := by
  rw [walk, walkM]
  simp only [bind, StateT.bind, readNext, pure, StateT.pure]
  split <;> rfl

/-- A replayed walk returns exactly its unused fuel when the destination list forms a path
to the target within the original fuel. -/
theorem walkM_replay_eq_some {edge : Fin N → Fin N → Bool} {target current : Fin N}
    {fuel left : ℕ} {tail : List (Fin N)} :
    (walkM readNext (fun u v => pure (edge u v)) target fuel current tail).1 = some left ↔
      (current :: tail).IsChainFromTo (fun u v => edge u v = true) current target ∧
      left + tail.length = fuel := by
  change walk edge target fuel current tail = some left ↔ _
  induction tail generalizing fuel current with
  | nil =>
    have hchain : [current].IsChainFromTo (fun u v => edge u v = true) current target ↔
        current = target := ⟨fun h => h.getLast_eq, fun h => h ▸ List.isChainFromTo_singleton⟩
    rw [walk_end, hchain]
    by_cases h : current = target <;> simp [h, eq_comm]
  | cons next rest ih =>
    have hchain :
        (current :: next :: rest).IsChainFromTo (fun u v => edge u v = true) current target ↔
          edge current next = true ∧
            (next :: rest).IsChainFromTo (fun u v => edge u v = true) next target :=
      ⟨fun h => ⟨(List.isChain_cons_cons.mp h.isChain).1, h.of_cons_cons⟩,
        fun ⟨h, ht⟩ => ht.cons h⟩
    cases fuel with
    | zero => simp [walk_exhausted]
    | succ fuel =>
      rw [walk_next, hchain]
      by_cases h : edge current next = true
      · simp only [h, ite_true, ih, true_and, List.length_cons, Nat.add_succ, Nat.succ.injEq]
      · simp [h]

/-- A verified prefix's accumulated tally and membership bit. -/
structure Result where
  /-- Number and total length of all selected walks checked so far. -/
  tally : Tally
  /-- Whether the queried vertex has been selected. -/
  hit : Bool

private def add (a b : Result) : Result :=
  ⟨⟨a.tally.count + b.tally.count, a.tally.lengthSum + b.tally.lengthSum⟩, a.hit || b.hit⟩

/-- The accumulator before the first vertex has been scanned. -/
@[expose] def Result.zero : Result := ⟨⟨0, 0⟩, false⟩

/-- The contribution of one selected walk, given the initial and remaining budgets. -/
private def Result.ofWalk (budget remaining : ℕ) (hit : Bool) : Result :=
  ⟨⟨1, budget - remaining⟩, hit⟩

/-- Record one selected walk in the membership tally. -/
@[expose] def Result.recordWalk (acc : Result) (budget remaining : ℕ) (hit : Bool) : Result :=
  ⟨⟨acc.tally.count + 1, acc.tally.lengthSum + (budget - remaining)⟩, acc.hit || hit⟩

private theorem add_ofWalk (acc : Result) (budget remaining : ℕ) (hit : Bool) :
    add acc (Result.ofWalk budget remaining hit) = acc.recordWalk budget remaining hit := rfl

private def candidateM [Monad m] (select : Fin N → m Bool) (next : m (Option (Fin N)))
    (edge : Fin N → Fin N → m Bool) (source target : Fin N) (k : ℕ) (v : Fin N) :
    m (Option Result) := do
  if ← select v then
    let checked ← walkM next edge v k source
    return checked.map fun left => Result.ofWalk k left (v == target)
  else
    return some Result.zero

/-- Run the bounded scan using one selection action per vertex and one destination-read action
per walk step or stop marker. Adjacency is a read-only callback. Rejection stops the fold. -/
def tallyM [Monad m] (select : Fin N → m Bool) (next : m (Option (Fin N)))
    (edge : Fin N → Fin N → m Bool) (source target : Fin N) (k : ℕ) : m (Option Result) :=
  (Fin.foldlM (m := OptionT m) N (fun acc v => OptionT.mk do
    let checked ← candidateM select next edge source target k v
    return checked.map (add acc)) Result.zero).run

/-- Replay a selection, loading its segment in the proof-level choice provider. -/
def readSelection (branch : Branch N) (v : Fin N) : StateM (List (Fin N)) Bool :=
  fun _ => ((branch v).isSome, (branch v).getD [])

private def candidate (edge : Fin N → Fin N → Bool) (source target : Fin N)
    (k : ℕ) (branch : Branch N) (v : Fin N) : Option Result :=
  (candidateM (readSelection branch) readNext (fun u v => pure (edge u v))
    source target k v []).1

private theorem candidate_eq (edge : Fin N → Fin N → Bool) (source target : Fin N)
    (k : ℕ) (branch : Branch N) (v : Fin N) :
    candidate edge source target k branch v =
      match branch v with
      | none => some Result.zero
      | some tail =>
        (walk edge v k source tail).map fun left => Result.ofWalk k left (v == target) := by
  cases h : branch v with
  | none =>
    simp [candidateM, candidate, readSelection, h, bind, pure, StateT.bind, StateT.pure]
  | some vs =>
    simp only [candidateM, candidate, walk, readSelection, h, bind, pure, StateT.bind,
      StateT.pure, Option.isSome_some, ite_true, Option.getD_some]
    cases walkM readNext (fun u v => pure (edge u v)) v k source vs
    rfl

/-- Replay the first `n` vertices in increasing order. The input branch can be consumed
one segment at a time. -/
def tallyPrefix (edge : Fin N → Fin N → Bool) (source target : Fin N) (k : ℕ)
    (branch : Branch N) {n : ℕ} (hn : n ≤ N) : Option Result :=
  Fin.foldlM n (fun acc v =>
    (candidate edge source target k branch (v.castLE hn)).map (add acc)) Result.zero

/-- The empty prefix has the initial membership accumulator. -/
theorem tallyPrefix_zero (edge : Fin N → Fin N → Bool) (source target : Fin N)
    (k : ℕ) (branch : Branch N) :
    tallyPrefix edge source target k branch (Nat.zero_le N) = some Result.zero := by
  rw [tallyPrefix, Fin.foldlM_zero]; rfl

/-- Extending a verified prefix skips an unselected vertex or adds its checked walk.
The update consumes only the remaining budget returned by that walk. -/
theorem tallyPrefix_succ (edge : Fin N → Fin N → Bool) (source target : Fin N)
    (k : ℕ) (branch : Branch N) {n : ℕ} (hn : n < N) :
    tallyPrefix edge source target k branch (Nat.succ_le_of_lt hn) =
      (tallyPrefix edge source target k branch hn.le).bind fun acc =>
        let v : Fin N := ⟨n, hn⟩
        match branch v with
        | none => some acc
        | some tail =>
          ((walkM readNext (fun u v => pure (edge u v)) v k source tail).1).map
            fun left => acc.recordWalk k left (v == target) := by
  unfold tallyPrefix
  rw [Fin.foldlM_succ_last]
  change (_ : Option Result).bind _ = _
  refine congrArg (Option.bind _) (funext fun acc => ?_)
  rw [candidate_eq, show (Fin.last n).castLE (Nat.succ_le_of_lt hn) = (⟨n, hn⟩ : Fin N) from rfl]
  dsimp only
  cases branch (⟨n, hn⟩ : Fin N)
  · rcases acc with ⟨⟨_, _⟩, _⟩
    simp [add, Result.zero]
  · simp only [Option.map_map, Function.comp_def, add_ofWalk, walk]

/-- A partial tally depends only on selections below its cursor. -/
theorem tallyPrefix_congr (edge : Fin N → Fin N → Bool) (source target : Fin N)
    (k : ℕ) {n : ℕ} (hn : n ≤ N) {a b : Branch N}
    (h : ∀ v : Fin N, v.val < n → a v = b v) :
    tallyPrefix edge source target k a hn = tallyPrefix edge source target k b hn := by
  induction n with
  | zero => simp only [tallyPrefix_zero]
  | succ n ih =>
    rw [tallyPrefix_succ edge source target k a hn, tallyPrefix_succ edge source target k b hn,
      ih (Nat.le_of_lt hn) (fun v hv => h v (by omega))]
    simp only [h ⟨n, hn⟩ (Nat.lt_succ_self n)]

/-- Replay a scan, returning the accumulated tally and target membership if all chosen walks
check. -/
def tally (edge : Fin N → Fin N → Bool) (source target : Fin N) (k : ℕ)
    (branch : Branch N) : Option Result :=
  tallyPrefix edge source target k branch le_rfl

private theorem foldlM_replay {σ : Type} {R : Type}
    (f : R → Fin N → OptionT (StateM σ) R) (g : R → Fin N → Option R)
    (h : ∀ a v s, ((f a v).run s).1 = g a v) (a : R) (s : σ) :
    (((Fin.foldlM N f a).run) s).1 = Fin.foldlM N g a := by
  induction N generalizing a s with
  | zero => simp [Fin.foldlM_zero, pure, OptionT.pure, OptionT.run, OptionT.mk, StateT.pure]
  | succ N ih =>
    simp only [Fin.foldlM_succ, bind, OptionT.bind, OptionT.mk, OptionT.run, StateT.bind]
    have hr : (f a 0 s).1 = g a 0 := h a 0 s
    rcases he : f a 0 s with ⟨r, s'⟩
    rw [he] at hr
    rw [← hr]
    cases r with
    | none => rfl
    | some a' => exact ih _ _ (fun b v t => h b v.succ t) a' s'

/-- The streaming implementation replayed from typed choices gives the same tally and bit
as `tally`. The state monad holds the replay cursor, which belongs to the choice provider. -/
theorem tallyM_replay (edge : Fin N → Fin N → Bool) (source target : Fin N)
    (k : ℕ) (branch : Branch N) :
    (tallyM (readSelection branch) readNext (fun u v => pure (edge u v))
      source target k []).1 =
      tally edge source target k branch := by
  unfold tallyM tally tallyPrefix
  simp only [Fin.castLE_refl]
  exact foldlM_replay _ _ (fun _ _ _ => rfl) _ _

/-- Read the membership bit when both observed totals match the expected tally. -/
@[expose] def Result.finish (expected : Tally) (result : Result) : Option Bool :=
  if result.tally.matches expected then some result.hit else none

/-- Run the streaming membership scan with the terminal tally check. A successful negative
answer is `some false`; rejection is `none`. -/
def runM [Monad m] (select : Fin N → m Bool) (next : m (Option (Fin N)))
    (edge : Fin N → Fin N → m Bool) (source target : Fin N) (k : ℕ)
    (expected : Tally) : m (Option Bool) := do
  let result ← tallyM select next edge source target k
  return result.bind (Result.finish expected)

/-- Replay with the terminal tally check. -/
def run (edge : Fin N → Fin N → Bool) (source target : Fin N) (k : ℕ)
    (expected : Tally) (branch : Branch N) : Option Bool :=
  (tally edge source target k branch).bind (Result.finish expected)

/-- The terminal scan checks the required totals after processing all candidates. -/
theorem run_eq_finish (edge : Fin N → Fin N → Bool) (source target : Fin N) (k : ℕ)
    (expected : Tally) (branch : Branch N) :
    run edge source target k expected branch =
      (tallyPrefix edge source target k branch le_rfl).bind (Result.finish expected) := by
  rw [run, tally]

/-- Feeding the streaming scanner a typed branch implements its replay, including the
terminal tally test. -/
theorem runM_replay (edge : Fin N → Fin N → Bool) (source target : Fin N)
    (k : ℕ) (expected : Tally) (branch : Branch N) :
    (runM (readSelection branch) readNext (fun u v => pure (edge u v))
      source target k expected []).1 =
      run edge source target k expected branch := by
  unfold runM run
  simp only [bind, StateT.bind]
  rcases ht : tallyM (readSelection branch) readNext (fun u v => pure (edge u v))
    source target k [] with ⟨res, _⟩
  exact congrArg (Option.bind · (Result.finish expected))
    ((ht ▸ tallyM_replay edge source target k branch : (res, _).1 = _))

private def contribution (target : Fin N) (branch : Branch N) (v : Fin N) : Result :=
  ⟨⟨(branch v).isSome.toNat, ((branch v).getD []).length⟩, v == target && (branch v).isSome⟩

open scoped Classical in
private theorem candidate_spec (edge : Fin N → Fin N → Bool) (source target : Fin N)
    (k : ℕ) (branch : Branch N) (v : Fin N) :
    candidate edge source target k branch v =
      if ∀ p, transcript source branch v = some p →
          p.IsChainFromTo (fun u v => edge u v = true) source v ∧
            guessedLength (transcript source branch) v ≤ k
      then some (contribution target branch v) else none := by
  classical
  cases hb : branch v with
  | none => simp [candidate_eq, contribution, transcript, Result.zero, hb]
  | some tail =>
    simp only [candidate_eq, contribution, transcript, guessedLength, hb, Option.map_some,
      Option.some.injEq, forall_eq', Option.getD_some, List.length_cons, Nat.add_sub_cancel]
    cases hw : walk edge v k source tail with
    | none =>
      refine (ite_eq_right fun ⟨hc, hl⟩ => ?_).symm
      have hs : walk edge v k source tail = some (k - tail.length) :=
        walkM_replay_eq_some.mpr ⟨hc, Nat.sub_add_cancel hl⟩
      simp [hw] at hs
    | some left =>
      obtain ⟨hc, hl⟩ := walkM_replay_eq_some.mp hw
      simp [Result.ofWalk, hc, show tail.length ≤ k by omega, show k - left = tail.length by omega]

private noncomputable def aggregate (f : Fin N → Result) : Result := by
  classical
  exact ⟨⟨∑ v, (f v).tally.count, ∑ v, (f v).tally.lengthSum⟩,
    decide (∃ v, (f v).hit = true)⟩

open scoped Classical in
private theorem foldlM_spec (ok : Fin N → Prop) (f : Fin N → Result)
    (g : Fin N → Option Result) (hg : ∀ v, g v = if ok v then some (f v) else none)
    (acc : Result) :
    Fin.foldlM N (fun a v => (g v).map (add a)) acc =
      if ∀ v, ok v then some (add acc (aggregate f)) else none := by
  classical
  induction N with
  | zero => simp [Fin.foldlM_zero, aggregate, add]
  | succ N ih =>
    rw [Fin.foldlM_succ_last]
    dsimp only
    rw [ih (fun v => ok v.castSucc) (fun v => f v.castSucc)
      (fun v => g v.castSucc) (fun v => hg v.castSucc)]
    simp only [Fin.forall_fin_succ' (P := ok), hg (Fin.last N)]
    by_cases hp : ∀ v : Fin N, ok v.castSucc <;> by_cases hl : ok (Fin.last N) <;>
      simp [hp, hl, add, aggregate, Fin.sum_univ_castSucc, Fin.exists_fin_succ',
        Nat.add_assoc, Bool.or_assoc]

private theorem contribution_matches (source target : Fin N) (branch : Branch N) :
    aggregate (contribution target branch) =
      ⟨observed (transcript source branch), (branch target).isSome⟩ := by
  classical
  have hs : selected (transcript source branch) =
      Finset.univ.filter (fun v => (branch v).isSome) := by
    ext v
    cases h : branch v <;> simp [transcript, h]
  have hcount : ∑ v, (branch v).isSome.toNat = (selected (transcript source branch)).card := by
    rw [Finset.card_eq_sum_ones, hs, Finset.sum_filter]
    exact Finset.sum_congr rfl fun v _ => by cases branch v <;> rfl
  have hsum : ∑ v, ((branch v).getD []).length =
      ∑ v ∈ selected (transcript source branch), guessedLength (transcript source branch) v := by
    rw [hs, Finset.sum_filter]
    exact Finset.sum_congr rfl fun v _ => by
      cases h : branch v <;> simp [guessedLength, transcript, h]
  have hh : decide (∃ v, (contribution target branch v).hit = true) =
      (branch target).isSome := by simp [contribution]
  unfold aggregate
  rw [hh]
  simp only [contribution, hcount, hsum, observed]

open scoped Classical in
private theorem tally_spec (edge : Fin N → Fin N → Bool) (source target : Fin N)
    (k : ℕ) (branch : Branch N) :
    tally edge source target k branch =
      if ∀ v p, transcript source branch v = some p →
          p.IsChainFromTo (fun u v => edge u v = true) source v ∧
            guessedLength (transcript source branch) v ≤ k
      then some ⟨observed (transcript source branch), (branch target).isSome⟩ else none := by
  classical
  unfold tally tallyPrefix
  simp only [Fin.castLE_refl]
  have hf := foldlM_spec
    (fun v => ∀ p, transcript source branch v = some p →
      p.IsChainFromTo (fun u v => edge u v = true) source v ∧
        guessedLength (transcript source branch) v ≤ k)
    (contribution target branch) (candidate edge source target k branch)
    (fun v => by
      rw [candidate_spec]
      split <;> rfl) Result.zero
  rw [hf, contribution_matches source]
  split
  · simp [add, Result.zero]
  · rfl

/-- With exact round totals, success checks precisely the transcript contract and returns
the membership bit for the queried vertex. -/
theorem run_eq_some_iff (edge : Fin N → Fin N → Bool) (source target : Fin N)
    (k : ℕ) (branch : Branch N) (hit : Bool) :
    run edge source target k (expected (fun u v => edge u v = true) source k) branch = some hit ↔
      Passes (fun u v => edge u v = true) source k (transcript source branch) ∧
        (branch target).isSome = hit := by
  classical
  unfold run Passes
  rw [tally_spec]
  by_cases h : ∀ v p, transcript source branch v = some p →
      p.IsChainFromTo (fun u v => edge u v = true) source v ∧
        guessedLength (transcript source branch) v ≤ k
  · rw [ite_eq_left h]
    change (if (observed (transcript source branch)).matches _ then _ else none) = some hit ↔ _
    split <;> rename_i hm
    · exact ⟨fun he => ⟨⟨h, hm⟩, Option.some.inj he⟩, fun he => congrArg some he.2⟩
    · simp only [reduceCtorEq, hm, false_and, and_false]
  · rw [ite_eq_right h]
    simp [Option.bind, h]

/-- The streaming scanner with the canonical choice provider returns a bit exactly when
the corresponding transcript passes, and that bit records selection of the target. -/
theorem runM_eq_some_iff (edge : Fin N → Fin N → Bool) (source target : Fin N)
    (k : ℕ) (branch : Branch N) (hit : Bool) :
    (runM (readSelection branch) readNext (fun u v => pure (edge u v)) source target k
        (expected (fun u v => edge u v = true) source k) []).1 = some hit ↔
      Passes (fun u v => edge u v = true) source k (transcript source branch) ∧
        (branch target).isSome = hit := by
  rw [runM_replay, run_eq_some_iff]

/-- A successful scan with exact round totals reports bounded reachability at its target. -/
theorem hit_iff_reachable (edge : Fin N → Fin N → Bool) (source target : Fin N)
    (k : ℕ) (branch : Branch N) (hit : Bool)
    (h : (runM (readSelection branch) readNext (fun u v => pure (edge u v)) source target k
        (expected (fun u v => edge u v = true) source k) []).1 = some hit) :
    hit ↔ target ∈ Relation.reachableWithin (fun u v => edge u v = true) source k := by
  obtain ⟨hpass, hhit⟩ := (runM_eq_some_iff edge source target k branch hit).mp h
  simpa only [transcript, Option.isSome_map, hhit] using (isSome_iff (v := target) hpass)

private theorem transcript_tail (edge : Fin N → Fin N → Bool) (source : Fin N) (k : ℕ)
    (w : Transcript (Fin N)) (hw : Passes (fun u v => edge u v = true) source k w) :
    transcript source (fun v => (w v).map List.tail) = w := by
  funext v
  cases h : w v with
  | none => simp [transcript, h]
  | some p =>
    have hc := (hw.1 v p h).1
    change ((w v).map List.tail).map (source :: ·) = some p
    rw [h, Option.map_some, Option.map_some, ← hc.head_eq, List.cons_head_tail hc.ne_nil]

/-- Successful typed branches are in bijection with passing transcripts. The inverse deletes
the initial source of each selected walk. -/
noncomputable def successfulBranches (edge : Fin N → Fin N → Bool) (source target : Fin N)
    (k : ℕ) :
    {b : Branch N // (run edge source target k
      (expected (fun u v => edge u v = true) source k) b).isSome} ≃
    {w : Transcript (Fin N) // Passes (fun u v => edge u v = true) source k w} where
  toFun b := ⟨transcript source b.val, by
    obtain ⟨hit, hhit⟩ := Option.isSome_iff_exists.mp b.property
    exact (run_eq_some_iff edge source target k b.val hit).mp hhit |>.1⟩
  invFun w := ⟨fun v => (w.val v).map List.tail, by
    apply Option.isSome_iff_exists.mpr
    refine ⟨_, (run_eq_some_iff edge source target k _ _).mpr ⟨?_, rfl⟩⟩
    simpa only [transcript_tail edge source k w.val w.property] using w.property⟩
  left_inv b := by
    apply Subtype.ext
    funext v
    cases h : b.val v <;> simp [transcript, h]
  right_inv w := Subtype.ext (transcript_tail edge source k w.val w.property)

/-- At the exact round totals, a unique passing transcript gives a unique successful branch,
including when the branch answers false. -/
theorem existsUnique_successful_branch (edge : Fin N → Fin N → Bool) (source target : Fin N)
    (k : ℕ) (h : ∃! w, Passes (fun u v => edge u v = true) source k w) :
    ∃! b, (run edge source target k (expected (fun u v => edge u v = true) source k) b).isSome :=
  (successfulBranches edge source target k).existsUnique_subtype_congr.mpr h

private theorem candidate_registers_le (edge : Fin N → Fin N → Bool)
    (source target : Fin N) (k : ℕ) (branch : Branch N) (v : Fin N)
    (r : Result) (hr : candidate edge source target k branch v = some r) :
    r.tally.count ≤ 1 ∧ r.tally.lengthSum ≤ k := by
  rw [candidate_eq] at hr
  cases h : branch v <;> simp only [h, Option.some.injEq] at hr
  · subst r
    simp [Result.zero]
  · obtain ⟨left, _, rfl⟩ := Option.map_eq_some_iff.mp hr
    exact ⟨le_rfl, Nat.sub_le _ _⟩

private theorem foldlM_registers_le (g : Fin N → Option Result) (k : ℕ)
    (hg : ∀ v r, g v = some r → r.tally.count ≤ 1 ∧ r.tally.lengthSum ≤ k)
    (r : Result) (hr : Fin.foldlM N (fun acc v => (g v).map (add acc)) Result.zero = some r) :
    r.tally.count ≤ N ∧ r.tally.lengthSum ≤ N * k := by
  induction N generalizing r with
  | zero =>
    simp only [Fin.foldlM_zero, pure, Option.some.injEq] at hr
    subst r
    simp [Result.zero]
  | succ N ih =>
    rw [Fin.foldlM_succ_last] at hr
    change ((Fin.foldlM N (fun acc v => (g v.castSucc).map (add acc)) Result.zero).bind
      (fun acc => (g (Fin.last N)).map (add acc))) = some r at hr
    obtain ⟨partialResult, hp, hr⟩ := Option.bind_eq_some_iff.mp hr
    obtain ⟨last, hl, rfl⟩ := Option.map_eq_some_iff.mp hr
    have hb := ih (fun v => g v.castSucc) (fun v => hg v.castSucc) partialResult hp
    have hlast := hg (Fin.last N) last hl
    exact ⟨Nat.add_le_add hb.1 hlast.1,
      (Nat.add_le_add hb.2 hlast.2).trans_eq (Nat.succ_mul N k).symm⟩

/-- In any successfully processed prefix, the count is bounded by the number of processed
vertices, and the length sum by that number times the walk budget. The prefix may be followed
by invalid guesses. -/
theorem prefix_registers_le (edge : Fin N → Fin N → Bool) (source target : Fin N)
    (k : ℕ) (branch : Branch N) {n : ℕ} (hn : n ≤ N) (r : Result)
    (hr : tallyPrefix edge source target k branch hn = some r) :
    r.tally.count ≤ n ∧ r.tally.lengthSum ≤ n * k :=
  foldlM_registers_le _ _ (fun v => candidate_registers_le edge source target k branch
    (v.castLE hn)) r hr

private theorem walkM_clock {σ : Type} (clock : σ → ℕ)
    (next : StateM σ (Option (Fin N))) (edge : Fin N → Fin N → StateM σ Bool)
    (hn : ∀ s, clock (next s).2 ≤ clock s + 1)
    (he : ∀ u v s, clock (edge u v s).2 ≤ clock s + 1)
    (target current : Fin N) (k : ℕ) (s : σ) :
    clock (walkM next edge target k current s).2 ≤ clock s + (2 * k + 1) := by
  induction k generalizing current s with
  | zero =>
    rw [walkM, show 2 * 0 + 1 = 1 + 0 by rfl]
    apply bind_stateM_clock clock 1 0 _ _ hn
    intro result t
    cases result <;> exact le_rfl
  | succ k ih =>
    rw [walkM, show 2 * (k + 1) + 1 = 1 + (1 + (2 * k + 1)) by omega]
    apply bind_stateM_clock clock 1 (1 + (2 * k + 1)) _ _ hn
    intro result t
    cases result with
    | none => exact Nat.le_add_right (clock t) _
    | some v =>
      apply bind_stateM_clock clock 1 (2 * k + 1) _ _ (he current v)
      intro answer u
      cases answer with
      | false => exact Nat.le_add_right (clock u) _
      | true => exact ih v u

/-- All branches use at most `N * (2 * k + 2)` callback actions when each selection,
destination read, or adjacency query advances the clock by at most one. This bound includes
walks that fail an edge test or try to exceed the round budget. -/
theorem tallyM_clock {σ : Type} (clock : σ → ℕ)
    (select : Fin N → StateM σ Bool) (next : StateM σ (Option (Fin N)))
    (edge : Fin N → Fin N → StateM σ Bool) (source target : Fin N) (k : ℕ)
    (hs : ∀ v s, clock (select v s).2 ≤ clock s + 1)
    (hn : ∀ s, clock (next s).2 ≤ clock s + 1)
    (he : ∀ u v s, clock (edge u v s).2 ≤ clock s + 1) (s : σ) :
    clock (tallyM select next edge source target k s).2 ≤ clock s + N * (2 * k + 2) := by
  unfold tallyM
  apply foldlM_optionT_clock
  intro acc v state
  have hselect := hs v state
  simp only [OptionT.run, OptionT.mk, candidateM, bind, StateT.bind]
  rcases hc : select v state with ⟨choice, t⟩
  rw [hc] at hselect
  change clock t ≤ clock state + 1 at hselect
  cases choice
  · change clock t ≤ _
    omega
  · simp only [ite_true, bind, StateT.bind]
    have hwalk := walkM_clock clock next edge hn he v source k t
    rcases hw : walkM next edge v k source t with ⟨_, u⟩
    rw [hw] at hwalk
    change clock u ≤ _ at hwalk ⊢
    omega

/-- The terminal tally check adds no callback action to `tallyM_clock`. Both a rejected scan
and a successful false membership answer retain the same callback-action bound. -/
theorem runM_clock {σ : Type} (clock : σ → ℕ)
    (select : Fin N → StateM σ Bool) (next : StateM σ (Option (Fin N)))
    (edge : Fin N → Fin N → StateM σ Bool) (source target : Fin N) (k : ℕ) (expected : Tally)
    (hs : ∀ v s, clock (select v s).2 ≤ clock s + 1)
    (hn : ∀ s, clock (next s).2 ≤ clock s + 1)
    (he : ∀ u v s, clock (edge u v s).2 ≤ clock s + 1) (s : σ) :
    clock (runM select next edge source target k expected s).2 ≤
      clock s + N * (2 * k + 2) := by
  have h := tallyM_clock clock select next edge source target k hs hn he s
  cases ht : tallyM select next edge source target k s with
  | mk result state =>
    simpa only [runM, bind, StateT.bind, pure, StateT.pure, ht] using h

end Cslib.DoubleCounting.Scan
