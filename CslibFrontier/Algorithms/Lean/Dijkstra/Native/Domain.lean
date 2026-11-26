/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Dijkstra.Native.Word
import CslibFrontier.DataStructure.StateTransition.ClientMap

/-!
# Shared reached-state reasoning for native Dijkstra clients

These are the original binary consumer's abstract history, key-bound and scan/round facts,
shared with the Fibonacci consumer. They use the existing indexed-queue specification and
refinements, without assuming a heap representation or a zero potential. They certify source
and domain transport, not native instruction bounds.

## Main definitions

* `remainingEdges`: the original remaining adjacency scan.
* `abstractLoopStep`: the original extraction/scan round.

## Main results

* `remainingEdges_step`, `scan_valid_remainingEdges`: refinement and suffix validity along a scan.
* `abstractLoopStep_extract`: extraction-to-scan refinement and key-bound transport for one round.
* `client_keys`: the queued-key bound after an admissible client.
* `loopStep_eq_link`: complete program equality for the original round.
* `initial_loop_safe_insert`: initial loop admissibility after setting the source distance and
  inserting the source into the queue.
-/

public section

namespace Cslib.Algorithms.Lean.Dijkstra.Native

open Cslib.DataStructure Cslib.DataStructure.Memory Cslib.DataStructure.PriorityQueue
open Cslib.WordRAM Cslib.WordRAM.Realization

/-- The original relaxation history supplies the reached insert or decrease-key precondition. -/
theorem relax_valid_queue {n K V : ℕ}
    {pq : IndexedMinPQ.State n} {dist : Dictionary.State n} {adj : AdjacencyList.State n}
    (u v : Fin n) (du i c : ℕ)
    (hg : AdjacencyList.step adj (.edge u i) = (adj, (v, c)))
    (hv : (spec n K V).ValidHistory (pq, dist, adj)
      ((spec n K V).clientHistory (pq, dist, adj) (relaxEdge u du i))) :
    match dist v with
    | none => IndexedMinPQ.valid K pq (.insert v (du + c))
    | some old => du + c < old → IndexedMinPQ.valid K pq (.decreaseKey v (du + c)) := by
  unfold relaxEdge at hv
  dsimp only [edge, getDist, setDist, queue, StateTransitionSpec.clientHistory,
    StateTransitionSpec.runClient, PFunctor.FreeM.lift, PFunctor.FreeM.bind,
    Bind.bind, Pure.pure, PFunctor.FreeM.instBind, PFunctor.FreeM.instPure,
    StateTransitionSpec.stepFn, productStepFn] at hv
  rw [hg] at hv
  dsimp only [Dictionary.step, StateTransitionSpec.runClient, PFunctor.FreeM.bind,
    Bind.bind, Pure.pure, PFunctor.FreeM.instBind, PFunctor.FreeM.instPure] at hv
  rcases hd : dist v with _ | old
  · rw [hd] at hv
    exact hv.2.2.2.1
  · intro hc
    simp only [hd, ite_eq_left hc] at hv
    exact hv.2.2.2.1


/-- The suffix of the original adjacency scan after the first `i` edges. -/
@[expose] def remainingEdges {n K V : ℕ} (u : Fin n) (du b i : ℕ) :
    (spec n K V).Client Unit := (List.range' i (b - i)).forM (relaxEdge u du)

/-- A nonempty scan suffix exposes its next relaxation and remaining suffix. -/
theorem remainingEdges_cons {n K V : ℕ} (u : Fin n) (du b i : ℕ) (hi : i < b) :
    remainingEdges (K := K) (V := V) u du b i = (do
      relaxEdge u du i
      remainingEdges u du b (i + 1)) := by
  have he : b - i = (b - (i + 1)) + 1 := by omega
  rw [remainingEdges, he, List.range'_succ]; rfl

/-- A valid scan suffix retains the refinement invariant and next suffix validity. -/
theorem remainingEdges_step {n K V w : ℕ}
    (M : Refinement (spec n K V) (Memory.spec w)) (u : Fin n) (du b i : ℕ)
    (s : Memory.State) (hi : i < b) (hinv : M.inv s)
    (hv : (spec n K V).ValidHistory (M.abs s)
      ((spec n K V).clientHistory (M.abs s) (remainingEdges u du b i))) :
    (spec n K V).ValidHistory (M.abs s)
      ((spec n K V).clientHistory (M.abs s) (relaxEdge u du i)) ∧
    M.inv ((Memory.spec w).clientState s (link M.methods (relaxEdge u du i))) ∧
    (spec n K V).ValidHistory
      (M.abs ((Memory.spec w).clientState s (link M.methods (relaxEdge u du i))))
      ((spec n K V).clientHistory
        (M.abs ((Memory.spec w).clientState s (link M.methods (relaxEdge u du i))))
        (remainingEdges u du b (i + 1))) := by
  rw [remainingEdges_cons u du b i hi, StateTransitionSpec.clientHistory_bind,
    StateTransitionSpec.validHistory_append, StateTransitionSpec.run_runClient] at hv
  obtain ⟨_, _, he, hinv'⟩ := M.simulates_client (relaxEdge u du i) hinv hv.1
  exact ⟨hv.1, hinv', he.symm ▸ hv.2⟩

/-- An admissible `scan u du` history supplies an admissible `remainingEdges` suffix from `0`. -/
theorem scan_valid_remainingEdges {n K V : ℕ}
    {pq : IndexedMinPQ.State n} {dist : Dictionary.State n} {adj : AdjacencyList.State n}
    (u : Fin n) (du : ℕ)
    (hv : (spec n K V).ValidHistory (pq, dist, adj)
      ((spec n K V).clientHistory (pq, dist, adj) (scan u du))) :
    (spec n K V).ValidHistory (pq, dist, adj)
      ((spec n K V).clientHistory (pq, dist, adj) (remainingEdges u du (adj u).length 0)) := by
  unfold scan at hv
  dsimp only [degree, StateTransitionSpec.clientHistory, StateTransitionSpec.runClient,
    PFunctor.FreeM.lift, PFunctor.FreeM.bind, Bind.bind, Pure.pure,
    PFunctor.FreeM.instBind, PFunctor.FreeM.instPure, StateTransitionSpec.stepFn,
    productStepFn, AdjacencyList.step] at hv
  simpa only [remainingEdges, Nat.sub_zero, List.range_eq_range',
    StateTransitionSpec.clientHistory, AdjacencyList.step] using hv.2


/-- Every word-level round lowers the remaining-round counter, including the empty exit. -/
theorem loopStepWord_result_le (extract : Memory.Prog (Option (ℕ × ℕ)))
    (ins dec : ℕ → ℕ → Memory.Prog Unit) (T : Block)
    (A : AdjacencyList.Memory.Layout) (n : ℕ) (x : Unit × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientResult s (loopStepWord extract ins dec T A n x) ≤ x.2 - 1 := by
  unfold loopStepWord
  rw [StateTransitionSpec.clientResult_bind]
  rcases (Memory.spec 0).clientResult s extract with _ | ⟨u, du⟩
  · exact Nat.zero_le _
  · dsimp only
    split_ifs <;> simp only [client_simps, le_rfl, Nat.zero_le]

/-- One original abstract extraction and scan, with its early-exit round counter. -/
@[expose] def abstractLoopStep {n K V : ℕ} (a : ℕ) : (spec n K V).Client ℕ := do
  match ← queue .extractMin with
  | none => pure 0
  | some (u, du) => scan u du; pure (a - 1)

/-- A positive original loop exposes one complete round before its remainder. -/
theorem loop_eq_step {n K V : ℕ} (a : ℕ) (ha : a ≠ 0) :
    loop (n := n) (K := K) (V := V) a = (do
      let b ← abstractLoopStep (n := n) (K := K) (V := V) a
      loop b) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha
  rw [loop]
  unfold abstractLoopStep
  simp only [bind_assoc]
  congr 1 with e : 1
  rcases e with _ | ⟨u, du⟩
  · rfl
  · simp only [bind_assoc, pure_bind, Nat.succ_sub_one]

/-- The word-free round view is exactly the original linked abstract round. -/
theorem loopStep_eq_link {n K V w : ℕ}
    (M : Methods (spec n K V) (Memory.spec w)) (a : ℕ) :
    loopStep M ((), a) = link M (abstractLoopStep (K := K) (V := V) a) := by
  symm
  unfold loopStep abstractLoopStep link
  refine (PFunctor.FreeM.liftM_bind M (queue .extractMin) _).trans ?_
  have hq : (queue (n := n) (K := K) (V := V) .extractMin).liftM M = M (.inl .extractMin) :=
    PFunctor.FreeM.liftM_lift (P := (spec n K V).signature) M (.inl .extractMin)
  rw [hq]
  congr 1 with (_ | ⟨u, du⟩) : 1
  · rfl
  · dsimp only
    rw [PFunctor.FreeM.liftM_bind, scanView_eq]
    rfl

/-- An admissible indexed-queue step preserves the bound on every present key. -/
theorem indexed_step_keys {n K : ℕ} (s : IndexedMinPQ.State n) (o : IndexedMinPQ.Op n)
    (hv : IndexedMinPQ.valid K s o)
    (hb : ∀ v k, s v = some k → k ≤ K) :
    ∀ v k, (IndexedMinPQ.step s o).1 v = some k → k ≤ K := by
  cases o with
  | isEmpty | getKey _ => exact hb
  | insert u d | decreaseKey u d =>
    intro v k hk
    rcases eq_or_ne v u with rfl | h
    · simp only [IndexedMinPQ.step, Function.update_self, Option.some.injEq] at hk
      exact hk ▸ hv.2
    · exact hb v k (by simpa only [IndexedMinPQ.step, Function.update_of_ne h] using hk)
  | extractMin =>
    rcases hf : IndexedMinPQ.findMin s with _ | ⟨u, d⟩
    · simpa only [IndexedMinPQ.step, hf] using hb
    · intro v k hk
      rcases eq_or_ne v u with rfl | h
      · simp [IndexedMinPQ.step, hf] at hk
      · exact hb v k (by simpa only [IndexedMinPQ.step, hf, Function.update_of_ne h] using hk)

/-- A Dijkstra-interface step preserves the bound on every queued key. -/
theorem composite_step_keys {n K V : ℕ} (s : (spec n K V).State)
    (o : (spec n K V).Op) (hv : (spec n K V).valid s o)
    (hb : ∀ v k, s.1 v = some k → k ≤ K) :
    ∀ v k, ((spec n K V).stepFn s o).1.1 v = some k → k ≤ K := by
  cases o with
  | inl o => exact indexed_step_keys s.1 o hv hb
  | inr _ => exact hb

/-- An admissible Dijkstra history preserves the bound on every queued key. -/
theorem history_keys {n K V : ℕ} (s : (spec n K V).State)
    (os : List (spec n K V).Op) (hv : (spec n K V).ValidHistory s os)
    (hb : ∀ v k, s.1 v = some k → k ≤ K) :
    ∀ v k, ((spec n K V).run s os).1.1 v = some k → k ≤ K := by
  induction os generalizing s with
  | nil => exact hb
  | cons o os ih => exact ih _ hv.2 (composite_step_keys s o hv.1 hb)

/-- A valid Dijkstra client preserves the bound on every queued key. -/
theorem client_keys {n K V : ℕ} {α : Type} (s : (spec n K V).State)
    (p : (spec n K V).Client α)
    (hv : (spec n K V).ValidHistory s ((spec n K V).clientHistory s p))
    (hb : ∀ v k, s.1 v = some k → k ≤ K) :
    ∀ v k, ((spec n K V).clientState s p).1 v = some k → k ≤ K := by
  exact (spec n K V).run_runClient p s ▸ history_keys s _ hv hb

/-- A refinement and the original remaining scan justify every reached native step domain.
The proof excludes truncation by the actual increasing index, not by assuming a loop result. -/
theorem scan_while_safe {n K V w : ℕ}
    (M : Refinement (spec n K V) (Memory.spec w)) (u : Fin n) (du b : ℕ)
    (step : ℕ → Memory.Prog Unit) (safe : ℕ → ℕ → Memory.State → Prop)
    (heq : ∀ i, step i = link M.methods (relaxEdge u du i))
    (hsafe : ∀ i s, i < b → M.inv s →
      (spec n K V).ValidHistory (M.abs s)
        ((spec n K V).clientHistory (M.abs s) (relaxEdge u du i)) → safe w i s)
    (s : Memory.State) (hi : M.inv s) (hfit : Fits w b)
    (hv : (spec n K V).ValidHistory (M.abs s)
      ((spec n K V).clientHistory (M.abs s) (remainingEdges u du b 0)))
    (hm : (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s
      (boundedWhile (fun b i : ℕ => i < b) (fun x => do
        step x.2; pure (x.2 + 1)) b b 0))) :
    whileSafe (fun b i : ℕ => i < b) (fun x => do step x.2; pure (x.2 + 1))
      (fun w x s => safe w x.2 s ∧ Fits w (x.2 + 1)) w b b 0 s := by
  let I (i : ℕ) (s : Memory.State) := i ≤ b ∧ M.inv s ∧
    (spec n K V).ValidHistory (M.abs s)
      ((spec n K V).clientHistory (M.abs s) (remainingEdges u du b i))
  apply whileSafe_of_measure _ _ _ w b I (fun i _ => b - i) ?_ ?_ ⟨Nat.zero_le _, hi, hv⟩
    (by omega) hm
  · exact fun a _ _ hr hg => (Nat.sub_pos_of_lt hg).ne' hr
  · rintro a s ⟨hle, hinv₀, hv₀⟩ ha _
    obtain ⟨hfirst, hinv, hrest⟩ := remainingEdges_step M u du b a s ha hinv₀ hv₀
    have hstate : (Memory.spec 0).clientState s (do step a; pure (a + 1)) =
        (Memory.spec w).clientState s (link M.methods (relaxEdge u du a)) := by
      simpa only [client_simps, heq] using (clientState_width w (step a) s).symm
    refine ⟨⟨hsafe a s ha hinv₀ hfirst, hfit.of_le (by omega)⟩, ?_,
      by simpa only [client_simps] using Nat.sub_succ_lt_self b a ha⟩
    simpa only [I, client_simps, hstate] using ⟨Nat.succ_le_of_lt ha, hinv, hrest⟩

/-- The original remaining-round history and a strictly decreasing native counter justify a
complete early-exit loop. The existing key invariant is retained through every abstract step. -/
theorem loop_while_safe {n K V w : ℕ} {ε : Type}
    (M : Refinement (spec n K V) (Memory.spec w)) (e : ε)
    (guard : ε → ℕ → Prop) [∀ e, DecidablePred (guard e)] (body : ε × ℕ → Memory.Prog ℕ)
    (safe : ℕ → ε × ℕ → Memory.State → Prop)
    (hguard : ∀ a, guard e a ↔ 0 < a)
    (heq : ∀ a, body (e, a) = link M.methods (abstractLoopStep a))
    (hdown : ∀ a s, (Memory.spec 0).clientResult s (body (e, a)) ≤ a - 1)
    (hsafe : ∀ a s, 0 < a → M.inv s →
      (∀ v k, (M.abs s).1 v = some k → k ≤ K) →
      (spec n K V).ValidHistory (M.abs s)
        ((spec n K V).clientHistory (M.abs s) (abstractLoopStep a)) → safe w (e, a) s)
    (a₀ : ℕ) (s : Memory.State) (hi : M.inv s)
    (hk : ∀ v k, (M.abs s).1 v = some k → k ≤ K)
    (hv : (spec n K V).ValidHistory (M.abs s)
      ((spec n K V).clientHistory (M.abs s) (loop a₀)))
    (hm : (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (boundedWhile guard body e a₀ a₀))) :
    whileSafe guard body safe w e a₀ a₀ s := by
  let I (a : ℕ) (s : Memory.State) := M.inv s ∧
    (∀ v k, (M.abs s).1 v = some k → k ≤ K) ∧
    (spec n K V).ValidHistory (M.abs s)
      ((spec n K V).clientHistory (M.abs s) (loop a))
  apply whileSafe_of_measure _ _ _ w e I (fun a _ => a) ?_ ?_ ⟨hi, hk, hv⟩ le_rfl hm
  · exact fun a _ _ hr hg => ((hguard a).mp hg).ne' hr
  · rintro a s ⟨hinv₀, hkeys₀, hp⟩ ha _
    have hpos := (hguard a).mp ha
    rw [loop_eq_step a hpos.ne', StateTransitionSpec.clientHistory_bind,
      StateTransitionSpec.validHistory_append, StateTransitionSpec.run_runClient] at hp
    obtain ⟨_, hres, hst, hinv⟩ := M.simulates_client (abstractLoopStep a) hinv₀ hp.1
    refine ⟨hsafe a s hpos hinv₀ hkeys₀ hp.1, ?_,
      (hdown a s).trans_lt (Nat.sub_lt hpos Nat.one_pos)⟩
    rw [heq, ← clientResult_width w, ← clientState_width w]
    exact ⟨hinv, hst ▸ client_keys (M.abs s) (abstractLoopStep a) hp.1 hkeys₀,
      hst ▸ hres ▸ hp.2⟩

/-- Running an erased native `extractMin` on an admissible `abstractLoopStep` state either yields
`none` or yields `some (u.val, du)` for some `u : Fin n` with `du ≤ K` and an admissible `scan u du`
in the post-extraction state. -/
theorem abstractLoopStep_extract {n K V w a : ℕ}
    (M : Refinement (spec n K V) (Memory.spec w))
    (extract : Memory.Prog (Option (ℕ × ℕ)))
    (hex : extract =
      (M.methods (.inl .extractMin) : Memory.Prog (Option (Fin n × ℕ))).map
        (Option.map fun p => (p.1.val, p.2)))
    (s : Memory.State) (hf : M.inv s)
    (hb : ∀ v k, (M.abs s).1 v = some k → k ≤ K)
    (hv : (spec n K V).ValidHistory (M.abs s)
      ((spec n K V).clientHistory (M.abs s) (abstractLoopStep a))) :
    (Memory.spec 0).clientResult s extract = none ∨
      ∃ (u : Fin n) (du : ℕ),
        (Memory.spec 0).clientResult s extract = some (u.val, du) ∧
        du ≤ K ∧
        M.inv ((Memory.spec 0).clientState s extract) ∧
        (spec n K V).ValidHistory (M.abs ((Memory.spec 0).clientState s extract))
          ((spec n K V).clientHistory (M.abs ((Memory.spec 0).clientState s extract))
            (scan u du)) := by
  let q : Memory.Prog (Option (Fin n × ℕ)) := M.methods (.inl .extractMin)
  change extract = q.map (Option.map fun p => (p.1.val, p.2)) at hex
  rw [abstractLoopStep, StateTransitionSpec.clientHistory_bind,
    StateTransitionSpec.validHistory_append, StateTransitionSpec.run_runClient] at hv
  obtain ⟨hv1, htail⟩ := hv
  obtain ⟨_, hres, hstate, hinv⟩ := M.simulates_client (queue .extractMin) hf hv1
  have hql : link M.methods (queue (n := n) (K := K) (V := V) .extractMin) = q :=
    PFunctor.FreeM.liftM_lift (P := (spec n K V).signature) M.methods (.inl .extractMin)
  rw [hql, clientResult_width] at hres
  rw [hql, clientState_width] at hstate hinv
  rw [hex, PFunctor.FreeM.map_eq_map, StateTransitionSpec.clientResult_map,
    StateTransitionSpec.clientState_map, hres]
  rcases hq : (spec n K V).clientResult (M.abs s) (queue .extractMin) with _ | ⟨u, du⟩
  · exact .inl rfl
  · have hfind : IndexedMinPQ.findMin (M.abs s).1 = some (u, du) := by
      change (IndexedMinPQ.step (M.abs s).1 .extractMin).2 = some (u, du) at hq
      rcases h : IndexedMinPQ.findMin (M.abs s).1 with _ | ⟨v, dv⟩ <;>
        simpa only [IndexedMinPQ.step, h] using hq
    rw [hq, StateTransitionSpec.clientHistory_bind, StateTransitionSpec.validHistory_append]
      at htail
    exact .inr ⟨u, du, rfl, hb u du (IndexedMinPQ.findMin_eq_some_state hfind), hinv,
      hstate ▸ htail.1⟩

/-- Installing the source distance word at `f + G.source.val` and executing the queue insertion
`ins0` leaves an admissible main loop with queued keys bounded by `K`. -/
theorem initial_loop_safe_insert {K V w f : ℕ}
    (G : Cslib.Algorithms.Dijkstra.ListInstance)
    (hK : G.n * G.maxWeight ≤ K) (hV : G.n * G.maxWeight < V)
    (M : Refinement (spec G.n K V) (Memory.spec w))
    (ins0 : Memory.Prog Unit)
    (hset : M.methods (.inr (.inl (.insert G.source 0))) = write (f + G.source.val) 1)
    (hins : M.methods (.inl (.insert G.source 0)) = ins0)
    (s : Memory.State) (hi : M.inv s) (habs : M.abs s = init G) :
    let t := (Memory.spec 0).clientState
      ⟨Function.update s.mem (f + G.source.val) 1, s.frontier⟩ ins0
    M.inv t ∧ (∀ v k, (M.abs t).1 v = some k → k ≤ K) ∧
      (spec G.n K V).ValidHistory (M.abs t)
        ((spec G.n K V).clientHistory (M.abs t) (loop G.n)) := by
  let p : (spec G.n K V).Client Unit := do
    setDist G.source 0
    queue (.insert G.source 0)
  have hp : dijkstra (K := K) (V := V) G.source = (do p; loop G.n) := by
    exact (bind_assoc _ _ _).symm
  obtain ⟨hv, _⟩ := dijkstra_correct G hK hV
  rw [← habs, hp, StateTransitionSpec.clientHistory_bind,
    StateTransitionSpec.validHistory_append, StateTransitionSpec.run_runClient] at hv
  obtain ⟨_, _, hstate, hinv⟩ := M.simulates_client p hi hv.1
  have hpeq : link M.methods p = (do write (f + G.source.val) 1; ins0) := by
    exact (PFunctor.FreeM.liftM_bind M.methods (setDist G.source 0) _).trans
      (congrArg₂ Bind.bind
        ((PFunctor.FreeM.liftM_lift (P := (spec G.n K V).signature) M.methods
          (.inr (.inl (.insert G.source 0)))).trans hset)
        (funext fun _ => (PFunctor.FreeM.liftM_lift (P := (spec G.n K V).signature) M.methods
          (.inl (.insert G.source 0))).trans hins))
  rw [hpeq, StateTransitionSpec.clientState_bind, clientState_width] at hstate hinv
  refine ⟨hinv, hstate ▸ client_keys (M.abs s) p hv.1 fun v k hk => ?_, hstate ▸ hv.2⟩
  cases habs ▸ hk

end Cslib.Algorithms.Lean.Dijkstra.Native
