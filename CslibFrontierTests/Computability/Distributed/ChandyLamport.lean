/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.Distributed.ChandyLamport.Correctness

/-! Chandy–Lamport consistent global snapshots on asynchronous FIFO networks (checked as a `module`
client with ordinary imports): concrete 3-process token-passing ring on `Fin 3` where the assembled
snapshot `S* = extractSnapshot S_final` is strictly distinct from every physical state `project S_k`
visited along the 8-step execution, yet conserves total tokens (`totalTokens = 2`) and arises as the
intermediate state of the explicit `tracePreEvents`-before-`tracePostEvents` causal permutation;
stable-property detection (`stablePred_transfer`) for bounded token count, token-loss refutation,
and deadlock (`isStablePred_isTerminal`); polymorphic typeclass-minimality checks on infinite types;
and end-to-end non-vacuity of `snapshot_liveness` and `snapshot_liveness_complete`. -/
set_option linter.privateModule false

namespace CslibFrontierTests.Distributed.ChandyLamport

open Cslib Cslib.ωSequence Cslib.Distributed.ChandyLamport

/-! ### Concrete 3-process directed token-passing ring (`0 → 1 → 2 → 0`) -/

private theorem fin3_cases (x : Fin 3) : x = 0 ∨ x = 1 ∨ x = 2 := by
  revert x; decide

/-- Directed 3-cycle `0 → 1 → 2 → 0` on `Fin 3`. -/
abbrev ringGraph : Digraph (Fin 3) :=
  Digraph.mk' fun u v => decide (v = u + 1)

instance instDecidableRelRingGraph : DecidableRel ringGraph.Adj := fun u v =>
  inferInstanceAs (Decidable (decide (v = u + 1) = true))

theorem ringGraph_stronglyConnected : StronglyConnected ringGraph := by
  intro u v
  rcases fin3_cases u with rfl | rfl | rfl <;> rcases fin3_cases v with rfl | rfl | rfl
  · exact .refl
  · exact .single (by decide)
  · exact .tail (b := 1) (.single (by decide)) (by decide)
  · exact .tail (b := 2) (.single (by decide)) (by decide)
  · exact .refl
  · exact .single (by decide)
  · exact .single (by decide)
  · exact .tail (b := 0) (.single (by decide)) (by decide)
  · exact .refl

/-- Asynchronous token-passing system on `ringGraph`: any process holding at least one token may
spontaneously send a token `()` to `p + 1`, and receiving `()` increments the recipient's token
count by `1`. -/
abbrev tokenSys : System (Fin 3) ℕ Unit where
  graph := ringGraph
  internal p st st' sent := 0 < st ∧ st' = st - 1 ∧ sent = [(p + 1, ())]
  recv _ _ st _ st' sent := st' = st + 1 ∧ sent = []

instance instDecidableTokenInternal (p : Fin 3) (st st' : ℕ) (sent : List (Fin 3 × Unit)) :
    Decidable (tokenSys.internal p st st' sent) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

instance instDecidableTokenRecv (src dest : Fin 3) (st : ℕ) (msg : Unit) (st' : ℕ)
    (sent : List (Fin 3 × Unit)) : Decidable (tokenSys.recv src dest st msg st' sent) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem tokenSys_inputEnabled : tokenSys.InputEnabled := by
  intro _ _ _ st _
  exact ⟨st + 1, [], ⟨rfl, rfl⟩, by simp⟩

/-- Total number of tokens across all 3 processes and all 9 FIFO channels. -/
def totalTokens (s : GlobalState (Fin 3) ℕ Unit) : ℕ :=
  (s.proc 0 + s.proc 1 + s.proc 2) +
    ((s.chan 0 0).length + (s.chan 0 1).length + (s.chan 0 2).length +
      (s.chan 1 0).length + (s.chan 1 1).length + (s.chan 1 2).length +
      (s.chan 2 0).length + (s.chan 2 1).length + (s.chan 2 2).length)

/-- Every transition of `tokenSys.lts` conserves `totalTokens`. -/
theorem tokenSys_totalTokens_tr {s s' : GlobalState (Fin 3) ℕ Unit} {e : Event (Fin 3) ℕ Unit}
    (htr : tokenSys.lts.Tr s e s') : totalTokens s' = totalTokens s := by
  obtain ⟨hen, rfl⟩ := htr
  cases e with
  | internal p st' sent =>
    rcases hen with ⟨⟨hpos, rfl, rfl⟩, _⟩
    rcases fin3_cases p with rfl | rfl | rfl <;>
      · simp only [totalTokens, GlobalState.applyEvent, GlobalState.applyLocal, outgoingTo,
          Fin.isValue, Fin.reduceAdd, Fin.reduceEq, ↓reduceIte, List.filterMap_cons,
          List.filterMap_nil, List.length_append, List.length_singleton, List.append_nil]
        omega
  | recv src dest msg st' sent =>
    rcases hen with ⟨hadj, hhead, ⟨rfl, rfl⟩, _⟩
    obtain ⟨t, ht⟩ := List.head?_eq_some_iff.mp hhead
    rcases fin3_cases src with rfl | rfl | rfl <;>
      rcases fin3_cases dest with rfl | rfl | rfl <;>
      first
      | exact False.elim ((by decide : ¬ ringGraph.Adj _ _) hadj)
      | (simp only [totalTokens, GlobalState.applyEvent, GlobalState.applyLocal,
            GlobalState.popChan, outgoingTo_nil, List.append_nil, Fin.isValue, Fin.reduceEq,
            and_self, and_false, false_and, ↓reduceIte, ht, List.tail_cons, List.length_cons]
         omega)

theorem isStablePred_totalTokens_eq (k : ℕ) :
    IsStablePred tokenSys (fun s => totalTokens s = k) :=
  fun _ _ _ htr hk => (tokenSys_totalTokens_tr htr).trans hk

theorem isStablePred_totalTokens_le (k : ℕ) :
    IsStablePred tokenSys (fun s => totalTokens s ≤ k) :=
  fun _ _ _ htr hk => (tokenSys_totalTokens_tr htr).le.trans hk

/-! ### 8-step trace whose recorded snapshot `S*` equals NO physical state along the execution -/

/-- Initial 2-token configuration: process `0` holds `1`, process `1` holds `0`, process `2` holds
`1`, and all channels are empty. -/
def s₀ : GlobalState (Fin 3) ℕ Unit where
  proc
    | 0 => 1
    | 1 => 0
    | 2 => 1
  chan _ _ := []

/-- Pre-snapshot lift of `s₀`. -/
def S₀ : SnapGlobalState (Fin 3) ℕ Unit := liftState s₀

/-- Concrete 8-step Chandy–Lamport execution:
1. `0` initiates the snapshot (`snapState 0 = some 1`, `.marker` on `0 → 1`).
2. `Post` at `0`: `0` sends its token to `1` behind `.marker` (`proc = (0, 0, 1)`).
3. `Pre` at `2`: unrecorded `2` sends its token to `0` (`proc = (0, 0, 0)`, `chan 2 0 = [.app ()]`).
4. `Post` at `0`: recorded `0` receives `2`'s token while `chanRec 2` is `.recording []`, recording
   `chanRec 2 = .recording [()]` (`proc = (1, 0, 0)`, `chan 2 0 = []`).
5. `1` receives `.marker` from `0` (`snapState 1 = some 0`, `.marker` on `1 → 2`).
6. `2` receives `.marker` from `1` (`snapState 2 = some 0`, `.marker` on `2 → 0`).
7. `0` receives `.marker` from `2` (`chanRec 2` finalized as `.done [()]`).
8. `Post` at `1`: recorded `1` receives `0`'s post-snapshot token after `chanRec 0 = .done []`, so
   `chanRec 0` remains `.done []` (`proc = (1, 1, 0)`, all channels `[]`). -/
def witnessTrace : List (SnapEvent (Fin 3) ℕ Unit) :=
  [ .initiateSnapshot 0
  , .app (.internal 0 0 [(1, ())])
  , .app (.internal 2 0 [(0, ())])
  , .app (.recv 2 0 () 1 [])
  , .recvMarker 0 1
  , .recvMarker 1 2
  , .recvMarker 2 0
  , .app (.recv 0 1 () 1 [])
  ]

def S_final : SnapGlobalState (Fin 3) ℕ Unit :=
  tokenSys.runSnapEvents S₀ witnessTrace

/-- Assembled Chandy–Lamport snapshot `S*`. -/
def S_star : GlobalState (Fin 3) ℕ Unit :=
  extractSnapshot S_final

/-- Expected snapshot state: `proc = (1, 0, 0)` with one in-flight token on channel `2 → 0`. -/
def expectedSnapshot : GlobalState (Fin 3) ℕ Unit where
  proc
    | 0 => 1
    | 1 => 0
    | 2 => 0
  chan u v := if u = 2 ∧ v = 0 then [()] else []

theorem witness_isPreSnapshot : tokenSys.IsPreSnapshot S₀ := by decide

theorem witness_mTr : tokenSys.snapLts.MTr S₀ witnessTrace S_final := by decide

theorem witness_complete : IsSnapshotComplete S_final := by decide

theorem witness_snapshot_eq : S_star = expectedSnapshot := by decide

/-- `S*` does not appear among the 9 physical states `project S_0, ..., project S_8` visited along
`witnessTrace`! -/
theorem witness_not_in_physical_states :
    (tokenSys.snapStates S₀ witnessTrace).length = 9 ∧
    S_star ∉ (tokenSys.snapStates S₀ witnessTrace).map project := by decide

/-- Formal prefix-split non-physicality: for every decomposition `witnessTrace = xl₁ ++ xl₂` through
an intermediate augmented state `S_k`, the recorded snapshot `S_star` differs from `project S_k`. -/
theorem witness_ne_every_intermediate_state {xl₁ xl₂ : List (SnapEvent (Fin 3) ℕ Unit)}
    {S_k : SnapGlobalState (Fin 3) ℕ Unit}
    (hsplit : witnessTrace = xl₁ ++ xl₂)
    (hm₁ : tokenSys.snapLts.MTr S₀ xl₁ S_k)
    (hm₂ : tokenSys.snapLts.MTr S_k xl₂ S_final) :
    S_star ≠ project S_k := by
  intro heq
  have hmem : S_k ∈ tokenSys.snapStates S₀ witnessTrace :=
    (tokenSys.mem_snapStates_iff_split witness_mTr).mpr ⟨xl₁, xl₂, hsplit, hm₁, hm₂⟩
  exact witness_not_in_physical_states.2 (heq ▸ List.mem_map_of_mem hmem)

/-- `S*` conserves total tokens (`totalTokens = 2`) and satisfies the explicit `Pre`-before-`Post`
causal reordering of `witnessTrace`. -/
theorem witness_causal_reordering_and_tokens :
    totalTokens s₀ = 2 ∧
    totalTokens S_star = 2 ∧
    totalTokens (project S_final) = 2 ∧
    tokenSys.tracePreEvents S₀ witnessTrace = [.internal 2 0 [(0, ())]] ∧
    tokenSys.tracePostEvents S₀ witnessTrace =
      [.internal 0 0 [(1, ())], .recv 2 0 () 1 [], .recv 0 1 () 1 []] ∧
    tokenSys.lts.MTr s₀ (tokenSys.tracePreEvents S₀ witnessTrace) S_star ∧
    tokenSys.lts.MTr S_star (tokenSys.tracePostEvents S₀ witnessTrace) (project S_final) := by
  decide

/-! ### Client instantiations of `chandyLamport_consistent_cut` and `stablePred_transfer` -/

example :
    tokenSys.lts.CanReach s₀ S_star ∧
    tokenSys.lts.CanReach S_star (project S_final) := by
  simpa [S₀, S_star] using
    tokenSys.chandyLamport_consistent_cut witness_isPreSnapshot witness_mTr witness_complete

example :
    tokenSys.lts.MTr s₀ (tokenSys.tracePreEvents S₀ witnessTrace) S_star ∧
    tokenSys.lts.MTr S_star (tokenSys.tracePostEvents S₀ witnessTrace) (project S_final) ∧
    (tokenSys.tracePreEvents S₀ witnessTrace ++
      tokenSys.tracePostEvents S₀ witnessTrace).Perm (eraseTrace witnessTrace) := by
  simpa [S₀, S_star] using
    tokenSys.chandyLamport_perm_mTr witness_isPreSnapshot witness_mTr witness_complete

-- Bounded token count (`totalTokens ≤ 2`) transfers forward from `S_star` to `project S_final`.
example : totalTokens (project S_final) ≤ 2 :=
  (tokenSys.stablePred_transfer (isStablePred_totalTokens_le 2)
    witness_isPreSnapshot witness_mTr witness_complete).1 (by decide)

-- Token-loss predicate (`totalTokens = 0`) is stable; since `totalTokens S_star ≠ 0`, `s₀` had not
-- lost all tokens either.
example : totalTokens s₀ ≠ 0 := by
  have hback := (tokenSys.stablePred_transfer (isStablePred_totalTokens_eq 0)
    witness_isPreSnapshot witness_mTr witness_complete).2 (by decide)
  simpa [S₀] using hback

-- Global deadlock (`tokenSys.lts.IsTerminal`) is a stable predicate; if `S_star` were deadlocked,
-- `project S_final` would also be deadlocked.
example (hterm : tokenSys.lts.IsTerminal S_star) :
    tokenSys.lts.IsTerminal (project S_final) :=
  (tokenSys.stablePred_transfer (isStablePred_isTerminal tokenSys)
    witness_isPreSnapshot witness_mTr witness_complete).1 hterm

-- Polymorphic check on infinite process/state/message types (`P = ℕ`, `S = ℕ → Prop`, `M = ℕ → ℕ`,
-- where neither `S` nor `M` has `DecidableEq` and `P` is infinite!).
example (sys : System ℕ (ℕ → Prop) (ℕ → ℕ)) [DecidableRel sys.graph.Adj]
    {S_init S_end : SnapGlobalState ℕ (ℕ → Prop) (ℕ → ℕ)}
    {xl : List (SnapEvent ℕ (ℕ → Prop) (ℕ → ℕ))}
    (hpre : sys.IsPreSnapshot S_init)
    (hmtr : sys.snapLts.MTr S_init xl S_end)
    (hcomp : IsSnapshotComplete S_end) :
    sys.lts.CanReach (project S_init) (extractSnapshot S_end) ∧
    sys.lts.CanReach (extractSnapshot S_end) (project S_end) :=
  sys.chandyLamport_consistent_cut hpre hmtr hcomp

/-! ### Non-blocking simulation & single-marker checks -/

example : ∀ u v : Fin 3, (S_final.chan u v).countP WireMsg.isMarker ≤ 1 :=
  tokenSys.count_marker_le_one witness_isPreSnapshot witness_mTr

example : ∀ u v : Fin 3, WireMsg.marker ∉ S_final.chan u v :=
  tokenSys.isSnapshotComplete_no_markers
    (tokenSys.snapInv_mTr witness_isPreSnapshot witness_mTr) witness_complete

-- At step 1 (`S₁ = initiateSnapshot 0` followed by `0` sending to `1`), channel `0 → 1` has
-- `[.marker, .app ()]`, yet `1` can still receive `()` in 2 steps via `snapMTr_appRecv_of_tr`!
example :
    let xl₁ : List (SnapEvent (Fin 3) ℕ Unit) :=
      [.initiateSnapshot 0, .app (.internal 0 0 [(1, ())])]
    let S₁ := tokenSys.runSnapEvents S₀ xl₁
    ∃ xl_sim S₁',
      xl_sim.length ≤ 2 ∧
      eraseTrace xl_sim = [.recv 0 1 () 1 []] ∧
      tokenSys.snapLts.MTr S₁ xl_sim S₁' := by
  intro xl₁ S₁
  have hm₁ : tokenSys.snapLts.MTr S₀ xl₁ S₁ := by decide
  have hinv₁ := tokenSys.snapInv_mTr witness_isPreSnapshot hm₁
  have htr_app : tokenSys.lts.Tr (project S₁) (.recv 0 1 () 1 [])
      ((project S₁).applyEvent (.recv 0 1 () 1 [])) := ⟨by decide, rfl⟩
  obtain ⟨xl_sim, S₁', hlen, herase, hmtr_sim, _⟩ := tokenSys.snapMTr_appRecv_of_tr hinv₁ htr_app
  exact ⟨xl_sim, S₁', hlen, herase, hmtr_sim⟩

/-! ### End-to-end liveness non-vacuity on `ringGraph` (`Fin 3`) and complete network `⊤` -/

/-- Unconditional existence of an infinite fair execution of `tokenSys.snapLts` from `S₀` on the
3-process directed ring in which `0` initiates a snapshot at step `0` and `IsSnapshotComplete`
holds permanently from some step `K` onward. -/
theorem tokenSys_exists_completing_fair_execution :
    ∃ ss xs K,
      ss 0 = S₀ ∧
      tokenSys.snapLts.OmegaExecution ss xs ∧
      FairChannels ss xs ∧
      ∀ k, K ≤ k → IsSnapshotComplete (ss k) := by
  let S₁ := tokenSys.stepSnap S₀ (.initiateSnapshot 0)
  have htr₀ : tokenSys.snapLts.Tr S₀ (.initiateSnapshot 0) S₁ := ⟨by decide, rfl⟩
  have hwf₀ : tokenSys.WellFormedSnapChan S₀ := fun _ _ _ => rfl
  have hwf₁ : tokenSys.WellFormedSnapChan S₁ :=
    tokenSys.wellFormedSnapChan_mTr (LTS.MTr.single tokenSys.snapLts htr₀) hwf₀
  obtain ⟨ss', xs', hss'0, hexec', hfair'⟩ :=
    tokenSys_inputEnabled.exists_fair_snapOmegaExecution hwf₁
  let ss : ωSequence (SnapGlobalState (Fin 3) ℕ Unit) := S₀ ::ω ss'
  let xs : ωSequence (SnapEvent (Fin 3) ℕ Unit) := SnapEvent.initiateSnapshot 0 ::ω xs'
  have hexec : tokenSys.snapLts.OmegaExecution ss xs := hexec'.cons htr₀ hss'0
  have hfair : FairChannels ss xs := by
    intro src dest k hne
    cases k with
    | zero => exact absurd rfl hne
    | succ k =>
      obtain ⟨j, hkj, hdel⟩ := hfair' src dest k hne
      exact ⟨j + 1, Nat.succ_le_succ hkj, hdel⟩
  have hinit : ((ss 1).proc 0).snapState.isSome = true := by
    simp [ss, hss'0, S₁, System.stepSnap, System.applyInitiate]
  obtain ⟨K, _, hK⟩ := tokenSys.snapshot_liveness ringGraph_stronglyConnected
    witness_isPreSnapshot hexec hfair hinit
  exact ⟨ss, xs, K, rfl, hexec, hfair, hK⟩

-- Complete-network specialization `snapshot_liveness_complete` on `⊤ : Digraph (Fin 4)`.
example (sys : System (Fin 4) ℕ ℕ) (htop : sys.graph = ⊤) [DecidableRel sys.graph.Adj]
    {ss : ωSequence (SnapGlobalState (Fin 4) ℕ ℕ)}
    {xs : ωSequence (SnapEvent (Fin 4) ℕ ℕ)}
    (hpre₀ : sys.IsPreSnapshot (ss 0))
    (hexec : sys.snapLts.OmegaExecution ss xs)
    (hfair : FairChannels ss xs)
    (hinit : ((ss 0).proc 0).snapState.isSome = true) :
    ∃ K, 0 ≤ K ∧ ∀ k, K ≤ k → IsSnapshotComplete (ss k) :=
  sys.snapshot_liveness_complete htop hpre₀ hexec hfair hinit

end CslibFrontierTests.Distributed.ChandyLamport
