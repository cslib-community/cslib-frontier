/-
Copyright (c) 2026 Phillipp Schoppmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Phillipp Schoppmann
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.UC.MultiSession
import CslibFrontier.Crypto.Protocols.SSP.ParFinLazy
import CslibFrontier.Languages.Probabilistic.Oracle.Vector

/-!
# Dynamic-SID multi-session universal composition

This module extends the fixed-arity `Fin m` multi-session composition of
`CslibFrontier.Crypto.Protocols.UC.MultiSession` to an arbitrary `[DecidableEq SID]` type of
session identifiers with **lazy first-touch session creation**, bounded dynamically by the caller's
polynomial query budget.

## Scope and relation to [Canetti2020]

These results adapt Theorem 22 and Corollaries 23–24 of [Canetti2020] (JACM pp. 28:58–28:59; ePrint
2000/067, rev. February 11, 2020, pp. 61–62) to dynamically chosen session identifiers `sid : SID`
with depth-1 subroutine sessions in this library's call-bounded statistical UC model (**not the full
PPT ITM Theorem 22; `#6043` remains open**). Specifically:

1. **Dynamic first-touch `SID` creation vs. recursive ITI spawning.** Calling protocols and
   environments may query arbitrary `sid : SID` (including when `SID` is infinite, e.g., `ℕ` or
   `List Bool`); `dynParLazy` and `dynHybridSim` initialize each session's state lazily on its first
   access (matching the single-functionality lazy pattern of `IdealFunctionality.multiSession` in
   `CslibFrontier.Crypto.Protocols.UC.JointState`), and `mem_support_dynParLazy_touched_card_le`
   / `touchedSessions_transcript_card_le` prove that on every supported path of a `b`-bounded
   execution at most `b` distinct `SID`s are initialized or queried. Subroutines do not recursively
   spawn nested dynamic sub-sessions (depth-1 call tree).
2. **Homogeneous subroutine protocol `σ`.** Every dynamic session instantiates the same subroutine
   protocol `σ` (or `F.toProtocol`), whereas fixed-arity heterogeneous families are treated in
   `CslibFrontier.Crypto.Protocols.UC.MultiSession`.
3. **Call-bounded statistical model vs. PPT ITMs and §4.4.** `DynHybridProtocol.PolyBounded`,
   `Protocol.PolyBounded`, `Adversary.PolyBounded`, and `Environment.PolyBounded` count oracle
   calls and private samples per activation, leaving local computation, state size, and message
   length unbounded; corruptions `C : Finset (Fin n)` are static and shared across the calling
   protocol and all dynamic sessions; interfaces are pull-based. No implication to or from
   Canetti's PPT or §4.4 notions is claimed.

## Proof strategy

Given a `b`-query-bounded program over `dynSessionSpec SID E`, `allocMachine` assigns each newly
touched `sid : SID` to the next slot in `Fin (b + 1)` on first access
(`eval_run_dynParLazy_eq_parFin`), using `SSP.run_parFinLazy_eq_parFin` from
`CslibFrontier.Crypto.Protocols.SSP.ParFinLazy` to pass from lazy first-touch initialization to
eager `SSP.parFin` over `Fin (b + 1)`, and then invoking `SSP.advantage_parFin_le_sum` from
`CslibFrontier.Crypto.Protocols.SSP.Hybrid` / `MultiSession`.
Because `dynHybridSim` itself initializes simulator states lazily on first touch with per-activation
budget `2 * pD + 1`, a single simulator serves every environment budget `pZ` uniformly.

## Main definitions

* `Cslib.Crypto.Protocols.UC.dynSessionSpec`, `Cslib.Crypto.Protocols.UC.dynParLazy`: lazy
  first-touch parallel machine over an arbitrary `[DecidableEq SID]`.
* `Cslib.Crypto.Protocols.UC.touchedSessions`: `Finset SID` of session identifiers queried along a
  transcript.
* `Cslib.Crypto.Protocols.UC.DynSessionCall`, `Cslib.Crypto.Protocols.UC.dynPartySpec`,
  `Cslib.Crypto.Protocols.UC.DynHybridProtocol`,
  `Cslib.Crypto.Protocols.UC.DynHybridProtocol.PolyBounded`,
  `Cslib.Crypto.Protocols.UC.DynNetQ`: dynamic-SID hybrid protocol interfaces.
* `Cslib.Crypto.Protocols.UC.dynSessionRouter`, `Cslib.Crypto.Protocols.UC.dynHybridWrap`,
  `Cslib.Crypto.Protocols.UC.composeDyn`, `Cslib.Crypto.Protocols.UC.dynHybridSim`,
  `Cslib.Crypto.Protocols.UC.absorbDynHybrid`: dynamic-SID subroutine replacement, lazy
  parallel simulator, and absorbed hybrid distinguisher.
* `Cslib.Crypto.Protocols.UC.dynSessionHopPoly`: explicit polynomial budget bound for single-hop
  distinguishers.

## Main results

* `Cslib.Crypto.Protocols.UC.isBounded_dynParLazy`,
  `Cslib.Crypto.Protocols.UC.dynHybridSim_polyBounded`,
  `Cslib.Crypto.Protocols.UC.composeDyn_polyBounded`,
  `Cslib.Crypto.Protocols.UC.absorbDynHybrid_polyBounded`: call-budget preservation independent of
  any pre-chosen session count.
* `Cslib.Crypto.Protocols.UC.mem_support_dynParLazy_touched_card_le`,
  `Cslib.Crypto.Protocols.UC.touchedSessions_transcript_card_le`: at most `b` distinct sessions
  are initialized or queried along any `b`-bounded path.
* `Cslib.Crypto.Protocols.UC.eval_run_dynParLazy_eq_parFin`: finite first-touch reindexing and
  lazy-vs-eager equivalence with `SSP.parFin`.
* `Cslib.Crypto.Protocols.UC.EmulatesDummyWithin.composeDyn`,
  `Cslib.Crypto.Protocols.UC.EmulatesWithin.composeDyn`,
  `Cslib.Crypto.Protocols.UC.Emulates.composeDyn`,
  `Cslib.Crypto.Protocols.UC.Realizes.composeDyn`,
  `Cslib.Crypto.Protocols.UC.Realizes.composeDyn_trans`: concrete and asymptotic dynamic-SID
  universal composition.

## References

* [R. Canetti, *Universally Composable Security*][Canetti2020], J. ACM 67(5), Article 28, 2020:
  Section 6.1 (Theorem 22 p. 28:58; Corollaries 23–24 p. 28:59); IACR ePrint 2000/067 (rev.
  February 11, 2020), pp. 61–62.
* [C. Brzuska, A. Delignat-Lavaud, C. Fournet, K. Kohbrok, M. Kohlweiss, *State Separation for
  Code-Based Game-Playing Proofs*][BrzuskaDFKK2018]: `SSP.parFin`, `SSP.advantage_parFin_le_sum`.
-/

public section

namespace Cslib.Crypto.Protocols.UC

open OracleComp (sumHandler)
open scoped NNReal

/-! ### Dynamic-SID parallel sessions and lazy first-touch bounds -/

section DynPar

/-- Interface of dynamically indexed sessions over `SID`: a query pairs a session identifier
`sid : SID` with an `E`-query `q`, answered as `E q`. -/
abbrev dynSessionSpec (SID : Type) {ιE : Type} (E : ιE → Type) : SID × ιE → Type :=
  fun q => E q.2

/-- Lazy first-touch parallel composition of a family of closed machines `M : SID → Machine ...`
for an arbitrary `[DecidableEq SID]`. Each session `sid` starts uninitialized (`none`) and samples
`(M sid).init` on its first query. -/
@[expose] def dynParLazy {SID : Type} [DecidableEq SID] {ιE : Type} {E : ιE → Type}
    (M : SID → Machine OracleSpec.empty E) :
    Machine OracleSpec.empty (dynSessionSpec SID E) where
  State := (sid : SID) → Option (M sid).State
  init := pure fun _ => none
  handle
    | (sid, q) => fun s => do
        let st ← match s sid with
          | some st => pure st
          | none => ProbOracleComp.sample (M sid).init
        let (r, st') ← ((M sid).handle q).run st
        return (r, Function.update s sid (some st'))

/-- Every activation of `dynParLazy M` makes at most `2 * t` calls when each `(M sid)` is
`t`-bounded (at most `t` for first-touch initialization plus `t` for the activation itself). -/
theorem isBounded_dynParLazy {SID : Type} [DecidableEq SID] {ιE : Type} {E : ιE → Type}
    {M : SID → Machine OracleSpec.empty E} {t : ℕ} (hM : ∀ sid, (M sid).IsBounded t) :
    (dynParLazy M).IsBounded (2 * t) := by
  refine ⟨OracleComp.IsCostBounded.pure _ _, fun ⟨sid, q⟩ s => ?_⟩
  dsimp only [dynParLazy, StateT.run]
  cases s sid with
  | none =>
    have hinit : OracleComp.IsQueryBounded
        (ProbOracleComp.sample (spec := OracleSpec.empty) (M sid).init) t :=
      Machine.isQueryBounded_sample (hM sid).1
    refine (hinit.bind fun st =>
      ((hM sid).2 q st).bind fun x =>
        OracleComp.IsCostBounded.pure (x.1, Function.update s sid (some x.2)) 0).mono ?_
    omega
  | some st =>
    simp only [pure_bind]
    exact (((hM sid).2 q st).bind fun x =>
      OracleComp.IsCostBounded.pure (x.1, Function.update s sid (some x.2)) 0).mono (by omega)

/-- The `Finset SID` of session identifiers queried along a transcript over
`probOracleSpec (dynSessionSpec SID E)`. -/
def touchedSessions {SID : Type} [DecidableEq SID] {ιE : Type} {E : ιE → Type}
    (t : OracleComp.Transcript (probOracleSpec (dynSessionSpec SID E))) : Finset SID :=
  (t.filterMap fun entry =>
    match entry.1 with
    | .inl _ => none
    | .inr (sid, _) => some sid).toFinset

private theorem toFinset_filterMap_card_le_length {α β : Type} [DecidableEq β]
    (f : α → Option β) (xs : List α) :
    (xs.filterMap f).toFinset.card ≤ xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.filterMap_cons, List.length_cons]
    cases f x with
    | none => exact ih.trans (Nat.le_succ _)
    | some b =>
      simp only [List.toFinset_cons]
      exact (Finset.card_insert_le b _).trans (Nat.add_le_add_right ih 1)

/-- Along any supported run of a `b`-query-bounded program against a stateful oracle over
`probOracleSpec (dynSessionSpec SID E)`, the `Finset SID` of touched session IDs has cardinality at
most `b`. -/
theorem touchedSessions_transcript_card_le {SID : Type} [DecidableEq SID]
    {ιE : Type} {E : ιE → Type} {State γ : Type}
    {prog : ProbOracleComp (dynSessionSpec SID E) γ} {b : ℕ}
    (hprog : OracleComp.IsQueryBounded prog b)
    (oracle : (q : ℕ ⊕ (SID × ιE)) → StateT State PMF (probOracleSpec (dynSessionSpec SID E) q))
    {s s' : State} {res : γ}
    {t : OracleComp.Transcript (probOracleSpec (dynSessionSpec SID E))}
    (hmem : (res, s', t) ∈
      ((OracleComp.interpret (OracleComp.withTranscript oracle) prog).run (s, [])).support) :
    (touchedSessions t).card ≤ b :=
  (toFinset_filterMap_card_le_length _ t).trans (hprog.length_transcript_le oracle hmem)

/-- Along any supported run of `dynParLazy M` on a program making at most `b` external calls
(counting private coin samples at cost `0`), at most `b` new sessions become initialized
(`some`). -/
theorem mem_support_dynParLazy_touched_card_le {SID : Type} [DecidableEq SID]
    {ιE : Type} {E : ιE → Type} (M : SID → Machine OracleSpec.empty E) {γ : Type}
    {prog : ProbOracleComp (dynSessionSpec SID E) γ} {b : ℕ}
    (hprog : OracleComp.IsCostBounded (Sum.elim (fun _ => 0) (fun _ => 1)) prog b)
    (S₀ : Finset SID) (s₀ : (dynParLazy M).State) (hS₀ : ∀ sid, sid ∉ S₀ → s₀ sid = none)
    {res : γ} {s' : (dynParLazy M).State}
    (hmem : (res, s') ∈ (Machine.closeEval ((dynParLazy M).runFrom prog s₀)).support) :
    ∃ S : Finset SID, S₀ ⊆ S ∧ S.card ≤ S₀.card + b ∧ ∀ sid, sid ∉ S → s' sid = none := by
  induction hprog generalizing S₀ s₀ with
  | pure a n =>
    simp only [Machine.runFrom_pure, Machine.mem_support_closeEval_pure, Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, rfl⟩
    exact ⟨S₀, Finset.Subset.rfl, Nat.le_add_right _ _, hS₀⟩
  | liftBind q cont n hcont ih =>
    rcases q with k | ⟨sid, e⟩
    · simp only [Sum.elim_inl, Nat.add_zero]
      erw [Machine.runFrom_bind] at hmem
      have hinl : (dynParLazy M).runFrom (OracleComp.query (Sum.inl k)) s₀ =
          (fun a => (a, s₀)) <$> ProbOracleComp.sample (ProbComp.unifFin k) := by
        rw [← ProbOracleComp.sample_unifFin, Machine.runFrom_sample]
      rw [hinl, bind_map_left] at hmem
      rcases Machine.mem_support_closeEval_bind.mp hmem with ⟨a, _, ha⟩
      exact ih a S₀ s₀ hS₀ ha
    · simp only [Sum.elim_inr]
      erw [Machine.runFrom_bind, ← ProbOracleComp.query, Machine.runFrom_query] at hmem
      rcases Machine.mem_support_closeEval_bind.mp hmem with ⟨⟨r, s₁⟩, hs₁, hrest⟩
      have hupd : ∀ x, x ∉ insert sid S₀ → s₁ x = none := by
        intro x hx
        have hxsid : x ≠ sid := fun h => hx (h ▸ Finset.mem_insert_self sid S₀)
        have hxS₀ : x ∉ S₀ := fun h => hx (Finset.mem_insert_of_mem h)
        dsimp only [dynParLazy] at s₀ s₁ hs₁
        cases hs0 : s₀ sid with
        | none =>
          simp only [hs0, StateT.run] at hs₁
          erw [Machine.mem_support_closeEval_bind] at hs₁
          rcases hs₁ with ⟨st, _, hs₁⟩
          erw [Machine.mem_support_closeEval_bind] at hs₁
          rcases hs₁ with ⟨⟨r', st'⟩, _, hs₁⟩
          erw [Machine.mem_support_closeEval_pure, Prod.mk.injEq] at hs₁
          rcases hs₁ with ⟨_, rfl⟩
          rw [Function.update_of_ne hxsid]
          exact hS₀ x hxS₀
        | some st =>
          simp only [hs0, StateT.run, pure_bind] at hs₁
          erw [Machine.mem_support_closeEval_bind] at hs₁
          rcases hs₁ with ⟨⟨r', st'⟩, _, hs₁⟩
          erw [Machine.mem_support_closeEval_pure, Prod.mk.injEq] at hs₁
          rcases hs₁ with ⟨_, rfl⟩
          rw [Function.update_of_ne hxsid]
          exact hS₀ x hxS₀
      obtain ⟨S, hsub, hcard, hS⟩ := ih r (insert sid S₀) s₁ hupd hrest
      refine ⟨S, (Finset.subset_insert sid S₀).trans hsub, ?_, hS⟩
      have hle : (insert sid S₀).card ≤ S₀.card + 1 := Finset.card_insert_le sid S₀
      omega

/-- Starting from the initial all-`none` state of `dynParLazy M`, any supported run of a
`b`-query-bounded program leaves at most `b` distinct sessions initialized. -/
theorem mem_support_dynParLazy_init_touched_card_le {SID : Type} [DecidableEq SID]
    {ιE : Type} {E : ιE → Type} (M : SID → Machine OracleSpec.empty E) {γ : Type}
    {prog : ProbOracleComp (dynSessionSpec SID E) γ} {b : ℕ}
    (hprog : OracleComp.IsQueryBounded prog b)
    {res : γ} {s' : (dynParLazy M).State}
    (hmem : (res, s') ∈ (Machine.closeEval ((dynParLazy M).runFrom prog (fun _ => none))).support) :
    ∃ S : Finset SID, S.card ≤ b ∧ ∀ sid, (s' sid).isSome → sid ∈ S := by
  have hcost : OracleComp.IsCostBounded (Sum.elim (fun _ => 0) (fun _ => 1)) prog b :=
    hprog.of_le fun q => by cases q <;> simp
  obtain ⟨S, _, hcard, hnone⟩ :=
    mem_support_dynParLazy_touched_card_le M hcost ∅ _ (fun _ _ => rfl) hmem
  refine ⟨S, by simpa using hcard, fun sid hsome => ?_⟩
  by_contra hnot
  simp [hnone sid hnot] at hsome

end DynPar

/-! ### Finite first-touch allocator and lazy-vs-eager equivalence -/

section Allocator

private def findSlotIdx {SID : Type} [DecidableEq SID] (sid : SID) : List SID → Option ℕ
  | [] => none
  | x :: xs => if x = sid then some 0 else (findSlotIdx sid xs).map Nat.succ

private theorem findSlotIdx_eq_none_iff {SID : Type} [DecidableEq SID] (sid : SID)
    (xs : List SID) : findSlotIdx sid xs = none ↔ sid ∉ xs := by
  induction xs with
  | nil => simp [findSlotIdx]
  | cons x xs ih =>
    simp only [findSlotIdx, List.mem_cons, not_or]
    by_cases h : x = sid
    · subst h; simp
    · simp [h, ih, Ne.symm h]

private theorem findSlotIdx_eq_some {SID : Type} [DecidableEq SID] {sid : SID} {xs : List SID}
    {k : ℕ} (h : findSlotIdx sid xs = some k) : ∃ hk : k < xs.length, xs[k] = sid := by
  induction xs generalizing k with
  | nil => simp [findSlotIdx] at h
  | cons x xs ih =>
    simp only [findSlotIdx] at h
    by_cases hx : x = sid
    · subst hx
      simp only [↓reduceIte, Option.some.injEq] at h
      subst h
      exact ⟨Nat.zero_lt_succ _, rfl⟩
    · simp only [hx, ↓reduceIte, Option.map_eq_some_iff] at h
      rcases h with ⟨k', hk', rfl⟩
      obtain ⟨hk'len, hget⟩ := ih hk'
      exact ⟨Nat.succ_lt_succ hk'len, hget⟩

private def allocSlot {SID : Type} [DecidableEq SID] (m : ℕ) (seen : List SID) (sid : SID) :
    Fin (m + 1) × List SID :=
  match findSlotIdx sid seen with
  | some k => if hk : k < m + 1 then (⟨k, hk⟩, seen) else (Fin.last m, seen)
  | none =>
    if hlen : seen.length < m then (⟨seen.length, Nat.lt_succ_of_lt hlen⟩, seen ++ [sid])
    else (Fin.last m, seen)

/-- First-touch allocator translating dynamic queries over `dynSessionSpec SID E` into fixed-arity
queries over `SSP.sessionSpec (m + 1) E`. Up to `m` distinct session identifiers receive sequential
indices `0, ..., m - 1`, and `Fin.last m` serves as an unreachable fallback slot. -/
def allocMachine (SID : Type) [DecidableEq SID] (m : ℕ) {ιE : Type} (E : ιE → Type) :
    Machine (SSP.sessionSpec (m + 1) E) (dynSessionSpec SID E) where
  State := List SID
  init := pure []
  handle
    | (sid, q) => fun seen => do
        let (j, seen') := allocSlot m seen sid
        let r ← ProbOracleComp.query (spec := SSP.sessionSpec (m + 1) E) (j, q)
        return (r, seen')

private structure AllocInv {SID : Type} [DecidableEq SID] {ιE : Type} {E : ιE → Type}
    (M₀ : Machine OracleSpec.empty E) (m : ℕ) (seen : List SID)
    (sDyn : SID → Option M₀.State) (sFin : Fin (m + 1) → Option M₀.State) : Prop where
  nodup : seen.Nodup
  len_le : seen.length ≤ m
  unseen_none : ∀ sid, sid ∉ seen → sDyn sid = none
  agree : ∀ (k : ℕ) (hk : k < seen.length),
    sFin ⟨k, Nat.lt_of_lt_of_le hk (len_le.trans (Nat.le_succ m))⟩ = sDyn seen[k]
  tail_none : ∀ (k : ℕ) (hk : k < m + 1), seen.length ≤ k → sFin ⟨k, hk⟩ = none

private theorem allocInv_update_existing {SID : Type} [DecidableEq SID] {ιE : Type}
    {E : ιE → Type} {M₀ : Machine OracleSpec.empty E} {m : ℕ} {seen : List SID}
    {sDyn : SID → Option M₀.State} {sFin : Fin (m + 1) → Option M₀.State}
    (hinv : AllocInv M₀ m seen sDyn sFin) {k : ℕ} (hk : k < seen.length) (st' : M₀.State) :
    AllocInv M₀ m seen (Function.update sDyn seen[k] (some st'))
      (Function.update sFin ⟨k, Nat.lt_of_lt_of_le hk (hinv.len_le.trans (Nat.le_succ m))⟩
        (some st')) := by
  refine ⟨hinv.nodup, hinv.len_le, ?_, ?_, ?_⟩
  · intro sid hnot
    have hne : sid ≠ seen[k] := fun h => hnot (h ▸ List.getElem_mem hk)
    rw [Function.update_of_ne hne]
    exact hinv.unseen_none sid hnot
  · intro i hi
    by_cases hik : i = k
    · subst hik; simp
    · have hne_idx :
          (⟨i, Nat.lt_of_lt_of_le hi (hinv.len_le.trans (Nat.le_succ m))⟩ : Fin (m + 1)) ≠
            ⟨k, Nat.lt_of_lt_of_le hk (hinv.len_le.trans (Nat.le_succ m))⟩ :=
        fun h => hik (Fin.mk.inj h)
      have hne_val : seen[i] ≠ seen[k] := by
        intro h
        have hfin : (⟨i, hi⟩ : Fin seen.length) = ⟨k, hk⟩ :=
          (List.nodup_iff_injective_getElem.mp hinv.nodup) h
        exact hik (Fin.mk.inj hfin)
      rw [Function.update_of_ne hne_idx, Function.update_of_ne hne_val]
      exact hinv.agree i hi
  · intro i hi hlen
    have hne_idx :
        (⟨i, hi⟩ : Fin (m + 1)) ≠
          ⟨k, Nat.lt_of_lt_of_le hk (hinv.len_le.trans (Nat.le_succ m))⟩ := by
      intro h
      have := Fin.mk.inj h
      omega
    rw [Function.update_of_ne hne_idx]
    exact hinv.tail_none i hi hlen

private theorem allocInv_insert_fresh {SID : Type} [DecidableEq SID] {ιE : Type} {E : ιE → Type}
    {M₀ : Machine OracleSpec.empty E} {m : ℕ} {seen : List SID}
    {sDyn : SID → Option M₀.State} {sFin : Fin (m + 1) → Option M₀.State}
    (hinv : AllocInv M₀ m seen sDyn sFin) {sid : SID} (hnot : sid ∉ seen)
    (hlt : seen.length < m) (st' : M₀.State) :
    AllocInv M₀ m (seen ++ [sid]) (Function.update sDyn sid (some st'))
      (Function.update sFin ⟨seen.length, Nat.lt_succ_of_lt hlt⟩ (some st')) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [List.nodup_append]
    refine ⟨hinv.nodup, List.nodup_singleton _, fun a ha b hb => ?_⟩
    simp only [List.mem_singleton] at hb
    subst hb
    exact fun heq => hnot (heq ▸ ha)
  · simp; omega
  · intro x hx
    simp only [List.mem_append, List.mem_singleton, not_or] at hx
    rw [Function.update_of_ne hx.2]
    exact hinv.unseen_none x hx.1
  · intro i hi
    simp only [List.length_append, List.length_singleton] at hi
    by_cases hil : i < seen.length
    · have hne_idx :
          (⟨i, Nat.lt_of_lt_of_le hi (by have := hinv.len_le; omega)⟩ : Fin (m + 1)) ≠
            ⟨seen.length, Nat.lt_succ_of_lt hlt⟩ := fun h => by
        have := Fin.mk.inj h; omega
      have hget : (seen ++ [sid])[i] = seen[i] := List.getElem_append_left hil
      have hne_val : seen[i] ≠ sid := fun h => hnot (h ▸ List.getElem_mem hil)
      rw [hget, Function.update_of_ne hne_idx, Function.update_of_ne hne_val]
      exact hinv.agree i hil
    · have hieq : i = seen.length := by omega
      subst hieq
      simp
  · intro i hi hlen
    simp only [List.length_append, List.length_singleton] at hlen
    have hne_idx : (⟨i, hi⟩ : Fin (m + 1)) ≠ ⟨seen.length, Nat.lt_succ_of_lt hlt⟩ := fun h => by
      have := Fin.mk.inj h; omega
    rw [Function.update_of_ne hne_idx]
    exact hinv.tail_none i hi (by omega)

private theorem closeEval_runFrom_dynParLazy_eq_alloc {SID : Type} [DecidableEq SID]
    {ιE : Type} {E : ιE → Type} (M₀ : Machine OracleSpec.empty E) (m : ℕ) {γ : Type}
    {prog : ProbOracleComp (dynSessionSpec SID E) γ} {b : ℕ}
    (hb : OracleComp.IsCostBounded (Sum.elim (fun _ => 0) (fun _ => 1)) prog b)
    (seen : List SID) (sDyn : SID → Option M₀.State) (sFin : Fin (m + 1) → Option M₀.State)
    (hinv : AllocInv M₀ m seen sDyn sFin) (hrem : seen.length + b ≤ m) :
    Machine.closeEval (Prod.fst <$> (dynParLazy fun _ => M₀).runFrom prog sDyn) =
      Machine.closeEval (Prod.fst <$>
        ((allocMachine SID m E).comp (SSP.parFinLazy fun _ => M₀)).runFrom prog (seen, sFin)) := by
  induction hb generalizing seen sDyn sFin with
  | pure a n => rfl
  | liftBind q cont n hcont ih =>
    rcases q with k | ⟨sid, e⟩
    · simp only [Sum.elim_inl, Nat.add_zero] at hrem
      erw [Machine.runFrom_bind, Machine.runFrom_bind]
      have hinl₁ : (dynParLazy fun _ => M₀).runFrom (OracleComp.query (Sum.inl k)) sDyn =
          (fun a => (a, sDyn)) <$> ProbOracleComp.sample (ProbComp.unifFin k) := by
        erw [← ProbOracleComp.sample_unifFin, Machine.runFrom_sample]; rfl
      have hinl₂ : ((allocMachine SID m E).comp (SSP.parFinLazy fun _ => M₀)).runFrom
          (OracleComp.query (Sum.inl k)) (seen, sFin) =
          (fun a => (a, (seen, sFin))) <$> ProbOracleComp.sample (ProbComp.unifFin k) := by
        erw [← ProbOracleComp.sample_unifFin, Machine.runFrom_sample]; rfl
      erw [hinl₁, hinl₂, bind_map_left, bind_map_left, map_bind, map_bind]
      conv_lhs => erw [Machine.closeEval_bind]
      conv_rhs => erw [Machine.closeEval_bind]
      dsimp only
      refine congrArg _ (funext fun a => ?_)
      exact ih a seen sDyn sFin hinv hrem
    · simp only [Sum.elim_inr] at hrem
      erw [Machine.runFrom_bind, Machine.runFrom_bind,
        ← ProbOracleComp.query, Machine.runFrom_query, Machine.runFrom_query]
      have hslot : ∀ j seen' (hmatch : allocSlot m seen sid = (j, seen')),
          (((allocMachine SID m E).comp (SSP.parFinLazy fun _ => M₀)).handle (sid, e)).run
            (seen, sFin) =
          (fun x => (x.1, (seen', x.2))) <$>
            ((SSP.parFinLazy fun _ => M₀).handle (j, e)).run sFin := by
        intro j seen' hmatch
        dsimp only [Machine.comp, allocMachine, StateT.run]
        rw [hmatch]
        erw [Machine.runFrom_bind, Machine.runFrom_query]
        erw [map_bind, ← bind_pure_comp]
        rfl
      have hL_none : ∀ (hs : sDyn sid = none),
          ((dynParLazy fun _ : SID => M₀).handle (sid, e)).run sDyn = (do
            let st ← ProbOracleComp.sample M₀.init
            let __x ← M₀.handle e st
            pure (__x.1, Function.update sDyn sid (some __x.2))) := fun hs => by
        dsimp only [dynParLazy, StateT.run]; rw [hs]
      have hL_some : ∀ st (hs : sDyn sid = some st),
          ((dynParLazy fun _ : SID => M₀).handle (sid, e)).run sDyn = (do
            let __x ← M₀.handle e st
            pure (__x.1, Function.update sDyn sid (some __x.2))) := fun st hs => by
        dsimp only [dynParLazy, StateT.run]; rw [hs]; simp only [pure_bind]
      have hR_none : ∀ (j : Fin (m + 1)) (hs : sFin j = none),
          ((SSP.parFinLazy fun _ : Fin (m + 1) => M₀).handle (j, e)).run sFin = (do
            let st ← ProbOracleComp.sample M₀.init
            let __x ← M₀.handle e st
            pure (__x.1, Function.update sFin j (some __x.2))) := fun j hs => by
        dsimp only [SSP.parFinLazy, StateT.run]; rw [hs]
      have hR_some : ∀ (j : Fin (m + 1)) st (hs : sFin j = some st),
          ((SSP.parFinLazy fun _ : Fin (m + 1) => M₀).handle (j, e)).run sFin = (do
            let __x ← M₀.handle e st
            pure (__x.1, Function.update sFin j (some __x.2))) := fun j st hs => by
        dsimp only [SSP.parFinLazy, StateT.run]; rw [hs]; simp only [pure_bind]
      cases hfind : findSlotIdx sid seen with
      | some k =>
        obtain ⟨hk, hget⟩ := findSlotIdx_eq_some hfind
        have hklt : k < m + 1 := Nat.lt_of_lt_of_le hk (hinv.len_le.trans (Nat.le_succ m))
        let j : Fin (m + 1) := ⟨k, hklt⟩
        have halloc : allocSlot m seen sid = (j, seen) := by
          simp [allocSlot, hfind, hklt, j]
        erw [hslot j seen halloc]
        have heq : sFin j = sDyn sid := hget ▸ hinv.agree k hk
        cases hs : sDyn sid with
        | none =>
          rw [hL_none hs, hR_none j (heq.trans hs)]
          conv_lhs => erw [map_bind, bind_assoc, Machine.closeEval_bind]
          conv_rhs =>
            erw [map_bind, bind_map_left, bind_assoc, Machine.closeEval_bind]
          refine congrArg _ (funext fun st => ?_)
          conv_lhs => simp only [bind_assoc, pure_bind]; erw [Machine.closeEval_bind]
          conv_rhs => simp only [bind_assoc, pure_bind]; erw [Machine.closeEval_bind]
          refine congrArg _ (funext fun ⟨r, st'⟩ => ?_)
          exact ih r seen (Function.update sDyn sid (some st')) (Function.update sFin j (some st'))
            (by rw [← hget]; exact allocInv_update_existing hinv hk st') (by omega)
        | some st =>
          rw [hL_some st hs, hR_some j st (heq.trans hs)]
          conv_lhs => simp only [bind_assoc, pure_bind]; erw [map_bind, Machine.closeEval_bind]
          conv_rhs =>
            erw [map_bind, bind_map_left]
            simp only [bind_assoc, pure_bind]
            erw [Machine.closeEval_bind]
          refine congrArg _ (funext fun ⟨r, st'⟩ => ?_)
          exact ih r seen (Function.update sDyn sid (some st')) (Function.update sFin j (some st'))
            (by rw [← hget]; exact allocInv_update_existing hinv hk st') (by omega)
      | none =>
        have hnot : sid ∉ seen := (findSlotIdx_eq_none_iff sid seen).mp hfind
        have hlt : seen.length < m := by omega
        let j : Fin (m + 1) := ⟨seen.length, Nat.lt_succ_of_lt hlt⟩
        have halloc : allocSlot m seen sid = (j, seen ++ [sid]) := by
          simp [allocSlot, hfind, hlt, j]
        erw [hslot j (seen ++ [sid]) halloc]
        have hsD : sDyn sid = none := hinv.unseen_none sid hnot
        have hsF : sFin j = none := hinv.tail_none seen.length (Nat.lt_succ_of_lt hlt) le_rfl
        rw [hL_none hsD, hR_none j hsF]
        conv_lhs => erw [map_bind, bind_assoc, Machine.closeEval_bind]
        conv_rhs =>
          erw [map_bind, bind_map_left, bind_assoc, Machine.closeEval_bind]
        refine congrArg _ (funext fun st => ?_)
        conv_lhs => simp only [bind_assoc, pure_bind]; erw [Machine.closeEval_bind]
        conv_rhs => simp only [bind_assoc, pure_bind]; erw [Machine.closeEval_bind]
        refine congrArg _ (funext fun ⟨r, st'⟩ => ?_)
        exact ih r (seen ++ [sid]) (Function.update sDyn sid (some st'))
          (Function.update sFin j (some st'))
          (allocInv_insert_fresh hinv hnot hlt st') (by simp; omega)

/-- **Lazy-vs-eager finite reindexing equivalence:** running `dynParLazy (fun _ => M₀)` on any
`b`-query-bounded dynamic-SID program gives the exact same output distribution as running eager
`SSP.parFin (fun (_ : Fin (b + 1)) => M₀)` on the first-touch reindexed program
`(allocMachine SID b E).link prog`. -/
theorem eval_run_dynParLazy_eq_parFin {SID : Type} [DecidableEq SID]
    {ιE : Type} {E : ιE → Type} (M₀ : Machine OracleSpec.empty E) (b : ℕ) {γ : Type}
    {prog : ProbOracleComp (dynSessionSpec SID E) γ}
    (hprog : OracleComp.IsQueryBounded prog b) :
    ((dynParLazy fun _ : SID => M₀).run prog).eval =
      ((SSP.parFin fun _ : Fin (b + 1) => M₀).run ((allocMachine SID b E).link prog)).eval := by
  have hcost : OracleComp.IsCostBounded (Sum.elim (fun _ => 0) (fun _ => 1)) prog b :=
    hprog.of_le fun q => by cases q <;> simp
  have hinit : AllocInv M₀ b ([] : List SID) (fun _ => none) (fun _ => none) :=
    ⟨List.nodup_nil, Nat.zero_le b, fun _ _ => rfl, fun k hk => by simp at hk, fun _ _ _ => rfl⟩
  have hcomp : ((dynParLazy fun _ : SID => M₀).run prog).eval =
      (((allocMachine SID b E).comp (SSP.parFinLazy fun _ : Fin (b + 1) => M₀)).run prog).eval := by
    simp only [Machine.run, Machine.link]
    have hL : (dynParLazy fun _ : SID => M₀).init = pure fun _ => none := rfl
    have hR : ((allocMachine SID b E).comp (SSP.parFinLazy fun _ : Fin (b + 1) => M₀)).init =
        pure ([], fun _ => none) := by
      simp [Machine.comp, allocMachine, SSP.parFinLazy]
    erw [hL, hR, ProbOracleComp.sample_pure, ProbOracleComp.sample_pure, pure_bind, pure_bind]
    exact closeEval_runFrom_dynParLazy_eq_alloc M₀ b hcost [] _ _ hinit (by simp)
  rw [hcomp, Machine.run_comp, SSP.run_parFinLazy_eq_parFin]

end Allocator

/-! ### Dynamic-SID hybrid protocols, routers, simulator, and budgets -/

section Protocols

/-- A subroutine party-port call from a dynamic-SID hybrid protocol, targeting party port `party`
of dynamically chosen session `sid : SID`. -/
structure DynSessionCall (SID : Type) (n : ℕ) (SubIn : Type) : Type where
  /-- Target subroutine session identifier. -/
  sid : SID
  /-- Target party port index (`0 ≤ party < n`) in that subroutine session. -/
  party : Fin n
  /-- Input (or poll token) delivered to `(sid, party)`. -/
  input : SubIn
  deriving DecidableEq

/-- The party-port interface of dynamic-SID subroutine sessions of `n` parties: each
`DynSessionCall` receives an optional output of the subroutine. -/
@[expose] def dynPartySpec (SID : Type) (n : ℕ) (SubIn SubOut : Type) :
    DynSessionCall SID n SubIn → Type :=
  fun _ => Option SubOut

/-- An `n`-party protocol in the dynamic-SID hybrid model calling depth-1 subroutine sessions
indexed by `SID`. -/
abbrev DynHybridProtocol (SID : Type) (n : ℕ) (In Out NetQ NetR SubIn SubOut : Type) : Type 1 :=
  ℕ → Finset (Fin n) → Machine (dynPartySpec SID n SubIn SubOut) (protocolSpec n In Out NetQ NetR)

/-- Every activation of the dynamic-SID hybrid protocol at security parameter `κ` makes at most
`p.eval κ` calls, counting private samples and subroutine calls. -/
@[expose] def DynHybridProtocol.PolyBounded {SID : Type} {n : ℕ}
    {In Out NetQ NetR SubIn SubOut : Type}
    (ρ : DynHybridProtocol SID n In Out NetQ NetR SubIn SubOut) (p : Polynomial ℕ) : Prop :=
  ∀ κ C, (ρ κ C).IsBounded (p.eval κ)

/-- Network-side query to a dynamic-SID composed protocol: either a query to the outer calling
protocol `ρ`'s own network port, or a query to dynamic subroutine session `sid`'s routed network
port. -/
inductive DynNetQ (SID NetQ SubRoutedQ : Type) : Type
  /-- A query directed to the outer calling protocol `ρ`'s own network port. -/
  | outer (query : NetQ)
  /-- A query directed to dynamic subroutine session `sid`'s routed network port. -/
  | sub (sid : SID) (query : SubRoutedQ)
  deriving DecidableEq

/-- Lazy first-touch parallel router for dynamic-SID subroutine sessions of `σ` sharing the static
corruption set `C`. Each session `sid : SID` is initialized on first access inside `dynParLazy`. -/
@[expose] def dynSessionRouter {SID : Type} [DecidableEq SID] {n : ℕ}
    {SubIn SubOut NQ NR : Type} (C : Finset (Fin n)) (σ : Machine OracleSpec.empty
      (protocolSpec n SubIn SubOut NQ NR)) :
    Machine OracleSpec.empty
      (dynSessionSpec SID (protocolSpec n SubIn SubOut (RoutedNetQ n SubIn NQ)
        (RoutedNetR SubOut NR))) :=
  dynParLazy fun _ => corruptRouter C σ

/-- Lift a program calling only `dynPartySpec` to call `dynSessionSpec SID (protocolSpec ...)`. -/
@[expose] def liftDynParty {SID : Type} {n : ℕ} {SubIn SubOut NQ NR α : Type}
    (program : ProbOracleComp (dynPartySpec SID n SubIn SubOut) α) :
    ProbOracleComp (dynSessionSpec SID (protocolSpec n SubIn SubOut NQ NR)) α :=
  OracleComp.interpret
    (sumHandler
      (fun k => OracleComp.query
        (spec := probOracleSpec (dynSessionSpec SID (protocolSpec n SubIn SubOut NQ NR)))
        (Sum.inl k))
      fun c => ProbOracleComp.query
        (spec := dynSessionSpec SID (protocolSpec n SubIn SubOut NQ NR))
        (c.sid, Sum.inl (c.party, c.input)))
    program

/-- Wrap a dynamic-SID hybrid protocol machine so its subroutine party calls target
`dynSessionSpec SID` and each session's network port is exposed under `DynNetQ.sub sid`. -/
@[expose] def dynHybridWrap {SID : Type} {n : ℕ} {In Out NetQ NetR SubIn SubOut NQ NR : Type}
    (M : Machine (dynPartySpec SID n SubIn SubOut) (protocolSpec n In Out NetQ NetR)) :
    Machine (dynSessionSpec SID (protocolSpec n SubIn SubOut NQ NR))
      (protocolSpec n In Out (DynNetQ SID NetQ NQ) (NetR ⊕ NR)) where
  State := M.State
  init := M.init
  handle
    | .inl p => fun s => liftDynParty ((M.handle (.inl p)).run s)
    | .inr (.outer q) => fun s => liftDynParty ((Sum.inl <$> M.handle (.inr q)).run s)
    | .inr (.sub sid q) => StateT.lift (Sum.inr <$>
        ProbOracleComp.query (spec := dynSessionSpec SID (protocolSpec n SubIn SubOut NQ NR))
          (sid, Sum.inr q))

/-- Dynamic-SID homogeneous subroutine replacement: `ρ` calling lazily initialized independent
instances of `σ` indexed by `SID`. -/
@[expose] def composeDyn {SID : Type} [DecidableEq SID] {n : ℕ}
    {In Out NetQ NetR SubIn SubOut NQ NR : Type}
    (ρ : DynHybridProtocol SID n In Out NetQ NetR SubIn SubOut)
    (σ : Protocol n SubIn SubOut NQ NR) :
    Protocol n In Out
      (DynNetQ SID NetQ (RoutedNetQ n SubIn NQ))
      (NetR ⊕ RoutedNetR SubOut NR) :=
  fun κ C => (dynHybridWrap (ρ κ C)).comp (dynSessionRouter C (σ κ C))

/-- Lift a single-session network program at session `sid` into the composed network interface. -/
@[expose] def liftDynSubNet {SID : Type} {n : ℕ}
    {In Out NetQ NetR SubIn SubOut NQ NR α : Type} (sid : SID)
    (program : ProbOracleComp (netSpec (RoutedNetQ n SubIn NQ) (RoutedNetR SubOut NR)) α) :
    ProbOracleComp
      (netSpec (RoutedNetQ n In (DynNetQ SID NetQ (RoutedNetQ n SubIn NQ)))
        (RoutedNetR Out (NetR ⊕ RoutedNetR SubOut NR))) α :=
  OracleComp.interpret
    (sumHandler
      (fun k => OracleComp.query
        (spec := probOracleSpec (netSpec
          (RoutedNetQ n In (DynNetQ SID NetQ (RoutedNetQ n SubIn NQ)))
          (RoutedNetR Out (NetR ⊕ RoutedNetR SubOut NR))))
        (Sum.inl k))
      fun q => subReply <$> ProbOracleComp.query
        (spec := netSpec
          (RoutedNetQ n In (DynNetQ SID NetQ (RoutedNetQ n SubIn NQ)))
          (RoutedNetR Out (NetR ⊕ RoutedNetR SubOut NR)))
        (.inr (.sub sid q)))
    program

/-- Lazy parallel machine combining dynamic-SID copies of a single-session simulator `S` on the
composed network interface, initializing session `sid`'s simulator state on first network query
`.inr (.sub sid q)`. -/
@[expose] def dynHybridSimMachine {SID : Type} [DecidableEq SID] {n : ℕ}
    {In Out NetQ NetR SubIn SubOut NQ₁ NR₁ NQ₂ NR₂ : Type}
    (S : Machine (netSpec (RoutedNetQ n SubIn NQ₂) (RoutedNetR SubOut NR₂))
      (netSpec (RoutedNetQ n SubIn NQ₁) (RoutedNetR SubOut NR₁))) :
    Machine
      (netSpec (RoutedNetQ n In (DynNetQ SID NetQ (RoutedNetQ n SubIn NQ₂)))
        (RoutedNetR Out (NetR ⊕ RoutedNetR SubOut NR₂)))
      (netSpec (RoutedNetQ n In (DynNetQ SID NetQ (RoutedNetQ n SubIn NQ₁)))
        (RoutedNetR Out (NetR ⊕ RoutedNetR SubOut NR₁))) where
  State := SID → Option S.State
  init := pure fun _ => none
  handle
    | .inl p => StateT.lift (outerReply <$> ProbOracleComp.query (spec := netSpec
        (RoutedNetQ n In (DynNetQ SID NetQ (RoutedNetQ n SubIn NQ₂)))
        (RoutedNetR Out (NetR ⊕ RoutedNetR SubOut NR₂))) (.inl p))
    | .inr (.outer q) => StateT.lift (outerReply <$> ProbOracleComp.query (spec := netSpec
        (RoutedNetQ n In (DynNetQ SID NetQ (RoutedNetQ n SubIn NQ₂)))
        (RoutedNetR Out (NetR ⊕ RoutedNetR SubOut NR₂))) (.inr (.outer q)))
    | .inr (.sub sid q) => fun s => do
        let st ← match s sid with
          | some st => pure st
          | none => ProbOracleComp.sample S.init
        liftDynSubNet sid ((fun x => (Sum.inr (Sum.inr x.1), Function.update s sid (some x.2))) <$>
          (S.handle q).run st)

/-- Lazy parallel simulator for `composeDyn ρ π` against `composeDyn ρ φ`, creating an independent
instance of `S` on first network touch of each `sid : SID`. Because session states are created
lazily, one fixed simulator serves environments of every polynomial call budget. -/
@[expose] def dynHybridSim {SID : Type} [DecidableEq SID] {n : ℕ}
    {In Out NetQ NetR SubIn SubOut NQ₁ NR₁ NQ₂ NR₂ : Type}
    (S : Adversary n (RoutedNetQ n SubIn NQ₁) (RoutedNetR SubOut NR₁)
      (RoutedNetQ n SubIn NQ₂) (RoutedNetR SubOut NR₂)) :
    Adversary n
      (RoutedNetQ n In (DynNetQ SID NetQ (RoutedNetQ n SubIn NQ₁)))
      (RoutedNetR Out (NetR ⊕ RoutedNetR SubOut NR₁))
      (RoutedNetQ n In (DynNetQ SID NetQ (RoutedNetQ n SubIn NQ₂)))
      (RoutedNetR Out (NetR ⊕ RoutedNetR SubOut NR₂)) :=
  fun κ C => dynHybridSimMachine (S κ C)

/-- Absorbing `ρ κ C` into an environment `Z` produces a distinguisher against the dynamic-SID
subroutine interface `dynSessionSpec SID (protocolSpec n SubIn SubOut ...)`. -/
@[expose] def absorbDynHybrid {SID : Type} {n : ℕ} {In Out NetQ NetR SubIn SubOut NQ NR : Type}
    (C : Finset (Fin n))
    (ρ : DynHybridProtocol SID n In Out NetQ NetR SubIn SubOut)
    (Z : Environment n In Out
      (RoutedNetQ n In (DynNetQ SID NetQ (RoutedNetQ n SubIn NQ)))
      (RoutedNetR Out (NetR ⊕ RoutedNetR SubOut NR)))
    (κ : ℕ) (z : List Bool) :
    ProbOracleComp
      (dynSessionSpec SID
        (protocolSpec n SubIn SubOut (RoutedNetQ n SubIn NQ) (RoutedNetR SubOut NR)))
      Bool :=
  (routeCorrupt C (dynHybridWrap (ρ κ C))).link (Z κ z)

/-- Polynomial query budget of each single-hop hybrid distinguisher when at most
`absorbPoly pZ pρ + 1` dynamic slots are needed. -/
@[expose] noncomputable def dynSessionHopPoly (pZ pρ pπ pφ pD : Polynomial ℕ) : Polynomial ℕ :=
  absorbPoly (absorbPoly pZ pρ) ((absorbPoly pZ pρ + 1) * sessionUnitPoly pπ pφ pD)

private theorem isQueryBounded_liftDynParty {SID : Type} {n : ℕ} {SubIn SubOut NQ NR α : Type}
    {program : ProbOracleComp (dynPartySpec SID n SubIn SubOut) α} {t : ℕ}
    (h : OracleComp.IsQueryBounded program t) :
    OracleComp.IsQueryBounded (liftDynParty (NQ := NQ) (NR := NR) program) t := by
  refine OracleComp.IsCostBounded.interpret (fun q => ?_) h
  cases q with
  | inl k => exact OracleComp.IsCostBounded.query (Sum.inl k)
  | inr c => exact OracleComp.IsCostBounded.query (Sum.inr (c.sid, Sum.inl (c.party, c.input)))

private theorem isQueryBounded_liftDynSubNet {SID : Type} {n : ℕ}
    {In Out NetQ NetR SubIn SubOut NQ NR α : Type} (sid : SID)
    {program : ProbOracleComp (netSpec (RoutedNetQ n SubIn NQ) (RoutedNetR SubOut NR)) α}
    {t : ℕ} (h : OracleComp.IsQueryBounded program t) :
    OracleComp.IsQueryBounded
      (liftDynSubNet (In := In) (Out := Out) (NetQ := NetQ) (NetR := NetR) sid program) t := by
  refine OracleComp.IsCostBounded.interpret (fun q => ?_) h
  cases q with
  | inl k => exact OracleComp.IsCostBounded.query (Sum.inl k)
  | inr q' =>
    dsimp only [sumHandler]
    rw [← bind_pure_comp]
    exact (OracleComp.IsCostBounded.query
      (Sum.inr (Sum.inr (DynNetQ.sub sid q') :
        RoutedNetQ n In (DynNetQ SID NetQ (RoutedNetQ n SubIn NQ))))).bind
      fun _ => OracleComp.IsCostBounded.pure _ 0

/-- Wrapping a `t`-bounded dynamic-SID hybrid machine yields a `(t + 1)`-bounded machine. -/
theorem isBounded_dynHybridWrap {SID : Type} {n : ℕ} {In Out NetQ NetR SubIn SubOut NQ NR : Type}
    {M : Machine (dynPartySpec SID n SubIn SubOut) (protocolSpec n In Out NetQ NetR)}
    {t : ℕ} (h : M.IsBounded t) :
    (dynHybridWrap (NQ := NQ) (NR := NR) M).IsBounded (t + 1) := by
  refine ⟨h.1.mono (Nat.le_succ t), fun q s => ?_⟩
  rcases q with p | outer | ⟨sid, q⟩
  · exact (isQueryBounded_liftDynParty (h.2 (.inl p) s)).mono (Nat.le_succ t)
  · dsimp only [dynHybridWrap] at s ⊢
    change OracleComp.IsQueryBounded
      (liftDynParty ((Sum.inl <$> M.handle (.inr outer)).run s)) (t + 1)
    rw [liftDynParty, StateT.run_map]
    erw [OracleComp.interpret_map]
    rw [← liftDynParty]
    exact ((OracleComp.isCostBounded_map_iff _ _ _).mpr
      (isQueryBounded_liftDynParty (h.2 (.inr outer) s))).mono (Nat.le_succ t)
  · change OracleComp.IsQueryBounded ((StateT.lift (Sum.inr <$>
      ProbOracleComp.query (spec := dynSessionSpec SID (protocolSpec n SubIn SubOut NQ NR))
        (sid, Sum.inr q))).run s) (t + 1)
    rw [StateT.run_lift, bind_pure_comp, Functor.map_map, ← bind_pure_comp]
    exact ((OracleComp.IsCostBounded.query (Sum.inr (sid, Sum.inr q))).bind fun _ =>
      OracleComp.IsCostBounded.pure _ 0).mono (Nat.le_add_left 1 t)

/-- Absorbing a `pρ`-bounded dynamic-SID hybrid protocol into a `pZ`-bounded environment gives
query bound `(absorbPoly pZ pρ).eval κ`. -/
theorem absorbDynHybrid_polyBounded {SID : Type} {n : ℕ}
    {In Out NetQ NetR SubIn SubOut NQ NR : Type}
    (C : Finset (Fin n))
    {ρ : DynHybridProtocol SID n In Out NetQ NetR SubIn SubOut}
    {Z : Environment n In Out
      (RoutedNetQ n In (DynNetQ SID NetQ (RoutedNetQ n SubIn NQ)))
      (RoutedNetR Out (NetR ⊕ RoutedNetR SubOut NR))}
    {pρ pZ : Polynomial ℕ} (hρ : ρ.PolyBounded pρ) (hZ : Z.PolyBounded pZ) :
    ∀ κ z, (absorbDynHybrid C ρ Z κ z).IsQueryBounded ((absorbPoly pZ pρ).eval κ) := by
  intro κ z
  have hM : (routeCorrupt C
      (dynHybridWrap (NQ := RoutedNetQ n SubIn NQ) (NR := RoutedNetR SubOut NR)
        (ρ κ C))).IsBounded (pρ.eval κ + 1) :=
    isBounded_routeCorrupt C (isBounded_dynHybridWrap (hρ κ C))
  refine (Machine.isQueryBounded_link hM (hZ κ z)).mono (le_of_eq ?_)
  simp [absorbPoly, Polynomial.eval_ofNat]

/-- Composing a `pρ`-bounded dynamic-SID hybrid protocol with a `pσ`-bounded protocol yields a
`((pρ + 1) * (2 * pσ + 1) + 2 * pσ)`-bounded composed protocol, independent of the number of
sessions touched. -/
theorem composeDyn_polyBounded {SID : Type} [DecidableEq SID] {n : ℕ}
    {In Out NetQ NetR SubIn SubOut NQ NR : Type}
    {ρ : DynHybridProtocol SID n In Out NetQ NetR SubIn SubOut}
    {σ : Protocol n SubIn SubOut NQ NR} {pρ pσ : Polynomial ℕ}
    (hρ : ρ.PolyBounded pρ) (hσ : σ.PolyBounded pσ) :
    (composeDyn ρ σ).PolyBounded ((pρ + 1) * (2 * pσ + 1) + 2 * pσ) := by
  intro κ C
  have hwrap :
      (dynHybridWrap (NQ := RoutedNetQ n SubIn NQ) (NR := RoutedNetR SubOut NR)
        (ρ κ C)).IsBounded (pρ.eval κ + 1) :=
    isBounded_dynHybridWrap (hρ κ C)
  have hrouter : (dynSessionRouter (SID := SID) C (σ κ C)).IsBounded (2 * pσ.eval κ) :=
    isBounded_dynParLazy fun _ => isBounded_routeCorrupt C (hσ κ C)
  refine (hwrap.comp hrouter).mono (le_of_eq ?_)
  simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_one, Polynomial.eval_ofNat]

/-- The lazy dynamic-SID simulator `dynHybridSim S` for a `pS`-bounded simulator `S` has polynomial
call budget `2 * pS + 1`, independent of any session count. -/
theorem dynHybridSim_polyBounded {SID : Type} [DecidableEq SID] {n : ℕ}
    {In Out NetQ NetR SubIn SubOut NQ₁ NR₁ NQ₂ NR₂ : Type}
    {S : Adversary n (RoutedNetQ n SubIn NQ₁) (RoutedNetR SubOut NR₁)
      (RoutedNetQ n SubIn NQ₂) (RoutedNetR SubOut NR₂)}
    {pS : Polynomial ℕ} (hS : S.PolyBounded pS) :
    (dynHybridSim (SID := SID) (In := In) (Out := Out) (NetQ := NetQ) (NetR := NetR) S).PolyBounded
      (2 * pS + 1) := by
  intro κ C
  refine ⟨OracleComp.IsCostBounded.pure _ _, fun q s => ?_⟩
  rcases q with p | outer | ⟨sid, q⟩
  · dsimp only [dynHybridSim, dynHybridSimMachine] at s ⊢
    rw [StateT.run_lift, bind_pure_comp, Functor.map_map, ← bind_pure_comp]
    refine ((OracleComp.IsCostBounded.query
        (Sum.inr (Sum.inl p : RoutedNetQ n In (DynNetQ SID NetQ (RoutedNetQ n SubIn NQ₂))))).bind
      fun _ => OracleComp.IsCostBounded.pure _ 0).mono ?_
    simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_one]
  · dsimp only [dynHybridSim, dynHybridSimMachine] at s ⊢
    rw [StateT.run_lift, bind_pure_comp, Functor.map_map, ← bind_pure_comp]
    refine ((OracleComp.IsCostBounded.query
        (Sum.inr (Sum.inr (DynNetQ.outer outer) :
          RoutedNetQ n In (DynNetQ SID NetQ (RoutedNetQ n SubIn NQ₂))))).bind
      fun _ => OracleComp.IsCostBounded.pure _ 0).mono ?_
    simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_one]
  · have hsub : ∀ st : (S κ C).State, OracleComp.IsQueryBounded
        (liftDynSubNet (In := In) (Out := Out) (NetQ := NetQ) (NetR := NetR) sid
          ((fun (x : RoutedNetR SubOut NR₁ × (S κ C).State) =>
              ((Sum.inr (Sum.inr x.1) :
                RoutedNetR Out (NetR ⊕ RoutedNetR SubOut NR₁)),
               Function.update s sid (some x.2))) <$>
            ((S κ C).handle q).run st)) (pS.eval κ) := fun st => by
      rw [liftDynSubNet, OracleComp.interpret_map]
      exact (OracleComp.isCostBounded_map_iff _ _ _).mpr
        (isQueryBounded_liftDynSubNet sid ((hS κ C).2 q st))
    dsimp only [dynHybridSim, dynHybridSimMachine, StateT.run] at s ⊢
    cases hs : s sid with
    | none =>
      refine ((Machine.isQueryBounded_sample (hS κ C).1).bind hsub).mono ?_
      simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_one,
        Polynomial.eval_ofNat]
      omega
    | some st =>
      simp only [pure_bind]
      refine (hsub st).mono ?_
      simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_one,
        Polynomial.eval_ofNat]
      omega

end Protocols

/-! ### Execution identities and reduction to `SSP.parFin` -/

section ExecutionBridge

private def liftDynSessionNet {SID : Type} {n : ℕ} {SubIn SubOut NQ NR α : Type} (sid : SID)
    (program : ProbOracleComp (netSpec (RoutedNetQ n SubIn NQ) (RoutedNetR SubOut NR)) α) :
    ProbOracleComp
      (dynSessionSpec SID (protocolSpec n SubIn SubOut (RoutedNetQ n SubIn NQ)
        (RoutedNetR SubOut NR))) α :=
  OracleComp.interpret
    (sumHandler
      (fun k => OracleComp.query
        (spec := probOracleSpec (dynSessionSpec SID (protocolSpec n SubIn SubOut
          (RoutedNetQ n SubIn NQ) (RoutedNetR SubOut NR))))
        (Sum.inl k))
      fun q => ProbOracleComp.query
        (spec := dynSessionSpec SID (protocolSpec n SubIn SubOut (RoutedNetQ n SubIn NQ)
          (RoutedNetR SubOut NR)))
        (sid, Sum.inr q))
    program

private def dynParLiftAdversary {SID : Type} [DecidableEq SID] {n : ℕ}
    {SubIn SubOut NQ₁ NR₁ NQ₂ NR₂ : Type}
    (S : Machine (netSpec (RoutedNetQ n SubIn NQ₂) (RoutedNetR SubOut NR₂))
      (netSpec (RoutedNetQ n SubIn NQ₁) (RoutedNetR SubOut NR₁))) :
    Machine
      (dynSessionSpec SID (protocolSpec n SubIn SubOut (RoutedNetQ n SubIn NQ₂)
        (RoutedNetR SubOut NR₂)))
      (dynSessionSpec SID (protocolSpec n SubIn SubOut (RoutedNetQ n SubIn NQ₁)
        (RoutedNetR SubOut NR₁))) where
  State := SID → Option S.State
  init := pure fun _ => none
  handle
    | (sid, .inl p) => StateT.lift (ProbOracleComp.query
        (spec := dynSessionSpec SID (protocolSpec n SubIn SubOut (RoutedNetQ n SubIn NQ₂)
          (RoutedNetR SubOut NR₂)))
        (sid, Sum.inl p))
    | (sid, .inr q) => fun s => do
        let st ← match s sid with
          | some st => pure st
          | none => ProbOracleComp.sample S.init
        liftDynSessionNet sid ((fun x => (x.1, Function.update s sid (some x.2))) <$>
          (S.handle q).run st)

/-- Running `composeDyn ρ π` with the dummy adversary is running `dynSessionRouter` against
`absorbDynHybrid`. -/
theorem exec_composeDyn_dummy {SID : Type} [DecidableEq SID] {n : ℕ}
    {In Out NetQ NetR SubIn SubOut NQ NR : Type}
    (ρ : DynHybridProtocol SID n In Out NetQ NetR SubIn SubOut)
    (π : Protocol n SubIn SubOut NQ NR) (C : Finset (Fin n))
    (Z : Environment n In Out
      (RoutedNetQ n In (DynNetQ SID NetQ (RoutedNetQ n SubIn NQ)))
      (RoutedNetR Out (NetR ⊕ RoutedNetR SubOut NR)))
    (κ : ℕ) (z : List Bool) :
    exec (composeDyn ρ π) (dummyAdversary n _ _) C Z κ z =
      (dynSessionRouter (SID := SID) C (π κ C)).run (absorbDynHybrid C ρ Z κ z) := by
  simp only [exec, execMachine, dummyAdversary, Machine.liftRight_id, Machine.run_comp,
    Machine.link_id, composeDyn, corruptRouter_comp, absorbDynHybrid]

private theorem runFrom_dynParLiftAdversary_liftDynParty {SID : Type} [DecidableEq SID] {n : ℕ}
    {SubIn SubOut NQ₁ NR₁ NQ₂ NR₂ α : Type}
    (S : Machine (netSpec (RoutedNetQ n SubIn NQ₂) (RoutedNetR SubOut NR₂))
      (netSpec (RoutedNetQ n SubIn NQ₁) (RoutedNetR SubOut NR₁)))
    (program : ProbOracleComp (dynPartySpec SID n SubIn SubOut) α)
    (s : (dynParLiftAdversary (SID := SID) S).State) :
    (dynParLiftAdversary S).runFrom (liftDynParty program) s =
      (fun a => (a, s)) <$> liftDynParty program := by
  refine Machine.runFrom_interpret_of_forward (dynParLiftAdversary S) _ _ (fun q s => ?_) program s
  cases q with
  | inl k => exact runFrom_query_sample _ k s
  | inr c =>
    change (dynParLiftAdversary S).runFrom
      (ProbOracleComp.query (c.sid, Sum.inl (c.party, c.input))) s = _
    rw [Machine.runFrom_query]
    change (StateT.lift (ProbOracleComp.query _)).run s = _
    rw [StateT.run_lift, bind_pure_comp]
    rfl

private theorem runFrom_routeCorrupt_liftNet_liftDynSubNet {SID : Type} {n : ℕ}
    {In Out NetQ NetR SubIn SubOut NQ NR α : Type} (C : Finset (Fin n))
    (M : Machine (dynPartySpec SID n SubIn SubOut) (protocolSpec n In Out NetQ NetR))
    (sid : SID)
    (program : ProbOracleComp (netSpec (RoutedNetQ n SubIn NQ) (RoutedNetR SubOut NR)) α)
    (s : M.State) :
    (routeCorrupt C
        (dynHybridWrap (NQ := RoutedNetQ n SubIn NQ) (NR := RoutedNetR SubOut NR) M)).runFrom
        (liftNet (liftDynSubNet sid program)) s =
      (fun a => (a, s)) <$> liftDynSessionNet sid program := by
  dsimp only [liftNet]
  rw [Machine.liftRightProgram, liftDynSubNet, OracleComp.interpret_interpret, liftDynSessionNet]
  refine Machine.runFrom_interpret_of_forward (routeCorrupt C (dynHybridWrap M)) _ _
    (fun q s => ?_) program s
  cases q with
  | inl k =>
    simp only [OracleComp.interpret_query]
    exact runFrom_query_sample _ k s
  | inr q =>
    simp only [OracleComp.interpret_map, ProbOracleComp.interpret_query, Machine.runFrom_map,
      Machine.runFrom_query]
    change Prod.map subReply _root_.id <$> ((Sum.inr <$> StateT.lift (Sum.inr <$>
      ProbOracleComp.query (spec := dynSessionSpec SID (protocolSpec n SubIn SubOut
        (RoutedNetQ n SubIn NQ) (RoutedNetR SubOut NR))) (sid, Sum.inr q))).run s) = _
    rw [StateT.run_map, StateT.run_lift, bind_pure_comp, Functor.map_map, Functor.map_map,
      Functor.map_map]
    rfl

private theorem dyn_handle_swap {SID : Type} [DecidableEq SID] {n : ℕ}
    {In Out NetQ NetR SubIn SubOut NQ₁ NR₁ NQ₂ NR₂ : Type}
    (C : Finset (Fin n))
    (M : Machine (dynPartySpec SID n SubIn SubOut) (protocolSpec n In Out NetQ NetR))
    (S : Machine (netSpec (RoutedNetQ n SubIn NQ₂) (RoutedNetR SubOut NR₂))
      (netSpec (RoutedNetQ n SubIn NQ₁) (RoutedNetR SubOut NR₁)))
    (q : (Fin n × In) ⊕ RoutedNetQ n In (DynNetQ SID NetQ (RoutedNetQ n SubIn NQ₁)))
    (sρ : M.State) (sS : SID → Option S.State) :
    Equiv.prodAssoc _ _ _ <$> (routeCorrupt C (dynHybridWrap
        (NQ := RoutedNetQ n SubIn NQ₂) (NR := RoutedNetR SubOut NR₂) M)).runFrom
        (((liftAdversary (n := n) (In := In) (Out := Out)
          (dynHybridSimMachine (SID := SID) S)).handle q).run sS) sρ =
      Prod.map _root_.id Prod.swap <$> (Equiv.prodAssoc _ _ _ <$>
        (dynParLiftAdversary S).runFrom
          (((routeCorrupt C (dynHybridWrap (NQ := RoutedNetQ n SubIn NQ₁)
            (NR := RoutedNetR SubOut NR₁) M)).handle q).run sρ) sS) := by
  rcases q with ⟨i, x⟩ | ⟨i, x⟩ | q | ⟨sid, q⟩
  · erw [liftAdversary_handle_inl, Machine.runFrom_map, Machine.runFrom_query,
      routeCorrupt_handle_inl, routeCorrupt_handle_inl]
    by_cases hi : i ∈ C
    · simp only [hi, ↓reduceIte]
      rfl
    · simp only [hi, ↓reduceIte]
      change _ = Prod.map _root_.id Prod.swap <$> (Equiv.prodAssoc _ _ _ <$>
        (dynParLiftAdversary S).runFrom (liftDynParty ((M.handle (.inl (i, x))).run sρ)) sS)
      erw [runFrom_dynParLiftAdversary_liftDynParty]
      repeat erw [Functor.map_map]
      rfl
  · change Equiv.prodAssoc _ _ _ <$> (routeCorrupt C (dynHybridWrap M)).runFrom
        (Machine.liftRightProgram (partySpec n In Out) ((StateT.lift (outerReply <$>
          ProbOracleComp.query (.inl (i, x)))).run sS)) sρ = _
    rw [StateT.run_lift, bind_pure_comp, Functor.map_map, Machine.liftRightProgram_map,
      Machine.liftRightProgram_query]
    erw [Machine.runFrom_map, Machine.runFrom_query, routeCorrupt_handle_inr_inl,
      routeCorrupt_handle_inr_inl]
    by_cases hi : i ∈ C
    · simp only [hi, ↓reduceIte]
      change _ = Prod.map _root_.id Prod.swap <$> (Equiv.prodAssoc _ _ _ <$>
        (dynParLiftAdversary S).runFrom
          ((fun p => (Sum.inl p.1, p.2)) <$> liftDynParty ((M.handle (.inl (i, x))).run sρ)) sS)
      erw [Machine.runFrom_map, runFrom_dynParLiftAdversary_liftDynParty]
      repeat erw [Functor.map_map]
      rfl
    · simp only [hi, ↓reduceIte]
      rfl
  · change Equiv.prodAssoc _ _ _ <$> (routeCorrupt C (dynHybridWrap M)).runFrom
        (Machine.liftRightProgram (partySpec n In Out) ((StateT.lift (outerReply <$>
          ProbOracleComp.query (.inr (.outer q)))).run sS)) sρ = _
    rw [StateT.run_lift, bind_pure_comp, Functor.map_map, Machine.liftRightProgram_map,
      Machine.liftRightProgram_query]
    erw [Machine.runFrom_map, Machine.runFrom_query, routeCorrupt_handle_inr_inr,
      routeCorrupt_handle_inr_inr]
    have hwrap : ∀ {NQ' NR'} (q' : NetQ) (s : M.State),
        ((dynHybridWrap (NQ := NQ') (NR := NR') M).handle (.inr (.outer q'))).run s =
          (fun p => (Sum.inl p.1, p.2)) <$> liftDynParty ((M.handle (.inr q')).run s) :=
      fun _ s => by
        change liftDynParty ((Sum.inl <$> M.handle (.inr _)).run s) = _
        rw [StateT.run_map]
        exact OracleComp.interpret_map _ _ _
    erw [hwrap, hwrap]
    repeat erw [Functor.map_map]
    erw [Machine.runFrom_map, runFrom_dynParLiftAdversary_liftDynParty]
    repeat erw [Functor.map_map]
    rfl
  · have hrun : ∀ st : S.State,
        Equiv.prodAssoc _ _ _ <$> (routeCorrupt C (dynHybridWrap M)).runFrom
            (Machine.liftRightProgram (partySpec n In Out) (liftDynSubNet sid
              ((fun x => ((Sum.inr (Sum.inr x.1) :
                RoutedNetR Out (NetR ⊕ RoutedNetR SubOut NR₁)),
                Function.update sS sid (some x.2))) <$>
                (S.handle q).run st))) sρ =
          Prod.map _root_.id Prod.swap <$> (Equiv.prodAssoc _ _ _ <$>
            (Prod.map (fun a => ((Sum.inr (Sum.inr a) :
              RoutedNetR Out (NetR ⊕ RoutedNetR SubOut NR₁)), sρ)) _root_.id <$>
              liftDynSessionNet sid
                ((fun x => (x.1, Function.update sS sid (some x.2))) <$> (S.handle q).run st))) :=
      fun st => by
        have hmap : ∀ {α β : Type} (f : α → β)
            (p : ProbOracleComp (netSpec (RoutedNetQ n SubIn NQ₂) (RoutedNetR SubOut NR₂)) α),
            liftDynSubNet (In := In) (Out := Out) (NetQ := NetQ) (NetR := NetR) sid (f <$> p) =
              f <$> liftDynSubNet sid p :=
          fun _ _ => OracleComp.interpret_map _ _ _
        have hmap' : ∀ {α β : Type} (f : α → β)
            (p : ProbOracleComp (netSpec (RoutedNetQ n SubIn NQ₂) (RoutedNetR SubOut NR₂)) α),
            liftDynSessionNet (SubIn := SubIn) (SubOut := SubOut) (NQ := NQ₂) (NR := NR₂)
              sid (f <$> p) =
              f <$> liftDynSessionNet sid p :=
          fun _ _ => OracleComp.interpret_map _ _ _
        rw [hmap, Machine.liftRightProgram_map, hmap']
        erw [Machine.runFrom_map, runFrom_routeCorrupt_liftNet_liftDynSubNet]
        conv_lhs => erw [Functor.map_map, Functor.map_map]
        conv_rhs => erw [Functor.map_map, Functor.map_map, Functor.map_map]
        rfl
    have hR : ((routeCorrupt C (dynHybridWrap M)).handle (.inr (.inr (.sub sid q)))).run sρ =
        (fun a => ((Sum.inr (Sum.inr a) :
          RoutedNetR Out (NetR ⊕ RoutedNetR SubOut NR₁)), sρ)) <$>
          ProbOracleComp.query (spec := dynSessionSpec SID
            (protocolSpec n SubIn SubOut (RoutedNetQ n SubIn NQ₁) (RoutedNetR SubOut NR₁)))
            (sid, Sum.inr q) := by
      erw [routeCorrupt_handle_inr_inr]
      change (fun p => (Sum.inr p.1, p.2)) <$> ((StateT.lift (Sum.inr <$>
        ProbOracleComp.query (sid, Sum.inr q))).run sρ) = _
      rw [StateT.run_lift, bind_pure_comp, Functor.map_map, Functor.map_map]
    erw [hR, Machine.runFrom_map, Machine.runFrom_query]
    change Equiv.prodAssoc _ _ _ <$> (routeCorrupt C (dynHybridWrap M)).runFrom
        (Machine.liftRightProgram (partySpec n In Out)
          (((dynHybridSimMachine S).handle (.inr (.sub sid q))).run sS)) sρ =
      Prod.map _root_.id Prod.swap <$> (Equiv.prodAssoc _ _ _ <$>
        (Prod.map (fun a => ((Sum.inr (Sum.inr a) :
          RoutedNetR Out (NetR ⊕ RoutedNetR SubOut NR₁)), sρ)) _root_.id <$>
          (((dynParLiftAdversary S).handle (sid, Sum.inr q)).run sS)))
    dsimp only [dynHybridSimMachine, dynParLiftAdversary, StateT.run]
    cases hs : sS sid with
    | none =>
      simp only [Machine.liftRightProgram_bind, Machine.liftRightProgram_sample, map_bind]
      erw [Machine.runFrom_bind, Machine.runFrom_sample]
      simp only [bind_map_left, map_bind]
      refine bind_congr fun st => hrun st
    | some st =>
      simp only [pure_bind]
      exact hrun st

private theorem eval_exec_composeDyn_dynHybridSim_swapped {SID : Type} [DecidableEq SID] {n : ℕ}
    {In Out NetQ NetR SubIn SubOut NQ₁ NR₁ NQ₂ NR₂ : Type}
    (ρ : DynHybridProtocol SID n In Out NetQ NetR SubIn SubOut)
    (φ : Protocol n SubIn SubOut NQ₂ NR₂)
    (S : Adversary n (RoutedNetQ n SubIn NQ₁) (RoutedNetR SubOut NR₁)
      (RoutedNetQ n SubIn NQ₂) (RoutedNetR SubOut NR₂))
    (C : Finset (Fin n))
    (Z : Environment n In Out
      (RoutedNetQ n In (DynNetQ SID NetQ (RoutedNetQ n SubIn NQ₁)))
      (RoutedNetR Out (NetR ⊕ RoutedNetR SubOut NR₁)))
    (κ : ℕ) (z : List Bool) :
    (exec (composeDyn ρ φ) (dynHybridSim S) C Z κ z).eval =
      (((dynParLiftAdversary (SID := SID) (S κ C)).comp (dynSessionRouter C (φ κ C))).run
        (absorbDynHybrid C ρ Z κ z)).eval := by
  simp only [exec, execMachine, composeDyn, corruptRouter_comp, dynHybridSim, absorbDynHybrid,
    Machine.run_comp, ← Machine.link_comp]
  refine eval_run_link_swap
    (liftAdversary (n := n) (In := In) (Out := Out) (dynHybridSimMachine (S κ C)))
    (routeCorrupt C (dynHybridWrap (NQ := RoutedNetQ n SubIn NQ₂)
      (NR := RoutedNetR SubOut NR₂) (ρ κ C)))
    (routeCorrupt C (dynHybridWrap (NQ := RoutedNetQ n SubIn NQ₁)
      (NR := RoutedNetR SubOut NR₁) (ρ κ C)))
    (dynParLiftAdversary (S κ C))
    _root_.id _root_.id (id_map _) (id_map _)
    (fun q s => dyn_handle_swap C (ρ κ C) (S κ C) q s.1 s.2)
    (dynSessionRouter C (φ κ C)) (Z κ z)

/-- Single-session lazy adapter holding `Option S.State × Option (corruptRouter C φ).State` so
the entire `(dynParLiftAdversary S).comp (dynSessionRouter C φ)` reduces via
`eval_run_dynParLazy_eq_parFin` and `SSP.run_parFinLazy_eq_parFin` to
`SSP.parFin (fun _ => execMachine φ S κ C)`. -/
private def slotExecMachine {n : ℕ} {SubIn SubOut NQ₁ NR₁ NQ₂ NR₂ : Type}
    (C : Finset (Fin n)) (φ : Machine OracleSpec.empty (protocolSpec n SubIn SubOut NQ₂ NR₂))
    (S : Machine (netSpec (RoutedNetQ n SubIn NQ₂) (RoutedNetR SubOut NR₂))
      (netSpec (RoutedNetQ n SubIn NQ₁) (RoutedNetR SubOut NR₁))) :
    Machine OracleSpec.empty
      (protocolSpec n SubIn SubOut (RoutedNetQ n SubIn NQ₁) (RoutedNetR SubOut NR₁)) where
  State := Option S.State × Option (corruptRouter C φ).State
  init := pure (none, none)
  handle
    | .inl p => fun (sS?, sφ?) => do
        let stφ ← match sφ? with
          | some st => pure st
          | none => ProbOracleComp.sample (corruptRouter C φ).init
        let (r, stφ') ← ((corruptRouter C φ).handle (.inl p)).run stφ
        return (r, (sS?, some stφ'))
    | .inr q => fun (sS?, sφ?) => do
        let stS ← match sS? with
          | some st => pure st
          | none => ProbOracleComp.sample S.init
        let initφ : (q' : ℕ ⊕ RoutedNetQ n SubIn NQ₂) →
            StateT (Option (corruptRouter C φ).State) (ProbOracleComp OracleSpec.empty)
              (probOracleSpec (netSpec (RoutedNetQ n SubIn NQ₂) (RoutedNetR SubOut NR₂)) q') :=
          sumHandler
            (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
            (fun nq sφc? =>
              match sφc? with
              | some st => do
                let __x ← ((corruptRouter C φ).handle (.inr nq)).run st
                pure (__x.1, some __x.2)
              | none => do
                let stφ ← ProbOracleComp.sample (corruptRouter C φ).init
                let __x ← ((corruptRouter C φ).handle (.inr nq)).run stφ
                pure (__x.1, some __x.2))
        let ((r, stS'), sφ'?) ← (OracleComp.interpret initφ ((S.handle q).run stS)).run sφ?
        return (r, (some stS', sφ'?))

private theorem runFrom_dynSessionRouter_liftDynSessionNet {SID : Type} [DecidableEq SID]
    {n : ℕ} {SubIn SubOut NQ NR α : Type} (C : Finset (Fin n))
    (φ : Machine OracleSpec.empty (protocolSpec n SubIn SubOut NQ NR)) (sid : SID)
    (program : ProbOracleComp (netSpec (RoutedNetQ n SubIn NQ) (RoutedNetR SubOut NR)) α)
    (s : (dynSessionRouter (SID := SID) C φ).State) :
    (dynSessionRouter C φ).runFrom (liftDynSessionNet sid program) s =
      (fun (x : α × Option (corruptRouter C φ).State) =>
          (x.1, Function.update s sid x.2)) <$>
        (OracleComp.interpret
          (sumHandler
            (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
            (fun nq sφ? =>
              match sφ? with
              | some st => do
                let __x ← ((corruptRouter C φ).handle (.inr nq)).run st
                pure (__x.1, some __x.2)
              | none => do
                let stφ ← ProbOracleComp.sample (corruptRouter C φ).init
                let __x ← ((corruptRouter C φ).handle (.inr nq)).run stφ
                pure (__x.1, some __x.2)))
          program).run (s sid) := by
  induction program using OracleComp.induction generalizing s with
  | pure a =>
    simp only [liftDynSessionNet, OracleComp.interpret_pure, Machine.runFrom_pure,
      StateT.run_pure, map_pure]
    erw [Function.update_eq_self]
    rfl
  | query_bind q cont ih =>
    rcases q with k | nq
    · simp only [PFunctor.FreeM.bind_eq_bind, liftDynSessionNet, OracleComp.interpret_bind,
        OracleComp.interpret_query, sumHandler]
      rw [← ProbOracleComp.sample_unifFin, Machine.runFrom_bind, Machine.runFrom_sample,
        bind_map_left]
      erw [StateT.run_bind, StateT.run_lift]
      simp only [bind_assoc, pure_bind, map_bind]
      exact bind_congr fun a => ih a s
    · simp only [PFunctor.FreeM.bind_eq_bind, liftDynSessionNet, OracleComp.interpret_bind,
        OracleComp.interpret_query, sumHandler]
      rw [Machine.runFrom_bind, Machine.runFrom_query]
      erw [StateT.run_bind]
      have hstep : ((dynSessionRouter C φ).handle (sid, Sum.inr nq)).run s =
          match s sid with
          | none => (do
            let st ← ProbOracleComp.sample (corruptRouter C φ).init
            let x ← ((corruptRouter C φ).handle (.inr nq)).run st
            pure (x.1, Function.update s sid (some x.2)))
          | some st => (do
            let x ← ((corruptRouter C φ).handle (.inr nq)).run st
            pure (x.1, Function.update s sid (some x.2))) := by
        dsimp only [dynSessionRouter, dynParLazy, StateT.run]
        cases s sid <;> simp only [pure_bind]
      rw [hstep]
      cases hs : s sid with
      | none =>
        dsimp only [StateT.run]
        simp only [pure_bind, bind_assoc, map_bind]
        refine bind_congr fun st => bind_congr fun x => ?_
        dsimp only [dynSessionRouter, dynParLazy]
        erw [ih x.1 (Function.update s sid (some x.2)), Function.update_self]
        refine congrArg (fun f => f <$> _) (funext fun ⟨res, final⟩ => ?_)
        exact Prod.ext rfl (by erw [Function.update_idem])
      | some st =>
        dsimp only [StateT.run]
        simp only [pure_bind, bind_assoc, map_bind]
        refine bind_congr fun x => ?_
        dsimp only [dynSessionRouter, dynParLazy]
        erw [ih x.1 (Function.update s sid (some x.2)), Function.update_self]
        refine congrArg (fun f => f <$> _) (funext fun ⟨res, final⟩ => ?_)
        exact Prod.ext rfl (by erw [Function.update_idem])

private theorem eval_run_dynParLiftAdversary_comp_eq_dynParLazy_slotExec {SID : Type}
    [DecidableEq SID] {n : ℕ} {SubIn SubOut NQ₁ NR₁ NQ₂ NR₂ α : Type}
    (C : Finset (Fin n))
    (φ : Machine OracleSpec.empty (protocolSpec n SubIn SubOut NQ₂ NR₂))
    (S : Machine (netSpec (RoutedNetQ n SubIn NQ₂) (RoutedNetR SubOut NR₂))
      (netSpec (RoutedNetQ n SubIn NQ₁) (RoutedNetR SubOut NR₁)))
    (prog : ProbOracleComp
      (dynSessionSpec SID (protocolSpec n SubIn SubOut (RoutedNetQ n SubIn NQ₁)
        (RoutedNetR SubOut NR₁))) α) :
    (((dynParLiftAdversary (SID := SID) S).comp (dynSessionRouter C φ)).run prog).eval =
      ((dynParLazy fun _ : SID => slotExecMachine C φ S).run prog).eval := by
  let rep : ((dynParLiftAdversary (SID := SID) S).comp (dynSessionRouter C φ)).State →
      (dynParLazy fun _ : SID => slotExecMachine C φ S).State :=
    fun (sS, sφ) sid =>
      match sS sid, sφ sid with
      | none, none => none
      | sS?, sφ? => some (sS?, sφ?)
  refine SSP.eval_run_eq_of_represent _ _ rep ?_ ?_ prog
  · simp [Machine.comp, dynParLiftAdversary, dynSessionRouter, dynParLazy, rep]
  · rintro ⟨sid, q⟩ ⟨sS, sφ⟩
    have hrep_upd : ∀ (sS' : Option S.State) (sφ' : Option (corruptRouter C φ).State)
        (hs : sS'.isSome ∨ sφ'.isSome),
        rep (Function.update sS sid sS', Function.update sφ sid sφ') =
          Function.update (rep (sS, sφ)) sid (some (sS', sφ')) := fun sS' sφ' hs => by
      funext x
      by_cases hx : x = sid
      · subst hx
        dsimp only [rep]
        erw [Function.update_self, Function.update_self, Function.update_self]
        rcases sS' with _ | _ <;> rcases sφ' with _ | _ <;> simp_all
      · dsimp only [rep]
        erw [Function.update_of_ne hx, Function.update_of_ne hx, Function.update_of_ne hx]
    rcases q with p | nq
    · dsimp only [Machine.comp, dynParLiftAdversary, StateT.run, StateT.lift, MonadLift.monadLift]
      rw [bind_pure_comp]
      erw [Machine.runFrom_map, Machine.runFrom_query]
      dsimp only [dynSessionRouter, dynParLazy, slotExecMachine, StateT.run]
      have hleaf : ∀ (x : Option SubOut × (corruptRouter C φ).State)
          (sS_opt : Option S.State) (hs : sS sid = sS_opt),
          (PMF.pure (((Equiv.prodAssoc _ _ _) ((x.1, sS), Function.update sφ sid (some x.2))).1,
            fun sid_1 =>
              match ((Equiv.prodAssoc _ _ _)
                  ((x.1, sS), Function.update sφ sid (some x.2))).2.1 sid_1,
                ((Equiv.prodAssoc _ _ _)
                  ((x.1, sS), Function.update sφ sid (some x.2))).2.2 sid_1 with
              | none, none => none
              | sS?, sφ? => some (sS?, sφ?)) :
            PMF (dynSessionSpec SID (protocolSpec n SubIn SubOut (RoutedNetQ n SubIn NQ₁)
              (RoutedNetR SubOut NR₁)) (sid, Sum.inl p) ×
              (SID → Option (Option S.State × Option (corruptRouter C φ).State)))) =
          PMF.pure (x.1, Function.update (fun sid =>
            match sS sid, sφ sid with
            | none, none => none
            | sS?, sφ? => some (sS?, sφ?)) sid (some (sS_opt, some x.2))) := fun x sS_opt hs => by
        erw [Equiv.prodAssoc_apply]
        dsimp only
        have h := hrep_upd sS_opt (some x.2) (Or.inr rfl)
        have hupd : Function.update sS sid sS_opt = sS := by
          rw [← hs]; exact Function.update_eq_self _ _
        rw [hupd] at h
        dsimp only [rep] at h
        exact congrArg PMF.pure (Prod.ext rfl h)
      cases h1 : sS sid <;> cases h2 : sφ sid
      all_goals simp only [h1, h2, rep, bind_assoc, pure_bind, Machine.closeProgram_map,
        Machine.closeProgram_bind, Machine.closeProgram_sample, Machine.closeProgram_pure,
        ProbComp.eval_map, ProbComp.eval_bind, ProbComp.eval_pure, Functor.map_map]
      all_goals dsimp only [PMF.map]
      all_goals simp only [PMF.bind_bind, PMF.pure_bind, Function.comp_def]
      · refine congrArg _ (funext fun stφ =>
          congrArg (PMF.bind _) (funext fun x => hleaf x none h1))
      · exact congrArg (PMF.bind _) (funext fun x => hleaf x none h1)
      · refine congrArg _ (funext fun stφ =>
          congrArg (PMF.bind _) (funext fun x => hleaf x (some _) h1))
      · exact congrArg (PMF.bind _) (funext fun x => hleaf x (some _) h1)
    · dsimp only [Machine.comp, dynParLiftAdversary, StateT.run]
      have liftDynSessionNet_map_loc :
          ∀ {β γ : Type} (f : β → γ)
            (p : ProbOracleComp (netSpec (RoutedNetQ n SubIn NQ₂) (RoutedNetR SubOut NR₂)) β),
            liftDynSessionNet (SubIn := SubIn) (SubOut := SubOut)
              (NQ := NQ₂) (NR := NR₂) sid (f <$> p) = f <$> liftDynSessionNet sid p :=
        fun _ _ => OracleComp.interpret_map _ _ _
      dsimp only [dynParLazy, slotExecMachine, StateT.run]
      dsimp only [rep] at hrep_upd
      cases h1 : sS sid
      · cases h2 : sφ sid
        all_goals simp only [h1, h2, Machine.runFrom_bind, Machine.runFrom_sample, bind_map_left,
          liftDynSessionNet_map_loc, Machine.runFrom_map,
          runFrom_dynSessionRouter_liftDynSessionNet, rep, Machine.closeProgram_map,
          Machine.closeProgram_bind, Machine.closeProgram_sample, Machine.closeProgram_pure,
          ProbComp.eval_map, ProbComp.eval_bind, ProbComp.eval_pure, PMF.map_bind,
          PMF.pure_bind, PMF.bind_bind]
        all_goals refine congrArg (PMF.bind _) (funext fun _ => ?_)
        all_goals repeat erw [Machine.closeProgram_map]
        all_goals repeat erw [ProbComp.eval_map]
        all_goals repeat erw [PMF.map_comp]
        all_goals dsimp only [PMF.map]
        all_goals
          refine congrArg (PMF.bind _) (funext fun ⟨⟨_, stS'⟩, sφ'?⟩ => ?_)
          refine congrArg PMF.pure (Prod.ext rfl ?_)
          exact hrep_upd (some stS') sφ'? (Or.inl rfl)
      · cases h2 : sφ sid
        all_goals simp only [h1, h2, pure_bind, liftDynSessionNet_map_loc, Machine.runFrom_map,
          runFrom_dynSessionRouter_liftDynSessionNet, rep, Machine.closeProgram_map,
          Machine.closeProgram_bind, Machine.closeProgram_pure, ProbComp.eval_map,
          ProbComp.eval_bind, ProbComp.eval_pure, PMF.pure_bind, PMF.bind_bind]
        all_goals repeat erw [Machine.closeProgram_map]
        all_goals repeat erw [ProbComp.eval_map]
        all_goals repeat erw [PMF.map_comp]
        all_goals dsimp only [PMF.map]
        all_goals
          refine congrArg (PMF.bind _) (funext fun ⟨⟨_, stS'⟩, sφ'?⟩ => ?_)
          refine congrArg PMF.pure (Prod.ext rfl ?_)
          exact hrep_upd (some stS') sφ'? (Or.inl rfl)

private def liftEmpty {ιE : Type} (E : ιE → Type) {α : Type}
    (p : ProbOracleComp OracleSpec.empty α) : ProbOracleComp E α :=
  OracleComp.interpret
    (sumHandler (fun k => OracleComp.query (spec := probOracleSpec E) (.inl k)) fun q => q.elim) p

private theorem liftEmpty_pure {ιE : Type} (E : ιE → Type) {α : Type} (a : α) :
    liftEmpty E (pure a) = pure a := rfl

private theorem liftEmpty_bind {ιE : Type} (E : ιE → Type) {α β : Type}
    (p : ProbOracleComp OracleSpec.empty α) (q : α → ProbOracleComp OracleSpec.empty β) :
    liftEmpty E (p >>= q) = liftEmpty E p >>= fun a => liftEmpty E (q a) :=
  OracleComp.interpret_bind _ _ _

private theorem liftEmpty_sample {ιE : Type} (E : ιE → Type) {α : Type} (p : ProbComp α) :
    liftEmpty E (ProbOracleComp.sample p) = ProbOracleComp.sample p := by
  induction p using OracleComp.induction with
  | pure a => rfl
  | query_bind k f ih =>
    change liftEmpty E (OracleComp.query (Sum.inl k) >>= fun x => ProbOracleComp.sample (f x)) = _
    rw [liftEmpty_bind]
    exact bind_congr fun x => ih x

private theorem runFrom_liftEmpty {ιE : Type} {E : ιE → Type}
    (M : Machine OracleSpec.empty E) {α : Type}
    (p : ProbOracleComp OracleSpec.empty α) (s : M.State) :
    M.runFrom (liftEmpty E p) s = (fun a => (a, s)) <$> p := by
  induction p using OracleComp.induction with
  | pure a => rw [liftEmpty_pure, Machine.runFrom_pure, map_pure]
  | query_bind q _ ih =>
    rcases q with k | e
    · rw [PFunctor.FreeM.bind_eq_bind, liftEmpty_bind, ← ProbOracleComp.sample_unifFin,
        liftEmpty_sample, Machine.runFrom_bind, Machine.runFrom_sample, bind_map_left, map_bind]
      exact bind_congr fun a => ih a
    · exact e.elim

private def initStoreMachine {α : Type} (p : ProbComp α) :
    Machine OracleSpec.empty (fun _ : Unit => α) where
  State := α
  init := p
  handle _ a := pure (a, a)

private theorem pi_const_pure {m : ℕ} {ι : Type} {E : ι → Type} {α : Type} (x : α) :
    OracleComp.pi (fun _ : Fin m => (pure x : OracleComp E α)) = pure (fun _ => x) := by
  induction m with
  | zero =>
    change pure (fun i : Fin 0 => i.elim0) = _
    congr 1
    funext i
    exact i.elim0
  | succ m ih =>
    simp only [OracleComp.pi_succ, pure_bind, ih, map_pure]
    congr 1
    funext i
    exact Fin.cases rfl (fun _ => rfl) i

private theorem runFrom_parFin_initStore_pure {m : ℕ} {α β : Type} (p : ProbComp α)
    (a : β) (s : (SSP.parFin fun _ : Fin m => initStoreMachine p).State) :
    (SSP.parFin fun _ : Fin m => initStoreMachine p).runFrom (pure a) s = pure (a, s) := rfl

private theorem runFrom_parFinLazy_initStore_pure {m : ℕ} {α β : Type} (p : ProbComp α)
    (a : β) (s : (SSP.parFinLazy fun _ : Fin m => initStoreMachine p).State) :
    (SSP.parFinLazy fun _ : Fin m => initStoreMachine p).runFrom (pure a) s = pure (a, s) := rfl

private def slotWithPhiOracle {m n : ℕ} {SubIn SubOut NQ₁ NR₁ NQ₂ NR₂ : Type}
    (C : Finset (Fin n)) (φ : Machine OracleSpec.empty (protocolSpec n SubIn SubOut NQ₂ NR₂))
    (S : Machine (netSpec (RoutedNetQ n SubIn NQ₂) (RoutedNetR SubOut NR₂))
      (netSpec (RoutedNetQ n SubIn NQ₁) (RoutedNetR SubOut NR₁))) :
    Machine (SSP.sessionSpec m fun _ : Unit => (corruptRouter C φ).State)
      (SSP.sessionSpec m (protocolSpec n SubIn SubOut (RoutedNetQ n SubIn NQ₁)
        (RoutedNetR SubOut NR₁))) where
  State := Fin m → Option S.State × Option (corruptRouter C φ).State
  init := pure fun _ => (none, none)
  handle
    | (j, .inl p) => fun s => do
        let stφ ← match (s j).2 with
          | some st => pure st
          | none => ProbOracleComp.query (spec := SSP.sessionSpec m
              fun _ : Unit => (corruptRouter C φ).State) (j, ())
        let (r, stφ') ← liftEmpty (SSP.sessionSpec m fun _ : Unit => (corruptRouter C φ).State)
          (((corruptRouter C φ).handle (.inl p)).run stφ)
        return (r, Function.update s j ((s j).1, some stφ'))
    | (j, .inr q) => fun s => do
        let stS ← match (s j).1 with
          | some st => pure st
          | none => ProbOracleComp.sample S.init
        let hφ : (q' : ℕ ⊕ RoutedNetQ n SubIn NQ₂) →
            StateT (Option (corruptRouter C φ).State)
              (ProbOracleComp (SSP.sessionSpec m fun _ : Unit => (corruptRouter C φ).State))
              (probOracleSpec (netSpec (RoutedNetQ n SubIn NQ₂) (RoutedNetR SubOut NR₂)) q') :=
          sumHandler
            (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
            (fun nq sφc? =>
              match sφc? with
              | some st => do
                let __x ← liftEmpty
                  (SSP.sessionSpec m fun _ : Unit => (corruptRouter C φ).State)
                  (((corruptRouter C φ).handle (.inr nq)).run st)
                pure (__x.1, some __x.2)
              | none => do
                let stφ ← ProbOracleComp.query (spec := SSP.sessionSpec m
                    fun _ : Unit => (corruptRouter C φ).State) (j, ())
                let __x ← liftEmpty
                  (SSP.sessionSpec m fun _ : Unit => (corruptRouter C φ).State)
                  (((corruptRouter C φ).handle (.inr nq)).run stφ)
                pure (__x.1, some __x.2))
        let ((r, stS'), sφ'?) ← (OracleComp.interpret hφ ((S.handle q).run stS)).run (s j).2
        return (r, Function.update s j (some stS', sφ'?))

private def slotWithSOracle {m n : ℕ} {SubIn SubOut NQ₁ NR₁ NQ₂ NR₂ : Type}
    (C : Finset (Fin n)) (φ : Machine OracleSpec.empty (protocolSpec n SubIn SubOut NQ₂ NR₂))
    (S : Machine (netSpec (RoutedNetQ n SubIn NQ₂) (RoutedNetR SubOut NR₂))
      (netSpec (RoutedNetQ n SubIn NQ₁) (RoutedNetR SubOut NR₁))) :
    Machine (SSP.sessionSpec m fun _ : Unit => S.State)
      (SSP.sessionSpec m (protocolSpec n SubIn SubOut (RoutedNetQ n SubIn NQ₁)
        (RoutedNetR SubOut NR₁))) where
  State := Fin m → Option S.State × (corruptRouter C φ).State
  init := OracleComp.pi fun _ => (none, ·) <$> (corruptRouter C φ).init
  handle
    | (j, .inl p) => fun s => do
        let (r, stφ') ← liftEmpty (SSP.sessionSpec m fun _ : Unit => S.State)
          (((corruptRouter C φ).handle (.inl p)).run (s j).2)
        return (r, Function.update s j ((s j).1, stφ'))
    | (j, .inr q) => fun s => do
        let stS ← match (s j).1 with
          | some st => pure st
          | none => ProbOracleComp.query (spec := SSP.sessionSpec m
              fun _ : Unit => S.State) (j, ())
        let hφ : (q' : ℕ ⊕ RoutedNetQ n SubIn NQ₂) →
            StateT (corruptRouter C φ).State
              (ProbOracleComp (SSP.sessionSpec m fun _ : Unit => S.State))
              (probOracleSpec (netSpec (RoutedNetQ n SubIn NQ₂) (RoutedNetR SubOut NR₂)) q') :=
          sumHandler
            (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
            (fun nq stφ =>
              liftEmpty (SSP.sessionSpec m fun _ : Unit => S.State)
                (((corruptRouter C φ).handle (.inr nq)).run stφ))
        let ((r, stS'), stφ') ← (OracleComp.interpret hφ ((S.handle q).run stS)).run (s j).2
        return (r, Function.update s j (some stS', stφ'))

private theorem runFrom_initStore_phi {m n : ℕ} {SubIn SubOut NQ NR : Type}
    (C : Finset (Fin n)) (φ : Machine OracleSpec.empty (protocolSpec n SubIn SubOut NQ NR))
    (j : Fin m) {α β : Type}
    (prog : ProbOracleComp (netSpec (RoutedNetQ n SubIn NQ) (RoutedNetR SubOut NR)) α)
    (sφ? : Option (corruptRouter C φ).State)
    (sInit : Fin m → Option (corruptRouter C φ).State)
    (hs : sφ?.isSome ↔ (sInit j).isSome)
    (k₁ : (α × Option (corruptRouter C φ).State) ×
        (Fin m → Option (corruptRouter C φ).State) → ProbOracleComp OracleSpec.empty β)
    (k₂ : α × Option (corruptRouter C φ).State → ProbOracleComp OracleSpec.empty β)
    (hk : ∀ r sφ'? sInit', (sφ'?.isSome ↔ (sInit' j).isSome) →
      (∀ i, i ≠ j → sInit' i = sInit i) → k₁ ((r, sφ'?), sInit') = k₂ (r, sφ'?)) :
    ((SSP.parFinLazy fun _ : Fin m => initStoreMachine (corruptRouter C φ).init).runFrom
        ((OracleComp.interpret
          (sumHandler
            (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
            (fun nq sφc? =>
              match sφc? with
              | some st => do
                let __x ← liftEmpty
                  (SSP.sessionSpec m fun _ : Unit => (corruptRouter C φ).State)
                  (((corruptRouter C φ).handle (.inr nq)).run st)
                pure (__x.1, some __x.2)
              | none => do
                let stφ ← ProbOracleComp.query (spec := SSP.sessionSpec m
                    fun _ : Unit => (corruptRouter C φ).State) (j, ())
                let __x ← liftEmpty
                  (SSP.sessionSpec m fun _ : Unit => (corruptRouter C φ).State)
                  (((corruptRouter C φ).handle (.inr nq)).run stφ)
                pure (__x.1, some __x.2)))
          prog).run sφ?) sInit >>= k₁) =
      ((OracleComp.interpret
        (sumHandler
          (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
          (fun nq sφc? =>
            match sφc? with
            | some st => do
              let __x ← ((corruptRouter C φ).handle (.inr nq)).run st
              pure (__x.1, some __x.2)
            | none => do
              let stφ ← ProbOracleComp.sample (corruptRouter C φ).init
              let __x ← ((corruptRouter C φ).handle (.inr nq)).run stφ
              pure (__x.1, some __x.2)))
        prog).run sφ? >>= k₂) := by
  induction prog using OracleComp.induction generalizing sφ? sInit with
  | pure a =>
    simp only [OracleComp.interpret_pure, StateT.run_pure, pure_bind]
    exact hk a sφ? sInit hs (fun _ _ => rfl)
  | query_bind q cont ih =>
    rcases q with k | nq
    · simp only [PFunctor.FreeM.bind_eq_bind, OracleComp.interpret_bind, StateT.run_bind,
        OracleComp.interpret_query, sumHandler, StateT.run_lift]
      erw [bind_pure_comp, bind_map_left, Machine.runFrom_bind, Machine.runFrom_sample]
      simp only [bind_map_left, pure_bind, bind_assoc]
      erw [bind_assoc]
      exact bind_congr fun a => ih a sφ? sInit hs hk
    · simp only [PFunctor.FreeM.bind_eq_bind, OracleComp.interpret_bind,
        OracleComp.interpret_query, sumHandler, StateT.run_bind]
      dsimp only [StateT.run]
      cases hsφ : sφ? with
      | some st =>
        dsimp only
        erw [Machine.runFrom_bind, Machine.runFrom_bind, runFrom_liftEmpty, bind_map_left]
        repeat erw [bind_assoc]
        refine bind_congr fun x => ?_
        exact ih x.1 (some x.2) sInit (by simp_all) hk
      | none =>
        have hsI : sInit j = none :=
          Option.not_isSome_iff_eq_none.mp fun h => by
            have := hs.mpr h
            simp [hsφ] at this
        dsimp only
        erw [Machine.runFrom_bind, Machine.runFrom_bind, Machine.runFrom_query]
        have hstep : ((SSP.parFinLazy fun _ : Fin m =>
            initStoreMachine (corruptRouter C φ).init).handle (j, ())).run sInit =
            (fun st => (st, Function.update sInit j (some st))) <$>
              ProbOracleComp.sample (corruptRouter C φ).init := by
          dsimp only [SSP.parFinLazy, initStoreMachine, StateT.run]
          rw [hsI]
          simp only [pure_bind, ← bind_pure_comp]
        rw [hstep]
        erw [bind_map_left]
        repeat erw [bind_assoc]
        refine bind_congr fun st => ?_
        erw [Machine.runFrom_bind, runFrom_liftEmpty, bind_map_left]
        repeat erw [bind_assoc]
        refine bind_congr fun x => ?_
        refine ih x.1 (some x.2) (Function.update sInit j (some st)) (by simp)
          fun r' sφ'' sInit' hs'' hne => ?_
        exact hk r' sφ'' sInit' hs'' fun i hi => by
          rw [hne i hi, Function.update_of_ne hi]

private theorem eval_run_slotExec_eq_slotWithPhiOracle {m n : ℕ}
    {SubIn SubOut NQ₁ NR₁ NQ₂ NR₂ α : Type}
    (C : Finset (Fin n)) (φ : Machine OracleSpec.empty (protocolSpec n SubIn SubOut NQ₂ NR₂))
    (S : Machine (netSpec (RoutedNetQ n SubIn NQ₂) (RoutedNetR SubOut NR₂))
      (netSpec (RoutedNetQ n SubIn NQ₁) (RoutedNetR SubOut NR₁)))
    (prog : ProbOracleComp
      (SSP.sessionSpec m (protocolSpec n SubIn SubOut (RoutedNetQ n SubIn NQ₁)
        (RoutedNetR SubOut NR₁))) α) :
    ((SSP.parFin fun _ : Fin m => slotExecMachine C φ S).run prog).eval =
      (((slotWithPhiOracle C φ S).comp
        (SSP.parFinLazy fun _ : Fin m =>
          initStoreMachine (corruptRouter C φ).init)).run prog).eval := by
  let R : (SSP.parFin fun _ : Fin m => slotExecMachine C φ S).State →
      ((slotWithPhiOracle C φ S).comp
        (SSP.parFinLazy fun _ : Fin m => initStoreMachine (corruptRouter C φ).init)).State →
      Prop :=
    fun s₁ (sSφ?, sInit) =>
      (∀ j, s₁ j = sSφ? j) ∧ (∀ j, (sSφ? j).2.isSome ↔ (sInit j).isSome)
  have hrun :
      Prod.fst <$>
          (SSP.parFin fun _ : Fin m => slotExecMachine C φ S).runFrom prog (fun _ => (none, none)) =
        Prod.fst <$>
          ((slotWithPhiOracle C φ S).comp
            (SSP.parFinLazy fun _ : Fin m => initStoreMachine (corruptRouter C φ).init)).runFrom
            prog (fun _ => (none, none), fun _ => none) := by
    have := Machine.runFrom_intertwine
      (SSP.parFin fun _ : Fin m => slotExecMachine C φ S)
      ((slotWithPhiOracle C φ S).comp
        (SSP.parFinLazy fun _ : Fin m => initStoreMachine (corruptRouter C φ).init))
      (fun _ => True) R prog
      (OracleComp.QueriesSatisfy.of_forall (fun q => by cases q <;> trivial) _)
      (fun _ => (none, none)) (fun _ => (none, none), fun _ => none)
      ⟨fun _ => rfl, fun _ => Iff.rfl⟩
      (fun x => pure x.1) (fun x => pure x.1) (fun _ _ _ _ => rfl)
      fun ⟨j, q⟩ s₁ ⟨sSφ?, sInit⟩ k₁ k₂ _ ⟨hEq, hIso⟩ hk => by
        have hpar : ∀ q',
            ((SSP.parFin fun _ : Fin m => slotExecMachine C φ S).handle (j, q')).run s₁ =
              (fun x => (x.1, Function.update s₁ j x.2)) <$>
                ((slotExecMachine C φ S).handle q').run (s₁ j) := fun _ => rfl
        rw [hpar]
        rcases q with p | nq
        · dsimp only [slotExecMachine, Machine.comp, slotWithPhiOracle, StateT.run]
          rw [hEq j]
          cases h2 : (sSφ? j).2 with
          | some st =>
            dsimp only
            conv_lhs =>
              erw [pure_bind, map_bind, bind_assoc]
              simp only [map_pure, pure_bind]
            conv_rhs =>
              erw [pure_bind, Machine.runFrom_bind, runFrom_liftEmpty, bind_map_left,
                bind_map_left]
              simp only [runFrom_parFinLazy_initStore_pure, pure_bind, bind_assoc,
                Equiv.prodAssoc_apply]
            refine bind_congr fun x => ?_
            refine hk x.1 _ (Function.update sSφ? j ((sSφ? j).1, some x.2), sInit)
              ⟨fun i => ?_, fun i => ?_⟩
            · by_cases hi : i = j
              · rw [hi]; erw [Function.update_self, Function.update_self]
              · erw [Function.update_of_ne hi, Function.update_of_ne hi]; exact hEq i
            · by_cases hi : i = j
              · rw [hi]; erw [Function.update_self]
                simp [(hIso j).mp (by simp [h2])]
              · erw [Function.update_of_ne hi]; exact hIso i
          | none =>
            have hsI : sInit j = none :=
              Option.not_isSome_iff_eq_none.mp fun h => by
                have := (hIso j).mpr h
                simp [h2] at this
            dsimp only
            conv_lhs =>
              simp only [map_bind, map_pure, pure_bind]
              repeat erw [bind_assoc]
            conv_rhs =>
              erw [Machine.runFrom_bind, Machine.runFrom_query]
            have hstep : ((SSP.parFinLazy fun _ : Fin m =>
                initStoreMachine (corruptRouter C φ).init).handle (j, ())).run sInit =
                (fun st => (st, Function.update sInit j (some st))) <$>
                  ProbOracleComp.sample (corruptRouter C φ).init := by
              dsimp only [SSP.parFinLazy, initStoreMachine, StateT.run]
              rw [hsI]
              simp only [pure_bind, ← bind_pure_comp]
            rw [hstep]
            conv_rhs =>
              erw [bind_map_left, bind_assoc, bind_map_left]
            refine bind_congr fun st => ?_
            conv_lhs => erw [bind_assoc]
            conv_rhs =>
              erw [Machine.runFrom_bind, runFrom_liftEmpty, bind_map_left]
              simp only [runFrom_parFinLazy_initStore_pure, pure_bind, bind_assoc,
                Equiv.prodAssoc_apply]
            refine bind_congr fun x => ?_
            refine hk x.1 _ (Function.update sSφ? j ((sSφ? j).1, some x.2),
              Function.update sInit j (some st)) ⟨fun i => ?_, fun i => ?_⟩
            · by_cases hi : i = j
              · rw [hi]; erw [Function.update_self, Function.update_self]
              · erw [Function.update_of_ne hi, Function.update_of_ne hi]; exact hEq i
            · by_cases hi : i = j
              · rw [hi]; erw [Function.update_self, Function.update_self]; rfl
              · erw [Function.update_of_ne hi, Function.update_of_ne hi]; exact hIso i
        · dsimp only [slotExecMachine, Machine.comp, slotWithPhiOracle, StateT.run]
          rw [hEq j]
          have hStepS : ∀ stS : S.State,
              ((fun x => (x.1, Function.update s₁ j x.2)) <$>
                (do
                  let a ←
                    (OracleComp.interpret
                      (sumHandler
                        (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
                        (fun nq' sφc? =>
                          match sφc? with
                          | some st => do
                            let __x ← ((corruptRouter C φ).handle (.inr nq')).run st
                            pure (__x.1, some __x.2)
                          | none => do
                            let stφ ← ProbOracleComp.sample (corruptRouter C φ).init
                            let __x ← ((corruptRouter C φ).handle (.inr nq')).run stφ
                            pure (__x.1, some __x.2)))
                      ((S.handle nq).run stS)).run (sSφ? j).2
                  pure (a.1.1, some a.1.2, a.2)) >>= k₁) =
                ((Equiv.prodAssoc _ _ _ <$>
                  ((SSP.parFinLazy fun _ : Fin m =>
                      initStoreMachine (corruptRouter C φ).init).runFrom
                    (do
                      let a ←
                        (OracleComp.interpret
                          (sumHandler
                            (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
                            (fun nq' sφc? =>
                              match sφc? with
                              | some st => do
                                let __x ← liftEmpty
                                  (SSP.sessionSpec m fun _ : Unit => (corruptRouter C φ).State)
                                  (((corruptRouter C φ).handle (.inr nq')).run st)
                                pure (__x.1, some __x.2)
                              | none => do
                                let stφ ← ProbOracleComp.query (spec := SSP.sessionSpec m
                                    fun _ : Unit => (corruptRouter C φ).State) (j, ())
                                let __x ← liftEmpty
                                  (SSP.sessionSpec m fun _ : Unit => (corruptRouter C φ).State)
                                  (((corruptRouter C φ).handle (.inr nq')).run stφ)
                                pure (__x.1, some __x.2)))
                          ((S.handle nq).run stS)).run (sSφ? j).2
                      pure (a.1.1, Function.update sSφ? j (some a.1.2, a.2)))
                    sInit)) >>= k₂) := by
            intro stS
            conv_lhs =>
              erw [map_bind, bind_assoc]
              simp only [map_pure]
            conv_rhs =>
              erw [Machine.runFrom_bind, map_bind, bind_assoc]
              simp only [runFrom_parFinLazy_initStore_pure, map_pure, Equiv.prodAssoc_apply]
            refine (runFrom_initStore_phi C φ j ((S.handle nq).run stS) (sSφ? j).2 sInit
              (hIso j)
              (fun x => pure (x.1.1.1, Function.update sSφ? j (some x.1.1.2, x.1.2), x.2) >>= k₂)
              (fun x => pure (x.1.1, Function.update s₁ j (some x.1.2, x.2)) >>= k₁)
              fun ⟨r, stS'⟩ sφ'? sInit' hs' hne => ?_).symm
            erw [pure_bind, pure_bind]
            refine (hk r (Function.update s₁ j (some stS', sφ'?))
              (Function.update sSφ? j (some stS', sφ'?), sInit') ⟨fun i => ?_, fun i => ?_⟩).symm
            · by_cases hi : i = j
              · rw [hi]; erw [Function.update_self, Function.update_self]
              · erw [Function.update_of_ne hi, Function.update_of_ne hi]; exact hEq i
            · by_cases hi : i = j
              · rw [hi]; erw [Function.update_self]; exact hs'
              · erw [Function.update_of_ne hi]; simp [hne i hi, hIso]
          cases h1 : (sSφ? j).1 with
          | some stS =>
            dsimp only
            conv_lhs => erw [pure_bind]
            conv_rhs => erw [pure_bind]
            exact hStepS stS
          | none =>
            dsimp only
            conv_lhs => erw [map_bind, bind_assoc]
            conv_rhs => erw [Machine.runFrom_bind, Machine.runFrom_sample, map_bind,
              bind_map_left, bind_assoc]
            exact bind_congr fun stS => hStepS stS
    simpa only [bind_pure_comp] using this
  have hL : ((SSP.parFin fun _ : Fin m => slotExecMachine C φ S).run prog).eval =
      (Machine.closeProgram (Prod.fst <$>
        (SSP.parFin fun _ : Fin m => slotExecMachine C φ S).runFrom prog
          (fun _ => (none, none)))).eval := by
    simp only [Machine.run, Machine.link, SSP.parFin, slotExecMachine,
      pi_const_pure, ProbOracleComp.sample_pure, pure_bind]
  have hR : (((slotWithPhiOracle C φ S).comp
        (SSP.parFinLazy fun _ : Fin m =>
          initStoreMachine (corruptRouter C φ).init)).run prog).eval =
      (Machine.closeProgram (Prod.fst <$>
        ((slotWithPhiOracle C φ S).comp
          (SSP.parFinLazy fun _ : Fin m => initStoreMachine (corruptRouter C φ).init)).runFrom
          prog (fun _ => (none, none), fun _ => none))).eval := by
    simp only [Machine.run, Machine.link, Machine.comp, slotWithPhiOracle, SSP.parFinLazy,
      ProbOracleComp.sample_pure, pure_bind]
  rw [hL, hR, hrun]

private theorem runFrom_eagerPhi_step {m n : ℕ} {SubIn SubOut NQ NR : Type}
    (C : Finset (Fin n)) (φ : Machine OracleSpec.empty (protocolSpec n SubIn SubOut NQ NR))
    (j : Fin m) {α β : Type}
    (prog : ProbOracleComp (netSpec (RoutedNetQ n SubIn NQ) (RoutedNetR SubOut NR)) α)
    (sφ? : Option (corruptRouter C φ).State)
    (sPhiInit : Fin m → (corruptRouter C φ).State)
    (k₁ : ((α × Option (corruptRouter C φ).State) ×
      (SSP.parFin fun _ : Fin m => initStoreMachine (corruptRouter C φ).init).State) →
      ProbOracleComp OracleSpec.empty β)
    (k₂ : (α × (corruptRouter C φ).State) → ProbOracleComp OracleSpec.empty β)
    (hk : ∀ r sφ'?, k₁ ((r, sφ'?), sPhiInit) = k₂ (r, sφ'?.getD (sPhiInit j))) :
    ((SSP.parFin fun _ : Fin m => initStoreMachine (corruptRouter C φ).init).runFrom
        ((OracleComp.interpret
          (sumHandler
            (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
            (fun nq sφc? =>
              match sφc? with
              | some st => do
                let __x ← liftEmpty
                  (SSP.sessionSpec m fun _ : Unit => (corruptRouter C φ).State)
                  (((corruptRouter C φ).handle (.inr nq)).run st)
                pure (__x.1, some __x.2)
              | none => do
                let stφ ← ProbOracleComp.query (spec := SSP.sessionSpec m
                    fun _ : Unit => (corruptRouter C φ).State) (j, ())
                let __x ← liftEmpty
                  (SSP.sessionSpec m fun _ : Unit => (corruptRouter C φ).State)
                  (((corruptRouter C φ).handle (.inr nq)).run stφ)
                pure (__x.1, some __x.2)))
          prog).run sφ?) sPhiInit >>= k₁) =
      ((OracleComp.interpret
        (sumHandler
          (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
          (fun nq stφ => ((corruptRouter C φ).handle (.inr nq)).run stφ))
        prog).run (sφ?.getD (sPhiInit j)) >>= k₂) := by
  induction prog using OracleComp.induction generalizing sφ? with
  | pure a =>
    simp only [OracleComp.interpret_pure, StateT.run_pure, pure_bind]
    exact hk a sφ?
  | query_bind q cont ih =>
    rcases q with k | nq
    · simp only [PFunctor.FreeM.bind_eq_bind, OracleComp.interpret_bind, StateT.run_bind,
        OracleComp.interpret_query, sumHandler, StateT.run_lift]
      erw [bind_pure_comp, bind_map_left, Machine.runFrom_bind, Machine.runFrom_sample, bind_assoc]
      simp only [bind_map_left, pure_bind, bind_assoc]
      exact bind_congr fun a => ih a sφ?
    · simp only [PFunctor.FreeM.bind_eq_bind, OracleComp.interpret_bind,
        OracleComp.interpret_query, sumHandler, StateT.run_bind]
      dsimp only [StateT.run]
      cases hsφ : sφ? with
      | some st =>
        dsimp only [Option.getD]
        erw [Machine.runFrom_bind, Machine.runFrom_bind, runFrom_liftEmpty, bind_map_left]
        repeat erw [bind_assoc]
        refine bind_congr fun x => ?_
        exact ih x.1 (some x.2)
      | none =>
        dsimp only [Option.getD]
        erw [Machine.runFrom_bind, Machine.runFrom_bind, Machine.runFrom_query]
        have hstep : ((SSP.parFin fun _ : Fin m =>
            initStoreMachine (corruptRouter C φ).init).handle (j, ())).run sPhiInit =
            pure (sPhiInit j, sPhiInit) := by
          dsimp only [SSP.parFin, initStoreMachine, StateT.run]
          rw [map_pure]
          erw [Function.update_eq_self]
        erw [hstep, pure_bind, Machine.runFrom_bind, runFrom_liftEmpty, bind_map_left]
        repeat erw [bind_assoc]
        refine bind_congr fun x => ?_
        exact ih x.1 (some x.2)

private theorem runFrom_liftEmpty_interpret_s {m n : ℕ} {SubIn SubOut NQ NR : Type}
    (C : Finset (Fin n)) (φ : Machine OracleSpec.empty (protocolSpec n SubIn SubOut NQ NR))
    {SState : Type} (M : Machine OracleSpec.empty (SSP.sessionSpec m fun _ : Unit => SState))
    {α : Type}
    (prog : ProbOracleComp (netSpec (RoutedNetQ n SubIn NQ) (RoutedNetR SubOut NR)) α)
    (stφ : (corruptRouter C φ).State) (sM : M.State) :
    M.runFrom ((OracleComp.interpret
      (sumHandler
        (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
        (fun nq st => liftEmpty (SSP.sessionSpec m fun _ : Unit => SState)
          (((corruptRouter C φ).handle (.inr nq)).run st)))
      prog).run stφ) sM =
      (fun a => (a, sM)) <$>
        (OracleComp.interpret
          (sumHandler
            (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
            (fun nq st => ((corruptRouter C φ).handle (.inr nq)).run st))
          prog).run stφ := by
  induction prog using OracleComp.induction generalizing stφ with
  | pure a =>
    simp only [OracleComp.interpret_pure, StateT.run_pure, Machine.runFrom_pure, map_pure]
  | query_bind q _ ih =>
    rcases q with k | nq
    · simp only [PFunctor.FreeM.bind_eq_bind, OracleComp.interpret_bind, StateT.run_bind,
        OracleComp.interpret_query, sumHandler, StateT.run_lift]
      erw [bind_pure_comp, bind_map_left, Machine.runFrom_bind, Machine.runFrom_sample]
      simp only [bind_map_left, map_bind]
      exact bind_congr fun a => ih a stφ
    · simp only [PFunctor.FreeM.bind_eq_bind, OracleComp.interpret_bind,
        OracleComp.interpret_query, sumHandler, StateT.run_bind]
      dsimp only [StateT.run]
      erw [Machine.runFrom_bind, runFrom_liftEmpty]
      simp only [bind_map_left, map_bind]
      exact bind_congr fun x => ih x.1 x.2

private theorem eval_run_slotWithPhiOracle_eq_slotWithSOracle {m n : ℕ}
    {SubIn SubOut NQ₁ NR₁ NQ₂ NR₂ α : Type}
    (C : Finset (Fin n)) (φ : Machine OracleSpec.empty (protocolSpec n SubIn SubOut NQ₂ NR₂))
    (S : Machine (netSpec (RoutedNetQ n SubIn NQ₂) (RoutedNetR SubOut NR₂))
      (netSpec (RoutedNetQ n SubIn NQ₁) (RoutedNetR SubOut NR₁)))
    (prog : ProbOracleComp
      (SSP.sessionSpec m (protocolSpec n SubIn SubOut (RoutedNetQ n SubIn NQ₁)
        (RoutedNetR SubOut NR₁))) α) :
    (((slotWithPhiOracle C φ S).comp
        (SSP.parFin fun _ : Fin m => initStoreMachine (corruptRouter C φ).init)).run prog).eval =
      (((slotWithSOracle C φ S).comp
        (SSP.parFinLazy fun _ : Fin m => initStoreMachine S.init)).run prog).eval := by
  let R : ((slotWithPhiOracle C φ S).comp
        (SSP.parFin fun _ : Fin m => initStoreMachine (corruptRouter C φ).init)).State →
      ((slotWithSOracle C φ S).comp
        (SSP.parFinLazy fun _ : Fin m => initStoreMachine S.init)).State → Prop :=
    fun (sSφ?, sPhiInit) (sPhiS?, sSInit) =>
      (∀ j, (sPhiS? j).1 = (sSφ? j).1) ∧
      (∀ j, (sPhiS? j).2 = (sSφ? j).2.getD (sPhiInit j)) ∧
      (∀ j, (sSφ? j).1.isSome ↔ (sSInit j).isSome)
  have hStep : ∀ (sPhiInit : Fin m → (corruptRouter C φ).State),
      Prod.fst <$>
          ((slotWithPhiOracle C φ S).comp
            (SSP.parFin fun _ : Fin m => initStoreMachine (corruptRouter C φ).init)).runFrom
            prog (fun _ => (none, none), sPhiInit) =
        Prod.fst <$>
          ((slotWithSOracle C φ S).comp
            (SSP.parFinLazy fun _ : Fin m => initStoreMachine S.init)).runFrom
            prog (fun j => (none, sPhiInit j), fun _ => none) := by
    intro sPhiInit
    have := Machine.runFrom_intertwine
      ((slotWithPhiOracle C φ S).comp
        (SSP.parFin fun _ : Fin m => initStoreMachine (corruptRouter C φ).init))
      ((slotWithSOracle C φ S).comp
        (SSP.parFinLazy fun _ : Fin m => initStoreMachine S.init))
      (fun _ => True) R prog
      (OracleComp.QueriesSatisfy.of_forall (fun q => by cases q <;> trivial) _)
      (fun _ => (none, none), sPhiInit) (fun j => (none, sPhiInit j), fun _ => none)
      ⟨fun _ => rfl, fun _ => rfl, fun _ => Iff.rfl⟩
      (fun x => pure x.1) (fun x => pure x.1) (fun _ _ _ _ => rfl)
      fun ⟨j, q⟩ ⟨sSφ?, sPhiInit'⟩ ⟨sPhiS?, sSInit⟩ k₁ k₂ _ ⟨h1, h2, hIso⟩ hk => by
        rcases q with p | nq
        · dsimp only [Machine.comp, slotWithPhiOracle, slotWithSOracle, StateT.run]
          rw [h2 j]
          cases hφ : (sSφ? j).2 with
          | some st =>
            dsimp only [Option.getD]
            conv_lhs =>
              erw [Machine.runFrom_bind, runFrom_parFin_initStore_pure, pure_bind,
                Machine.runFrom_bind, runFrom_liftEmpty, bind_map_left, bind_map_left]
              simp only [runFrom_parFin_initStore_pure, pure_bind, bind_assoc,
                Equiv.prodAssoc_apply]
            conv_rhs =>
              erw [Machine.runFrom_bind, runFrom_liftEmpty, bind_map_left, bind_map_left]
              simp only [runFrom_parFinLazy_initStore_pure, pure_bind, bind_assoc,
                Equiv.prodAssoc_apply]
            refine bind_congr fun x => ?_
            refine hk x.1 (Function.update sSφ? j ((sSφ? j).1, some x.2), sPhiInit')
              (Function.update sPhiS? j ((sPhiS? j).1, x.2), sSInit)
              ⟨fun i => ?_, fun i => ?_, fun i => ?_⟩
            · by_cases hi : i = j
              · rw [hi]; erw [Function.update_self, Function.update_self]; exact h1 j
              · erw [Function.update_of_ne hi, Function.update_of_ne hi]; exact h1 i
            · by_cases hi : i = j
              · rw [hi]; erw [Function.update_self, Function.update_self]; rfl
              · erw [Function.update_of_ne hi, Function.update_of_ne hi]; exact h2 i
            · by_cases hi : i = j
              · rw [hi]; erw [Function.update_self]; exact hIso j
              · erw [Function.update_of_ne hi]; exact hIso i
          | none =>
            dsimp only [Option.getD]
            dsimp only [SSP.parFin, initStoreMachine] at sPhiInit' ⊢
            conv_lhs => erw [Machine.runFrom_bind, Machine.runFrom_query]
            have hstep : ((SSP.parFin fun _ : Fin m =>
                initStoreMachine (corruptRouter C φ).init).handle (j, ())).run sPhiInit' =
                pure (sPhiInit' j, sPhiInit') := by
              dsimp only [SSP.parFin, initStoreMachine, StateT.run]
              rw [map_pure]
              erw [Function.update_eq_self]
            conv_lhs =>
              erw [hstep, pure_bind, Machine.runFrom_bind, runFrom_liftEmpty, bind_map_left,
                bind_map_left]
              simp only [runFrom_parFin_initStore_pure, pure_bind, bind_assoc,
                Equiv.prodAssoc_apply]
            conv_rhs =>
              erw [Machine.runFrom_bind, runFrom_liftEmpty, bind_map_left, bind_map_left]
              simp only [runFrom_parFinLazy_initStore_pure, pure_bind, bind_assoc,
                Equiv.prodAssoc_apply]
            refine bind_congr fun x => ?_
            refine hk x.1 (Function.update sSφ? j ((sSφ? j).1, some x.2), sPhiInit')
              (Function.update sPhiS? j ((sPhiS? j).1, x.2), sSInit)
              ⟨fun i => ?_, fun i => ?_, fun i => ?_⟩
            · by_cases hi : i = j
              · rw [hi]; erw [Function.update_self, Function.update_self]; exact h1 j
              · erw [Function.update_of_ne hi, Function.update_of_ne hi]; exact h1 i
            · by_cases hi : i = j
              · rw [hi]; erw [Function.update_self, Function.update_self]; rfl
              · erw [Function.update_of_ne hi, Function.update_of_ne hi]; exact h2 i
            · by_cases hi : i = j
              · rw [hi]; erw [Function.update_self]; exact hIso j
              · erw [Function.update_of_ne hi]; exact hIso i
        · dsimp only [Machine.comp, slotWithPhiOracle, slotWithSOracle, StateT.run]
          have hStepS : ∀ (stS : S.State) (sSInit' : Fin m → Option S.State),
              (∀ i, i ≠ j → ((sSφ? i).1.isSome ↔ (sSInit' i).isSome)) →
              (sSInit' j).isSome →
              ((Equiv.prodAssoc _ _ _ <$>
                ((SSP.parFin fun _ : Fin m =>
                    initStoreMachine (corruptRouter C φ).init).runFrom
                  (do
                    let a ←
                      (OracleComp.interpret
                        (sumHandler
                          (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
                          (fun nq' sφc? =>
                            match sφc? with
                            | some st => do
                              let __x ← liftEmpty
                                (SSP.sessionSpec m fun _ : Unit => (corruptRouter C φ).State)
                                (((corruptRouter C φ).handle (.inr nq')).run st)
                              pure (__x.1, some __x.2)
                            | none => do
                              let stφ ← ProbOracleComp.query (spec := SSP.sessionSpec m
                                  fun _ : Unit => (corruptRouter C φ).State) (j, ())
                              let __x ← liftEmpty
                                (SSP.sessionSpec m fun _ : Unit => (corruptRouter C φ).State)
                                (((corruptRouter C φ).handle (.inr nq')).run stφ)
                              pure (__x.1, some __x.2)))
                        ((S.handle nq).run stS)).run (sSφ? j).2
                    pure (a.1.1, Function.update sSφ? j (some a.1.2, a.2)))
                  sPhiInit')) >>= k₁) =
              ((OracleComp.interpret
                (sumHandler
                  (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
                  (fun nq' st => ((corruptRouter C φ).handle (.inr nq')).run st))
                ((S.handle nq).run stS)).run (sPhiS? j).2 >>= fun ((r, stS'), stφ') =>
                k₂ (r, (Function.update sPhiS? j (some stS', stφ'), sSInit'))) := by
            intro stS sSInit' hIsoAll hsj
            conv_lhs =>
              erw [Machine.runFrom_bind, bind_map_left, bind_assoc]
              simp only [runFrom_parFin_initStore_pure, pure_bind, Equiv.prodAssoc_apply]
            rw [h2 j]
            refine runFrom_eagerPhi_step C φ j ((S.handle nq).run stS) (sSφ? j).2 sPhiInit'
              (fun x => k₁ (x.1.1.1, Function.update sSφ? j (some x.1.1.2, x.1.2), x.2))
              (fun x => k₂ (x.1.1, (Function.update sPhiS? j (some x.1.2, x.2), sSInit')))
              fun ⟨r, stS'⟩ sφ'? => ?_
            refine hk r (Function.update sSφ? j (some stS', sφ'?), sPhiInit')
              (Function.update sPhiS? j (some stS', sφ'?.getD (sPhiInit' j)), sSInit')
              ⟨fun i => ?_, fun i => ?_, fun i => ?_⟩
            · by_cases hi : i = j
              · rw [hi]; erw [Function.update_self, Function.update_self]
              · erw [Function.update_of_ne hi, Function.update_of_ne hi]; exact h1 i
            · by_cases hi : i = j
              · rw [hi]; erw [Function.update_self, Function.update_self]
              · erw [Function.update_of_ne hi, Function.update_of_ne hi]; exact h2 i
            · by_cases hi : i = j
              · rw [hi]; erw [Function.update_self]; exact iff_of_true rfl hsj
              · erw [Function.update_of_ne hi]; exact hIsoAll i hi
          rw [h1 j]
          cases hS : (sSφ? j).1 with
          | some stS =>
            have hsj : (sSInit j).isSome := (hIso j).mp (by simp [hS])
            dsimp only
            conv_lhs => erw [pure_bind]
            conv_rhs =>
              erw [pure_bind, Machine.runFrom_bind, runFrom_liftEmpty_interpret_s, bind_map_left,
                bind_map_left]
              simp only [runFrom_parFinLazy_initStore_pure, pure_bind, bind_assoc,
                Equiv.prodAssoc_apply]
            exact hStepS stS sSInit (fun i _ => hIso i) hsj
          | none =>
            have hsI : sSInit j = none :=
              Option.not_isSome_iff_eq_none.mp fun h => by
                have := (hIso j).mpr h
                simp [hS] at this
            dsimp only
            dsimp only [slotWithSOracle, SSP.parFinLazy, initStoreMachine] at sPhiS? sSInit
            conv_lhs =>
              arg 1; arg 2
              erw [Machine.runFrom_bind, Machine.runFrom_sample, bind_map_left]
            conv_lhs =>
              erw [map_bind, bind_assoc]
            have hstep : ((SSP.parFinLazy fun _ : Fin m =>
                initStoreMachine S.init).handle (j, ())).run sSInit =
                (fun st => (st, Function.update sSInit j (some st))) <$>
                  ProbOracleComp.sample S.init := by
              dsimp only [SSP.parFinLazy, initStoreMachine, StateT.run]
              rw [hsI]
              simp only [pure_bind, ← bind_pure_comp]
            conv_rhs =>
              erw [Machine.runFrom_bind, Machine.runFrom_query, hstep, bind_map_left, bind_assoc,
                bind_map_left]
            refine bind_congr fun stS => ?_
            conv_rhs =>
              erw [Machine.runFrom_bind, runFrom_liftEmpty_interpret_s, bind_map_left]
              repeat erw [bind_assoc]
              dsimp only [SSP.parFinLazy, initStoreMachine]
            exact hStepS stS (Function.update sSInit j (some stS))
              (fun i hi => by rw [Function.update_of_ne hi]; exact hIso i) (by simp)
    simpa only [bind_pure_comp] using this
  have hInitL : ProbComp.eval
      ((slotWithPhiOracle C φ S).comp
        (SSP.parFin fun _ : Fin m => initStoreMachine (corruptRouter C φ).init)).init =
      (ProbComp.eval (OracleComp.pi fun _ : Fin m => (corruptRouter C φ).init)).map
        fun sPhiInit => (fun _ => (none, none), sPhiInit) := by
    dsimp only [Machine.comp, slotWithPhiOracle, SSP.parFin, initStoreMachine]
    simp only [ProbComp.eval_bind, ProbComp.eval_pure, PMF.pure_bind]
    rfl
  have hInitR : ProbComp.eval
      ((slotWithSOracle C φ S).comp
        (SSP.parFinLazy fun _ : Fin m => initStoreMachine S.init)).init =
      (ProbComp.eval (OracleComp.pi fun _ : Fin m => (corruptRouter C φ).init)).map
        fun sPhiInit => (fun j => (none, sPhiInit j), fun _ => none) := by
    dsimp only [Machine.comp, slotWithSOracle, SSP.parFinLazy, initStoreMachine]
    simp only [pure_bind, ProbComp.eval_bind, ProbComp.eval_pure]
    rw [ProbComp.eval_pi_map, PMF.bind_map]
    rfl
  simp only [Machine.run, Machine.link, Machine.closeProgram_bind, Machine.closeProgram_sample,
    ProbComp.eval_bind]
  erw [hInitL, hInitR, PMF.bind_map, PMF.bind_map]
  refine congrArg _ (funext fun sPhiInit => ?_)
  exact congrArg (fun p => (Machine.closeProgram p).eval) (hStep sPhiInit)

private theorem runFrom_corruptRouter_liftNet_eq_interpret {n : ℕ}
    {SubIn SubOut NQ₂ NR₂ α : Type} (C : Finset (Fin n))
    (φ : Machine OracleSpec.empty (protocolSpec n SubIn SubOut NQ₂ NR₂))
    (prog : ProbOracleComp (netSpec (RoutedNetQ n SubIn NQ₂) (RoutedNetR SubOut NR₂)) α)
    (stφ : (corruptRouter C φ).State) :
    (corruptRouter C φ).runFrom (liftNet prog) stφ =
      (OracleComp.interpret
        (sumHandler
          (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
          (fun nq st => ((corruptRouter C φ).handle (.inr nq)).run st))
        prog).run stφ := by
  induction prog using OracleComp.induction generalizing stφ with
  | pure a =>
    simp only [liftNet, Machine.liftRightProgram_pure, Machine.runFrom_pure,
      OracleComp.interpret_pure, StateT.run_pure]
  | query_bind q _ ih =>
    rcases q with k | nq
    · simp only [PFunctor.FreeM.bind_eq_bind, liftNet, Machine.liftRightProgram_bind]
      have hs : Machine.liftRightProgram (partySpec n SubIn SubOut)
          (OracleComp.query (spec := probOracleSpec
            (netSpec (RoutedNetQ n SubIn NQ₂) (RoutedNetR SubOut NR₂))) (Sum.inl k)) =
          ProbOracleComp.sample (ProbComp.unifFin k) := by
        rw [← ProbOracleComp.sample_unifFin, Machine.liftRightProgram_sample]
      rw [hs, Machine.runFrom_bind, Machine.runFrom_sample, bind_map_left]
      rw [OracleComp.interpret_bind, OracleComp.interpret_query, sumHandler, StateT.run_bind]
      simp only [StateT.run_lift, bind_pure_comp, bind_map_left]
      exact bind_congr fun a => ih a stφ
    · simp only [PFunctor.FreeM.bind_eq_bind, liftNet, Machine.liftRightProgram_bind]
      erw [← ProbOracleComp.query, Machine.liftRightProgram_query, Machine.runFrom_bind,
        Machine.runFrom_query]
      rw [OracleComp.interpret_bind]
      erw [OracleComp.interpret_query]
      rw [sumHandler, StateT.run_bind]
      exact bind_congr fun x => ih x.1 x.2

private theorem eval_run_slotWithSOracle_eq_execMachine {m n : ℕ}
    {SubIn SubOut NQ₁ NR₁ NQ₂ NR₂ α : Type}
    (C : Finset (Fin n)) (φ : Protocol n SubIn SubOut NQ₂ NR₂)
    (S : Adversary n (RoutedNetQ n SubIn NQ₁) (RoutedNetR SubOut NR₁)
      (RoutedNetQ n SubIn NQ₂) (RoutedNetR SubOut NR₂)) (κ : ℕ)
    (prog : ProbOracleComp
      (SSP.sessionSpec m (protocolSpec n SubIn SubOut (RoutedNetQ n SubIn NQ₁)
        (RoutedNetR SubOut NR₁))) α) :
    (((slotWithSOracle C (φ κ C) (S κ C)).comp
        (SSP.parFin fun _ : Fin m => initStoreMachine (S κ C).init)).run prog).eval =
      ((SSP.parFin fun _ : Fin m => execMachine φ S κ C).run prog).eval := by
  let rep : ((slotWithSOracle C (φ κ C) (S κ C)).comp
        (SSP.parFin fun _ : Fin m => initStoreMachine (S κ C).init)).State →
      (SSP.parFin fun _ : Fin m => execMachine φ S κ C).State :=
    fun (sPhiS?, sSInit) j => ((sPhiS? j).1.getD (sSInit j), (sPhiS? j).2)
  refine SSP.eval_run_eq_of_represent
    ((slotWithSOracle C (φ κ C) (S κ C)).comp
      (SSP.parFin fun _ : Fin m => initStoreMachine (S κ C).init))
    (SSP.parFin fun _ : Fin m => execMachine φ S κ C) rep ?_ ?_ prog
  · have hpair := congrArg (PMF.map fun f (j : Fin m) => Prod.swap (f j))
      (ProbComp.eval_pi_pair (fun _ : Fin m => (corruptRouter C (φ κ C)).init)
        (fun _ : Fin m => (S κ C).init))
    rw [← ProbComp.eval_pi_map] at hpair
    simp only [map_bind, map_pure, Prod.swap] at hpair
    dsimp only [PMF.map] at hpair
    simp only [PMF.bind_bind, PMF.pure_bind, Function.comp_def] at hpair
    dsimp only [Machine.comp, slotWithSOracle, SSP.parFin, initStoreMachine, execMachine,
      Machine.liftRight, liftAdversary]
    simp only [ProbComp.eval_bind, ProbComp.eval_pure]
    rw [ProbComp.eval_pi_map]
    dsimp only [PMF.map]
    simp only [PMF.bind_bind, PMF.pure_bind, rep, Function.comp_def]
    erw [PMF.bind_comm]
    exact hpair.symm
  · rintro ⟨j, q⟩ ⟨sPhiS?, sSInit⟩
    rcases q with p | nq
    · have hL_inl : ∀ (s1 : (slotWithSOracle C (φ κ C) (S κ C)).State)
          (s2 : (SSP.parFin fun _ : Fin m => initStoreMachine (S κ C).init).State),
          (((slotWithSOracle C (φ κ C) (S κ C)).comp
            (SSP.parFin fun _ : Fin m => initStoreMachine (S κ C).init)).handle (j, .inl p)).run
            (s1, s2) =
            (fun a => (a.1, (Function.update s1 j ((s1 j).1, a.2), s2))) <$>
              (((corruptRouter C (φ κ C)).handle (.inl p)).run (s1 j).2) := fun s1 s2 => by
        dsimp only [Machine.comp, slotWithSOracle, SSP.parFin, initStoreMachine, StateT.run]
        rw [bind_pure_comp]
        erw [Machine.runFrom_map, runFrom_liftEmpty]
        simp only [Functor.map_map]
        rfl
      have hR_inl : ∀ s : (SSP.parFin fun _ : Fin m => execMachine φ S κ C).State,
          ((SSP.parFin fun _ : Fin m => execMachine φ S κ C).handle (j, .inl p)).run s =
            (fun a => (a.1, Function.update s j ((s j).1, a.2))) <$>
              (((corruptRouter C (φ κ C)).handle (.inl p)).run (s j).2) := fun s => by
        dsimp only [SSP.parFin, execMachine, Machine.comp, liftAdversary, Machine.liftRight,
          StateT.lift, MonadLift.monadLift, StateT.run]
        rw [bind_pure_comp]
        erw [Machine.runFrom_map, Machine.runFrom_query]
        simp only [Functor.map_map]
        rfl
      rw [hL_inl sPhiS? sSInit, hR_inl (rep (sPhiS?, sSInit))]
      repeat erw [Machine.closeProgram_map]
      repeat erw [ProbComp.eval_map]
      repeat erw [PMF.map_comp]
      refine congrArg (PMF.map · _) (funext fun ⟨r, stφ'⟩ => ?_)
      refine Prod.ext rfl (funext fun i => ?_)
      dsimp only [Function.comp, rep]
      by_cases hi : i = j
      · rw [hi]; erw [Function.update_self, Function.update_self]
      · erw [Function.update_of_ne hi, Function.update_of_ne hi]
    · have hR_inr : ∀ s : (SSP.parFin fun _ : Fin m => execMachine φ S κ C).State,
          ((SSP.parFin fun _ : Fin m => execMachine φ S κ C).handle (j, .inr nq)).run s =
            (fun ((r, stS'), stφ') => (r, Function.update s j (stS', stφ'))) <$>
              ((OracleComp.interpret
                (sumHandler
                  (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
                  (fun nq' st => ((corruptRouter C (φ κ C)).handle (.inr nq')).run st))
                (((S κ C).handle nq).run (s j).1)).run (s j).2) := fun s => by
        dsimp only [SSP.parFin, execMachine, Machine.comp, liftAdversary, Machine.liftRight,
          StateT.run]
        erw [runFrom_corruptRouter_liftNet_eq_interpret]
        simp only [Functor.map_map]
        rfl
      rw [hR_inr (rep (sPhiS?, sSInit))]
      cases hS : (sPhiS? j).1 with
      | some stS =>
        have hL_inr : ∀ (s1 : (slotWithSOracle C (φ κ C) (S κ C)).State)
            (s2 : (SSP.parFin fun _ : Fin m => initStoreMachine (S κ C).init).State),
            (s1 j).1 = some stS →
            (((slotWithSOracle C (φ κ C) (S κ C)).comp
              (SSP.parFin fun _ : Fin m => initStoreMachine (S κ C).init)).handle (j, .inr nq)).run
              (s1, s2) =
              (fun ((r, stS'), stφ') =>
                (r, (Function.update s1 j (some stS', stφ'), s2))) <$>
                ((OracleComp.interpret
                  (sumHandler
                    (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
                    (fun nq' st => ((corruptRouter C (φ κ C)).handle (.inr nq')).run st))
                  (((S κ C).handle nq).run stS)).run (s1 j).2) := fun s1 s2 hs1 => by
          dsimp only [Machine.comp, slotWithSOracle, StateT.run]
          rw [hs1]
          dsimp only
          erw [pure_bind, Machine.runFrom_bind, runFrom_liftEmpty_interpret_s, bind_map_left]
          simp only [map_bind, runFrom_parFin_initStore_pure, map_pure, Equiv.prodAssoc_apply]
          rw [← bind_pure_comp]
          rfl
        rw [hL_inr sPhiS? sSInit hS]
        have hrepj : rep (sPhiS?, sSInit) j = (stS, (sPhiS? j).2) := by simp [rep, hS]; rfl
        rw [hrepj]
        repeat erw [Machine.closeProgram_map]
        repeat erw [ProbComp.eval_map]
        repeat erw [PMF.map_comp]
        refine congrArg (PMF.map · _) (funext fun x => ?_)
        refine Prod.ext rfl (funext fun i => ?_)
        dsimp only [Function.comp, rep]
        by_cases hi : i = j
        · rw [hi]; erw [Function.update_self, Function.update_self]; rfl
        · erw [Function.update_of_ne hi, Function.update_of_ne hi]
      | none =>
        have hL_inr : ∀ (s1 : (slotWithSOracle C (φ κ C) (S κ C)).State)
            (s2 : (SSP.parFin fun _ : Fin m => initStoreMachine (S κ C).init).State),
            (s1 j).1 = none →
            (((slotWithSOracle C (φ κ C) (S κ C)).comp
              (SSP.parFin fun _ : Fin m => initStoreMachine (S κ C).init)).handle (j, .inr nq)).run
              (s1, s2) =
              (fun ((r, stS'), stφ') =>
                (r, (Function.update s1 j (some stS', stφ'), s2))) <$>
                ((OracleComp.interpret
                  (sumHandler
                    (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
                    (fun nq' st => ((corruptRouter C (φ κ C)).handle (.inr nq')).run st))
                  (((S κ C).handle nq).run (s2 j))).run (s1 j).2) := fun s1 s2 hs1 => by
          dsimp only [Machine.comp, slotWithSOracle, StateT.run]
          rw [hs1]
          dsimp only
          erw [Machine.runFrom_bind, Machine.runFrom_query]
          have hstep : ((SSP.parFin fun _ : Fin m =>
              initStoreMachine (S κ C).init).handle (j, ())).run s2 =
              pure (s2 j, s2) := by
            dsimp only [SSP.parFin, initStoreMachine, StateT.run]
            rw [map_pure]
            erw [Function.update_eq_self]
          erw [hstep, pure_bind, Machine.runFrom_bind, runFrom_liftEmpty_interpret_s, bind_map_left]
          simp only [map_bind, runFrom_parFin_initStore_pure, map_pure, Equiv.prodAssoc_apply]
          rw [← bind_pure_comp]
          rfl
        rw [hL_inr sPhiS? sSInit hS]
        have hrepj : rep (sPhiS?, sSInit) j = (sSInit j, (sPhiS? j).2) := by simp [rep, hS]; rfl
        rw [hrepj]
        repeat erw [Machine.closeProgram_map]
        repeat erw [ProbComp.eval_map]
        repeat erw [PMF.map_comp]
        refine congrArg (PMF.map · _) (funext fun x => ?_)
        refine Prod.ext rfl (funext fun i => ?_)
        dsimp only [Function.comp, rep]
        by_cases hi : i = j
        · rw [hi]; erw [Function.update_self, Function.update_self]; rfl
        · erw [Function.update_of_ne hi, Function.update_of_ne hi]

private theorem eval_exec_composeDyn_dynHybridSim_eq_parFin {SID : Type} [DecidableEq SID] {n : ℕ}
    {In Out NetQ NetR SubIn SubOut NQ₁ NR₁ NQ₂ NR₂ : Type}
    (ρ : DynHybridProtocol SID n In Out NetQ NetR SubIn SubOut)
    (φ : Protocol n SubIn SubOut NQ₂ NR₂)
    (S : Adversary n (RoutedNetQ n SubIn NQ₁) (RoutedNetR SubOut NR₁)
      (RoutedNetQ n SubIn NQ₂) (RoutedNetR SubOut NR₂))
    (C : Finset (Fin n))
    (Z : Environment n In Out
      (RoutedNetQ n In (DynNetQ SID NetQ (RoutedNetQ n SubIn NQ₁)))
      (RoutedNetR Out (NetR ⊕ RoutedNetR SubOut NR₁)))
    (κ : ℕ) (z : List Bool) {b : ℕ} (hb : OracleComp.IsQueryBounded (absorbDynHybrid C ρ Z κ z) b) :
    (exec (composeDyn ρ φ) (dynHybridSim S) C Z κ z).eval =
      ((SSP.parFin fun _ : Fin (b + 1) => execMachine φ S κ C).run
        ((allocMachine SID b _).link (absorbDynHybrid C ρ Z κ z))).eval := by
  rw [eval_exec_composeDyn_dynHybridSim_swapped,
    eval_run_dynParLiftAdversary_comp_eq_dynParLazy_slotExec,
    eval_run_dynParLazy_eq_parFin (slotExecMachine C (φ κ C) (S κ C)) b hb,
    eval_run_slotExec_eq_slotWithPhiOracle, Machine.run_comp, SSP.run_parFinLazy_eq_parFin,
    ← Machine.run_comp, eval_run_slotWithPhiOracle_eq_slotWithSOracle, Machine.run_comp,
    SSP.run_parFinLazy_eq_parFin, ← Machine.run_comp, eval_run_slotWithSOracle_eq_execMachine]

private theorem isQueryBounded_link_allocMachine {SID : Type} [DecidableEq SID] (m : ℕ)
    {ιE : Type} (E : ιE → Type) {γ : Type} {prog : ProbOracleComp (dynSessionSpec SID E) γ}
    {b : ℕ} (h : OracleComp.IsQueryBounded prog b) :
    OracleComp.IsQueryBounded ((allocMachine SID m E).link prog) b := by
  have hrun : ∀ (seen : List SID) {α : Type} (p : ProbOracleComp (dynSessionSpec SID E) α)
      {k : ℕ} (hp : OracleComp.IsQueryBounded p k),
      OracleComp.IsQueryBounded (Prod.fst <$> (allocMachine SID m E).runFrom p seen) k := by
    intro seen α p k hp
    induction hp generalizing seen with
    | pure a n =>
      erw [Machine.runFrom_pure, map_pure]
      exact OracleComp.IsCostBounded.pure _ _
    | liftBind q cont n hcont ih =>
      rcases q with r | ⟨sid, e⟩
      · erw [Machine.runFrom_bind]
        have hs : (allocMachine SID m E).runFrom (OracleComp.query (Sum.inl r)) seen =
            (fun a => (a, seen)) <$> ProbOracleComp.sample (ProbComp.unifFin r) := by
          erw [← ProbOracleComp.sample_unifFin, Machine.runFrom_sample]; rfl
        erw [hs, bind_map_left, map_bind]
        rw [ProbOracleComp.sample_unifFin]
        have hbind : OracleComp.IsQueryBounded
            (OracleComp.query (Sum.inl r) >>= fun a =>
              Prod.fst <$> (allocMachine SID m E).runFrom (cont a) seen) (1 + n) :=
          (OracleComp.IsCostBounded.query (cost := fun _ => (1 : ℕ)) (Sum.inl r)).bind fun a => by
            simpa only [ProbComp.unifFin] using ih a seen
        exact hbind.mono (by omega)
      · erw [Machine.runFrom_bind]
        have hq : (allocMachine SID m E).runFrom (OracleComp.query (Sum.inr (sid, e))) seen =
            (fun r => (r, (allocSlot m seen sid).2)) <$>
              ProbOracleComp.query (spec := SSP.sessionSpec (m + 1) E)
                ((allocSlot m seen sid).1, e) := by
          erw [← ProbOracleComp.query, Machine.runFrom_query]
          dsimp only [allocMachine, StateT.run]
          rw [bind_pure_comp]
        erw [hq, bind_map_left, map_bind]
        have hbind : OracleComp.IsQueryBounded
            (OracleComp.query (Sum.inr ((allocSlot m seen sid).1, e)) >>= fun a =>
              Prod.fst <$> (allocMachine SID m E).runFrom (cont a) (allocSlot m seen sid).2)
            (1 + n) :=
          (OracleComp.IsCostBounded.query (cost := fun _ => (1 : ℕ))
            (Sum.inr ((allocSlot m seen sid).1, e))).bind fun a => ih a (allocSlot m seen sid).2
        exact hbind.mono (by omega)
  change OracleComp.IsQueryBounded
    (ProbOracleComp.sample (pure ([] : List SID)) >>=
      fun s₀ => Prod.fst <$> (allocMachine SID m E).runFrom prog s₀) b
  rw [ProbOracleComp.sample_pure, pure_bind]
  exact hrun [] prog h

/-- Single-hop hybrid distinguisher for dynamic-SID composition, running `absorbDynHybrid` reindexed
through `allocMachine` against `SSP.hybridDistinguisher`. -/
@[expose] def dynSessionHopDistinguisher {SID : Type} [DecidableEq SID] {n : ℕ}
    {In Out NetQ NetR SubIn SubOut NQ₁ NR₁ NQ₂ NR₂ : Type}
    (C : Finset (Fin n))
    (ρ : DynHybridProtocol SID n In Out NetQ NetR SubIn SubOut)
    (π : Protocol n SubIn SubOut NQ₁ NR₁)
    (φ : Protocol n SubIn SubOut NQ₂ NR₂)
    (S : Adversary n (RoutedNetQ n SubIn NQ₁) (RoutedNetR SubOut NR₁)
      (RoutedNetQ n SubIn NQ₂) (RoutedNetR SubOut NR₂))
    (Z : Environment n In Out
      (RoutedNetQ n In (DynNetQ SID NetQ (RoutedNetQ n SubIn NQ₁)))
      (RoutedNetR Out (NetR ⊕ RoutedNetR SubOut NR₁)))
    (κ : ℕ) (z : List Bool) (b : ℕ) (j₀ : Fin (b + 1)) :
    ProbOracleComp
      (protocolSpec n SubIn SubOut (RoutedNetQ n SubIn NQ₁) (RoutedNetR SubOut NR₁)) Bool :=
  SSP.hybridDistinguisher
    (fun _ => corruptRouter C (π κ C))
    (fun _ => execMachine φ S κ C)
    ((allocMachine SID b _).link (absorbDynHybrid C ρ Z κ z))
    j₀

/-- Hybrid telescoping bound for dynamic-SID sessions: for any `b`-query-bounded absorbed
environment `absorbDynHybrid C ρ Z κ z`, the dummy-adversary distinguishing advantage between
`composeDyn ρ π` and `composeDyn ρ φ` (under `dynHybridSim S`) is at most the sum over
`j : Fin (b + 1)` of single-session advantages against `dynSessionHopDistinguisher`. -/
theorem advantage_composeDyn_le_sum {SID : Type} [DecidableEq SID] {n : ℕ}
    {In Out NetQ NetR SubIn SubOut NQ₁ NR₁ NQ₂ NR₂ : Type}
    (ρ : DynHybridProtocol SID n In Out NetQ NetR SubIn SubOut)
    (π : Protocol n SubIn SubOut NQ₁ NR₁)
    (φ : Protocol n SubIn SubOut NQ₂ NR₂)
    (S : Adversary n (RoutedNetQ n SubIn NQ₁) (RoutedNetR SubOut NR₁)
      (RoutedNetQ n SubIn NQ₂) (RoutedNetR SubOut NR₂))
    (C : Finset (Fin n))
    (Z : Environment n In Out
      (RoutedNetQ n In (DynNetQ SID NetQ (RoutedNetQ n SubIn NQ₁)))
      (RoutedNetR Out (NetR ⊕ RoutedNetR SubOut NR₁)))
    (κ : ℕ) (z : List Bool) {b : ℕ}
    (hb : OracleComp.IsQueryBounded (absorbDynHybrid C ρ Z κ z) b) :
    advantage (composeDyn ρ π) (composeDyn ρ φ)
        (dummyAdversary n _ _) (dynHybridSim S) C Z κ z ≤
      ∑ j : Fin (b + 1),
        advantage π φ (dummyAdversary n _ _) S C
          (fun κ' z' => if κ' = κ ∧ z' = z then
            dynSessionHopDistinguisher C ρ π φ S Z κ z b j else pure false) κ z := by
  have hreal : (exec (composeDyn ρ π) (dummyAdversary n _ _) C Z κ z).eval =
      ((SSP.parFin fun _ : Fin (b + 1) => corruptRouter C (π κ C)).run
        ((allocMachine SID b _).link (absorbDynHybrid C ρ Z κ z))).eval := by
    rw [exec_composeDyn_dummy, dynSessionRouter, eval_run_dynParLazy_eq_parFin _ b hb]
  have hideal : (exec (composeDyn ρ φ) (dynHybridSim S) C Z κ z).eval =
      ((SSP.parFin fun _ : Fin (b + 1) => execMachine φ S κ C).run
        ((allocMachine SID b _).link (absorbDynHybrid C ρ Z κ z))).eval :=
    eval_exec_composeDyn_dynHybridSim_eq_parFin ρ φ S C Z κ z hb
  have hcongr :
      advantage (composeDyn ρ π) (composeDyn ρ φ)
          (dummyAdversary n _ _) (dynHybridSim S) C Z κ z =
        SSP.advantage ((allocMachine SID b _).link (absorbDynHybrid C ρ Z κ z))
          (SSP.parFin fun _ : Fin (b + 1) => corruptRouter C (π κ C))
          (SSP.parFin fun _ : Fin (b + 1) => execMachine φ S κ C) := by
    simp only [advantage, SSP.advantage, hreal, hideal]
  rw [hcongr]
  refine (SSP.advantage_parFin_le_sum
    (fun _ => corruptRouter C (π κ C))
    (fun _ => execMachine φ S κ C)
    ((allocMachine SID b _).link (absorbDynHybrid C ρ Z κ z))).trans_eq ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [advantage, SSP.advantage, exec, execMachine,
    dummyAdversary, Machine.liftRight_id, Machine.run_comp, Machine.link_id, ↓reduceIte,
    and_self]
  rfl

end ExecutionBridge

/-! ### Dynamic-SID UC composition theorems -/

section Composition

private theorem isQueryBounded_dynSessionHopDistinguisher {SID : Type} [DecidableEq SID] {n : ℕ}
    {In Out NetQ NetR SubIn SubOut NQ₁ NR₁ NQ₂ NR₂ : Type}
    (C : Finset (Fin n))
    (ρ : DynHybridProtocol SID n In Out NetQ NetR SubIn SubOut)
    (π : Protocol n SubIn SubOut NQ₁ NR₁)
    (φ : Protocol n SubIn SubOut NQ₂ NR₂)
    (S : Adversary n (RoutedNetQ n SubIn NQ₁) (RoutedNetR SubOut NR₁)
      (RoutedNetQ n SubIn NQ₂) (RoutedNetR SubOut NR₂))
    (Z : Environment n In Out
      (RoutedNetQ n In (DynNetQ SID NetQ (RoutedNetQ n SubIn NQ₁)))
      (RoutedNetR Out (NetR ⊕ RoutedNetR SubOut NR₁)))
    {pρ pπ pφ pD pZ : Polynomial ℕ}
    (hρ : ρ.PolyBounded pρ) (hπ : π.PolyBounded pπ) (hφ : φ.PolyBounded pφ)
    (hS : S.PolyBounded pD) (hZ : Z.PolyBounded pZ)
    (κ : ℕ) (z : List Bool) (j₀ : Fin ((absorbPoly pZ pρ).eval κ + 1)) :
    OracleComp.IsQueryBounded
      (dynSessionHopDistinguisher C ρ π φ S Z κ z ((absorbPoly pZ pρ).eval κ) j₀)
      ((dynSessionHopPoly pZ pρ pπ pφ pD).eval κ) := by
  let b := (absorbPoly pZ pρ).eval κ
  have hreal : ∀ _ : Fin (b + 1),
      (corruptRouter C (π κ C)).IsBounded ((sessionUnitPoly pπ pφ pD).eval κ) := fun _ =>
    (isBounded_routeCorrupt C (hπ κ C)).mono (by simp [sessionUnitPoly])
  have hideal : ∀ _ : Fin (b + 1),
      (execMachine φ S κ C).IsBounded ((sessionUnitPoly pπ pφ pD).eval κ) := fun _ => by
    have hcomp := (Machine.isBounded_liftRight (partySpec n SubIn SubOut) (hS κ C)).comp
      (isBounded_routeCorrupt C (hφ κ C))
    refine hcomp.mono ?_
    simp [sessionUnitPoly, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_one]
  have habs :
      OracleComp.IsQueryBounded ((allocMachine SID b _).link (absorbDynHybrid C ρ Z κ z)) b :=
    isQueryBounded_link_allocMachine b _ (absorbDynHybrid_polyBounded C hρ hZ κ z)
  have hdist := SSP.isQueryBounded_hybridDistinguisher
    (fun _ : Fin (b + 1) => corruptRouter C (π κ C))
    (fun _ : Fin (b + 1) => execMachine φ S κ C)
    j₀ hreal hideal habs
  refine hdist.mono (le_of_eq ?_)
  simp only [dynSessionHopPoly, absorbPoly, b, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_one, Polynomial.eval_ofNat]

/-- Dynamic-SID composition step for `EmulatesDummyWithin`, extending
`EmulatesDummyWithin.composeMulti` from fixed `Fin m` to an arbitrary `[DecidableEq SID]` with
lazy first-touch session creation (`dynHybridSim`).
Adapts Theorem 22 of [Canetti2020] (JACM p. 28:58; ePrint 2000/067, p. 61) to static corruptions,
depth-1 dynamic sessions, and this library's call-bounded statistical model; not the full PPT ITM
theorem (`#6043` remains open). -/
theorem EmulatesDummyWithin.composeDyn {SID : Type} [DecidableEq SID] {n : ℕ}
    {In Out NetQ NetR SubIn SubOut NQ₁ NR₁ NQ₂ NR₂ : Type}
    {ρ : DynHybridProtocol SID n In Out NetQ NetR SubIn SubOut}
    {π : Protocol n SubIn SubOut NQ₁ NR₁} {φ : Protocol n SubIn SubOut NQ₂ NR₂}
    {pρ pπ pφ pD : Polynomial ℕ} {ε : Polynomial ℕ → ℕ → ℝ≥0}
    (hρ : ρ.PolyBounded pρ) (hπ : π.PolyBounded pπ) (hφ : φ.PolyBounded pφ)
    (h : EmulatesDummyWithin π φ pD ε) :
    EmulatesDummyWithin (composeDyn ρ π) (composeDyn ρ φ)
      (2 * pD + 1)
      (fun pZ κ => ((absorbPoly pZ pρ).eval κ + 1) •
        ε (dynSessionHopPoly pZ pρ pπ pφ pD) κ) := by
  obtain ⟨S_D, hSD, hadv⟩ := h
  refine ⟨dynHybridSim S_D, dynHybridSim_polyBounded hSD, fun C Z pZ hZ κ z => ?_⟩
  have habs := absorbDynHybrid_polyBounded C hρ hZ κ z
  refine (advantage_composeDyn_le_sum ρ π φ S_D C Z κ z habs).trans ?_
  have hle : ∀ j : Fin ((absorbPoly pZ pρ).eval κ + 1),
      advantage π φ (dummyAdversary n _ _) S_D C
        (fun κ' z' => if κ' = κ ∧ z' = z then
          dynSessionHopDistinguisher C ρ π φ S_D Z κ z ((absorbPoly pZ pρ).eval κ) j
          else pure false) κ z ≤
        ε (dynSessionHopPoly pZ pρ pπ pφ pD) κ := fun j => by
    refine hadv C _ (dynSessionHopPoly pZ pρ pπ pφ pD) (fun κ' z' => ?_) κ z
    by_cases hcond : κ' = κ ∧ z' = z
    · rcases hcond with ⟨hκ, hz⟩
      rw [hκ, hz]
      simpa only [↓reduceIte, and_self] using
        isQueryBounded_dynSessionHopDistinguisher C ρ π φ S_D Z hρ hπ hφ hSD hZ κ z j
    · simp only [hcond, ↓reduceIte]
      exact OracleComp.IsCostBounded.pure false _
  calc ∑ j : Fin ((absorbPoly pZ pρ).eval κ + 1),
        advantage π φ (dummyAdversary n _ _) S_D C
          (fun κ' z' => if κ' = κ ∧ z' = z then
            dynSessionHopDistinguisher C ρ π φ S_D Z κ z ((absorbPoly pZ pρ).eval κ) j
            else pure false) κ z
      ≤ ∑ _j : Fin ((absorbPoly pZ pρ).eval κ + 1), ε (dynSessionHopPoly pZ pρ pπ pφ pD) κ :=
        Finset.sum_le_sum fun j _ => hle j
    _ = ((absorbPoly pZ pρ).eval κ + 1) • ε (dynSessionHopPoly pZ pρ pπ pφ pD) κ := by
        simp [Finset.sum_const]

/-- Dynamic-SID concrete quantitative composition step for `EmulatesWithin` with lazy first-touch
session creation over an arbitrary `[DecidableEq SID]`.
Adapts Theorem 22 of [Canetti2020] (JACM p. 28:58; ePrint 2000/067, p. 61) to static corruptions,
depth-1 dynamic sessions, and this library's call-bounded statistical model; not the full PPT ITM
theorem (`#6043` remains open). -/
theorem EmulatesWithin.composeDyn {SID : Type} [DecidableEq SID] {n : ℕ}
    {In Out NetQ NetR SubIn SubOut NQ₁ NR₁ NQ₂ NR₂ : Type}
    {ρ : DynHybridProtocol SID n In Out NetQ NetR SubIn SubOut}
    {π : Protocol n SubIn SubOut NQ₁ NR₁} {φ : Protocol n SubIn SubOut NQ₂ NR₂}
    {pρ pπ pφ g : Polynomial ℕ} {ε : Polynomial ℕ → Polynomial ℕ → ℕ → ℝ≥0}
    (hρ : ρ.PolyBounded pρ) (hπ : π.PolyBounded pπ) (hφ : φ.PolyBounded pφ)
    (h : EmulatesWithin π φ g ε) :
    EmulatesWithin (composeDyn ρ π) (composeDyn ρ φ)
      (Polynomial.X * (2 * g.comp (Polynomial.X + 1) + 1 + 1) +
        (2 * g.comp (Polynomial.X + 1) + 1))
      (fun pA pZ κ =>
        ((absorbPoly (absorbPoly pZ pA) pρ).eval κ + 1) •
          ε 1 (dynSessionHopPoly (absorbPoly pZ pA) pρ pπ pφ (g.comp (Polynomial.X + 1))) κ) := by
  rcases h.emulatesDummyWithin with ⟨pD, hpD, S_D, hSD, hadv⟩
  have hD' : EmulatesDummyWithin π φ (g.comp (Polynomial.X + 1)) (fun pZ => ε 1 pZ) :=
    ⟨S_D, hSD.mono fun κ => by
      simpa [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
        using hpD κ, hadv⟩
  exact (EmulatesDummyWithin.composeDyn hρ hπ hφ hD').emulatesWithin

private theorem polynomiallyBounded_eval_add_one (p : Polynomial ℕ) :
    PolynomiallyBounded (fun κ => p.eval κ + 1) := by
  refine polynomiallyBounded_iff_le.mpr
    ⟨p.sum (fun _ c => c) + 1, p.natDegree, fun κ => ?_⟩
  have h1 : p.eval κ ≤ p.sum (fun _ c => c) * (κ + 1) ^ p.natDegree := by
    rw [Polynomial.eval_eq_sum]
    calc ∑ i ∈ p.support, p.coeff i * κ ^ i
        ≤ ∑ i ∈ p.support, p.coeff i * (κ + 1) ^ p.natDegree := by
          refine Finset.sum_le_sum fun i hi => Nat.mul_le_mul_left _ ?_
          exact (Nat.pow_le_pow_left (Nat.le_succ κ) i).trans
            (Nat.pow_le_pow_right (Nat.succ_pos κ) (Polynomial.le_natDegree_of_mem_supp _ hi))
      _ = (∑ i ∈ p.support, p.coeff i) * (κ + 1) ^ p.natDegree := by
          rw [← Finset.sum_mul]
  calc p.eval κ + 1
      ≤ p.sum (fun _ c => c) * (κ + 1) ^ p.natDegree + 1 * (κ + 1) ^ p.natDegree := by
        refine Nat.add_le_add h1 ?_
        rw [one_mul]
        exact Nat.one_le_pow _ _ (Nat.succ_pos κ)
    _ = (p.sum (fun _ c => c) + 1) * (κ + 1) ^ p.natDegree := by ring

/-- Dynamic-SID composition step for `Emulates` with lazy first-touch session creation over an
arbitrary `[DecidableEq SID]`: if `π` emulates `φ` and `ρ`, `π`, `φ` are polynomially call-bounded,
then `composeDyn ρ π` emulates `composeDyn ρ φ`.
Adapts Theorem 22 of [Canetti2020] (JACM p. 28:58; ePrint 2000/067, p. 61) to static corruptions,
depth-1 dynamic sessions, and this library's call-bounded statistical model; not the full PPT ITM
theorem (`#6043` remains open). -/
theorem Emulates.composeDyn {SID : Type} [DecidableEq SID] {n : ℕ}
    {In Out NetQ NetR SubIn SubOut NQ₁ NR₁ NQ₂ NR₂ : Type}
    {ρ : DynHybridProtocol SID n In Out NetQ NetR SubIn SubOut}
    {π : Protocol n SubIn SubOut NQ₁ NR₁} {φ : Protocol n SubIn SubOut NQ₂ NR₂}
    {pρ pπ pφ : Polynomial ℕ}
    (hρ : ρ.PolyBounded pρ) (hπ : π.PolyBounded pπ) (hφ : φ.PolyBounded pφ)
    (h : Emulates π φ) :
    Emulates (composeDyn ρ π) (composeDyn ρ φ) := by
  obtain ⟨S_D, pD, hSD, hadv⟩ :=
    h _ _ (dummyAdversary n _ _) 1 (dummyAdversary_polyBounded n _ _)
  have hdummy : ∃ ε : Polynomial ℕ → ℕ → ℝ≥0,
      (∀ pZ, Negligible (ε pZ)) ∧ EmulatesDummyWithin π φ pD ε := by
    choose ε hε hε_adv using hadv
    exact ⟨ε, hε, S_D, hSD, fun C Z pZ hZ κ z => hε_adv pZ C Z hZ κ z⟩
  rcases hdummy with ⟨ε, hε, hD⟩
  refine (EmulatesDummyWithin.composeDyn hρ hπ hφ hD).emulatesWithin.emulates fun pA pZ => ?_
  have hneg : Negligible (ε (dynSessionHopPoly (absorbPoly pZ pA) pρ pπ pφ pD)) :=
    hε (dynSessionHopPoly (absorbPoly pZ pA) pρ pπ pφ pD)
  have hpoly : PolynomiallyBounded
      (fun κ => (absorbPoly (absorbPoly pZ pA) pρ).eval κ + 1) :=
    polynomiallyBounded_eval_add_one (absorbPoly (absorbPoly pZ pA) pρ)
  simpa only [nsmul_eq_mul] using hneg.polynomiallyBounded_mul hpoly

/-- Dynamic-SID composition step for `Realizes`, replacing dynamically created instances of `F` in
`composeDyn ρ F.toProtocol` with a protocol `π` realizing `F`.
Adapts Corollary 23 of [Canetti2020] (JACM p. 28:59; ePrint 2000/067, p. 62) to static corruptions,
depth-1 dynamic sessions, and this library's call-bounded statistical model; not the full PPT ITM
corollary (`#6043` remains open). -/
theorem Realizes.composeDyn {SID : Type} [DecidableEq SID] {n : ℕ}
    {In Out NetQ NetR SubIn SubOut NQ NR BackQ BackR : Type}
    {ρ : DynHybridProtocol SID n In Out NetQ NetR SubIn SubOut}
    {π : Protocol n SubIn SubOut NQ NR}
    {F : IdealFunctionality n SubIn SubOut BackQ BackR}
    {pρ pπ pF : Polynomial ℕ}
    (hρ : ρ.PolyBounded pρ) (hπ : π.PolyBounded pπ) (hF : F.toProtocol.PolyBounded pF)
    (h : Realizes π F) :
    Emulates (UC.composeDyn ρ π) (UC.composeDyn ρ F.toProtocol) :=
  Emulates.composeDyn hρ hπ hF h

/-- Dynamic-SID transitive hybrid replacement step for `Realizes`, this library's own call-bounded
emulation relation against an ideal functionality: if `π` realizes `F` and
`composeDyn ρ F.toProtocol` realizes `G`, then `composeDyn ρ π` realizes `G`.
Adapts Corollary 24 of [Canetti2020] (JACM p. 28:59; ePrint 2000/067, p. 62) to static corruptions,
depth-1 dynamic sessions, and this library's call-bounded statistical model; not the full PPT ITM
corollary (`#6043` remains open). -/
theorem Realizes.composeDyn_trans {SID : Type} [DecidableEq SID] {n : ℕ}
    {In Out NetQ NetR SubIn SubOut NQ NR BackQ BackR GQ GR : Type}
    {ρ : DynHybridProtocol SID n In Out NetQ NetR SubIn SubOut}
    {π : Protocol n SubIn SubOut NQ NR}
    {F : IdealFunctionality n SubIn SubOut BackQ BackR}
    {G : IdealFunctionality n In Out GQ GR}
    {pρ pπ pF : Polynomial ℕ}
    (hρ : ρ.PolyBounded pρ) (hπ : π.PolyBounded pπ) (hF : F.toProtocol.PolyBounded pF)
    (hπF : Realizes π F) (hρG : Realizes (UC.composeDyn ρ F.toProtocol) G) :
    Realizes (UC.composeDyn ρ π) G :=
  Emulates.trans (Realizes.composeDyn hρ hπ hF hπF) hρG

end Composition

end Cslib.Crypto.Protocols.UC
