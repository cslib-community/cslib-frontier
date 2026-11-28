/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.TreeSignature.Reduction
import CslibFrontier.Crypto.Computational.TreeSignature.Handlers
import CslibFrontier.Foundations.Data.List.GetD
import CslibFrontier.Foundations.Data.List.Lookup
import CslibFrontier.Foundations.Data.List.SortedAssoc
import CslibFrontier.Languages.Probabilistic.Iteration.Chain
import CslibFrontier.Languages.Probabilistic.Oracle.InterpNorm
import CslibFrontier.Languages.Probabilistic.Oracle.QueryBoundedSimulation
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Bool
import CslibFrontier.Tactic.SuppCases
import Mathlib.Data.List.GetD

/-!
# Lazy-tree to indexed-forgery reduction for stateless tree signatures

Proves the second post-PRF game hop toward [BonehShoup2023], Section 14.6.3, Theorem 14.6, p. 600
(binary case `q = 2`): pre-sampling `dyadicSize (slotBound n)` node key pairs and planting the
indexed challenge verification key at a uniform dyadic slot `target` simulates `lazyTreeGame`
exactly whenever `Q * depth n ≤ slotBound n` and every edge signature fits in `sigCap n` bits. Any
valid tree forgery on a fresh `n`-bit message yields an indexed forgery at the deepest visited node
along the forged path (`extractForgery`).

## Main results

* `Cslib.Crypto.TreeSignature.succProbability_lazyTreeGame_le`: plug-and-pray bound reducing
  `lazyTreeGame` to `S.indexedEufCmaGame` via `indexedForger`.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023],
  Section 14.6.3, Theorem 14.6, p. 600.
-/

public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM
open scoped NNReal ENNReal

namespace TreeSignature

/-- Full log entry `(path, slotIdx, u, msg)` recorded on every fresh edge signature in the
pre-sampled tree experiment. -/
private abbrev AllSignedLog := List (List Bool × ℕ × ℕ × List Bool)

/-- Inner state of the pre-sampled tree handler: `(visited, edges, allSigned)`. -/
private abbrev PresampledInner := NodeSlotCache × EdgeSigCache × AllSignedLog

/-- State of the pre-sampled tree signing handler. -/
private abbrev PresampledState := TreeState PresampledInner

private def initPresampledState : PresampledState :=
  (([([], 0)], [], []), ⟨[], [], false⟩)

/-- Extract the indexed signing oracle log `(u, msg)` at slot `target` from `allSigned`. -/
private def signedLogOf (target : ℕ) (allSigned : AllSignedLog) : List (ℕ × List Bool) :=
  (allSigned.filter fun e => e.2.1 == target).map fun e => (e.2.2.1, e.2.2.2)

/-- Pure counterpart of `visitNodeM`. -/
private def visitNodePure (cap : ℕ) (path : List Bool) (visited : NodeSlotCache) :
    ℕ × NodeSlotCache :=
  match visited.lookup path with
  | some idx => (idx, visited)
  | none => let idx := min visited.length cap; (idx, (path, idx) :: visited)

private theorem run_interpret_visitNodeM {External : Type}
    (oracle : Unit × List Bool → StateT External PMF (List Bool))
    (cap : ℕ) (path : List Bool) (visited : NodeSlotCache) (ext : External) :
    (OracleComp.interpret
      (OracleComp.sumHandler (fun j => StateT.lift (ProbComp.unifOracle j)) oracle)
      (visitNodeM cap path visited)).run ext =
      PMF.pure (visitNodePure cap path visited, ext) := by
  simp only [visitNodeM, visitNodePure, memoize]
  cases visited.lookup path <;>
    simp only [pure_bind, OracleComp.run_interpret_pure, Probability.PMF.monad_pure_eq_pure]

private theorem filter_headD_of_mem_unique (visited : NodeSlotCache) {p : List Bool}
    {idx : ℕ} (hmem : (p, idx) ∈ visited)
    (huniq : ∀ e₁ ∈ visited, ∀ e₂ ∈ visited, e₁.2 = e₂.2 → e₁ = e₂) :
    ((visited.filter fun e => e.2 == idx).headD ([], 0)).1 = p := by
  have hin : (p, idx) ∈ visited.filter fun e => e.2 == idx :=
    List.mem_filter.mpr ⟨hmem, beq_self_eq_true idx⟩
  cases hflt : visited.filter fun e => e.2 == idx with
  | nil => simp [hflt] at hin
  | cons hd tl =>
    obtain ⟨hhd_vis, hhd_eq⟩ := List.mem_filter.mp (hflt ▸ List.mem_cons_self)
    rw [List.headD_cons, huniq hd hhd_vis (p, idx) hmem (beq_iff_eq.mp hhd_eq)]

private theorem slot_bound_lt_dyadicSize {Q d B : ℕ} (hd : 1 ≤ d) (hB : Q * d ≤ B) :
    1 + Q * (d - 1) < dyadicSize B := by
  rcases Nat.eq_zero_or_pos Q with rfl | hQ
  · have := two_le_dyadicSize B; omega
  · have := Nat.mul_sub_left_distrib Q d 1
    have : Q ≤ Q * d := Nat.le_mul_of_pos_right Q hd
    have := lt_dyadicSize B
    omega

private theorem fst_getD_splice (front back : List (List Bool × List Bool))
    (x : List Bool × List Bool) (idx : ℕ) :
    ((front ++ (x.1, []) :: back).getD idx ([], [])).1 =
      ((front ++ x :: back).getD idx ([], [])).1 := by
  by_cases h : idx = front.length
  · subst h; simp only [List.getD_append_cons_length]
  · rw [List.getD_append_cons_of_ne front back (x.1, []) x ([], []) h]

/-- Local edge-signing step on pre-sampled `keys`, truncating fresh signatures to `sigCap` bits and
recording `(path, idx, u, msg)` in `allSigned`. -/
private noncomputable def localSignEdge (S : IndexedSignatureScheme)
    (keys : List (List Bool × List Bool)) (sigCap : ℕ) (path : List Bool) (idx u : ℕ)
    (msg : List Bool) (ea : EdgeSigCache × AllSignedLog) :
    PMF (List Bool × (EdgeSigCache × AllSignedLog)) :=
  match ea.1.lookup (path, u) with
  | some σ => PMF.pure (σ, ea)
  | none =>
    (ProbComp.eval (S.sign (keys.getD idx ([], [])).2 u msg)).map fun raw =>
      let σ := raw.take sigCap
      (σ, (((path, u), σ) :: ea.1, (path, idx, u, msg) :: ea.2))

private theorem mem_support_localSignEdge {S : IndexedSignatureScheme}
    {keys : List (List Bool × List Bool)} {sigCap : ℕ} {path : List Bool} {idx u : ℕ}
    {msg : List Bool} {edges : EdgeSigCache} {allSigned : AllSignedLog}
    {σ : List Bool} {edges' : EdgeSigCache} {allSigned' : AllSignedLog}
    (hm : (σ, edges', allSigned') ∈
      (localSignEdge S keys sigCap path idx u msg (edges, allSigned)).support) :
    (edges' = edges ∧ allSigned' = allSigned) ∨
      (edges' = ((path, u), σ) :: edges ∧ allSigned' = (path, idx, u, msg) :: allSigned) := by
  simp only [localSignEdge] at hm
  cases hlk : edges.lookup (path, u) with
  | some σ₀ => rw [hlk] at hm; supp_cases hm; exact Or.inl ⟨rfl, rfl⟩
  | none => rw [hlk] at hm; supp_cases hm with ⟨raw, -, rfl, rfl, rfl⟩; exact Or.inr ⟨rfl, rfl⟩

private abbrev LocalCertState :=
  (List Bool × ℕ × List (List Bool × List Bool)) × PresampledInner

private noncomputable def localCertifyStep (S : IndexedSignatureScheme)
    (keys : List (List Bool × List Bool)) (sigCap : ℕ) (leaf : List Bool)
    (state : LocalCertState) : PMF LocalCertState :=
  let ((node, idx, certs), (visited, edges, allSigned)) := state
  let bit := leaf.getD node.length false
  let childPath := node ++ [bit]
  let (childIdx, visited') := visitNodePure keys.length childPath visited
  let childPk := (keys.getD childIdx ([], [])).1
  (localSignEdge S keys sigCap node idx bit.toNat childPk (edges, allSigned)).map
    fun (σ, (edges', allSigned')) =>
      ((childPath, childIdx, certs ++ [(childPk, σ)]), (visited', edges', allSigned'))

private noncomputable def localCertify (S : IndexedSignatureScheme) (depth : ℕ → ℕ)
    (keys : List (List Bool × List Bool)) (sigCap n : ℕ) (leaf : List Bool)
    (caches : PresampledInner) : PMF LocalCertState :=
  Nat.iterate (fun d => d.bind (localCertifyStep S keys sigCap leaf)) (depth n - 1)
    (PMF.pure (([], 0, []), caches))

private noncomputable def localSignBody (S : IndexedSignatureScheme) (depth : ℕ → ℕ)
    (keys : List (List Bool × List Bool)) (sigCap n : ℕ) : TreeBody PresampledInner :=
  fun leaf msg caches =>
    (localCertify S depth keys sigCap n leaf caches).bind fun
      ((node, idx, certs), (visited', edges', allSigned')) =>
        (localSignEdge S keys sigCap node idx (leaf.getLastD false).toNat msg
          (edges', allSigned')).map fun (σ, (edges'', allSigned'')) =>
            (encodeSignature leaf certs σ, (visited', edges'', allSigned''))

private noncomputable def localTreeHandler (S : IndexedSignatureScheme) (depth : ℕ → ℕ)
    (keys : List (List Bool × List Bool)) (sigCap n : ℕ) :
    Unit × List Bool → StateT PresampledState PMF (List Bool) :=
  guardedTreeHandler depth n (localSignBody S depth keys sigCap n)

/-- Pre-sampled tree experiment: sample `dyadicSize (slotBound n)` key pairs of `S`, then run
`adversary` against `localTreeHandler`. -/
private noncomputable def presampledExp (S : IndexedSignatureScheme)
    (depth slotBound sigCap : ℕ → ℕ) (adversary : Forger) (n : ℕ) :
    PMF (List (List Bool × List Bool) × (List Bool × List Bool) × PresampledState) := do
  let keys ← ProbComp.eval (OracleComp.replicate (dyadicSize (slotBound n)) (S.keyGen n))
  let pk := encPair encUnary encBits (n, (keys.getD 0 ([], [])).1)
  ((OracleComp.interpret
    (OracleComp.sumHandler (fun j => StateT.lift (ProbComp.unifOracle j))
      (localTreeHandler S depth keys (sigCap n) n))
    (adversary n pk)).run initPresampledState).map fun (msig, st) => (keys, msig, st)

/-- Whether `indexedForgerAt` at `target` wins on a pre-sampled outcome. -/
private def plantedWin (S : IndexedSignatureScheme) (depth : ℕ → ℕ) (n target : ℕ)
    (out : List (List Bool × List Bool) × (List Bool × List Bool) × PresampledState) : Bool :=
  let (keys, msig, ((visited, _, allSigned), _)) := out
  let cand := extractForgery (depth n) target visited msig.1 msig.2
  !(signedLogOf target allSigned).contains (cand.1, cand.2.1) &&
    S.verify (keys.getD target ([], [])).1 cand.1 cand.2.1 cand.2.2

/-- Whether `adversary` wins `lazyTreeGame` on a pre-sampled outcome. -/
private def treeWinOfPresampled (S : IndexedSignatureScheme) (depth : ℕ → ℕ) (n : ℕ)
    (out : List (List Bool × List Bool) × (List Bool × List Bool) × PresampledState) : Bool :=
  let (keys, msig, (_, log)) := out
  let pk := encPair encUnary encBits (n, (keys.getD 0 ([], [])).1)
  (msig.1.length == n) && !log.queried.contains msig.1 && verify S depth pk msig.1 msig.2

/-! ### Simulation of `plantedTreeHandler` + `indexedSigningOracle` by `localTreeHandler` -/

/-- Uniqueness and edge-log invariant for `localTreeHandler` with slot capacity `K`. -/
private structure SlotEdgeInv (K : ℕ) (st : PresampledInner) : Prop where
  root_mem : ([], 0) ∈ st.1
  slots_lt : ∀ e ∈ st.1, e.2 < K → e.2 < st.1.length
  slots_unique : ∀ e₁ ∈ st.1, ∀ e₂ ∈ st.1, e₁.2 < K → e₁.2 = e₂.2 → e₁ = e₂
  allSigned_ok : ∀ p idx u m, (p, idx, u, m) ∈ st.2.2 →
    (p, idx) ∈ st.1 ∧ st.2.1.lookup (p, u) ≠ none

/-- Output invariant of `visitNodePure` parameterized by a path predicate `P`. -/
private structure VisitNodePureSpec (P : List Bool → Prop) (K : ℕ) (path : List Bool)
    (visited : NodeSlotCache) (idx : ℕ) (visited' : NodeSlotCache) : Prop where
  mem_new : (path, idx) ∈ visited'
  mono : ∀ e ∈ visited, e ∈ visited'
  length_le : visited'.length ≤ visited.length + 1
  slots_ok : ∀ e ∈ visited', P e.1 ∧ (e.2 < K → e.2 < visited'.length)
  unique : ∀ e₁ ∈ visited', ∀ e₂ ∈ visited', e₁.2 < K → e₁.2 = e₂.2 → e₁ = e₂
  mem_or_new : ∀ e ∈ visited', e ∈ visited ∨ e = (path, min visited.length K)

private theorem visitNodePure_inv {P : List Bool → Prop} {K : ℕ} {visited : NodeSlotCache}
    (path : List Bool) (hp : P path)
    (hlt : ∀ e ∈ visited, P e.1 ∧ (e.2 < K → e.2 < visited.length))
    (huniq : ∀ e₁ ∈ visited, ∀ e₂ ∈ visited, e₁.2 < K → e₁.2 = e₂.2 → e₁ = e₂) :
    let vp := visitNodePure K path visited
    VisitNodePureSpec P K path visited vp.1 vp.2 := by
  simp only [visitNodePure]
  cases hlk : visited.lookup path with
  | some idx =>
    exact ⟨List.mem_of_lookup_eq_some hlk, fun _ h => h, Nat.le_succ _, hlt, huniq,
      fun _ h => Or.inl h⟩
  | none =>
    refine ⟨List.mem_cons_self, fun _ h => List.mem_cons_of_mem _ h, le_rfl, fun e he => ?_,
      fun e₁ he₁ e₂ he₂ he₁K heq => ?_, fun _ h => (List.mem_cons.mp h).symm⟩
    · rcases List.mem_cons.mp he with rfl | ht
      · exact ⟨hp, fun _ => Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩
      · exact ⟨(hlt e ht).1, fun hK => Nat.lt_succ_of_lt ((hlt e ht).2 hK)⟩
    · rcases List.mem_cons.mp he₁ with rfl | ht₁ <;> rcases List.mem_cons.mp he₂ with rfl | ht₂
      · rfl
      · have := (hlt e₂ ht₂).2 (heq ▸ he₁K); dsimp only at he₁K heq; omega
      · have := (hlt e₁ ht₁).2 he₁K; dsimp only at heq; omega
      · exact huniq e₁ ht₁ e₂ ht₂ he₁K heq

private theorem localSignEdge_planted_spec (S : IndexedSignatureScheme)
    {n sigCap : ℕ} (hcap : 2 ≤ S.capacity n)
    {front back : List (List Bool × List Bool)} {x : List Bool × List Bool}
    {visited : NodeSlotCache} {edges : EdgeSigCache} {allSigned : AllSignedLog}
    (hslotLt : front.length < (front ++ x :: back).length)
    (huniq : ∀ e₁ ∈ visited, ∀ e₂ ∈ visited,
      e₁.2 < (front ++ x :: back).length → e₁.2 = e₂.2 → e₁ = e₂)
    (hall : ∀ p₀ idx₀ u₀ m₀, (p₀, idx₀, u₀, m₀) ∈ allSigned →
      (p₀, idx₀) ∈ visited ∧ edges.lookup (p₀, u₀) ≠ none)
    {path : List Bool} {idx u : ℕ} (hvis : (path, idx) ∈ visited) (hu : u ≤ 1)
    (msg : List Bool) :
    PMF.RepInv (localSignEdge S (front ++ x :: back) sigCap path idx u msg (edges, allSigned))
      ((OracleComp.interpret
        (OracleComp.sumHandler (fun j => StateT.lift (ProbComp.unifOracle j))
          (fun q s => ProbComp.eval (S.indexedSigningOracle n x.2 q s)))
        (signEdgeM S (front ++ (x.1, []) :: back) front.length sigCap path idx u msg edges)).run
        (signedLogOf front.length allSigned))
      (fun (σ, (edges', allSigned')) => ((σ, edges'), signedLogOf front.length allSigned'))
      (fun (_, (edges', allSigned')) =>
        ∀ p₀ idx₀ u₀ m₀, (p₀, idx₀, u₀, m₀) ∈ allSigned' →
          (p₀, idx₀) ∈ visited ∧ edges'.lookup (p₀, u₀) ≠ none) := by
  refine ⟨?_, fun ⟨σ, edges', allSigned'⟩ hm p₀ idx₀ u₀ m₀ hm_all => ?_⟩
  · simp only [localSignEdge, signEdgeM, memoize]
    cases hes : edges.lookup (path, u) with
    | some σ₀ => simp only [OracleComp.run_interpret_pure, pmf_norm]
    | none =>
      simp only [signEdgeRaw]
      by_cases hidx : idx = front.length
      · subst hidx
        have hnotMem : u ∉ (signedLogOf front.length allSigned).map Prod.fst := by
          simp only [signedLogOf, List.mem_map, List.mem_filter, beq_iff_eq]
          rintro ⟨_, ⟨⟨p₀, idx₀, u₀, m₀⟩, ⟨hm_all, rfl⟩, rfl⟩, rfl⟩
          obtain ⟨hp₀_vis, hp₀_lk⟩ := hall p₀ front.length u₀ m₀ hm_all
          exact hp₀_lk (congrArg (fun p => edges.lookup (p, u₀))
            (Prod.mk.inj (huniq _ hp₀_vis _ hvis hslotLt rfl)).1 |>.trans hes)
        have huLt : u < S.capacity n := by omega
        have hlog : signedLogOf front.length ((path, front.length, u, msg) :: allSigned) =
            (u, msg) :: signedLogOf front.length allSigned := by simp [signedLogOf]
        simp only [↓reduceIte, List.getD_append_cons_length, OracleComp.run_interpret_bind,
          OracleComp.interpret_map, ProbOracleComp.interpret_query, OracleComp.run_interpret_pure,
          StateT.run_map, IndexedSignatureScheme.indexedSigningOracle,
          IndexedSignatureScheme.requestDecoder.decode_enc, hlog, pmf_norm]
        dsimp only [StateT.run]
        simp only [huLt, hnotMem, not_false_eq_true, and_self, ↓reduceIte, pmf_norm, PMF.map]
      · rw [List.getD_append_cons_of_ne front back (x.1, []) x ([], []) hidx]
        simp only [hidx, ↓reduceIte, interp_norm, signedLogOf, List.filter_cons,
          beq_false_of_ne hidx, Bool.false_eq_true, pmf_norm, PMF.map]
  · rcases mem_support_localSignEdge hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hall p₀ idx₀ u₀ m₀ hm_all
    · rcases List.mem_cons.mp hm_all with hhead | ht
      · cases hhead
        exact ⟨hvis, by simp⟩
      · obtain ⟨hpv, hpl⟩ := hall p₀ idx₀ u₀ m₀ ht
        refine ⟨hpv, ?_⟩
        rw [List.lookup_cons]; cases (p₀, u₀) == (path, u) <;> [exact hpl; rintro ⟨⟩]

private theorem localCertify_planted_spec (S : IndexedSignatureScheme) (depth : ℕ → ℕ)
    {n sigCap : ℕ} (hcap : 2 ≤ S.capacity n)
    {front back : List (List Bool × List Bool)} {x : List Bool × List Bool}
    (leaf : List Bool) {caches : PresampledInner}
    (hinv : SlotEdgeInv (front ++ x :: back).length caches) :
    let keys := front ++ x :: back
    let keys' := front ++ (x.1, []) :: back
    PMF.RepInv (localCertify S depth keys sigCap n leaf caches)
      ((OracleComp.interpret
        (OracleComp.sumHandler (fun j => StateT.lift (ProbComp.unifOracle j))
          (fun q s => ProbComp.eval (S.indexedSigningOracle n x.2 q s)))
        (certifyPlanted S depth keys' front.length sigCap n leaf (caches.1, caches.2.1))).run
        (signedLogOf front.length caches.2.2))
      (fun (c, (v, e, a)) => ((c, (v, e)), signedLogOf front.length a))
      (fun (c, (v, e, a)) => (c.1, c.2.1) ∈ v ∧ SlotEdgeInv keys.length (v, e, a)) := by
  obtain ⟨visited, edges, allSigned⟩ := caches
  intro keys keys'
  have hslotLt : front.length < keys.length := by simp [keys]
  have hlenEq : keys'.length = keys.length := by simp [keys, keys']
  dsimp only [localCertify, certifyPlanted]
  rw [OracleComp.run_interpret_iterate_pmf]
  refine PMF.RepInv.iterate
    (fun (_ : ℕ) (x : LocalCertState) => (x.1.1, x.1.2.1) ∈ x.2.1 ∧ SlotEdgeInv keys.length x.2)
    rfl ⟨hinv.root_mem, hinv⟩
    fun _ _ ⟨⟨node, idx, certs⟩, v, e, a⟩ ⟨hnode_v, hinv_v⟩ => ?_
  set bit := leaf.getD node.length false
  set childPath := node ++ [bit]
  have hvp := visitNodePure_inv (P := fun _ => True) childPath trivial
    (fun ent he => ⟨trivial, hinv_v.slots_lt ent he⟩) hinv_v.slots_unique
  set vp := visitNodePure keys.length childPath v
  dsimp only [localCertifyStep, certifyStepPlanted]
  simp only [hlenEq, OracleComp.run_interpret_bind,
    OracleComp.run_interpret_pure, run_interpret_visitNodeM, pmf_norm]
  rw [fst_getD_splice front back x vp.1]
  exact (localSignEdge_planted_spec S (sigCap := sigCap) hcap hslotLt hvp.unique
    (fun p₀ i₀ u₀ m₀ hm =>
      ⟨hvp.mono _ (hinv_v.allSigned_ok _ _ _ _ hm).1, (hinv_v.allSigned_ok _ _ _ _ hm).2⟩)
    (hvp.mono _ hnode_v) (Bool.toNat_le bit) (keys.getD vp.1 ([], [])).1).map
    fun _ _ hedg => ⟨rfl, hvp.mem_new,
      ⟨hvp.mono _ hinv_v.root_mem, fun ent he => (hvp.slots_ok ent he).2, hvp.unique, hedg⟩⟩

private theorem localTreeHandler_planted_step (S : IndexedSignatureScheme) (depth : ℕ → ℕ)
    {n sigCap : ℕ} (hcap : 2 ≤ S.capacity n)
    {front back : List (List Bool × List Bool)} {x : List Bool × List Bool}
    (req : Unit × List Bool) (st : PresampledState)
    (hinv : SlotEdgeInv (front ++ x :: back).length st.1) :
    PMF.RepInv (localTreeHandler S depth (front ++ x :: back) sigCap n req st)
      (((OracleComp.interpret
        (OracleComp.sumHandler (fun j => StateT.lift (ProbComp.unifOracle j))
          (fun q s => ProbComp.eval (S.indexedSigningOracle n x.2 q s)))
        (plantedTreeHandler S depth (front ++ (x.1, []) :: back) front.length sigCap n req
          ((st.1.1, st.1.2.1), st.2))).run (signedLogOf front.length st.1.2.2)).map
        fun ((ans, ps'), sg') => (ans, ps', sg'))
      (fun (ans, (v, e, a), log) => (ans, ((v, e), log), signedLogOf front.length a))
      (fun (_, st') => SlotEdgeInv (front ++ x :: back).length st'.1) := by
  obtain ⟨⟨visited, edges, allSigned⟩, ⟨queried, seen, bad⟩⟩ := st
  simp only [localTreeHandler, guardedTreeHandler, plantedTreeHandler]
  split_ifs with hmsg hbad
  · simp only [OracleComp.run_interpret_pure, pmf_norm]
    exact .pure rfl hinv
  · simp only [OracleComp.run_interpret_bind, ProbOracleComp.run_interpret_sample,
      BitString.eval_sampleList, pmf_norm]
    refine (PMF.RepInv.of_eq (PMF.map_id (BitString.uniformList (depth n)))).bind fun leaf _ _ => ?_
    dsimp only [id, localSignBody]
    split_ifs
    · simp only [OracleComp.run_interpret_pure, pmf_norm]
      exact .pure rfl hinv
    · simp only [OracleComp.run_interpret_bind, OracleComp.run_interpret_pure, pmf_norm]
      exact (localCertify_planted_spec S depth hcap leaf hinv).bind
        fun ⟨⟨node, idx, certs⟩, v', e', a'⟩ _ ⟨hnode_v', hinv'⟩ =>
          (localSignEdge_planted_spec S hcap (by simp) hinv'.slots_unique hinv'.allSigned_ok
            hnode_v' (Bool.toNat_le _) req.2).map
            fun _ _ hedg => ⟨rfl, ⟨hinv'.root_mem, hinv'.slots_lt, hinv'.slots_unique, hedg⟩⟩
  · simp only [OracleComp.run_interpret_pure, pmf_norm]
    exact .pure rfl hinv

/-- The index of an extracted forgery is a bit, so it lies below every capacity of at least `2`. -/
private theorem extractForgery_fst_lt (d target : ℕ) (visited : NodeSlotCache)
    (msg sig : List Bool) {cap : ℕ} (hcap : 2 ≤ cap) :
    (extractForgery d target visited msg sig).1 < cap := by
  unfold extractForgery
  rcases signatureDecoder.decode sig with ⟨leaf, certs, last⟩
  dsimp only
  split_ifs <;> exact (Bool.toNat_le _).trans_lt (by omega)

private theorem map_plantedWin_presampledExp (S : IndexedSignatureScheme)
    (depth slotBound sigCap : ℕ → ℕ) {n : ℕ} (hcap : 2 ≤ S.capacity n)
    (adversary : Forger) {target : ℕ} (htarget : target < dyadicSize (slotBound n)) :
    (presampledExp S depth slotBound sigCap adversary n).map (plantedWin S depth n target) =
      ProbComp.eval
        (S.indexedEufCmaGame (indexedForgerAt S depth slotBound sigCap adversary target) n) := by
  set K := dyadicSize (slotBound n) with hK_def
  have hmin : min target (K - 1) = target := Nat.min_eq_left (by omega)
  have hsplit : K = target + ((K - target - 1) + 1) := by omega
  simp only [presampledExp, IndexedSignatureScheme.indexedEufCmaGame, indexedForgerAt,
    plantNodeKeys, ← hK_def, hmin]
  conv_lhs => rw [hsplit, ← ProbComp.eval_replicate_splice]
  simp only [ProbOracleComp.eval_run_interpret, interp_norm, pmf_norm]
  refine PMF.bind_congr_on_support _ _ _ fun x _ =>
    PMF.bind_congr_on_support _ _ _ fun front hfront =>
    PMF.bind_congr_on_support _ _ _ fun back _ => ?_
  obtain rfl : front.length = target := ((ProbComp.mem_support_replicate_iff _ _ _).mp hfront).1
  set keys := front ++ x :: back
  set keys' := front ++ (x.1, []) :: back
  set pk := encPair encUnary encBits (n, (keys.getD 0 ([], [])).1)
  have hinitInv : SlotEdgeInv keys.length initPresampledState.1 :=
    ⟨List.mem_singleton.mpr rfl,
      fun e he _ => by rw [List.mem_singleton.mp he]; simp [initPresampledState],
      fun e₁ he₁ e₂ he₂ _ _ => by rw [List.mem_singleton.mp he₁, List.mem_singleton.mp he₂],
      fun _ _ _ _ h => by cases h⟩
  have hflat := ProbOracleComp.run_interpret_run_interpret
    (plantedTreeHandler S depth keys' front.length (sigCap n) n)
    (fun q s => ProbComp.eval (S.indexedSigningOracle n x.2 q s))
    (adversary n pk) initPlantedState []
  have hsim := ProbOracleComp.run_interpret_map_state_of_invariant
    (localTreeHandler S depth keys (sigCap n) n)
    (fun q (st : PlantedState × List (ℕ × List Bool)) =>
      ((OracleComp.interpret
        (OracleComp.sumHandler (fun j => StateT.lift (ProbComp.unifOracle j))
          (fun q s => ProbComp.eval (S.indexedSigningOracle n x.2 q s)))
        (plantedTreeHandler S depth keys' front.length (sigCap n) n q st.1)).run st.2).map
        fun ((a, b), c) => (a, b, c))
    (fun ((v, e, a), log) => (((v, e), log), signedLogOf front.length a)) _
    (fun q st hst ans st' hm =>
      (localTreeHandler_planted_step S depth hcap q st hst).support_inv (ans, st') hm)
    (fun q st hst => (localTreeHandler_planted_step S depth hcap q st hst).map_eq)
    (adversary n pk) initPresampledState hinitInv
  rw [fst_getD_splice front back x 0]
  have hwin := congrArg (PMF.map fun ((msig, ps), sg) =>
    let cand := extractForgery (depth n) front.length ps.1.1 msig.1 msig.2
    decide (cand.1 < S.capacity n) && !sg.contains (cand.1, cand.2.1) &&
      S.verify x.1 cand.1 cand.2.1 cand.2.2)
    ((congrArg (PMF.map fun (a, b, c) => ((a, b), c)) hsim).trans hflat.symm)
  simpa only [pmf_norm, PMF.map, plantedWin, keys, List.getD_append_cons_length,
    extractForgery_fst_lt _ _ _ _ _ hcap, decide_true, Bool.true_and] using hwin

/-! ### Equivalence between `lazyTreeGame` and `presampledExp` -/

private abbrev JointKeysInner := List (List Bool × List Bool) × PresampledInner
private abbrev JointKeysState := TreeState JointKeysInner
private abbrev JointKeysCertState := List (List Bool × List Bool) × LocalCertState

private def nodesOf (usedKeys : List (List Bool × List Bool)) (visited : NodeSlotCache) :
    NodeKeyCache :=
  visited.map fun e => (e.1, usedKeys.getD e.2 ([], []))

private noncomputable def jointVisitKey (S : IndexedSignatureScheme) (n : ℕ) (path : List Bool)
    (uv : List (List Bool × List Bool) × NodeSlotCache) :
    PMF (ℕ × (List (List Bool × List Bool) × NodeSlotCache)) :=
  match uv.2.lookup path with
  | some idx => PMF.pure (idx, uv)
  | none =>
    (ProbComp.eval (S.keyGen n)).map fun child =>
      (uv.2.length, (uv.1 ++ [child], (path, uv.2.length) :: uv.2))

private noncomputable def jointKeysCertifyStep (S : IndexedSignatureScheme) (sigCap n : ℕ)
    (leaf : List Bool) (st : JointKeysCertState) : PMF JointKeysCertState := do
  let (usedKeys, ((node, idx, certs), (visited, edges, allSigned))) := st
  let bit := leaf.getD node.length false
  let childPath := node ++ [bit]
  let (childIdx, (usedKeys', visited')) ← jointVisitKey S n childPath (usedKeys, visited)
  let childPk := (usedKeys'.getD childIdx ([], [])).1
  (localSignEdge S usedKeys' sigCap node idx bit.toNat childPk (edges, allSigned)).map
    fun (σ, (edges', allSigned')) =>
      (usedKeys', ((childPath, childIdx, certs ++ [(childPk, σ)]), (visited', edges', allSigned')))

private noncomputable def jointKeysCertify (S : IndexedSignatureScheme) (depth : ℕ → ℕ)
    (sigCap n : ℕ) (leaf : List Bool) (init : JointKeysInner) : PMF JointKeysCertState :=
  Nat.iterate (fun d => d.bind (jointKeysCertifyStep S sigCap n leaf)) (depth n - 1)
    (PMF.pure (init.1, (([], 0, []), init.2)))

private noncomputable def jointKeysBody (S : IndexedSignatureScheme) (depth : ℕ → ℕ)
    (sigCap n : ℕ) : TreeBody JointKeysInner :=
  fun leaf msg st =>
    (jointKeysCertify S depth sigCap n leaf st).bind fun
      (uk', ((node, idx, certs), (vis', edg', all'))) =>
        (localSignEdge S uk' sigCap node idx (leaf.getLastD false).toNat msg (edg', all')).map
          fun (σ, (edg'', all'')) => (encodeSignature leaf certs σ, (uk', (vis', edg'', all'')))

private noncomputable def jointKeysHandler (S : IndexedSignatureScheme) (depth : ℕ → ℕ)
    (sigCap n : ℕ) : Unit × List Bool → StateT JointKeysState PMF (List Bool) :=
  guardedTreeHandler depth n (jointKeysBody S depth sigCap n)

/-- Invariant linking dynamically grown `usedKeys` with `visited` slots for the lazy/eager hop. -/
private structure JointKeysInv (S : IndexedSignatureScheme) (n : ℕ) (root : List Bool × List Bool)
    (st : JointKeysInner) : Prop where
  len_eq : st.1.length = st.2.1.length
  root_lookup : st.2.1.lookup [] = some 0
  root_key : st.1.getD 0 ([], []) = root
  keys_supp : ∀ k ∈ st.1, k ∈ (ProbComp.eval (S.keyGen n)).support
  slots_lt : ∀ e ∈ st.2.1, e.2 < st.2.1.length

private theorem nodesOf_append_singleton (usedKeys : List (List Bool × List Bool))
    (visited : NodeSlotCache) (hvis : ∀ e ∈ visited, e.2 < usedKeys.length)
    (path : List Bool) (child : List Bool × List Bool) :
    nodesOf (usedKeys ++ [child]) ((path, usedKeys.length) :: visited) =
      (path, child) :: nodesOf usedKeys visited := by
  simp only [nodesOf, List.map_cons, List.getD_append_cons_length usedKeys [] child ([], [])]
  exact congrArg _ (List.map_congr_left fun e he => by rw [List.getD_append _ _ _ _ (hvis e he)])

private theorem jointVisitKey_support_inv (S : IndexedSignatureScheme) (n : ℕ)
    {uk : List (List Bool × List Bool)} {vis : NodeSlotCache}
    (hlen : uk.length = vis.length) (hpos : 0 < uk.length)
    (hvis : ∀ e ∈ vis, e.2 < vis.length) (path : List Bool)
    {idx : ℕ} {uk' : List (List Bool × List Bool)} {vis' : NodeSlotCache}
    (hm : (idx, (uk', vis')) ∈ (jointVisitKey S n path (uk, vis)).support) :
    uk'.length = vis'.length ∧ 0 < uk'.length ∧ (∀ e ∈ vis', e.2 < vis'.length) ∧
    idx < uk'.length ∧ uk.length ≤ uk'.length ∧ vis'.length ≤ vis.length + 1 ∧
    uk'.getD 0 ([], []) = uk.getD 0 ([], []) ∧
    (∀ k ∈ uk', k ∈ uk ∨ k ∈ (ProbComp.eval (S.keyGen n)).support) ∧
    (∀ j < uk.length, uk'.getD j ([], []) = uk.getD j ([], [])) ∧
    (∀ p₀ i₀, vis.lookup p₀ = some i₀ → vis'.lookup p₀ = some i₀) := by
  simp only [jointVisitKey] at hm
  cases hlk : vis.lookup path with
  | some i₀ =>
    rw [hlk] at hm; supp_cases hm
    exact ⟨hlen, hpos, hvis, hlen ▸ hvis _ (List.mem_of_lookup_eq_some hlk), le_rfl, Nat.le_succ _,
      rfl, fun _ h => Or.inl h, fun _ _ => rfl, fun _ _ h => h⟩
  | none =>
    rw [hlk] at hm; supp_cases hm with ⟨child, hchild, rfl, rfl, rfl⟩
    refine ⟨by simp [hlen], by simp, fun e he => ?_, by simp [hlen], by simp, by simp,
      List.getD_append _ _ _ _ hpos, fun k hk => ?_, fun j hj => List.getD_append _ _ _ _ hj,
      fun p₀ i₀ hp₀ => by
        rw [List.lookup_cons_of_ne fun h => by subst h; rw [hp₀] at hlk; cases hlk]; exact hp₀⟩
    · rcases List.mem_cons.mp he with rfl | ht
      · simp
      · exact Nat.lt_succ_of_lt (hvis e ht)
    · rcases List.mem_append.mp hk with hk | hk
      · exact Or.inl hk
      · exact Or.inr (List.mem_singleton.mp hk ▸ hchild)

private theorem localSignEdge_notrunc (S : IndexedSignatureScheme) {sigCap n : ℕ}
    (hsigCap : ∀ keys ∈ (ProbComp.eval (S.keyGen n)).support, ∀ u ≤ 1, ∀ msg,
      TreeMsg S n msg → ∀ σ ∈ (ProbComp.eval (S.sign keys.2 u msg)).support, σ.length ≤ sigCap)
    {usedKeys : List (List Bool × List Bool)}
    (hsupp : ∀ k ∈ usedKeys, k ∈ (ProbComp.eval (S.keyGen n)).support)
    {idx u : ℕ} (hidx : idx < usedKeys.length) (hu : u ≤ 1)
    {path msg : List Bool} (hmsg : TreeMsg S n msg)
    (edges : EdgeSigCache) (allSigned : AllSignedLog) :
    ((localSignEdge S usedKeys sigCap path idx u msg (edges, allSigned)).map
      fun (σ, (edges', _)) => (σ, edges')) =
      ProbComp.eval
        (memoize (fun _ => S.sign (usedKeys.getD idx ([], [])).2 u msg) (path, u) edges) := by
  simp only [localSignEdge, memoize]
  cases edges.lookup (path, u) with
  | some σ₀ => simp only [pmf_norm]
  | none =>
    simp only [bind_pure_comp, pmf_norm]
    refine PMF.map_congr_on_support _ _ _ fun raw hraw => ?_
    simp only [List.take_of_length_le
      (hsigCap _ (hsupp _ (List.getD_mem ([], []) hidx)) u hu msg hmsg raw hraw)]

private theorem jointKeysCertify_lazy_spec (S : IndexedSignatureScheme) (depth : ℕ → ℕ)
    {sigCap n : ℕ}
    (hsigCap : ∀ keys ∈ (ProbComp.eval (S.keyGen n)).support, ∀ u ≤ 1, ∀ msg,
      TreeMsg S n msg → ∀ σ ∈ (ProbComp.eval (S.sign keys.2 u msg)).support, σ.length ≤ sigCap)
    {root : List Bool × List Bool} {st : JointKeysInner}
    (hinv : JointKeysInv S n root st) (leaf : List Bool) :
    PMF.RepInv (jointKeysCertify S depth sigCap n leaf st)
      (ProbComp.eval (certifyLazy S depth n root leaf (nodesOf st.1 st.2.1, st.2.2.1)))
      (fun (uk', ((node, idx, certs), (vis', edg', _))) =>
        ((node, uk'.getD idx ([], []), certs), (nodesOf uk' vis', edg')))
      (fun (uk', ((_, idx, _), p)) => JointKeysInv S n root (uk', p) ∧ idx < uk'.length) := by
  obtain ⟨usedKeys, visited, edges, allSigned⟩ := st
  have hpos0 : 0 < usedKeys.length :=
    hinv.len_eq ▸ hinv.slots_lt _ (List.mem_of_lookup_eq_some hinv.root_lookup)
  dsimp only [jointKeysCertify, certifyLazy]; rw [ProbComp.eval_iterate]
  apply PMF.RepInv.iterate
    (fun (_ : ℕ) (x : JointKeysCertState) =>
      JointKeysInv S n root (x.1, x.2.2) ∧ x.2.1.2.1 < x.1.length)
    (by simp only [hinv.root_key]) ⟨hinv, hpos0⟩
  rintro _ _ ⟨uk, ⟨node, idx, certs⟩, vis, edg, all⟩ ⟨hinv_m, hidx⟩
  set bit := leaf.getD node.length false
  set childPath := node ++ [bit]
  have hpos : 0 < uk.length := Nat.lt_of_le_of_lt (Nat.zero_le _) hidx
  have hvis_rep : PMF.RepInv (jointVisitKey S n childPath (uk, vis))
      (ProbComp.eval (memoize (fun _ => S.keyGen n) childPath (nodesOf uk vis)))
      (fun (i, (uk', vis')) => (uk'.getD i ([], []), nodesOf uk' vis'))
      (fun (cIdx, (uk', vis')) =>
        JointKeysInv S n root (uk', vis', edg, all) ∧ cIdx < uk'.length ∧
        uk'.getD idx ([], []) = uk.getD idx ([], []) ∧ idx < uk'.length) := by
    refine ⟨?_, fun ⟨cIdx, uk', vis'⟩ hm => ?_⟩
    · simp only [jointVisitKey, memoize]
      have hlkM : (nodesOf uk vis).lookup childPath =
          (vis.lookup childPath).map (fun i => uk.getD i ([], [])) :=
        List.lookup_map_snd vis (fun i => uk.getD i ([], [])) childPath
      cases hlk : vis.lookup childPath with
      | some i => rw [hlk, Option.map_some] at hlkM; simp only [hlkM, pmf_norm]
      | none =>
        rw [hlk, Option.map_none] at hlkM
        simp only [hlkM, bind_pure_comp, pmf_norm]
        exact PMF.map_congr_on_support _ _ _ fun child _ => by
          simp only [← hinv_m.len_eq, List.getD_append_cons_length uk [] child ([], []),
            nodesOf_append_singleton uk vis (fun e he => hinv_m.len_eq ▸ hinv_m.slots_lt e he)
              childPath child]
    · obtain ⟨hlen', _, hvis', hcLt, hle, _, h0, h4, hkeep, hlk0⟩ :=
        jointVisitKey_support_inv S n hinv_m.len_eq hpos hinv_m.slots_lt childPath hm
      exact ⟨⟨hlen', hlk0 [] 0 hinv_m.root_lookup, h0.trans hinv_m.root_key,
        fun k hk => (h4 k hk).elim (hinv_m.keys_supp k) id, hvis'⟩,
        hcLt, hkeep idx hidx, hidx.trans_le hle⟩
  dsimp only [jointKeysCertifyStep, certifyStepLazy]
  simp only [pmf_norm]
  exact hvis_rep.bind fun ⟨cIdx, uk', vis'⟩ _ ⟨hinv', hcLt, hidx_eq, hidx'⟩ => by
    rw [← hidx_eq]
    exact (PMF.RepInv.of_eq (localSignEdge_notrunc S hsigCap hinv'.keys_supp hidx'
      (Bool.toNat_le bit)
      (Or.inr ⟨_, hinv'.keys_supp _ (List.getD_mem ([], []) hcLt), rfl⟩) edg all)).map
      fun _ _ _ => ⟨rfl,
        ⟨hinv'.len_eq, hinv'.root_lookup, hinv'.root_key, hinv'.keys_supp, hinv'.slots_lt⟩,
        hcLt⟩

private theorem jointKeysHandler_lazy_step (S : IndexedSignatureScheme) (depth : ℕ → ℕ)
    {sigCap n : ℕ}
    (hsigCap : ∀ keys ∈ (ProbComp.eval (S.keyGen n)).support, ∀ u ≤ 1, ∀ msg,
      TreeMsg S n msg → ∀ σ ∈ (ProbComp.eval (S.sign keys.2 u msg)).support, σ.length ≤ sigCap)
    {root : List Bool × List Bool} (req : Unit × List Bool) (st : JointKeysState)
    (hinv : JointKeysInv S n root st.1) :
    PMF.RepInv (jointKeysHandler S depth sigCap n req st)
      (ProbComp.eval (lazySignHandler S depth n root req
        ((nodesOf st.1.1 st.1.2.1, st.1.2.2.1), st.2)))
      (fun (ans, st') => (ans, (nodesOf st'.1.1 st'.1.2.1, st'.1.2.2.1), st'.2))
      (fun (_, st') => JointKeysInv S n root st'.1) := by
  obtain ⟨inner, ⟨queried, seen, bad⟩⟩ := st
  rw [eval_lazySignHandler_eq]
  refine guardedTreeHandler_map depth n (fun (uk, vis, edg, _) => (nodesOf uk vis, edg))
    (fun s => JointKeysInv S n root s.1) req inner queried seen bad (fun _ => hinv)
    fun hmsg _ leaf _ _ => ?_
  dsimp only [jointKeysBody, lazySignBody]
  exact (jointKeysCertify_lazy_spec S depth hsigCap hinv leaf).bind
    fun ⟨uk', ⟨node, idx, certs⟩, vis', edg', all'⟩ _ ⟨hi', hidx'⟩ =>
      (PMF.RepInv.of_eq (localSignEdge_notrunc S hsigCap hi'.keys_supp hidx'
        (Bool.toNat_le _) (Or.inl hmsg) edg' all')).map
        fun _ _ _ => ⟨rfl,
          ⟨hi'.len_eq, hi'.root_lookup, hi'.root_key, hi'.keys_supp, hi'.slots_lt⟩⟩

private noncomputable def expandKeys (S : IndexedSignatureScheme) (n K : ℕ)
    (uk : List (List Bool × List Bool)) : PMF (List (List Bool × List Bool)) :=
  (ProbComp.eval (OracleComp.replicate (K - uk.length) (S.keyGen n))).map (uk ++ ·)

private theorem jointVisitKey_expandKeys (S : IndexedSignatureScheme) (n K : ℕ)
    {uk : List (List Bool × List Bool)} {vis : NodeSlotCache}
    (hlen : uk.length = vis.length) (hpos : 0 < uk.length)
    (hvis : ∀ e ∈ vis, e.2 < vis.length) (hlt : vis.length < K) (path : List Bool) :
    PMF.HiddenCoupling (jointVisitKey S n path (uk, vis)) (expandKeys S n K uk)
      (fun x => expandKeys S n K x.2.1) (fun x => (x.1, x.2.2))
      (fun keys => PMF.pure (visitNodePure keys.length path vis))
      (fun (idx, uk', vis') => uk'.length = vis'.length ∧ 0 < uk'.length ∧
        (∀ e ∈ vis', e.2 < vis'.length) ∧ idx < uk'.length ∧
        uk.length ≤ uk'.length ∧ vis'.length ≤ vis.length + 1) := by
  refine ⟨?_, fun ⟨idx, uk', vis'⟩ hm => ?_⟩
  · simp only [jointVisitKey, visitNodePure, PMF.map, pmf_norm]
    cases vis.lookup path with
    | some idx => simp only [pmf_norm]
    | none =>
      set m := K - uk.length - 1
      have hsub : K - uk.length = m + 1 := by omega
      simp only [expandKeys, hsub, OracleComp.replicate_succ, pmf_norm]
      refine PMF.bind_congr_on_support _ _ _ fun child _ => ?_
      rw [show K - (uk ++ [child]).length = m by simp; omega]
      refine PMF.bind_congr_on_support _ _ _ fun rem hrem => ?_
      have hremLen := ((ProbComp.mem_support_replicate_iff _ _ _).mp hrem).1
      have hmin : min vis.length (uk ++ child :: rem).length = vis.length :=
        Nat.min_eq_left (by simp [hremLen]; omega)
      simp only [List.append_assoc, List.singleton_append, hmin]
  · obtain ⟨hl, hp, hv, hc, hle, hg, -⟩ := jointVisitKey_support_inv S n hlen hpos hvis path hm
    exact ⟨hl, hp, hv, hc, hle, hg⟩

private theorem localSignEdge_expandKeys (S : IndexedSignatureScheme) (n K sigCap : ℕ)
    {uk : List (List Bool × List Bool)} {idx : ℕ} (hidx : idx < uk.length)
    (path : List Bool) (u : ℕ) (msg : List Bool) (ea : EdgeSigCache × AllSignedLog) :
    PMF.HiddenCoupling (localSignEdge S uk sigCap path idx u msg ea)
      (expandKeys S n K uk) (fun _ => expandKeys S n K uk) id
      (fun keys => localSignEdge S keys sigCap path idx u msg ea)
      (fun _ => True) := by
  refine ⟨?_, fun _ _ => trivial⟩
  dsimp only [id]
  have hcomm : ((localSignEdge S uk sigCap path idx u msg ea).bind fun out =>
      (expandKeys S n K uk).map fun keys => (keys, out)) =
      (expandKeys S n K uk).bind fun keys =>
        (localSignEdge S uk sigCap path idx u msg ea).map fun out => (keys, out) := by
    simp only [PMF.map]; exact PMF.bind_comm _ _ _
  rw [hcomm]
  refine PMF.bind_congr_on_support _ _ _ fun keys hkeys => ?_
  supp_cases hkeys [expandKeys] with ⟨rem, -, rfl⟩
  simp only [localSignEdge, List.getD_append _ _ _ _ hidx]

private theorem jointKeysCertify_expandKeys (S : IndexedSignatureScheme) (depth : ℕ → ℕ)
    (sigCap n K : ℕ) {uk : List (List Bool × List Bool)} {vis : NodeSlotCache}
    (hlen0 : uk.length = vis.length) (hpos0 : 0 < uk.length)
    (hvis0 : ∀ e ∈ vis, e.2 < vis.length) (hbound : vis.length + (depth n - 1) ≤ K)
    (leaf : List Bool) (edg : EdgeSigCache) (all : AllSignedLog) :
    PMF.HiddenCoupling (jointKeysCertify S depth sigCap n leaf (uk, vis, edg, all))
      (expandKeys S n K uk) (fun x => expandKeys S n K x.1) Prod.snd
      (fun keys => localCertify S depth keys sigCap n leaf (vis, edg, all))
      (fun (uk', cs) => uk'.length = cs.2.1.length ∧ 0 < uk'.length ∧
        (∀ e ∈ cs.2.1, e.2 < cs.2.1.length) ∧
        cs.1.2.1 < uk'.length ∧ cs.2.1.length ≤ vis.length + (depth n - 1)) := by
  dsimp only [jointKeysCertify, localCertify]
  apply PMF.HiddenCoupling.iterate fun m (st : JointKeysCertState) =>
    st.1.length = st.2.2.1.length ∧ 0 < st.1.length ∧
    (∀ e ∈ st.2.2.1, e.2 < st.2.2.1.length) ∧
    st.2.1.2.1 < st.1.length ∧ st.2.2.1.length ≤ vis.length + m
  · rfl
  · exact fun _ _ => rfl
  · exact ⟨hlen0, hpos0, hvis0, hpos0, Nat.le_add_right _ _⟩
  rintro m hm ⟨uk_m, ⟨node, idx, certs⟩, vis_m, edg_m, all_m⟩
    ⟨hlen_m, hpos_m, hvis_m, hidx_m, hgrow_m⟩
  dsimp only at hlen_m hpos_m hvis_m hidx_m hgrow_m
  dsimp only [jointKeysCertifyStep, localCertifyStep]
  simp only [pmf_norm]
  set bit := leaf.getD node.length false
  set childPath := node ++ [bit]
  apply PMF.HiddenCoupling.bind_pure
    (f₂ := fun keys vp =>
      let childPk := (keys.getD vp.1 ([], [])).1
      (localSignEdge S keys sigCap node idx bit.toNat childPk (edg_m, all_m)).map
        fun x => ((childPath, vp.1, certs ++ [(childPk, x.1)]), vp.2, x.2.1, x.2.2))
    (jointVisitKey_expandKeys S n K hlen_m hpos_m hvis_m (by omega) childPath)
  rintro ⟨cIdx, uk', vis'⟩ - ⟨hl1, hp1, hv1, hcLt, hleU, hg1⟩
  have hget : ∀ keys ∈ (expandKeys S n K uk').support,
      (keys.getD cIdx ([], [])).1 = (uk'.getD cIdx ([], [])).1 := fun keys hk => by
    supp_cases hk [expandKeys] with ⟨_, -, rfl⟩
    rw [List.getD_append _ _ _ _ hcLt]
  apply ((localSignEdge_expandKeys S n K sigCap (hidx_m.trans_le hleU) node bit.toNat
    (uk'.getD cIdx ([], [])).1 (edg_m, all_m)).congr rfl
    (fun keys hk => by rw [hget keys hk]) fun _ _ h => h).map
  intro _ _ _
  exact ⟨rfl, fun keys hk => by simp only [id_eq, hget keys hk],
    hl1, hp1, hv1, hcLt, hg1.trans (Nat.add_le_add_right hgrow_m 1)⟩

/-- Query-budgeted capacity invariant for the `expandKeys` hidden-coupling step. -/
private structure JointExpandInv (K budget : ℕ) (st : JointKeysInner) : Prop where
  len_eq : st.1.length = st.2.1.length
  len_pos : 0 < st.1.length
  slots_lt : ∀ e ∈ st.2.1, e.2 < st.2.1.length
  cap_ok : st.2.1.length + budget ≤ K

private theorem jointKeysHandler_expandKeys (S : IndexedSignatureScheme) (depth : ℕ → ℕ)
    (sigCap n K : ℕ) (req : Unit × List Bool) (st : JointKeysState)
    (hinv : JointExpandInv K (depth n - 1) st.1) :
    PMF.HiddenCoupling (jointKeysHandler S depth sigCap n req st)
      (expandKeys S n K st.1.1) (fun x => expandKeys S n K x.2.1.1)
      (fun (ans, st') => (ans, st'.1.2, st'.2))
      (fun keys => localTreeHandler S depth keys sigCap n req (st.1.2, st.2))
      (fun (_, st') => st'.1.1.length = st'.1.2.1.length ∧ 0 < st'.1.1.length ∧
        (∀ e ∈ st'.1.2.1, e.2 < st'.1.2.1.length) ∧
        st'.1.2.1.length ≤ st.1.2.1.length + (depth n - 1)) := by
  obtain ⟨⟨uk, vis, edg, allSigned⟩, ⟨queried, seen, bad⟩⟩ := st
  apply guardedTreeHandler_bind_comm depth n (fun x => expandKeys S n K x.1) Prod.snd
    (fun s => s.1.1.length = s.1.2.1.length ∧ 0 < s.1.1.length ∧
      (∀ e ∈ s.1.2.1, e.2 < s.1.2.1.length) ∧ s.1.2.1.length ≤ vis.length + (depth n - 1))
    req (uk, vis, edg, allSigned) queried seen bad
    (fun _ => ⟨hinv.len_eq, hinv.len_pos, hinv.slots_lt, Nat.le_add_right _ _⟩)
  intro _ _ leaf _ _
  dsimp only [jointKeysBody, localSignBody]
  exact (jointKeysCertify_expandKeys S depth sigCap n K hinv.len_eq hinv.len_pos hinv.slots_lt
    hinv.cap_ok leaf edg allSigned).bind fun ⟨uk', ⟨node, idx, certs⟩, vis', edg', all'⟩ _
      ⟨hl1, hp1, hv1, hidx', hg1⟩ =>
      (localSignEdge_expandKeys S n K sigCap hidx' node (leaf.getLastD false).toNat req.2
        (edg', all')).map fun _ _ _ => ⟨rfl, fun _ _ => rfl, hl1, hp1, hv1, hg1⟩

private theorem eval_lazyTreeGame_eq_presampled (S : IndexedSignatureScheme)
    (depth slotBound sigCap : ℕ → ℕ) {n Q : ℕ} (hdepth_pos : 1 ≤ depth n)
    (hslot : Q * depth n ≤ slotBound n)
    (hsigCap : ∀ keys ∈ (ProbComp.eval (S.keyGen n)).support, ∀ u ≤ 1, ∀ msg,
      TreeMsg S n msg → ∀ σ ∈ (ProbComp.eval (S.sign keys.2 u msg)).support, σ.length ≤ sigCap n)
    (adversary : Forger)
    (hq : ∀ root ∈ (ProbComp.eval (S.keyGen n)).support,
      (adversary n (encPair encUnary encBits (n, root.1))).IsQueryBounded Q) :
    ProbComp.eval (lazyTreeGame S depth adversary n) =
      (presampledExp S depth slotBound sigCap adversary n).map
        (treeWinOfPresampled S depth n) := by
  set K := dyadicSize (slotBound n) with hK_def
  have hslotLt : 1 + Q * (depth n - 1) < K := slot_bound_lt_dyadicSize hdepth_pos hslot
  have hrep : ProbComp.eval (OracleComp.replicate K (S.keyGen n)) =
      (ProbComp.eval (S.keyGen n)).bind fun root => expandKeys S n K [root] := by
    have hKeq : K = (K - 1) + 1 := by have := two_le_dyadicSize (slotBound n); omega
    conv_lhs => rw [hKeq, OracleComp.replicate_succ]
    simp only [expandKeys, List.length_singleton, List.singleton_append, pmf_norm]
  simp only [lazyTreeGame, presampledExp, ← hK_def, ProbOracleComp.eval_run_interpret, hrep,
    pmf_norm]
  apply PMF.bind_congr_on_support; intro root hroot
  set pk := encPair encUnary encBits (n, root.1)
  set initJ : JointKeysState := (([root], initPresampledState.1), initPresampledState.2)
  have hjInv : JointKeysInv S n root initJ.1 :=
    ⟨rfl, rfl, rfl, fun k hk => List.mem_singleton.mp hk ▸ hroot,
      fun e he => by
        rw [List.mem_singleton.mp he]
        simp [initJ, initPresampledState]⟩
  have hproj := ProbOracleComp.run_interpret_map_state_of_invariant _
    (fun q s => ProbComp.eval (lazySignHandler S depth n root q s))
    (fun s => ((nodesOf s.1.1 s.1.2.1, s.1.2.2.1), s.2)) _
    (fun q s hs a s' hm =>
      (jointKeysHandler_lazy_step S depth hsigCap q s hs).support_inv (a, s') hm)
    (fun q s hs => (jointKeysHandler_lazy_step S depth hsigCap q s hs).map_eq)
    (adversary n pk) initJ hjInv
  have hexpRun := (ProbOracleComp.IsQueryBounded.run_interpret_bind_comm_of_invariant
    (jointKeysHandler S depth (sigCap n) n)
    (fun keys => localTreeHandler S depth keys (sigCap n) n)
    (fun st => expandKeys S n K st.1.1) (fun st => (st.1.2, st.2))
    (fun rem st => JointExpandInv K (rem * (depth n - 1)) st.1)
    (fun r s h =>
      ⟨h.len_eq, h.len_pos, h.slots_lt,
        le_trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_succ r)) _) h.cap_ok⟩)
    (fun r req s h => by
      have hmul : (r + 1) * (depth n - 1) = r * (depth n - 1) + (depth n - 1) :=
        Nat.succ_mul r (depth n - 1)
      have hcap := h.cap_ok
      obtain ⟨heq, hsupp⟩ := jointKeysHandler_expandKeys S depth (sigCap n) n K req s
        ⟨h.len_eq, h.len_pos, h.slots_lt, by omega⟩
      exact ⟨heq, fun ans s' hm => by
        obtain ⟨hl, hp, hv, hg⟩ := hsupp (ans, s') hm
        exact ⟨hl, hp, hv, by omega⟩⟩)
    (hq root hroot) (s := initJ)
    ⟨rfl, Nat.zero_lt_one,
      fun e he => by rw [List.mem_singleton.mp he]; simp [initJ, initPresampledState],
      by simpa [initJ, initPresampledState] using hslotLt.le⟩).1
  refine Eq.trans ?_
    ((congrArg (PMF.map (treeWinOfPresampled S depth n)) hexpRun).trans ?_)
  · rw [show (([([], root)], []), ⟨[], [], false⟩) =
      ((nodesOf initJ.1.1 initJ.1.2.1, initJ.1.2.2.1), initJ.2) from rfl, ← hproj]
    simp only [pmf_norm]
    refine PMF.bind_congr_on_support _ _ _ fun ⟨msig, st'⟩ hm_run => ?_
    have hjInv' := ProbOracleComp.run_interpret_invariant
      (jointKeysHandler S depth (sigCap n) n) (fun s => JointKeysInv S n root s.1)
      (fun q s hs a s' hm =>
        (jointKeysHandler_lazy_step S depth hsigCap q s hs).support_inv (a, s') hm)
      (adversary n pk) initJ hjInv msig st' hm_run
    have hpos' : 0 < st'.1.1.length :=
      hjInv'.len_eq ▸ hjInv'.slots_lt ([], 0) (List.mem_of_lookup_eq_some hjInv'.root_lookup)
    symm
    rw [← PMF.map_const (expandKeys S n K st'.1.1)]
    refine PMF.map_congr_on_support _ _ _ fun keys hkeys => ?_
    supp_cases hkeys [expandKeys] with ⟨_, -, rfl⟩
    simp only [treeWinOfPresampled, List.getD_append _ _ _ _ hpos', hjInv'.root_key, pk]; rfl
  · simp only [pmf_norm]
    refine PMF.bind_congr_on_support _ _ _ fun keys hkeys => ?_
    supp_cases hkeys [expandKeys] with ⟨_, -, rfl⟩; rfl

/-! ### Query-bounded invariant on `presampledExp` and forgery extraction -/

private def allSignedInv (d : ℕ) (keys : List (List Bool × List Bool))
    (visited : NodeSlotCache) (queried : List (List Bool)) (allSigned : AllSignedLog) : Prop :=
  ∀ p idx u m, (p, idx, u, m) ∈ allSigned →
    (p, idx) ∈ visited ∧
    ((p.length + 1 < d ∧ ∃ (b : Bool) (childIdx : ℕ),
        b.toNat = u ∧ (p ++ [b], childIdx) ∈ visited ∧ m = (keys.getD childIdx ([], [])).1) ∨
      (p.length + 1 = d ∧ m ∈ queried))

private theorem allSignedInv_mono {d : ℕ} {keys : List (List Bool × List Bool)}
    {v₁ v₂ : NodeSlotCache} {q₁ q₂ : List (List Bool)} {a : AllSignedLog}
    (hv : ∀ e ∈ v₁, e ∈ v₂) (hq : ∀ m ∈ q₁, m ∈ q₂) (h : allSignedInv d keys v₁ q₁ a) :
    allSignedInv d keys v₂ q₂ a := fun p idx u m hm =>
  let ⟨hp, hd⟩ := h p idx u m hm
  ⟨hv _ hp, hd.imp (fun ⟨hl, b, c, hb, hc, hm⟩ => ⟨hl, b, c, hb, hv _ hc, hm⟩)
    (fun ⟨hl, hm⟩ => ⟨hl, hq _ hm⟩)⟩

private theorem allSignedInv_localSignEdge {S : IndexedSignatureScheme}
    {d : ℕ} {keys : List (List Bool × List Bool)} {sigCap : ℕ}
    {node msg : List Bool} {idx u : ℕ} {e : EdgeSigCache} {a : AllSignedLog}
    {v : NodeSlotCache} {q : List (List Bool)} {σ : List Bool} {e' : EdgeSigCache}
    {a' : AllSignedLog}
    (hm : (σ, (e', a')) ∈ (localSignEdge S keys sigCap node idx u msg (e, a)).support)
    (hinv : allSignedInv d keys v q a)
    (hnew : (node, idx) ∈ v ∧
      ((node.length + 1 < d ∧ ∃ (b : Bool) (childIdx : ℕ), b.toNat = u ∧
          (node ++ [b], childIdx) ∈ v ∧ msg = (keys.getD childIdx ([], [])).1) ∨
        (node.length + 1 = d ∧ msg ∈ q))) :
    allSignedInv d keys v q a' := by
  rcases mem_support_localSignEdge hm with ⟨_, rfl⟩ | ⟨_, rfl⟩
  · exact hinv
  · intro p i₀ u' m hm'
    rcases List.mem_cons.mp hm' with hhead | ht
    · cases hhead
      exact hnew
    · exact hinv p i₀ u' m ht

/-- Query-bounded invariant tying visited tree paths, slot allocations, and signed edge logs. -/
private structure PresampledBoundedInv (d : ℕ) (keys : List (List Bool × List Bool)) (rem : ℕ)
    (st : PresampledState) : Prop where
  root_mem : ([], 0) ∈ st.1.1
  cap_ok : st.1.1.length + rem * (d - 1) ≤ keys.length
  visited_ok : ∀ e ∈ st.1.1, e.1.length < d ∧ e.2 < st.1.1.length
  visited_unique : ∀ e₁ ∈ st.1.1, ∀ e₂ ∈ st.1.1, e₁.2 = e₂.2 → e₁ = e₂
  allSigned_ok : allSignedInv d keys st.1.1 st.2.queried st.1.2.2

private theorem localCertify_bounded_inv (S : IndexedSignatureScheme) (depth : ℕ → ℕ)
    (keys : List (List Bool × List Bool)) (sigCap n : ℕ) (hd : 1 ≤ depth n)
    (leaf : List Bool) {visited : NodeSlotCache} {edges : EdgeSigCache}
    {queried : List (List Bool)} {allSigned : AllSignedLog}
    (hroot : ([], 0) ∈ visited) (hbound : visited.length + (depth n - 1) ≤ keys.length)
    (hvis : ∀ e ∈ visited, e.1.length < depth n ∧ e.2 < visited.length)
    (huniq : ∀ e₁ ∈ visited, ∀ e₂ ∈ visited, e₁.2 = e₂.2 → e₁ = e₂)
    (hall : allSignedInv (depth n) keys visited queried allSigned) :
    ∀ node idx certs v' e' a',
      ((node, idx, certs), (v', e', a')) ∈
        (localCertify S depth keys sigCap n leaf (visited, edges, allSigned)).support →
      node.length + 1 = depth n ∧ (node, idx) ∈ v' ∧ ([], 0) ∈ v' ∧
      v'.length ≤ visited.length + (depth n - 1) ∧
      (∀ e ∈ v', e.1.length < depth n ∧ e.2 < v'.length) ∧
      (∀ e₁ ∈ v', ∀ e₂ ∈ v', e₁.2 = e₂.2 → e₁ = e₂) ∧
      allSignedInv (depth n) keys v' queried a' := by
  let inv (k : ℕ) (cs : LocalCertState) : Prop :=
    cs.1.1.length = k ∧ (cs.1.1, cs.1.2.1) ∈ cs.2.1 ∧ ([], 0) ∈ cs.2.1 ∧
    cs.2.1.length ≤ visited.length + k ∧
    (∀ e ∈ cs.2.1, e.1.length < depth n ∧ e.2 < cs.2.1.length) ∧
    (∀ e₁ ∈ cs.2.1, ∀ e₂ ∈ cs.2.1, e₁.2 = e₂.2 → e₁ = e₂) ∧
    allSignedInv (depth n) keys cs.2.1 queried cs.2.2.2
  have hmain := PMF.iterate_bind_invariant (localCertifyStep S keys sigCap leaf) inv (depth n - 1)
    (([], 0, []), (visited, edges, allSigned))
    ⟨rfl, hroot, hroot, Nat.le_add_right _ _, hvis, huniq, hall⟩
    fun k hk ⟨⟨node, idx, certs⟩, v, e, a⟩
        ⟨hnLen, hnode_v, hroot_v, hgrow_v, hvis_v, huniq_v, hall_v⟩ cs' hm_step => by
      dsimp only at hnLen hnode_v hroot_v hgrow_v hvis_v huniq_v hall_v
      have hvLt : v.length < keys.length := by omega
      have hkLt : k + 1 < depth n := by omega
      set bit := leaf.getD node.length false
      set childPath := node ++ [bit]
      have hcLen : childPath.length = k + 1 := by simp [childPath, hnLen]
      supp_cases hm_step [localCertifyStep] with ⟨⟨σ, e', a'⟩, hm_se, rfl⟩
      have hvp := visitNodePure_inv (P := fun p => p.length < depth n) (K := keys.length)
        childPath (hcLen ▸ hkLt) (fun ent he => ⟨(hvis_v ent he).1, fun _ => (hvis_v ent he).2⟩)
        (fun e₁ he₁ e₂ he₂ _ heq => huniq_v e₁ he₁ e₂ he₂ heq)
      set vp := visitNodePure keys.length childPath v
      have hltK : ∀ ent ∈ vp.2, ent.2 < keys.length := fun ent he =>
        (hvp.mem_or_new ent he).elim (fun h => (hvis_v ent h).2.trans hvLt)
          (fun h => h ▸ (Nat.min_le_left _ _).trans_lt hvLt)
      refine ⟨hcLen, hvp.mem_new, hvp.mono _ hroot_v,
        hvp.length_le.trans (Nat.add_le_add_right hgrow_v 1),
        fun ent he => ⟨(hvp.slots_ok ent he).1, (hvp.slots_ok ent he).2 (hltK ent he)⟩,
        fun e₁ he₁ e₂ he₂ heq => hvp.unique e₁ he₁ e₂ he₂ (hltK e₁ he₁) heq,
        allSignedInv_localSignEdge hm_se (allSignedInv_mono hvp.mono (fun _ h => h) hall_v)
          ⟨hvp.mono _ hnode_v, Or.inl ⟨hnLen ▸ hkLt, bit, vp.1, rfl, hvp.mem_new, rfl⟩⟩⟩
  intro node idx certs v' e' a' hm
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hmain _ hm
  exact ⟨by dsimp only at h1; omega, h2, h3, h4, h5, h6, h7⟩

private theorem localTreeHandler_bounded_inv (S : IndexedSignatureScheme) (depth : ℕ → ℕ)
    (keys : List (List Bool × List Bool)) (sigCap n : ℕ) (hd : 1 ≤ depth n)
    (req : Unit × List Bool) {rem : ℕ} {st : PresampledState}
    (hinv : PresampledBoundedInv (depth n) keys (rem + 1) st) :
    ∀ ans st', (ans, st') ∈ (localTreeHandler S depth keys sigCap n req st).support →
      PresampledBoundedInv (depth n) keys rem st' := by
  obtain ⟨⟨visited, edges, allSigned⟩, ⟨queried, seen, bad⟩⟩ := st
  obtain ⟨hroot, hbound, hvis_ok, huniq, hall_ok⟩ := hinv
  dsimp only at hroot hbound hvis_ok huniq hall_ok
  have hmul : (rem + 1) * (depth n - 1) = rem * (depth n - 1) + (depth n - 1) :=
    Nat.succ_mul rem (depth n - 1)
  refine guardedTreeHandler_support_inv depth n (localSignBody S depth keys sigCap n)
    (PresampledBoundedInv (depth n) keys rem) req (visited, edges, allSigned) queried seen bad
    (fun _ => ⟨hroot, show visited.length + rem * (depth n - 1) ≤ keys.length by omega, hvis_ok,
      huniq, allSignedInv_mono (fun _ h => h) (fun _ => List.mem_cons_of_mem _) hall_ok⟩)
    fun _ _ leaf _ _ sig ⟨v', e'', a''⟩ hm => ?_
  supp_cases hm [localSignBody] with ⟨⟨⟨node, idx, certs⟩, v₁, e₁, a₁⟩, hm_cert, ⟨σ, e₃, a₃⟩,
    hm_edge, rfl, rfl, rfl, rfl⟩
  obtain ⟨hnLen, hnode_v', hroot_v', hgrow_v', hvis_v', huniq_v', hall_v'⟩ :=
    localCertify_bounded_inv S depth keys sigCap n hd leaf hroot (by omega) hvis_ok huniq hall_ok
      node idx certs v₁ e₁ a₁ hm_cert
  exact ⟨hroot_v', show v₁.length + rem * (depth n - 1) ≤ keys.length by omega,
    hvis_v', huniq_v', allSignedInv_localSignEdge hm_edge
    (allSignedInv_mono (fun _ h => h) (fun _ => List.mem_cons_of_mem req.2) hall_v')
    ⟨hnode_v', Or.inr ⟨hnLen, List.mem_cons_self⟩⟩⟩

private def chainPk (pk₀ : List Bool) (certs : List (List Bool × List Bool)) (j : ℕ) :
    List Bool :=
  if j = 0 then pk₀ else (certs.getD (j - 1) ([], [])).1

private theorem foldl_verifyStep_spec (S : IndexedSignatureScheme) (pk₀ : List Bool)
    (bits : List Bool) (certs : List (List Bool × List Bool)) (hlen : bits.length = certs.length) :
    ((bits.zip certs).foldl (verifyStep S) (true, pk₀)).2 = chainPk pk₀ certs bits.length ∧
    (((bits.zip certs).foldl (verifyStep S) (true, pk₀)).1 = true ↔
      ∀ j < bits.length,
        S.verify (chainPk pk₀ certs j) (bits.getD j false).toNat
          (certs.getD j ([], [])).1 (certs.getD j ([], [])).2 = true) := by
  suffices ∀ m ≤ bits.length,
      (((bits.take m).zip (certs.take m)).foldl (verifyStep S) (true, pk₀)).2 =
        chainPk pk₀ certs m ∧
      ((((bits.take m).zip (certs.take m)).foldl (verifyStep S) (true, pk₀)).1 = true ↔
        ∀ j < m, S.verify (chainPk pk₀ certs j) (bits.getD j false).toNat
          (certs.getD j ([], [])).1 (certs.getD j ([], [])).2 = true) by
    have h := this bits.length le_rfl
    rwa [List.take_length, hlen, List.take_length, ← hlen] at h
  intro m
  induction m with
  | zero => intro _; simp [chainPk]
  | succ m ih =>
    intro hm
    obtain ⟨ih_pk, ih_ok⟩ := ih (by omega)
    rw [List.take_succ_eq_append_getElem hm, List.take_succ_eq_append_getElem (hlen ▸ hm),
      List.zip_append (by simp [hlen]), List.zip_cons_cons, List.zip_nil_right, List.foldl_append,
      List.foldl_cons, List.foldl_nil]
    simp only [verifyStep, ih_pk, Bool.and_eq_true, ih_ok,
      ← List.getD_eq_getElem bits false hm, ← List.getD_eq_getElem certs ([], []) (hlen ▸ hm)]
    exact ⟨by simp [chainPk],
      ⟨fun ⟨ha, hl⟩ j hj => (Nat.lt_succ_iff_lt_or_eq.mp hj).elim (ha j) (· ▸ hl),
        fun h => ⟨fun j hj => h j (Nat.lt_succ_of_lt hj), h m (Nat.lt_succ_self m)⟩⟩⟩

private theorem win_implies_any_plantedWin (S : IndexedSignatureScheme) (depth : ℕ → ℕ)
    {n K : ℕ} (hd : 1 ≤ depth n)
    {out : List (List Bool × List Bool) × (List Bool × List Bool) × PresampledState}
    (hkeysLen : out.1.length = K)
    (hinv : PresampledBoundedInv (depth n) out.1 0 out.2.2)
    (hwin : treeWinOfPresampled S depth n out = true) :
    ((List.range K).any fun j => plantedWin S depth n j out) = true := by
  classical
  obtain ⟨keys, ⟨msgStar, sigStar⟩, ⟨visited, edges, allSigned⟩, ⟨queried, seen, bad⟩⟩ := out
  have hbound : visited.length ≤ keys.length := by simpa using hinv.cap_ok
  simp only [treeWinOfPresampled, Bool.and_eq_true, Bool.not_eq_true', Bool.eq_false_iff,
    ne_eq, List.contains_iff_mem, beq_iff_eq] at hwin
  obtain ⟨⟨_, hfresh⟩, hver⟩ := hwin
  set pk₀ := (keys.getD 0 ([], [])).1
  rcases hdec : signatureDecoder.decode sigStar with ⟨leaf, certs, last⟩
  simp only [verify, keyDecoder.decode_enc, hdec, Bool.and_eq_true, beq_iff_eq] at hver
  obtain ⟨⟨⟨hleafLen, hcertsLen⟩, hchainOk⟩, hlastOk⟩ := hver
  have hdropLen : leaf.dropLast.length = certs.length := by
    rw [List.length_dropLast, hleafLen]; omega
  obtain ⟨hchainPk, hchainAll⟩ := foldl_verifyStep_spec S pk₀ leaf.dropLast certs hdropLen
  have hcertsVer : ∀ j < depth n - 1,
      S.verify (chainPk pk₀ certs j) (leaf.getD j false).toNat
        (certs.getD j ([], [])).1 (certs.getD j ([], [])).2 = true := fun j hj => by
    have hvj := hchainAll.mp hchainOk j (by rw [List.length_dropLast, hleafLen]; exact hj)
    rwa [List.dropLast_eq_take, hleafLen,
      List.getD_eq_getElem (_ : List Bool) false (by simp; omega),
      List.getElem_take, ← List.getD_eq_getElem leaf false (by omega)] at hvj
  rw [hchainPk, List.length_dropLast, hleafLen, show leaf.getLastD false =
    leaf.getD (depth n - 1) false by
      rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, hleafLen,
        List.getD_eq_getElem?_getD]] at hlastOk
  let P (j : ℕ) : Prop :=
    ∃ idx, (leaf.take j, idx) ∈ visited ∧ (keys.getD idx ([], [])).1 = chainPk pk₀ certs j
  set jStar := Nat.findGreatest P (depth n - 1)
  have hjLe : jStar ≤ depth n - 1 := Nat.findGreatest_le (depth n - 1)
  obtain ⟨target, hmemT, hpkT⟩ : P jStar :=
    Nat.findGreatest_spec (Nat.zero_le _) ⟨0, hinv.root_mem, rfl⟩
  have hpathEq := filter_headD_of_mem_unique visited hmemT hinv.visited_unique
  have hpathLen : (leaf.take jStar).length = jStar := by
    rw [List.length_take, hleafLen]; exact Nat.min_eq_left (by omega)
  have hlogMem : ∀ {u₀ m₀}, (u₀, m₀) ∈ signedLogOf target allSigned →
      ((leaf.take jStar).length + 1 < depth n ∧ ∃ (b : Bool) (childIdx : ℕ), b.toNat = u₀ ∧
        (leaf.take jStar ++ [b], childIdx) ∈ visited ∧ m₀ = (keys.getD childIdx ([], [])).1) ∨
      ((leaf.take jStar).length + 1 = depth n ∧ m₀ ∈ queried) := fun {u₀ m₀} hmemLog => by
    simp only [signedLogOf, List.mem_map, List.mem_filter, beq_iff_eq] at hmemLog
    obtain ⟨⟨p, idx, u', m'⟩, ⟨hm_all, hidxEq⟩, heq⟩ := hmemLog
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq; dsimp only at hidxEq; subst hidxEq
    obtain ⟨hp_vis, hdisj⟩ := hinv.allSigned_ok p idx u' m' hm_all
    exact (Prod.mk.inj (hinv.visited_unique _ hp_vis _ hmemT rfl)).1 ▸ hdisj
  rw [List.any_eq_true]
  refine ⟨target, List.mem_range.mpr
    (((hinv.visited_ok _ hmemT).2 : target < visited.length).trans_le
      (hbound.trans_eq hkeysLen)), ?_⟩
  simp only [plantedWin, extractForgery, hdec, Bool.and_eq_true, Bool.not_eq_true',
    Bool.eq_false_iff, ne_eq, List.contains_iff_mem, hpathEq, hpathLen]
  split_ifs with hjLt
  · refine ⟨fun hm => ?_, hpkT ▸ hcertsVer jStar (by omega)⟩
    rcases hlogMem hm with ⟨_, b, childIdx, hbu, hcVis, hcmEq⟩ | ⟨hbadLen, _⟩
    · obtain rfl : b = leaf.getD jStar false :=
        (Bool.ofNat_toNat b).symm.trans (hbu ▸ Bool.ofNat_toNat _)
      have hjLeaf : jStar < leaf.length := by omega
      rw [List.getD_eq_getElem _ _ hjLeaf, ← List.take_succ_eq_append_getElem hjLeaf] at hcVis
      exact Nat.findGreatest_is_greatest (lt_add_one jStar) (by omega)
        ⟨childIdx, hcVis, by simpa [chainPk] using hcmEq.symm⟩
    · rw [hpathLen] at hbadLen; omega
  · obtain hje : jStar = depth n - 1 := by omega
    refine ⟨fun hm => ?_, by rwa [hpkT, hje]⟩
    rcases hlogMem hm with ⟨hbadLt, _⟩ | ⟨_, hmq⟩
    · rw [hpathLen, hje] at hbadLt; omega
    · exact hfresh hmq

private theorem eval_indexedEufCmaGame_indexedForger (S : IndexedSignatureScheme)
    (depth slotBound sigCap : ℕ → ℕ) (adversary : Forger) (n : ℕ) :
    ProbComp.eval (S.indexedEufCmaGame (indexedForger S depth slotBound sigCap adversary) n) =
      (PMF.uniformOfFintype (Fin (dyadicSize (slotBound n)))).bind fun target =>
        ProbComp.eval
          (S.indexedEufCmaGame (indexedForgerAt S depth slotBound sigCap adversary target.val)
            n) := by
  simp only [IndexedSignatureScheme.indexedEufCmaGame, indexedForger,
    ProbOracleComp.eval_run_interpret, interp_norm,
    ProbComp.eval_sampleDyadicIndex, pmf_norm]
  rw [PMF.bind_comm]

/-- **From lazy tree signing to indexed forgery**: when `Q * depth n ≤ slotBound n` and `sigCap n`
bounds all supported edge signature lengths, the forging probability in `lazyTreeGame` is at most
`dyadicSize (slotBound n)` times `indexedForger`'s forging probability against `S`. -/
theorem succProbability_lazyTreeGame_le (S : IndexedSignatureScheme)
    (depth slotBound sigCap : ℕ → ℕ) {n Q : ℕ}
    (hcap : 2 ≤ S.capacity n) (hdepth_pos : 1 ≤ depth n)
    (hslot : Q * depth n ≤ slotBound n)
    (hsigCap : ∀ keys ∈ (ProbComp.eval (S.keyGen n)).support, ∀ u ≤ 1, ∀ msg,
      TreeMsg S n msg →
      ∀ σ ∈ (ProbComp.eval (S.sign keys.2 u msg)).support, σ.length ≤ sigCap n)
    (adversary : Forger)
    (hq : ∀ root ∈ (ProbComp.eval (S.keyGen n)).support,
      (adversary n (encPair encUnary encBits (n, root.1))).IsQueryBounded Q) :
    Game.succProbability (ProbComp.eval (lazyTreeGame S depth adversary n)) ≤
      dyadicSize (slotBound n) * Game.succProbability
        (ProbComp.eval
          (S.indexedEufCmaGame (indexedForger S depth slotBound sigCap adversary) n)) := by
  set K := dyadicSize (slotBound n)
  set X := presampledExp S depth slotBound sigCap adversary n
  have hslotLt : 1 + Q * (depth n - 1) < K := slot_bound_lt_dyadicSize hdepth_pos hslot
  have hsupp : ∀ out ∈ X.support,
      out.1.length = K ∧ PresampledBoundedInv (depth n) out.1 0 out.2.2 := by
    intro out hout
    supp_cases hout [X, presampledExp] with ⟨keys, hkeys, ⟨msig, st⟩, hrun, rfl⟩
    obtain ⟨hkLen, hkSupp⟩ := (ProbComp.mem_support_replicate_iff _ _ _).mp hkeys
    have hpos : 0 < keys.length := by have := two_le_dyadicSize (slotBound n); omega
    have hinit : PresampledBoundedInv (depth n) keys Q initPresampledState :=
      ⟨List.mem_singleton.mpr rfl, by simpa [initPresampledState, hkLen] using hslotLt.le,
        fun e he => by
          rw [List.mem_singleton.mp he]
          exact ⟨by simp; omega, by simp [initPresampledState]⟩,
        fun e₁ he₁ e₂ he₂ _ => by rw [List.mem_singleton.mp he₁, List.mem_singleton.mp he₂],
        fun _ _ _ _ h => by cases h⟩
    exact ⟨hkLen, ProbOracleComp.IsQueryBounded.run_interpret_invariant
      (localTreeHandler S depth keys (sigCap n) n) (PresampledBoundedInv (depth n) keys)
      (fun r _ h =>
        ⟨h.root_mem,
          le_trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_succ r)) _) h.cap_ok,
          h.visited_ok, h.visited_unique, h.allSigned_ok⟩)
      (fun _ req _ hs ans st' hm => localTreeHandler_bounded_inv S depth keys (sigCap n) n
        hdepth_pos req hs ans st' hm)
      (hq _ (hkSupp _ (List.getD_mem ([], []) hpos))) hinit msig st hrun⟩
  have havg : ((K : ℕ) : ℝ≥0∞) * ProbComp.eval
        (S.indexedEufCmaGame (indexedForger S depth slotBound sigCap adversary) n) true =
      ∑ i ∈ Finset.range K, ProbComp.eval
        (S.indexedEufCmaGame (indexedForgerAt S depth slotBound sigCap adversary i) n) true := by
    rw [eval_indexedEufCmaGame_indexedForger, PMF.bind_apply, tsum_fintype]
    simp only [PMF.uniformOfFintype_apply, Fintype.card_fin]
    rw [← Finset.mul_sum, ← mul_assoc,
      ENNReal.mul_inv_cancel (Nat.cast_ne_zero.mpr (dyadicSize_pos (slotBound n)).ne') (by simp),
      one_mul, ← Fin.sum_univ_eq_sum_range]
  have hsum : ProbComp.eval (lazyTreeGame S depth adversary n) true ≤
      ((K : ℕ) : ℝ≥0∞) * ProbComp.eval
        (S.indexedEufCmaGame (indexedForger S depth slotBound sigCap adversary) n) true := by
    rw [eval_lazyTreeGame_eq_presampled S depth slotBound sigCap hdepth_pos hslot hsigCap
      adversary hq, havg]
    exact (PMF.map_true_mono X
      (F := fun out => (List.range K).any fun j => plantedWin S depth n j out) fun out ho hw =>
        let ⟨hk, hi⟩ := hsupp out ho; win_implies_any_plantedWin S depth hdepth_pos hk hi hw).trans
      ((PMF.map_any_range_true_le_sum X K (plantedWin S depth n)).trans
        (Finset.sum_le_sum fun i hi => by
          rw [map_plantedWin_presampledExp S depth slotBound sigCap hcap adversary
            (Finset.mem_range.mp hi)]))
  simpa only [ENNReal.toNNReal_mul, ENNReal.toNNReal_natCast] using
    ENNReal.toNNReal_mono (ENNReal.mul_ne_top (by simp) (PMF.apply_ne_top _ _)) hsum

end TreeSignature

end Cslib.Crypto
