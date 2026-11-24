/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Query.MinimumSpanningForest.Certificate.State
public import CslibFrontier.Algorithms.Lean.Query.Select.Quota
public import CslibFrontier.Algorithms.Lean.Query.Sort.LEQuery.KeyOracle
public import Mathlib.Analysis.Real.Sqrt
import CslibFrontier.Algorithms.Lean.Query.FreeM.LiftM
import CslibFrontier.Foundations.Combinatorics.SetFamily.HittingSet
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Tactic.IntervalCases

/-!
# Batch processing of the certificate procedure

At the end of each block of rounds, the certificate procedure of
[Khanna, Putterman and Song][KhannaPuttermanSong2026] processes the batch `B` of edges that chose
the action *find* (§3.2, pp. 14–16; Algorithm 1, lines 20–21, p. 14). Every vertex `v` groups its
edges in `B` by their other end and selects the `k = r²` lightest *representatives* (lightest
admissible edges of a group), with the quota selection of Lemma 3.3; the selected edges are
*declared*, forming `D`, and `S_v` is the set of neighbours they reach. New portals `P'` meet
every `S_v` of size `k`. Each such `v` gets the lighter of its spoke and a selected edge to a new
portal. Edges whose admissibility test failed form `R'`. Finally the forest is replaced by
`MSF(F ∪ D)`.

`Cslib.Query.Certificate.batch test msfSub r st B` is this procedure as a comparison program in
`FreeM (LEQuery E)`, acting on the state `st` of the call (`Cslib.Query.Certificate.State`) and
returning a `Cslib.Query.Certificate.BatchResult`. Its two subprograms are parameters:

* `test e` decides whether `e` is admissible. It is correct for a predicate `adm` against the
  comparison oracle `LEQuery.keyOracle w` of the weights, and costs at most `cs` comparisons when
  `e` is admissible and `cf` when not. In the certificate procedure the test scans the projection
  record of `e` (p. 13). The test returns a `Bool`; the first invalid recursion level of a
  rejected edge, which Algorithm 1 uses on line 18, is recomputed by the caller, at the cost of one
  more test per rejected edge.
* `msfSub S` is the exact minimum spanning forest call `MSF(G[F ∪ D])` of line 21. Costs are
  stated as the comparisons outside the call plus those of the call, and results that read the new
  forest assume that the call returned `msf (F ∪ D)`.

## Source mapping

Lemma 3.2 (§3.2, p. 15), for a batch `B` on an instance with `n` vertices:

* `D ⊆ B`, `|D| ≤ k n`, and every declared edge is admissible:
  `Cslib.Query.Certificate.declared_subset_batch`, `Cslib.Query.Certificate.card_declared_batch_le`,
  `Cslib.Query.Certificate.adm_of_mem_declared_batch`.
* `|P'| ≤ 2n / r`, as `|P'| r ≤ 2 n`, for every oracle:
  `Cslib.Query.Certificate.card_newPortals_batch_mul_le`; and `P' ⊆ X`
  (`Cslib.Query.Certificate.newPortals_subset_batch`).
* `R'` consists of edges of `B` that failed their test:
  `Cslib.Query.Certificate.rejected_subset_batch`,
  `Cslib.Query.Certificate.not_adm_of_mem_rejected_batch`.
* After `F ← MSF(F ∪ D)`, every `e ∈ B \ R'` is supported by `F`, or both its ends have spokes
  with `max (w σ(u)) (w σ(v)) ≤ w e`: `Cslib.Query.Certificate.supported_or_spokes_batch`.

The accounting paragraph after Lemma 3.3 (p. 16): `Cslib.Query.Certificate.countQueries_batch_le`
bounds the comparisons by `468 |B| + n` outside the tests and the exact call, `cs r² √(8 n |B|)`
for successful tests, `cf |R'|` for failed tests, and the call itself, on `F ∪ D`.

What the correctness argument of §3.3 (Claims 3.5–3.6, Lemma 3.7, pp. 17–18) uses of the spokes:

* `Cslib.Query.Certificate.spoke_batch_le`: spokes are never removed and only get lighter;
* `Cslib.Query.Certificate.spoke_batch_eq_or_mem_declared`: a new spoke is a declared edge;
* `Cslib.Query.Certificate.State.Invariant.batch`: the invariant of the state is preserved: in
  particular a spoke of `v` has ends `v` and `π v ∈ P ∪ P'`, and every spoke is supported by the
  new forest.

`Cslib.Query.Certificate.vertices_batch`, `Cslib.Query.Certificate.ends_batch`,
`Cslib.Query.Certificate.portals_batch` and `Cslib.Query.Certificate.forest_batch` describe the new
state.

## Deviations from §3.2

None changes Lemma 3.2.

* Self-loops of `B` are left out of the per-vertex lists. Every forest supports a self-loop.
* Quota selection runs only at vertices with an edge of `B` other than a self-loop, so that a
  vertex without edges costs no tests; the paper's `O(k log(deg_B v + 1))` is `0` there.
* An edge that failed its test at one end is left out of the lists of later vertices, rather than
  stored and looked up (p. 15). So no edge fails twice, and the failed tests number exactly `|R'|`.
* The new portals are any hitting set of the full `S_v` with `|P'| r ≤ 2 n`, chosen without
  comparisons. It exists by the paper's greedy argument (`Cslib.exists_hittingSet_card_mul_le`).
  The candidate spoke of `v` is the first selected edge of `v` to a new portal, rather than the
  edge to "the first portal selected" (p. 15); the proof of Lemma 3.2 uses only that it is a
  selected edge to a new portal.
* The constants use `⌈log₂⌉` from Lemma 3.3 as formalized (`⌈log₂ d⌉ + 1 ≤ 2 √d`), in place of the
  paper's `log (x + 1) ≤ √x`.
* The program is noncomputable: it enumerates finite sets and chooses the portals classically.
  This is free computation between comparisons, which the decision-tree model allows.

## References

* [S. Khanna, A. Putterman and J. Song, *A Deterministic Linear Time Algorithm for Minimum
  Spanning Tree*][KhannaPuttermanSong2026], §3.2, pp. 14–16.
-/

public section

namespace Cslib.Query.Certificate

open Finset Multigraph

variable {V E : Type} [DecidableEq V] [DecidableEq E]

/-! ### The program -/

/-- Run a comparison as itself and a test of `e` by the subprogram `test e`. -/
private def runTests (test : E → FreeM (LEQuery E) Bool) :
    {ι : Type} → CmpTestQuery E ι → FreeM (LEQuery E) ι
  | _, .inl q => FreeM.lift q
  | _, .inr (.test e) => test e

/-- The edges of `B` at `v`, other than self-loops. -/
private def incident (ends : E → Sym2 V) (B : Finset E) (v : V) : Finset E :=
  {e ∈ B | v ∈ ends e ∧ ¬(ends e).IsDiag}

omit [DecidableEq E] in
private theorem mem_incident {ends : E → Sym2 V} {B : Finset E} {v : V} {e : E} :
    e ∈ incident ends B v ↔ e ∈ B ∧ v ∈ ends e ∧ ¬(ends e).IsDiag := by
  simp [incident]

/-- The vertices of `X` with an edge of `B` other than a self-loop. -/
private def active (ends : E → Sym2 V) (B : Finset E) (X : Finset V) : Finset V :=
  {v ∈ X | (incident ends B v).Nonempty}

/-- Quota selection at each vertex of the list in turn: at `v`, among the edges of `B` at `v`
grouped by their other end, select the `k` lightest representatives, with the tests run by
`test`. Edges whose test failed at an earlier vertex (the set `R`) are left out, so that no edge
is tested twice and fails twice. -/
private noncomputable def selectAll (test : E → FreeM (LEQuery E) Bool) (ends : E → Sym2 V)
    (k : ℕ) (B : Finset E) : List V → Finset E → FreeM (LEQuery E) (V → QuotaSelection E)
  | [], _ => pure fun _ => ⟨[], []⟩
  | v :: vs, R => do
    let s ← (quotaSelect (fun e => otherEnd v (ends e)) k (incident ends B v \ R).toList).liftM
      (runTests test)
    let rest ← selectAll test ends k B vs (R ∪ s.failed.toFinset)
    pure (Function.update rest v s)

/-- The neighbours `S_v` of `v` reached by its selected edges. -/
private def reached (ends : E → Sym2 V) (sel : V → QuotaSelection E) (v : V) : Finset V :=
  (sel v).selected.toFinset.image fun e => otherEnd v (ends e)

open scoped Classical in
/-- A set of new portals inside `X` meeting every `S v` of size `r²`, of size at most `2|X| / r`,
when one exists (by the greedy argument, `Cslib.exists_hittingSet_card_mul_le`, it does). It is
chosen without comparisons. -/
private noncomputable def portalCover (X : Finset V) (r : ℕ) (S : V → Finset V) : Finset V :=
  if h : ∃ P ⊆ X, (∀ v ∈ X, #(S v) = r ^ 2 → (P ∩ S v).Nonempty) ∧ #P * r ≤ 2 * #X then
    h.choose
  else ∅

/-- The candidate spoke of `v`: when `|S_v| = r²`, a selected edge of `v` to a new portal. -/
private def candidate (ends : E → Sym2 V) (r : ℕ) (P' : Finset V) (sel : V → QuotaSelection E)
    (v : V) : Option E :=
  if #(reached ends sel v) = r ^ 2 then
    (sel v).selected.find? fun e => otherEnd v (ends e) ∈ P'
  else none

/-- Offer a candidate spoke to a vertex: it keeps the lighter of the candidate and its current
spoke, by one comparison. -/
private def offerSpoke : Option E → Option E → FreeM (LEQuery E) (Option E)
  | none, old => pure old
  | some c, none => pure (some c)
  | some c, some s => do if ← LEQuery.ask c s then pure (some c) else pure (some s)

/-- Offer its candidate spoke to each vertex of the list. -/
private def updateSpokes (cand spoke : V → Option E) :
    List V → FreeM (LEQuery E) (V → Option E)
  | [] => pure spoke
  | v :: vs => do
    let s ← offerSpoke (cand v) (spoke v)
    let rest ← updateSpokes cand spoke vs
    pure (Function.update rest v s)

/-- The result of processing a batch. -/
structure BatchResult (V E : Type) where
  /-- The state after the batch: new portals and spokes, and the forest `MSF(F ∪ D)`. -/
  state : State V E
  /-- The declared edges `D`. -/
  declared : Finset E
  /-- The new portals `P'`. -/
  newPortals : Finset V
  /-- The edges `R'` whose admissibility test failed. -/
  rejected : Finset E

/-- **Batch processing** ([KhannaPuttermanSong2026], §3.2, pp. 14–16; Algorithm 1, lines 20–21,
p. 14). For each vertex `v` with an edge of `B` (other than a self-loop), select by quota
selection (Lemma 3.3) the `k = r²` lightest representatives of the groups of its edges in `B` by
their other end, running admissibility tests by `test`; declare the selected edges. Choose new
portals `P'` meeting every `S_v` of size `k`, at no comparisons. Give each `v` with `|S_v| = k` the
lighter of its spoke and a selected edge to a new portal, by one comparison. Finally replace the
forest `F` by `msfSub (F ∪ D)`, the exact minimum spanning forest call. -/
noncomputable def batch (test : E → FreeM (LEQuery E) Bool)
    (msfSub : Finset E → FreeM (LEQuery E) (Finset E)) (r : ℕ) (st : State V E) (B : Finset E) :
    FreeM (LEQuery E) (BatchResult V E) := do
  let A := active st.ends B st.vertices
  let sel ← selectAll test st.ends (r ^ 2) B A.toList ∅
  let P' := portalCover st.vertices r (reached st.ends sel)
  let spoke ← updateSpokes (candidate st.ends r P' sel) st.spoke st.vertices.toList
  let D := A.biUnion fun v => (sel v).selected.toFinset
  let F ← msfSub (st.forest ∪ D)
  pure
    { state := { st with portals := st.portals ∪ P', spoke := spoke, forest := F }
      declared := D
      newPortals := P'
      rejected := A.biUnion fun v => (sel v).failed.toFinset }

/-! ### Running tests by subprograms -/

section Lift

variable {W : Type} [LinearOrder W] {w : E → W} {adm : E → Prop} [DecidablePred adm]
  {test : E → FreeM (LEQuery E) Bool}

omit [DecidableEq E] in
private theorem eval_liftM_runTests
    (htest : ∀ e, (test e).eval (LEQuery.keyOracle w) = decide (adm e))
    {α : Type} (p : FreeM (CmpTestQuery E) α) :
    (p.liftM (runTests test)).eval (LEQuery.keyOracle w) =
      p.eval (CmpTestQuery.oracleOf w adm) := by
  rw [FreeM.eval_liftM]
  congr 1
  funext ι q
  cases q with
  | inl q => cases q; rfl
  | inr q => cases q; exact htest _

omit [DecidableEq E] in
private theorem countQueries_liftM_runTests_le
    (htest : ∀ e, (test e).eval (LEQuery.keyOracle w) = decide (adm e)) {cs cf : ℕ}
    (hcs : ∀ e, adm e → (test e).countQueries (LEQuery.keyOracle w) ≤ cs)
    (hcf : ∀ e, ¬adm e → (test e).countQueries (LEQuery.keyOracle w) ≤ cf)
    {α : Type} (p : FreeM (CmpTestQuery E) α) :
    (p.liftM (runTests test)).countQueries (LEQuery.keyOracle w) ≤
      SumQuery.countInl (CmpTestQuery.oracleOf w adm) p +
        cs * p.cost (CmpTestQuery.oracleOf w adm)
          (CmpTestQuery.passWeight (CmpTestQuery.oracleOf w adm)) +
        cf * p.cost (CmpTestQuery.oracleOf w adm)
          (CmpTestQuery.failWeight (CmpTestQuery.oracleOf w adm)) := by
  induction p with
  | pure a => simp
  | lift_bind op cont ih =>
    change ((FreeM.lift op >>= cont).liftM (runTests test)).countQueries _ ≤
      SumQuery.countInl _ (FreeM.lift op >>= cont) +
        cs * (FreeM.lift op >>= cont).cost _ _ + cf * (FreeM.lift op >>= cont).cost _ _
    rw [FreeM.liftM_lift_bind, FreeM.countQueries_bind]
    simp only [SumQuery.countInl, FreeM.cost_liftBind]
    cases op with
    | inl q =>
      cases q with
      | le a b =>
        have e1 : CmpTestQuery.oracleOf w adm (SumQuery.inl (LEQuery.le a b)) =
            LEQuery.keyOracle w (.le a b) := rfl
        have := ih (LEQuery.keyOracle w (.le a b))
        simp only [SumQuery.countInl] at this
        simp only [runTests, e1, CmpTestQuery.passWeight, CmpTestQuery.failWeight,
          SumQuery.weightInl, FreeM.countQueries_lift, FreeM.eval_lift, zero_add]
        linarith
    | inr q =>
      cases q with
      | test e =>
        have e1 : CmpTestQuery.oracleOf w adm (SumQuery.inr (TestQuery.test e)) = decide (adm e) :=
          rfl
        have h := ih (decide (adm e))
        simp only [SumQuery.countInl] at h
        simp only [runTests, e1, htest, CmpTestQuery.passWeight, CmpTestQuery.failWeight,
          SumQuery.weightInl, zero_add]
        by_cases ha : adm e
        · simp only [ha, decide_true, ↓reduceIte] at h ⊢
          have := hcs e ha
          nlinarith
        · simp only [ha, decide_false, Bool.false_eq_true, ↓reduceIte] at h ⊢
          have := hcf e ha
          nlinarith

end Lift

/-! ### Quota selection at every vertex -/

section Select

variable {W : Type} [LinearOrder W] {w : E → W} {adm : E → Prop} [DecidablePred adm]
  {test : E → FreeM (LEQuery E) Bool}

/-- The run of `selectAll`: vertices outside the list select nothing; a vertex of the list runs
quota selection on its edges outside a set of earlier failures; and the failures are disjoint
from `R`, at distinct vertices, and each reported once. -/
private theorem selectAll_spec (hw : Function.Injective w)
    (htest : ∀ e, (test e).eval (LEQuery.keyOracle w) = decide (adm e))
    (ends : E → Sym2 V) (k : ℕ) (B : Finset E) (L : List V) (hL : L.Nodup) (R : Finset E) :
    let sel := (selectAll test ends k B L R).eval (LEQuery.keyOracle w)
    let U := L.toFinset.biUnion fun u => (sel u).failed.toFinset
    (∀ v ∉ L, sel v = ⟨[], []⟩) ∧
    (∀ v ∈ L, ∃ Rv ⊆ R ∪ U, sel v = (quotaSelect (fun e => otherEnd v (ends e)) k
        (incident ends B v \ Rv).toList).eval (CmpTestQuery.oracleOf w adm)) ∧
    Disjoint R U ∧ ∑ v ∈ L.toFinset, (sel v).failed.length = #U := by
  induction L generalizing R with
  | nil => simp [selectAll]
  | cons v vs ih =>
    intro sel U
    obtain ⟨hv, hvs⟩ := List.nodup_cons.1 hL
    set s := (quotaSelect (fun e => otherEnd v (ends e)) k (incident ends B v \ R).toList).eval
      (CmpTestQuery.oracleOf w adm) with hs
    set rest := (selectAll test ends k B vs (R ∪ s.failed.toFinset)).eval (LEQuery.keyOracle w)
      with hrest_def
    have hsel : sel = Function.update rest v s := by
      simp only [sel, selectAll, FreeM.eval_bind, FreeM.eval_pure, eval_liftM_runTests htest, s,
        rest]
    obtain ⟨h1, h2, h3, h4⟩ := ih hvs (R ∪ s.failed.toFinset)
    have hrest : ∀ u ∈ vs, sel u = rest u := fun u hu => by
      rw [hsel, Function.update_of_ne (by rintro rfl; exact hv hu)]
    have hsv : sel v = s := by rw [hsel, Function.update_self]
    obtain ⟨hsnd, hsf⟩ := failed_quotaSelect (adm := adm) (k := k)
      (fun e => otherEnd v (ends e)) hw (nodup_toList (incident ends B v \ R))
    have hsR : Disjoint R s.failed.toFinset := disjoint_left.2 fun x hxR hx => by
      have := (mem_sdiff.1 (mem_toList.1 (hsf x (List.mem_toFinset.1 hx)).1)).2
      exact this hxR
    set U' := vs.toFinset.biUnion fun u => (rest u).failed.toFinset
    have hU : U = s.failed.toFinset ∪ U' := by
      simp only [U, List.toFinset_cons, biUnion_insert, hsv]
      exact congrArg _ (biUnion_congr rfl fun u hu => by rw [hrest u (List.mem_toFinset.1 hu)])
    refine ⟨fun u hu => ?_, fun u hu => ?_, ?_, ?_⟩
    · rw [hsel, Function.update_of_ne (by rintro rfl; exact hu List.mem_cons_self)]
      exact h1 u fun h => hu (List.mem_cons_of_mem _ h)
    · rcases List.mem_cons.1 hu with rfl | hu
      · exact ⟨R, subset_union_left, hsv⟩
      · obtain ⟨Ru, hRu, hu'⟩ := h2 u hu
        refine ⟨Ru, hRu.trans ?_, (hrest u hu).trans hu'⟩
        rw [hU, union_assoc]
    · rw [hU]
      exact disjoint_union_right.2 ⟨hsR, h3.mono_left subset_union_left⟩
    · have hv' : v ∉ vs.toFinset := fun h => hv (List.mem_toFinset.1 h)
      rw [List.toFinset_cons, sum_insert hv', hsv, hU,
        card_union_of_disjoint (h3.mono_left subset_union_right), ← h4,
        List.toFinset_card_of_nodup hsnd]
      exact congrArg _ (sum_congr rfl fun u hu => by rw [hrest u (List.mem_toFinset.1 hu)])

/-- The comparisons of `selectAll`, with the tests run by subprograms that cost at most `cs` on
admissible and `cf` on inadmissible edges. -/
private theorem countQueries_selectAll_le
    (htest : ∀ e, (test e).eval (LEQuery.keyOracle w) = decide (adm e)) {cs cf : ℕ}
    (hcs : ∀ e, adm e → (test e).countQueries (LEQuery.keyOracle w) ≤ cs)
    (hcf : ∀ e, ¬adm e → (test e).countQueries (LEQuery.keyOracle w) ≤ cf)
    (ends : E → Sym2 V) (k : ℕ) (B : Finset E) (L : List V) (hL : L.Nodup) (R : Finset E) :
    (selectAll test ends k B L R).countQueries (LEQuery.keyOracle w) ≤
      ∑ v ∈ L.toFinset, (234 * #(incident ends B v) +
        cs * (k * (Nat.clog 2 #(incident ends B v) + 1)) +
        cf * ((selectAll test ends k B L R).eval (LEQuery.keyOracle w) v).failed.length) := by
  induction L generalizing R with
  | nil => simp [selectAll]
  | cons v vs ih =>
    obtain ⟨hv, hvs⟩ := List.nodup_cons.1 hL
    set q := quotaSelect (fun e => otherEnd v (ends e)) k (incident ends B v \ R).toList
    set s := q.eval (CmpTestQuery.oracleOf w adm) with hs
    set rest := (selectAll test ends k B vs (R ∪ s.failed.toFinset)).eval (LEQuery.keyOracle w)
    have hsel : (selectAll test ends k B (v :: vs) R).eval (LEQuery.keyOracle w) =
        Function.update rest v s := by
      simp only [selectAll, FreeM.eval_bind, FreeM.eval_pure, eval_liftM_runTests htest, s, rest,
        q]
    have hcq : (selectAll test ends k B (v :: vs) R).countQueries (LEQuery.keyOracle w) =
        (q.liftM (runTests test)).countQueries (LEQuery.keyOracle w) +
          (selectAll test ends k B vs (R ∪ s.failed.toFinset)).countQueries
            (LEQuery.keyOracle w) := by
      simp only [selectAll, FreeM.countQueries_bind, FreeM.countQueries_pure, add_zero,
        eval_liftM_runTests htest, q, s]
    have hv' : v ∉ vs.toFinset := fun h => hv (List.mem_toFinset.1 h)
    rw [hcq, List.toFinset_cons, sum_insert hv', hsel, Function.update_self]
    have hlen : (incident ends B v \ R).toList.length ≤ #(incident ends B v) := by
      rw [length_toList]; exact card_le_card sdiff_subset
    have hq := countQueries_liftM_runTests_le htest hcs hcf q
    have hin := countInl_quotaSelect_le (fun e => otherEnd v (ends e)) k
      (incident ends B v \ R).toList (CmpTestQuery.oracleOf w adm)
    have hpass := cost_passWeight_quotaSelect_le (fun e => otherEnd v (ends e)) k
      (incident ends B v \ R).toList (CmpTestQuery.oracleOf w adm)
    have hfail := cost_failWeight_quotaSelect (fun e => otherEnd v (ends e)) k
      (incident ends B v \ R).toList (CmpTestQuery.oracleOf w adm)
    have hclog := Nat.clog_mono_right 2 hlen
    have hrestsum := ih hvs (R ∪ s.failed.toFinset)
    have hcongr : ∑ u ∈ vs.toFinset, (234 * #(incident ends B u) +
        cs * (k * (Nat.clog 2 #(incident ends B u) + 1)) + cf * (rest u).failed.length) =
        ∑ u ∈ vs.toFinset, (234 * #(incident ends B u) +
        cs * (k * (Nat.clog 2 #(incident ends B u) + 1)) +
          cf * (Function.update rest v s u).failed.length) :=
      sum_congr rfl fun u hu => by
        rw [Function.update_of_ne (by rintro rfl; exact hv' hu)]
    rw [← hcongr]
    have h1 : SumQuery.countInl (CmpTestQuery.oracleOf w adm) q ≤ 234 * #(incident ends B v) :=
      hin.trans (Nat.mul_le_mul_left _ hlen)
    have h2 : q.cost (CmpTestQuery.oracleOf w adm)
        (CmpTestQuery.passWeight (CmpTestQuery.oracleOf w adm)) ≤
          k * (Nat.clog 2 #(incident ends B v) + 1) :=
      hpass.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right hclog 1))
    have h2' := Nat.mul_le_mul_left cs h2
    rw [hfail] at hq
    nlinarith

/-- What the batch proof uses of the selection `q` at `v`: the selected edges are admissible
edges at `v` going to distinct neighbours, at most `k` of them, and the failed edges are
inadmissible edges at `v`. -/
private structure SelFacts (ends : E → Sym2 V) (B : Finset E) (k : ℕ) (adm : E → Prop) (v : V)
    (q : QuotaSelection E) : Prop where
  selected : ∀ c ∈ q.selected, c ∈ incident ends B v ∧ adm c
  failed : ∀ c ∈ q.failed, c ∈ incident ends B v ∧ ¬adm c
  nodup : q.selected.Nodup
  length_le : q.selected.length ≤ k
  inj : ∀ c ∈ q.selected, ∀ c' ∈ q.selected, otherEnd v (ends c) = otherEnd v (ends c') → c = c'

omit [DecidableEq E] [DecidablePred adm] in
private theorem selFacts_empty (ends : E → Sym2 V) (B : Finset E) (k : ℕ) (v : V) :
    SelFacts ends B k adm v ⟨[], []⟩ :=
  ⟨by simp, by simp, List.nodup_nil, by simp, by simp⟩

private theorem selFacts_quotaSelect (hw : Function.Injective w) (ends : E → Sym2 V)
    (B : Finset E) (k : ℕ) (v : V) (R : Finset E) :
    SelFacts ends B k adm v ((quotaSelect (fun e => otherEnd v (ends e)) k
      (incident ends B v \ R).toList).eval (CmpTestQuery.oracleOf w adm)) := by
  have hnd := nodup_toList (incident ends B v \ R)
  have hrep : ∀ c ∈ ((quotaSelect (fun e => otherEnd v (ends e)) k
      (incident ends B v \ R).toList).eval (CmpTestQuery.oracleOf w adm)).selected,
      IsGroupRepresentative (fun e => otherEnd v (ends e)) w adm
        (incident ends B v \ R).toList c :=
    fun c hc => ((mem_selected_quotaSelect _ hw hnd c).1 hc).1
  refine ⟨fun c hc => ?_, fun c hc => ?_, nodup_selected_quotaSelect _ hw hnd, ?_,
    fun c hc c' hc' h => ?_⟩
  · obtain ⟨hmem, hadm, -⟩ := hrep c hc
    exact ⟨(mem_sdiff.1 (mem_toList.1 hmem)).1, hadm⟩
  · obtain ⟨hmem, hadm⟩ := (failed_quotaSelect _ hw hnd).2 c hc
    exact ⟨(mem_sdiff.1 (mem_toList.1 hmem)).1, hadm⟩
  · rw [length_selected_quotaSelect _ hw hnd]
    exact min_le_left _ _
  · obtain ⟨hm, ha, hle⟩ := hrep c hc
    obtain ⟨hm', ha', hle'⟩ := hrep c' hc'
    exact hw (le_antisymm (hle c' hm' ha' h.symm) (hle' c hm ha h))

end Select

/-! ### Spokes and portals -/

section Spokes

variable {W : Type} [LinearOrder W] {w : E → W}

omit [DecidableEq V] [DecidableEq E] in
private theorem offerSpoke_spec (cand old : Option E) :
    (∀ s, old = some s →
      ∃ s', (offerSpoke cand old).eval (LEQuery.keyOracle w) = some s' ∧ w s' ≤ w s) ∧
    (∀ c, cand = some c →
      ∃ s', (offerSpoke cand old).eval (LEQuery.keyOracle w) = some s' ∧ w s' ≤ w c) ∧
    (∀ s', (offerSpoke cand old).eval (LEQuery.keyOracle w) = some s' →
      old = some s' ∨ cand = some s') := by
  rcases cand with _ | c <;> rcases old with _ | s
  · simp [offerSpoke]
  · simp [offerSpoke]
  · simp [offerSpoke]
  · by_cases h : w c ≤ w s
    · simp [offerSpoke, h]
    · simp [offerSpoke, h, (not_le.1 h).le]

omit [DecidableEq V] [DecidableEq E] in
private theorem countQueries_offerSpoke_le (o : {ι : Type} → LEQuery E ι → ι)
    (cand old : Option E) : (offerSpoke cand old).countQueries o ≤ 1 := by
  rcases cand with _ | c <;> rcases old with _ | s
  · simp [offerSpoke]
  · simp [offerSpoke]
  · simp [offerSpoke]
  · simp only [offerSpoke, FreeM.countQueries_bind, LEQuery.ask, FreeM.countQueries_lift]
    split <;> simp

omit [DecidableEq E] in
private theorem eval_updateSpokes (o : {ι : Type} → LEQuery E ι → ι) (cand spoke : V → Option E)
    (L : List V) (v : V) : (updateSpokes cand spoke L).eval o v =
      if v ∈ L then (offerSpoke (cand v) (spoke v)).eval o else spoke v := by
  induction L with
  | nil => simp [updateSpokes]
  | cons u us ih =>
    simp only [updateSpokes, FreeM.eval_bind, FreeM.eval_pure, List.mem_cons]
    by_cases h : v = u
    · subst h; simp
    · rw [Function.update_of_ne h, ih]; simp [h]

omit [DecidableEq E] in
private theorem countQueries_updateSpokes_le (o : {ι : Type} → LEQuery E ι → ι)
    (cand spoke : V → Option E) (L : List V) :
    (updateSpokes cand spoke L).countQueries o ≤ L.length := by
  induction L with
  | nil => simp [updateSpokes]
  | cons u us ih =>
    simp only [updateSpokes, FreeM.countQueries_bind, FreeM.countQueries_pure, add_zero,
      List.length_cons]
    have := countQueries_offerSpoke_le o (cand u) (spoke u)
    omega

private theorem portalCover_spec (X : Finset V) (r : ℕ) (S : V → Finset V) :
    portalCover X r S ⊆ X ∧ #(portalCover X r S) * r ≤ 2 * #X := by
  unfold portalCover
  split
  · next h => exact ⟨h.choose_spec.1, h.choose_spec.2.2⟩
  · simp

private theorem portalCover_hits {X : Finset V} {r : ℕ} {S : V → Finset V} (hr : 0 < r)
    (hS : ∀ v ∈ X, S v ⊆ X) {v : V} (hv : v ∈ X) (hvS : #(S v) = r ^ 2) :
    (portalCover X r S ∩ S v).Nonempty := by
  classical
  obtain ⟨P, hPX, hP, hPc⟩ := exists_hittingSet_card_mul_le X {u ∈ X | #(S u) = r ^ 2} S hr
    (fun u hu => hS u (mem_filter.1 hu).1) (fun u hu => (mem_filter.1 hu).2.ge)
  have hex : ∃ P ⊆ X, (∀ v ∈ X, #(S v) = r ^ 2 → (P ∩ S v).Nonempty) ∧ #P * r ≤ 2 * #X :=
    ⟨P, hPX, fun u hu hu' => hP u (mem_filter.2 ⟨hu, hu'⟩),
      hPc.trans (by have := card_filter_le X fun u => #(S u) = r ^ 2; omega)⟩
  unfold portalCover
  split
  · next h => exact h.choose_spec.2.1 v hv hvS
  · next h => exact absurd hex h

end Spokes

/-! ### Counting -/

/-- `⌈log₂ d⌉ + 1 ≤ 2 √d` for `d ≥ 1`. -/
private theorem clog_add_one_le_two_sqrt {d : ℕ} (hd : 1 ≤ d) :
    ((Nat.clog 2 d + 1 : ℕ) : ℝ) ≤ 2 * √(d : ℝ) := by
  have aux : ∀ c : ℕ, 2 ≤ c → 2 * c + 3 ≤ 2 ^ (c + 1) := by
    intro c hc
    induction c, hc using Nat.le_induction with
    | base => norm_num
    | succ c _ ih => rw [pow_succ]; omega
  have main : ∀ c : ℕ, (c + 1) ^ 2 ≤ 2 ^ (c + 1) + 4 := by
    intro c
    rcases Nat.lt_or_ge c 2 with hc | hc
    · interval_cases c <;> norm_num
    · induction c, hc using Nat.le_induction with
      | base => norm_num
      | succ c hc ih =>
        have := aux c hc
        have h2 : 2 ^ (c + 1 + 1) = 2 * 2 ^ (c + 1) := by rw [pow_succ]; ring
        nlinarith
  have hsq : (Nat.clog 2 d + 1) ^ 2 ≤ 4 * d := by
    rcases Nat.eq_or_lt_of_le hd with rfl | hd2
    · simp
    · have hlt := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) hd2
      have hpos : 0 < Nat.clog 2 d := Nat.clog_pos (by norm_num) hd2
      obtain ⟨c, hc⟩ : ∃ c, Nat.clog 2 d = c + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
      rw [hc] at hlt ⊢
      have := main (c + 1)
      have h2 : 2 ^ (c + 1 + 1) = 4 * 2 ^ c := by rw [pow_succ, pow_succ]; ring
      simp only [Nat.pred_succ] at hlt
      omega
  rw [show (2 : ℝ) * √(d : ℝ) = √(4 * d) by
    rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]]
  exact Real.le_sqrt_of_sq_le (by exact_mod_cast hsq)

omit [DecidableEq E] in
/-- Every edge other than a self-loop is at two vertices, so the degrees in `B` add up to at most
`2 |B|`. -/
private theorem sum_card_incident_le (ends : E → Sym2 V) (B : Finset E) (X : Finset V) :
    ∑ v ∈ X, #(incident ends B v) ≤ 2 * #B := by
  have h := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (s := X) (t := B)
    (r := fun v e => v ∈ ends e ∧ ¬(ends e).IsDiag)
  simp only [bipartiteAbove, bipartiteBelow] at h
  simp only [incident]
  rw [h, mul_comm]
  refine sum_le_card_nsmul _ _ _ fun e _ => ?_
  calc #{v ∈ X | v ∈ ends e ∧ ¬(ends e).IsDiag} ≤ #(ends e).toFinset :=
        card_le_card fun v hv => Sym2.mem_toFinset.2 (mem_filter.1 hv).2.1
    _ ≤ 2 := by
        by_cases hd : (ends e).IsDiag
        · rw [Sym2.card_toFinset_of_isDiag _ hd]; norm_num
        · rw [Sym2.card_toFinset_of_not_isDiag _ hd]

omit [DecidableEq E] in
/-- The successful tests of a batch, after Cauchy–Schwarz: `∑ k (⌈log₂ d_v⌉ + 1) ≤ k √(8 n |B|)`
over the vertices with an edge (p. 16). -/
private theorem sum_testBound_le (ends : E → Sym2 V) (B : Finset E) (X : Finset V) (k : ℕ) :
    ((k * ∑ v ∈ active ends B X, (Nat.clog 2 #(incident ends B v) + 1) : ℕ) : ℝ) ≤
      k * √(8 * #X * #B) := by
  set A := active ends B X
  have hAX : A ⊆ X := filter_subset _ _
  have hdeg : ∀ v ∈ A, 1 ≤ #(incident ends B v) := fun v hv =>
    card_pos.2 (mem_filter.1 hv).2
  have hsum : (∑ v ∈ A, (#(incident ends B v) : ℝ)) ≤ 2 * #B := by
    exact_mod_cast (sum_le_sum_of_subset hAX).trans (sum_card_incident_le ends B X)
  have hcs := Real.sum_sqrt_mul_sqrt_le A (f := fun _ => (1 : ℝ))
    (g := fun v => (#(incident ends B v) : ℝ)) (fun _ => zero_le_one) (fun _ => by positivity)
  simp only [Real.sqrt_one, one_mul, sum_const, nsmul_eq_mul, mul_one] at hcs
  push_cast
  rw [mul_sum]
  calc ∑ v ∈ A, (k : ℝ) * ((Nat.clog 2 #(incident ends B v) : ℝ) + 1)
      ≤ ∑ v ∈ A, (k : ℝ) * (2 * √(#(incident ends B v) : ℝ)) := by
        refine sum_le_sum fun v hv => mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact_mod_cast clog_add_one_le_two_sqrt (hdeg v hv)
    _ = 2 * k * ∑ v ∈ A, √(#(incident ends B v) : ℝ) := by
        rw [mul_sum]; exact sum_congr rfl fun _ _ => by ring
    _ ≤ 2 * k * (√(#A : ℝ) * √(∑ v ∈ A, (#(incident ends B v) : ℝ))) :=
        mul_le_mul_of_nonneg_left hcs (by positivity)
    _ ≤ 2 * k * (√(#X : ℝ) * √(2 * #B)) := by
        gcongr
    _ = k * √(8 * #X * #B) := by
        have h1 : √((8 : ℝ) * #X * #B) = √((2 : ℝ) ^ 2) * (√(#X : ℝ) * √(2 * #B)) := by
          rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity)]; ring_nf
        rw [h1, Real.sqrt_sq (by norm_num)]; ring

/-! ### The batch -/

section Batch

variable {W : Type} [LinearOrder W] {w : E → W} {adm : E → Prop} [DecidablePred adm]
  {test : E → FreeM (LEQuery E) Bool} {msfSub : Finset E → FreeM (LEQuery E) (Finset E)}
  {r : ℕ} {st : State V E} {B : Finset E}

/-- The selections of the batch. -/
private noncomputable def selOf (test : E → FreeM (LEQuery E) Bool) (r : ℕ) (st : State V E)
    (B : Finset E) (o : {ι : Type} → LEQuery E ι → ι) : V → QuotaSelection E :=
  (selectAll test st.ends (r ^ 2) B (active st.ends B st.vertices).toList ∅).eval o

/-- The new portals of the batch. -/
private noncomputable def portalsOf (test : E → FreeM (LEQuery E) Bool) (r : ℕ)
    (st : State V E) (B : Finset E) (o : {ι : Type} → LEQuery E ι → ι) : Finset V :=
  portalCover st.vertices r (reached st.ends (selOf test r st B o))

/-- The spokes after the batch. -/
private noncomputable def spokesOf (test : E → FreeM (LEQuery E) Bool) (r : ℕ)
    (st : State V E) (B : Finset E) (o : {ι : Type} → LEQuery E ι → ι) : V → Option E :=
  (updateSpokes (candidate st.ends r (portalsOf test r st B o) (selOf test r st B o)) st.spoke
    st.vertices.toList).eval o

/-- The declared edges of the batch. -/
private noncomputable def declOf (test : E → FreeM (LEQuery E) Bool) (r : ℕ)
    (st : State V E) (B : Finset E) (o : {ι : Type} → LEQuery E ι → ι) : Finset E :=
  (active st.ends B st.vertices).biUnion fun v => (selOf test r st B o v).selected.toFinset

/-- The rejected edges of the batch. -/
private noncomputable def rejOf (test : E → FreeM (LEQuery E) Bool) (r : ℕ)
    (st : State V E) (B : Finset E) (o : {ι : Type} → LEQuery E ι → ι) : Finset E :=
  (active st.ends B st.vertices).biUnion fun v => (selOf test r st B o v).failed.toFinset

private theorem eval_batch (o : {ι : Type} → LEQuery E ι → ι) :
    (batch test msfSub r st B).eval o =
      { state := { st with
          portals := st.portals ∪ portalsOf test r st B o
          spoke := spokesOf test r st B o
          forest := (msfSub (st.forest ∪ declOf test r st B o)).eval o }
        declared := declOf test r st B o
        newPortals := portalsOf test r st B o
        rejected := rejOf test r st B o } := by
  simp only [batch, FreeM.eval_bind, FreeM.eval_pure, selOf, portalsOf, spokesOf, declOf, rejOf]

@[simp] theorem vertices_batch (o : {ι : Type} → LEQuery E ι → ι) :
    ((batch test msfSub r st B).eval o).state.vertices = st.vertices := by
  simp only [eval_batch]

@[simp] theorem ends_batch (o : {ι : Type} → LEQuery E ι → ι) :
    ((batch test msfSub r st B).eval o).state.ends = st.ends := by
  simp only [eval_batch]

/-- The portals after the batch are the old ones and the new ones. -/
theorem portals_batch (o : {ι : Type} → LEQuery E ι → ι) :
    ((batch test msfSub r st B).eval o).state.portals =
      st.portals ∪ ((batch test msfSub r st B).eval o).newPortals := by
  simp only [eval_batch]

/-- The forest after the batch is the answer of the exact minimum spanning forest call on the old
forest and the declared edges. -/
theorem forest_batch (o : {ι : Type} → LEQuery E ι → ι) :
    ((batch test msfSub r st B).eval o).state.forest =
      (msfSub (st.forest ∪ ((batch test msfSub r st B).eval o).declared)).eval o := by
  simp only [eval_batch]

/-- The new portals are vertices of the instance. -/
theorem newPortals_subset_batch (o : {ι : Type} → LEQuery E ι → ι) :
    ((batch test msfSub r st B).eval o).newPortals ⊆ st.vertices := by
  simp only [eval_batch, portalsOf]
  exact (portalCover_spec _ _ _).1

/-- **Lemma 3.2, the portals** ([KhannaPuttermanSong2026], §3.2, p. 15): at most `2n / r` new
portals, in the form `|P'| r ≤ 2n`, for every oracle. -/
theorem card_newPortals_batch_mul_le (o : {ι : Type} → LEQuery E ι → ι) :
    #((batch test msfSub r st B).eval o).newPortals * r ≤ 2 * #st.vertices := by
  simp only [eval_batch, portalsOf]
  exact (portalCover_spec _ _ _).2

/-! ### With the oracle of the weights -/

private theorem sel_spec (hw : Function.Injective w)
    (htest : ∀ e, (test e).eval (LEQuery.keyOracle w) = decide (adm e)) (r : ℕ)
    (st : State V E) (B : Finset E) :
    (∀ v, SelFacts st.ends B (r ^ 2) adm v (selOf test r st B (LEQuery.keyOracle w) v)) ∧
    (∀ v ∉ active st.ends B st.vertices, selOf test r st B (LEQuery.keyOracle w) v = ⟨[], []⟩) ∧
    (∀ v ∈ active st.ends B st.vertices, ∃ Rv ⊆ rejOf test r st B (LEQuery.keyOracle w),
      selOf test r st B (LEQuery.keyOracle w) v =
        (quotaSelect (fun e => otherEnd v (st.ends e)) (r ^ 2)
          (incident st.ends B v \ Rv).toList).eval (CmpTestQuery.oracleOf w adm)) ∧
    ∑ v ∈ active st.ends B st.vertices, (selOf test r st B (LEQuery.keyOracle w) v).failed.length =
      #(rejOf test r st B (LEQuery.keyOracle w)) := by
  obtain ⟨h1, h2, -, h4⟩ := selectAll_spec (adm := adm) hw htest st.ends (r ^ 2) B
    (active st.ends B st.vertices).toList (nodup_toList _) ∅
  simp only [toList_toFinset, empty_union, mem_toList] at h1 h2 h4
  refine ⟨fun v => ?_, h1, h2, h4⟩
  by_cases hv : v ∈ active st.ends B st.vertices
  · obtain ⟨Rv, -, hRv⟩ := h2 v hv
    simp only [selOf]
    rw [hRv]
    exact selFacts_quotaSelect hw _ _ _ _ _
  · simp only [selOf]
    rw [h1 v hv]
    exact selFacts_empty _ _ _ _

private theorem mem_declOf {o : {ι : Type} → LEQuery E ι → ι} {v : V} {c : E}
    (hc : c ∈ (selOf test r st B o v).selected)
    (hne : ∀ v ∉ active st.ends B st.vertices, selOf test r st B o v = ⟨[], []⟩) :
    c ∈ declOf test r st B o := by
  by_cases hv : v ∈ active st.ends B st.vertices
  · exact mem_biUnion.2 ⟨v, hv, List.mem_toFinset.2 hc⟩
  · rw [hne v hv] at hc; simp at hc

/-- The declared edges are edges of the batch. -/
theorem declared_subset_batch (hw : Function.Injective w)
    (htest : ∀ e, (test e).eval (LEQuery.keyOracle w) = decide (adm e)) :
    ((batch test msfSub r st B).eval (LEQuery.keyOracle w)).declared ⊆ B := by
  obtain ⟨hf, -⟩ := sel_spec hw htest r st B
  simp only [eval_batch, declOf]
  intro e he
  obtain ⟨v, -, hv⟩ := mem_biUnion.1 he
  exact (mem_incident.1 ((hf v).selected e (List.mem_toFinset.1 hv)).1).1

/-- The declared edges are admissible: each passed its test. -/
theorem adm_of_mem_declared_batch (hw : Function.Injective w)
    (htest : ∀ e, (test e).eval (LEQuery.keyOracle w) = decide (adm e)) {e : E}
    (he : e ∈ ((batch test msfSub r st B).eval (LEQuery.keyOracle w)).declared) : adm e := by
  obtain ⟨hf, -⟩ := sel_spec hw htest r st B
  simp only [eval_batch, declOf] at he
  obtain ⟨v, -, hv⟩ := mem_biUnion.1 he
  exact ((hf v).selected e (List.mem_toFinset.1 hv)).2

/-- **Lemma 3.2, the declared edges** ([KhannaPuttermanSong2026], §3.2, p. 15): each vertex
declares at most `k = r²` edges, so `|D| ≤ k n`. -/
theorem card_declared_batch_le (hw : Function.Injective w)
    (htest : ∀ e, (test e).eval (LEQuery.keyOracle w) = decide (adm e)) :
    #((batch test msfSub r st B).eval (LEQuery.keyOracle w)).declared ≤ r ^ 2 * #st.vertices := by
  obtain ⟨hf, -⟩ := sel_spec hw htest r st B
  simp only [eval_batch, declOf]
  calc _ ≤ ∑ v ∈ active st.ends B st.vertices,
        #(selOf test r st B (LEQuery.keyOracle w) v).selected.toFinset := card_biUnion_le
    _ ≤ ∑ _v ∈ active st.ends B st.vertices, r ^ 2 :=
        sum_le_sum fun v _ => (List.toFinset_card_le _).trans (hf v).length_le
    _ ≤ r ^ 2 * #st.vertices := by
        rw [sum_const, smul_eq_mul, mul_comm]
        exact Nat.mul_le_mul_left _ (card_filter_le _ _)

/-- The rejected edges `R'` are edges of the batch. -/
theorem rejected_subset_batch (hw : Function.Injective w)
    (htest : ∀ e, (test e).eval (LEQuery.keyOracle w) = decide (adm e)) :
    ((batch test msfSub r st B).eval (LEQuery.keyOracle w)).rejected ⊆ B := by
  obtain ⟨hf, -⟩ := sel_spec hw htest r st B
  simp only [eval_batch, rejOf]
  intro e he
  obtain ⟨v, -, hv⟩ := mem_biUnion.1 he
  exact (mem_incident.1 ((hf v).failed e (List.mem_toFinset.1 hv)).1).1

/-- The rejected edges `R'` are inadmissible: each failed its test. -/
theorem not_adm_of_mem_rejected_batch (hw : Function.Injective w)
    (htest : ∀ e, (test e).eval (LEQuery.keyOracle w) = decide (adm e)) {e : E}
    (he : e ∈ ((batch test msfSub r st B).eval (LEQuery.keyOracle w)).rejected) : ¬adm e := by
  obtain ⟨hf, -⟩ := sel_spec hw htest r st B
  simp only [eval_batch, rejOf] at he
  obtain ⟨v, -, hv⟩ := mem_biUnion.1 he
  exact ((hf v).failed e (List.mem_toFinset.1 hv)).2

private theorem candidate_some {ends : E → Sym2 V} {P' : Finset V} {sel : V → QuotaSelection E}
    {v : V} {c : E} (h : candidate ends r P' sel v = some c) :
    c ∈ (sel v).selected ∧ otherEnd v (ends c) ∈ P' := by
  unfold candidate at h
  split at h
  · exact ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩
  · simp at h

/-- A spoke after the batch is the old spoke or a declared edge, at a vertex of the instance. -/
private theorem spokesOf_cases {o : {ι : Type} → LEQuery E ι → ι} {v : V} {s : E}
    (h : spokesOf test r st B o v = some s) :
    st.spoke v = some s ∨ (v ∈ st.vertices ∧
      candidate st.ends r (portalsOf test r st B o) (selOf test r st B o) v = some s) := by
  simp only [spokesOf, eval_updateSpokes, mem_toList] at h
  split at h
  · next hv =>
    rcases hc : candidate st.ends r (portalsOf test r st B o) (selOf test r st B o) v with _ | c
    · rw [hc] at h; exact Or.inl h
    · rcases hs : st.spoke v with _ | s₀
      · rw [hc, hs] at h; simp only [offerSpoke, FreeM.eval_pure] at h
        exact Or.inr ⟨hv, h ▸ rfl⟩
      · rw [hc, hs] at h
        simp only [offerSpoke, FreeM.eval_bind, LEQuery.eval_ask] at h
        by_cases ho : o (LEQuery.le c s₀) = true
        · simp only [ho, ↓reduceIte, FreeM.eval_pure] at h; exact Or.inr ⟨hv, h⟩
        · simp only [ho, Bool.false_eq_true, ↓reduceIte, FreeM.eval_pure] at h; exact Or.inl h
  · exact Or.inl h

/-- **Spokes are never removed and only get lighter** (used in Lemma 3.7, p. 18: "`p(e')` can only
decrease"). -/
theorem spoke_batch_le {v : V} {s : E} (hs : st.spoke v = some s) :
    ∃ s', ((batch test msfSub r st B).eval (LEQuery.keyOracle w)).state.spoke v = some s' ∧
      w s' ≤ w s := by
  simp only [eval_batch, spokesOf, eval_updateSpokes]
  split
  · exact (offerSpoke_spec _ _).1 s hs
  · exact ⟨s, hs, le_rfl⟩

/-- **New spokes are declared edges** (Claim 3.6, p. 17: "spokes can only arise from declared
edges `D`"). A spoke after the batch is the old spoke of the vertex or a declared edge. -/
theorem spoke_batch_eq_or_mem_declared (hw : Function.Injective w)
    (htest : ∀ e, (test e).eval (LEQuery.keyOracle w) = decide (adm e)) {v : V} {s : E}
    (hs : ((batch test msfSub r st B).eval (LEQuery.keyOracle w)).state.spoke v = some s) :
    st.spoke v = some s ∨ s ∈ ((batch test msfSub r st B).eval (LEQuery.keyOracle w)).declared := by
  obtain ⟨-, hne, -⟩ := sel_spec hw htest r st B
  simp only [eval_batch] at hs ⊢
  rcases spokesOf_cases hs with h | ⟨-, h⟩
  · exact Or.inl h
  · exact Or.inr (mem_declOf (candidate_some h).1 hne)

/-- The neighbours reached by selected edges are vertices of the instance. -/
private theorem reached_subset (hw : Function.Injective w)
    (htest : ∀ e, (test e).eval (LEQuery.keyOracle w) = decide (adm e))
    (hB : ∀ e ∈ B, ∀ v ∈ st.ends e, v ∈ st.vertices) (v : V) :
    reached st.ends (selOf test r st B (LEQuery.keyOracle w)) v ⊆ st.vertices := by
  obtain ⟨hf, -⟩ := sel_spec hw htest r st B
  intro x hx
  obtain ⟨c, hc, rfl⟩ := mem_image.1 hx
  obtain ⟨hcB, hvc, -⟩ := mem_incident.1 ((hf v).selected c (List.mem_toFinset.1 hc)).1
  exact hB c hcB _ (otherEnd_mem hvc)

/-- **The guarantee at one end of an edge** (proof of Lemma 3.2, p. 15). Let `e ∈ B \ R'` have
ends `x ≠ y`. Either `x` declared an edge to `y` no heavier than `e`, or `x` selected `k` edges, all
lighter than `e`, and so has a spoke after the batch no heavier than `e`. -/
private theorem endpoint_guarantee (hw : Function.Injective w)
    (htest : ∀ e, (test e).eval (LEQuery.keyOracle w) = decide (adm e)) (hr : 0 < r)
    (hB : ∀ e ∈ B, ∀ v ∈ st.ends e, v ∈ st.vertices) {e : E} (he : e ∈ B)
    (heR : e ∉ rejOf test r st B (LEQuery.keyOracle w)) {x y : V} (hxy : st.ends e = s(x, y))
    (hne : x ≠ y) :
    (∃ c ∈ declOf test r st B (LEQuery.keyOracle w), st.ends c = s(x, y) ∧ w c ≤ w e) ∨
      ∃ s', spokesOf test r st B (LEQuery.keyOracle w) x = some s' ∧ w s' ≤ w e := by
  obtain ⟨hf, hempty, hq, -⟩ := sel_spec hw htest r st B
  set sel := selOf test r st B (LEQuery.keyOracle w)
  have hxX : x ∈ st.vertices := hB e he x (by rw [hxy]; exact Sym2.mem_mk_left _ _)
  have hdiag : ¬(st.ends e).IsDiag := by rw [hxy, Sym2.mk_isDiag_iff]; exact hne
  have heinc : e ∈ incident st.ends B x :=
    mem_incident.2 ⟨he, by rw [hxy]; exact Sym2.mem_mk_left _ _, hdiag⟩
  have hxA : x ∈ active st.ends B st.vertices := mem_filter.2 ⟨hxX, ⟨e, heinc⟩⟩
  obtain ⟨Rx, hRx, hselx⟩ := hq x hxA
  have hnd := nodup_toList (incident st.ends B x \ Rx)
  have hemem : e ∈ (incident st.ends B x \ Rx).toList :=
    mem_toList.2 (mem_sdiff.2 ⟨heinc, fun h => heR (hRx h)⟩)
  have hfail : e ∉ (sel x).failed := fun h =>
    heR (mem_biUnion.2 ⟨x, hxA, List.mem_toFinset.2 h⟩)
  rw [hselx] at hfail
  obtain ⟨g1, g2⟩ := quotaSelect_guarantee (fun e => otherEnd x (st.ends e)) hw hnd hemem hfail
  rw [← hselx] at g1 g2
  have hge : otherEnd x (st.ends e) = y := by rw [hxy, otherEnd_mk]
  have hends : ∀ c ∈ (sel x).selected, st.ends c = s(x, otherEnd x (st.ends c)) := fun c hc =>
    (mk_otherEnd (mem_incident.1 ((hf x).selected c hc).1).2.1).symm
  by_cases hc : ∃ c ∈ (sel x).selected, otherEnd x (st.ends c) = y
  · obtain ⟨c, hc, hcy⟩ := hc
    refine Or.inl ⟨c, mem_declOf hc hempty, by rw [hends c hc, hcy], g1 c hc (hcy.trans hge.symm)⟩
  · push Not at hc
    obtain ⟨hlen, hlt⟩ := g2 fun c hc' h => hc c hc' (h.trans hge)
    -- `x` reached `k` neighbours
    have hreach : #(reached st.ends sel x) = r ^ 2 := by
      rw [reached, card_image_of_injOn, List.toFinset_card_of_nodup (hf x).nodup, hlen]
      intro c hc c' hc' h
      exact (hf x).inj c (List.mem_toFinset.1 hc) c' (List.mem_toFinset.1 hc') h
    obtain ⟨p, hp⟩ := portalCover_hits hr (fun v _ => reached_subset hw htest hB v) hxX hreach
    obtain ⟨hpP, hpS⟩ := mem_inter.1 hp
    obtain ⟨c', hc', rfl⟩ := mem_image.1 hpS
    -- so it has a candidate spoke
    obtain ⟨c, hcand⟩ : ∃ c, candidate st.ends r (portalsOf test r st B (LEQuery.keyOracle w))
        sel x = some c := by
      unfold candidate
      simp only [hreach, ↓reduceIte]
      rcases hfind : (sel x).selected.find? fun e => decide
          (otherEnd x (st.ends e) ∈ portalsOf test r st B (LEQuery.keyOracle w)) with _ | c
      · have := List.find?_eq_none.1 hfind c' (List.mem_toFinset.1 hc')
        simp only [portalsOf] at this
        exact absurd (decide_eq_true hpP) this
      · exact ⟨c, rfl⟩
    have hcw := hlt c (candidate_some hcand).1
    simp only [spokesOf, eval_updateSpokes, mem_toList, hxX, ↓reduceIte]
    obtain ⟨s', hs', hle⟩ := (offerSpoke_spec (w := w) _ (st.spoke x)).2.1 c hcand
    exact Or.inr ⟨s', hs', hle.trans hcw.le⟩

/-- **Lemma 3.2, the guarantee** ([KhannaPuttermanSong2026], §3.2, p. 15). Let `R'` be the edges
that failed a test. After the forest is replaced by `MSF(F ∪ D)`, every edge `e ∈ B \ R'` with ends
`u, v` is supported by the new forest, or both of its ends have spokes and
`p(e) = max (w σ(u)) (w σ(v)) ≤ w e`. The exact minimum spanning forest call is assumed to return
`msf (F ∪ D)` (`hmsf`). -/
theorem supported_or_spokes_batch (hw : Function.Injective w)
    (htest : ∀ e, (test e).eval (LEQuery.keyOracle w) = decide (adm e)) (hr : 0 < r)
    (hB : ∀ e ∈ B, ∀ v ∈ st.ends e, v ∈ st.vertices)
    (hmsf : (msfSub (st.forest ∪ ((batch test msfSub r st B).eval
        (LEQuery.keyOracle w)).declared)).eval (LEQuery.keyOracle w) =
      msf st.ends w (st.forest ∪ ((batch test msfSub r st B).eval (LEQuery.keyOracle w)).declared))
    {e : E} (he : e ∈ B)
    (heR : e ∉ ((batch test msfSub r st B).eval (LEQuery.keyOracle w)).rejected) {u v : V}
    (huv : st.ends e = s(u, v)) :
    Supported st.ends w ↑((batch test msfSub r st B).eval (LEQuery.keyOracle w)).state.forest e ∨
      ∃ su sv, ((batch test msfSub r st B).eval (LEQuery.keyOracle w)).state.spoke u = some su ∧
        ((batch test msfSub r st B).eval (LEQuery.keyOracle w)).state.spoke v = some sv ∧
        max (w su) (w sv) ≤ w e := by
  rw [forest_batch, hmsf]
  simp only [eval_batch] at heR ⊢
  set D := declOf test r st B (LEQuery.keyOracle w)
  rw [supported_iff w huv]
  -- a declared edge `c` with ends `u, v`, no heavier than `e`, makes `e` supported
  have hsupp : ∀ c ∈ D, st.ends c = s(u, v) → w c ≤ w e →
      Joins st.ends {f | f ∈ msf st.ends w (st.forest ∪ D) ∧ w f ≤ w e} u v := fun c hc hcuv hce =>
    joins_msf_of_joins w (X := ↑(st.forest ∪ D)) subset_rfl
      (Joins.of_mem ⟨mem_union_right _ hc, hce⟩ hcuv)
  by_cases huv' : u = v
  · subst huv'; exact Or.inl (Joins.refl _)
  rcases endpoint_guarantee hw htest hr hB he heR huv huv' with ⟨c, hc, hcuv, hce⟩ | ⟨su, hsu, hsue⟩
  · exact Or.inl (hsupp c hc hcuv hce)
  rcases endpoint_guarantee hw htest hr hB he heR (huv.trans Sym2.eq_swap) (Ne.symm huv') with
    ⟨c, hc, hcvu, hce⟩ | ⟨sv, hsv, hsve⟩
  · exact Or.inl (hsupp c hc (hcvu.trans Sym2.eq_swap) hce)
  · exact Or.inr ⟨su, sv, hsu, hsv, max_le hsue hsve⟩

omit [DecidableEq V] [DecidableEq E] in
private theorem supported_mono {ends : E → Sym2 V} {S T : Set E} (hST : S ⊆ T) {e : E}
    (h : Supported ends w S e) : Supported ends w T e := by
  obtain ⟨⟨a, b⟩, hab⟩ := Quot.exists_rep (ends e)
  rw [supported_iff w hab.symm] at h ⊢
  refine h.mono ?_
  rintro f ⟨hf, hfe⟩
  exact ⟨hST hf, hfe⟩

omit [DecidableEq V] [DecidableEq E] in
private theorem supported_of_mem {ends : E → Sym2 V} {S : Set E} {e : E} (he : e ∈ S) :
    Supported ends w S e := by
  obtain ⟨⟨a, b⟩, hab⟩ := Quot.exists_rep (ends e)
  rw [supported_iff w hab.symm]
  exact Joins.of_mem ⟨he, le_rfl⟩ hab.symm

/-- **The batch preserves the invariant of the state** (§3.3, pp. 17–18). The new forest
`MSF(F ∪ D)` is an acyclic set of admissible edges, since declared edges passed their tests; the
new portals are vertices; a new spoke is a declared edge from its vertex to a new portal; and
every spoke, old or new, is supported by `MSF(F ∪ D)` by Fact 2.5, since old spokes were supported
by `F` and new ones are in `D`. The exact minimum spanning forest call is assumed to return
`msf (F ∪ D)` (`hmsf`). -/
theorem State.Invariant.batch (h : st.Invariant w adm) (hw : Function.Injective w)
    (htest : ∀ e, (test e).eval (LEQuery.keyOracle w) = decide (adm e))
    (hB : ∀ e ∈ B, ∀ v ∈ st.ends e, v ∈ st.vertices)
    (hmsf : (msfSub (st.forest ∪ ((Certificate.batch test msfSub r st B).eval
        (LEQuery.keyOracle w)).declared)).eval (LEQuery.keyOracle w) =
      msf st.ends w (st.forest ∪
        ((Certificate.batch test msfSub r st B).eval (LEQuery.keyOracle w)).declared)) :
    ((Certificate.batch test msfSub r st B).eval (LEQuery.keyOracle w)).state.Invariant w adm := by
  obtain ⟨hf, -⟩ := sel_spec hw htest r st B
  have hDB := declared_subset_batch (msfSub := msfSub) (r := r) (st := st) (B := B) hw htest
  have hDadm : ∀ e ∈ ((Certificate.batch test msfSub r st B).eval (LEQuery.keyOracle w)).declared,
      adm e :=
    fun e he => adm_of_mem_declared_batch hw htest he
  simp only [eval_batch] at hmsf hDB hDadm ⊢
  set D := declOf test r st B (LEQuery.keyOracle w)
  refine ⟨fun f hf' x hx => ?_, ?_, fun f hf' => ?_, ?_, fun v s hs => ?_, fun v s hs => ?_,
    fun v s hs => ?_, fun v s hs => ?_⟩
  · simp only [hmsf] at hf'
    rcases mem_union.1 (msf_subset w hf') with hF | hD
    · exact h.forest_ends f hF x hx
    · exact hB f (hDB hD) x hx
  · simp only [hmsf]
    exact isAcyclic_msf w hw
  · simp only [hmsf] at hf'
    rcases mem_union.1 (msf_subset w hf') with hF | hD
    · exact h.forest_adm f hF
    · exact hDadm f hD
  · exact union_subset h.portals_subset (portalCover_spec _ _ _).1
  · rcases spokesOf_cases hs with h' | ⟨hv, -⟩
    · exact h.mem_vertices_of_spoke v s h'
    · exact hv
  · rcases spokesOf_cases hs with h' | ⟨-, hc⟩
    · exact h.mem_ends_spoke v s h'
    · exact (mem_incident.1 ((hf v).selected s (candidate_some hc).1).1).2.1
  · rw [State.proj_of_spoke_eq_some hs]
    rcases spokesOf_cases hs with h' | ⟨-, hc⟩
    · have := h.proj_mem_portals v s h'
      rw [State.proj_of_spoke_eq_some h'] at this
      exact mem_union_left _ this
    · exact mem_union_right _ (candidate_some hc).2
  · simp only [hmsf]
    rw [supported_msf_iff]
    rcases spokesOf_cases hs with h' | ⟨-, hc⟩
    · exact supported_mono (fun f hf' => mem_union_left _ hf') (h.spoke_supported v s h')
    · obtain ⟨-, hne, -⟩ := sel_spec hw htest r st B
      exact supported_of_mem (mem_union_right _ (mem_declOf (candidate_some hc).1 hne))

/-- **Comparisons of the batch** ([KhannaPuttermanSong2026], §3.2, p. 16). Let each test cost at
most `cs` comparisons when it succeeds and `cf` when it fails. Then the batch makes at most
`468 |B| + n` comparisons outside the tests and the exact minimum spanning forest call (quota
selection at every vertex, and one comparison per vertex for the spokes), at most `r² √(8 n |B|)`
successful tests (`∑_v k (⌈log₂ deg_B v⌉ + 1)` over the vertices with an edge, by Cauchy–Schwarz),
at most `|R'|` failed tests (an edge that failed is not tested again), and the one exact call,
on `F ∪ D`. -/
theorem countQueries_batch_le (hw : Function.Injective w)
    (htest : ∀ e, (test e).eval (LEQuery.keyOracle w) = decide (adm e)) {cs cf : ℕ}
    (hcs : ∀ e, adm e → (test e).countQueries (LEQuery.keyOracle w) ≤ cs)
    (hcf : ∀ e, ¬adm e → (test e).countQueries (LEQuery.keyOracle w) ≤ cf) :
    ((batch test msfSub r st B).countQueries (LEQuery.keyOracle w) : ℝ) ≤
      468 * #B + #st.vertices + cs * (r ^ 2 * √(8 * #st.vertices * #B)) +
        cf * #((batch test msfSub r st B).eval (LEQuery.keyOracle w)).rejected +
        (msfSub (st.forest ∪ ((batch test msfSub r st B).eval
          (LEQuery.keyOracle w)).declared)).countQueries (LEQuery.keyOracle w) := by
  set A := active st.ends B st.vertices
  have hdec : (batch test msfSub r st B).countQueries (LEQuery.keyOracle w) =
      (selectAll test st.ends (r ^ 2) B A.toList ∅).countQueries (LEQuery.keyOracle w) +
        ((updateSpokes (candidate st.ends r (portalsOf test r st B (LEQuery.keyOracle w))
          (selOf test r st B (LEQuery.keyOracle w))) st.spoke st.vertices.toList).countQueries
            (LEQuery.keyOracle w) +
        (msfSub (st.forest ∪ declOf test r st B (LEQuery.keyOracle w))).countQueries
          (LEQuery.keyOracle w)) := by
    simp only [batch, FreeM.countQueries_bind, FreeM.countQueries_pure, add_zero, selOf,
      portalsOf, declOf, A]
  have hsel := countQueries_selectAll_le htest hcs hcf st.ends (r ^ 2) B A.toList
    (nodup_toList _) ∅
  simp only [toList_toFinset] at hsel
  rw [sum_add_distrib, sum_add_distrib, ← mul_sum, ← mul_sum, ← mul_sum, ← mul_sum] at hsel
  obtain ⟨-, -, -, hrej⟩ := sel_spec hw htest r st B
  change _ ≤ _ + _ + cf * ∑ v ∈ A, (selOf test r st B (LEQuery.keyOracle w) v).failed.length
    at hsel
  rw [hrej] at hsel
  have hspk := countQueries_updateSpokes_le (LEQuery.keyOracle w)
    (candidate st.ends r (portalsOf test r st B (LEQuery.keyOracle w))
      (selOf test r st B (LEQuery.keyOracle w))) st.spoke st.vertices.toList
  rw [length_toList] at hspk
  have hdeg : (∑ v ∈ A, #(incident st.ends B v) : ℝ) ≤ 2 * #B := by
    exact_mod_cast (sum_le_sum_of_subset (filter_subset _ _)).trans
      (sum_card_incident_le st.ends B st.vertices)
  have htb := sum_testBound_le st.ends B st.vertices (r ^ 2)
  simp only [eval_batch]
  rw [hdec]
  have hsel' : ((selectAll test st.ends (r ^ 2) B A.toList ∅).countQueries
      (LEQuery.keyOracle w) : ℝ) ≤ 234 * ∑ v ∈ A, (#(incident st.ends B v) : ℝ) +
        cs * ((r ^ 2 * ∑ v ∈ A, (Nat.clog 2 #(incident st.ends B v) + 1) : ℕ) : ℝ) +
        cf * #(rejOf test r st B (LEQuery.keyOracle w)) := by
    exact_mod_cast hsel
  have hcs0 : (0 : ℝ) ≤ cs := Nat.cast_nonneg _
  have := mul_le_mul_of_nonneg_left htb hcs0
  push_cast at this hsel' ⊢
  have hspk' : ((updateSpokes (candidate st.ends r (portalsOf test r st B (LEQuery.keyOracle w))
      (selOf test r st B (LEQuery.keyOracle w))) st.spoke st.vertices.toList).countQueries
        (LEQuery.keyOracle w) : ℝ) ≤ #st.vertices := by exact_mod_cast hspk
  linarith

end Batch

end Cslib.Query.Certificate
