/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Algorithms.Lean.Query.MinimumSpanningForest.Certificate.Batch
import Mathlib.Tactic.FinCases

/-!
# Tests for the batch processing of the certificate procedure

One batch on three vertices `0, 1, 2` with four edges, weighted by their index:

* edges `0` and `1` are parallel, between `0` and `1`, so they fall in one group at each end;
* edge `2` joins `0` and `2` and is inadmissible;
* edge `3` is a self-loop at `1`.

With `r = 7` every vertex has fewer than `k = 49` groups. The batch starts from the initial state,
with tests that answer correctly at no cost and an exact minimum spanning forest call that returns
`msf`, so every hypothesis of Lemma 3.2 and of the invariant holds. Since `|P'| r ≤ 2n` forces
`P' = ∅`, no vertex can get a spoke, and Lemma 3.2 then says that every edge of `B \ R'` is
supported by the new forest: the heavier parallel edge `1`, the self-loop `3`, and edge `2` unless
it failed its test. The comparison bound is instantiated with `cs = cf = 0`.

A second batch, with `r = 1` (`k = 1`), exercises the spoke branch. On the path `2 — 0 — 1 — 3`
with edges `0 = {0, 2}`, `1 = {1, 3}` and `2 = {0, 1}`, weighted by their index, each vertex
selects only its lightest edge, so the heaviest edge `2` is not declared
(`Cslib.Query.Certificate.exists_end_card_lt_of_mem_declared_batch`). It is then not supported by
the new forest, and Lemma 3.2 gives both of its ends spokes no heavier than it: vertex `0` gets the
spoke `0` to the new portal `2`, and vertex `1` the spoke `1` to the new portal `3`.
-/

namespace CslibFrontierTests.MSFCertificateBatch

open Cslib Cslib.Query Cslib.Query.Certificate Cslib.Multigraph Finset

/-- The ends of the four edges. -/
def ends : Fin 4 → Sym2 (Fin 3)
  | 0 => s(0, 1)
  | 1 => s(0, 1)
  | 2 => s(0, 2)
  | 3 => s(1, 1)

/-- Weights: the index of the edge. -/
def w : Fin 4 → ℕ := Fin.val

/-- Every edge but `2` is admissible. -/
def adm (e : Fin 4) : Prop := e ≠ 2

instance : DecidablePred adm := fun e => inferInstanceAs (Decidable (e ≠ 2))

/-- The admissibility test, answering without comparisons. -/
def test (e : Fin 4) : FreeM (LEQuery (Fin 4)) Bool := pure (decide (adm e))

/-- The exact minimum spanning forest call, answering without comparisons. -/
noncomputable def msfSub (S : Finset (Fin 4)) : FreeM (LEQuery (Fin 4)) (Finset (Fin 4)) :=
  pure (msf ends w S)

/-- The initial state on the three vertices. -/
abbrev st : State (Fin 3) (Fin 4) := State.init univ ends

/-- The run of the batch of all four edges, with `r = 7`. -/
noncomputable abbrev res : BatchResult (Fin 3) (Fin 4) :=
  (batch test msfSub 7 st univ).eval (LEQuery.keyOracle w)

theorem hw : Function.Injective w := Fin.val_injective

theorem htest (e : Fin 4) : (test e).eval (LEQuery.keyOracle w) = decide (adm e) := rfl

theorem hB : ∀ e ∈ (univ : Finset (Fin 4)), ∀ v ∈ st.ends e, v ∈ st.vertices := by
  simp [st]

theorem hmsf :
    (msfSub (st.forest ∪ res.declared)).eval (LEQuery.keyOracle w) =
      msf st.ends w (st.forest ∪ res.declared) := rfl

/-- `|P'| r ≤ 2n` with `r = 7 > 2n = 6` leaves no new portals. -/
theorem newPortals_eq : res.newPortals = ∅ := by
  have h : #res.newPortals * 7 ≤ 2 * #st.vertices := card_newPortals_batch_mul_le _
  have h3 : #st.vertices = 3 := by simp
  exact card_eq_zero.1 (by omega)

/-- So no vertex has a spoke after the batch. -/
theorem spoke_eq_none (v : Fin 3) : res.state.spoke v = none := by
  have hinv : res.state.Invariant w adm :=
    (State.invariant_init univ ends w adm).batch hw htest hB hmsf
  rcases hs : res.state.spoke v with _ | s
  · rfl
  · have := hinv.proj_mem_portals v s hs
    rw [portals_batch, newPortals_eq] at this
    simp at this

/-- Every edge of the batch outside `R'` is supported by the new forest. -/
theorem supported_of_notMem_rejected {e : Fin 4} (he : e ∉ res.rejected) {u v : Fin 3}
    (huv : ends e = s(u, v)) : Supported ends w ↑res.state.forest e := by
  rcases supported_or_spokes_batch (test := test) (msfSub := msfSub) (st := st) hw htest
    (by norm_num) hB hmsf (mem_univ e) he huv with h | ⟨su, -, hsu, -⟩
  · exact h
  · exact absurd ((spoke_eq_none u).symm.trans hsu) (by simp)

/-- Admissible edges are never rejected. -/
theorem notMem_rejected {e : Fin 4} (he : adm e) : e ∉ res.rejected := fun h =>
  not_adm_of_mem_rejected_batch hw htest h he

/-- The heavier of two parallel edges is supported, through the lighter one. -/
example : Supported ends w ↑res.state.forest 1 :=
  supported_of_notMem_rejected (notMem_rejected (by decide)) rfl

/-- The self-loop is supported. -/
example : Supported ends w ↑res.state.forest 3 :=
  supported_of_notMem_rejected (notMem_rejected (by decide)) rfl

/-- The inadmissible edge failed its test or is supported. -/
example : 2 ∈ res.rejected ∨ Supported ends w ↑res.state.forest 2 := by
  by_cases h : (2 : Fin 4) ∈ res.rejected
  · exact Or.inl h
  · exact Or.inr (supported_of_notMem_rejected h rfl)

/-- The comparison bound, with tests free of comparisons (`cs = cf = 0`). -/
example : ((batch test msfSub 7 st univ).countQueries (LEQuery.keyOracle w) : ℝ) ≤
    468 * #(univ : Finset (Fin 4)) + #st.vertices +
      ((0 : ℕ) : ℝ) * (7 ^ 2 * √(8 * #st.vertices * #(univ : Finset (Fin 4)))) +
      ((0 : ℕ) : ℝ) * #res.rejected +
      (msfSub (st.forest ∪ res.declared)).countQueries (LEQuery.keyOracle w) :=
  countQueries_batch_le hw htest (fun _ _ => le_of_eq rfl) (fun _ _ => le_of_eq rfl)

/-! ### A batch with `k = 1`, where vertices get spokes -/

namespace Spokes

/-- The path `2 — 0 — 1 — 3`. -/
def ends : Fin 3 → Sym2 (Fin 4)
  | 0 => s(0, 2)
  | 1 => s(1, 3)
  | 2 => s(0, 1)

/-- Weights: the index of the edge. -/
def w : Fin 3 → ℕ := Fin.val

/-- Every edge is admissible. -/
def adm (_ : Fin 3) : Prop := True

instance : DecidablePred adm := fun _ => inferInstanceAs (Decidable True)

/-- The admissibility test, answering without comparisons. -/
def test (e : Fin 3) : FreeM (LEQuery (Fin 3)) Bool := pure (decide (adm e))

/-- The exact minimum spanning forest call, answering without comparisons. -/
noncomputable def msfSub (S : Finset (Fin 3)) : FreeM (LEQuery (Fin 3)) (Finset (Fin 3)) :=
  pure (msf ends w S)

/-- The initial state on the four vertices. -/
abbrev st : State (Fin 4) (Fin 3) := State.init univ ends

/-- The run of the batch of all three edges, with `r = 1`. -/
noncomputable abbrev res : BatchResult (Fin 4) (Fin 3) :=
  (batch test msfSub 1 st univ).eval (LEQuery.keyOracle w)

theorem hw : Function.Injective w := Fin.val_injective

theorem htest (e : Fin 3) : (test e).eval (LEQuery.keyOracle w) = decide (adm e) := rfl

theorem hB : ∀ e ∈ (univ : Finset (Fin 3)), ∀ v ∈ st.ends e, v ∈ st.vertices := by
  simp [st]

theorem hmsf :
    (msfSub (st.forest ∪ res.declared)).eval (LEQuery.keyOracle w) =
      msf st.ends w (st.forest ∪ res.declared) := rfl

theorem hinv : res.state.Invariant w adm :=
  (State.invariant_init univ ends w adm).batch hw htest hB hmsf

/-- With quota `1`, each end of edge `2` has a lighter edge to another neighbour, so edge `2` is
not declared. -/
theorem two_notMem_declared : (2 : Fin 3) ∉ res.declared := by
  intro h
  obtain ⟨v, hv, hT⟩ := exists_end_card_lt_of_mem_declared_batch hw htest h
  have hv' : v = 0 ∨ v = 1 := by simpa [st, ends] using hv
  rcases hv' with rfl | rfl
  · have := hT {0} (subset_univ _) (by simp [st, ends, adm, w])
      (by rw [coe_singleton]; exact Set.injOn_singleton _ _)
    simp at this
  · have := hT {1} (subset_univ _) (by simp [st, ends, adm, w])
      (by rw [coe_singleton]; exact Set.injOn_singleton _ _)
    simp at this

/-- So edge `2` is not supported by the new forest: no other edge crosses between `{0, 2}` and
`{1, 3}`. -/
theorem two_not_supported : ¬Supported ends w ↑res.state.forest 2 := by
  rw [supported_iff w (show ends 2 = s(0, 1) from rfl)]
  intro hj
  obtain ⟨f, ⟨hfF, -⟩, hcut⟩ := hj.exists_mem_edgeCut (P := {0, 2}) (by simp) (by simp)
  rw [forest_batch, hmsf] at hfF
  have hf2 : f ≠ 2 := by
    rintro rfl
    exact two_notMem_declared (by simpa [st] using msf_subset w hfF)
  obtain ⟨a, b, hab, ha, hb⟩ := Graph.mem_edgeCut_iff.1 hcut
  change ends f = s(a, b) at hab
  fin_cases f
  · simp only [ends, Sym2.eq_iff] at hab
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp at ha hb
  · simp only [ends, Sym2.eq_iff] at hab
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp at ha hb
  · exact hf2 rfl

/-- Lemma 3.2 gives both ends of edge `2` spokes no heavier than it. -/
theorem spokes : ∃ su sv, res.state.spoke 0 = some su ∧ res.state.spoke 1 = some sv ∧
    max (w su) (w sv) ≤ w 2 :=
  (supported_or_spokes_batch hw htest (by norm_num) hB hmsf (mem_univ 2)
    (fun h => not_adm_of_mem_rejected_batch hw htest h trivial) rfl).resolve_left
    two_not_supported

/-- The spoke of an end of edge `2` is a declared edge at that end other than `2`. -/
theorem spoke_eq {v : Fin 4} {s e : Fin 3} (hs : res.state.spoke v = some s)
    (hother : ∀ f : Fin 3, v ∈ ends f → f = e ∨ f = 2) : s = e := by
  rcases spoke_batch_eq_or_mem_declared hw htest hs with h | h
  · simp [st] at h
  · rcases hother s (by simpa [st] using hinv.mem_ends_spoke v s hs) with h' | rfl
    · exact h'
    · exact absurd h two_notMem_declared

/-- Vertex `0` gets the spoke `0`, to the new portal `2`. -/
example : res.state.spoke 0 = some 0 ∧ res.state.proj 0 = 2 ∧ 2 ∈ res.newPortals ∧
    Supported ends w ↑res.state.forest 0 := by
  obtain ⟨su, -, hsu, -⟩ := spokes
  obtain rfl : su = 0 := spoke_eq hsu (by decide)
  have hproj : res.state.proj 0 = 2 := by
    rw [State.proj_of_spoke_eq_some hsu, ends_batch]; rfl
  have hport := hinv.proj_mem_portals 0 0 hsu
  rw [hproj, portals_batch] at hport
  exact ⟨hsu, hproj, by simpa [st] using hport, by
    have h := hinv.spoke_supported 0 0 hsu
    rw [ends_batch] at h
    exact h⟩

/-- Vertex `1` gets the spoke `1`, to the new portal `3`. -/
example : res.state.spoke 1 = some 1 ∧ res.state.proj 1 = 3 ∧ 3 ∈ res.newPortals ∧
    Supported ends w ↑res.state.forest 1 := by
  obtain ⟨-, sv, -, hsv, -⟩ := spokes
  obtain rfl : sv = 1 := spoke_eq hsv (by decide)
  have hproj : res.state.proj 1 = 3 := by
    rw [State.proj_of_spoke_eq_some hsv, ends_batch]; rfl
  have hport := hinv.proj_mem_portals 1 1 hsv
  rw [hproj, portals_batch] at hport
  exact ⟨hsv, hproj, by simpa [st] using hport, by
    have h := hinv.spoke_supported 1 1 hsv
    rw [ends_batch] at h
    exact h⟩

end Spokes

end CslibFrontierTests.MSFCertificateBatch
