/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Algorithms.Lean.Query.MinimumSpanningForest.Certificate.Batch

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

end CslibFrontierTests.MSFCertificateBatch
