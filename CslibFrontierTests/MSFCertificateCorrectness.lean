/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Algorithms.Lean.Query.MinimumSpanningForest.Certificate.Correctness
import CslibFrontierTests.MSFCertificateProcedure

/-!
# Tests for the correctness of the certificate procedure

On the triangle with a self-loop of `CslibFrontierTests.MSFCertificateProcedure`, with the trivial
schedule and estimator and an exact minimum spanning forest call, every hypothesis of Claim 3.5
and Lemma 3.7 holds (`hw`, `hmsf`, the ends of the edges among the vertices). The consequences
checked: the returned forest is an acyclic set of at most `n - 1 = 2` root edges (Claim 3.5), the
root rejects nothing, and the counting consequence of Lemma 3.7 bounds the unsupported edges.

With `γ = 1` the root has `t = 1`, and its single round is bad for every edge, so Lemma 3.7's
no-error hypothesis fails there. The second configuration `cfg2` witnesses it: `γ = 2`, so the root
has `t = 2` blocks of two rounds and `r = 64`. Every edge acts in round `0`. With `n = 3`, the
portals satisfy `64 · #P ≤ 6 · 2`, so there are none, no vertex ever has a spoke, every edge prefers
*find* in every round, and round `0` lies in a block followed by another block with a *find*
preference: it is good. So no edge has an error in any call, and Lemma 3.7 makes every edge
supported by the returned forest.
-/

namespace CslibFrontierTests.MSFCertificateCorrectness

open Cslib Cslib.Query Cslib.Query.Certificate Cslib.Multigraph Finset
open CslibFrontierTests.MSFCertificateProcedure

theorem hw : Function.Injective w := Fin.val_injective

theorem hmsf : cfg.ExactMsf w := fun _ _ => rfl

theorem hS : ∀ e ∈ (univ : Finset (Fin 4)), ∀ v ∈ ends e, v ∈ (univ : Finset (Fin 3)) :=
  fun _ _ _ _ => mem_univ _

/-- The result of the root call. -/
noncomputable abbrev res : Result (Fin 4) :=
  (certificate cfg root).eval (LEQuery.keyOracle w)

/-- **Claim 3.5**: the returned forest is acyclic, so it has at most `n - 1 = 2` edges. -/
example : IsAcyclic ends ↑res.forest ∧ #res.forest ≤ 2 := by
  have h := sound_certificate hw hmsf root root_wellFormed
  refine ⟨h.forest_acyclic, ?_⟩
  have := h.forest_acyclic.card_le (X := univ) fun _ _ _ _ => mem_univ _
  simpa using this

/-- The root rejects nothing. -/
example : res.rejected = ∅ := rejected_certificate_root hw hmsf hS

/-- **The counting consequence of Lemma 3.7**: the unsupported root edges, plus the rejected edges,
number at most the errors over all calls. -/
example : #(unsupported ends w ↑res.forest univ) +
      ((calls cfg (LEQuery.keyOracle w) root).map fun c =>
        ∑ i ∈ range (levelT cfg.γ c.level ^ 2), #(absorbed cfg (LEQuery.keyOracle w) c i)).sum ≤
    ((calls cfg (LEQuery.keyOracle w) root).map fun c => #(errors cfg w c)).sum :=
  card_unsupported_add_sum_absorbed_le hw hmsf hS

/-! ### A witness of Lemma 3.7's hypothesis -/

theorem levelT_two_pos (d : ℕ+) : 0 < levelT 2 d ^ 2 := by
  have := d.pos
  simp only [levelT]
  positivity

/-- `γ = 2`, every edge in round `0`, every estimate *find*, and `msf` as the exact call. -/
noncomputable def cfg2 : Config (Fin 3) (Fin 4) where
  γ := 2
  sched inst _ := ⟨0, levelT_two_pos inst.level⟩
  est _ _ _ := pure fun _ => .find
  msfSub ends S := pure (msf ends w S)

theorem hmsf2 : cfg2.ExactMsf w := fun _ _ => rfl

theorem levelT_root2 : levelT cfg2.γ root.level = 2 := by
  simp [cfg2, levelT]

/-- No vertex has a spoke at the start of rounds `0` to `4`: there are no portals. -/
theorem spoke_eq_none {j : ℕ} (hj : j ≤ 4) (v : Fin 3) :
    (snapshot cfg2 (LEQuery.keyOracle w) root j).state.spoke v = none := by
  rcases hs : (snapshot cfg2 (LEQuery.keyOracle w) root j).state.spoke v with _ | s
  · rfl
  · have hinv := (invariant_snapshot hw hmsf2 root_wellFormed j).state
    have hP := card_portals_snapshot_mul_le cfg2 (LEQuery.keyOracle w) root j
    rw [levelT_root2] at hP
    have hr : levelR cfg2.γ root.level = 64 := by simp [levelR, levelT, cfg2]
    have h3 : #root.vertices = 3 := by simp
    rw [hr, h3] at hP
    have hj2 : j / 2 ≤ 2 := by omega
    have h0 : #(snapshot cfg2 (LEQuery.keyOracle w) root j).state.portals = 0 := by
      have := Nat.mul_le_mul_left (2 * 3) hj2
      omega
    have := hinv.proj_mem_portals v s hs
    rw [card_eq_zero.1 h0] at this
    simp at this

/-- Every edge prefers *find* at the start of rounds `0` to `4`. -/
theorem prefSeq_eq_find {j : ℕ} (hj : j ≤ 4) (e : Fin 4) : prefSeq cfg2 w root e j = .find := by
  rw [prefSeq_eq, pref_eq_find_iff]
  refine prefersFind_of_not_projectable fun hp => ?_
  have := hp.isSome_spoke (Sym2.out_fst_mem _)
  rw [spoke_eq_none hj] at this
  simp at this

/-- No edge has an error at the root. -/
theorem not_hasError_root (e : Fin 4) : ¬HasError cfg2 w root e := by
  have hsched : (cfg2.sched root e : ℕ) = 0 := rfl
  rw [hasError_iff, hsched, levelT_root2]
  rintro (hbad | hest)
  · rcases hbad with ⟨h, -⟩ | ⟨-, h⟩
    · rw [prefSeq_eq_find (by omega)] at h
      cases h
    · have := h 2 (by norm_num) (by norm_num)
      rw [prefSeq_eq_find (by omega)] at this
      cases this
  · refine ne_of_maskAction_ne hest ?_
    rw [← prefSeq_eq, prefSeq_eq_find (by omega)]
    rfl

/-- The children of the root receive no edge. -/
theorem edges_child_root (i : ℕ) : (child cfg2 (LEQuery.keyOracle w) root i).edges = ∅ := by
  rw [edges_child]
  refine filter_false_of_mem fun e he h => ?_
  have hi : i = 0 := by rw [← sched_eq_of_mem_acting he]; rfl
  subst hi
  have hpref : pref w (snapshot cfg2 (LEQuery.keyOracle w) root 0).state e = .find := by
    rw [← prefSeq_eq]; exact prefSeq_eq_find (by norm_num) e
  have hne : estimate cfg2 (LEQuery.keyOracle w) root 0 e ≠
      pref w (snapshot cfg2 (LEQuery.keyOracle w) root 0).state e := by
    rw [h, hpref]; decide
  exact ne_of_maskAction_ne hne (by rw [hpref]; rfl)

/-- **Lemma 3.7 applies**: no error occurs in any call, so every edge of the triangle and the
self-loop is supported by the returned forest. -/
example (e : Fin 4) :
    Supported ends w
      ↑((certificate cfg2 root).eval (LEQuery.keyOracle w)).forest e := by
  refine supported_certificate_root_of_forall_not_hasError hw hmsf2 hS (mem_univ e) ?_
  intro c hc he
  have hS0 : root.edges ≠ ∅ := ne_empty_of_mem (mem_univ (0 : Fin 4))
  rw [calls_eq] at hc
  simp only [hS0, ↓reduceIte, List.mem_cons, List.mem_flatMap, List.mem_range] at hc
  rcases hc with rfl | ⟨i, -, hci⟩
  · exact not_hasError_root e
  · split at hci
    · rw [calls_eq, edges_child_root] at hci
      simp only [↓reduceIte, List.mem_singleton] at hci
      subst hci
      rw [edges_child_root] at he
      simp at he
    · simp at hci

end CslibFrontierTests.MSFCertificateCorrectness
