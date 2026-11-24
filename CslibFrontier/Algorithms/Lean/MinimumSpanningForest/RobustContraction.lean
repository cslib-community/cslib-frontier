/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/
module

-- upstream: candidate
public import CslibFrontier.Foundations.Combinatorics.Multigraph.MinimumSpanningForest

/-!
# Minimum spanning forest candidates from a corrupted Prim prefix

Pettie and Ramachandran grow a connected vertex set using keys that may overestimate
the original edge weights. Lemma 2.1 bounds paths between light exits of a Prim prefix.
Lemma 3.2 uses that path bound to preserve a small set of candidates for the *original*
minimum spanning forest, even when a tree edge chosen by Prim has a corrupted key.
See [Pettie and Ramachandran, §§2.2 and 3.1][PettieRamachandran2002].
-/

public section

namespace Cslib.Multigraph

variable {V E W : Type*} {ends : E → Sym2 V} [LinearOrder W]

/-- The input edges with both ends in a given vertex set. -/
noncomputable def internalEdges (ends : E → Sym2 V) (S : Finset E) (C : Set V) : Finset E := by
  classical
  exact S.filter fun e => ∀ z ∈ ends e, z ∈ C

theorem mem_internalEdges {S : Finset E} {C : Set V} {e : E} :
    e ∈ internalEdges ends S C ↔ e ∈ S ∧ ∀ z ∈ ends e, z ∈ C := by
  classical
  exact Finset.mem_filter

/-- Vertex sets reached by a finite prefix of Prim's algorithm using the keys `key`.
The next vertex can be chosen arbitrarily among minimum-key boundary edges. -/
inductive PrimPrefix (ends : E → Sym2 V) (S : Finset E) (key : E → W) : Set V → Prop where
  | start (v : V) : PrimPrefix ends S key {v}
  | step {C e u v} (prior : PrimPrefix ends S key C) (hu : u ∈ C) (hv : v ∉ C)
      (he : e ∈ S) (inc : ends e = s(u, v))
      (least : ∀ f ∈ S, ∀ x ∈ C, ∀ y ∉ C, ends f = s(x, y) → key e ≤ key f) :
      PrimPrefix ends S key (insert v C)

private def LightExit (ends : E → Sym2 V) (S : Finset E) (C : Set V) (key : E → W)
    (a : W) (x : V) : Prop :=
  x ∈ C ∧ ∃ f ∈ S, ∃ y ∉ C, ends f = s(x, y) ∧ key f ≤ a

private theorem PrimPrefix.joins_exits {S : Finset E} {C : Set V} {key : E → W}
    (p : PrimPrefix ends S key C) (a : W) {x y : V}
    (hx : LightExit ends S C key a x) (hy : LightExit ends S C key a y) :
    Joins ends {f | f ∈ internalEdges ends S C ∧ key f ≤ a} x y := by
  induction p generalizing x y with
  | start v => exact (show x = y from hx.1.trans hy.1.symm) ▸ Joins.refl _
  | @step C e u v _ hu hv he inc least ih =>
    have down {z : V} (hz : LightExit ends S (insert v C) key a z) (inC : z ∈ C) :
        LightExit ends S C key a z := by
      obtain ⟨_, f, hf, t, ht, j, le⟩ := hz
      exact ⟨inC, f, hf, t, fun h => ht (Set.mem_insert_of_mem _ h), j, le⟩
    have up : {f | f ∈ internalEdges ends S C ∧ key f ≤ a} ⊆
        {f | f ∈ internalEdges ends S (insert v C) ∧ key f ≤ a} := by
      rintro f ⟨hf, hle⟩
      obtain ⟨hfS, inside⟩ := mem_internalEdges.mp hf
      exact ⟨mem_internalEdges.mpr ⟨hfS, fun z hz => Set.mem_insert_of_mem _ (inside z hz)⟩, hle⟩
    have joinNew {z : V} (hz : LightExit ends S C key a z) :
        Joins ends {f | f ∈ internalEdges ends S (insert v C) ∧ key f ≤ a} z v := by
      obtain ⟨hzc, f, hf, t, ht, j, le⟩ := hz
      have hle := (least f hf z hzc t ht j).trans le
      have path := ih ⟨hzc, f, hf, t, ht, j, le⟩ ⟨hu, e, he, v, hv, inc, hle⟩
      apply (path.mono up).trans (Joins.of_mem (e := e) ?_ inc)
      refine ⟨mem_internalEdges.mpr ⟨he, ?_⟩, hle⟩
      simp [inc, Sym2.mem_iff, hu]
    rcases Set.mem_insert_iff.mp hx.1 with rfl | hxC <;>
      rcases Set.mem_insert_iff.mp hy.1 with rfl | hyC
    · exact Joins.refl _
    · exact (joinNew (down hy hyC)).symm
    · exact joinNew (down hx hxC)
    · exact (ih (down hx hxC) (down hy hyC)).mono up

/-- Robust contraction, Lemma 3.2 of [Pettie and Ramachandran][PettieRamachandran2002].
All three MSFs use the original weights. The prefix uses possibly raised keys. Marking
every corrupted boundary edge suffices, including when internal keys were raised too. -/
theorem PrimPrefix.msf_subset_robust [DecidableEq E] {S M : Finset E} {C : Set V}
    {w key : E → W} (prim : PrimPrefix ends S key C) (hw : Function.Injective w)
    (raised : ∀ f ∈ S, w f ≤ key f)
    (clean : ∀ f ∈ S, f ∉ M → ∀ a ∈ C, ∀ b ∉ C, ends f = s(a, b) → key f = w f) :
    msf ends w S ⊆ msf ends w (internalEdges ends S C) ∪
      msf (Sym2.map (contract ends (internalEdges ends S C)) ∘ ends) w
        ((S \ internalEdges ends S C) \ M) ∪ M := by
  classical
  let I := internalEdges ends S C
  let O := (S \ I) \ M
  let q := contract ends (I : Set E)
  intro e hMSF
  obtain ⟨a, b, hab⟩ : ∃ a b, ends e = s(a, b) := Sym2.inductionOn (ends e) fun a b => ⟨a, b, rfl⟩
  obtain ⟨he, hcut⟩ := (mem_msf_iff w hab).mp hMSF
  by_cases marked : e ∈ M
  · exact Finset.mem_union_right _ marked
  apply Finset.mem_union_left
  by_cases inner : e ∈ I
  · apply Finset.mem_union_left
    apply (mem_msf_iff w hab).mpr
    refine ⟨inner, fun path => hcut (path.mono ?_)⟩
    rintro f ⟨hf, hlt⟩
    exact ⟨(mem_internalEdges.mp hf).1, hlt⟩
  apply Finset.mem_union_right
  have heO : e ∈ O := Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨he, inner⟩, marked⟩
  have hq : (Sym2.map q ∘ ends) e = s(q a, q b) := by simp [hab]
  refine (mem_msf_iff w hq).mpr ⟨heO, fun bypass => hcut ?_⟩
  let B : Set E := {f | f ∈ S ∧ w f < w e}
  have safe : {f | f ∈ I ∧ key f ≤ w e} ⊆ B := by
    rintro f ⟨hI, hle⟩
    have hf := (mem_internalEdges.mp hI).1
    exact ⟨hf, lt_of_le_of_ne ((raised f hf).trans hle) (fun eq => inner (hw eq ▸ hI))⟩
  let pivot := if ex : ∃ z, LightExit ends S C key (w e) z then ex.choose else a
  let rep (z : V) := if z ∈ C then pivot else z
  have link {f : E} (hf : f ∈ O) (le : w f ≤ w e) {x y : V} (inc : ends f = s(x, y)) :
      Joins ends B x (rep x) := by
    by_cases hx : x ∈ C
    · obtain ⟨hSD, unmarked⟩ := Finset.mem_sdiff.mp hf
      obtain ⟨inS, noninternal⟩ := Finset.mem_sdiff.mp hSD
      have hy : y ∉ C := fun h => noninternal (mem_internalEdges.mpr ⟨inS, by
        simp [inc, Sym2.mem_iff, hx, h]⟩)
      have exitX : LightExit ends S C key (w e) x :=
        ⟨hx, f, inS, y, hy, inc, (clean f inS unmarked x hx y hy inc) ▸ le⟩
      have ex : ∃ z, LightExit ends S C key (w e) z := ⟨x, exitX⟩
      have exitP : LightExit ends S C key (w e) pivot := by simpa only [pivot, dite_eq_left ex] using ex.choose_spec
      simpa only [rep, ite_eq_left hx] using (prim.joins_exits _ exitX exitP).mono safe
    · simpa [rep, hx] using (Joins.refl (ends := ends) (S := B) x)
  have path := (joins_map_iff (ends := ends) (C := (I : Set E))
    (fun _ _ => contract_eq_contract_iff)).mp bypass
  have lifted : Joins ends B (rep a) (rep b) := by
    apply Joins.lift rep _ path
    rintro f (⟨ho, lt⟩ | hi) x y inc
    · have hinS := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp ho).1).1
      exact ((link ho lt.le inc).symm.trans (Joins.of_mem ⟨hinS, lt⟩ inc)).trans
        (link ho lt.le (inc.trans Sym2.eq_swap))
    · have hends := (mem_internalEdges.mp hi).2
      rw [inc] at hends
      simp [rep, hends x (Sym2.mem_mk_left ..), hends y (Sym2.mem_mk_right ..), Joins.refl]
  exact ((link heO le_rfl hab).trans lifted).trans (link heO le_rfl (hab.trans Sym2.eq_swap)).symm

end Cslib.Multigraph
