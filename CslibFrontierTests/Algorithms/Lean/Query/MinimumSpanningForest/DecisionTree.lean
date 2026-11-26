/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/

module
-- upstream: local-only (tests)

public import CslibFrontier.Algorithms.Lean.Query.MinimumSpanningForest.DecisionTree
public import CslibFrontier.Algorithms.Lean.Kruskal.Basic
import Mathlib.Tactic.FinCases

/-!
# Client Tests for `Query.MinimumSpanningForest.DecisionTree`

Kernel-checked tests for `Cslib.Query.MinimumSpanningForest` (`Basic`, `Canonical`, `Decomp`)
covering:
- Concrete graphs: `P_4` (`endsOfMask 4 37`), `K_3` (`endsOfMask 3 7`) + `le_two_mul_optDepthMN`
  (Prop 5.1) + `MSFDT.padTo`, and `C_4` via `optDepth_le_of_freeM`.
- Disjoint-union decomposition: two triangles sharing a cut vertex
  (`msfDecomposes_of_card_inter_le_one`, `optDepth_edgeUnion_eq_add`,
  `sum_optDepth_le_optDepthMN`, `two_mul_optDepthMN_le`).
- Boundary cases: empty graphs (`n = 0`, `m = 0`), 1-vertex self-loops, disconnected edges with an
  isolated vertex, parallel tie-breaking under flipped permutations, and `optDepthMN` monotonicity
  (`optDepthMN_mono_m`, `optDepthMN_mono_n`).
- Cross-check between `Cslib.Multigraph.msf` (`orderPerm`) and `Kruskal.kruskalEdges`.
-/

public section

namespace CslibFrontierTests.Algorithms.Lean.Query.MinimumSpanningForest.DecisionTree

open Cslib Cslib.Query
open Cslib.Query.MinimumSpanningForest
open Cslib.Algorithms.Lean.Kruskal

/-- Reverse permutation on `Fin e` mapping `i ↦ e - 1 - i`. -/
@[expose] def revPerm (e : ℕ) : Equiv.Perm (Fin e) where
  toFun i := ⟨e - 1 - i.val, by omega⟩
  invFun i := ⟨e - 1 - i.val, by omega⟩
  left_inv i := Fin.ext (by dsimp; omega)
  right_inv i := Fin.ext (by dsimp; omega)

private theorem not_joins_of_inv {E V : Type*} (ends : E → Sym2 V) (S : Set E) (P : V → Prop)
    (hS : ∀ e ∈ S, ∀ a b, ends e = s(a, b) → (P a ↔ P b)) {u v : V} (hu : P u) (hv : ¬ P v) :
    ¬ Cslib.Multigraph.Joins ends S u v := by
  intro hj
  obtain ⟨e, heS, hcut⟩ := hj.exists_mem_edgeCut (P := {x | P x}) hu hv
  obtain ⟨a, b, hab, ha, hb⟩ := Graph.mem_edgeCut_iff.1 hcut
  exact hb ((hS e heS a b hab).mp ha)

private theorem joins_of_sym2_eq {E V : Type*} {ends : E → Sym2 V} {S : Set E}
    {x y a b : V} (h : Cslib.Multigraph.Joins ends S x y) (heq : s(x, y) = s(a, b)) :
    Cslib.Multigraph.Joins ends S a b := by
  rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact h
  · exact h.symm

private theorem joins_subset_singleton {E V : Type*} (ends : E → Sym2 V) {S : Set E}
    {e' : E} (hS : ∀ f ∈ S, f = e') {a b : V} (hab : a ≠ b)
    (h : Cslib.Multigraph.Joins ends S a b) : ends e' = s(a, b) := by
  induction h with
  | refl => exact absurd rfl hab
  | @tail x y _ hstep ih =>
    obtain ⟨f, hfS, hf⟩ := hstep
    rcases hS f hfS with rfl
    by_cases hax : a = x
    · subst hax; exact hf
    · have h1 := ih hax
      rcases Sym2.eq_iff.mp (h1.symm.trans hf) with ⟨hax', _⟩ | ⟨hay', _⟩
      · exact absurd hax' hax
      · exact absurd hay' hab

/-! ### `P_4` (`endsOfMask 4 37`) -/

@[expose] def path4Ends : Fin 3 → Sym2 (Fin 4) := endsOfMask 4 37

@[expose] def path4Tree : MSFDT 3 := .leaf ({0, 1, 2} : Finset (Fin 3))

example : maskEdgePairs 4 37 = [(0, 1), (1, 2), (2, 3)] := by decide

private theorem path4_not_joins_erase (e : Fin 3) :
    ∀ a b, path4Ends e = s(a, b) →
      ¬ Cslib.Multigraph.Joins path4Ends (Finset.univ.erase e : Finset (Fin 3)) a b := by
  have he0 : path4Ends 0 = s(0, 1) := by decide
  have he1 : path4Ends 1 = s(1, 2) := by decide
  have he2 : path4Ends 2 = s(2, 3) := by decide
  intro a b hab
  have hsym : ∀ {x y : Fin 4} (P : Fin 4 → Prop),
      (∀ e' ∈ (Finset.univ.erase e : Finset (Fin 3)),
        ∀ u v, path4Ends e' = s(u, v) → (P u ↔ P v)) →
      P x → ¬ P y → s(x, y) = s(a, b) →
      ¬ Cslib.Multigraph.Joins path4Ends (Finset.univ.erase e : Finset (Fin 3)) a b :=
    fun P hinv hx hy hs hj =>
      not_joins_of_inv path4Ends _ P hinv hx hy (joins_of_sym2_eq hj hs.symm)
  fin_cases e
  · refine hsym (fun x => x = 0) (fun e' he' u v huv => ?_) rfl (by decide) (he0.symm.trans hab)
    have hne := (Finset.mem_erase.mp he').1
    fin_cases e'
    · exact absurd rfl hne
    · rcases Sym2.eq_iff.mp (he1.symm.trans huv) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
    · rcases Sym2.eq_iff.mp (he2.symm.trans huv) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  · refine hsym (fun x => x.val < 2) (fun e' he' u v huv => ?_) (by decide) (by decide)
      (he1.symm.trans hab)
    have hne := (Finset.mem_erase.mp he').1
    fin_cases e'
    · rcases Sym2.eq_iff.mp (he0.symm.trans huv) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
    · exact absurd rfl hne
    · rcases Sym2.eq_iff.mp (he2.symm.trans huv) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  · refine hsym (fun x => x ≠ 3) (fun e' he' u v huv => ?_) (by decide) (by decide)
      (he2.symm.trans hab)
    have hne := (Finset.mem_erase.mp he').1
    fin_cases e'
    · rcases Sym2.eq_iff.mp (he0.symm.trans huv) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
    · rcases Sym2.eq_iff.mp (he1.symm.trans huv) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
    · exact absurd rfl hne

theorem path4Tree_correct : path4Tree.Correct path4Ends := by
  rw [MSFDT.correct_iff]
  intro p
  ext i
  have hi : i ∈ Cslib.Multigraph.msf path4Ends p Finset.univ := by
    induction hpi : path4Ends i using Sym2.ind with
    | _ a b =>
      rw [Cslib.Multigraph.mem_msf_iff p hpi]
      refine ⟨Finset.mem_univ _, fun hc => ?_⟩
      refine path4_not_joins_erase i a b hpi (hc.mono fun x hx => ?_)
      have hlt : p x < p i := hx.2
      exact Finset.mem_coe.mpr (Finset.mem_erase.mpr
        ⟨fun h => by subst h; exact lt_irrefl _ hlt, Finset.mem_univ _⟩)
  simp only [path4Tree, MSFTree.eval]
  constructor
  · intro _; exact hi
  · intro _; fin_cases i <;> decide

example :
    IsSimple (endsOfMask 4 37) ∧ optDepth path4Ends = 0 :=
  ⟨endsOfMask_isSimple 4 37, Nat.eq_zero_of_le_zero (optDepth_le_of_correct path4Tree_correct)⟩

/-! ### `K_3`, Proposition 5.1, and `MSFDT.padTo` -/

@[expose] def k3Ends : Fin 3 → Sym2 (Fin 3) := endsOfMask 3 7

@[expose] def k3Tree : MSFDT 3 :=
  .node 0 1
    (.node 1 2 (.leaf {0, 1}) (.leaf {0, 2}))
    (.node 0 2 (.leaf {0, 1}) (.leaf {1, 2}))

example : maskEdgePairs 3 7 = [(0, 1), (0, 2), (1, 2)] := by decide
example : k3Tree.depth = 2 := by decide
example : k3Tree.eval (Equiv.refl (Fin 3)) = ({0, 1} : Finset (Fin 3)) := by decide
example : k3Tree.eval (Equiv.swap 0 2) = ({1, 2} : Finset (Fin 3)) := by decide
example : k3Tree.eval (revPerm 3) = ({1, 2} : Finset (Fin 3)) := by decide

private theorem k3_other_two_joins {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    {S : Set (Fin 3)} (hi : i ∈ S) (hj : j ∈ S) {a b : Fin 3} (hk : k3Ends k = s(a, b)) :
    Cslib.Multigraph.Joins k3Ends S a b := by
  have he0 : k3Ends 0 = s(0, 1) := rfl
  have he1 : k3Ends 1 = s(0, 2) := rfl
  have he2 : k3Ends 2 = s(1, 2) := rfl
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    first
      | exact absurd rfl hij
      | exact absurd rfl hik
      | exact absurd rfl hjk
      | exact joins_of_sym2_eq
          ((Cslib.Multigraph.Joins.of_mem hi he0).symm.trans
            (Cslib.Multigraph.Joins.of_mem hj he1))
          (he2.symm.trans hk)
      | exact joins_of_sym2_eq
          ((Cslib.Multigraph.Joins.of_mem hi he0).trans
            (Cslib.Multigraph.Joins.of_mem hj he2))
          (he1.symm.trans hk)
      | exact joins_of_sym2_eq
          ((Cslib.Multigraph.Joins.of_mem hi he1).symm.trans
            (Cslib.Multigraph.Joins.of_mem hj he0))
          (Sym2.eq_swap.trans (he2.symm.trans hk))
      | exact joins_of_sym2_eq
          ((Cslib.Multigraph.Joins.of_mem hi he1).trans
            (Cslib.Multigraph.Joins.of_mem hj he2).symm)
          (he0.symm.trans hk)
      | exact joins_of_sym2_eq
          ((Cslib.Multigraph.Joins.of_mem hi he2).symm.trans
            (Cslib.Multigraph.Joins.of_mem hj he0).symm)
          (Sym2.eq_swap.trans (he1.symm.trans hk))
      | exact joins_of_sym2_eq
          ((Cslib.Multigraph.Joins.of_mem hi he2).trans
            (Cslib.Multigraph.Joins.of_mem hj he1).symm)
          (Sym2.eq_swap.trans (he0.symm.trans hk))

private theorem k3_msf_of_max (p : Equiv.Perm (Fin 3)) {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (hi : p i < p k) (hj : p j < p k) :
    Cslib.Multigraph.msf k3Ends p Finset.univ = {i, j} := by
  have hsimp := (isSimple_iff _).mp (endsOfMask_isSimple 3 7)
  have hmem_of_lt : ∀ {x y : Fin 3}, x ≠ y → x ≠ k → y ≠ k → p x < p k →
      x ∈ Cslib.Multigraph.msf k3Ends p Finset.univ := fun {x y} hxy hxk hyk hxk_lt => by
    induction hx : k3Ends x using Sym2.ind with
    | _ a b =>
      rw [Cslib.Multigraph.mem_msf_iff p hx]
      refine ⟨Finset.mem_univ _, fun hc => ?_⟩
      have hne : a ≠ b := by
        intro heq; apply hsimp.1 x
        change (k3Ends x).IsDiag; rw [hx, Sym2.mk_isDiag_iff]; exact heq
      have hS : ∀ f ∈ {f | f ∈ (Finset.univ : Finset (Fin 3)) ∧ p f < p x}, f = y :=
        fun f hf => by
          have hlt : p f < p x := hf.2
          have : f = x ∨ f = y ∨ f = k := by omega
          rcases this with rfl | rfl | rfl
          · exact absurd hlt (lt_irrefl _)
          · rfl
          · exact absurd (lt_trans hxk_lt hlt) (lt_irrefl _)
      have heq_s := joins_subset_singleton k3Ends hS hne hc
      exact hxy (hsimp.2 (heq_s.trans hx.symm)).symm
  have hk_not : k ∉ Cslib.Multigraph.msf k3Ends p Finset.univ := by
    induction hk : k3Ends k using Sym2.ind with
    | _ a b =>
      intro hmem
      rw [Cslib.Multigraph.mem_msf_iff p hk] at hmem
      exact hmem.2 (k3_other_two_joins (S := {f | f ∈ (Finset.univ : Finset (Fin 3)) ∧ p f < p k})
        hij hik hjk ⟨Finset.mem_univ _, hi⟩ ⟨Finset.mem_univ _, hj⟩ hk)
  ext e
  rw [Finset.mem_insert, Finset.mem_singleton]
  have he_case : e = i ∨ e = j ∨ e = k := by omega
  rcases he_case with rfl | rfl | rfl
  · exact iff_of_true (hmem_of_lt hij hik hjk hi) (Or.inl rfl)
  · exact iff_of_true (hmem_of_lt hij.symm hjk hik hj) (Or.inr rfl)
  · exact iff_of_false hk_not (by rintro (rfl | rfl) <;> [exact hik rfl; exact hjk rfl])

theorem k3Tree_correct : k3Tree.Correct k3Ends := by
  rw [MSFDT.correct_iff]
  intro p
  dsimp only [k3Tree, MSFTree.eval]
  split_ifs with h01 h12 h02
  · exact (k3_msf_of_max p (by decide) (by decide) (by decide)
      (Fin.lt_def.mpr (lt_trans h01 h12)) (Fin.lt_def.mpr h12)).symm
  · have h21 : p 2 < p 1 :=
      lt_of_le_of_ne (Fin.le_def.mpr (not_lt.mp h12)) fun h => by
        have := p.injective h; exact absurd this (by decide)
    exact (k3_msf_of_max p (by decide) (by decide) (by decide)
      (Fin.lt_def.mpr h01) h21).symm
  · have h10 : p 1 < p 0 :=
      lt_of_le_of_ne (Fin.le_def.mpr (not_lt.mp h01)) fun h => by
        have := p.injective h; exact absurd this (by decide)
    exact (k3_msf_of_max p (by decide) (by decide) (by decide)
      (Fin.lt_def.mpr h02) (lt_trans h10 (Fin.lt_def.mpr h02))).symm
  · have h10 : p 1 < p 0 :=
      lt_of_le_of_ne (Fin.le_def.mpr (not_lt.mp h01)) fun h => by
        have := p.injective h; exact absurd this (by decide)
    have h20 : p 2 < p 0 :=
      lt_of_le_of_ne (Fin.le_def.mpr (not_lt.mp h02)) fun h => by
        have := p.injective h; exact absurd this (by decide)
    exact (k3_msf_of_max p (by decide) (by decide) (by decide) h10 h20).symm

example :
    optDepth k3Ends ≤ 2 ∧
      3 ≤ 2 * optDepthMN 3 3 ∧
      (k3Tree.padTo (by decide) 3).IsComplete 3 ∧
      (k3Tree.padTo (by decide) 3).depth = 3 ∧
      ∀ p : Equiv.Perm (Fin 3), (k3Tree.padTo (by decide) 3).eval p = k3Tree.eval p :=
  ⟨optDepth_le_of_correct k3Tree_correct,
   le_two_mul_optDepthMN (by decide) (by decide) (by decide),
   MSFDT.padTo_isComplete (by decide) 3 k3Tree (by decide),
   MSFTree.depth_of_isComplete (MSFDT.padTo_isComplete (by decide) 3 k3Tree (by decide)),
   fun p => MSFDT.padTo_eval (by decide) 3 k3Tree (by decide) p⟩

/-! ### `C_4` and `optDepth_le_of_freeM` -/

@[expose] def c4Ends : Fin 4 → Sym2 (Fin 4)
  | 0 => s(0, 1)
  | 1 => s(1, 2)
  | 2 => s(2, 3)
  | 3 => s(3, 0)

@[expose] def c4MaxElim : FreeM (LEQuery (Fin 4)) (Finset (Fin 4)) :=
  FreeM.liftBind (.le 0 1) fun b01 =>
  FreeM.liftBind (.le 2 3) fun b23 =>
    let m1 : Fin 4 := if b01 then 1 else 0
    let m2 : Fin 4 := if b23 then 3 else 2
    FreeM.liftBind (.le m1 m2) fun bm =>
      FreeM.pure (Finset.univ.erase (if bm then m2 else m1))

private theorem c4_other_three_joins {m : Fin 4} {S : Set (Fin 4)}
    (hS : ∀ x : Fin 4, x ≠ m → x ∈ S) {a b : Fin 4} (hm : c4Ends m = s(a, b)) :
    Cslib.Multigraph.Joins c4Ends S a b := by
  have he0 : c4Ends 0 = s(0, 1) := rfl
  have he1 : c4Ends 1 = s(1, 2) := rfl
  have he2 : c4Ends 2 = s(2, 3) := rfl
  have he3 : c4Ends 3 = s(3, 0) := rfl
  have j0 := fun (hm0 : (0 : Fin 4) ≠ m) => Cslib.Multigraph.Joins.of_mem (hS 0 hm0) he0
  have j1 := fun (hm1 : (1 : Fin 4) ≠ m) => Cslib.Multigraph.Joins.of_mem (hS 1 hm1) he1
  have j2 := fun (hm2 : (2 : Fin 4) ≠ m) => Cslib.Multigraph.Joins.of_mem (hS 2 hm2) he2
  have j3 := fun (hm3 : (3 : Fin 4) ≠ m) => Cslib.Multigraph.Joins.of_mem (hS 3 hm3) he3
  fin_cases m
  · exact joins_of_sym2_eq ((j3 (by decide)).symm.trans ((j2 (by decide)).symm.trans
      (j1 (by decide)).symm)) (he0.symm.trans hm)
  · exact joins_of_sym2_eq ((j0 (by decide)).symm.trans ((j3 (by decide)).symm.trans
      (j2 (by decide)).symm)) (he1.symm.trans hm)
  · exact joins_of_sym2_eq ((j1 (by decide)).symm.trans ((j0 (by decide)).symm.trans
      (j3 (by decide)).symm)) (he2.symm.trans hm)
  · exact joins_of_sym2_eq ((j2 (by decide)).symm.trans ((j1 (by decide)).symm.trans
      (j0 (by decide)).symm)) (he3.symm.trans hm)

private theorem c4_not_joins_without_two {e m : Fin 4} (hem : e ≠ m) {S : Set (Fin 4)}
    (heS : e ∉ S) (hmS : m ∉ S) {a b : Fin 4} (he : c4Ends e = s(a, b)) :
    ¬ Cslib.Multigraph.Joins c4Ends S a b := by
  have he0 : c4Ends 0 = s(0, 1) := rfl
  have he1 : c4Ends 1 = s(1, 2) := rfl
  have he2 : c4Ends 2 = s(2, 3) := rfl
  have he3 : c4Ends 3 = s(3, 0) := rfl
  have hsym : ∀ {x y : Fin 4} (P : Fin 4 → Prop),
      (∀ f ∈ S, ∀ u v, c4Ends f = s(u, v) → (P u ↔ P v)) →
      P x → ¬ P y → s(x, y) = s(a, b) → ¬ Cslib.Multigraph.Joins c4Ends S a b :=
    fun P hinv hx hy hs hj =>
      not_joins_of_inv c4Ends S P hinv hx hy (joins_of_sym2_eq hj hs.symm)
  fin_cases e <;> fin_cases m
  · exact absurd rfl hem
  · refine hsym (fun x => x ≠ 1) (fun f hf u v huv => ?_) (by decide) (by decide)
      (he0.symm.trans he)
    fin_cases f
    · exact absurd hf heS
    · exact absurd hf hmS
    · rcases Sym2.eq_iff.mp (he2.symm.trans huv) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
    · rcases Sym2.eq_iff.mp (he3.symm.trans huv) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  · refine hsym (fun x => x = 0 ∨ x = 3) (fun f hf u v huv => ?_) (by decide) (by decide)
      (he0.symm.trans he)
    fin_cases f
    · exact absurd hf heS
    · rcases Sym2.eq_iff.mp (he1.symm.trans huv) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
    · exact absurd hf hmS
    · rcases Sym2.eq_iff.mp (he3.symm.trans huv) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  · refine hsym (fun x => x = 0) (fun f hf u v huv => ?_) rfl (by decide) (he0.symm.trans he)
    fin_cases f
    · exact absurd hf heS
    · rcases Sym2.eq_iff.mp (he1.symm.trans huv) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
    · rcases Sym2.eq_iff.mp (he2.symm.trans huv) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
    · exact absurd hf hmS
  · refine hsym (fun x => x = 1) (fun f hf u v huv => ?_) rfl (by decide) (he1.symm.trans he)
    fin_cases f
    · exact absurd hf hmS
    · exact absurd hf heS
    · rcases Sym2.eq_iff.mp (he2.symm.trans huv) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
    · rcases Sym2.eq_iff.mp (he3.symm.trans huv) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  · exact absurd rfl hem
  · refine hsym (fun x => x ≠ 2) (fun f hf u v huv => ?_) (by decide) (by decide)
      (he1.symm.trans he)
    fin_cases f
    · rcases Sym2.eq_iff.mp (he0.symm.trans huv) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
    · exact absurd hf heS
    · exact absurd hf hmS
    · rcases Sym2.eq_iff.mp (he3.symm.trans huv) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  · refine hsym (fun x => x = 0 ∨ x = 1) (fun f hf u v huv => ?_) (by decide) (by decide)
      (he1.symm.trans he)
    fin_cases f
    · rcases Sym2.eq_iff.mp (he0.symm.trans huv) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
    · exact absurd hf heS
    · rcases Sym2.eq_iff.mp (he2.symm.trans huv) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
    · exact absurd hf hmS
  · refine hsym (fun x => x = 2 ∨ x = 1) (fun f hf u v huv => ?_) (by decide) (by decide)
      (he2.symm.trans he)
    fin_cases f
    · exact absurd hf hmS
    · rcases Sym2.eq_iff.mp (he1.symm.trans huv) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
    · exact absurd hf heS
    · rcases Sym2.eq_iff.mp (he3.symm.trans huv) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  · refine hsym (fun x => x = 2) (fun f hf u v huv => ?_) rfl (by decide) (he2.symm.trans he)
    fin_cases f
    · rcases Sym2.eq_iff.mp (he0.symm.trans huv) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
    · exact absurd hf hmS
    · exact absurd hf heS
    · rcases Sym2.eq_iff.mp (he3.symm.trans huv) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  · exact absurd rfl hem
  · refine hsym (fun x => x ≠ 3) (fun f hf u v huv => ?_) (by decide) (by decide)
      (he2.symm.trans he)
    fin_cases f
    · rcases Sym2.eq_iff.mp (he0.symm.trans huv) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
    · rcases Sym2.eq_iff.mp (he1.symm.trans huv) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
    · exact absurd hf heS
    · exact absurd hf hmS
  · refine hsym (fun x => x ≠ 0) (fun f hf u v huv => ?_) (by decide) (by decide)
      (he3.symm.trans he)
    fin_cases f
    · exact absurd hf hmS
    · rcases Sym2.eq_iff.mp (he1.symm.trans huv) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
    · rcases Sym2.eq_iff.mp (he2.symm.trans huv) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
    · exact absurd hf heS
  · refine hsym (fun x => x = 3 ∨ x = 2) (fun f hf u v huv => ?_) (by decide) (by decide)
      (he3.symm.trans he)
    fin_cases f
    · rcases Sym2.eq_iff.mp (he0.symm.trans huv) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
    · exact absurd hf hmS
    · rcases Sym2.eq_iff.mp (he2.symm.trans huv) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
    · exact absurd hf heS
  · refine hsym (fun x => x = 3) (fun f hf u v huv => ?_) rfl (by decide) (he3.symm.trans he)
    fin_cases f
    · rcases Sym2.eq_iff.mp (he0.symm.trans huv) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
    · rcases Sym2.eq_iff.mp (he1.symm.trans huv) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
    · exact absurd hf hmS
    · exact absurd hf heS
  · exact absurd rfl hem

example : optDepth c4Ends ≤ 3 := by
  refine optDepth_le_of_freeM c4Ends c4MaxElim 3 (fun p => ?_) (fun p => ?_)
  · dsimp only [c4MaxElim]
    change FreeM.eval (LEQuery.keyOracle p) (FreeM.liftBind _ _) = _
    have hstep : ∀ (a b : Fin 4) (k : Bool → FreeM (LEQuery (Fin 4)) (Finset (Fin 4))),
        FreeM.eval (LEQuery.keyOracle p) (FreeM.liftBind (.le a b) k) =
          FreeM.eval (LEQuery.keyOracle p) (k (decide (p a ≤ p b))) := fun _ _ _ => rfl
    rw [hstep, hstep, hstep]
    change Finset.univ.erase _ = _
    let m1 : Fin 4 := if decide (p 0 ≤ p 1) then 1 else 0
    let m2 : Fin 4 := if decide (p 2 ≤ p 3) then 3 else 2
    let m : Fin 4 := if decide (p m1 ≤ p m2) then m2 else m1
    have hmax : ∀ x : Fin 4, p x ≤ p m := by
      have hm1 : p 0 ≤ p m1 ∧ p 1 ≤ p m1 := by
        dsimp only [m1]; split_ifs with h
        · exact ⟨of_decide_eq_true h, le_rfl⟩
        · exact ⟨le_rfl, le_of_not_ge fun hle => h (decide_eq_true hle)⟩
      have hm2 : p 2 ≤ p m2 ∧ p 3 ≤ p m2 := by
        dsimp only [m2]; split_ifs with h
        · exact ⟨of_decide_eq_true h, le_rfl⟩
        · exact ⟨le_rfl, le_of_not_ge fun hle => h (decide_eq_true hle)⟩
      have hmm : p m1 ≤ p m ∧ p m2 ≤ p m := by
        dsimp only [m]; split_ifs with h
        · exact ⟨of_decide_eq_true h, le_rfl⟩
        · exact ⟨le_rfl, le_of_not_ge fun hle => h (decide_eq_true hle)⟩
      intro x
      fin_cases x
      · exact hm1.1.trans hmm.1
      · exact hm1.2.trans hmm.1
      · exact hm2.1.trans hmm.2
      · exact hm2.2.trans hmm.2
    ext e
    rw [Finset.mem_erase, and_iff_left (Finset.mem_univ _)]
    induction he : c4Ends e using Sym2.ind with
    | _ a b =>
      rw [Cslib.Multigraph.mem_msf_iff p he]
      simp only [Finset.mem_univ, true_and]
      by_cases hem : e = m
      · subst hem
        refine ⟨fun hne => False.elim (hne rfl), fun hc => False.elim (hc ?_)⟩
        exact c4_other_three_joins (S := {f | p f < p m})
          (fun x hx => lt_of_le_of_ne (hmax x) fun h => hx (p.injective h)) he
      · refine ⟨fun _ => ?_, fun _ => hem⟩
        exact c4_not_joins_without_two (S := {f | p f < p e}) hem
          (fun h => lt_irrefl _ (Set.mem_ofPred.mp h))
          (fun h => not_lt_of_ge (hmax e) (Set.mem_ofPred.mp h)) he
  · dsimp only [c4MaxElim]
    have hstep : ∀ (a b : Fin 4) (k : Bool → FreeM (LEQuery (Fin 4)) (Finset (Fin 4))),
        FreeM.countQueries (LEQuery.keyOracle p) (FreeM.liftBind (.le a b) k) =
          1 + FreeM.countQueries (LEQuery.keyOracle p) (k (decide (p a ≤ p b))) :=
      fun a b k => FreeM.countQueries_liftBind (LEQuery.keyOracle p) (.le a b) k
    rw [hstep, hstep, hstep]
    exact le_rfl

/-! ### Decomposition (`MSFDecomposes`, Lemma 5.5, Corollary 5.6, Corollary 5.7) -/

@[expose] def triL : Fin 3 → Sym2 (Fin 5)
  | 0 => s(0, 1)
  | 1 => s(0, 2)
  | 2 => s(1, 2)

@[expose] def triR : Fin 3 → Sym2 (Fin 5)
  | 0 => s(2, 3)
  | 1 => s(2, 4)
  | 2 => s(3, 4)

example :
    optDepth (edgeUnion triL triR) = optDepth triL + optDepth triR ∧
      optDepth triL + optDepth triR ≤ optDepthMN 6 5 ∧
      2 * optDepthMN 3 3 ≤ optDepthMN 6 6 := by
  let V₁ : Finset (Fin 5) := {0, 1, 2}
  let V₂ : Finset (Fin 5) := {2, 3, 4}
  have hV₁ : ∀ i : Fin 3, ∀ v ∈ triL i, v ∈ V₁ := fun i v hv => by
    fin_cases i
    · simp only [triL, Sym2.mem_iff] at hv; rcases hv with rfl | rfl <;> decide
    · simp only [triL, Sym2.mem_iff] at hv; rcases hv with rfl | rfl <;> decide
    · simp only [triL, Sym2.mem_iff] at hv; rcases hv with rfl | rfl <;> decide
  have hV₂ : ∀ j : Fin 3, ∀ v ∈ triR j, v ∈ V₂ := fun j v hv => by
    fin_cases j
    · simp only [triR, Sym2.mem_iff] at hv; rcases hv with rfl | rfl <;> decide
    · simp only [triR, Sym2.mem_iff] at hv; rcases hv with rfl | rfl <;> decide
    · simp only [triR, Sym2.mem_iff] at hv; rcases hv with rfl | rfl <;> decide
  have hinter : (V₁ ∩ V₂).card ≤ 1 := by decide
  have h53 : MSFDecomposes triL triR :=
    msfDecomposes_of_card_inter_le_one triL triR V₁ V₂ hV₁ hV₂ hinter
  have hadd : optDepth (edgeUnion triL triR) = optDepth triL + optDepth triR :=
    optDepth_edgeUnion_eq_add triL triR h53
  let Cs : List (Σ e, Fin e → Sym2 (Fin 5)) := [⟨3, triL⟩, ⟨3, triR⟩]
  have hV : ValidDecomp Cs := by
    rw [validDecomp_cons]
    refine ⟨?_, (validDecomp_cons _ _).mpr ⟨?_, validDecomp_nil⟩⟩
    · have hsub1 : compVerts triL ⊆ V₁ := by
        intro v hv
        simp only [compVerts, Finset.mem_biUnion, Finset.mem_univ, Sym2.mem_toFinset,
          true_and] at hv
        obtain ⟨i, hi⟩ := hv
        exact hV₁ i v hi
      have hsub2 : compVertsList [⟨3, triR⟩] ⊆ V₂ := by
        intro v hv
        dsimp only [compVertsList] at hv
        simp only [Finset.mem_union, Finset.notMem_empty, or_false, compVerts, Finset.mem_biUnion,
          Finset.mem_univ, Sym2.mem_toFinset, true_and] at hv
        obtain ⟨j, hj⟩ := hv
        exact hV₂ j v hj
      exact (Finset.card_le_card (Finset.inter_subset_inter hsub1 hsub2)).trans hinter
    · simp [compVertsList]
  have hsimp : IsSimple (edgeUnionList Cs) := by
    rw [isSimple_iff]
    refine ⟨fun i => ?_, fun i₁ i₂ he => ?_⟩
    · fin_cases i <;> decide
    · fin_cases i₁ <;> fin_cases i₂ <;> first | rfl | (exfalso; revert he; decide)
  have hsum := sum_optDepth_le_optDepthMN (m := 6) (n := 5) Cs hV hsimp (by decide)
  simp only [Cs, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at hsum
  exact ⟨hadd, hsum, two_mul_optDepthMN_le 3 3⟩

/-! ### Boundary Cases, Monotonicity, and Kruskal Cross-Check -/

example :
    optDepth (endsOfMask 0 0) = 0 ∧
      optDepthMN 0 0 = 0 ∧
      optDepth (endsOfMask 4 0) = 0 ∧
      optDepth (fun _ : Fin 2 => s((0 : Fin 1), (0 : Fin 1))) = 0 ∧
      optDepthMN 1 4 = 0 ∧
      optDepthMN 3 3 ≤ optDepthMN 6 3 ∧
      optDepthMN 3 3 ≤ optDepthMN 3 4 ∧
      optDepth (endsOfMask 3 3) ≤ optDepth (endsOfMask 3 7) ∧
      optDepthMN 3 3 = ((Finset.range (2 ^ Nat.choose 3 2)).filter fun mask =>
        (maskEdgePairs 3 mask).length = 3).sup fun mask => optDepth (endsOfMask 3 mask) := by
  have h00 : optDepth (endsOfMask 0 0) = 0 :=
    optDepth_eq_zero_of_le_one (Nat.zero_le 1) _
  have hmn0 : optDepthMN 0 0 = 0 := by
    obtain ⟨mask, _, hlen, heq⟩ := exists_endsOfMask_eq_optDepthMN 0 0
    rw [← heq]
    exact optDepth_eq_zero_of_le_one (by omega) _
  have h40 : optDepth (endsOfMask 4 0) = 0 :=
    optDepth_eq_zero_of_le_one (by decide) _
  have hloop : optDepth (fun _ : Fin 2 => s((0 : Fin 1), (0 : Fin 1))) = 0 := by
    let T : MSFDT 2 := .leaf ∅
    refine Nat.eq_zero_of_le_zero
      (optDepth_le_of_correct (T := T) ((MSFDT.correct_iff _ _).mpr fun p => ?_))
    ext i
    simp only [T, MSFTree.eval, Finset.notMem_empty, false_iff]
    exact Cslib.Multigraph.notMem_msf_of_isDiag p (by simp)
  have hm1 : optDepthMN 1 4 = 0 := by
    obtain ⟨mask, _, hlen, heq⟩ := exists_endsOfMask_eq_optDepthMN 1 4
    rw [← heq]
    exact optDepth_eq_zero_of_le_one hlen _
  have hsubmask : optDepth (endsOfMask 3 3) ≤ optDepth (endsOfMask 3 7) :=
    optDepth_le_of_submask fun k hk => by
      by_cases h0 : k = 0
      · subst h0; decide
      · by_cases h1 : k = 1
        · subst h1; decide
        · have h2 : 2 ≤ k := by omega
          have hdiv : 3 / 2 ^ k = 0 :=
            Nat.div_eq_of_lt (lt_of_lt_of_le (by decide) (Nat.pow_le_pow_right (by decide) h2))
          rw [Nat.testBit, Nat.shiftRight_eq_div_pow, hdiv] at hk
          exact absurd hk (by decide)
  exact ⟨h00, hmn0, h40, hloop, hm1, optDepthMN_mono_m (n := 3) (by decide),
    optDepthMN_mono_n (m := 3) (by decide), hsubmask, optDepthMN_eq_exact (by decide)⟩

/-- Parallel edges tie-breaking under `Equiv.refl` vs `revPerm 2`. -/
@[expose] def paraEnds : Fin 2 → Sym2 (Fin 2) := fun _ => s(0, 1)

private theorem para_msf_of_lt (p : Equiv.Perm (Fin 2)) {a b : Fin 2} (hab : a ≠ b)
    (hlt : p a < p b) : Cslib.Multigraph.msf paraEnds p Finset.univ = {a} := by
  ext e
  rw [Finset.mem_singleton, Cslib.Multigraph.mem_msf_iff p (e := e) (a := 0) (b := 1) rfl]
  have he : e = a ∨ e = b := by omega
  have ha01 : paraEnds a = s(0, 1) := rfl
  rcases he with rfl | rfl
  · refine ⟨fun _ => rfl, fun _ => ⟨Finset.mem_univ _, fun hj => ?_⟩⟩
    have hsub : ∀ f ∈ {f | f ∈ (Finset.univ : Finset (Fin 2)) ∧ p f < p e}, False := by
      intro f hf
      have hfeb : f = e ∨ f = b := by omega
      rcases hfeb with rfl | rfl
      · exact lt_irrefl _ hf.2
      · exact lt_irrefl _ (lt_trans hlt hf.2)
    have hinv := not_joins_of_inv paraEnds {f | f ∈ Finset.univ ∧ p f < p e} (fun x => x = 0)
      (fun f hf => False.elim (hsub f hf)) (u := 0) (v := 1) rfl (by decide)
    exact hinv hj
  · refine ⟨fun h => False.elim (h.2 ?_), fun h => False.elim (hab h.symm)⟩
    exact Cslib.Multigraph.Joins.of_mem ⟨Finset.mem_univ _, hlt⟩ ha01

example :
    Cslib.Multigraph.msf paraEnds (Equiv.refl (Fin 2)) Finset.univ = {0} ∧
      Cslib.Multigraph.msf paraEnds (revPerm 2) Finset.univ = {1} ∧
      optDepth paraEnds ≤ 1 := by
  let T : MSFDT 2 := .node 0 1 (.leaf {0}) (.leaf {1})
  have hcorrFun : ∀ p : Equiv.Perm (Fin 2),
      T.eval p = Cslib.Multigraph.msf paraEnds p Finset.univ := fun p => by
    dsimp only [T, MSFTree.eval]
    split_ifs with hlt
    · exact (para_msf_of_lt p (by decide) (Fin.lt_def.mpr hlt)).symm
    · have h10 : p 1 < p 0 :=
        lt_of_le_of_ne (Fin.le_def.mpr (not_lt.mp hlt)) fun h => by
          have := p.injective h; exact absurd this (by decide)
      exact (para_msf_of_lt p (by decide) h10).symm
  have hcorr : T.Correct paraEnds := (MSFDT.correct_iff _ _).mpr hcorrFun
  exact ⟨(hcorrFun (Equiv.refl (Fin 2))).symm, (hcorrFun (revPerm 2)).symm,
    optDepth_le_of_correct hcorr⟩

/-- Cross-check `Cslib.Multigraph.msf` via `orderPerm` against `Kruskal.kruskalEdges`. -/
@[expose] def crossEs : List (WeightedEdge 4 ℕ) :=
  [⟨0, 1, 4⟩, ⟨1, 2, 1⟩, ⟨0, 2, 3⟩, ⟨2, 3, 2⟩]

@[expose] def crossEnds : Fin 4 → Sym2 (Fin 4)
  | 0 => s(0, 1)
  | 1 => s(1, 2)
  | 2 => s(0, 2)
  | 3 => s(2, 3)

@[expose] def crossW : Fin 4 → ℕ
  | 0 => 4
  | 1 => 1
  | 2 => 3
  | 3 => 2

example :
    kruskalEdges crossEs = [⟨1, 2, 1⟩, ⟨2, 3, 2⟩, ⟨0, 2, 3⟩] ∧
      totalWeight (kruskalEdges crossEs) = 6 ∧
      ∀ (hw : Function.Injective crossW),
        Cslib.Multigraph.msf crossEnds (orderPerm crossW hw) Finset.univ = {1, 2, 3} := by
  have hk : kruskalEdges crossEs = [⟨1, 2, 1⟩, ⟨2, 3, 2⟩, ⟨0, 2, 3⟩] := by
    rw [kruskalEdges, show sortEdges crossEs =
      [⟨1, 2, 1⟩, ⟨2, 3, 2⟩, ⟨0, 2, 3⟩, ⟨0, 1, 4⟩] by simp [crossEs, sortEdges_cons_cons]]
    rfl
  refine ⟨hk, by rw [hk]; decide, fun hw => ?_⟩
  rw [msf_congr_lt crossEnds (orderPerm crossW hw) crossW Finset.univ
    (orderPerm_lt_iff crossW hw)]
  ext e
  rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]
  induction he : crossEnds e using Sym2.ind with
  | _ a b =>
    rw [Cslib.Multigraph.mem_msf_iff crossW he]
    fin_cases e
    · refine ⟨fun h => False.elim (h.2 ?_), fun h => by rcases h with h | h | h <;> cases h⟩
      have j1 := Cslib.Multigraph.Joins.of_mem
        (S := {f | f ∈ Finset.univ ∧ crossW f < crossW 0})
        ⟨Finset.mem_univ _, by decide⟩ (show crossEnds 1 = s(1, 2) by rfl)
      have j2 := Cslib.Multigraph.Joins.of_mem
        (S := {f | f ∈ Finset.univ ∧ crossW f < crossW 0})
        ⟨Finset.mem_univ _, by decide⟩ (show crossEnds 2 = s(0, 2) by rfl)
      exact joins_of_sym2_eq (j1.trans j2.symm).symm (show s(0, 1) = s(a, b) from he)
    · refine ⟨fun _ => Or.inl rfl, fun _ => ⟨Finset.mem_univ _, fun hj => ?_⟩⟩
      have h0 : ∀ f ∈ {f | f ∈ (Finset.univ : Finset (Fin 4)) ∧ crossW f < crossW 1}, False :=
        fun f hf => by fin_cases f <;> exact absurd hf.2 (by decide)
      have hne : a ≠ b := by
        intro h; subst h
        have hs : (s(1, 2) : Sym2 (Fin 4)) = s(a, a) := he
        rw [Sym2.eq_iff] at hs; rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
      exact not_joins_of_inv crossEnds {f | f ∈ Finset.univ ∧ crossW f < crossW 1} (fun x => x = a)
        (fun f hf => False.elim (h0 f hf)) rfl hne.symm hj
    · refine ⟨fun _ => Or.inr (Or.inl rfl), fun _ => ⟨Finset.mem_univ _, fun hj => ?_⟩⟩
      have he1 : crossEnds 1 = s(1, 2) := rfl
      have he2 : crossEnds 2 = s(0, 2) := rfl
      have he3 : crossEnds 3 = s(2, 3) := rfl
      have hc := not_joins_of_inv crossEnds {f | f ∈ Finset.univ ∧ crossW f < crossW 2}
        (fun x => x = 0) (fun f hf u v huv => by
          fin_cases f
          · exact absurd hf.2 (by decide)
          · rcases Sym2.eq_iff.mp (he1.symm.trans huv) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
          · exact absurd hf.2 (by decide)
          · rcases Sym2.eq_iff.mp (he3.symm.trans huv) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide)
        (u := 0) (v := 2) rfl (by decide)
      exact hc (joins_of_sym2_eq hj (he.symm.trans he2))
    · refine ⟨fun _ => Or.inr (Or.inr rfl), fun _ => ⟨Finset.mem_univ _, fun hj => ?_⟩⟩
      have he1 : crossEnds 1 = s(1, 2) := rfl
      have he3 : crossEnds 3 = s(2, 3) := rfl
      have hc := not_joins_of_inv crossEnds {f | f ∈ Finset.univ ∧ crossW f < crossW 3}
        (fun x => x ≠ 3) (fun f hf u v huv => by
          fin_cases f
          · exact absurd hf.2 (by decide)
          · rcases Sym2.eq_iff.mp (he1.symm.trans huv) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
          · exact absurd hf.2 (by decide)
          · exact absurd hf.2 (by decide)) (u := 2) (v := 3) (by decide) (by decide)
      exact hc (joins_of_sym2_eq hj (he.symm.trans he3))

end CslibFrontierTests.Algorithms.Lean.Query.MinimumSpanningForest.DecisionTree
