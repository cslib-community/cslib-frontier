/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/
module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.MinimumSpanningForest.OptimalTree.WorstCase
import Mathlib.Tactic.Ring

/-!
# The edge lower bound and the numerical recurrence

In the labeled multigraph model a bundle of parallel edges witnesses the linear lower bound.
Changing one unqueried edge from the smallest to the largest weight preserves the comparison
transcript and changes the forest. The doubling bound for the native optimum then closes the
numerical recursion in the proof of [PettieRamachandran2002], Theorem 5.8, once its local work
and recursive-size estimates have been established for a machine implementation.
-/

public section

namespace Cslib.Query.LEQuery

variable {E O : Type}

/-- Labels mentioned by a comparison along a single execution path. -/
@[expose] def touched [DecidableEq E] (ask : E → E → Bool) : FreeM (LEQuery E) O → Finset E
  | .pure _ => ∅
  | .liftBind (.le a b) cont => insert a (insert b (touched ask (cont (ask a b))))

/-- Each comparison can mention at most two new labels. -/
theorem card_touched_le [DecidableEq E] (ask : E → E → Bool) (p : FreeM (LEQuery E) O) :
    (touched ask p).card ≤ 2 * p.countQueries (oracleOf ask) := by
  induction p using FreeM.rec with
  | pure => simp [touched]
  | liftBind op cont ih =>
    cases op with
    | le a b =>
      let s := touched ask (cont (ask a b))
      have h1 := Finset.card_insert_le a (insert b s)
      have h2 := Finset.card_insert_le b s
      have h3 := ih (ask a b)
      let count := (cont (ask a b)).countQueries (oracleOf ask)
      change (insert a (insert b s)).card ≤ 2 * (1 + count)
      change s.card ≤ 2*count at h3
      omega

/-- Changing weights on labels never mentioned along a path preserves its returned value. -/
theorem eval_congr_touched [DecidableEq E] {W : Type*} [LinearOrder W] (w w' : E → W)
    (p : FreeM (LEQuery E) O)
    (same : ∀ a ∈ touched (fun x y => decide (w x ≤ w y)) p, w a = w' a) :
    p.eval (keyOracle w) = p.eval (keyOracle w') := by
  induction p using FreeM.rec with
  | pure => rfl
  | liftBind op cont ih =>
    cases op with
    | le a b =>
      let bit := decide (w a ≤ w b)
      let rest := touched (fun x y => decide (w x ≤ w y)) (cont bit)
      change ∀ x ∈ insert a (insert b rest), w x = w' x at same
      have agree : bit = decide (w' a ≤ w' b) := by
        dsimp [bit]
        rw [same a (Finset.mem_insert_self ..), same b (by simp)]
      change (cont bit).eval _ = (cont (decide (w' a ≤ w' b))).eval _
      rw [← agree]
      exact ih bit (fun x hx => same x (Finset.mem_insert_of_mem
        (Finset.mem_insert_of_mem hx)))

end Cslib.Query.LEQuery

namespace Cslib.Multigraph.OptimalTree

open Cslib.Query
open scoped Sym2

variable {m n : ℕ}

/-- The worst-case native comparison budget is at least `m/2` whenever there are at least
two edges and two vertices. The witness graph consists of parallel edges on two vertices. -/
theorem edgeCount_le_twice_worstCase (hm : 2 ≤ m) (hn : 2 ≤ n) : m ≤ 2 * worstCase m n := by
  classical
  let a : Fin n := ⟨0, by omega⟩
  let b : Fin n := ⟨1, by omega⟩
  let L : Fin m → Sym2 (Fin n) := fun _ => s(a,b)
  let w (x : Fin m) : ℕ := x.val + 1
  let p := optimalMSFProgram L
  let ask (x y : Fin m) := decide (w x ≤ w y)
  let used := LEQuery.touched ask p
  have hw : Function.Injective w := fun x y h => Fin.ext (Nat.add_right_cancel h)
  have all : used = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro x
    by_contra missing
    let lo (y : Fin m) := if y = x then 0 else w y
    let hi (y : Fin m) := if y = x then m+1 else w y
    have inj (z : ℕ) (outside : ∀ y, w y ≠ z) :
        Function.Injective (fun y => if y = x then z else w y) := by
      intro u v h
      by_cases hu : u = x <;> by_cases hv : v = x <;> simp_all [hw.eq_iff]
    have hlo : Function.Injective lo := inj 0 (fun y => Nat.succ_ne_zero _)
    have hhi : Function.Injective hi := inj (m+1) (fun y => by dsimp [w]; have := y.isLt; omega)
    have same (z : ℕ) : p.eval (LEQuery.keyOracle w) =
        p.eval (LEQuery.keyOracle (fun y => if y = x then z else w y)) :=
      LEQuery.eval_congr_touched _ _ p fun y hy => by
        have ne : y ≠ x := fun eq => missing (eq ▸ hy)
        simp [ne]
    have eq : msf L lo Finset.univ = msf L hi Finset.univ :=
      (optimalMSFProgram_spec L lo hlo).1.symm.trans
        ((same 0).symm.trans ((same (m+1)).trans (optimalMSFProgram_spec L hi hhi).1))
    have minEdge : x ∈ msf L lo Finset.univ := by
      refine mem_msf_of_mem_edgeCut lo (P := {a}) (Finset.mem_univ _) ?_ ?_
      · refine Graph.mem_edgeCut_iff.mpr ⟨a, b, rfl, rfl, ?_⟩
        intro bad
        have h := congrArg Fin.val (bad : b = a)
        exact Nat.noConfusion h
      · intro y _ _
        simp [lo]
    have diff : ∃ y : Fin m, y ≠ x := by
      let z : Fin m := ⟨0, by omega⟩
      let o : Fin m := ⟨1, by omega⟩
      by_cases h : x = z
      · refine ⟨o, ?_⟩
        rw [h]
        intro bad
        exact Nat.noConfusion (congrArg Fin.val bad)
      · exact ⟨z, Ne.symm h⟩
    obtain ⟨y, hy⟩ := diff
    have lighter : hi y < hi x := by
      simp [hi, hy, w]
    have maxEdge : x ∉ msf L hi Finset.univ :=
      notMem_msf_of_joins hi (X := {y}) (fun _ _ => Finset.mem_univ _)
        (fun f hf => by obtain rfl : f = y := hf; exact lighter)
        (show L x = s(a,b) from rfl) (Joins.of_mem (e := y) rfl rfl)
    exact maxEdge (eq ▸ minEdge)
  have card := LEQuery.card_touched_le ask p
  change used.card ≤ _ at card
  rw [all, Finset.card_univ, Fintype.card_fin] at card
  exact card.trans (Nat.mul_le_mul_left 2
    ((optimalMSFProgram_spec L w hw).2.trans (optimalMSFComparisons_le_worstCase L)))

/-- Numerical recurrence closure for a nonnegative cost with a bounded zero-edge base,
local contribution `a T*(m,n) + b m`, and recursive size at most `(m/2,n/4)`.
The recursive cost hypothesis is supplied by the concrete computation being analyzed. -/
theorem recurrence_le (T : ℕ → ℕ → ℕ) (a b base : ℕ)
    (zero : ∀ n, T 0 n ≤ base)
    (step : ∀ m n, 0 < m → ∃ k v, 2 * k ≤ m ∧ 4 * v ≤ n ∧
      T m n ≤ a * worstCase m n + b * m + T k v) (m n : ℕ) :
    T m n ≤ base + 2 * (a * worstCase m n + b * m) := by
  induction m using Nat.strong_induction_on generalizing n with
  | ind m ih =>
    by_cases hm : m = 0
    · subst m
      exact (zero n).trans (Nat.le_add_right _ _)
    · obtain ⟨k, v, hk, hv, hstep⟩ := step m n (by omega)
      have child := ih k (by omega) v
      have twice : 2 * worstCase k v ≤ worstCase m n :=
        (twice_worstCase_le k v).trans (worstCase_mono hk (by omega))
      have budget : 2*(a*worstCase k v + b * k) ≤ a*worstCase m n + b * m := by
        simpa only [Nat.mul_add, Nat.mul_left_comm 2] using
          Nat.add_le_add (Nat.mul_le_mul_left a twice) (Nat.mul_le_mul_left b hk)
      omega

/-- For at least two edges and vertices the linear term in the recurrence is absorbed by
the native comparison optimum, with an explicit constant independent of the two sizes. -/
theorem recurrence_le_worstCase (T : ℕ → ℕ → ℕ) (a b base : ℕ)
    (zero : ∀ n, T 0 n ≤ base)
    (step : ∀ m n, 0 < m → ∃ k v, 2 * k ≤ m ∧ 4 * v ≤ n ∧
      T m n ≤ a * worstCase m n + b * m + T k v) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    T m n ≤ (base + 2 * a + 4 * b) * worstCase m n := by
  have H := recurrence_le T a b base zero step m n
  have h := edgeCount_le_twice_worstCase hm hn
  have hb := Nat.mul_le_mul_left b h
  have hp : 0 < worstCase m n := by omega
  have hbase := Nat.le_mul_of_pos_right base hp
  calc
    _ ≤ base + 2 * (a * worstCase m n + b * m) := H
    _ ≤ base * worstCase m n + 2 * (a * worstCase m n + b * (2 * worstCase m n)) :=
      Nat.add_le_add hbase (Nat.mul_le_mul_left 2 (Nat.add_le_add_left hb _))
    _ = _ := by ring

end Cslib.Multigraph.OptimalTree
