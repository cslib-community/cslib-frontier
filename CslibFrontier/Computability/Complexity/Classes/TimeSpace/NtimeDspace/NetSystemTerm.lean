/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.CountingSimulation.BlockNetworks
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.NetTable
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# The network's weighted constraint system, accessed by terms

The counter reads the weighted constraint system of a block-counting network
(`NetworkSystem.toSystem`): its constraints are the vertices, the scope of a
constraint is the vertex's port list, and the weight of an assignment is a
table entry. This file gives terms for the arity of a constraint, the variable
at an incidence (the `i`-th port), and the weight at an assignment number, with
the contracts the counter term needs.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.LocalSim

open ProgTerm ProgTerm.Term _root_.Turing _root_.Turing.MultiTapePTM

variable {w : List Bool}

/-! ### Low bits -/

theorem sum_testBit_eq_mod (A : ℕ) : ∀ m : ℕ,
    ∑ r ∈ Finset.range m, (A.testBit r).toNat * 2 ^ r = A % 2 ^ m := by
  intro m
  induction m generalizing A with
  | zero => simp [Nat.mod_one]
  | succ m ih =>
    rw [Finset.sum_range_succ', pow_zero, mul_one]
    have h : ∀ r, (A.testBit (r + 1)).toNat * 2 ^ (r + 1) = 2 * ((A / 2).testBit r).toNat * 2 ^
        r := by
      intro r
      rw [Nat.testBit_succ, pow_succ]; ring
    simp only [h, mul_assoc, ← Finset.mul_sum, ih (A / 2)]
    rw [pow_succ', Nat.mod_mul]
    rcases Nat.mod_two_eq_zero_or_one A with h2 | h2 <;> simp [Nat.testBit_zero, h2] <;> omega

theorem lsbValue_ofFn_testBit (m A : ℕ) :
    Cslib.BitString.lsbValue (List.ofFn fun i : Fin m => A.testBit i) = A % 2 ^ m := by
  rw [List.ofFn_eq_map]
  rw [show (List.finRange m).map (fun i : Fin m => A.testBit i) =
    (List.range m).map A.testBit by
      rw [← List.map_coe_finRange_eq_range, List.map_map]; rfl]
  rw [lsbValue_map_range, sum_testBit_eq_mod]

/-! ### The element at a position of a filtered range -/

theorem getD_filter_range_eq_sum (p : ℕ → Bool) (N i : ℕ) :
    ((List.range N).filter p).getD i 0 =
      ∑ j ∈ Finset.range N, (if p j = true ∧ (List.range j).countP p = i then j else 0) := by
  set l := (List.range N).filter p
  have hnodup : l.Nodup := (List.nodup_range).filter _
  have hidx : ∀ j, j < N → p j = true → l.idxOf j = (List.range j).countP p := fun j hj hp => by
    rw [idxOf_filter_range, if_pos ⟨hj, hp⟩]
  by_cases hi : i < l.length
  · rw [List.getD_eq_getElem _ _ hi]
    have hmem : l[i] ∈ l := List.getElem_mem hi
    have hm := List.mem_filter.mp hmem
    have hN : l[i] < N := List.mem_range.mp hm.1
    rw [Finset.sum_eq_single l[i]]
    · have hc : (List.range l[i]).countP p = i := by
        rw [← hidx _ hN hm.2]
        have := List.get_idxOf hnodup ⟨i, hi⟩
        simpa using this
      rw [if_pos ⟨hm.2, hc⟩]
    · intro j hj hne
      rw [if_neg]
      rintro ⟨hp, hc⟩
      apply hne
      have hjm : j ∈ l := List.mem_filter.mpr ⟨List.mem_range.mpr (Finset.mem_range.mp hj), hp⟩
      rw [← hidx j (Finset.mem_range.mp hj) hp] at hc
      have h1 := List.idxOf_get (l := l) (a := j) (List.idxOf_lt_length_of_mem hjm)
      simp only [List.get_eq_getElem, hc] at h1
      exact h1.symm
    · intro h; exact absurd (Finset.mem_range.mpr hN) h
  · rw [List.getD_eq_default _ _ (by omega)]
    refine (Finset.sum_eq_zero fun j hj => ?_).symm
    rw [if_neg]
    rintro ⟨hp, hc⟩
    have hjm : j ∈ l := List.mem_filter.mpr ⟨List.mem_range.mpr (Finset.mem_range.mp hj), hp⟩
    have := List.idxOf_lt_length_of_mem hjm
    rw [hidx j (Finset.mem_range.mp hj) hp, hc] at this
    exact hi this

/-! ### Accessor terms -/

section Terms

variable (k s : ℕ)

/-- The number of edges, `2 q (3k + 1) m`. -/
def edgesT (qT bT : Term) : Term := mul (const 2) (halvesT k qT (letterBitsT k s bT))

/-- The arity of constraint (vertex) `e`: its number of ports. -/
def arityNT (qT bT σT e : Term) : Term :=
  portCountT k qT (letterBitsT k s bT) σT e (edgesT k s qT bT)

/-- The variable at incidence `(e, i)`: the `i`-th port of vertex `e`. -/
def portAtT (qT bT σT e i : Term) : Term :=
  sumT (edgesT k s qT bT) fun j =>
    mul (mul (portPredT k qT (letterBitsT k s bT) σT e j)
      (eqT (portCountT k qT (letterBitsT k s bT) σT e j) i)) j

variable {State : Type} (e : State ≃ Fin s) (machine : MultiTapePTM k Bool State)

/-- The weight of constraint `e` at the assignment number `A`. -/
def weightNT (RT NT qT bT σT eT A : Term) : Term :=
  tableEntryT k s e machine RT NT qT bT σT eT (mod A (pow2 (arityNT k s qT bT σT eT)))

end Terms

variable {k s : ℕ}

theorem denote_edgesT (qT bT : Term) (env : List ℕ) :
    (edgesT k s qT bT).denote w env =
      2 * (qT.denote w env * (3 * k + 1) * letterBits k s (bT.denote w env)) := by
  simp [edgesT, halvesT, letterBitsT, letterBits]

theorem denote_arityNT {qT bT σT eT : Term} {env : List ℕ} (hq : StableAt w qT env)
    (hb : StableAt w bT env) (hσ : StableAt w σT env) (he : StableAt w eT env) :
    (arityNT k s qT bT σT eT).denote w env =
      (explicitPortsNum k (qT.denote w env) (letterBits k s (bT.denote w env)) (σT.denote w env)
        (eT.denote w env)).length := by
  have hm : StableAt w (letterBitsT k s bT) env := (stableAt_const _ _).mul hb
  have hmv : (letterBitsT k s bT).denote w env = letterBits k s (bT.denote w env) := by
    simp [letterBitsT, letterBits]
  unfold arityNT
  rw [denote_portCountT k _ hq hm hσ he, denote_edgesT, hmv, length_explicitPortsNum]

theorem StableAt.arityNT {qT bT σT eT : Term} {env : List ℕ} (hq : StableAt w qT env)
    (hb : StableAt w bT env) (hσ : StableAt w σT env) (he : StableAt w eT env) :
    StableAt w (arityNT k s qT bT σT eT) env := fun extra => by
  rw [denote_arityNT (hq.extend extra) (hb.extend extra) (hσ.extend extra) (he.extend extra),
    denote_arityNT hq hb hσ he, hq extra, hb extra, hσ extra, he extra]

theorem denote_portAtT {qT bT σT eT : Term} {env : List ℕ} (hq : StableAt w qT env)
    (hb : StableAt w bT env) (hσ : StableAt w σT env) (he : StableAt w eT env) (iT : Term)
    (hi : StableAt w iT env) :
    (portAtT k s qT bT σT eT iT).denote w env =
      (explicitPortsNum k (qT.denote w env) (letterBits k s (bT.denote w env)) (σT.denote w env)
        (eT.denote w env)).getD (iT.denote w env) 0 := by
  have hm : StableAt w (letterBitsT k s bT) env := (stableAt_const _ _).mul hb
  have hmv : (letterBitsT k s bT).denote w env = letterBits k s (bT.denote w env) := by
    simp [letterBitsT, letterBits]
  unfold portAtT explicitPortsNum
  rw [show (fun j => decide (explicitSrcNum k (qT.denote w env) (letterBits k s (bT.denote w env))
      (σT.denote w env) j = eT.denote w env ∨ explicitTgtNum k (qT.denote w env)
      (letterBits k s (bT.denote w env)) j = eT.denote w env)) =
      portPred k (qT.denote w env) (letterBits k s (bT.denote w env)) (σT.denote w env)
        (eT.denote w env) from rfl, getD_filter_range_eq_sum,
    denote_sumT _ _ env (fun j => if portPred k (qT.denote w env) (letterBits k s (bT.denote w env))
      (σT.denote w env) (eT.denote w env) j = true ∧ (List.range j).countP (portPred k
        (qT.denote w env) (letterBits k s (bT.denote w env)) (σT.denote w env) (eT.denote w env)) =
        iT.denote w env then j else 0), denote_edgesT]
  intro acc j
  have hj : StableAt w (lvl env.length) ([acc, j] ++ env) := stableAt_lvl (by simp)
  have h1 := denote_portPredT k (vT := eT) (hq.extend [acc, j]) (hm.extend [acc, j])
    (hσ.extend [acc, j]) hj
  have h2 := denote_portCountT k (lvl env.length) (hq.extend [acc, j]) (hm.extend [acc, j])
    (hσ.extend [acc, j]) (he.extend [acc, j])
  simp only [List.cons_append, List.nil_append] at h1 h2
  rw [denote_mul, denote_mul, h1, denote_eqT, h2]
  simp only [denote_lvl_index, hq.cons₂, hm.cons₂, hσ.cons₂, he.cons₂, hi.cons₂, hmv]
  by_cases hp : portPred k (qT.denote w env) (letterBits k s (bT.denote w env)) (σT.denote w env)
      (eT.denote w env) j <;>
    by_cases hc : (List.range j).countP (portPred k (qT.denote w env)
      (letterBits k s (bT.denote w env)) (σT.denote w env) (eT.denote w env)) = iT.denote w env <;>
    simp [hp, hc]

theorem StableAt.pow2' {a : Term} {env : List ℕ} (h : StableAt w a env) :
    StableAt w (pow2 a) env := fun extra => by rw [denote_pow2, denote_pow2, h extra]

variable {State : Type} {e : State ≃ Fin s} {machine : MultiTapePTM k Bool State}

theorem denote_weightNT [DecidableEq State] {RT NT qT bT σT eT A : Term} {env : List ℕ}
    (hR : StableAt w RT env) (hN : StableAt w NT env) (hq : StableAt w qT env)
    (hb : StableAt w bT env) (hσ : StableAt w σT env) (he : StableAt w eT env)
    (hA : StableAt w A env) (hbpos : 0 < bT.denote w env)
    (hRv : RT.denote w env = radix (bT.denote w env) w.length s)
    (hNv : NT.denote w env = w.length) :
    (weightNT k s e machine RT NT qT bT σT eT A).denote w env =
      tableEntryNum e (bT.denote w env) machine w (qT.denote w env) (σT.denote w env)
        (eT.denote w env)
        (explicitPortsNum k (qT.denote w env) (letterBits k s (bT.denote w env)) (σT.denote w env)
          (eT.denote w env))
        (A.denote w env % 2 ^ (explicitPortsNum k (qT.denote w env)
          (letterBits k s (bT.denote w env)) (σT.denote w env) (eT.denote w env)).length) := by
  have har := StableAt.arityNT (k := k) (s := s) hq hb hσ he
  unfold weightNT
  rw [denote_tableEntryT hR hN hq hb hσ he (hA.mod (StableAt.pow2' har)) hbpos hRv hNv, denote_mod,
    denote_pow2, denote_arityNT hq hb hσ he]

end Cslib.Complexity.NtimeDspace.LocalSim
