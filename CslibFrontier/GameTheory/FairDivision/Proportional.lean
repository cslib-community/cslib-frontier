/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.FairDivision.Basic
public import Cslib.Algorithms.Lean.Query.Bounds
public import Mathlib.Data.Nat.Log
import CslibFrontier.Algorithms.Lean.Query.FreeM.MOfFn
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Proportional Cake-Cutting Protocols: Cut-and-Choose, Dubins–Spanier, and Even–Paz

Formalizes three classical discrete cake-cutting protocols in the Robertson–Webb query model
(`FreeM (RWQuery (Fin n))`) over arbitrary nonatomic finite additive valuations (`CakeValuation`) on
`[0, 1]`:

1. **Cut-and-Choose (`n = 2`)** ([Steinhaus1948]; [RobertsonWebb1998]): Player `0` cuts `[0, 1]`
   into two pieces of equal `v₀`-value `1 / 2`, and Player `1` evaluates `[0, c]` and chooses the
   higher-valued piece (`2` Robertson–Webb queries, `1` physical cut). The resulting contiguous
   division is both **envy-free** and **proportional** (`≥ 1 / 2`).
2. **Dubins–Spanier discrete protocol (`n` agents)** ([DubinsSpanier1961]; [RobertsonWebb1998]):
   By induction on the `m` remaining active agents (`m = n, n - 1, …, 1`), while `m ≥ 2` every
   active agent marks a cut point of value `1 / n` from the current left boundary `a`, the agent
   with the leftmost mark `c` receives `[a, c]`, and the remaining `m - 1` agents recurse on
   `[c, 1]`; the final agent receives `[a, 1]` (`n - 1` cuts, contiguous bundles, exact query count
   `n * (n + 1) / 2 - 1 ≤ n ^ 2` for `n ≥ 1`, every agent receives value `≥ 1 / n`).
3. **Even–Paz divide-and-conquer protocol (`n` agents)** ([EvenPaz1984]; [RobertsonWebb1998]):
   For `m ≥ 2` active agents on `[a, b]`, every active agent queries `v_i(a, b)` and marks a cut
   point of value `(⌊m / 2⌋ / m) · v_i(a, b)`; cutting at the `⌊m / 2⌋`-th mark splits the agents
   into groups of sizes `⌊m / 2⌋` on `[a, c]` and `m - ⌊m / 2⌋` on `[c, b]`. Produces a contiguous
   proportional division (`≥ 1 / n`) with `n - 1` cuts and at most `2 * n * Nat.clog 2 n`
   (`O(n log n)`) Robertson–Webb queries.

## Main definitions

* `Cslib.GameTheory.FairDivision.cutAndChooseQ`,
  `Cslib.GameTheory.FairDivision.cutAndChoose`: two-player Cut-and-Choose protocol in `FreeM` and
  its canonical evaluation.
* `Cslib.GameTheory.FairDivision.dubinsSpanierQ`,
  `Cslib.GameTheory.FairDivision.dubinsSpanier`: `n`-player discrete Dubins–Spanier protocol in
  `FreeM` and its canonical evaluation.
* `Cslib.GameTheory.FairDivision.evenPazQ`,
  `Cslib.GameTheory.FairDivision.evenPaz`: `n`-player Even–Paz divide-and-conquer protocol in
  `FreeM` and its canonical evaluation.

## Main results

* `Cslib.GameTheory.FairDivision.isValidPartition_cutAndChooseQ`,
  `Cslib.GameTheory.FairDivision.isEnvyFree_cutAndChooseQ`,
  `Cslib.GameTheory.FairDivision.isProportional_cutAndChooseQ`,
  `Cslib.GameTheory.FairDivision.countQueries_cutAndChooseQ`: Cut-and-Choose produces an envy-free
  and proportional `1`-cut contiguous partition using `2` queries.
* `Cslib.GameTheory.FairDivision.isValidPartition_dubinsSpanierQ`,
  `Cslib.GameTheory.FairDivision.isProportional_dubinsSpanierQ`,
  `Cslib.GameTheory.FairDivision.countQueries_dubinsSpanierQ`,
  `Cslib.GameTheory.FairDivision.countQueries_dubinsSpanierQ_le`,
  `Cslib.GameTheory.FairDivision.upperBound_dubinsSpanierNatQ`: Dubins–Spanier produces an
  `(n - 1)`-cut contiguous proportional partition using `n * (n + 1) / 2 - 1 ≤ n ^ 2` queries.
* `Cslib.GameTheory.FairDivision.isValidPartition_evenPazQ`,
  `Cslib.GameTheory.FairDivision.isProportional_evenPazQ`,
  `Cslib.GameTheory.FairDivision.countQueries_evenPazQ_le`,
  `Cslib.GameTheory.FairDivision.upperBound_evenPazNatQ`: Even–Paz produces an `(n - 1)`-cut
  contiguous proportional partition in at most `2 * n * Nat.clog 2 n` (`O(n log n)`) queries.

## References

* [H. Steinhaus, *The Problem of Fair Division*][Steinhaus1948]
* [L. E. Dubins and E. H. Spanier, *How to Cut a Cake Fairly*][DubinsSpanier1961]
* [S. Even and A. Paz, *A Note on Cake Cutting*][EvenPaz1984]
* [J. Robertson and W. Webb, *Cake-Cutting Algorithms: Be Fair If You Can*][RobertsonWebb1998]
-/

public section

namespace Cslib.GameTheory.FairDivision

open Cslib (FreeM)
open Cslib.Query (UpperBound)

/-! ### 1. Two-Player Cut-and-Choose (`n = 2`) -/

/-- Two-player **Cut-and-Choose** protocol in the Robertson–Webb query model ([Steinhaus1948]):
Player `0` cuts `[0, 1]` at `c` with `v₀(0, c) = 1 / 2`, and Player `1` evaluates `[0, c]` and
takes `[0, c]` if `1 / 2 ≤ v₁(0, c)` and `[c, 1]` otherwise, leaving the remaining piece to
Player `0`. -/
@[expose] noncomputable def cutAndChooseQ : FreeM (RWQuery (Fin 2)) (DividedCake 2) := do
  let c ← RWQuery.cutIn 0 0 1 (1 / 2)
  let vLeft ← RWQuery.evalAsk 1 0 c
  if 1 / 2 ≤ vLeft then
    pure
      { cuts := [c]
        pieces := fun i => if i = 0 then [⟨c, 1⟩] else [⟨0, c⟩] }
  else
    pure
      { cuts := [c]
        pieces := fun i => if i = 0 then [⟨0, c⟩] else [⟨c, 1⟩] }

/-- Canonical pure evaluation of `cutAndChooseQ` against `RWQuery.oracleOf v`. -/
@[expose] noncomputable def cutAndChoose (v : Fin 2 → CakeValuation) : DividedCake 2 :=
  cutAndChooseQ.eval (RWQuery.oracleOf v)

/-- `cutAndChooseQ` makes exactly `2` Robertson–Webb queries against any oracle. -/
@[simp]
theorem countQueries_cutAndChooseQ
    (oracle : {ι : Type} → RWQuery (Fin 2) ι → ι) :
    cutAndChooseQ.countQueries oracle = 2 := by
  simp only [cutAndChooseQ, FreeM.countQueries_bind, RWQuery.countQueries_cutIn,
    RWQuery.countQueries_evalAsk]
  split_ifs <;> rfl

/-- `cutAndChooseQ` makes exactly `1` physical cut on `[0, 1]`. -/
@[simp]
theorem numCuts_cutAndChooseQ
    (oracle : {ι : Type} → RWQuery (Fin 2) ι → ι) :
    (cutAndChooseQ.eval oracle).numCuts = 1 := by
  simp only [cutAndChooseQ, FreeM.eval_bind]
  split_ifs <;> rfl

/-- `cutAndChooseQ` assigns each player a single contiguous interval. -/
theorem isContiguous_cutAndChooseQ
    (oracle : {ι : Type} → RWQuery (Fin 2) ι → ι) :
    (cutAndChooseQ.eval oracle).IsContiguous := by
  intro i
  simp only [cutAndChooseQ, FreeM.eval_bind]
  split_ifs <;> simp only [FreeM.eval_pure] <;> split_ifs <;> rfl

/-- `cutAndChooseQ` always produces a valid partition of `[0, 1]`. -/
theorem isValidPartition_cutAndChooseQ
    (oracle : {ι : Type} → RWQuery (Fin 2) ι → ι) :
    (cutAndChooseQ.eval oracle).IsValidPartition := by
  set c := (RWQuery.cutIn (0 : Fin 2) 0 1 (1 / 2)).eval oracle
  have hc := RWQuery.eval_cutIn_mem_Icc oracle (0 : Fin 2) (by norm_num : (0 : ℝ) ≤ 1) (1 / 2)
  have hofFn : ∀ f : Fin 2 → List CakePiece, List.ofFn f = [f 0, f 1] := fun _ => rfl
  simp only [cutAndChooseQ, FreeM.eval_bind]
  split_ifs <;> refine ⟨⟨hc.1, hc.2⟩, ?_⟩ <;>
    simp only [FreeM.eval_pure, DividedCake.allPieces, hofFn, Fin.isValue, ↓reduceIte,
      one_ne_zero, List.flatten_cons, List.flatten_nil, List.singleton_append, List.append_nil,
      intervalsOfCuts, intervalsOfCutsOn]
  · exact List.Perm.swap (⟨0, c⟩ : CakePiece) ⟨c, 1⟩ []
  · exact List.Perm.refl _

/-- **Cut-and-Choose envy-freeness:** for every two-player valuation profile `v` and valid
Robertson–Webb oracle `oracle`, `cutAndChooseQ` outputs an envy-free division. -/
theorem isEnvyFree_cutAndChooseQ {v : Fin 2 → CakeValuation}
    {oracle : {ι : Type} → RWQuery (Fin 2) ι → ι} (ho : RWQuery.IsValidOracle v oracle) :
    (cutAndChooseQ.eval oracle).IsEnvyFree v := by
  have hhalf_hi : (1 / 2 : ℝ) ≤ v 0 0 1 := by
    rw [(v 0).apply_zero_one]
    norm_num
  obtain ⟨⟨hc0, hc1⟩, hvc0⟩ :=
    ho.eval_cutIn_spec 0 le_rfl (by norm_num) le_rfl (by norm_num) hhalf_hi
  set c := (RWQuery.cutIn (0 : Fin 2) 0 1 (1 / 2)).eval oracle
  have hadd0 := (v 0).val_add le_rfl hc0 hc1 le_rfl
  have h01 := (v 0).apply_zero_one
  have hv1_sum : v 1 0 c + v 1 c 1 = 1 := by
    rw [(v 1).val_add le_rfl hc0 hc1 le_rfl, (v 1).apply_zero_one]
  intro i j
  simp only [cutAndChooseQ, FreeM.eval_bind,
    show (RWQuery.cutIn (0 : Fin 2) 0 1 (1 / 2)).eval oracle = c from rfl,
    ho.eval_evalAsk 1 0 c]
  split_ifs <;> fin_cases i <;> fin_cases j <;>
    simp only [FreeM.eval_pure, Fin.zero_eta, Fin.mk_one, Fin.isValue, ↓reduceIte, one_ne_zero,
      CakeValuation.bundleVal_singleton] <;> linarith

/-- **Cut-and-Choose proportionality:** for every two-player valuation profile `v` and valid
Robertson–Webb oracle `oracle`, both players receive value at least `1 / 2`. -/
theorem isProportional_cutAndChooseQ {v : Fin 2 → CakeValuation}
    {oracle : {ι : Type} → RWQuery (Fin 2) ι → ι} (ho : RWQuery.IsValidOracle v oracle) :
    (cutAndChooseQ.eval oracle).IsProportional v :=
  (isEnvyFree_cutAndChooseQ ho).isProportional (isValidPartition_cutAndChooseQ oracle)

/-! ### Shared contiguous-subdivision assembly and agent-index query lifting -/

/-- Recursive subinterval division output for `m` active agents: interior cuts `cuts` and one
assigned `CakePiece` per local index `r : Fin m`. -/
private structure SubDivision (m : ℕ) where
  cuts : List ℝ
  pieceOf : Fin m → CakePiece

/-- Wrap a root `SubDivision n` into a contiguous `DividedCake n`. -/
private def SubDivision.toDividedCake {n : ℕ} (S : SubDivision n) : DividedCake n where
  cuts := S.cuts
  pieces i := [S.pieceOf i]

private theorem flatten_ofFn_singleton {α : Type} {n : ℕ} (f : Fin n → α) :
    (List.ofFn fun i => [f i]).flatten = List.ofFn f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [List.ofFn_succ, List.flatten_cons, List.singleton_append]
    exact congrArg (f 0 :: ·) (ih (f ∘ Fin.succ))

private theorem SubDivision.toDividedCake_valid {n : ℕ} {S : SubDivision n}
    (h : OrderedCutsOn 0 1 S.cuts ∧ S.cuts.length = n - 1 ∧
      (List.ofFn S.pieceOf).Perm (intervalsOfCutsOn 0 1 S.cuts)) :
    S.toDividedCake.IsValidPartition ∧ S.toDividedCake.numCuts = n - 1 ∧
      S.toDividedCake.IsContiguous :=
  ⟨⟨h.1, by simpa only [SubDivision.toDividedCake, DividedCake.allPieces,
      flatten_ofFn_singleton, intervalsOfCuts] using h.2.2⟩, h.2.1, fun _ => rfl⟩

/-- Reindexing `List.ofFn` by an equivalence `e : Fin m₁ ≃ Fin m₂` yields a `List.Perm`. -/
private theorem ofFn_comp_equiv_perm {α : Type} {m₁ m₂ : ℕ} (g : Fin m₂ → α)
    (e : Fin m₁ ≃ Fin m₂) :
    (List.ofFn (g ∘ e)).Perm (List.ofFn g) := by
  rw [List.ofFn_eq_map, List.ofFn_eq_map, ← List.map_map]
  refine List.Perm.map g ?_
  refine List.perm_iff_count.mpr fun x => ?_
  have h1 : ((List.finRange m₁).map e).Nodup :=
    (List.nodup_finRange m₁).map e.injective
  have hmem1 : x ∈ (List.finRange m₁).map e :=
    List.mem_map.mpr ⟨e.symm x, List.mem_finRange _, e.apply_symm_apply x⟩
  rw [List.count_eq_one_of_mem h1 hmem1,
    List.count_eq_one_of_mem (List.nodup_finRange m₂) (List.mem_finRange x)]

private theorem countQueries_mOfFn_const {Q : Type → Type}
    (oracle : {ι : Type} → Q ι → ι) {m c : ℕ} {α : Type}
    (f : Fin m → FreeM Q α) (hc : ∀ r : Fin m, (f r).countQueries oracle = c) :
    (List.Vector.mOfFn f).countQueries oracle = m * c := by
  rw [FreeM.countQueries_eq_cost_one, Cslib.FreeM.cost_mOfFn]
  have h' : ∀ r : Fin m, (f r).cost oracle (fun _ => 1) = c := hc
  simp only [h', Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

/-! ### 2. Dubins–Spanier Proportional Division (`n` Agents, `O(n²)` Queries) -/

private noncomputable def dubinsSpanierAux (n : ℕ) :
    ∀ (m : ℕ), ℝ → (Fin m → Fin n) → FreeM (RWQuery (Fin n)) (SubDivision m)
  | 0, _, _ => pure ⟨[], Fin.elim0⟩
  | 1, a, _ => pure ⟨[], fun _ => ⟨a, 1⟩⟩
  | k + 2, a, agents => do
      let marks ← List.Vector.mOfFn (fun r : Fin (k + 2) =>
        RWQuery.cutIn (agents r) a 1 (1 / (n : ℝ)))
      let σ : Equiv.Perm (Fin (k + 2)) := Tuple.sort marks.get
      let c : ℝ := marks.get (σ 0)
      let sub ← dubinsSpanierAux n (k + 1) c (fun s : Fin (k + 1) => agents (σ s.succ))
      pure
        { cuts := c :: sub.cuts
          pieceOf := fun r => Fin.cases ⟨a, c⟩ sub.pieceOf (σ.symm r) }

/-- **`n`-player discrete Dubins–Spanier protocol** in the Robertson–Webb query model
([DubinsSpanier1961]; [RobertsonWebb1998]). -/
noncomputable def dubinsSpanierQ (n : ℕ) :
    FreeM (RWQuery (Fin n)) (DividedCake n) :=
  SubDivision.toDividedCake <$> dubinsSpanierAux n n 0 id

/-- Size-uniform `RWQuery ℕ` packaging of `dubinsSpanierQ` for `Cslib.Query.UpperBound`. -/
@[expose] noncomputable def dubinsSpanierNatQ (n : ℕ) :
    FreeM (RWQuery ℕ) (Σ k : ℕ, DividedCake k) :=
  (fun D => ⟨n, D⟩) <$> RWQuery.liftFin (dubinsSpanierQ n)

/-- Canonical pure evaluation of `dubinsSpanierQ n` against `RWQuery.oracleOf v`. -/
@[expose] noncomputable def dubinsSpanier {n : ℕ} (v : Fin n → CakeValuation) : DividedCake n :=
  (dubinsSpanierQ n).eval (RWQuery.oracleOf v)

private theorem countQueries_dubinsSpanierAux (n : ℕ)
    (oracle : {ι : Type} → RWQuery (Fin n) ι → ι) :
    ∀ (m : ℕ) (_hm : 1 ≤ m) (a : ℝ) (agents : Fin m → Fin n),
      (dubinsSpanierAux n m a agents).countQueries oracle = m * (m + 1) / 2 - 1
  | 0, hm, _, _ => absurd hm (by omega)
  | 1, _, _, _ => rfl
  | k + 2, _, a, agents => by
      simp only [dubinsSpanierAux, FreeM.countQueries_bind, FreeM.countQueries_pure, add_zero]
      rw [countQueries_mOfFn_const oracle _ (fun _ => RWQuery.countQueries_cutIn _ _ _ _ _),
        Nat.mul_one]
      rw [countQueries_dubinsSpanierAux n oracle (k + 1) (by omega)]
      have heven : ∃ q, (k + 1) * (k + 1 + 1) = 2 * q := by
        rcases Nat.even_or_odd k with ⟨t, rfl⟩ | ⟨t, rfl⟩
        · exact ⟨(2 * t + 1) * (t + 1), by ring⟩
        · exact ⟨(t + 1) * (2 * t + 3), by ring⟩
      obtain ⟨q, hq⟩ := heven
      have hq_pos : 1 ≤ q := by nlinarith
      have hnext : (k + 2) * (k + 2 + 1) = 2 * (q + (k + 2)) := by linarith
      rw [hq, hnext, Nat.mul_div_right q (by omega), Nat.mul_div_right (q + (k + 2)) (by omega)]
      omega

/-- Exact Robertson–Webb query count of `dubinsSpanierQ n` for `1 ≤ n`:
`n * (n + 1) / 2 - 1`. -/
theorem countQueries_dubinsSpanierQ {n : ℕ} (hn : 1 ≤ n)
    (oracle : {ι : Type} → RWQuery (Fin n) ι → ι) :
    (dubinsSpanierQ n).countQueries oracle = n * (n + 1) / 2 - 1 := by
  rw [dubinsSpanierQ, FreeM.countQueries_map]
  exact countQueries_dubinsSpanierAux n oracle n hn 0 id

/-- Quadratic query bound for `dubinsSpanierQ n`: at most `n ^ 2` Robertson–Webb queries for every
`n` and every oracle. -/
theorem countQueries_dubinsSpanierQ_le (n : ℕ)
    (oracle : {ι : Type} → RWQuery (Fin n) ι → ι) :
    (dubinsSpanierQ n).countQueries oracle ≤ n ^ 2 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [dubinsSpanierQ, FreeM.countQueries_map]
    simp only [dubinsSpanierAux, FreeM.countQueries_pure, zero_pow (by omega : 2 ≠ 0), le_refl]
  · rw [countQueries_dubinsSpanierQ hn oracle]
    have hle : n * (n + 1) ≤ 2 * n ^ 2 := by nlinarith
    omega

/-- `Cslib.Query.UpperBound` formulation (`n ^ 2`) for Dubins–Spanier across all `n : ℕ`. -/
theorem upperBound_dubinsSpanierNatQ :
    UpperBound dubinsSpanierNatQ id (fun n => n ^ 2) :=
  UpperBound.of_pointwise
    (fun _ _ h => Nat.pow_le_pow_left h 2)
    fun oracle n => by
      simp only [dubinsSpanierNatQ, FreeM.countQueries_map, RWQuery.countQueries_liftFin, id_eq]
      exact countQueries_dubinsSpanierQ_le n _

private theorem dubinsSpanierAux_partition (n : ℕ)
    (oracle : {ι : Type} → RWQuery (Fin n) ι → ι) :
    ∀ (m : ℕ) (_hm : 1 ≤ m) {a : ℝ} (_ha : a ≤ 1) (agents : Fin m → Fin n),
      let S := (dubinsSpanierAux n m a agents).eval oracle
      OrderedCutsOn a 1 S.cuts ∧
        S.cuts.length = m - 1 ∧
        (List.ofFn S.pieceOf).Perm (intervalsOfCutsOn a 1 S.cuts)
  | 0, hm, _, _, _ => absurd hm (by omega)
  | 1, _, _, ha, _ => by
      simp only [dubinsSpanierAux, FreeM.eval_pure, orderedCutsOn_nil, List.length_nil,
        Nat.sub_self, intervalsOfCutsOn]
      exact ⟨ha, trivial, List.Perm.refl _⟩
  | k + 2, _, a, ha, agents => by
      simp only [dubinsSpanierAux, FreeM.eval_bind, FreeM.eval_pure, Cslib.FreeM.eval_mOfFn]
      set marks := List.Vector.ofFn fun r : Fin (k + 2) =>
        (RWQuery.cutIn (agents r) a 1 (1 / (n : ℝ))).eval oracle
      set σ : Equiv.Perm (Fin (k + 2)) := Tuple.sort marks.get
      set c : ℝ := marks.get (σ 0)
      have hc_mem : c ∈ Set.Icc a 1 := by
        simp only [c, marks, List.Vector.get_ofFn]
        exact RWQuery.eval_cutIn_mem_Icc oracle _ ha _
      obtain ⟨hord_sub, hlen_sub, hperm_sub⟩ :=
        dubinsSpanierAux_partition n oracle (k + 1) (by omega) hc_mem.2
          (fun s : Fin (k + 1) => agents (σ s.succ))
      refine ⟨⟨hc_mem.1, hord_sub⟩, by simp only [List.length_cons, hlen_sub]; omega, ?_⟩
      set sub := (dubinsSpanierAux n (k + 1) c (fun s => agents (σ s.succ))).eval oracle
      set pieceOf : Fin (k + 2) → CakePiece :=
        fun r => Fin.cases ⟨a, c⟩ sub.pieceOf (σ.symm r)
      have hcomp : pieceOf ∘ σ = Fin.cases ⟨a, c⟩ sub.pieceOf :=
        funext fun j => by simp only [Function.comp_apply, pieceOf, Equiv.symm_apply_apply]
      refine (ofFn_comp_equiv_perm pieceOf σ).symm.trans ?_
      rw [hcomp, List.ofFn_succ, Fin.cases_zero]
      exact hperm_sub.cons ⟨a, c⟩

/-- For `1 ≤ n`, `dubinsSpanierQ n` produces a valid `(n - 1)`-cut contiguous partition of `[0, 1]`
against any oracle. -/
theorem isValidPartition_dubinsSpanierQ {n : ℕ} (hn : 1 ≤ n)
    (oracle : {ι : Type} → RWQuery (Fin n) ι → ι) :
    ((dubinsSpanierQ n).eval oracle).IsValidPartition ∧
      ((dubinsSpanierQ n).eval oracle).numCuts = n - 1 ∧
      ((dubinsSpanierQ n).eval oracle).IsContiguous := by
  rw [dubinsSpanierQ, FreeM.eval_map]
  exact SubDivision.toDividedCake_valid
    (dubinsSpanierAux_partition n oracle n hn (by norm_num : (0 : ℝ) ≤ 1) id)

private theorem dubinsSpanierAux_proportional {n : ℕ} {v : Fin n → CakeValuation}
    {oracle : {ι : Type} → RWQuery (Fin n) ι → ι} (ho : RWQuery.IsValidOracle v oracle) :
    ∀ (m : ℕ) {a : ℝ} (_ha0 : 0 ≤ a) (_ha1 : a ≤ 1) (agents : Fin m → Fin n)
      (_hrem : ∀ r : Fin m, (m : ℝ) / (n : ℝ) ≤ v (agents r) a 1),
      ∀ r : Fin m,
        1 / (n : ℝ) ≤
          (v (agents r)).pieceVal (((dubinsSpanierAux n m a agents).eval oracle).pieceOf r)
  | 0, _, _, _, _, _, r => Fin.elim0 r
  | 1, _, _, _, _, hrem, r => by
      simp only [dubinsSpanierAux, FreeM.eval_pure, CakeValuation.pieceVal]
      have h := hrem r
      simpa only [Nat.cast_one] using h
  | k + 2, a, ha0, ha1, agents, hrem, r => by
      have hn_pos : 0 < n := (agents 0).pos
      have hn_real : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
      simp only [dubinsSpanierAux, FreeM.eval_bind, FreeM.eval_pure, Cslib.FreeM.eval_mOfFn]
      set markFn : Fin (k + 2) → ℝ := fun j =>
        (RWQuery.cutIn (agents j) a 1 (1 / (n : ℝ))).eval oracle
      have hmark_spec : ∀ j : Fin (k + 2),
          markFn j ∈ Set.Icc a 1 ∧ v (agents j) a (markFn j) = 1 / (n : ℝ) := by
        intro j
        have h1_le : 1 / (n : ℝ) ≤ v (agents j) a 1 := by
          have hj := hrem j
          have h1m : (1 : ℝ) ≤ (k + 2 : ℕ) := by exact_mod_cast (by omega : 1 ≤ k + 2)
          exact (div_le_div_of_nonneg_right h1m (Nat.cast_nonneg n)).trans hj
        exact ho.eval_cutIn_spec (agents j) ha0 ha1 le_rfl hn_real h1_le
      set marks := List.Vector.ofFn markFn
      have hmarks_get : marks.get = markFn := funext fun j => List.Vector.get_ofFn markFn j
      set σ : Equiv.Perm (Fin (k + 2)) := Tuple.sort marks.get
      set c : ℝ := marks.get (σ 0)
      have hc_bounds : a ≤ c ∧ c ≤ 1 := by
        rw [show c = markFn (σ 0) by rw [← hmarks_get]]
        exact (hmark_spec (σ 0)).1
      have hrem_next : ∀ s : Fin (k + 1),
          ((k + 1 : ℕ) : ℝ) / (n : ℝ) ≤ v (agents (σ s.succ)) c 1 := by
        intro s
        have hle_mark : c ≤ markFn (σ s.succ) := by
          rw [← hmarks_get]
          exact Tuple.monotone_sort marks.get (Fin.zero_le s.succ)
        have hv_ac : v (agents (σ s.succ)) a c ≤ 1 / (n : ℝ) := by
          rw [← (hmark_spec (σ s.succ)).2]
          exact (v (agents (σ s.succ))).apply_mono_right ha0 hle_mark
            (hmark_spec (σ s.succ)).1.2
        have hadd := (v (agents (σ s.succ))).val_add ha0 hc_bounds.1 hc_bounds.2 le_rfl
        have htot := hrem (σ s.succ)
        have hcast : ((k + 2 : ℕ) : ℝ) / (n : ℝ) - 1 / (n : ℝ) =
            ((k + 1 : ℕ) : ℝ) / (n : ℝ) := by
          push_cast
          ring
        linarith
      set j := σ.symm r
      have hr : agents r = agents (σ j) := by rw [Equiv.apply_symm_apply]
      rw [hr]
      refine Fin.cases ?_ (fun s => ?_) j
      · simp only [Fin.cases_zero, CakeValuation.pieceVal]
        rw [show c = markFn (σ 0) by rw [← hmarks_get], (hmark_spec (σ 0)).2]
      · simp only [Fin.cases_succ]
        exact dubinsSpanierAux_proportional ho (k + 1) (ha0.trans hc_bounds.1) hc_bounds.2
          (fun t => agents (σ t.succ)) hrem_next s

/-- **Dubins–Spanier proportionality:** for every `n`-agent valuation profile `v` and every valid
Robertson–Webb oracle `oracle`, `dubinsSpanierQ n` gives every agent value at least `1 / n`. -/
theorem isProportional_dubinsSpanierQ {n : ℕ} {v : Fin n → CakeValuation}
    {oracle : {ι : Type} → RWQuery (Fin n) ι → ι} (ho : RWQuery.IsValidOracle v oracle) :
    ((dubinsSpanierQ n).eval oracle).IsProportional v := by
  intro i
  rw [dubinsSpanierQ, FreeM.eval_map]
  dsimp only [SubDivision.toDividedCake]
  rw [CakeValuation.bundleVal_singleton, ← CakeValuation.pieceVal]
  have hrem : ∀ r : Fin n, (n : ℝ) / (n : ℝ) ≤ v r 0 1 := by
    intro r
    have hn_ne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr r.pos.ne'
    rw [div_self hn_ne, (v r).apply_zero_one]
  exact dubinsSpanierAux_proportional ho n le_rfl (by norm_num) id hrem i

/-! ### 3. Even–Paz Divide-and-Conquer Proportional Division (`n` Agents, `O(n log n)` Queries) -/

private noncomputable def evenPazMarkQuery {n : ℕ} (a b : ℝ) (k m : ℕ) (i : Fin n) :
    FreeM (RWQuery (Fin n)) ℝ := do
  let total ← RWQuery.evalAsk i a b
  RWQuery.cutIn i a b (((k : ℝ) / (m : ℝ)) * total)

private theorem countQueries_evenPazMarkQuery {n : ℕ}
    (oracle : {ι : Type} → RWQuery (Fin n) ι → ι) (a b : ℝ) (k m : ℕ) (i : Fin n) :
    (evenPazMarkQuery a b k m i).countQueries oracle = 2 := by
  simp only [evenPazMarkQuery, FreeM.countQueries_bind, RWQuery.countQueries_evalAsk,
    RWQuery.countQueries_cutIn]

/-- Direct index split equivalence `Fin k ⊕ Fin (m - k) ≃ Fin m` for `k ≤ m`. -/
private def splitFinEquiv {m : ℕ} (k : ℕ) (hk : k ≤ m) :
    Fin k ⊕ Fin (m - k) ≃ Fin m where
  toFun
    | .inl r => ⟨r.1, by omega⟩
    | .inr r => ⟨k + r.1, by omega⟩
  invFun j :=
    if h : j.1 < k then .inl ⟨j.1, h⟩ else .inr ⟨j.1 - k, by omega⟩
  left_inv
    | .inl r => by simp only [r.2, ↓reduceDIte]
    | .inr r => by
        have hnot : ¬ k + r.1 < k := by omega
        simp only [hnot, ↓reduceDIte, Nat.add_sub_cancel_left]
  right_inv j := by
    by_cases h : j.1 < k
    · simp only [h, ↓reduceDIte]
    · simp only [h, ↓reduceDIte]
      exact Fin.ext (by dsimp only; omega)

private theorem ofFn_sumElim_splitFinEquiv {α : Type} {m k : ℕ} (hk : k ≤ m)
    (fL : Fin k → α) (fR : Fin (m - k) → α) :
    List.ofFn (Sum.elim fL fR ∘ (splitFinEquiv k hk).symm) =
      List.ofFn fL ++ List.ofFn fR := by
  refine List.ext_getElem ?_ fun i hi1 hi2 => ?_
  · simp only [List.length_ofFn, List.length_append]
    omega
  · simp only [List.length_ofFn] at hi1
    rw [List.getElem_ofFn]
    by_cases hik : i < k
    · rw [List.getElem_append_left (by simp only [List.length_ofFn]; exact hik),
        List.getElem_ofFn]
      simp only [Function.comp_apply, splitFinEquiv, Equiv.coe_fn_symm_mk, hik, ↓reduceDIte,
        Sum.elim_inl]
    · rw [List.getElem_append_right (by simp only [List.length_ofFn]; omega),
        List.getElem_ofFn]
      simp only [Function.comp_apply, splitFinEquiv, Equiv.coe_fn_symm_mk, hik, ↓reduceDIte,
        Sum.elim_inr, List.length_ofFn]

private noncomputable def evenPazAux (n : ℕ) (m : ℕ) (a b : ℝ) (agents : Fin m → Fin n) :
    FreeM (RWQuery (Fin n)) (SubDivision m) :=
  if hm0 : m = 0 then
    pure ⟨[], fun r => Fin.elim0 (hm0 ▸ r)⟩
  else if _hm1 : m = 1 then
    pure ⟨[], fun _ => ⟨a, b⟩⟩
  else do
    let k : ℕ := m / 2
    let marks ← List.Vector.mOfFn (fun r : Fin m => evenPazMarkQuery a b k m (agents r))
    let σ : Equiv.Perm (Fin m) := Tuple.sort marks.get
    let pivotIdx : Fin m := ⟨k - 1, by omega⟩
    let c : ℝ := marks.get (σ pivotIdx)
    let e : Fin k ⊕ Fin (m - k) ≃ Fin m := splitFinEquiv k (Nat.div_le_self m 2)
    let subL ← evenPazAux n k a c (fun r : Fin k => agents (σ (e (.inl r))))
    let subR ← evenPazAux n (m - k) c b (fun r : Fin (m - k) => agents (σ (e (.inr r))))
    pure
      { cuts := subL.cuts ++ c :: subR.cuts
        pieceOf := fun r => Sum.elim subL.pieceOf subR.pieceOf (e.symm (σ.symm r)) }
termination_by m
decreasing_by all_goals omega

/-- **`n`-player Even–Paz divide-and-conquer protocol** in the Robertson–Webb query model
([EvenPaz1984]; [RobertsonWebb1998]). -/
noncomputable def evenPazQ (n : ℕ) :
    FreeM (RWQuery (Fin n)) (DividedCake n) :=
  SubDivision.toDividedCake <$> evenPazAux n n 0 1 id

/-- Size-uniform `RWQuery ℕ` packaging of `evenPazQ` for `Cslib.Query.UpperBound`. -/
@[expose] noncomputable def evenPazNatQ (n : ℕ) :
    FreeM (RWQuery ℕ) (Σ k : ℕ, DividedCake k) :=
  (fun D => ⟨n, D⟩) <$> RWQuery.liftFin (evenPazQ n)

/-- Canonical pure evaluation of `evenPazQ n` against `RWQuery.oracleOf v`. -/
@[expose] noncomputable def evenPaz {n : ℕ} (v : Fin n → CakeValuation) : DividedCake n :=
  (evenPazQ n).eval (RWQuery.oracleOf v)

private theorem clog_half_le_pred {m : ℕ} (hm : 2 ≤ m) :
    Nat.clog 2 (m / 2) ≤ Nat.clog 2 m - 1 ∧
      Nat.clog 2 (m - m / 2) ≤ Nat.clog 2 m - 1 := by
  have hr_pos : 1 ≤ Nat.clog 2 m := by
    have h1 : 0 < Nat.clog 2 m := Nat.clog_pos (by omega) (by omega)
    omega
  have hpow : m ≤ 2 ^ Nat.clog 2 m := Nat.le_pow_clog (by omega) m
  have hexp : 2 ^ Nat.clog 2 m = 2 * 2 ^ (Nat.clog 2 m - 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel hr_pos, Nat.pow_succ, Nat.mul_comm]
  set P := 2 ^ (Nat.clog 2 m - 1)
  have hk_le : m / 2 ≤ P := by omega
  have hmk_le : m - m / 2 ≤ P := by omega
  exact ⟨(Nat.clog_le_iff_le_pow (by omega)).mpr hk_le,
    (Nat.clog_le_iff_le_pow (by omega)).mpr hmk_le⟩

private theorem countQueries_evenPazAux_le (n : ℕ)
    (oracle : {ι : Type} → RWQuery (Fin n) ι → ι) :
    ∀ (m : ℕ) (a b : ℝ) (agents : Fin m → Fin n),
      (evenPazAux n m a b agents).countQueries oracle ≤ 2 * m * Nat.clog 2 m := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro a b agents
    unfold evenPazAux
    split_ifs with hm0 hm1
    · subst hm0
      simp only [FreeM.countQueries_pure, Nat.mul_zero, Nat.zero_mul, le_refl]
    · subst hm1
      simp only [FreeM.countQueries_pure, Nat.clog_one_right, Nat.mul_zero, le_refl]
    · have hm2 : 2 ≤ m := by omega
      simp only [FreeM.countQueries_bind, FreeM.countQueries_pure, add_zero,
        Cslib.FreeM.eval_mOfFn]
      rw [countQueries_mOfFn_const oracle _ (fun _ => countQueries_evenPazMarkQuery _ _ _ _ _ _)]
      obtain ⟨hlogL, hlogR⟩ := clog_half_le_pred hm2
      have hr_pos : 1 ≤ Nat.clog 2 m := Nat.clog_pos (by omega) (by omega)
      calc _ ≤ m * 2 + (2 * (m / 2) * Nat.clog 2 (m / 2) +
            2 * (m - m / 2) * Nat.clog 2 (m - m / 2)) :=
            Nat.add_le_add_left (Nat.add_le_add (ih (m / 2) (by omega) _ _ _)
              (ih (m - m / 2) (by omega) _ _ _)) _
        _ ≤ m * 2 + (2 * (m / 2) * (Nat.clog 2 m - 1) +
            2 * (m - m / 2) * (Nat.clog 2 m - 1)) := by gcongr
        _ = 2 * m * Nat.clog 2 m := by
            zify [Nat.div_le_self m 2, hr_pos]
            ring

/-- **Even–Paz `O(n log n)` Robertson–Webb query bound:** `evenPazQ n` makes at most
`2 * n * Nat.clog 2 n` queries against every oracle. -/
theorem countQueries_evenPazQ_le (n : ℕ)
    (oracle : {ι : Type} → RWQuery (Fin n) ι → ι) :
    (evenPazQ n).countQueries oracle ≤ 2 * n * Nat.clog 2 n := by
  rw [evenPazQ, FreeM.countQueries_map]
  exact countQueries_evenPazAux_le n oracle n 0 1 id

/-- `Cslib.Query.UpperBound` formulation (`2 * n * ⌈log₂ n⌉`, i.e. `O(n log n)`) for Even–Paz
across all `n : ℕ`. -/
theorem upperBound_evenPazNatQ :
    UpperBound evenPazNatQ id (fun n => 2 * n * Nat.clog 2 n) :=
  UpperBound.of_pointwise
    (fun m₁ m₂ h => Nat.mul_le_mul (Nat.mul_le_mul_left 2 h) (Nat.clog_mono_right 2 h))
    fun oracle n => by
      simp only [evenPazNatQ, FreeM.countQueries_map, RWQuery.countQueries_liftFin, id_eq]
      exact countQueries_evenPazQ_le n _

private theorem evenPazAux_partition (n : ℕ)
    (oracle : {ι : Type} → RWQuery (Fin n) ι → ι) :
    ∀ (m : ℕ) (_hm : 1 ≤ m) {a b : ℝ} (_hab : a ≤ b) (agents : Fin m → Fin n),
      let S := (evenPazAux n m a b agents).eval oracle
      OrderedCutsOn a b S.cuts ∧
        S.cuts.length = m - 1 ∧
        (List.ofFn S.pieceOf).Perm (intervalsOfCutsOn a b S.cuts) := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro hm a b hab agents
    unfold evenPazAux
    have hm0 : m ≠ 0 := by omega
    rw [dite_eq_right hm0]
    split_ifs with hm1
    · subst hm1
      simp only [FreeM.eval_pure, orderedCutsOn_nil, List.length_nil, Nat.sub_self,
        intervalsOfCutsOn]
      exact ⟨hab, trivial, List.Perm.refl _⟩
    · have hm2 : 2 ≤ m := by omega
      simp only [FreeM.eval_bind, FreeM.eval_pure, Cslib.FreeM.eval_mOfFn]
      set k := m / 2
      have hk1 : 1 ≤ k := by omega
      have hmk1 : 1 ≤ m - k := by omega
      have hk_lt : k < m := by omega
      have hmk_lt : m - k < m := by omega
      have hk_le : k ≤ m := Nat.div_le_self m 2
      set marks := List.Vector.ofFn fun r : Fin m =>
        (evenPazMarkQuery a b k m (agents r)).eval oracle
      set σ : Equiv.Perm (Fin m) := Tuple.sort marks.get
      set pivotIdx : Fin m := ⟨k - 1, by omega⟩
      set c : ℝ := marks.get (σ pivotIdx)
      have hc_mem : c ∈ Set.Icc a b := by
        simp only [c, marks, List.Vector.get_ofFn, evenPazMarkQuery, FreeM.eval_bind]
        exact RWQuery.eval_cutIn_mem_Icc oracle _ hab _
      set e := splitFinEquiv k hk_le
      set subL := (evenPazAux n k a c (fun r => agents (σ (e (.inl r))))).eval oracle
      set subR := (evenPazAux n (m - k) c b (fun r => agents (σ (e (.inr r))))).eval oracle
      obtain ⟨hordL, hlenL, hpermL⟩ := ih k hk_lt hk1 hc_mem.1 (fun r => agents (σ (e (.inl r))))
      obtain ⟨hordR, hlenR, hpermR⟩ := ih (m - k) hmk_lt hmk1 hc_mem.2
        (fun r => agents (σ (e (.inr r))))
      refine ⟨(orderedCutsOn_append_cons _ _).mpr ⟨hordL, hordR⟩, ?_, ?_⟩
      · rw [List.length_append, List.length_cons, hlenL, hlenR]
        omega
      · set pieceOf : Fin m → CakePiece :=
          fun r => Sum.elim subL.pieceOf subR.pieceOf (e.symm (σ.symm r))
        have hcomp : pieceOf ∘ σ = Sum.elim subL.pieceOf subR.pieceOf ∘ e.symm := by
          funext j
          simp only [Function.comp_apply, pieceOf, Equiv.symm_apply_apply]
        have hperm1 : (List.ofFn pieceOf).Perm (List.ofFn (pieceOf ∘ σ)) :=
          (ofFn_comp_equiv_perm pieceOf σ).symm
        rw [hcomp, ofFn_sumElim_splitFinEquiv hk_le] at hperm1
        rw [intervalsOfCutsOn_append_cons]
        exact hperm1.trans (hpermL.append hpermR)

/-- For `1 ≤ n`, `evenPazQ n` produces a valid `(n - 1)`-cut contiguous partition of `[0, 1]`
against any oracle. -/
theorem isValidPartition_evenPazQ {n : ℕ} (hn : 1 ≤ n)
    (oracle : {ι : Type} → RWQuery (Fin n) ι → ι) :
    ((evenPazQ n).eval oracle).IsValidPartition ∧
      ((evenPazQ n).eval oracle).numCuts = n - 1 ∧
      ((evenPazQ n).eval oracle).IsContiguous := by
  rw [evenPazQ, FreeM.eval_map]
  exact SubDivision.toDividedCake_valid
    (evenPazAux_partition n oracle n hn (by norm_num : (0 : ℝ) ≤ 1) id)

private theorem evenPazAux_proportional {n : ℕ} {v : Fin n → CakeValuation}
    {oracle : {ι : Type} → RWQuery (Fin n) ι → ι} (ho : RWQuery.IsValidOracle v oracle) :
    ∀ (m : ℕ) {a b : ℝ} (_ha : 0 ≤ a) (_hab : a ≤ b) (_hb : b ≤ 1) (agents : Fin m → Fin n),
      ∀ r : Fin m,
        v (agents r) a b / (m : ℝ) ≤
          (v (agents r)).pieceVal (((evenPazAux n m a b agents).eval oracle).pieceOf r) := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro a b ha hab hb agents r
    unfold evenPazAux
    by_cases hm0 : m = 0
    · subst hm0; exact Fin.elim0 r
    rw [dite_eq_right hm0]
    split_ifs with hm1
    · subst hm1
      simp only [FreeM.eval_pure, CakeValuation.pieceVal, Nat.cast_one, div_one, le_refl]
    · have hm2 : 2 ≤ m := by omega
      simp only [FreeM.eval_bind, FreeM.eval_pure, Cslib.FreeM.eval_mOfFn]
      set k := m / 2
      have hk1 : 1 ≤ k := by omega
      have hmk1 : 1 ≤ m - k := by omega
      have hk_lt : k < m := by omega
      have hmk_lt : m - k < m := by omega
      have hk_le : k ≤ m := Nat.div_le_self m 2
      set markFn : Fin m → ℝ := fun j => (evenPazMarkQuery a b k m (agents j)).eval oracle
      have hmark_spec : ∀ j : Fin m,
          markFn j ∈ Set.Icc a b ∧
            v (agents j) a (markFn j) = ((k : ℝ) / (m : ℝ)) * v (agents j) a b := by
        intro j
        simp only [markFn, evenPazMarkQuery, FreeM.eval_bind, ho.eval_evalAsk]
        have hv_nn : 0 ≤ v (agents j) a b := (v (agents j)).val_nonneg ha hb
        have hkm_nn : 0 ≤ ((k : ℝ) / (m : ℝ)) * v (agents j) a b := by positivity
        have hkm_le : ((k : ℝ) / (m : ℝ)) * v (agents j) a b ≤ v (agents j) a b := by
          have hfrac : (k : ℝ) / (m : ℝ) ≤ 1 := by
            rw [div_le_one (by positivity : (0 : ℝ) < m)]
            exact_mod_cast hk_le
          nlinarith
        exact ho.eval_cutIn_spec (agents j) ha hab hb hkm_nn hkm_le
      set marks := List.Vector.ofFn markFn
      have hmarks_get : marks.get = markFn := funext fun j => List.Vector.get_ofFn markFn j
      set σ : Equiv.Perm (Fin m) := Tuple.sort marks.get
      set pivotIdx : Fin m := ⟨k - 1, by omega⟩
      set c : ℝ := marks.get (σ pivotIdx)
      have hc_bounds : a ≤ c ∧ c ≤ b := by
        rw [show c = markFn (σ pivotIdx) by rw [← hmarks_get]]
        exact (hmark_spec (σ pivotIdx)).1
      set e := splitFinEquiv k hk_le
      set s := e.symm (σ.symm r)
      have hr : agents r = agents (σ (e s)) := by simp only [s, Equiv.apply_symm_apply]
      rw [hr]
      have hdiv_of_mul {x v₀ w₀ : ℝ} (hx : 0 < x) (h : (x / (m : ℝ)) * v₀ ≤ w₀) :
          v₀ / (m : ℝ) ≤ w₀ / x := by
        have h1 := div_le_div_of_nonneg_right h hx.le
        rwa [show (x / (m : ℝ)) * v₀ / x = v₀ / (m : ℝ) by field_simp [hx.ne']] at h1
      rcases s with rL | rR
      · simp only [Sum.elim_inl]
        have h_idx_le : e (.inl rL) ≤ pivotIdx := by
          change (e (.inl rL)).1 ≤ k - 1
          simp only [e, splitFinEquiv, Equiv.coe_fn_mk]
          omega
        have hmark_le : markFn (σ (e (.inl rL))) ≤ c := by
          rw [← hmarks_get]
          exact Tuple.monotone_sort marks.get h_idx_le
        have hval_ac : ((k : ℝ) / (m : ℝ)) * v (agents (σ (e (.inl rL)))) a b ≤
            v (agents (σ (e (.inl rL)))) a c := by
          rw [← (hmark_spec (σ (e (.inl rL)))).2]
          exact (v (agents (σ (e (.inl rL))))).apply_mono_right ha hmark_le (hc_bounds.2.trans hb)
        exact (hdiv_of_mul (by exact_mod_cast hk1) hval_ac).trans
          (ih k hk_lt ha hc_bounds.1 (hc_bounds.2.trans hb)
            (fun t => agents (σ (e (.inl t)))) rL)
      · simp only [Sum.elim_inr]
        have h_idx_ge : pivotIdx ≤ e (.inr rR) := by
          change k - 1 ≤ (e (.inr rR)).1
          simp only [e, splitFinEquiv, Equiv.coe_fn_mk]
          omega
        have hmark_ge : c ≤ markFn (σ (e (.inr rR))) := by
          rw [← hmarks_get]
          exact Tuple.monotone_sort marks.get h_idx_ge
        have hval_ac_le : v (agents (σ (e (.inr rR)))) a c ≤
            ((k : ℝ) / (m : ℝ)) * v (agents (σ (e (.inr rR)))) a b := by
          rw [← (hmark_spec (σ (e (.inr rR)))).2]
          exact (v (agents (σ (e (.inr rR))))).apply_mono_right ha hmark_ge
            ((hmark_spec (σ (e (.inr rR)))).1.2.trans hb)
        have hadd := (v (agents (σ (e (.inr rR))))).val_add ha hc_bounds.1 hc_bounds.2 hb
        have hm_pos : (0 : ℝ) < m := by positivity
        have hval_cb : (((m - k : ℕ) : ℝ) / (m : ℝ)) * v (agents (σ (e (.inr rR)))) a b ≤
            v (agents (σ (e (.inr rR)))) c b := by
          have hident : 1 - (k : ℝ) / (m : ℝ) = (((m - k : ℕ) : ℝ) / (m : ℝ)) := by
            rw [Nat.cast_sub hk_le]
            field_simp [hm_pos.ne']
          linarith [congrArg (· * v (agents (σ (e (.inr rR)))) a b) hident]
        exact (hdiv_of_mul (by exact_mod_cast hmk1) hval_cb).trans
          (ih (m - k) hmk_lt (ha.trans hc_bounds.1) hc_bounds.2 hb
            (fun t => agents (σ (e (.inr t)))) rR)

/-- **Even–Paz proportionality:** for every `n`-agent valuation profile `v` and valid
Robertson–Webb oracle `oracle`, `evenPazQ n` gives every agent value at least `1 / n`. -/
theorem isProportional_evenPazQ {n : ℕ} {v : Fin n → CakeValuation}
    {oracle : {ι : Type} → RWQuery (Fin n) ι → ι} (ho : RWQuery.IsValidOracle v oracle) :
    ((evenPazQ n).eval oracle).IsProportional v := by
  intro i
  rw [evenPazQ, FreeM.eval_map]
  dsimp only [SubDivision.toDividedCake]
  rw [CakeValuation.bundleVal_singleton, ← CakeValuation.pieceVal]
  have h := evenPazAux_proportional ho n le_rfl (by norm_num) le_rfl id i
  dsimp only [id] at h
  rwa [(v i).apply_zero_one] at h

end Cslib.GameTheory.FairDivision
