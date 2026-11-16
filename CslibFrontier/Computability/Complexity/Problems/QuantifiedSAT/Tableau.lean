/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

import CslibFrontier.Computability.Complexity.Classes.Alternation.Game

public import CslibFrontier.Computability.Complexity.Problems.QuantifiedSAT
public import CslibFrontier.Computability.Complexity.Classes.Space.TQBF.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Logics.Propositional.CNF.PolyTime

/-!
# Grouping the Cook–Levin certificate variables

The existing TQBF tableau formula has an existential block of auxiliary variables.
Grouping its certificate variables and appending the auxiliary variables to the final block
preserves the number of alternations. A universally quantified final block uses the negated
matrix for a rejecting computation.
-/

public section

namespace Cslib.Complexity.QuantifiedSAT

open Cslib.Logic.PL Turing.MultiTapeTM ComputableInPolyTime TQBF

/-- `i` consecutive blocks of `n` certificate variables, starting at certificate position `o`.
`w` is the width parameter of the existing TQBF tableau interface (`2 * w` certificate bits). -/
@[expose] def certBlocks (w n : ℕ) : ℕ → ℕ → List (List ℕ)
  | 0, _ => []
  | i + 1, o => ((List.range n).map fun j => certVar w (o + j)) :: certBlocks w n i (o + n)

private theorem flatten_certBlocks (w n i o : ℕ) :
    (certBlocks w n i o).flatten = (List.range (i * n)).map (fun j => certVar w (o + j)) := by
  induction i generalizing o with
  | zero => simp [certBlocks]
  | succ i ih =>
    rw [certBlocks, List.flatten_cons, ih, Nat.succ_mul, Nat.add_comm (i * n) n,
      List.range_add, List.map_append, List.map_map]
    congr 1
    exact List.map_congr_left fun j _ => by simp [Nat.add_assoc]

private theorem lengths_certBlocks (w n i o : ℕ) :
    (certBlocks w n i o).map List.length = List.replicate i n := by
  induction i generalizing o with
  | zero => rfl
  | succ i ih => simp only [certBlocks, List.map_cons, List.length_map, List.length_range,
      ih, List.replicate_succ]

/-- Consecutive certificate blocks enumerate exactly the source and target variables of the
existing tableau formula when their total length is `2 * w`. -/
theorem flatten_certBlocks_eq (w n i : ℕ) (h : i * n = 2 * w) :
    (certBlocks w n i 0).flatten = blockVars w 0 0 ++ blockVars w 1 0 := by
  rw [flatten_certBlocks, h]
  simp only [Nat.zero_add]
  rw [show 2 * w = w + w by omega, List.range_add, List.map_append, List.map_map]
  congr 1
  · exact List.map_congr_left fun j hj => by simp [certVar, List.mem_range.mp hj]
  · exact List.map_congr_left fun j hj => by simp [certVar]

/-- Quantifying the certificate blocks ranges over all certificate words, for any matrix
whose value depends on the source and target variables through the indicated predicate. -/
theorem eval_certBlocks {φ : QBF ℕ} {P : List Bool → Prop}
    (w n i : ℕ) (h : i * n = 2 * w) (q : Bool) (σ : ℕ → Bool)
    (hφ : ∀ σ, φ.eval σ = true ↔ P (block σ w 0 0 ++ block σ w 1 0)) :
    (QBF.blocks q (certBlocks w n i 0) φ).eval σ = true ↔
      Alternation q (List.replicate i n) P := by
  rw [QBF.eval_blocks_eq_true_iff, lengths_certBlocks]
  refine alternation_congr_of_length fun z hz => ?_
  rw [List.sum_replicate, smul_eq_mul, h] at hz
  rw [hφ]
  have hread :
      block (QBF.updates σ (certBlocks w n i 0).flatten z) w 0 0 ++
        block (QBF.updates σ (certBlocks w n i 0).flatten z) w 1 0 = z := by
    rw [block, block, ← List.map_append, ← flatten_certBlocks_eq w n i h]
    exact QBF.map_updates (flatten_certBlocks_eq w n i h ▸ nodup_blockVars_append w 0)
      (by simpa only [flatten_certBlocks_eq w n i h, List.length_append, blockVars,
        List.length_map, List.length_range, ← two_mul] using hz)
  rw [hread]

/-- Grouped certificate variables can be written in polynomial time from unary widths. -/
theorem certBlocks_polyTime {α : Type} {enc : α ↪ List Bool} {w n o : α → ℕ}
    (i : ℕ) (hw : ComputableInPolyTime w enc encUnary)
    (hn : ComputableInPolyTime n enc encUnary) (ho : ComputableInPolyTime o enc encUnary) :
    ComputableInPolyTime (fun a => certBlocks (w a) (n a) i (o a))
      enc (encList (encList encNat)) := by
  induction i generalizing o with
  | zero => exact const []
  | succ i ih =>
    have htail := ih (unary_add.comp (ho.prod hn))
    simp only [certBlocks]
    fun_prop

private theorem matrix_quantifierFree {k : ℕ} {State : Type} [Fintype State]
    (tab : CNF (CookLevin.Var k State)) (w : ℕ) : (baseMatrix tab w).QuantifierFree := by
  rw [baseMatrix, QBF.quantifierFree_and]
  refine ⟨?_, QBF.quantifierFree_ofCNF _⟩
  unfold certLinks
  have hc (fs : List (QBF ℕ)) (h : ∀ φ ∈ fs, φ.QuantifierFree) :
      (QBF.conj fs).QuantifierFree := by
    induction fs with
    | nil => exact QBF.quantifierFree_top
    | cons φ fs ih =>
      rw [QBF.conj, List.foldr_cons, QBF.quantifierFree_and]
      exact ⟨h _ List.mem_cons_self, ih (fun ψ hψ => h ψ (.tail _ hψ))⟩
  apply hc
  simp only [List.forall_mem_map]
  intro j _
  simp [QBF.iff]

/-- Merge the auxiliary tableau variables into the final certificate block. `r` is the
polarity of that final block; a universal block uses the negated tableau matrix. -/
noncomputable def instanceOfTableau {k : ℕ} {State : Type} [Fintype State]
    (tab : CNF (CookLevin.Var k State)) (w n i : ℕ) (r : Bool) : PrenexQBF :=
  ⟨QBF.appendLast (certBlocks w n i 0) (baseVars tab w),
    if r then baseMatrix tab w else (baseMatrix tab w).not⟩

/-- Merging the tableau variables preserves well-formedness and the number of blocks. -/
theorem instanceOfTableau_wellFormed {k : ℕ} {State : Type} [Fintype State]
    (tab : CNF (CookLevin.Var k State)) (w n i : ℕ) (hi : 1 ≤ i)
    (h : i * n = 2 * w) (r : Bool) : (instanceOfTableau tab w n i r).WellFormed i := by
  have hlen : (certBlocks w n i 0).length = i := by
    have := congrArg List.length (lengths_certBlocks w n i 0)
    simpa only [List.length_map, List.length_replicate] using this
  have hne : certBlocks w n i 0 ≠ [] := by
    intro heq
    simp only [heq, List.length_nil] at hlen
    omega
  refine ⟨(QBF.length_appendLast hne _).trans hlen, ?_, ?_⟩
  · cases r
    · exact QBF.quantifierFree_not.mpr (matrix_quantifierFree tab w)
    · exact matrix_quantifierFree tab w
  · intro x hx
    have hx' : x ∈ (baseMatrix tab w).freeVars := by cases r <;> exact hx
    change x ∈ (QBF.appendLast (certBlocks w n i 0) (baseVars tab w)).flatten.toFinset
    rw [List.mem_toFinset, QBF.flatten_appendLast, List.mem_append]
    by_cases hb : x ∈ baseVars tab w
    · exact .inr hb
    · have hbase : x ∈ (baseFormula tab w).freeVars := by
        rw [baseFormula, QBF.freeVars_exs, Finset.mem_sdiff, List.mem_toFinset]
        exact ⟨hx', hb⟩
      rw [flatten_certBlocks_eq w n i h, List.mem_append]
      exact .inl (mem_freeVars_baseFormula tab w x hbase)

private theorem eval_blocks_congr {φ ψ : QBF ℕ} (h : ∀ σ, φ.eval σ = ψ.eval σ)
    (q : Bool) (bs : List (List ℕ)) (σ : ℕ → Bool) :
    (QBF.blocks q bs φ).eval σ = (QBF.blocks q bs ψ).eval σ := by
  rw [Bool.eq_iff_iff, QBF.eval_blocks_eq_true_iff, QBF.eval_blocks_eq_true_iff]
  exact alternation_congr fun w => by rw [h]

/-- Positive-length certificate blocks remain nonempty after the tableau variables merge. -/
theorem instanceOfTableau_nonempty {k : ℕ} {State : Type} [Fintype State]
    (tab : CNF (CookLevin.Var k State)) (w n i : ℕ) (hi : 1 ≤ i) (hn : 1 ≤ n) (r : Bool) :
    ∀ b ∈ (instanceOfTableau tab w n i r).blocks, b ≠ [] := by
  have hbase : ∀ b ∈ certBlocks w n i 0, b ≠ [] := by
    intro b hb heq
    have hmem := List.mem_map_of_mem (f := List.length) hb
    rw [lengths_certBlocks] at hmem
    have := List.eq_of_mem_replicate hmem
    simp only [heq, List.length_nil] at this
    omega
  have hne : certBlocks w n i 0 ≠ [] := by
    intro h
    have := lengths_certBlocks w n i 0
    simp [h] at this
    omega
  suffices ∀ (bs : List (List ℕ)), bs ≠ [] → (∀ b ∈ bs, b ≠ []) →
      ∀ b ∈ QBF.appendLast bs (baseVars tab w), b ≠ [] from this _ hne hbase
  intro bs
  induction bs with
  | nil => simp
  | cons b bs ih =>
    intro _ hall
    cases bs with
    | nil =>
      have hb : b ++ baseVars tab w ≠ [] := fun heq =>
        hall b (by simp) (List.append_eq_nil_iff.mp heq).1
      simpa only [QBF.appendLast, List.mem_singleton, forall_eq] using hb
    | cons c bs =>
      simp only [QBF.appendLast, List.mem_cons, forall_eq_or_imp]
      exact ⟨hall b (by simp), ih (by simp) (fun d hd => hall d (.tail _ hd))⟩

/-- The merged formula has the value of the original certificate prefix followed by the
existential tableau, or its negation when the final block is universal. -/
theorem eval_instanceOfTableau {k : ℕ} {State : Type} [Fintype State]
    (tab : CNF (CookLevin.Var k State)) (w n i : ℕ) (hi : 1 ≤ i) (q r : Bool)
    (hr : Bool.not^[i] q = !r) (σ : ℕ → Bool) :
    ((instanceOfTableau tab w n i r).formula q).eval σ =
      (QBF.blocks q (certBlocks w n i 0)
        (if r then baseFormula tab w else (baseFormula tab w).not)).eval σ := by
  have hlen : (certBlocks w n i 0).length = i := by
    have := congrArg List.length (lengths_certBlocks w n i 0)
    simpa only [List.length_map, List.length_replicate] using this
  have hne : certBlocks w n i 0 ≠ [] := by
    intro heq
    simp only [heq, List.length_nil] at hlen
    omega
  rw [PrenexQBF.formula, instanceOfTableau,
    QBF.blocks_appendLast q r hne (hlen.symm ▸ hr)]
  apply eval_blocks_congr
  intro τ
  cases r
  · have hd := QBF.eval_blocks_dual true [baseVars tab w] (baseMatrix tab w) τ
    exact hd
  · rfl

/-- The merged tableau instance is polynomial-time in the tableau and its unary parameters,
for a fixed number of certificate blocks. -/
theorem instanceOfTableau_polyTime {α : Type} {enc : α ↪ List Bool} {k : ℕ} {State : Type}
    [Fintype State] {tab : α → CNF (CookLevin.Var k State)} {w n : α → ℕ}
    (i : ℕ) (r : Bool)
    (htab : ComputableInPolyTime tab enc
      (encList (encList (encPair CookLevin.encVar encBool))))
    (hw : ComputableInPolyTime w enc encUnary) (hn : ComputableInPolyTime n enc encUnary) :
    ComputableInPolyTime (fun a => instanceOfTableau (tab a) (w a) (n a) i r)
      enc encPrenexQBF := by
  have hbs := certBlocks_polyTime i hw hn (const 0)
  have ht := computableInPolyTime_tabVar (k := k) (State := State)
  have hc := CookLevin.computableInPolyTime_cert (k := k) (State := State)
  have hv := CNF.computableInPolyTime_vars (CookLevin.encVar (k := k) (State := State))
  have hrel := CNF.computableInPolyTime_relabel ht
  have haux : ComputableInPolyTime (fun a => baseVars (tab a) (w a)) enc (encList encNat) := by
    unfold baseVars
    fun_prop
  have hm := computableInPolyTime_baseMatrix htab hw
  unfold instanceOfTableau
  simp only [QBF.appendLast_eq_reverse]
  cases r <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> fun_prop

end Cslib.Complexity.QuantifiedSAT
