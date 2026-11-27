/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.Approximation.Hastad
public import CslibFrontier.Computability.PCP.Approximation.ThreeXOR
public import CslibFrontier.Logics.Propositional.CSP.UnsatVal
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListMap
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeNatFrontends
import CslibFrontier.Foundations.Data.Finset.Expect
import CslibFrontier.Foundations.Data.List.Filter
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Håstad's folded Long Code reduction from Label Cover to MAX-E3LIN-2

This module constructs the explicit polynomial-time reduction turning a Label Cover instance
`g : Graph (β → γ)` into an unweighted system of three-variable parity equations over distinct
variables (`CSP Bool ℕ` under `Cslib.Logic.PL.CSP.paritySem`), realizing Håstad's noisy 3-bit
linear test at rational noise rate `δ = 1 / m` (`2 ≤ m`) [Håstad, Section 5, proof of Theorem 5.4,
author PDF pp. 27–28 / JACM pp. 821–822][Hastad2001].

1. **Folding (`foldArg`, `decodeRight`)**: fixing a coordinate `y₀ : γ`, each right query `f` is
   folded to its canonical representative `foldArg y₀ f` with bit `false` at `y₀`, while the bit
   `f y₀` is absorbed into the equation's right-hand side. Every Boolean assignment `σ : ℕ → Bool`
   therefore decodes to folded (odd) right tables `decodeRight T σ` (`isOdd_decodeRight`) and
   left tables `decodeLeft T σ`, and every pair of folded right tables and arbitrary left tables
   arises from some assignment.
2. **Unweighted rational noise (`noiseMask`)**: sampling `r : β → Fin m` uniformly and setting
   `noiseMask r x := decide ((r x : ℕ) = 0)` realizes `bernoulliAverage (1 / m)` as a uniform
   finite average, eliminating equation weights concretely by unweighted enumeration.
3. **Distinct variables (`scopes_reduce`)**: right variables are even (`rightVar`) and left
   variables are odd (`leftVar`), so a collision occurs only when the two left queries coincide,
   i.e., `f ∘ π = noiseMask r`. Dropping these degenerate triples leaves strictly three distinct
   variables in every equation (`c.scope.length = 3 ∧ c.scope.Nodup`), discarding at most a
   fraction `w = (1 - 1 / m) ^ |β|` of the equations per edge. For nonempty `β` and `2 ≤ m`,
   `w < 1`, so the reduction is always nonempty (`length_reduce_pos`).
4. **Value transfer**: on graphs with at least one edge, completeness loses at most `w`
   (`exists_countSat_reduce_ge`) and soundness inflates by at most `1 / (1 - w)`
   (`countSat_reduce_div_length_le`) relative to `graphLinearProb g (1 / m)`. Edgeless graphs map
   to a single trivially satisfiable distinct-variable equation `trivialEq`.
5. **Polynomial-time computability (`isPolyTime_reduce`)**: for fixed finite label sets `β, γ`
   and fixed noise denominator `m`, the projection-to-template table depends only on the finite
   projection `π : β → γ` (certified by `ComputableInPolyTime.of_finite`), and combining each
   template with the unary edge endpoints and converting to binary `encNat` runs in native
   multi-tape polynomial time.

## Main definitions

* `Cslib.PCP.Hastad.Reduction.Tables`, `Cslib.PCP.Hastad.Reduction.Tables.Valid`: explicit
  folding pivot, variable indexers, and complete duplicate-free query/noise enumerations.
* `Cslib.PCP.Hastad.Reduction.foldArg`, `Cslib.PCP.Hastad.Reduction.noiseMask`: folding
  representative and `1 / m`-rate noise mask.
* `Cslib.PCP.Hastad.Reduction.rightVar`, `Cslib.PCP.Hastad.Reduction.leftVar`: disjoint variable
  numbering for right and left Long Code tables.
* `Cslib.PCP.Hastad.Reduction.edgeEquations`, `Cslib.PCP.Hastad.Reduction.reduce`: the reduction
  from Label Cover to distinct three-variable parity equations.
* `Cslib.PCP.Hastad.Reduction.decodeRight`, `Cslib.PCP.Hastad.Reduction.decodeLeft`: decoding an
  assignment into folded right tables and left tables.

## Main results

* `Cslib.PCP.Hastad.Reduction.scopes_reduce`: every emitted equation has three distinct variables.
* `Cslib.PCP.Hastad.Reduction.length_reduce_pos`: the output system is nonempty.
* `Cslib.PCP.Hastad.Reduction.exists_countSat_reduce_ge`: completeness transfer with loss at most
  `(1 - 1 / m) ^ |β|`.
* `Cslib.PCP.Hastad.Reduction.countSat_reduce_div_length_le`: soundness transfer with factor at
  most `1 / (1 - (1 - 1 / m) ^ |β|)`.
* `Cslib.PCP.Hastad.Reduction.isPolyTime_reduce`: native polynomial-time certificate under
  `Graph.encoding (encPi encG)` and `encCSP encBool encNat`.

## References

* [J. Håstad, *Some optimal inapproximability results*][Hastad2001], Section 5, proof of
  Theorem 5.4 (author PDF pp. 27–28 / JACM pp. 821–822).
-/

public section

namespace Cslib.PCP.Hastad.Reduction

open Finset Cslib.BitString Cslib.Logic.PL Cslib.PCP.Encoded Cslib.Complexity Turing.MultiTapeTM
open scoped BigOperators

/-- Explicit finite tables parameterizing Håstad's folded Long Code reduction at noise rate
`1 / m`: a folding coordinate in `γ`, injective variable indexers on right and left Long Code
queries, and duplicate-free enumerations of right queries, left queries, and noise digits. -/
structure Tables (β γ : Type) (m : ℕ) where
  /-- Designated right-label coordinate around which right tables are folded. -/
  pivot : γ
  /-- Variable index assigned to each right-table query `f : γ → Bool`. -/
  rightIdx : (γ → Bool) → ℕ
  /-- Variable index assigned to each left-table query `g : β → Bool`. -/
  leftIdx : (β → Bool) → ℕ
  /-- Complete duplicate-free enumeration of right-table queries `γ → Bool`. -/
  rightQueries : List (γ → Bool)
  /-- Complete duplicate-free enumeration of left-table queries `β → Bool`. -/
  leftQueries : List (β → Bool)
  /-- Complete duplicate-free enumeration of noise digits `β → Fin m`. -/
  noiseDigits : List (β → Fin m)

/-- Validity of `Tables`: both variable indexers are injective, and all three enumerations are
duplicate-free and complete. -/
structure Tables.Valid {β γ : Type} {m : ℕ} (T : Tables β γ m) : Prop where
  /-- Distinct right queries receive distinct indices. -/
  rightIdx_injective : Function.Injective T.rightIdx
  /-- Distinct left queries receive distinct indices. -/
  leftIdx_injective : Function.Injective T.leftIdx
  /-- Right queries are listed without duplicates. -/
  rightQueries_nodup : T.rightQueries.Nodup
  /-- Every right query appears in `rightQueries`. -/
  mem_rightQueries : ∀ f, f ∈ T.rightQueries
  /-- Left queries are listed without duplicates. -/
  leftQueries_nodup : T.leftQueries.Nodup
  /-- Every left query appears in `leftQueries`. -/
  mem_leftQueries : ∀ g, g ∈ T.leftQueries
  /-- Noise digit vectors are listed without duplicates. -/
  noiseDigits_nodup : T.noiseDigits.Nodup
  /-- Every noise digit vector appears in `noiseDigits`. -/
  mem_noiseDigits : ∀ r, r ∈ T.noiseDigits

/-- Canonical `Tables` built from `Fintype` instances and a chosen folding pivot `y₀ : γ`. -/
noncomputable def Tables.ofFintype {β γ : Type} [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ] (m : ℕ) (y₀ : γ) : Tables β γ m where
  pivot := y₀
  rightIdx f := (Fintype.equivFin (γ → Bool) f).val
  leftIdx g := (Fintype.equivFin (β → Bool) g).val
  rightQueries := (Finset.univ : Finset (γ → Bool)).toList
  leftQueries := (Finset.univ : Finset (β → Bool)).toList
  noiseDigits := (Finset.univ : Finset (β → Fin m)).toList

/-- `Tables.ofFintype` satisfies `Tables.Valid`. -/
theorem Tables.valid_ofFintype {β γ : Type} [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ] (m : ℕ) (y₀ : γ) :
    (Tables.ofFintype (β := β) m y₀).Valid where
  rightIdx_injective := Fin.val_injective.comp (Fintype.equivFin (γ → Bool)).injective
  leftIdx_injective := Fin.val_injective.comp (Fintype.equivFin (β → Bool)).injective
  rightQueries_nodup := Finset.nodup_toList _
  mem_rightQueries _ := Finset.mem_toList.2 (Finset.mem_univ _)
  leftQueries_nodup := Finset.nodup_toList _
  mem_leftQueries _ := Finset.mem_toList.2 (Finset.mem_univ _)
  noiseDigits_nodup := Finset.nodup_toList _
  mem_noiseDigits _ := Finset.mem_toList.2 (Finset.mem_univ _)

/-! ### Folding, noise masks, and variable numbering -/

/-- Canonical representative of `{f, f + 1}` whose value at `y₀` is `false`. -/
@[expose] def foldArg {γ : Type} (y₀ : γ) (f : γ → Bool) : γ → Bool :=
  if f y₀ then f + fun _ => true else f

/-- Boolean noise mask selecting coordinates whose `Fin m` digit is zero (rate `1 / m`). -/
@[expose] def noiseMask {β : Type} {m : ℕ} (r : β → Fin m) : β → Bool :=
  fun x => decide ((r x : ℕ) = 0)

/-- Variable number for the right Long Code entry at right vertex `w` and query index `i` (even). -/
@[expose] def rightVar (w i : ℕ) : ℕ :=
  2 * Nat.pair w i

/-- Variable number for the left Long Code entry at left vertex `u` and query index `i` (odd). -/
@[expose] def leftVar (u i : ℕ) : ℕ :=
  2 * Nat.pair u i + 1

private theorem rightVar_ne_leftVar (w i u j : ℕ) : rightVar w i ≠ leftVar u j := by
  simp only [rightVar, leftVar]
  omega

private theorem leftVar_inj {u₁ i₁ u₂ i₂ : ℕ} (h : leftVar u₁ i₁ = leftVar u₂ i₂) :
    u₁ = u₂ ∧ i₁ = i₂ := by
  simp only [leftVar] at h
  exact Nat.pair_eq_pair.1 (by omega)

/-! ### The reduction from Label Cover to distinct three-variable parity equations -/

/-- Parity equations emitted for a single Label Cover edge `d`: for every `(f, r, g)` with
`f ∘ d.constraint ≠ noiseMask r`, emits the folded 3-bit test equation on three distinct
variables. -/
@[expose] def edgeEquations {β γ : Type} [Fintype β] {m : ℕ}
    (T : Tables β γ m) (d : Edge (β → γ)) : CSP Bool ℕ :=
  T.rightQueries.flatMap fun f =>
    (T.noiseDigits.filter fun r => decide (f ∘ d.constraint ≠ noiseMask r)).flatMap fun r =>
      T.leftQueries.map fun g =>
        ⟨f T.pivot,
          [rightVar d.dst (T.rightIdx (foldArg T.pivot f)),
            leftVar d.src (T.leftIdx g),
            leftVar d.src (T.leftIdx ((f ∘ d.constraint) + g + noiseMask r))]⟩

/-- Fixed satisfiable parity equation on three distinct variables, emitted for edgeless graphs. -/
@[expose] def trivialEq : Constraint Bool ℕ :=
  ⟨false, [0, 1, 2]⟩

/-- **Håstad's folded Long Code reduction** from Label Cover to three-variable parity equations
over distinct variables (`CSP Bool ℕ`). Edgeless graphs map to `[trivialEq]` so that the output
system is always nonempty. -/
@[expose] def reduce {β γ : Type} [Fintype β] {m : ℕ}
    (T : Tables β γ m) (g : Graph (β → γ)) : CSP Bool ℕ :=
  if g.edges.isEmpty then [trivialEq] else g.edges.flatMap (edgeEquations T)

/-- On an edgeless graph, `reduce` returns `[trivialEq]`. -/
theorem reduce_of_edges_nil {β γ : Type} [Fintype β] {m : ℕ}
    (T : Tables β γ m) {g : Graph (β → γ)} (hg : g.edges = []) :
    reduce T g = [trivialEq] := by
  simp [reduce, hg]

/-- On a graph with at least one edge, `reduce` flattens `edgeEquations` over `g.edges`. -/
theorem reduce_of_edges_ne_nil {β γ : Type} [Fintype β] {m : ℕ}
    (T : Tables β γ m) {g : Graph (β → γ)} (hg : g.edges ≠ []) :
    reduce T g = g.edges.flatMap (edgeEquations T) := by
  have he : g.edges.isEmpty = false := by
    cases h : g.edges with
    | nil => exact (hg h).elim
    | cons _ _ => rfl
  simp [reduce, he]

/-- Every equation emitted by `reduce` has three distinct variables. -/
theorem scopes_reduce {β γ : Type} [Fintype β] {m : ℕ}
    {T : Tables β γ m} (hT : T.Valid) (g : Graph (β → γ)) :
    ∀ c ∈ reduce T g, c.scope.length = 3 ∧ c.scope.Nodup := by
  intro c hc
  by_cases hg : g.edges = []
  · rw [reduce_of_edges_nil T hg] at hc
    rw [List.mem_singleton.1 hc]
    decide
  · rw [reduce_of_edges_ne_nil T hg] at hc
    obtain ⟨d, _, hc⟩ := List.mem_flatMap.1 hc
    obtain ⟨f, _, hc⟩ := List.mem_flatMap.1 hc
    obtain ⟨r, hr, hc⟩ := List.mem_flatMap.1 hc
    obtain ⟨g', _, rfl⟩ := List.mem_map.1 hc
    have hne : f ∘ d.constraint ≠ noiseMask r := of_decide_eq_true (List.mem_filter.1 hr).2
    refine ⟨rfl, ?_⟩
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, not_false_eq_true, and_true]
    refine ⟨⟨rightVar_ne_leftVar _ _ _ _, rightVar_ne_leftVar _ _ _ _⟩, fun heq => hne ?_⟩
    have hidx : g' = (f ∘ d.constraint) + g' + noiseMask r :=
      hT.leftIdx_injective (leftVar_inj heq).2
    funext x
    have hx := congrFun hidx x
    simp only [Pi.add_apply] at hx
    cases h1 : g' x <;> cases h2 : f (d.constraint x) <;> cases h3 : noiseMask r x <;>
      simp [h1, h2, h3, Bool.add_eq_xor] at hx ⊢

/-! ### Decoding and encoding Long Code tables -/

/-- Decode folded (odd) right Long Code tables from an assignment `σ : ℕ → Bool`. -/
@[expose] def decodeRight {β γ : Type} {m : ℕ} (T : Tables β γ m) (σ : ℕ → Bool) (w : ℕ) :
    (γ → Bool) → Bool :=
  BitString.foldTable T.pivot fun f => σ (rightVar w (T.rightIdx f))

/-- Decode left Long Code tables from an assignment `σ : ℕ → Bool`. -/
@[expose] def decodeLeft {β γ : Type} {m : ℕ} (T : Tables β γ m) (σ : ℕ → Bool) (u : ℕ) :
    (β → Bool) → Bool :=
  fun g => σ (leftVar u (T.leftIdx g))

/-- Every decoded right table is folded (odd). -/
theorem isOdd_decodeRight {β γ : Type} {m : ℕ} (T : Tables β γ m) (σ : ℕ → Bool) (w : ℕ) :
    IsOdd (decodeRight T σ w) :=
  isOdd_foldTable T.pivot _

/-- Evaluating an emitted constraint against `σ` is identical to Håstad's 3-bit linear test on
the decoded tables `(decodeRight T σ, decodeLeft T σ)`. -/
private theorem eval_emitted_eq {β γ : Type} {m : ℕ}
    (T : Tables β γ m) (σ : ℕ → Bool) (d : Edge (β → γ)) (f : γ → Bool)
    (r : β → Fin m) (g' : β → Bool) :
    Constraint.eval CSP.paritySem σ
      ⟨f T.pivot,
        [rightVar d.dst (T.rightIdx (foldArg T.pivot f)),
          leftVar d.src (T.leftIdx g'),
          leftVar d.src (T.leftIdx ((f ∘ d.constraint) + g' + noiseMask r))]⟩ =
      decide ((decodeRight T σ d.dst f ^^ decodeLeft T σ d.src g' ^^
        decodeLeft T σ d.src ((f ∘ d.constraint) + g' + noiseMask r)) = false) := by
  have hfold : decodeRight T σ d.dst f =
      (σ (rightVar d.dst (T.rightIdx (foldArg T.pivot f))) ^^ f T.pivot) := by
    simp only [decodeRight, foldTable, foldArg]
    cases f T.pivot <;> simp
  simp only [Constraint.eval, List.map_cons, List.map_nil, CSP.paritySem_three, hfold, decodeLeft]
  cases σ (rightVar d.dst (T.rightIdx (foldArg T.pivot f))) <;>
    cases f T.pivot <;>
    cases σ (leftVar d.src (T.leftIdx g')) <;>
    cases σ (leftVar d.src (T.leftIdx ((f ∘ d.constraint) + g' + noiseMask r))) <;>
    rfl

/-- Encode folded right tables `B` and left tables `A` into a single assignment `ℕ → Bool`. -/
private noncomputable def encodeTables {β γ : Type} {m : ℕ} (T : Tables β γ m)
    (B : ℕ → (γ → Bool) → Bool) (A : ℕ → (β → Bool) → Bool) (v : ℕ) : Bool :=
  if v % 2 = 0 then
    let p := Nat.unpair (v / 2)
    B p.1 (Function.invFun T.rightIdx p.2)
  else
    let p := Nat.unpair (v / 2)
    A p.1 (Function.invFun T.leftIdx p.2)

private theorem decodeRight_encodeTables {β γ : Type} {m : ℕ} {T : Tables β γ m}
    (hT : T.Valid) {B : ℕ → (γ → Bool) → Bool} (hB : ∀ w, IsOdd (B w))
    (A : ℕ → (β → Bool) → Bool) (w : ℕ) :
    decodeRight T (encodeTables T B A) w = B w := by
  have hraw : (fun f => encodeTables T B A (rightVar w (T.rightIdx f))) = B w := by
    funext f
    simp only [encodeTables, rightVar, Nat.mul_mod_right, ↓reduceIte,
      Nat.mul_div_right _ (by norm_num : 0 < 2), Nat.unpair_pair,
      Function.leftInverse_invFun hT.rightIdx_injective f]
  simpa only [decodeRight, hraw] using (hB w).foldTable_eq T.pivot

private theorem decodeLeft_encodeTables {β γ : Type} {m : ℕ} {T : Tables β γ m}
    (hT : T.Valid) (B : ℕ → (γ → Bool) → Bool) (A : ℕ → (β → Bool) → Bool) (u : ℕ) :
    decodeLeft T (encodeTables T B A) u = A u := by
  funext g
  have hmod : (2 * Nat.pair u (T.leftIdx g) + 1) % 2 ≠ 0 := by omega
  have hdiv : (2 * Nat.pair u (T.leftIdx g) + 1) / 2 = Nat.pair u (T.leftIdx g) := by omega
  simp only [decodeLeft, encodeTables, leftVar, hmod, ↓reduceIte, hdiv, Nat.unpair_pair,
    Function.leftInverse_invFun hT.leftIdx_injective g]

/-! ### Unweighted counting of rational-rate Bernoulli noise and degenerate drops -/

section Counting

variable {β γ : Type} [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]

/-- Fiber cardinality of `noiseMask` over `β → Fin m`: the number of digit vectors realizing mask
`P` is `m ^ |β| * bernoulliWeight (1 / m) P`. -/
private theorem sum_noiseMask_eq_bernoulliWeight {m : ℕ} (hm : 0 < m) (P : β → Bool) :
    ∑ r : β → Fin m, (if noiseMask r = P then (1 : ℝ) else 0) =
      (m : ℝ) ^ Fintype.card β * bernoulliWeight (1 / (m : ℝ)) P := by
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  have hdigit (b : Bool) :
      ∑ r : Fin m, (if decide ((r : ℕ) = 0) = b then (1 : ℝ) else 0) =
        (m : ℝ) * if b then 1 / (m : ℝ) else 1 - 1 / (m : ℝ) := by
    have hzero : ∑ r : Fin m, (if (r : ℕ) = 0 then (1 : ℝ) else 0) = 1 := by
      rw [Finset.sum_eq_single (⟨0, hm⟩ : Fin m)]
      · simp
      · intro r _ hr
        have hne : (r : ℕ) ≠ 0 := fun h => hr (Fin.ext h)
        simp [hne]
      · intro h
        exact (h (Finset.mem_univ _)).elim
    cases b
    · have hnot (r : Fin m) :
          (if decide ((r : ℕ) = 0) = false then (1 : ℝ) else 0) =
            1 - if (r : ℕ) = 0 then 1 else 0 := by
        by_cases h : (r : ℕ) = 0 <;> simp [h]
      simp only [hnot, Finset.sum_sub_distrib, hzero, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, mul_one, Bool.false_eq_true, ↓reduceIte]
      field_simp
    · simp only [decide_eq_true_eq, hzero, ↓reduceIte]
      field_simp
  simp only [noiseMask, funext_iff, ← Fintype.prod_boole, bernoulliWeight]
  rw [← Fintype.prod_sum fun x (r : Fin m) =>
    if decide ((r : ℕ) = 0) = P x then (1 : ℝ) else 0]
  simp only [hdigit, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]

/-- Uniform expectation over `r : β → Fin m` of `F (noiseMask r)` equals
`bernoulliAverage (1 / m) F`. -/
private theorem expect_noiseMask_eq_bernoulliAverage {m : ℕ} (hm : 0 < m)
    (F : (β → Bool) → ℝ) :
    (𝔼 r : β → Fin m, F (noiseMask r)) = bernoulliAverage (1 / (m : ℝ)) F := by
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  have hfiber : ∑ r : β → Fin m, F (noiseMask r) =
      ∑ P : β → Bool, (∑ r : β → Fin m, if noiseMask r = P then (1 : ℝ) else 0) * F P := by
    simp only [Finset.sum_mul, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_univ _)]
  rw [Fintype.expect_eq_sum_div_card, hfiber, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow,
    div_eq_mul_inv, Finset.sum_mul, bernoulliAverage]
  refine Finset.sum_congr rfl fun P _ => ?_
  rw [sum_noiseMask_eq_bernoulliWeight hm P]
  field_simp

/-- For `2 ≤ m`, every single mask has Bernoulli weight at most `(1 - 1 / m) ^ |β|`. -/
private theorem bernoulliWeight_inv_le {β : Type} [Fintype β] {m : ℕ} (hm : 2 ≤ m)
    (P : β → Bool) :
    bernoulliWeight (1 / (m : ℝ)) P ≤ (1 - 1 / (m : ℝ)) ^ Fintype.card β := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hinv_nn : (0 : ℝ) ≤ 1 / (m : ℝ) := by positivity
  have hinv_le : 1 / (m : ℝ) ≤ 1 - 1 / (m : ℝ) := by
    rw [le_sub_iff_add_le, show 1 / (m : ℝ) + 1 / (m : ℝ) = 2 / (m : ℝ) by ring,
      div_le_one hm0]
    exact hm2
  rw [bernoulliWeight_eq_pow_mul_pow]
  have hsub : 0 ≤ 1 - 1 / (m : ℝ) := le_trans hinv_nn hinv_le
  have hpow : (1 / (m : ℝ)) ^ weight P ≤ (1 - 1 / (m : ℝ)) ^ weight P :=
    pow_le_pow_left₀ hinv_nn hinv_le _
  calc (1 / (m : ℝ)) ^ weight P * (1 - 1 / (m : ℝ)) ^ (Fintype.card β - weight P)
      ≤ (1 - 1 / (m : ℝ)) ^ weight P * (1 - 1 / (m : ℝ)) ^ (Fintype.card β - weight P) :=
        mul_le_mul_of_nonneg_right hpow (pow_nonneg hsub _)
    _ = (1 - 1 / (m : ℝ)) ^ (weight P + (Fintype.card β - weight P)) := (pow_add _ _ _).symm
    _ = (1 - 1 / (m : ℝ)) ^ Fintype.card β := by
        rw [Nat.add_sub_of_le (weight_le P)]

/-- Summing a function over a duplicate-free complete list equals the `Fintype` sum. -/
private theorem sum_map_eq_univ_sum {α : Type*} [Fintype α] {l : List α}
    (hnd : l.Nodup) (hmem : ∀ x, x ∈ l) (F : α → ℕ) :
    (l.map F).sum = ∑ x : α, F x := by
  classical
  have hfin : l.toFinset = Finset.univ := Finset.ext fun x => by simp [hmem x]
  rw [← hfin, List.sum_toFinset _ hnd]

/-- Counting elements satisfying `p` equals summing the `0/1` indicator along the list. -/
private theorem countP_eq_sum_map {α : Type*} (l : List α) (p : α → Bool) :
    l.countP p = (l.map fun x => if p x then 1 else 0).sum := by
  induction l with
  | nil => rfl
  | cons a ls ih =>
    simp only [List.countP_cons, List.map_cons, List.sum_cons, ih]
    cases p a <;> simp [Nat.add_comm]

/-- Summing a mapped list equals summing over its `Fin` indices. -/
private theorem list_sum_map_eq_fin_sum {α : Type*} (l : List α) (F : α → ℕ) :
    (l.map F).sum = ∑ i : Fin l.length, F (l.get i) := by
  induction l with
  | nil => simp
  | cons a ls ih =>
    rw [List.map_cons, List.sum_cons, ih]
    exact (Fin.sum_univ_succ fun i : Fin (ls.length + 1) => F ((a :: ls).get i)).symm

/-- Total number of unfiltered `(f, r, g)` triples per edge. -/
private def triplesPerEdge (β γ : Type) [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ] (m : ℕ) : ℕ :=
  Fintype.card (γ → Bool) * Fintype.card (β → Fin m) * Fintype.card (β → Bool)

private theorem triplesPerEdge_pos {m : ℕ} (hm : 0 < m) : 0 < triplesPerEdge β γ m := by
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  simp only [triplesPerEdge]
  exact Nat.mul_pos (Nat.mul_pos Fintype.card_pos Fintype.card_pos) Fintype.card_pos

/-- Number of unfiltered triples on edge `d` satisfied by `(B, A)`. -/
private def edgeAllSat (d : Edge (β → γ)) (m : ℕ)
    (B : (γ → Bool) → Bool) (A : (β → Bool) → Bool) : ℕ :=
  ∑ f : γ → Bool, ∑ r : β → Fin m, ∑ g' : β → Bool,
    if (B f ^^ A g' ^^ A ((f ∘ d.constraint) + g' + noiseMask r)) = false then 1 else 0

/-- The unfiltered satisfied count on edge `d` equals `triplesPerEdge * linearProb`. -/
private theorem edgeAllSat_eq_mul_linearProb {m : ℕ} (hm : 0 < m) (d : Edge (β → γ))
    (B : (γ → Bool) → Bool) (A : (β → Bool) → Bool) :
    (edgeAllSat d m B A : ℝ) =
      (triplesPerEdge β γ m : ℝ) * linearProb d.constraint (1 / (m : ℝ)) B A := by
  have hpos : (triplesPerEdge β γ m : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.2 (triplesPerEdge_pos (β := β) (γ := γ) hm).ne'
  rw [linearProb]
  have hstep :
      (𝔼 f : γ → Bool, 𝔼 g' : β → Bool, bernoulliAverage (1 / (m : ℝ)) fun μ =>
        if (B f ^^ A g' ^^ A ((f ∘ d.constraint) + g' + μ)) = false then (1 : ℝ) else 0) =
      (𝔼 f : γ → Bool, 𝔼 r : β → Fin m, 𝔼 g' : β → Bool,
        if (B f ^^ A g' ^^ A ((f ∘ d.constraint) + g' + noiseMask r)) = false then (1 : ℝ)
        else 0) := by
    refine Finset.expect_congr rfl fun f _ => ?_
    simp_rw [← expect_noiseMask_eq_bernoulliAverage hm]
    exact Finset.expect_comm (s := (Finset.univ : Finset (β → Bool)))
      (t := (Finset.univ : Finset (β → Fin m)))
      (f := fun g' r =>
        if (B f ^^ A g' ^^ A ((f ∘ d.constraint) + g' + noiseMask r)) = false then (1 : ℝ) else 0)
  rw [hstep]
  simp only [Fintype.expect_eq_sum_div_card, ← Finset.sum_div, div_div,
    edgeAllSat, triplesPerEdge, Nat.cast_sum, Nat.cast_mul, Nat.cast_ite, Nat.cast_one,
    Nat.cast_zero]
  have hcard : (Fintype.card (β → Bool) : ℝ) * Fintype.card (β → Fin m) *
      Fintype.card (γ → Bool) =
      (Fintype.card (γ → Bool) : ℝ) * Fintype.card (β → Fin m) * Fintype.card (β → Bool) := by
    ring
  rw [hcard]
  have hne : (Fintype.card (γ → Bool) : ℝ) * Fintype.card (β → Fin m) *
      Fintype.card (β → Bool) ≠ 0 := by
    simpa [triplesPerEdge, Nat.cast_mul] using hpos
  field_simp

/-- Number of degenerate triples dropped on edge `d`. -/
private def edgeDropped (d : Edge (β → γ)) (m : ℕ) : ℕ :=
  ∑ f : γ → Bool,
    (∑ r : β → Fin m, if f ∘ d.constraint = noiseMask r then 1 else 0) *
      Fintype.card (β → Bool)

/-- Per-edge identity: filtered equation count plus dropped count equals `triplesPerEdge`. -/
private theorem length_edgeEquations_add_dropped {m : ℕ} {T : Tables β γ m} (hT : T.Valid)
    (d : Edge (β → γ)) :
    (edgeEquations T d).length + edgeDropped d m = triplesPerEdge β γ m := by
  have hleft : T.leftQueries.length = Fintype.card (β → Bool) := by
    simpa only [List.map_const', List.sum_replicate, smul_eq_mul, mul_one,
      Finset.sum_const, Finset.card_univ] using
      sum_map_eq_univ_sum hT.leftQueries_nodup hT.mem_leftQueries (fun _ => 1)
  have hflt (f : γ → Bool) :
      ((T.noiseDigits.filter fun r => decide (f ∘ d.constraint ≠ noiseMask r)).map
        fun _ => T.leftQueries.length).sum =
      (∑ r : β → Fin m, if f ∘ d.constraint ≠ noiseMask r then 1 else 0) *
        Fintype.card (β → Bool) := by
    rw [List.map_const', List.sum_replicate, smul_eq_mul, hleft, ← List.countP_eq_length_filter,
      countP_eq_sum_map, sum_map_eq_univ_sum hT.noiseDigits_nodup hT.mem_noiseDigits]
    simp only [decide_eq_true_eq]
  have hlen : (edgeEquations T d).length =
      ∑ f : γ → Bool,
        (∑ r : β → Fin m, if f ∘ d.constraint ≠ noiseMask r then 1 else 0) *
          Fintype.card (β → Bool) := by
    simp only [edgeEquations, List.length_flatMap]
    rw [sum_map_eq_univ_sum hT.rightQueries_nodup hT.mem_rightQueries]
    refine Finset.sum_congr rfl fun f _ => ?_
    simp only [List.length_map, hflt f]
  rw [hlen, edgeDropped, ← Finset.sum_add_distrib]
  have hinner (f : γ → Bool) :
      (∑ r : β → Fin m, if f ∘ d.constraint ≠ noiseMask r then 1 else 0) *
          Fintype.card (β → Bool) +
        (∑ r : β → Fin m, if f ∘ d.constraint = noiseMask r then 1 else 0) *
          Fintype.card (β → Bool) =
      Fintype.card (β → Fin m) * Fintype.card (β → Bool) := by
    rw [← Nat.add_mul, ← Finset.sum_add_distrib]
    have h1 : ∀ r : β → Fin m,
        (if f ∘ d.constraint ≠ noiseMask r then 1 else 0) +
          (if f ∘ d.constraint = noiseMask r then 1 else 0) = 1 := fun r => by
      by_cases h : f ∘ d.constraint = noiseMask r <;> simp [h]
    simp only [h1, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]
  simp only [hinner, Finset.sum_const, Finset.card_univ, smul_eq_mul, triplesPerEdge, mul_assoc]

/-- At most a fraction `(1 - 1 / m) ^ |β|` of the triples on any edge are dropped. -/
private theorem edgeDropped_le {m : ℕ} (hm : 2 ≤ m) (d : Edge (β → γ)) :
    (edgeDropped d m : ℝ) ≤
      (1 - 1 / (m : ℝ)) ^ Fintype.card β * (triplesPerEdge β γ m : ℝ) := by
  have hm0 : 0 < m := by omega
  simp only [edgeDropped, Nat.cast_sum, Nat.cast_mul, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  have hterm (f : γ → Bool) :
      (∑ r : β → Fin m, if f ∘ d.constraint = noiseMask r then (1 : ℝ) else 0) *
        (Fintype.card (β → Bool) : ℝ) ≤
      (1 - 1 / (m : ℝ)) ^ Fintype.card β *
        ((Fintype.card (β → Fin m) : ℝ) * (Fintype.card (β → Bool) : ℝ)) := by
    have hsymm :
        (∑ r : β → Fin m, if f ∘ d.constraint = noiseMask r then (1 : ℝ) else 0) =
        ∑ r : β → Fin m, if noiseMask r = f ∘ d.constraint then (1 : ℝ) else 0 :=
      Finset.sum_congr rfl fun r _ => by simp only [eq_comm]
    rw [hsymm, sum_noiseMask_eq_bernoulliWeight hm0 (f ∘ d.constraint)]
    have hcard_r : (Fintype.card (β → Fin m) : ℝ) = (m : ℝ) ^ Fintype.card β := by
      rw [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
    rw [hcard_r]
    have hw := bernoulliWeight_inv_le (β := β) hm (f ∘ d.constraint)
    have hnn : (0 : ℝ) ≤ (m : ℝ) ^ Fintype.card β * (Fintype.card (β → Bool) : ℝ) := by
      positivity
    nlinarith
  calc ∑ f : γ → Bool,
        (∑ r : β → Fin m, if f ∘ d.constraint = noiseMask r then (1 : ℝ) else 0) *
          (Fintype.card (β → Bool) : ℝ)
      ≤ ∑ _f : γ → Bool,
        (1 - 1 / (m : ℝ)) ^ Fintype.card β *
          ((Fintype.card (β → Fin m) : ℝ) * (Fintype.card (β → Bool) : ℝ)) :=
        Finset.sum_le_sum fun f _ => hterm f
    _ = (1 - 1 / (m : ℝ)) ^ Fintype.card β * (triplesPerEdge β γ m : ℝ) := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, triplesPerEdge, Nat.cast_mul]
        ring

/-- Per-edge satisfaction counts on the filtered equations sandwich `edgeAllSat` within
`edgeDropped`. -/
private theorem countSat_edgeEquations_bounds {m : ℕ} {T : Tables β γ m} (hT : T.Valid)
    (σ : ℕ → Bool) (d : Edge (β → γ)) :
    (edgeEquations T d).countP (Constraint.eval CSP.paritySem σ) ≤
        edgeAllSat d m (decodeRight T σ d.dst) (decodeLeft T σ d.src) ∧
      edgeAllSat d m (decodeRight T σ d.dst) (decodeLeft T σ d.src) ≤
        (edgeEquations T d).countP (Constraint.eval CSP.paritySem σ) + edgeDropped d m := by
  let P (f : γ → Bool) (r : β → Fin m) (g' : β → Bool) : Prop :=
    (decodeRight T σ d.dst f ^^ decodeLeft T σ d.src g' ^^
      decodeLeft T σ d.src ((f ∘ d.constraint) + g' + noiseMask r)) = false
  have hcount :
      (edgeEquations T d).countP (Constraint.eval CSP.paritySem σ) =
      ∑ f : γ → Bool, ∑ r : β → Fin m,
        if f ∘ d.constraint ≠ noiseMask r then
          ∑ g' : β → Bool, if P f r g' then (1 : ℕ) else 0
        else 0 := by
    simp only [edgeEquations, List.countP_flatMap, Function.comp_def]
    rw [sum_map_eq_univ_sum hT.rightQueries_nodup hT.mem_rightQueries]
    refine Finset.sum_congr rfl fun f _ => ?_
    have hinner (r : β → Fin m) :
        (T.leftQueries.map fun g' =>
          (⟨f T.pivot,
            [rightVar d.dst (T.rightIdx (foldArg T.pivot f)),
              leftVar d.src (T.leftIdx g'),
              leftVar d.src (T.leftIdx ((f ∘ d.constraint) + g' + noiseMask r))]⟩ :
            Constraint Bool ℕ)).countP (Constraint.eval CSP.paritySem σ) =
        ∑ g' : β → Bool, if P f r g' then (1 : ℕ) else 0 := by
      rw [List.countP_map, countP_eq_sum_map,
        sum_map_eq_univ_sum hT.leftQueries_nodup hT.mem_leftQueries]
      refine Finset.sum_congr rfl fun g' _ => ?_
      simp only [Function.comp_apply, eval_emitted_eq, decide_eq_true_eq, P]
    have hstep :
        ((T.noiseDigits.filter fun r => decide (f ∘ d.constraint ≠ noiseMask r)).map
          fun r => (T.leftQueries.map fun g' =>
            (⟨f T.pivot,
              [rightVar d.dst (T.rightIdx (foldArg T.pivot f)),
                leftVar d.src (T.leftIdx g'),
                leftVar d.src (T.leftIdx ((f ∘ d.constraint) + g' + noiseMask r))]⟩ :
              Constraint Bool ℕ)).countP (Constraint.eval CSP.paritySem σ)).sum =
        ∑ r : β → Fin m,
          if f ∘ d.constraint ≠ noiseMask r then
            ∑ g' : β → Bool, if P f r g' then (1 : ℕ) else 0
          else 0 := by
      rw [List.sum_map_filter, sum_map_eq_univ_sum hT.noiseDigits_nodup hT.mem_noiseDigits]
      refine Finset.sum_congr rfl fun r _ => ?_
      simp only [decide_eq_true_eq, hinner r]
    simpa only [List.countP_flatMap, Function.comp_def] using hstep
  rw [hcount, edgeAllSat, edgeDropped]
  constructor
  · refine Finset.sum_le_sum fun f _ => Finset.sum_le_sum fun r _ => ?_
    split_ifs
    · exact le_rfl
    · exact Nat.zero_le _
  · rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun f _ => ?_
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun r _ => ?_
    by_cases h : f ∘ d.constraint = noiseMask r
    · rw [ite_eq_right (not_not.2 h), ite_eq_left h, zero_add, one_mul]
      calc ∑ g' : β → Bool, (if P f r g' then (1 : ℕ) else 0)
          ≤ ∑ _g' : β → Bool, (1 : ℕ) :=
            Finset.sum_le_sum fun _ _ => by dsimp only [P]; split_ifs <;> omega
        _ = Fintype.card (β → Bool) := by simp
    · rw [ite_eq_left h, ite_eq_right h, zero_mul, add_zero]

/-- The output of `reduce` is always nonempty when `2 ≤ m` and `β` is nonempty. -/
theorem length_reduce_pos {β γ : Type} [Fintype β] [Nonempty β] [Finite γ]
    {m : ℕ} (hm : 2 ≤ m) {T : Tables β γ m} (hT : T.Valid)
    (g : Graph (β → γ)) : 0 < (reduce T g).length := by
  classical
  let _ := Fintype.ofFinite γ
  by_cases hg : g.edges = []
  · rw [reduce_of_edges_nil T hg]
    simp
  · rw [reduce_of_edges_ne_nil T hg]
    obtain ⟨d, ds, hds⟩ := List.exists_cons_of_ne_nil hg
    rw [hds, List.flatMap_cons, List.length_append]
    have hdrop := edgeDropped_le (β := β) (γ := γ) hm d
    have hsum := length_edgeEquations_add_dropped hT d
    have hwlt : (1 - 1 / (m : ℝ)) ^ Fintype.card β < 1 := by
      have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
      have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
      exact pow_lt_one₀ (by rw [sub_nonneg, div_le_one hm0]; linarith)
        (by rw [sub_lt_self_iff]; positivity) Fintype.card_ne_zero
    have hN0 : (0 : ℝ) < triplesPerEdge β γ m :=
      Nat.cast_pos.2 (triplesPerEdge_pos (β := β) (γ := γ) (by omega))
    have hlen_pos : 0 < (edgeEquations T d).length := by
      by_contra h0
      have h0' : (edgeEquations T d).length = 0 := Nat.eq_zero_of_not_pos h0
      rw [h0', zero_add] at hsum
      have hcast : (edgeDropped d m : ℝ) = (triplesPerEdge β γ m : ℝ) := by exact_mod_cast hsum
      nlinarith
    omega

/-- Multi-edge aggregation of filtered counts vs `graphLinearProb`. -/
private theorem total_counts_bounds {m : ℕ} (hm : 2 ≤ m) {T : Tables β γ m}
    (hT : T.Valid) {g : Graph (β → γ)} (hg : g.edges ≠ []) (σ : ℕ → Bool) :
    let w : ℝ := (1 - 1 / (m : ℝ)) ^ Fintype.card β
    let N : ℝ := (g.edges.length : ℝ) * (triplesPerEdge β γ m : ℝ)
    let p : ℝ := graphLinearProb g (1 / (m : ℝ)) (decodeRight T σ) (decodeLeft T σ)
    (1 - w) * N ≤ ((reduce T g).length : ℝ) ∧
      ((reduce T g).length : ℝ) ≤ N ∧
      ((reduce T g).countP (Constraint.eval CSP.paritySem σ) : ℝ) ≤ N * p ∧
      N * p - w * N ≤ ((reduce T g).countP (Constraint.eval CSP.paritySem σ) : ℝ) := by
  intro w N p
  have hm0 : 0 < m := by omega
  have hred := reduce_of_edges_ne_nil T hg
  let totalDrop : ℕ := (g.edges.map fun d => edgeDropped d m).sum
  let totalAllSat : ℕ := (g.edges.map fun d =>
    edgeAllSat d m (decodeRight T σ d.dst) (decodeLeft T σ d.src)).sum
  have hlen_eq : (reduce T g).length + totalDrop = g.edges.length * triplesPerEdge β γ m := by
    rw [hred, List.length_flatMap]
    dsimp only [totalDrop]
    induction g.edges with
    | nil => simp
    | cons d ds ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
      have hd := length_edgeEquations_add_dropped hT d
      omega
  have hdrop_le : (totalDrop : ℝ) ≤ w * N := by
    dsimp only [totalDrop, N]
    rw [list_sum_map_eq_fin_sum]
    push_cast
    calc ∑ i : Fin g.edges.length, (edgeDropped (g.edges.get i) m : ℝ)
        ≤ ∑ _i : Fin g.edges.length, w * (triplesPerEdge β γ m : ℝ) :=
          Finset.sum_le_sum fun i _ => edgeDropped_le (β := β) (γ := γ) hm (g.edges.get i)
      _ = w * ((g.edges.length : ℝ) * (triplesPerEdge β γ m : ℝ)) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  have hallSat_eq : (totalAllSat : ℝ) = N * p := by
    dsimp only [totalAllSat, N, p, graphLinearProb]
    rw [list_sum_map_eq_fin_sum, Fintype.expect_eq_sum_div_card, Fintype.card_fin]
    push_cast
    have hge : (g.edges.length : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (List.length_pos_of_ne_nil hg).ne'
    have hsum :
        ∑ i : Fin g.edges.length,
          (edgeAllSat (g.edges.get i) m (decodeRight T σ (g.edges.get i).dst)
            (decodeLeft T σ (g.edges.get i).src) : ℝ) =
        (triplesPerEdge β γ m : ℝ) *
          ∑ i : Fin g.edges.length,
            linearProb (g.edges.get i).constraint (1 / (m : ℝ))
              (decodeRight T σ (g.edges.get i).dst) (decodeLeft T σ (g.edges.get i).src) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => edgeAllSat_eq_mul_linearProb hm0 _ _ _
    rw [hsum]
    field_simp
  have hsat_bounds :
      (reduce T g).countP (Constraint.eval CSP.paritySem σ) ≤ totalAllSat ∧
      totalAllSat ≤ (reduce T g).countP (Constraint.eval CSP.paritySem σ) + totalDrop := by
    rw [hred, List.countP_flatMap]
    dsimp only [totalAllSat, totalDrop]
    induction g.edges with
    | nil => simp
    | cons d ds ih =>
      simp only [List.map_cons, List.sum_cons, Function.comp_apply]
      have hd := countSat_edgeEquations_bounds hT σ d
      omega
  have hlen_cast : ((reduce T g).length : ℝ) + (totalDrop : ℝ) = N := by
    dsimp only [N]
    exact_mod_cast hlen_eq
  have hsat_le : ((reduce T g).countP (Constraint.eval CSP.paritySem σ) : ℝ) ≤ N * p := by
    rw [← hallSat_eq]
    exact_mod_cast hsat_bounds.1
  have hsat_ge : N * p ≤
      ((reduce T g).countP (Constraint.eval CSP.paritySem σ) : ℝ) + (totalDrop : ℝ) := by
    rw [← hallSat_eq]
    exact_mod_cast hsat_bounds.2
  refine ⟨by linarith, by linarith [Nat.cast_nonneg (α := ℝ) totalDrop], hsat_le, by linarith⟩

private theorem totalAll_pos {m : ℕ} (hm : 2 ≤ m) {g : Graph (β → γ)} (hg : g.edges ≠ []) :
    (0 : ℝ) < (g.edges.length : ℝ) * (triplesPerEdge β γ m : ℝ) :=
  mul_pos (Nat.cast_pos.2 (List.length_pos_of_ne_nil hg))
    (Nat.cast_pos.2 (triplesPerEdge_pos (β := β) (γ := γ) (by omega)))

/-- **Soundness transfer of the folded Long Code reduction**: for every assignment `σ`, the
fraction of equations in `reduce T g` that `σ` satisfies is at most
`graphLinearProb g (1 / m) (decodeRight T σ) (decodeLeft T σ) / (1 - (1 - 1 / m) ^ |β|)`. -/
theorem countSat_reduce_div_length_le [Nonempty β] {m : ℕ} (hm : 2 ≤ m) {T : Tables β γ m}
    (hT : T.Valid) {g : Graph (β → γ)} (hg : g.edges ≠ []) (σ : ℕ → Bool) :
    ((reduce T g).countP (Constraint.eval CSP.paritySem σ) : ℝ) / (reduce T g).length ≤
      graphLinearProb g (1 / (m : ℝ)) (decodeRight T σ) (decodeLeft T σ) /
        (1 - (1 - 1 / (m : ℝ)) ^ Fintype.card β) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hwlt : (1 - 1 / (m : ℝ)) ^ Fintype.card β < 1 :=
    pow_lt_one₀ (by rw [sub_nonneg, div_le_one hm0]; linarith)
      (by rw [sub_lt_self_iff]; positivity) Fintype.card_ne_zero
  have h1w : 0 < 1 - (1 - 1 / (m : ℝ)) ^ Fintype.card β := sub_pos.2 hwlt
  have hN := totalAll_pos (β := β) (γ := γ) hm hg
  have hlen : (0 : ℝ) < (reduce T g).length := Nat.cast_pos.2 (length_reduce_pos hm hT g)
  obtain ⟨hlen_ge, _, hsat_le, _⟩ := total_counts_bounds hm hT hg σ
  rw [div_le_div_iff₀ hlen h1w]
  calc ((reduce T g).countP (Constraint.eval CSP.paritySem σ) : ℝ) *
        (1 - (1 - 1 / (m : ℝ)) ^ Fintype.card β)
      ≤ ((g.edges.length : ℝ) * (triplesPerEdge β γ m : ℝ) *
          graphLinearProb g (1 / (m : ℝ)) (decodeRight T σ) (decodeLeft T σ)) *
        (1 - (1 - 1 / (m : ℝ)) ^ Fintype.card β) :=
        mul_le_mul_of_nonneg_right hsat_le h1w.le
    _ = graphLinearProb g (1 / (m : ℝ)) (decodeRight T σ) (decodeLeft T σ) *
        ((1 - (1 - 1 / (m : ℝ)) ^ Fintype.card β) *
          ((g.edges.length : ℝ) * (triplesPerEdge β γ m : ℝ))) := by ring
    _ ≤ graphLinearProb g (1 / (m : ℝ)) (decodeRight T σ) (decodeLeft T σ) *
        ((reduce T g).length : ℝ) := by
        refine mul_le_mul_of_nonneg_left hlen_ge ?_
        have hsat_nn : (0 : ℝ) ≤ (reduce T g).countP (Constraint.eval CSP.paritySem σ) :=
          Nat.cast_nonneg _
        nlinarith

/-- **Completeness transfer of the folded Long Code reduction**: for any folded right tables `B`
and arbitrary left tables `A`, some assignment `σ` satisfies at least a fraction
`graphLinearProb g (1 / m) B A - (1 - 1 / m) ^ |β|` of the equations of `reduce T g`. -/
theorem exists_countSat_reduce_ge [Nonempty β] {m : ℕ} (hm : 2 ≤ m) {T : Tables β γ m}
    (hT : T.Valid) {g : Graph (β → γ)} (hg : g.edges ≠ [])
    {B : ℕ → (γ → Bool) → Bool} (hB : ∀ w, IsOdd (B w)) (A : ℕ → (β → Bool) → Bool) :
    ∃ σ : ℕ → Bool,
      graphLinearProb g (1 / (m : ℝ)) B A - (1 - 1 / (m : ℝ)) ^ Fintype.card β ≤
        ((reduce T g).countP (Constraint.eval CSP.paritySem σ) : ℝ) / (reduce T g).length := by
  let σ := encodeTables T B A
  have hdecR : decodeRight T σ = B := funext fun w => decodeRight_encodeTables hT hB A w
  have hdecL : decodeLeft T σ = A := funext fun u => decodeLeft_encodeTables hT B A u
  obtain ⟨_, hlen_le, _, hsat_ge⟩ := total_counts_bounds hm hT hg σ
  rw [hdecR, hdecL] at hsat_ge
  refine ⟨σ, ?_⟩
  have hdiv1 : graphLinearProb g (1 / (m : ℝ)) B A - (1 - 1 / (m : ℝ)) ^ Fintype.card β ≤
      ((reduce T g).countP (Constraint.eval CSP.paritySem σ) : ℝ) /
        ((g.edges.length : ℝ) * (triplesPerEdge β γ m : ℝ)) :=
    (le_div_iff₀ (totalAll_pos (β := β) (γ := γ) hm hg)).2 (by linarith)
  exact hdiv1.trans (div_le_div_of_nonneg_left (Nat.cast_nonneg _)
    (Nat.cast_pos.2 (length_reduce_pos hm hT g)) hlen_le)

end Counting

/-! ### Polynomial-time computability -/

section PolyTime

/-- Edge-local equation template, depending only on the finite projection `π : β → γ`. -/
private structure EqTemplate where
  rhs : Bool
  rightIdx : ℕ
  leftIdx₁ : ℕ
  leftIdx₂ : ℕ

private enc_structure encEqTemplate : EqTemplate where
  rhs : encBool, rightIdx : encUnary, leftIdx₁ : encUnary, leftIdx₂ : encUnary

/-- Non-degenerate templates generated for a projection `π : β → γ`. -/
private def edgeTemplates {β γ : Type} [Fintype β] {m : ℕ}
    (T : Tables β γ m) (π : β → γ) : List EqTemplate :=
  T.rightQueries.flatMap fun f =>
    (T.noiseDigits.filter fun r => decide (f ∘ π ≠ noiseMask r)).flatMap fun r =>
      T.leftQueries.map fun g =>
        ⟨f T.pivot, T.rightIdx (foldArg T.pivot f), T.leftIdx g,
          T.leftIdx ((f ∘ π) + g + noiseMask r)⟩

/-- Instantiate a template on an edge `d` into a three-variable parity constraint. -/
private def instantiateTemplate {C : Type} (d : Edge C) (t : EqTemplate) :
    Constraint Bool ℕ :=
  ⟨t.rhs, [rightVar d.dst t.rightIdx, leftVar d.src t.leftIdx₁, leftVar d.src t.leftIdx₂]⟩

private theorem edgeEquations_eq_map_templates {β γ : Type} [Fintype β] {m : ℕ}
    (T : Tables β γ m) (d : Edge (β → γ)) :
    edgeEquations T d = (edgeTemplates T d.constraint).map (instantiateTemplate d) := by
  simp only [edgeEquations, edgeTemplates, instantiateTemplate, List.map_flatMap, List.map_map,
    Function.comp_def]

private theorem isPolyTime_rightVar :
    ComputableInPolyTime (fun p : ℕ × ℕ => rightVar p.1 p.2)
      (encPair encUnary encUnary) encNat :=
  ComputableInPolyTime.unary_to_binary.comp
    (ComputableInPolyTime.unary_mul' (.const 2) ComputableInPolyTime.unary_pair)

private theorem isPolyTime_leftVar :
    ComputableInPolyTime (fun p : ℕ × ℕ => leftVar p.1 p.2)
      (encPair encUnary encUnary) encNat :=
  ComputableInPolyTime.unary_to_binary.comp
    (ComputableInPolyTime.unary_add'
      (ComputableInPolyTime.unary_mul' (.const 2) ComputableInPolyTime.unary_pair) (.const 1))

/-- Combining an edge with a template produces a binary-variable parity constraint in polynomial
time. -/
private theorem isPolyTime_instantiateTemplate {C : Type} (encC : C ↪ List Bool) :
    ComputableInPolyTime
      (fun p : Edge C × EqTemplate => instantiateTemplate p.1 p.2)
      (encPair (Edge.encoding encC) encEqTemplate)
      (encConstraint encBool encNat) := by
  have hright := isPolyTime_rightVar
  have hleft := isPolyTime_leftVar
  have hcons := ComputableInPolyTime.cons encNat
  unfold instantiateTemplate
  fun_prop

/-- Generating the equations for a single edge is polynomial-time for fixed finite `β, γ` and
fixed `T`. -/
private theorem isPolyTime_edgeEquations {β γ : Type} [Fintype β] [Finite γ]
    {m : ℕ} (T : Tables β γ m) (encG : γ ↪ List Bool) :
    ComputableInPolyTime (edgeEquations T)
      (Edge.encoding (encPi encG)) (encCSP encBool encNat) := by
  have htpl : ComputableInPolyTime (edgeTemplates T)
      (encPi encG) (encList encEqTemplate) := .of_finite _
  have hlist : ComputableInPolyTime (fun d : Edge (β → γ) => edgeTemplates T d.constraint)
      (Edge.encoding (encPi encG)) (encList encEqTemplate) :=
    htpl.comp (Edge.isPolyTime_constraint .id')
  have hmap := ComputableInPolyTime.mapWithInput hlist (isPolyTime_instantiateTemplate (encPi encG))
  have heq : edgeEquations T =
      fun d => (edgeTemplates T d.constraint).map (instantiateTemplate d) :=
    funext (edgeEquations_eq_map_templates T)
  rw [heq]
  exact hmap

/-- **Håstad's folded Long Code reduction is polynomial-time** for fixed finite label sets `β, γ`,
fixed noise denominator `m`, and fixed finite tables `T`, from `Graph.encoding (encPi encG)`
(unary endpoints, complete projection tables) to `encCSP encBool encNat` (binary variable
indices). -/
@[fun_prop]
theorem isPolyTime_reduce {β γ : Type} [Fintype β] [Finite γ]
    {m : ℕ} (T : Tables β γ m) (encG : γ ↪ List Bool) :
    ComputableInPolyTime (reduce T)
      (Graph.encoding (encPi encG)) (encCSP encBool encNat) := by
  have hedges : ComputableInPolyTime (fun g : Graph (β → γ) => g.edges)
      (Graph.encoding (encPi encG)) (encList (Edge.encoding (encPi encG))) :=
    Graph.isPolyTime_edges .id'
  have hempty : ComputableInPolyTime (fun g : Graph (β → γ) => g.edges.isEmpty)
      (Graph.encoding (encPi encG)) encBool :=
    (ComputableInPolyTime.listIsEmpty' (Edge.encoding (encPi encG))).comp hedges
  have hflat : ComputableInPolyTime (fun g : Graph (β → γ) => g.edges.flatMap (edgeEquations T))
      (Graph.encoding (encPi encG)) (encCSP encBool encNat) :=
    ComputableInPolyTime.flatMapWithInput hedges
      ((isPolyTime_edgeEquations T encG).comp (.snd _ _))
  exact ComputableInPolyTime.ite hempty (.const [trivialEq]) hflat

end PolyTime

end Cslib.PCP.Hastad.Reduction
