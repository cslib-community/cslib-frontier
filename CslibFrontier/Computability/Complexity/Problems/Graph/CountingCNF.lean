/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.ExactOne
public import CslibFrontier.Computability.Complexity.Problems.Coloring
public import CslibFrontier.Computability.Complexity.Problems.Graph.PerfectMatchingPolyTime
public import CslibFrontier.Computability.Complexity.Problems.IndependentSet
public import CslibFrontier.Logics.Propositional.CNF.GraphCountingEncodings
public import CslibFrontier.Logics.Propositional.CNF.ModelCount.Declared
import CslibFrontier.Computability.Circuit.Boolean.Encoding
import CslibFrontier.Computability.Complexity.Problems.Graph.VertexColors
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Foundations.Data.List.EraseDupsBy
import CslibFrontier.Foundations.Data.List.Lookup
import CslibFrontier.Foundations.Data.List.Range
import CslibFrontier.Logics.Propositional.CSP.Vars
import CslibFrontier.Tactic.EncLen

/-!
# Polynomial-time counting CNF reductions for graph problems

Executable polynomial-time CNF encodings for three classical graph counting problems on
`Cslib.Complexity.Graph`, preserving exact solution counts with explicit assignment bijections:

1. **Independent sets** (`Graph.toIndepSetCNF`): `n = |V|` variables, clause width `2`,
   preserving `Nat.card {S // G.induced.IsIndepSet S}`.
2. **Proper `q`-colourings** (`Graph.toColoringCNF q`): `n = q * |V|` variables, clause width
   `≤ max q 2`, preserving `Nat.card (G.induced.Coloring (Fin q))`.
3. **Perfect matchings** (`Graph.toPerfectMatchingCNF`): `n ≤ 1 + 4 |V| + 7 |E| = O(|V| + |E|)`
   variables, exact clause width `3`, compiled via sequential linear-size exact-one De Morgan
   circuits (`Cslib.Circuits.Boolean.seqExactlyOneAll`) and `tseitinSatCNF`, preserving
   `Nat.card {M : G.induced.Subgraph // M.IsPerfectMatching}` ([Tseitin 1983][Tseitin1983],
   [Cygan et al.][CyganEtAl2015]).

## Main definitions

* `Cslib.Complexity.Graph.toIndepSetCNF`, `Cslib.Complexity.Graph.indepSetCNFEquiv`.
* `Cslib.Complexity.Graph.coloringVar`, `Cslib.Complexity.Graph.toColoringCNF`,
  `Cslib.Complexity.Graph.coloringCNFEquiv`.
* `Cslib.Complexity.Graph.perfectMatchingWires`, `Cslib.Complexity.Graph.perfectMatchingCircuit`,
  `Cslib.Complexity.Graph.toPerfectMatchingCNF`, `Cslib.Complexity.Graph.perfectMatchingCNFEquiv`.

## Main results

* `Cslib.Complexity.Graph.modelCount_toIndepSetCNF`,
  `Cslib.Complexity.Graph.computableInPolyTime_toIndepSetCNF`: exact count, width `2`,
  `numVars = |V|`, and polynomial-time compilation for independent sets.
* `Cslib.Complexity.Graph.modelCount_toColoringCNF`,
  `Cslib.Complexity.Graph.computableInPolyTime_toColoringCNF`: exact count, width `≤ max q 2`,
  `numVars = q * |V|`, and polynomial-time compilation for `q`-colourings.
* `Cslib.Complexity.Graph.modelCountOn_toPerfectMatchingCNF`,
  `Cslib.Complexity.Graph.numVars_toPerfectMatchingCNF_le`,
  `Cslib.Complexity.Graph.computableInPolyTime_toPerfectMatchingCNF`: exact count, width `3`,
  linear `O(|V| + |E|)` variables and clauses, and polynomial-time compilation for perfect
  matchings.

## References

* [S. Arora and B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [M. Cygan, F. V. Fomin, Ł. Kowalik, D. Lokshtanov, D. Marx, M. Pilipczuk, M. Pilipczuk,
  and S. Saurabh, *Parameterized Algorithms*][CyganEtAl2015]
* [G. S. Tseitin, *On the complexity of derivation in propositional calculus*][Tseitin1983]
-/

public section

namespace Cslib.Complexity.Graph

open Cslib.Logic.PL Turing.MultiTapeTM ComputableInPolyTime Circuits Boolean

/-! ### 1. Independent sets (`n = |V|`, width `2`) -/

/-- Executable width-`2` CNF encoding of the independent sets of `G.induced` on `|V|` variables. -/
@[expose] def toIndepSetCNF (G : Graph) : CNF ℕ :=
  CNF.indepSetCNF G.vertices G.edges

/-- Every clause of `G.toIndepSetCNF` has exact length `2`. -/
theorem length_clause_toIndepSetCNF {G : Graph} {c : Clause ℕ} (hc : c ∈ G.toIndepSetCNF) :
    c.length = 2 :=
  CNF.length_clause_indepSetCNF hc

/-- `G.toIndepSetCNF` has exactly `G.1.toFinset.card` occurring variables. -/
@[simp]
theorem numVars_toIndepSetCNF (G : Graph) : G.toIndepSetCNF.numVars = G.vertices.toFinset.card :=
  CNF.numVars_indepSetCNF G.vertices G.edges

/-- Occurring variables of `G.toIndepSetCNF` are bounded by `(encGraph G).length`. -/
theorem numVars_toIndepSetCNF_le_enc (G : Graph) :
    G.toIndepSetCNF.numVars ≤ (encGraph G).length := by
  rw [numVars_toIndepSetCNF]
  exact G.vertices.toFinset_card_le.trans G.length_vertices_le_encGraph

/-- Explicit bijection between satisfying assignments of `G.toIndepSetCNF` on `G.1.toFinset`
and independent sets of `G.induced`. -/
def indepSetCNFEquiv (G : Graph) :
    {σ : G.vertices.toFinset → Bool //
      G.toIndepSetCNF.eval (fun v => if hv : v ∈ G.vertices.toFinset then σ ⟨v, hv⟩ else false) =
        true} ≃
      {S : Finset {v : ℕ // v ∈ G.vertices} //
        G.induced.IsIndepSet (S : Set {v : ℕ // v ∈ G.vertices})} :=
  CNF.indepSetCNFEquiv (G := G.induced) fun _ _ => Graph.induced_adj.trans Graph.toSimpleGraph_adj

/-- **Exact model count of `G.toIndepSetCNF`**: number of independent sets of `G.induced`. -/
theorem modelCount_toIndepSetCNF (G : Graph) :
    G.toIndepSetCNF.modelCount =
      Nat.card {S : Finset {v : ℕ // v ∈ G.vertices} //
        G.induced.IsIndepSet (S : Set {v : ℕ // v ∈ G.vertices})} :=
  CNF.modelCount_indepSetCNF (G := G.induced) fun _ _ =>
    Graph.induced_adj.trans Graph.toSimpleGraph_adj

private theorem computableInPolyTime_edgePairs :
    ComputableInPolyTime (fun G : Graph => CNF.edgePairs G.vertices G.edges)
      encGraph (encList (encPair encNat encNat)) := by
  have h : ComputableInPolyTime
      (fun G : Graph => G.edges.filter fun e =>
        decide (e.1 ∈ G.vertices) && decide (e.2 ∈ G.vertices) && decide (e.1 ≠ e.2))
      encGraph (encList (encPair encNat encNat)) := by
    fun_prop
  refine h.of_enc_eq fun G => congrArg (encList (encPair encNat encNat)) ?_
  simp only [CNF.edgePairs, Bool.decide_and, Bool.and_assoc]

/-- Constructing `G.toIndepSetCNF` from `encGraph` is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_toIndepSetCNF :
    ComputableInPolyTime toIndepSetCNF encGraph encCNF := by
  have hed := computableInPolyTime_edgePairs
  unfold toIndepSetCNF CNF.indepSetCNF
  fun_prop

/-! ### 2. Proper `q`-colourings (`n = q * |V|`, width `≤ max q 2`) -/

/-- Natural variable index encoding `(v, c)` as `q * G.distinctVertices.idxOf v + c`. -/
@[expose] def coloringVar (q : ℕ) (G : Graph) (p : ℕ × ℕ) : ℕ :=
  q * G.distinctVertices.idxOf p.1 + p.2

/-- Executable CNF encoding of proper `q`-colourings of `G.induced` over dense natural variables
`0, …, q * |V| - 1`, with clause width at most `max q 2`. -/
@[expose] def toColoringCNF (q : ℕ) (G : Graph) : CNF ℕ :=
  (CNF.coloringCNF q G.vertices G.edges).relabel (coloringVar q G)

/-- Every clause of `G.toColoringCNF q` has width at most `max q 2`. -/
theorem length_clause_toColoringCNF_le {q : ℕ} {G : Graph} {c : Clause ℕ}
    (hc : c ∈ G.toColoringCNF q) : c.length ≤ max q 2 := by
  simp only [toColoringCNF, CNF.relabel, Clause.relabel, List.mem_map] at hc
  obtain ⟨c₀, hc₀, rfl⟩ := hc
  rw [List.length_map]
  exact CNF.length_clause_coloringCNF_le hc₀

private theorem coloringVar_injOn (q : ℕ) (G : Graph) :
    Set.InjOn (coloringVar q G) {p | p ∈ (CNF.coloringCNF q G.vertices G.edges).vars} := by
  intro ⟨v₁, c₁⟩ h₁ ⟨v₂, c₂⟩ h₂ heq
  obtain ⟨hv₁, hc₁⟩ := CNF.mem_vars_coloringCNF.mp h₁
  obtain ⟨hv₂, hc₂⟩ := CNF.mem_vars_coloringCNF.mp h₂
  dsimp only [coloringVar] at heq
  have hq : 0 < q := Nat.zero_lt_of_lt hc₁
  have hdv₁ : (q * G.distinctVertices.idxOf v₁ + c₁) / q = G.distinctVertices.idxOf v₁ := by
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ hq, Nat.div_eq_of_lt hc₁, Nat.zero_add]
  have hdv₂ : (q * G.distinctVertices.idxOf v₂ + c₂) / q = G.distinctVertices.idxOf v₂ := by
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ hq, Nat.div_eq_of_lt hc₂, Nat.zero_add]
  have hdiv : G.distinctVertices.idxOf v₁ = G.distinctVertices.idxOf v₂ :=
    hdv₁.symm.trans ((congrArg (· / q) heq).trans hdv₂)
  have hmod : c₁ = c₂ := by
    have hm1 : (q * G.distinctVertices.idxOf v₁ + c₁) % q = c₁ := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc₁]
    have hm2 : (q * G.distinctVertices.idxOf v₂ + c₂) % q = c₂ := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc₂]
    exact hm1.symm.trans ((congrArg (· % q) heq).trans hm2)
  have hvEq : v₁ = v₂ :=
    (List.idxOf_inj (Graph.mem_distinctVertices.mpr hv₁)).mp hdiv
  exact Prod.ext hvEq hmod

/-- The occurring variables of `G.toColoringCNF q` are precisely `Finset.range (q * |V|)`. -/
theorem vars_toColoringCNF (q : ℕ) (G : Graph) :
    (G.toColoringCNF q).vars.toFinset = Finset.range (q * G.distinctVertices.length) := by
  ext k
  rw [toColoringCNF, List.mem_toFinset, CNF.vars_relabel, List.mem_map, Finset.mem_range]
  constructor
  · rintro ⟨⟨v, c⟩, hv, rfl⟩
    obtain ⟨hvG, hc⟩ := CNF.mem_vars_coloringCNF.mp hv
    have hidx : G.distinctVertices.idxOf v < G.distinctVertices.length :=
      List.idxOf_lt_length_iff.mpr (Graph.mem_distinctVertices.mpr hvG)
    have h1 : q * G.distinctVertices.idxOf v + c < q * (G.distinctVertices.idxOf v + 1) := by
      rw [Nat.mul_add, Nat.mul_one]
      omega
    exact h1.trans_le (Nat.mul_le_mul_left q (Nat.succ_le_of_lt hidx))
  · intro hk
    have hq : 0 < q := by
      by_contra hq0
      have hq' : q = 0 := by omega
      subst hq'
      simp at hk
    have hdiv : k / q < G.distinctVertices.length := (Nat.div_lt_iff_lt_mul hq).mpr
      (by simpa only [Nat.mul_comm] using hk)
    let v := G.distinctVertices[k / q]
    have hv : v ∈ G.vertices := Graph.mem_distinctVertices.mp (List.getElem_mem hdiv)
    refine ⟨(v, k % q), CNF.mem_vars_coloringCNF.mpr ⟨hv, Nat.mod_lt k hq⟩, ?_⟩
    rw [coloringVar, (Graph.nodup_distinctVertices G).idxOf_getElem (k / q) hdiv]
    have := Nat.div_add_mod k q
    omega

/-- `G.toColoringCNF q` uses exactly `q * G.1.toFinset.card` variables. -/
@[simp]
theorem numVars_toColoringCNF (q : ℕ) (G : Graph) :
    (G.toColoringCNF q).numVars = q * G.vertices.toFinset.card := by
  rw [CNF.numVars, vars_toColoringCNF, Finset.card_range, Graph.length_distinctVertices]

theorem validDeclaredInput_toColoringCNF (q : ℕ) (G : Graph) :
    CNF.validDeclaredInput (max q 2) (q * G.distinctVertices.length) (G.toColoringCNF q) =
      true := by
  rw [CNF.validDeclaredInput_eq_true_iff, vars_toColoringCNF]
  exact ⟨fun _ hc => length_clause_toColoringCNF_le hc, Finset.Subset.rfl⟩

/-- Variable-domain bijection `G.1.toFinset ×ˢ Finset.range q ≃ Finset.range (q * |V|)`. -/
private def coloringDomainEquiv (q : ℕ) (G : Graph) :
    ↥(G.vertices.toFinset ×ˢ Finset.range q) ≃ ↥(Finset.range (q * G.distinctVertices.length)) where
  toFun p := ⟨coloringVar q G p.val, by
    have hp := Finset.mem_product.mp p.property
    have hvG : p.val.1 ∈ G.vertices := List.mem_toFinset.mp hp.1
    have hc : p.val.2 < q := Finset.mem_range.mp hp.2
    have hidx : G.distinctVertices.idxOf p.val.1 < G.distinctVertices.length :=
      List.idxOf_lt_length_iff.mpr (Graph.mem_distinctVertices.mpr hvG)
    have h1 : q * G.distinctVertices.idxOf p.val.1 + p.val.2 <
        q * (G.distinctVertices.idxOf p.val.1 + 1) := by
      rw [Nat.mul_add, Nat.mul_one]
      omega
    exact Finset.mem_range.mpr (h1.trans_le (Nat.mul_le_mul_left q (Nat.succ_le_of_lt hidx)))⟩
  invFun k := ⟨(G.distinctVertices[k.val / q]'(by
      have hq : 0 < q := by
        by_contra h0
        have : q = 0 := by omega
        have hk := Finset.mem_range.mp k.property
        subst this
        simp at hk
      exact (Nat.div_lt_iff_lt_mul hq).mpr
        (by simpa only [Nat.mul_comm] using Finset.mem_range.mp k.property)), k.val % q), by
    have hk := Finset.mem_range.mp k.property
    have hq : 0 < q := by
      by_contra h0
      have : q = 0 := by omega
      subst this
      simp at hk
    have hdiv : k.val / q < G.distinctVertices.length :=
      (Nat.div_lt_iff_lt_mul hq).mpr (by simpa only [Nat.mul_comm] using hk)
    exact Finset.mem_product.mpr
      ⟨List.mem_toFinset.mpr (Graph.mem_distinctVertices.mp (List.getElem_mem hdiv)),
        Finset.mem_range.mpr (Nat.mod_lt k.val hq)⟩⟩
  left_inv p := by
    have hp := Finset.mem_product.mp p.property
    have hvG : p.val.1 ∈ G.vertices := List.mem_toFinset.mp hp.1
    have hc : p.val.2 < q := Finset.mem_range.mp hp.2
    have hq : 0 < q := Nat.zero_lt_of_lt hc
    have hdiv : (q * G.distinctVertices.idxOf p.val.1 + p.val.2) / q =
        G.distinctVertices.idxOf p.val.1 := by
      rw [Nat.add_comm, Nat.add_mul_div_left _ _ hq, Nat.div_eq_of_lt hc, Nat.zero_add]
    have hmod : (q * G.distinctVertices.idxOf p.val.1 + p.val.2) % q = p.val.2 := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc]
    refine Subtype.ext (Prod.ext ?_ hmod)
    simp only [coloringVar, hdiv]
    exact List.getElem_idxOf (List.idxOf_lt_length_iff.mpr (Graph.mem_distinctVertices.mpr hvG))
  right_inv k := by
    have hk := Finset.mem_range.mp k.property
    have hq : 0 < q := by
      by_contra h0
      have : q = 0 := by omega
      subst this
      simp at hk
    have hdiv : k.val / q < G.distinctVertices.length :=
      (Nat.div_lt_iff_lt_mul hq).mpr (by simpa only [Nat.mul_comm] using hk)
    refine Subtype.ext ?_
    dsimp only [coloringVar]
    rw [(Graph.nodup_distinctVertices G).idxOf_getElem (k.val / q) hdiv]
    have := Nat.div_add_mod k.val q
    omega

/-- Explicit bijection between satisfying assignments of `G.toColoringCNF q` on
`Finset.range (q * |V|)` and proper `q`-colourings of `G.induced`. -/
noncomputable def coloringCNFEquiv (q : ℕ) (G : Graph) :
    {σ : Finset.range (q * G.distinctVertices.length) → Bool //
      (G.toColoringCNF q).eval
        (fun k => if hk : k ∈ Finset.range (q * G.distinctVertices.length) then σ ⟨k, hk⟩
          else false) = true} ≃
      G.induced.Coloring (Fin q) := by
  let eAssign :
      {σ : Finset.range (q * G.distinctVertices.length) → Bool //
        (G.toColoringCNF q).eval
          (fun k => if hk : k ∈ Finset.range (q * G.distinctVertices.length) then σ ⟨k, hk⟩
            else false) = true} ≃
      {σ : G.vertices.toFinset ×ˢ Finset.range q → Bool //
        (CNF.coloringCNF q G.vertices G.edges).eval
          (fun p => if hp : p ∈ G.vertices.toFinset ×ˢ Finset.range q then σ ⟨p, hp⟩ else false) =
            true} :=
    { toFun := fun σ => ⟨fun p => σ.val (coloringDomainEquiv q G p), by
        have h := σ.property
        dsimp only [toColoringCNF] at h
        rw [CNF.eval_relabel] at h
        refine (CNF.eval_congr fun p hp => ?_).trans h
        have hp' : p ∈ G.vertices.toFinset ×ˢ Finset.range q := by
          obtain ⟨hv, hc⟩ := CNF.mem_vars_coloringCNF.mp hp
          exact Finset.mem_product.mpr ⟨List.mem_toFinset.mpr hv, Finset.mem_range.mpr hc⟩
        have hmem : coloringVar q G p ∈ Finset.range (q * G.distinctVertices.length) :=
          (coloringDomainEquiv q G ⟨p, hp'⟩).property
        simp only [Function.comp_def, hp', ↓reduceDIte, hmem]
        rfl⟩
      invFun := fun σ => ⟨fun k => σ.val ((coloringDomainEquiv q G).symm k), by
        dsimp only [toColoringCNF]
        rw [CNF.eval_relabel]
        refine (CNF.eval_congr fun p hp => ?_).trans σ.property
        have hp' : p ∈ G.vertices.toFinset ×ˢ Finset.range q := by
          obtain ⟨hv, hc⟩ := CNF.mem_vars_coloringCNF.mp hp
          exact Finset.mem_product.mpr ⟨List.mem_toFinset.mpr hv, Finset.mem_range.mpr hc⟩
        have hmem : coloringVar q G p ∈ Finset.range (q * G.distinctVertices.length) :=
          (coloringDomainEquiv q G ⟨p, hp'⟩).property
        simp only [Function.comp_def, hmem, ↓reduceDIte, hp']
        exact congrArg σ.val ((coloringDomainEquiv q G).symm_apply_apply ⟨p, hp'⟩)⟩
      left_inv := fun σ => Subtype.ext (funext fun k =>
        congrArg σ.val ((coloringDomainEquiv q G).apply_symm_apply k))
      right_inv := fun σ => Subtype.ext (funext fun p =>
        congrArg σ.val ((coloringDomainEquiv q G).symm_apply_apply p)) }
  exact eAssign.trans (CNF.coloringCNFEquiv (G := G.induced) fun _ _ =>
    Graph.induced_adj.trans Graph.toSimpleGraph_adj)

/-- **Exact model count of `G.toColoringCNF q`**: number of proper `q`-colourings of `G.induced`. -/
theorem modelCount_toColoringCNF (q : ℕ) (G : Graph) :
    (G.toColoringCNF q).modelCount = Nat.card (G.induced.Coloring (Fin q)) := by
  rw [toColoringCNF, CNF.modelCount_relabel_of_injOn _ (coloringVar_injOn q G)]
  exact CNF.modelCount_coloringCNF (G := G.induced) fun _ _ =>
    Graph.induced_adj.trans Graph.toSimpleGraph_adj

theorem modelCountOn_toColoringCNF (q : ℕ) (G : Graph) :
    (G.toColoringCNF q).modelCountOn (Finset.range (q * G.distinctVertices.length)) =
      Nat.card (G.induced.Coloring (Fin q)) := by
  rw [← vars_toColoringCNF, CNF.modelCountOn_vars, modelCount_toColoringCNF]

private theorem polyTime_coloringVar (q c : ℕ) :
    ComputableInPolyTime (fun p : Graph × ℕ => coloringVar q p.1 (p.2, c))
      (encPair encGraph encNat) encNat := by
  unfold coloringVar
  have hidx := idxOfWithInput
    (Graph.computableInPolyTime_distinctVertices.comp (fst encGraph encNat)) (snd encGraph encNat)
  exact unary_to_binary.comp
    (unary_add.comp ((unary_mul.comp ((const q).prod hidx)).prod (const c)))

private theorem polyTime_coloringVertexClauses (q : ℕ) :
    ComputableInPolyTime
      (fun p : Graph × ℕ =>
        ([(List.range q).map fun c => (coloringVar q p.1 (p.2, c), true)] : CNF ℕ) ++
          (List.range q).flatMap fun c₁ =>
            ((List.range q).filter fun c₂ => decide (c₁ ≠ c₂)).map fun c₂ =>
              [(coloringVar q p.1 (p.2, c₁), false), (coloringVar q p.1 (p.2, c₂), false)])
      (encPair encGraph encNat) encCNF := by
  have hal : ComputableInPolyTime
      (fun p : Graph × ℕ => (List.range q).map fun c => (coloringVar q p.1 (p.2, c), true))
      (encPair encGraph encNat) (encClause encNat) :=
    mapConst (List.range q) fun c _ => (polyTime_coloringVar q c).prod (const true)
  have hamo : ComputableInPolyTime
      (fun p : Graph × ℕ =>
        (List.range q).flatMap fun c₁ =>
          ((List.range q).filter fun c₂ => decide (c₁ ≠ c₂)).map fun c₂ =>
            [(coloringVar q p.1 (p.2, c₁), false), (coloringVar q p.1 (p.2, c₂), false)])
      (encPair encGraph encNat) encCNF :=
    flatMapConst (List.range q) fun c₁ _ =>
      mapConst ((List.range q).filter fun c₂ => decide (c₁ ≠ c₂)) fun c₂ _ =>
        ((polyTime_coloringVar q c₁).prod (const false)).cons'
          (((polyTime_coloringVar q c₂).prod (const false)).cons' (const ([] : Clause ℕ)))
  exact (listAppend (encClause encNat)).comp ((hal.cons' (const ([] : CNF ℕ))).prod hamo)

private theorem polyTime_coloringEdgeVar1 (q c : ℕ) :
    ComputableInPolyTime (fun p : Graph × ℕ × ℕ => coloringVar q p.1 (p.2.1, c))
      (encPair encGraph (encPair encNat encNat)) encNat :=
  (polyTime_coloringVar q c).comp
    ((fst encGraph (encPair encNat encNat)).prod (snd encGraph (encPair encNat encNat)).fst')

private theorem polyTime_coloringEdgeVar2 (q c : ℕ) :
    ComputableInPolyTime (fun p : Graph × ℕ × ℕ => coloringVar q p.1 (p.2.2, c))
      (encPair encGraph (encPair encNat encNat)) encNat :=
  (polyTime_coloringVar q c).comp
    ((fst encGraph (encPair encNat encNat)).prod (snd encGraph (encPair encNat encNat)).snd')

private theorem polyTime_coloringEdgeClauses (q : ℕ) :
    ComputableInPolyTime
      (fun p : Graph × ℕ × ℕ =>
        (List.range q).map fun c =>
          [(coloringVar q p.1 (p.2.1, c), false), (coloringVar q p.1 (p.2.2, c), false)])
      (encPair encGraph (encPair encNat encNat)) encCNF :=
  mapConst (List.range q) fun c _ =>
    ((polyTime_coloringEdgeVar1 q c).prod (const false)).cons'
      (((polyTime_coloringEdgeVar2 q c).prod (const false)).cons' (const ([] : Clause ℕ)))

/-- Constructing `G.toColoringCNF q` from `encGraph` is polynomial-time for every fixed `q`. -/
@[fun_prop]
theorem computableInPolyTime_toColoringCNF (q : ℕ) :
    ComputableInPolyTime (toColoringCNF q) encGraph encCNF := by
  have hpart1 : ComputableInPolyTime
      (fun G : Graph => G.vertices.flatMap fun v =>
        [List.map (fun c => (coloringVar q G (v, c), true)) (List.range q)] ++
          (List.range q).flatMap fun c₁ =>
            ((List.range q).filter fun c₂ => decide (c₁ ≠ c₂)).map fun c₂ =>
              [(coloringVar q G (v, c₁), false), (coloringVar q G (v, c₂), false)])
      encGraph encCNF :=
    flatMapWithInput (encGraph_vertices_polyTime id') (polyTime_coloringVertexClauses q)
  have hpart2 : ComputableInPolyTime
      (fun G : Graph => (CNF.edgePairs G.vertices G.edges).flatMap fun e =>
        (List.range q).map fun c =>
          [(coloringVar q G (e.1, c), false), (coloringVar q G (e.2, c), false)])
      encGraph encCNF :=
    flatMapWithInput computableInPolyTime_edgePairs (polyTime_coloringEdgeClauses q)
  refine ((listAppend (encClause encNat)).comp (hpart1.prod hpart2)).of_enc_eq fun G =>
    congrArg encCNF ?_
  simp only [toColoringCNF, CNF.coloringCNF, CNF.relabel, Clause.relabel, CNF.exactlyOne,
    CNF.atLeastOne, CNF.atMostOne, List.map_append, List.map_flatMap, List.map_cons,
    List.map_nil, List.map_map, Function.comp_def, List.flatMap_map,
    List.cons_append, List.nil_append]
  congr 1
  refine List.flatMap_congr fun v _ => ?_
  congr 1
  refine List.flatMap_congr fun c₁ _ => ?_
  rw [List.filter_map, List.map_map]
  congr 1
  refine List.filter_congr fun c₂ _ => ?_
  simp [eq_comm]

/-! ### 3. Perfect matchings (`n = O(|V| + |E|)`, width `3`) -/

/-- Exact-one wire lists for `G.edgeList`: for each distinct vertex `v ∈ G.distinctVertices`,
the positions `i < G.edgeList.length` of edges incident to `v`. -/
@[expose] def perfectMatchingWires (G : Graph) : List (List ℕ) :=
  G.distinctVertices.map fun v =>
    (List.range G.edgeList.length).filter fun i =>
      Graph.incident (G.edgeList.getD i (0, 0)) v

/-- Linear-size sequential exact-one De Morgan gate list and output wire for `G`. -/
@[expose] def perfectMatchingCircuit (G : Graph) : ExactOneCircuitResult :=
  seqExactlyOneAll G.edgeList.length G.perfectMatchingWires

/-- **Width-`3` CNF encoding of perfect matchings** via sequential exact-one De Morgan circuits
and Tseitin compilation: exact clause width `3` and `O(|V| + |E|)` variables and clauses. -/
@[expose] def toPerfectMatchingCNF (G : Graph) : CNF ℕ :=
  tseitinSatCNF [] G.edgeList.length G.perfectMatchingCircuit.gates
    G.perfectMatchingCircuit.outWire

/-- Every clause of `G.toPerfectMatchingCNF` has exact width `3`. -/
theorem length_clause_toPerfectMatchingCNF {G : Graph} {c : Clause ℕ}
    (hc : c ∈ G.toPerfectMatchingCNF) : c.length = 3 :=
  length_of_mem_tseitinSatCNF hc

/-- `G.edgeList` has at most `G.2.length` entries. -/
theorem length_edgeList_le (G : Graph) : G.edgeList.length ≤ G.edges.length :=
  (List.eraseDupsBy_sublist _).length_le.trans List.filter_sublist.length_le

private theorem mem_perfectMatchingWires_lt (G : Graph) :
    ∀ ws ∈ G.perfectMatchingWires, ∀ w ∈ ws, w < G.edgeList.length := by
  intro ws hws w hw
  simp only [perfectMatchingWires, List.mem_map] at hws
  obtain ⟨v, _, rfl⟩ := hws
  exact List.mem_range.mp (List.mem_filter.mp hw).1

/-- Total length of all vertex-incidence lists is at most `2 * G.edgeList.length`, since each
edge contributes to at most two vertex constraints. -/
theorem sum_length_perfectMatchingWires_le (G : Graph) :
    (G.perfectMatchingWires.map List.length).sum ≤ 2 * G.edgeList.length := by
  classical
  have hvars : G.perfectMatchingWires.flatten = G.perfectMatchingInstance.vars := by
    simp only [perfectMatchingWires, perfectMatchingInstance, CSP.vars, List.flatMap_map,
      List.flatten_eq_flatMap, id_eq]
  have hsub : G.perfectMatchingInstance.vars.toFinset ⊆ Finset.range G.edgeList.length := by
    intro i hi
    exact Finset.mem_range.mpr (mem_vars_perfectMatchingInstance.mp (List.mem_toFinset.mp hi))
  rw [← List.length_flatten, hvars]
  exact (CSP.length_vars_le_mul_numVars (Graph.count_vars_perfectMatchingInstance G)).trans
    ((Nat.mul_le_mul_left 2 (Finset.card_le_card hsub)).trans_eq
      (by rw [Finset.card_range]))

/-- Number of gates in `G.perfectMatchingCircuit` is `O(|V| + |E|)`. -/
theorem length_perfectMatchingCircuit_le (G : Graph) :
    G.perfectMatchingCircuit.gates.length ≤
      1 + 4 * G.vertices.toFinset.card + 6 * G.edgeList.length := by
  rw [perfectMatchingCircuit, length_seqExactlyOneAll]
  have hwlen : G.perfectMatchingWires.length = G.vertices.toFinset.card := by
    rw [perfectMatchingWires, List.length_map, Graph.length_distinctVertices]
  have hsum := sum_length_perfectMatchingWires_le G
  omega

/-- Number of clauses of `G.toPerfectMatchingCNF` is linear: `≤ 4 + 12 |V| + 18 |E|`. -/
theorem length_toPerfectMatchingCNF_le (G : Graph) :
    G.toPerfectMatchingCNF.length ≤
      4 + 12 * G.vertices.toFinset.card + 18 * G.edgeList.length := by
  rw [toPerfectMatchingCNF, length_tseitinSatCNF, List.length_nil]
  have h := length_perfectMatchingCircuit_le G
  omega

theorem vars_toPerfectMatchingCNF_subset (G : Graph) :
    G.toPerfectMatchingCNF.vars.toFinset ⊆
      Finset.range (G.edgeList.length + G.perfectMatchingCircuit.gates.length) := by
  have hcode := isCodeFrom_seqExactlyOneAll G.edgeList.length (mem_perfectMatchingWires_lt G)
  have ho := outWire_seqExactlyOneAll_lt G.edgeList.length (mem_perfectMatchingWires_lt G)
  have hpos : 0 < G.edgeList.length + G.perfectMatchingCircuit.gates.length := by
    simp [perfectMatchingCircuit, length_seqExactlyOneAll]
  exact vars_tseitinSatCNF_subset hcode ho hpos

/-- Variable count of `G.toPerfectMatchingCNF` is linear: `≤ 1 + 4 |V| + 7 |E|`. -/
theorem numVars_toPerfectMatchingCNF_le (G : Graph) :
    G.toPerfectMatchingCNF.numVars ≤
      1 + 4 * G.vertices.toFinset.card + 7 * G.edgeList.length := by
  have h1 : G.toPerfectMatchingCNF.numVars ≤
      G.edgeList.length + G.perfectMatchingCircuit.gates.length :=
    (Finset.card_le_card (vars_toPerfectMatchingCNF_subset G)).trans_eq (Finset.card_range _)
  have h2 := length_perfectMatchingCircuit_le G
  omega

/-- Variable count of `G.toPerfectMatchingCNF` in terms of `(encGraph G).length`. -/
theorem numVars_toPerfectMatchingCNF_le_enc (G : Graph) :
    G.toPerfectMatchingCNF.numVars ≤ 7 * (encGraph G).length + 1 := by
  have h1 := numVars_toPerfectMatchingCNF_le G
  have h2 := G.vertices.toFinset_card_le
  have h3 := length_edgeList_le G
  have h4 := Graph.length_vertices_add_length_edges_le_encGraph G
  omega

/-- Explicit bijection between declared-range models of `G.toPerfectMatchingCNF` and perfect
matchings of `G.induced`. -/
noncomputable def perfectMatchingCNFEquiv (G : Graph) :
    {σ : Finset.range (G.edgeList.length + G.perfectMatchingCircuit.gates.length) → Bool //
      G.toPerfectMatchingCNF.eval
        (fun w =>
          if hw : w ∈ Finset.range (G.edgeList.length + G.perfectMatchingCircuit.gates.length) then
            σ ⟨w, hw⟩
          else false) = true} ≃
      {M : G.induced.Subgraph // M.IsPerfectMatching} := by
  have hcode := isCodeFrom_seqExactlyOneAll G.edgeList.length (mem_perfectMatchingWires_lt G)
  have ho := outWire_seqExactlyOneAll_lt G.edgeList.length (mem_perfectMatchingWires_lt G)
  let e1 := (tseitinSatAssignmentEquiv hcode ho).symm
  let e2 : {x : Fin G.edgeList.length → Bool //
        evalOutput (List.ofFn x) G.perfectMatchingCircuit.gates
          G.perfectMatchingCircuit.outWire = true} ≃
      {S : Finset ℕ // (∀ i ∈ S, i < G.edgeList.length) ∧
        ∀ v ∈ G.vertices, ∃! i, i < G.edgeList.length ∧
          Graph.incident (G.edgeList.getD i (0, 0)) v = true ∧ i ∈ S} :=
    { toFun := fun x =>
        ⟨(Finset.univ.filter fun i : Fin G.edgeList.length => x.val i = true).map
            ⟨Fin.val, Fin.val_injective⟩, by
          have hx := x.property
          dsimp only [perfectMatchingCircuit] at hx
          have hev := evalOutput_seqExactlyOneAll (x := List.ofFn x.val)
            (wss := G.perfectMatchingWires)
            (by simpa only [List.length_ofFn] using mem_perfectMatchingWires_lt G)
          simp only [List.length_ofFn] at hev
          rw [hev, List.all_eq_true] at hx
          refine ⟨fun i hi => ?_, fun v hv => ?_⟩
          · obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hi
            exact j.isLt
          · have hv' : v ∈ G.distinctVertices := Graph.mem_distinctVertices.mpr hv
            let ws := (List.range G.edgeList.length).filter fun i =>
              Graph.incident (G.edgeList.getD i (0, 0)) v
            have hws : ws ∈ G.perfectMatchingWires := List.mem_map.mpr ⟨v, hv', rfl⟩
            have hcnt := of_decide_eq_true (hx ws hws)
            rw [List.countP_eq_length_filter, List.filter_filter,
              List.length_filter_range_eq_one_iff] at hcnt
            obtain ⟨i, ⟨hi, hp⟩, huniq⟩ := hcnt
            rw [Bool.and_eq_true, List.getD_ofFn_of_lt x.val hi false] at hp
            refine ⟨i, ⟨hi, hp.2, Finset.mem_map.mpr
              ⟨⟨i, hi⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp.1⟩, rfl⟩⟩, ?_⟩
            intro j ⟨hj, hjinc, hjs⟩
            obtain ⟨j', hj', rfl⟩ := Finset.mem_map.mp hjs
            have hjxt := (Finset.mem_filter.mp hj').2
            refine huniq j'.val ⟨j'.isLt, ?_⟩
            rw [Bool.and_eq_true, List.getD_ofFn_of_lt x.val j'.isLt false]
            exact ⟨hjxt, hjinc⟩⟩
      invFun := fun S => ⟨fun i => decide (i.val ∈ S.val), by
        dsimp only [perfectMatchingCircuit]
        have hev := evalOutput_seqExactlyOneAll
          (x := List.ofFn fun i : Fin G.edgeList.length => decide (i.val ∈ S.val))
          (wss := G.perfectMatchingWires)
          (by simpa only [List.length_ofFn] using mem_perfectMatchingWires_lt G)
        simp only [List.length_ofFn] at hev
        rw [hev, List.all_eq_true]
        intro ws hws
        simp only [perfectMatchingWires, List.mem_map, Graph.mem_distinctVertices] at hws
        obtain ⟨v, hv, rfl⟩ := hws
        rw [decide_eq_true_eq, List.countP_eq_length_filter, List.filter_filter,
          List.length_filter_range_eq_one_iff]
        obtain ⟨i, ⟨hi, hinc, hiS⟩, huniq⟩ := S.property.2 v hv
        refine ⟨i, ⟨hi, ?_⟩, fun j ⟨hj, hjp⟩ => huniq j ⟨hj, ?_⟩⟩
        · rw [Bool.and_eq_true, List.getD_ofFn_of_lt _ hi false, decide_eq_true_eq]
          exact ⟨hiS, hinc⟩
        · rw [Bool.and_eq_true, List.getD_ofFn_of_lt _ hj false, decide_eq_true_eq] at hjp
          exact ⟨hjp.2, hjp.1⟩⟩
      left_inv := fun x => by
        obtain ⟨x, hx⟩ := x
        refine Subtype.ext (funext fun i => ?_)
        cases hxi : x i <;> simp [hxi]
      right_inv := fun S => by
        obtain ⟨S, hS1, hS2⟩ := S
        refine Subtype.ext (Finset.ext fun i => ?_)
        simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
          Function.Embedding.coeFn_mk]
        constructor
        · rintro ⟨j, hj, rfl⟩
          exact decide_eq_true_eq.mp hj
        · intro hi
          exact ⟨⟨i, hS1 i hi⟩, decide_eq_true hi, rfl⟩ }
  exact e1.trans (e2.trans (Graph.perfectMatchingPositionsEquiv G).symm)

/-- **Exact model count of `G.toPerfectMatchingCNF` on `Finset.range (|E| + gates)`**:
equals the number of perfect matchings of `G.induced`. -/
theorem modelCountOn_toPerfectMatchingCNF (G : Graph) :
    G.toPerfectMatchingCNF.modelCountOn
        (Finset.range (G.edgeList.length + G.perfectMatchingCircuit.gates.length)) =
      Nat.card {M : G.induced.Subgraph // M.IsPerfectMatching} := by
  classical
  rw [CNF.modelCountOn, ← Nat.card_eq_finsetCard]
  exact Nat.card_congr ((Equiv.subtypeEquivRight
    (fun _ => by simp only [Finset.mem_filter, Finset.mem_univ, true_and])).trans
    (perfectMatchingCNFEquiv G))

/-- **Exact model count of `G.toPerfectMatchingCNF`** (`modelCount`), preserving the number of
perfect matchings up to unused free wires (and exact equality when every wire occurs). -/
theorem modelCount_toPerfectMatchingCNF_mul (G : Graph) :
    2 ^ ((G.edgeList.length + G.perfectMatchingCircuit.gates.length) -
        G.toPerfectMatchingCNF.numVars) *
      G.toPerfectMatchingCNF.modelCount =
      Nat.card {M : G.induced.Subgraph // M.IsPerfectMatching} := by
  rw [← Finset.card_range (G.edgeList.length + G.perfectMatchingCircuit.gates.length),
    ← CNF.modelCountOn_eq_mul_modelCount G.toPerfectMatchingCNF
      (Finset.range (G.edgeList.length + G.perfectMatchingCircuit.gates.length))
      (vars_toPerfectMatchingCNF_subset G)]
  exact modelCountOn_toPerfectMatchingCNF G

theorem validDeclaredInput_toPerfectMatchingCNF (G : Graph) :
    CNF.validDeclaredInput 3
        (G.edgeList.length + G.perfectMatchingCircuit.gates.length) G.toPerfectMatchingCNF =
      true := by
  rw [CNF.validDeclaredInput_eq_true_iff]
  exact ⟨fun _ hc => (length_clause_toPerfectMatchingCNF hc).le,
    vars_toPerfectMatchingCNF_subset G⟩

/-! ### Polynomial-time certificate for `Graph.toPerfectMatchingCNF` -/

private theorem seqExactlyOneStep_eq_zipIdx (nextWire seen1 seen2 : ℕ) (ws : List ℕ) :
    (seqExactlyOneStep nextWire seen1 seen2 ws).gates =
      ws.zipIdx.flatMap fun p =>
        let nw := nextWire + 3 * p.2
        let s1 := if p.2 = 0 then seen1 else nw - 1
        let s2 := if p.2 = 0 then seen2 else nw - 2
        [(.and, [s1, p.1]), (.or, [s2, nw]), (.or, [s1, p.1])] := by
  induction ws generalizing nextWire seen1 seen2 with
  | nil => rfl
  | cons w ws ih =>
    rw [seqExactlyOneStep]
    dsimp only
    rw [ih (nextWire + 3) (nextWire + 2) (nextWire + 1), List.zipIdx_cons', List.flatMap_cons,
      List.flatMap_map]
    dsimp only [Nat.mul_zero, Nat.add_zero, ↓reduceIte]
    congr 1
    refine List.flatMap_congr fun ⟨u, j⟩ _ => ?_
    dsimp only [Prod.map, id_eq]
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]
    rcases j with _ | k
    · simp only [↓reduceIte, Nat.mul_zero, Nat.add_zero, Nat.zero_add, Nat.mul_one]
      have h1 : nextWire + 3 - 1 = nextWire + 2 := by omega
      have h2 : nextWire + 3 - 2 = nextWire + 1 := by omega
      rw [h1, h2]
    · simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]
      have h0 : nextWire + 3 * (k + 1 + 1) = nextWire + 3 + 3 * (k + 1) := by omega
      rw [h0]

private theorem seen1Wire_seqExactlyOneStep (nextWire seen1 seen2 : ℕ) (ws : List ℕ) :
    (seqExactlyOneStep nextWire seen1 seen2 ws).seen1Wire =
      if ws.length = 0 then seen1
      else nextWire + 3 * ws.length - 1 := by
  induction ws generalizing nextWire seen1 seen2 with
  | nil => rfl
  | cons w ws ih =>
    rw [seqExactlyOneStep, ih]
    rcases ws with _ | ⟨w', ws'⟩
    · simp
    · simp only [List.length_cons, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]
      omega

private theorem seen2Wire_seqExactlyOneStep (nextWire seen1 seen2 : ℕ) (ws : List ℕ) :
    (seqExactlyOneStep nextWire seen1 seen2 ws).seen2Wire =
      if ws.length = 0 then seen2
      else nextWire + 3 * ws.length - 2 := by
  induction ws generalizing nextWire seen1 seen2 with
  | nil => rfl
  | cons w ws ih =>
    rw [seqExactlyOneStep, ih]
    rcases ws with _ | ⟨w', ws'⟩
    · simp
    · simp only [List.length_cons, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]
      omega

private theorem sum_clauseGateCost_take (wss : List (List ℕ)) (i : ℕ) :
    ((wss.take i).map fun u => 3 * u.length + 4).sum =
      3 * (wss.take i).flatten.length + 4 * (wss.take i).length := by
  induction wss.take i with
  | nil => simp
  | cons u us ih =>
    simp only [List.map_cons, List.sum_cons, List.flatten_cons, List.length_append,
      List.length_cons, ih]
    omega

private theorem seqExactlyOneFold_eq_zipIdx (n base acc : ℕ) (wss : List (List ℕ)) :
    (seqExactlyOneFold n base acc wss).gates =
      wss.zipIdx.flatMap (fun p =>
        let off := ((wss.take p.2).map fun u => 3 * u.length + 4).sum
        let curBase := base + off
        let curAcc := if p.2 = 0 then acc else n + curBase - 1
        let cl := seqExactlyOneClause n curBase p.1
        cl.gates ++ [(.and, [curAcc, cl.outWire])]) ∧
      (seqExactlyOneFold n base acc wss).outWire =
        if wss.length = 0 then acc
        else n + base + (wss.map fun u => 3 * u.length + 4).sum - 1 := by
  induction wss generalizing base acc with
  | nil => simp [seqExactlyOneFold]
  | cons ws wss ih =>
    let cl := seqExactlyOneClause n base ws
    let nextAcc := n + base + cl.gates.length
    have hlen : cl.gates.length = 3 * ws.length + 3 := length_seqExactlyOneClause n base ws
    have hnext : base + cl.gates.length + 1 = base + (3 * ws.length + 4) := by omega
    have hacc : nextAcc = n + (base + (3 * ws.length + 4)) - 1 := by omega
    obtain ⟨ih1, ih2⟩ := ih (base + cl.gates.length + 1) nextAcc
    rw [seqExactlyOneFold]
    dsimp only
    refine ⟨?_, ?_⟩
    · rw [ih1, List.zipIdx_cons', List.flatMap_cons, List.flatMap_map]
      dsimp only [List.take_zero, List.map_nil, List.sum_nil, Nat.add_zero, ↓reduceIte, cl]
      congr 1
      refine List.flatMap_congr fun ⟨u, j⟩ _ => ?_
      dsimp only [Prod.map, id_eq]
      simp only [List.take_succ_cons, List.map_cons, List.sum_cons,
        Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]
      have hadd1 : base + (3 * ws.length + 4 +
          ((wss.take j).map fun u => 3 * u.length + 4).sum) =
          base + cl.gates.length + 1 + ((wss.take j).map fun u => 3 * u.length + 4).sum := by
        omega
      rw [hadd1]
      rcases j with _ | k
      · simp only [List.take_zero, List.map_nil, List.sum_nil, Nat.add_zero, ↓reduceIte]
        have ha : nextAcc = n + (base + cl.gates.length + 1) - 1 := by omega
        rw [ha]
      · simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]
        rfl
    · rw [ih2]
      rcases wss with _ | ⟨ws', wss'⟩
      · simp [nextAcc, hlen]
      · simp only [List.length_cons, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
          List.map_cons, List.sum_cons]
        omega

private theorem gateClauses_eq_ite (w : ℕ) (gate : Op × List ℕ) :
    gateClauses w gate =
      let a := gate.2.getD 0 0
      let b := gate.2.getD 1 0
      if gate.1 = .const false then
        [[(w, false), (w, false), (w, false)],
         [(w, false), (w, false), (w, false)],
         [(w, false), (w, false), (w, false)]]
      else if gate.1 = .const true then
        [[(w, true), (w, true), (w, true)],
         [(w, true), (w, true), (w, true)],
         [(w, true), (w, true), (w, true)]]
      else if gate.1 = .not then
        [[(w, true), (a, true), (a, true)],
         [(w, false), (a, false), (a, false)],
         [(w, true), (a, true), (a, true)]]
      else if gate.1 = .and then
        [[(w, false), (a, true), (a, true)],
         [(w, false), (b, true), (b, true)],
         [(w, true), (a, false), (b, false)]]
      else
        [[(w, true), (a, false), (a, false)],
         [(w, true), (b, false), (b, false)],
         [(w, false), (a, true), (b, true)]] := by
  obtain ⟨op, args⟩ := gate
  cases op with
  | const v => cases v <;> rfl
  | not => rfl
  | and => rfl
  | or => rfl

private theorem list_zipIdx_eq_map_finRange {α : Type*} (l : List α) :
    l.zipIdx = (List.finRange l.length).map fun i : Fin l.length => (l[i], i.val) := by
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  simp only [List.length_zipIdx] at h1
  simp [List.getElem_zipIdx]

private theorem tseitinCNF_eq_zipIdx (n : ℕ) (gates : List (Op × List ℕ)) :
    tseitinCNF n gates = gates.zipIdx.flatMap fun p => gateClauses (n + p.2) p.1 := by
  rw [tseitinCNF, list_zipIdx_eq_map_finRange, List.flatMap_map]

private theorem polyTime_perfectMatchingWires :
    ComputableInPolyTime perfectMatchingWires encGraph (encList (encList encUnary)) := by
  have hE := computableInPolyTime_edgeList
  unfold perfectMatchingWires Graph.incident
  fun_prop

private def seqStepClosed (nw s1 s2 : ℕ) (ws : List ℕ) : List (Op × List ℕ) :=
  ws.zipIdx.flatMap fun p =>
    let nw' := nw + 3 * p.2
    let a1 := if p.2 = 0 then s1 else nw' - 1
    let a2 := if p.2 = 0 then s2 else nw' - 2
    [(.and, [a1, p.1]), (.or, [a2, nw']), (.or, [a1, p.1])]

private theorem polyTime_seqStepClosed :
    ComputableInPolyTime
      (fun q : ((ℕ × ℕ) × ℕ) × List ℕ => seqStepClosed q.1.1.1 q.1.1.2 q.1.2 q.2)
      (encPair (encPair (encPair encUnary encUnary) encUnary) (encList encUnary))
      (encList encGate) := by
  let E0 := encPair (encPair (encPair encUnary encUnary) encUnary) (encList encUnary)
  let E := encPair E0 (encPair encUnary encUnary)
  have hq0 := fst E0 (encPair encUnary encUnary)
  have hq1 := snd E0 (encPair encUnary encUnary)
  have hnwU := unary_add.comp (hq0.fst'.fst'.fst'.prod (unary_mul.comp ((const 3).prod hq1.snd')))
  have hzero : ComputableInPolyTime
      (fun q : (((ℕ × ℕ) × ℕ) × List ℕ) × (ℕ × ℕ) => decide (q.2.2 = 0)) E encBool :=
    decide_eq' hq1.snd' (const (encOut := encUnary) 0)
  have ha1 := unary_to_binary.comp
    (ite_decide hzero hq0.fst'.fst'.snd' (unary_sub.comp (hnwU.prod (const 1))))
  have ha2 := unary_to_binary.comp
    (ite_decide hzero hq0.fst'.snd' (unary_sub.comp (hnwU.prod (const 2))))
  have hw := unary_to_binary.comp hq1.fst'
  have hgate (op : Op) {a b : (((ℕ × ℕ) × ℕ) × List ℕ) × (ℕ × ℕ) → ℕ}
      (ha : ComputableInPolyTime a E encNat) (hb : ComputableInPolyTime b E encNat) :
      ComputableInPolyTime (fun q => (op, [a q, b q])) E encGate :=
    (const op).prod (ha.cons' (hb.cons' (const ([] : List ℕ))))
  have hitem : ComputableInPolyTime
      (fun q : (((ℕ × ℕ) × ℕ) × List ℕ) × (ℕ × ℕ) =>
        let nw' := q.1.1.1.1 + 3 * q.2.2
        let a1 := if q.2.2 = 0 then q.1.1.1.2 else nw' - 1
        let a2 := if q.2.2 = 0 then q.1.1.2 else nw' - 2
        ([(.and, [a1, q.2.1]), (.or, [a2, nw']), (.or, [a1, q.2.1])] : List (Op × List ℕ)))
      E (encList encGate) :=
    (hgate .and ha1 hw).cons' ((hgate .or ha2 (unary_to_binary.comp hnwU)).cons'
      ((hgate .or ha1 hw).cons' (const ([] : List (Op × List ℕ)))))
  exact flatMapWithInput ((zipIdx encUnary).comp
    (snd (encPair (encPair encUnary encUnary) encUnary) (encList encUnary))) hitem

private theorem polyTime_seqExactlyOneClause :
    ComputableInPolyTime
      (fun q : (ℕ × ℕ) × List ℕ => (seqExactlyOneClause q.1.1 q.1.2 q.2).gates)
      (encPair (encPair encUnary encUnary) (encList encUnary)) (encList encGate) := by
  have hq := fst (encPair encUnary encUnary) (encList encUnary)
  have hW := snd (encPair encUnary encUnary) (encList encUnary)
  have hWLen := (length_list encUnary).comp hW
  have hNB := unary_add.comp (hq.fst'.prod hq.snd')
  have hNB1 := unary_add.comp (hNB.prod (const 1))
  have hNW := unary_add.comp (hNB1.prod (unary_mul.comp ((const 3).prod hWLen)))
  have hW0 : ComputableInPolyTime (fun q : (ℕ × ℕ) × List ℕ => decide (q.2.length = 0))
      (encPair (encPair encUnary encUnary) (encList encUnary)) encBool :=
    decide_eq' hWLen (const (encOut := encUnary) 0)
  have hseen (off : ℕ) :=
    unary_to_binary.comp (ite_decide hW0 hNB (unary_sub.comp (hNW.prod (const off))))
  have hhead := (listAppend encGate).comp
    ((const ([(.const false, [])] : List (Op × List ℕ))).prod
      (polyTime_seqStepClosed.comp (((hNB1.prod hNB).prod hNB).prod hW)))
  have htail :=
    ((const (encOut := encOp) Op.not).prod ((hseen 2).cons' (const ([] : List ℕ)))).cons'
      (((const (encOut := encOp) Op.and).prod ((hseen 1).cons' ((unary_to_binary.comp hNW).cons'
        (const ([] : List ℕ))))).cons' (const ([] : List (Op × List ℕ))))
  refine ((listAppend encGate).comp (hhead.prod htail)).of_enc_eq fun q =>
    congrArg (encList encGate) ?_
  rw [seqExactlyOneClause]
  dsimp only [Function.comp_apply]
  rw [length_seqExactlyOneStep, seqExactlyOneStep_eq_zipIdx, seqStepClosed,
    seen1Wire_seqExactlyOneStep, seen2Wire_seqExactlyOneStep]

private theorem polyTime_perfectMatchingBlock :
    ComputableInPolyTime
      (fun q : Graph × (List ℕ × ℕ) =>
        let take := q.1.perfectMatchingWires.take q.2.2
        let curBase := 1 + (3 * take.flatten.length + 4 * take.length)
        let curAcc := if q.2.2 = 0 then q.1.edgeList.length else q.1.edgeList.length + curBase - 1
        let cl := seqExactlyOneClause q.1.edgeList.length curBase q.2.1
        cl.gates ++ [(.and, [curAcc, cl.outWire])])
      (encPair encGraph (encPair (encList encUnary) encUnary)) (encList encGate) := by
  have hG := fst encGraph (encPair (encList encUnary) encUnary)
  have hP2 := snd encGraph (encPair (encList encUnary) encUnary)
  have hN := ((length_list (encPair encNat encNat)).comp computableInPolyTime_edgeList).comp hG
  have htake := listTakeWithInput (polyTime_perfectMatchingWires.comp hG) hP2.snd'
  have hbase := unary_add.comp ((const 1).prod (unary_add.comp
    ((unary_mul.comp ((const 3).prod ((length_list encUnary).comp ((flatten encUnary).comp
      htake)))).prod (unary_mul.comp ((const 4).prod ((length_list _).comp htake))))))
  have hidx0 : ComputableInPolyTime (fun q : Graph × (List ℕ × ℕ) => decide (q.2.2 = 0))
      (encPair encGraph (encPair (encList encUnary) encUnary)) encBool :=
    decide_eq' hP2.snd' (const (encOut := encUnary) 0)
  have hNb := unary_add.comp (hN.prod hbase)
  have hacc := unary_to_binary.comp
    (ite_decide hidx0 hN (unary_sub.comp (hNb.prod (const 1))))
  have hout := unary_to_binary.comp (unary_add.comp ((unary_add.comp (hNb.prod
    (unary_mul.comp ((const 3).prod ((length_list encUnary).comp hP2.fst'))))).prod (const 2)))
  refine ((listAppend encGate).comp
    ((polyTime_seqExactlyOneClause.comp ((hN.prod hbase).prod hP2.fst')).prod
      (((const (encOut := encOp) Op.and).prod (hacc.cons' (hout.cons' (const ([] : List ℕ))))).cons'
        (const ([] : List (Op × List ℕ)))))).of_enc_eq fun q => ?_
  dsimp only [Function.comp_apply]
  rw [outWire_seqExactlyOneClause]

private theorem polyTime_perfectMatchingGates :
    ComputableInPolyTime (fun G : Graph => G.perfectMatchingCircuit.gates)
      encGraph (encList encGate) := by
  have hzip := (zipIdx (encList encUnary)).comp polyTime_perfectMatchingWires
  have hfold : ComputableInPolyTime
      (fun G : Graph => (Op.const true, ([] : List ℕ)) ::
        (G.perfectMatchingWires.zipIdx.flatMap fun p =>
          let take := G.perfectMatchingWires.take p.2
          let curBase := 1 + (3 * take.flatten.length + 4 * take.length)
          let curAcc := if p.2 = 0 then G.edgeList.length else G.edgeList.length + curBase - 1
          let cl := seqExactlyOneClause G.edgeList.length curBase p.1
          cl.gates ++ [(.and, [curAcc, cl.outWire])]))
      encGraph (encList encGate) :=
    (const (Op.const true, ([] : List ℕ))).cons'
      (flatMapWithInput hzip polyTime_perfectMatchingBlock)
  refine hfold.of_enc_eq fun G => congrArg (encList encGate) ?_
  rw [perfectMatchingCircuit, seqExactlyOneAll]
  dsimp only
  congr 1
  rw [(seqExactlyOneFold_eq_zipIdx G.edgeList.length 1 G.edgeList.length
    G.perfectMatchingWires).1]
  refine List.flatMap_congr fun p _ => ?_
  rw [sum_clauseGateCost_take]

private theorem polyTime_perfectMatchingOutWire :
    ComputableInPolyTime (fun G : Graph => G.perfectMatchingCircuit.outWire)
      encGraph encUnary := by
  have hN := (length_list (encPair encNat encNat)).comp computableInPolyTime_edgeList
  have hwlen := (length_list (encList encUnary)).comp polyTime_perfectMatchingWires
  have hsumU := unary_add.comp ((unary_mul.comp ((const 3).prod ((length_list encUnary).comp
    ((flatten encUnary).comp polyTime_perfectMatchingWires)))).prod
    (unary_mul.comp ((const 4).prod hwlen)))
  have hw0 : ComputableInPolyTime
      (fun G : Graph => decide (G.perfectMatchingWires.length = 0)) encGraph encBool :=
    decide_eq' hwlen (const (encOut := encUnary) 0)
  refine (ite_decide hw0 hN (unary_sub.comp ((unary_add.comp
    ((unary_add.comp (hN.prod (const 1))).prod hsumU)).prod (const 1)))).of_enc_eq fun G => ?_
  dsimp only [Function.comp_apply]
  rw [perfectMatchingCircuit, seqExactlyOneAll,
    (seqExactlyOneFold_eq_zipIdx G.edgeList.length 1 G.edgeList.length
      G.perfectMatchingWires).2]
  have hsum : (G.perfectMatchingWires.map fun u => 3 * u.length + 4).sum =
      3 * G.perfectMatchingWires.flatten.length + 4 * G.perfectMatchingWires.length := by
    have ht := sum_clauseGateCost_take G.perfectMatchingWires G.perfectMatchingWires.length
    rwa [List.take_length] at ht
  rw [hsum]

private theorem polyTime_gateClauses :
    ComputableInPolyTime (fun p : ℕ × (Op × List ℕ) => gateClauses p.1 p.2)
      (encPair encUnary encGate) (encList (encClause encNat)) := by
  have hOpTag (op : Op) : ComputableInPolyTime
      (fun p : ℕ × (Op × List ℕ) => decide (p.2.1 = op))
      (encPair encUnary encGate) encBool :=
    (of_finite (encIn := encOp) (encOut := encBool) fun x => decide (x = op)).comp
      (snd encUnary encGate).fst'
  have hw : ComputableInPolyTime (fun p : ℕ × (Op × List ℕ) => p.1)
      (encPair encUnary encGate) encNat :=
    unary_to_binary.comp (fst encUnary encGate)
  have hget (i : ℕ) : ComputableInPolyTime (fun p : ℕ × (Op × List ℕ) => p.2.2.getD i 0)
      (encPair encUnary encGate) encNat :=
    listGetD_binary (encA := encNat) (encL := encList encNat) 0 (snd encUnary encGate).snd'
      (const i)
  have ha := hget 0
  have hb := hget 1
  have hcl3 (x y z : ℕ × (Op × List ℕ) → ℕ) (sx sy sz : Bool)
      (hx : ComputableInPolyTime x (encPair encUnary encGate) encNat)
      (hy : ComputableInPolyTime y (encPair encUnary encGate) encNat)
      (hz : ComputableInPolyTime z (encPair encUnary encGate) encNat) :
      ComputableInPolyTime
        (fun p => ([(x p, sx), (y p, sy), (z p, sz)] : Clause ℕ))
        (encPair encUnary encGate) (encClause encNat) :=
    (hx.prod (const sx)).cons' ((hy.prod (const sy)).cons'
      ((hz.prod (const sz)).cons' (const ([] : Clause ℕ))))
  have hcnf3 (c1 c2 c3 : ℕ × (Op × List ℕ) → Clause ℕ)
      (hc1 : ComputableInPolyTime c1 (encPair encUnary encGate) (encClause encNat))
      (hc2 : ComputableInPolyTime c2 (encPair encUnary encGate) (encClause encNat))
      (hc3 : ComputableInPolyTime c3 (encPair encUnary encGate) (encClause encNat)) :
      ComputableInPolyTime (fun p => ([c1 p, c2 p, c3 p] : CNF ℕ))
        (encPair encUnary encGate) (encList (encClause encNat)) :=
    hc1.cons' (hc2.cons' (hc3.cons' (const ([] : CNF ℕ))))
  have hcf := hcnf3 _ _ _ (hcl3 _ _ _ false false false hw hw hw)
    (hcl3 _ _ _ false false false hw hw hw) (hcl3 _ _ _ false false false hw hw hw)
  have hct := hcnf3 _ _ _ (hcl3 _ _ _ true true true hw hw hw)
    (hcl3 _ _ _ true true true hw hw hw) (hcl3 _ _ _ true true true hw hw hw)
  have hcnot := hcnf3 _ _ _ (hcl3 _ _ _ true true true hw ha ha)
    (hcl3 _ _ _ false false false hw ha ha) (hcl3 _ _ _ true true true hw ha ha)
  have hcand := hcnf3 _ _ _ (hcl3 _ _ _ false true true hw ha ha)
    (hcl3 _ _ _ false true true hw hb hb) (hcl3 _ _ _ true false false hw ha hb)
  have hcor := hcnf3 _ _ _ (hcl3 _ _ _ true false false hw ha ha)
    (hcl3 _ _ _ true false false hw hb hb) (hcl3 _ _ _ false true true hw ha hb)
  exact (ite (hOpTag (.const false)) hcf (ite (hOpTag (.const true)) hct
    (ite (hOpTag .not) hcnot (ite (hOpTag .and) hcand hcor)))).of_enc_eq fun p => by
    rw [gateClauses_eq_ite]
    simp only [decide_eq_true_eq]

/-- Constructing `G.toPerfectMatchingCNF` from `encGraph` is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_toPerfectMatchingCNF :
    ComputableInPolyTime toPerfectMatchingCNF encGraph encCNF := by
  have hN := (length_list (encPair encNat encNat)).comp computableInPolyTime_edgeList
  have hP2 := snd encGraph (encPair encGate encUnary)
  have hbody : ComputableInPolyTime
      (fun q : Graph × ((Op × List ℕ) × ℕ) => gateClauses (q.1.edgeList.length + q.2.2) q.2.1)
      (encPair encGraph (encPair encGate encUnary)) (encList (encClause encNat)) :=
    polyTime_gateClauses.comp ((unary_add.comp
      ((hN.comp (fst encGraph (encPair encGate encUnary))).prod hP2.snd')).prod hP2.fst')
  have hts : ComputableInPolyTime
      (fun G : Graph => tseitinCNF G.edgeList.length G.perfectMatchingCircuit.gates)
      encGraph encCNF :=
    (flatMapWithInput
      (f := fun (G : Graph) (p : (Op × List ℕ) × ℕ) => gateClauses (G.edgeList.length + p.2) p.1)
      ((zipIdx encGate).comp polyTime_perfectMatchingGates) hbody).of_enc_eq fun G =>
        congrArg (encList (encClause encNat))
          (tseitinCNF_eq_zipIdx G.edgeList.length G.perfectMatchingCircuit.gates)
  have hoLit :=
    (unary_to_binary.comp polyTime_perfectMatchingOutWire).prod (const (encOut := encBool) true)
  exact ((hoLit.cons' (hoLit.cons' (hoLit.cons' (const ([] : Clause ℕ))))).cons' hts).of_enc_eq
    fun G => congrArg encCNF (by simp [toPerfectMatchingCNF, tseitinSatCNF, unitClause])

end Cslib.Complexity.Graph
