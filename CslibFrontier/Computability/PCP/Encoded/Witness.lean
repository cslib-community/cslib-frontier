/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.Encoded.Amplification.Iteration
public import CslibFrontier.Computability.PCP.Encoded.GapTheorem
public import CslibFrontier.Computability.PCP.Encoded.ThreeSAT
public import CslibFrontier.Computability.PCP.Encoded.Verifier
public import CslibFrontier.Computability.Complexity.Problems.ThreeSAT.Levin
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Pi
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.RotationMap.Family
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Sum
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Finite
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import CslibFrontier.Logics.Propositional.CNF.PolyTime
import CslibFrontier.Logics.Propositional.CNF.ThreeCNF.PolyTime
import CslibFrontier.Tactic.PolyTime
import Mathlib.Tactic.FinCases

/-!
# Polynomial-time witness and labelling compilers for encoded PCP graphs

Every transformation in the executable Dinur–Gap-Amplification pipeline preserves satisfying graph
labellings constructively and in polynomial time:

* **CNF to compact 3-SAT constraint graph (`ofCompactCNFLabels`):** maps a formula `φ : CNF ℕ` and
  a `SAT.npRelation` witness `w` to the vertex labelling of `Graph.ofCompactCNF φ.to3CNF`.
* **Generic and selected assignment-tester composition (`composeLabels`,
  `composeSelectedLabels`):** lifts a vertex labelling through `composeTabulated` /
  `composeSelectedEnumerated` by computing long-code input blocks, auxiliary proof tables, and
  coin opinions in each `(vertices + edges)` owner block.
* **Preprocessing and powering (`powerPreprocessLabels`):** lifts a vertex labelling along
  `endpoint` and `WalkLabels` rotation walks on `preprocessRotation` to `powerPreprocess`.
* **Iterative amplification rounds (`amplifyLabels`, `amplifyIterLabels`):** threads the graph
  and its label list jointly through `amplifyIter` using `ComputableInPolyTime.iterate` against
  the `iterationSize` bound plus linear list-encoding overhead.
* **Bit-string proof packing (`proofOfLabelList`):** packs a label list into consecutive
  fixed-width blocks matching `Graph.proofOfLabels`.

## Main definitions

* `Cslib.PCP.Encoded.ofCompactCNFLabels`: vertex labelling of `Graph.ofCompactCNF φ.to3CNF`.
* `Cslib.PCP.AssignmentTester.Implementation.composeLabels`: generic composition labelling compiler.
* `Cslib.PCP.Encoded.composeSelectedLabels`: selected Hadamard composition labelling compiler.
* `Cslib.PCP.Encoded.Graph.powerPreprocessLabels`: powered preprocessed labelling compiler.
* `Cslib.PCP.Encoded.Graph.amplifyLabels`,
  `Cslib.PCP.Encoded.Graph.amplifyIterLabels`,
  `Cslib.PCP.Encoded.Graph.arithmeticAmplifyLabels`,
  `Cslib.PCP.Encoded.gapGraphLabels`: single-round, iterated, and complete `gapGraph`
  labelling compilers.
* `Cslib.PCP.Encoded.Graph.proofOfLabelList`: list-backed PCP proof packing.

## Main results

* `Cslib.PCP.Encoded.satisfies_ofCompactCNFLabels`,
  `Cslib.PCP.Encoded.isPolyTime_ofCompactCNFLabels`: correctness and efficiency of initial
  3-SAT constraint-graph labellings.
* `Cslib.PCP.AssignmentTester.Implementation.satisfies_composeLabels`,
  `Cslib.PCP.AssignmentTester.Implementation.isPolyTime_composeLabels`: correctness and
  efficiency of generic composition labelling.
* `Cslib.PCP.Encoded.satisfies_composeSelectedLabels`,
  `Cslib.PCP.Encoded.isPolyTime_composeSelectedLabels`: correctness and efficiency of selected
  composition labelling.
* `Cslib.PCP.Encoded.Graph.satisfies_powerPreprocessLabels`,
  `Cslib.PCP.Encoded.Graph.isPolyTime_powerPreprocessLabels`: correctness and efficiency of
  powered preprocessing labelling.
* `Cslib.PCP.Encoded.Graph.satisfies_amplifyLabels`,
  `Cslib.PCP.Encoded.Graph.satisfies_amplifyIterLabels`,
  `Cslib.PCP.Encoded.Graph.isPolyTime_amplifyIterLabels_clog`: correctness and logarithmic-round
  polynomial-time compilation through `amplifyIter`.
* `Cslib.PCP.Encoded.Graph.proofOfLabelList_eq_proofOfLabels`,
  `Cslib.PCP.Encoded.Graph.isPolyTime_proofOfLabelList`: exact agreement with `proofOfLabels`
  and polynomial-time packing.

## References

* [I. Dinur, *The PCP theorem by gap amplification*][Dinur2007]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Chapters 11 and 22][AroraBarak09]
-/

@[expose] public section

namespace Cslib.PCP

open Cslib.Complexity Cslib.Logic.PL Turing.MultiTapeTM ComputableInPolyTime

/-! ### Shared list-indexing lemma -/

private theorem getD_flatMap_range_finRange {β : Type*} {width : ℕ} :
    ∀ (N : ℕ) (f : ℕ → Fin width → β) (d : β) {owner : ℕ}, owner < N → ∀ (k : Fin width),
      ((List.range N).flatMap fun i => (List.finRange width).map (f i)).getD
        (owner * width + k.val) d = f owner k
  | 0, _, _, _, howner, _ => absurd howner (Nat.not_lt_zero _)
  | N + 1, f, d, owner, howner, k => by
    have hlen : ((List.range N).flatMap fun i => (List.finRange width).map (f i)).length =
        N * width := by simp [List.length_flatMap]
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.getD_eq_getElem?_getD]
    rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp howner) with hlt | rfl
    · have hidx : owner * width + k.val < N * width := by nlinarith [k.isLt]
      rw [List.getElem?_append_left (hlen ▸ hidx), ← List.getD_eq_getElem?_getD]
      exact getD_flatMap_range_finRange N f d hlt k
    · rw [List.getElem?_append_right (hlen ▸ Nat.le_add_right _ _), hlen, Nat.add_sub_cancel_left]
      simp

/-! ### Encodings for the normalized alphabet and amplification state -/

namespace Encoded

/-- Default symbol of `SelectedAlphabet`. -/
abbrev defaultSelectedAlphabet : SelectedAlphabet := (false, fun _ => false)

/-- Standard bit-tuple encoding of `SelectedAlphabet`. -/
noncomputable abbrev encSelectedAlphabet : SelectedAlphabet ↪ List Bool :=
  encPair encBool (encPi encBool)

/-- Encoding of the joint normalized graph and vertex-label list state in amplification loops. -/
noncomputable abbrev encAmplifyState :
    Graph (SelectedAlphabet → SelectedAlphabet → Bool) × List SelectedAlphabet ↪ List Bool :=
  encPair (Graph.encoding encConstraintTable) (encList encSelectedAlphabet)

/-! ### SAT witness to `Graph.ofCompactCNF φ.to3CNF` labels -/

/-- Explicit list of vertex labels for `Graph.ofCompactCNF φ.to3CNF` from a formula `φ` and its SAT
certificate `w`: even indices hold compacted variable assignments, odd indices hold clause
literal bits. -/
def ofCompactCNFLabels (φ : CNF ℕ) (w : List Bool) : List (Fin 3 → Bool) :=
  let ψ := φ.to3CNF
  let τ := φ.to3CNFAssignment (SAT.assignment φ w)
  (List.range (2 * (ψ.vars.length + ψ.length))).map fun v =>
    if v % 2 = 0 then
      fun _ => ψ.vars[v / 2]?.elim false τ
    else
      let κ := ψ.getD (v / 2) []
      fun q => κ[q.val]?.elim false fun lit => τ lit.1

/-- The compiled label list matches the declared vertex count of `Graph.ofCompactCNF φ.to3CNF`. -/
@[simp]
theorem length_ofCompactCNFLabels (φ : CNF ℕ) (w : List Bool) :
    (ofCompactCNFLabels φ w).length = (Graph.ofCompactCNF φ.to3CNF).vertices := by
  simp [ofCompactCNFLabels]

/-- Any `SAT.npRelation` witness `w` for `φ` produces a vertex-label list satisfying every edge of
`(Graph.ofCompactCNF φ.to3CNF).toGraph id`. -/
theorem satisfies_ofCompactCNFLabels {φ : CNF ℕ} {w : List Bool}
    (hw : SAT.npRelation.IsWitness φ w)
    (e : Fin (Graph.ofCompactCNF φ.to3CNF).edges.length) :
    ((Graph.ofCompactCNF φ.to3CNF).toGraph id).Satisfies
      (fun v => (ofCompactCNFLabels φ w).getD v (fun _ => false)) e := by
  let ψ := φ.to3CNF
  let τ := φ.to3CNFAssignment (SAT.assignment φ w)
  let τc : ℕ → Bool := fun i => ψ.vars[i]?.elim false τ
  have hceval : ψ.compact.eval τc = true :=
    (CNF.eval_compact ψ τ).trans
      (CNF.eval_to3CNF_to3CNFAssignment (SAT.eval_assignment_of_isWitness hw))
  have hc3 : ∀ c ∈ ψ.compact, c.length ≤ 3 := fun _ hc => by
    obtain ⟨κ, hκ, rfl⟩ := List.mem_map.mp hc
    exact (Clause.length_relabel _ κ).trans_le (CNF.length_le_three_of_mem_to3CNF hκ)
  have hsatMath : ∀ edge,
      (ConstraintGraph.ofCNF ψ.compact).Satisfies
        (ConstraintGraph.cnfLabelling ψ.compact τc) edge := by
    simpa [CNF.countUnsat_eq_zero_iff.mpr hceval, ConstraintGraph.unsatEdges_eq_empty_iff] using
      ConstraintGraph.card_unsatEdges_cnfLabelling_le (φ := ψ.compact) hc3 τc
  have hlabel (u : ℕ ⊕ Fin ψ.compact.length)
      (hu : Graph.cnfVertexNumber u < 2 * (ψ.vars.length + ψ.length)) :
      (ofCompactCNFLabels φ w).getD (Graph.cnfVertexNumber u) (fun _ => false) =
        ConstraintGraph.cnfLabelling ψ.compact τc u := by
    rw [ofCompactCNFLabels, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range hu, Option.map_some, Option.getD_some]
    dsimp only
    rw [show φ.to3CNF = ψ from rfl, show φ.to3CNFAssignment (SAT.assignment φ w) = τ from rfl]
    rcases u with x | j
    · simp only [Graph.cnfVertexNumber, Nat.mul_mod_right, ↓reduceIte,
        Nat.mul_div_right _ (by decide : 0 < 2), ConstraintGraph.cnfLabelling]
      rfl
    · have hj : j.val < ψ.length := by simpa only [CNF.length_compact] using j.isLt
      have hneg : ¬ (2 * j.val + 1) % 2 = 0 := by omega
      have hdiv : (2 * j.val + 1) / 2 = j.val := by omega
      simp only [Graph.cnfVertexNumber, hdiv, hneg, ↓reduceIte, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hj, Option.getD_some]
      funext q
      change ψ[j.val][q.val]?.elim false (fun lit => τ lit.1) =
        ψ.compact[j.val][q.val]?.elim false (fun l => ψ.vars[l.1]?.elim false τ)
      simp only [CNF.compact, CNF.relabel, List.getElem_map, Clause.relabel, List.getElem?_map]
      cases hq : ψ[j.val][q.val]? with
      | none => rfl
      | some lit =>
        have hmemVar : lit.1 ∈ ψ.vars := List.mem_map.mpr
          ⟨lit, List.mem_flatten.mpr ⟨ψ[j.val], List.getElem_mem hj, List.mem_of_getElem? hq⟩, rfl⟩
        simp only [Option.map_some, Option.elim_some, Prod.map_fst]
        rw [@List.getElem?_idxOf _ instBEqOfDecidableEq _ _ _ hmemVar]
        rfl
  have hedge := Graph.wellFormed_ofCompactCNF ψ _ (List.getElem_mem e.isLt)
  change ((Graph.ofCompactCNF ψ).toGraph id).Satisfies
    (fun v => (ofCompactCNFLabels φ w).getD v (fun _ => false)) e
  dsimp only [Graph.ofCompactCNF]
  rw [Graph.toGraph_ofCNF ψ.vars.length ψ.compact]
  set idx := (Graph.ofCNFEnumeration ψ.vars.length ψ.compact).equiv e
  have hgr := (Graph.toGraph_ofCNF ψ.vars.length ψ.compact).symm
  have hsrcIdx : Graph.cnfVertexNumber ((ConstraintGraph.ofCNF ψ.compact).src idx) <
      2 * (ψ.vars.length + ψ.length) :=
    (congrArg (fun g => g.src e) hgr).trans_lt
      (by simpa [Graph.toGraph, Graph.ofCompactCNF, Graph.ofCNF, CNF.length_compact] using hedge.1)
  have hdstIdx : Graph.cnfVertexNumber ((ConstraintGraph.ofCNF ψ.compact).dst idx) <
      2 * (ψ.vars.length + ψ.length) :=
    (congrArg (fun g => g.dst e) hgr).trans_lt
      (by simpa [Graph.toGraph, Graph.ofCompactCNF, Graph.ofCNF, CNF.length_compact] using hedge.2)
  simp only [ConstraintGraph.Satisfies, ConstraintGraph.comap, ConstraintGraph.map]
  change (ConstraintGraph.ofCNF ψ.compact).rel idx
    ((ofCompactCNFLabels φ w).getD
      (Graph.cnfVertexNumber ((ConstraintGraph.ofCNF ψ.compact).src idx)) (fun _ => false))
    ((ofCompactCNFLabels φ w).getD
      (Graph.cnfVertexNumber ((ConstraintGraph.ofCNF ψ.compact).dst idx)) (fun _ => false))
  rw [hlabel _ hsrcIdx, hlabel _ hdstIdx]
  exact hsatMath idx

/-- Compiling `Graph.ofCompactCNF φ.to3CNF` labels from `(φ, w)` runs in polynomial time. -/
theorem isPolyTime_ofCompactCNFLabels :
    ComputableInPolyTime (fun p : CNF ℕ × List Bool => ofCompactCNFLabels p.1 p.2)
      (encPair encCNF encBits) (encList (encPi (Index := Fin 3) encBool)) := by
  let encVar := encSum encNat (encPair encUnary encUnary)
  let encIn := encPair encCNF encBits
  let encStep := encPair encIn encUnary
  have hψ := (CNF.isPolyTime_to3CNF encNat).comp (fst encCNF encBits)
  have hvars := (CNF.computableInPolyTime_vars encVar).comp hψ
  have hcount : ComputableInPolyTime
      (fun p : CNF ℕ × List Bool => 2 * (p.1.to3CNF.vars.length + p.1.to3CNF.length))
      encIn encUnary := by
    have hv := (length_list encVar).comp hvars
    have hc := (length_list (encClause encVar)).comp hψ
    fun_prop
  have hhalf := unary_div' (snd encIn encUnary) (const 2)
  have hvarAt := getElem? (encA := encVar) (encL := encList encVar)
    (hvars.comp (fst encIn encUnary)) hhalf
  have heven := optionElimWithInput
    (body := fun (q : (CNF ℕ × List Bool) × ℕ) v =>
      q.1.1.to3CNFAssignment (SAT.assignment q.1.1 q.1.2) v)
    hvarAt (const false) (computableInPolyTime_to3CNFAssignment.comp
      (((fst encIn encUnary).comp (fst encStep encVar)).prod (snd encStep encVar)))
  have hclause : ComputableInPolyTime
      (fun q : (CNF ℕ × List Bool) × ℕ => q.1.1.to3CNF.getD (q.2 / 2) [])
      encStep (encList (encPair encVar encBool)) :=
    listGetDWithInput (hψ.comp (fst encIn encUnary)) hhalf []
  have hodd := pi fun i : Fin 3 =>
    optionElimWithInput
      (body := fun (q : (CNF ℕ × List Bool) × ℕ) (lit : (ℕ ⊕ ℕ × ℕ) × Bool) =>
        q.1.1.to3CNFAssignment (SAT.assignment q.1.1 q.1.2) lit.1)
      (getElem? (encA := encPair encVar encBool) (encL := encList (encPair encVar encBool))
        hclause (const i.val)) (const false)
      (computableInPolyTime_to3CNFAssignment.comp
        (((fst encIn encUnary).comp (fst encStep (encPair encVar encBool))).prod
          ((fst encVar encBool).comp (snd encStep (encPair encVar encBool)))))
  have hcond : ComputableInPolyTime
      (fun q : (CNF ℕ × List Bool) × ℕ => decide (q.2 % 2 = 0)) encStep encBool := by fun_prop
  unfold ofCompactCNFLabels
  exact mapWithInput (range.comp hcount)
    (ite_decide hcond (pi (Index := Fin 3) fun _ => heven) hodd)

end Encoded

/-! ### Generic and selected assignment-tester composition labels -/

namespace AssignmentTester.Implementation

open Encoded Encoded.Graph

variable {α I P R Q Γ : Type} {width : ℕ}

/-- Compute the composed alphabet label of one slot inside owner block `owner`. -/
def composeSlotLabel (encode : α → I → Γ)
    (aux : (α → α → Bool) → (Fin 2 → α) → P → Γ)
    (query : (α → α → Bool) → R → Q → ((Fin 2 × I) ⊕ P)) (γ : Γ)
    (c : α → α → Bool) (vLabel srcLabel dstLabel : α) : ComposeSlot I P R → Γ × (Q → Γ)
  | .inl r => (encode vLabel r, fun _ => γ)
  | .inr (.inl p) => (aux c ![srcLabel, dstLabel] p, fun _ => γ)
  | .inr (.inr ω) =>
    (γ, fun q => match query c ω q with
      | .inl (b, r) => encode (if b = 0 then srcLabel else dstLabel) r
      | .inr p => aux c ![srcLabel, dstLabel] p)

/-- Lift a vertex-label list `labels` along `impl.compose` / `impl.composeTabulated`. -/
def composeLabels (impl : Implementation α I P R Q Γ) (encode : α → I → Γ)
    (aux : (α → α → Bool) → (Fin 2 → α) → P → Γ) (number : ComposeSlot I P R ≃ Fin width)
    (default : α) (γ : Γ) (g : Graph (α → α → Bool)) (labels : List α) :
    List (Γ × (Q → Γ)) :=
  (List.range (g.vertices + g.edges.length)).flatMap fun owner =>
    let edge := g.edgeAt (fun _ _ => false) owner
    let vLabel := labels.getD owner default
    let srcLabel := labels.getD edge.src default
    let dstLabel := labels.getD edge.dst default
    (List.finRange width).map fun k =>
      composeSlotLabel encode aux impl.query γ edge.constraint vLabel srcLabel dstLabel
        (number.symm k)

/-- The compiled composition label list matches the declared vertex count of `composeTabulated`. -/
@[simp]
theorem length_composeLabels (impl : Implementation α I P R Q Γ) (encode : α → I → Γ)
    (aux : (α → α → Bool) → (Fin 2 → α) → P → Γ) (number : ComposeSlot I P R ≃ Fin width)
    (default : α) (γ : Γ) (g : Graph (α → α → Bool)) (labels : List α) :
    (impl.composeLabels encode aux number default γ g labels).length =
      (g.vertices + g.edges.length) * width := by
  simp [composeLabels, List.length_flatMap]

/-- Any label list satisfying `(g.toGraph id)` lifts to a label list satisfying every edge of
`(impl.composeTabulated number coins queries g).toGraph id`. -/
theorem satisfies_composeLabels (impl : Implementation α I P R Q Γ)
    {T : AssignmentTester α I P R Q Γ} (hreal : impl.Realizes T) (hcomplete : T.IsComplete)
    (encode : α → I → Γ) (hencode : T.encode = encode)
    (aux : (α → α → Bool) → (Fin 2 → α) → P → Γ)
    (haux : ∀ c τ p, T.auxiliary (fun a b => c a b = true) τ p = aux c τ p)
    [BEq Γ] [LawfulBEq Γ] (number : ComposeSlot I P R ≃ Fin width)
    (coins : List R) (queries : List Q)
    (hcoins : coins.Nodup) (hqueries : queries.Nodup)
    (hmemCoins : ∀ ω, ω ∈ coins) (hmemQueries : ∀ q, q ∈ queries)
    (default : α) (γ : Γ) {g : Graph (α → α → Bool)} (hg : g.WellFormed) {labels : List α}
    (hsat : ∀ e, (g.toGraph id).Satisfies (fun v => labels.getD v default) e)
    (defaultOut : Γ × (Q → Γ))
    (e : Fin (impl.composeTabulated number coins queries g).edges.length) :
    ((impl.composeTabulated number coins queries g).toGraph id).Satisfies
      (fun v => (impl.composeLabels encode aux number default γ g labels).getD v defaultOut) e := by
  let L := impl.composeLabels encode aux number default γ g labels
  let σ : ℕ → α := fun v => labels.getD v default
  let G := g.toGraph id
  let A := (T.composeTest G).labellingOf (T.composeProof G σ) γ
  have hslot {owner : ℕ} (howner : owner < g.vertices + g.edges.length)
      (slot : ComposeSlot I P R) :
      L.getD (owner * width + (number slot).val) defaultOut =
        let edge := g.edgeAt (fun _ _ => false) owner
        composeSlotLabel encode aux impl.query γ edge.constraint (σ owner) (σ edge.src) (σ edge.dst)
          slot := by
    simp only [L, σ, composeLabels]
    rw [getD_flatMap_range_finRange (g.vertices + g.edges.length) _ defaultOut howner (number slot)]
    simp only [Equiv.symm_apply_apply]
  have hedge (ed : Fin g.edges.length) : g.edgeAt (fun _ _ => false) ed.val = g.edges[ed.val] := by
    simp [edgeAt, List.getD_eq_getElem?_getD]
  have hends (ed : Fin g.edges.length) :
      (fun b : Fin 2 => σ (G.ends ed b)) = ![σ g.edges[ed.val].src, σ g.edges[ed.val].dst] := by
    funext b
    fin_cases b <;> rfl
  have hl_src (ed : Fin g.edges.length) (ω : R) :
      L.getD (composeVertex number Fin.val (.inr (ed, ω))) defaultOut = A (.inr (ed, ω)) := by
    change L.getD (ed.val * width + (number (.inr (.inr ω))).val) defaultOut = _
    rw [hslot (ed.isLt.trans_le (Nat.le_add_left _ _)) (.inr (.inr ω)), hedge ed]
    simp only [A, LocalTest.labellingOf, composeSlotLabel, Sum.elim_inr]
    congr 1
    funext q
    have hrel : G.rel ed = fun a b => g.edges[ed.val].constraint a b = true := by
      simp [G, toGraph, List.get_eq_getElem]
    change _ = (T.composeProof G σ ∘ testerPos G ed) ((T.test (G.rel ed)).query ω q)
    rw [composeProof_comp_testerPos, hrel, ← hreal.query_eq (g.edges[ed.val]).constraint ω q]
    rcases impl.query (g.edges[ed.val]).constraint ω q with ⟨b, r⟩ | p
    · fin_cases b <;>
        simp [AssignmentTester.honestProof, hencode, G, toGraph, ConstraintGraph.ends]
    · simp only [AssignmentTester.honestProof, Sum.elim_inr, ← hends ed]
      exact (haux (g.edges[ed.val]).constraint _ p).symm
  have hl_dst (ed : Fin g.edges.length) (pos : ((Fin 2 × I) ⊕ P)) :
      L.getD (composeVertex number Fin.val (.inl (testerPos G ed pos))) defaultOut =
        A (.inl (testerPos G ed pos)) := by
    rcases pos with ⟨b, r⟩ | p
    · have hend := hg _ (List.getElem_mem ed.isLt)
      have hown : G.ends ed b < g.vertices + g.edges.length := by
        fin_cases b
        exacts [hend.1.trans_le (Nat.le_add_right _ _), hend.2.trans_le (Nat.le_add_right _ _)]
      change L.getD (G.ends ed b * width + (number (.inl r)).val) defaultOut = _
      rw [hslot hown (.inl r)]
      fin_cases b <;>
        simp [A, LocalTest.labellingOf, composeSlotLabel, AssignmentTester.composeProof,
          testerPos, G, toGraph, ConstraintGraph.ends, hencode]
    · change L.getD (ed.val * width + (number (.inr (.inl p))).val) defaultOut = _
      rw [hslot (ed.isLt.trans_le (Nat.le_add_left _ _)) (.inr (.inl p)), hedge ed]
      simp only [A, LocalTest.labellingOf, composeSlotLabel, Sum.elim_inl,
        AssignmentTester.composeProof, testerPos, Prod.mk.injEq, and_true, ← hends ed]
      exact (haux (g.edges[ed.val]).constraint _ p).symm
  change ((impl.composeTabulated number coins queries g).toGraph id).Satisfies
    (fun v => L.getD v defaultOut) e
  dsimp only [composeTabulated]
  rw [toGraph_mapConstraints]
  set e' : Fin (impl.compose number coins queries g).edges.length :=
    finCongr (length_edges_mapConstraints _ _) e
  change ((impl.compose number coins queries g).toGraph (composeEval impl)).Satisfies
    (fun v => L.getD v defaultOut) e'
  rw [toGraph_compose impl hreal number coins queries g hcoins hqueries hmemCoins hmemQueries]
  set p := (composeEnumeration impl number coins queries g
    hcoins hqueries hmemCoins hmemQueries).equiv e'
  change (T.compose G).rel p
    (L.getD (composeVertex number Fin.val (.inr p.1)) defaultOut)
    (L.getD (composeVertex number Fin.val
      (.inl (testerPos G p.1.1 ((T.test (G.rel p.1.1)).query p.1.2 p.2)))) defaultOut)
  rw [hl_src p.1.1 p.1.2, hl_dst p.1.1]
  exact LocalTest.satisfies_labellingOf
    (passes_composeTest_composeProof hcomplete G (hsat p.1.1) p.1.2)

/-- Generic composition label compilation is polynomial-time for fixed finite alphabets and
slots. -/
theorem isPolyTime_composeLabels [Finite α] [Fintype Q]
    (impl : Implementation α I P R Q Γ) (encode : α → I → Γ)
    (aux : (α → α → Bool) → (Fin 2 → α) → P → Γ) (number : ComposeSlot I P R ≃ Fin width)
    (default : α) (γ : Γ) {Input : Type} {input : Input ↪ List Bool}
    {constraintEncoding : (α → α → Bool) ↪ List Bool} {alphabet : α ↪ List Bool}
    {gammaEncoding : Γ ↪ List Bool} {graph : Input → Graph (α → α → Bool)}
    {labels : Input → List α}
    (hgraph : ComputableInPolyTime graph input (encoding constraintEncoding))
    (hlabels : ComputableInPolyTime labels input (encList alphabet)) :
    ComputableInPolyTime
      (fun x => impl.composeLabels encode aux number default γ (graph x) (labels x))
      input (encList (encPair gammaEncoding (encPi gammaEncoding))) := by
  let _ := Fintype.ofFinite α
  let encOut := encPair gammaEncoding (encPi (Index := Q) gammaEncoding)
  let encTuple := encPair constraintEncoding (encPair alphabet (encPair alphabet alphabet))
  let encState := encPair (encoding constraintEncoding) (encList alphabet)
  have hcount : ComputableInPolyTime
      (fun s : Graph (α → α → Bool) × List α => s.1.vertices + s.1.edges.length)
      encState encUnary := by
    have hs := fst (encoding constraintEncoding) (encList alphabet)
    fun_prop
  have hblock : ComputableInPolyTime
      (fun (c, vLabel, srcLabel, dstLabel) =>
        (List.finRange width).map fun k =>
          composeSlotLabel encode aux impl.query γ c vLabel srcLabel dstLabel (number.symm k))
      encTuple (encList encOut) := .of_finite _
  have hState := fst encState encUnary
  have hg := (fst (encoding constraintEncoding) (encList alphabet)).comp hState
  have hls := (snd (encoding constraintEncoding) (encList alphabet)).comp hState
  have hown := snd encState encUnary
  have hedge := isPolyTime_edgeAt hg hown (fun _ _ => false)
  have hstep := hblock.comp ((Edge.isPolyTime_constraint hedge).prod
    ((listGetDWithInput hls hown default).prod
      ((listGetDWithInput hls (Edge.isPolyTime_src hedge) default).prod
        (listGetDWithInput hls (Edge.isPolyTime_dst hedge) default))))
  have hmain : ComputableInPolyTime
      (fun s : Graph (α → α → Bool) × List α =>
        impl.composeLabels encode aux number default γ s.1 s.2)
      encState (encList encOut) := flatMapWithInput (range.comp hcount) hstep
  exact hmain.comp (hgraph.prod hlabels)

end AssignmentTester.Implementation

namespace Encoded

open Cslib.PCP.HadamardTester

attribute [local instance] HadamardTester.instFinEnumBool HadamardTester.Rand.finEnum
  Graph.SelectedComposeSlot.finEnum

/-- Lift a vertex-label list through `composeSelectedEnumerated`. -/
def composeSelectedLabels {α : Type} [FinEnum α] (default : α)
    (g : Graph (α → α → Bool)) (labels : List α) : List SelectedAlphabet :=
  (SelectedHadamardTester.implementation (α := α)).composeLabels BitString.longCode
    (fun _ σ p => HadamardTester.honestProof σ (.inr p)) FinEnum.equiv default false g labels

/-- The length of `composeSelectedLabels` equals `g.composeSelectedEnumerated.vertices`. -/
@[simp]
theorem length_composeSelectedLabels {α : Type} [FinEnum α] (default : α)
    (g : Graph (α → α → Bool)) (labels : List α) :
    (composeSelectedLabels default g labels).length = g.composeSelectedEnumerated.vertices := by
  rw [composeSelectedLabels, AssignmentTester.Implementation.length_composeLabels,
    Graph.vertices_composeSelectedEnumerated, FinEnum.card_eq_fintypeCard]

/-- Satisfying vertex labels lift to satisfying labels of `g.composeSelectedEnumerated`. -/
theorem satisfies_composeSelectedLabels {α : Type} [FinEnum α] (default : α)
    {g : Graph (α → α → Bool)} (hg : g.WellFormed) {labels : List α}
    (hsat : ∀ e, (g.toGraph id).Satisfies (fun v => labels.getD v default) e)
    (e : Fin g.composeSelectedEnumerated.edges.length) :
    (g.composeSelectedEnumerated.toGraph id).Satisfies
      (fun v => (composeSelectedLabels default g labels).getD v defaultSelectedAlphabet) e :=
  AssignmentTester.Implementation.satisfies_composeLabels
    SelectedHadamardTester.implementation
    SelectedHadamardTester.realizes_implementation
    isComplete_selectedAssignmentTester
    BitString.longCode rfl
    (fun _ σ p => HadamardTester.honestProof σ (.inr p)) (fun _ _ _ => rfl)
    FinEnum.equiv (FinEnum.toList _) (FinEnum.toList _)
    FinEnum.nodup_toList FinEnum.nodup_toList FinEnum.mem_toList FinEnum.mem_toList
    default false hg hsat defaultSelectedAlphabet e

/-- Selected composition label compilation runs in polynomial time. -/
theorem isPolyTime_composeSelectedLabels {α Input : Type} [FinEnum α]
    {input : Input ↪ List Bool} {constraintEncoding : (α → α → Bool) ↪ List Bool}
    {alphabet : α ↪ List Bool} (default : α)
    {graph : Input → Graph (α → α → Bool)} {labels : Input → List α}
    (hgraph : ComputableInPolyTime graph input (Graph.encoding constraintEncoding))
    (hlabels : ComputableInPolyTime labels input (encList alphabet)) :
    ComputableInPolyTime (fun x => composeSelectedLabels default (graph x) (labels x))
      input (encList encSelectedAlphabet) :=
  AssignmentTester.Implementation.isPolyTime_composeLabels
    SelectedHadamardTester.implementation BitString.longCode
    (fun _ σ p => HadamardTester.honestProof σ (.inr p)) FinEnum.equiv default false hgraph hlabels

end Encoded

/-! ### Powering and preprocessing labels, and iterated amplification -/

namespace Encoded.Graph

open Cslib.PCP.HadamardTester ConstraintGraph

variable {C α D : Type}

/-- Lift a vertex-label list `labels` of `g` to truthful walk-opinion labels on
`g.powerPreprocess eval fallback rotate T q walks`. -/
def powerPreprocessLabels (fallback : C) (default : α) (rotate : ℕ × (ℕ × D) → ℕ × D)
    (T : ℕ) (g : Graph C) (labels : List α) : List (PowerAlphabet D α T) :=
  let rot := fun p : Graph C × ((ℕ × Bool) × PreprocessLabel D) =>
    p.1.preprocessRotation fallback rotate p.2
  (List.range (2 * g.edges.length)).map fun u w =>
    let ((nextIdx, nextDir), _) :=
      RotationMap.powRotWithInput rot w.1.val (g, halfEdgeOfNumber u, w.2)
    let edge := g.edgeAt fallback nextIdx
    labels.getD (if nextDir then edge.dst else edge.src) default

/-- The powered label list has one entry per half-edge of `g`. -/
@[simp]
theorem length_powerPreprocessLabels (fallback : C) (default : α)
    (rotate : ℕ × (ℕ × D) → ℕ × D) (T : ℕ) (g : Graph C) (labels : List α) :
    (powerPreprocessLabels fallback default rotate T g labels).length = 2 * g.edges.length := by
  simp [powerPreprocessLabels]

/-- Every preprocessed dart constraint holds on the endpoint pullback of a satisfying vertex
labelling. -/
private theorem satisfies_regularPreprocess (g : Graph C)
    (eval : C → α → α → Bool) (fallback : C) (family : (n : ℕ) → RotationMap (Fin n) D)
    {σ : ℕ → α} (hsat : ∀ e, (g.toGraph eval).Satisfies σ e)
    (dart : (Fin g.edges.length × Bool) × PreprocessLabel D) :
    (g.regularPreprocess eval fallback family).toConstraintGraph.Satisfies
      (σ ∘ (g.toGraph eval).endpoint) dart := by
  classical
  let R := g.regularPreprocess eval fallback family
  rw [RegularConstraintGraph.satisfies_toConstraintGraph_iff]
  change R.rel dart (σ ((g.toGraph eval).endpoint dart.1))
    (σ ((g.toGraph eval).endpoint (R.graph.neighbor dart.1 dart.2)))
  rw [← preprocessRelation_eq_true g eval fallback family dart.1 dart.2]
  rcases dart with ⟨v, ((u | d) | d) | u⟩
  · have hrot : R.graph.neighbor v (.inl (.inl (.inl u))) = (v.1, !v.2) := by
      simpa [R, regularPreprocess, RegularConstraintGraph.addLoops,
        RegularConstraintGraph.addTrivial, RegularConstraintGraph.union,
        RotationMap.neighbor] using neighbor_halfEdgeGraph v.1 v.2 u
    have hsatv := hsat v.1
    simp only [ConstraintGraph.Satisfies, toGraph, List.get_eq_getElem] at hsatv
    rcases v with ⟨e, side⟩
    have hedge : g.edgeAt fallback e.val = g.edges[e.val] := by
      simp [edgeAt, List.getD_eq_getElem?_getD]
    cases side <;>
      simpa only [preprocessRelation, hrot, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
        Bool.not_true, ConstraintGraph.endpoint, toGraph, hedge, List.get_eq_getElem] using hsatv
  · have hrot : R.graph.neighbor v (.inl (.inl (.inr d))) =
        ((g.toGraph eval).cloudGraph (g.cloudFamily eval fallback family)).neighbor v d := rfl
    rw [preprocessRelation, hrot, ConstraintGraph.endpoint_neighbor_cloudGraph]
    exact decide_eq_true rfl
  all_goals simp [preprocessRelation]

/-- Satisfying vertex labels lift to satisfying walk-opinion labels on
`g.powerPreprocess eval fallback rotate T q walks`. -/
theorem satisfies_powerPreprocessLabels [DecidableEq α] (g : Graph C)
    (eval : C → α → α → Bool) (fallback : C) (family : (n : ℕ) → RotationMap (Fin n) D)
    (rotate : ℕ × (ℕ × D) → ℕ × D)
    (hrotate : ∀ n (v : Fin n) d, rotate (n, v.val, d) =
      (((family n).rot (v, d)).1.val, ((family n).rot (v, d)).2))
    (T q : ℕ) [NeZero q] (walks : List (PowerLabel D T q))
    (hwalks : walks.Nodup) (hmem : ∀ d, d ∈ walks)
    (default : α) {labels : List α}
    (hsat : ∀ e, (g.toGraph eval).Satisfies (fun v => labels.getD v default) e)
    (defaultPow : PowerAlphabet D α T)
    (e : Fin (g.powerPreprocess eval fallback rotate T q walks).edges.length) :
    ((g.powerPreprocess eval fallback rotate T q walks).toGraph id).Satisfies
      (fun u => (powerPreprocessLabels fallback default rotate T g labels).getD u defaultPow)
      e := by
  classical
  let σ : ℕ → α := fun v => labels.getD v default
  let σ_prep : (Fin g.edges.length × Bool) → α := σ ∘ (g.toGraph eval).endpoint
  let R := g.regularPreprocess eval fallback family
  have hl (v : Fin g.edges.length × Bool) :
      (powerPreprocessLabels fallback default rotate T g labels).getD
        (halfEdgeNumber (v.1.val, v.2)) defaultPow = R.truthful T σ_prep v := by
    have hlt : halfEdgeNumber (v.1.val, v.2) < 2 * g.edges.length := halfEdgeNumber_lt v.1.isLt
    simp only [powerPreprocessLabels, List.getD_eq_getElem?_getD,
      List.getElem?_map, List.getElem?_range hlt, Option.map_some, Option.getD_some,
      halfEdgeOfNumber_halfEdgeNumber]
    funext w
    rw [RotationMap.powRotWithInput_eq
      (fun p : Graph C × ((ℕ × Bool) × PreprocessLabel D) =>
        p.1.preprocessRotation fallback rotate p.2)
      g R.graph (fun p => (p.1.val, p.2))
      (g.preprocessRotation_eq eval fallback family rotate hrotate) w.1.val v w.2]
    rcases hpair : ((R.graph.pow w.1.val).rot (v, w.2)).1 with ⟨idx, side⟩
    have hedge : g.edgeAt fallback idx.val = g.edges[idx.val] := by
      simp [edgeAt, List.getD_eq_getElem?_getD]
    change labels.getD (if side then (g.edgeAt fallback idx.val).dst else
        (g.edgeAt fallback idx.val).src) default =
      R.truthful T σ_prep v w
    rw [hedge]
    cases side <;> simp [RegularConstraintGraph.truthful, σ_prep, σ, ConstraintGraph.endpoint,
      toGraph, RotationMap.neighbor, hpair]
  change ((g.powerPreprocess eval fallback rotate T q walks).toGraph id).Satisfies
    (fun u => (powerPreprocessLabels fallback default rotate T g labels).getD u defaultPow) e
  rw [toGraph_powerPreprocess g eval fallback family rotate hrotate T q walks hwalks hmem]
  set p := (g.powerPreprocessEnumeration eval fallback rotate T q walks hwalks hmem).equiv e
  change (R.power T q).rel p
    ((powerPreprocessLabels fallback default rotate T g labels).getD
      (halfEdgeNumber (p.1.1.val, p.1.2)) defaultPow)
    ((powerPreprocessLabels fallback default rotate T g labels).getD
      (halfEdgeNumber (((R.graph.killedPow T q).rot p).1.1.val,
        ((R.graph.killedPow T q).rot p).1.2)) defaultPow)
  rw [hl p.1, hl ((R.graph.killedPow T q).rot p).1]
  exact RegularConstraintGraph.satisfies_power_iff.2 fun _ hi =>
    (R.rel_truthful_iff T q σ_prep p hi).2
      (satisfies_regularPreprocess g eval fallback family hsat _)

/-- Powered-preprocessing label compilation runs in polynomial time. -/
theorem isPolyTime_powerPreprocessLabels [Fintype D] [Finite α]
    {Input : Type} {input : Input ↪ List Bool}
    {enc : C ↪ List Bool} {alphabet : α ↪ List Bool} {labelEncoding : D ↪ List Bool}
    {graph : Input → Graph C} {labels : Input → List α} {rotate : ℕ × (ℕ × D) → ℕ × D}
    (hgraph : ComputableInPolyTime graph input (encoding enc))
    (hlabels : ComputableInPolyTime labels input (encList alphabet))
    (hrotate : ComputableInPolyTime rotate
      (encPair encUnary (encPair encUnary labelEncoding)) (encPair encUnary labelEncoding))
    (fallback : C) (default : α) (T : ℕ) :
    ComputableInPolyTime
      (fun x => powerPreprocessLabels fallback default rotate T (graph x) (labels x))
      input (encList (encPi (Index := WalkLabels (PreprocessLabel D) T) alphabet)) := by
  classical
  let _ := Fintype.ofFinite α
  let encState := encPair (encoding enc) (encList alphabet)
  let encDart : PreprocessLabel D ↪ List Bool := encFinite (PreprocessLabel D)
  have hrot := isPolyTime_preprocessRotation (labelEncoding := labelEncoding)
    (fst (encoding enc) (encPair (encPair encUnary encBool) encDart))
    (snd (encoding enc) (encPair (encPair encUnary encBool) encDart)) hrotate fallback
  have hState := fst encState encUnary
  have hg := (fst (encoding enc) (encList alphabet)).comp hState
  have hls := (snd (encoding enc) (encList alphabet)).comp hState
  have hu := snd encState encUnary
  have hpi := pi fun w : WalkLabels (PreprocessLabel D) T => by
    have hpow := ((rotationMap_powRotWithInput hrot w.1.val).comp
      (hg.prod ((isPolyTime_halfEdgeOfNumber.comp hu).prod (const w.2)))).fst'
    have hedge := isPolyTime_edgeAt hg hpow.fst' fallback
    exact listGetDWithInput hls
      (ite hpow.snd' (Edge.isPolyTime_dst hedge) (Edge.isPolyTime_src hedge)) default
  have hrange : ComputableInPolyTime
      (fun s : Graph C × List α => List.range (2 * s.1.edges.length))
      encState (encList encUnary) := by
    have hg₀ := fst (encoding enc) (encList alphabet)
    fun_prop
  have hmain : ComputableInPolyTime
      (fun s : Graph C × List α => powerPreprocessLabels fallback default rotate T s.1 s.2)
      encState (encList (encPi (Index := WalkLabels (PreprocessLabel D) T) alphabet)) :=
    mapWithInput hrange hpi
  exact hmain.comp (hgraph.prod hlabels)

section AmplifyLabels

attribute [local instance] HadamardTester.instFinEnumBool HadamardTester.Rand.finEnum
  SelectedComposeSlot.finEnum

local notation "Constraint" => (SelectedAlphabet → SelectedAlphabet → Bool)

variable [FinEnum D]

/-- Lift a vertex-label list through one normalized amplification round `g.amplify`. -/
def amplifyLabels (fallback : Constraint) (rotate : ℕ × (ℕ × D) → ℕ × D) (T q : ℕ) [NeZero q]
    (g : Graph Constraint) (labels : List SelectedAlphabet) : List SelectedAlphabet :=
  let powered := g.powerPreprocess id fallback rotate T q (FinEnum.toList _)
  let poweredLabels :=
    powerPreprocessLabels fallback defaultSelectedAlphabet rotate T g labels
  composeSelectedLabels (fun _ => defaultSelectedAlphabet) powered poweredLabels

@[simp]
theorem length_amplifyLabels (fallback : Constraint) (rotate : ℕ × (ℕ × D) → ℕ × D)
    (T q : ℕ) [NeZero q] (g : Graph Constraint) (labels : List SelectedAlphabet) :
    (amplifyLabels fallback rotate T q g labels).length =
      (g.amplify id fallback rotate T q).vertices := by
  dsimp only [amplifyLabels, amplify]
  exact length_composeSelectedLabels _ _ _

/-- One round of `amplify` preserves satisfaction of explicit label lists. -/
theorem satisfies_amplifyLabels (fallback : Constraint)
    (family : (n : ℕ) → RotationMap (Fin n) D) (rotate : ℕ × (ℕ × D) → ℕ × D)
    (hrotate : ∀ n (v : Fin n) d, rotate (n, v.val, d) =
      (((family n).rot (v, d)).1.val, ((family n).rot (v, d)).2))
    (T q : ℕ) [NeZero q] {g : Graph Constraint} {labels : List SelectedAlphabet}
    (hsat : ∀ e, (g.toGraph id).Satisfies (fun v => labels.getD v defaultSelectedAlphabet) e)
    (e : Fin (g.amplify id fallback rotate T q).edges.length) :
    ((g.amplify id fallback rotate T q).toGraph id).Satisfies
      (fun v => (amplifyLabels fallback rotate T q g labels).getD v defaultSelectedAlphabet)
      e := by
  have hwfPow := g.wellFormed_powerPreprocess id fallback family rotate hrotate T q
    (FinEnum.toList _)
  have hsatPow := satisfies_powerPreprocessLabels g id fallback family rotate hrotate T q
    (FinEnum.toList _) FinEnum.nodup_toList FinEnum.mem_toList defaultSelectedAlphabet hsat
    (fun _ => defaultSelectedAlphabet)
  exact satisfies_composeSelectedLabels (fun _ => defaultSelectedAlphabet) hwfPow hsatPow e

/-- Joint graph-and-label step for `amplifyIter`. -/
def amplifyIterStep (fallback : Constraint) (rotate : ℕ × (ℕ × D) → ℕ × D)
    (T q : ℕ) [NeZero q] :
    Graph Constraint × List SelectedAlphabet → Graph Constraint × List SelectedAlphabet
  | (g, labels) =>
    (g.amplify id fallback rotate T q, amplifyLabels fallback rotate T q g labels)

/-- Compile a vertex-label list through `k` rounds of `amplifyIter`. -/
def amplifyIterLabels (fallback : Constraint) (rotate : ℕ × (ℕ × D) → ℕ × D)
    (T q : ℕ) [NeZero q] (k : ℕ) (g : Graph Constraint) (labels : List SelectedAlphabet) :
    List SelectedAlphabet :=
  ((amplifyIterStep fallback rotate T q)^[k] (g, labels)).2

private theorem fst_amplifyIterStep (fallback : Constraint) (rotate : ℕ × (ℕ × D) → ℕ × D)
    (T q : ℕ) [NeZero q] (k : ℕ) (g : Graph Constraint) (labels : List SelectedAlphabet) :
    ((amplifyIterStep fallback rotate T q)^[k] (g, labels)).1 =
      amplifyIter fallback rotate T q k g := by
  rw [amplifyIter]
  induction k generalizing g labels with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    exact ih (g.amplify id fallback rotate T q) (amplifyLabels fallback rotate T q g labels)

@[simp]
theorem length_amplifyIterLabels (fallback : Constraint) (rotate : ℕ × (ℕ × D) → ℕ × D)
    (T q : ℕ) [NeZero q] (k : ℕ) {g : Graph Constraint} {labels : List SelectedAlphabet}
    (hlen : labels.length = g.vertices) :
    (amplifyIterLabels fallback rotate T q k g labels).length =
      (amplifyIter fallback rotate T q k g).vertices := by
  rw [amplifyIterLabels, amplifyIter]
  induction k generalizing g labels with
  | zero => exact hlen
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    exact ih (length_amplifyLabels fallback rotate T q g labels)

/-- Iterated normalized amplification rounds preserve satisfaction of explicit label lists. -/
theorem satisfies_amplifyIterLabels (fallback : Constraint)
    (family : (n : ℕ) → RotationMap (Fin n) D) (rotate : ℕ × (ℕ × D) → ℕ × D)
    (hrotate : ∀ n (v : Fin n) d, rotate (n, v.val, d) =
      (((family n).rot (v, d)).1.val, ((family n).rot (v, d)).2))
    (T q : ℕ) [NeZero q] (k : ℕ) {g : Graph Constraint} {labels : List SelectedAlphabet}
    (hsat : ∀ e, (g.toGraph id).Satisfies (fun v => labels.getD v defaultSelectedAlphabet) e)
    (e : Fin (amplifyIter fallback rotate T q k g).edges.length) :
    ((amplifyIter fallback rotate T q k g).toGraph id).Satisfies
      (fun v => (amplifyIterLabels fallback rotate T q k g labels).getD v defaultSelectedAlphabet)
      e := by
  revert e
  unfold amplifyIter amplifyIterLabels
  induction k generalizing g labels with
  | zero => exact hsat
  | succ k ih =>
    simp only [Function.iterate_succ_apply]
    exact @ih (g.amplify id fallback rotate T q)
      (amplifyLabels fallback rotate T q g labels)
      (satisfies_amplifyLabels fallback family rotate hrotate T q hsat)

private theorem polyBounded_amplifyStateBound {Input : Type} {input : Input ↪ List Bool}
    {graph : Input → Graph Constraint}
    (hgraph : ComputableInPolyTime graph input (encoding encConstraintTable))
    (factor descriptorBound : ℕ) :
    PolyBounded (fun x => (input x).length)
      (fun x => 2 * iterationSize factor descriptorBound (Nat.clog 2 (graph x).edges.length)
        (graph x) + 1 + 43 * (max factor 1 ^ Nat.clog 2 (graph x).edges.length *
          ((graph x).vertices + (graph x).edges.length))) := by
  apply ComputableInPolyTime.polyBounded
  unfold iterationSize
  fun_prop

private theorem length_encSelectedAlphabet (a : SelectedAlphabet) :
    (encSelectedAlphabet a).length ≤ 21 := by
  have hpi : (encPi (Index := Fin 6) encBool a.2).length ≤ 6 * (2 * 1 + 1) :=
    length_encPi_le encBool a.2 fun _ => by simp
  simp only [encSelectedAlphabet, length_encPair, encBool_apply, List.length_singleton]
  omega

/-- Iterating normalized label compilation for logarithmically many rounds runs in polynomial
time. -/
theorem isPolyTime_amplifyIterLabels_clog {Input : Type} {input : Input ↪ List Bool}
    {graph : Input → Graph Constraint} {labels : Input → List SelectedAlphabet}
    {labelEncoding : D ↪ List Bool}
    (hgraph : ComputableInPolyTime graph input (encoding encConstraintTable))
    (hlabels : ComputableInPolyTime labels input (encList encSelectedAlphabet))
    (hwellFormed : ∀ x, (graph x).WellFormed)
    (hlabelLen : ∀ x, (labels x).length = (graph x).vertices)
    (family : (n : ℕ) → RotationMap (Fin n) D) (rotate : ℕ × (ℕ × D) → ℕ × D)
    (hrotate : ∀ n (v : Fin n) d, rotate (n, v.val, d) =
      (((family n).rot (v, d)).1.val, ((family n).rot (v, d)).2))
    (hcost : ComputableInPolyTime rotate
      (encPair encUnary (encPair encUnary labelEncoding)) (encPair encUnary labelEncoding))
    (fallback : Constraint) (T q : ℕ) [NeZero q] :
    ComputableInPolyTime
      (fun x => amplifyIterLabels fallback rotate T q
        (Nat.clog 2 (graph x).edges.length) (graph x) (labels x))
      input (encList encSelectedAlphabet) := by
  let walks := Fintype.card (PowerLabel D T q)
  let factor :=
    (2 + 2 * walks) * Fintype.card (SelectedComposeSlot (PowerAlphabet D SelectedAlphabet T)) +
      2 * walks * Fintype.card (Fin 5 × Rand (PowerAlphabet D SelectedAlphabet T)) * 6
  let descriptorBound := Fintype.card SelectedAlphabet * (6 * Fintype.card SelectedAlphabet + 1)
  have hgrowth (g : Graph Constraint) :
      (g.amplify id fallback rotate T q).vertices +
        (g.amplify id fallback rotate T q).edges.length ≤
          factor * (g.vertices + g.edges.length) := by
    calc _ = factor * g.edges.length := by
           simp only [vertices_amplify, length_edges_amplify, factor, walks,
             Fintype.card_eq_nat_card]
           ring
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.le_add_left _ _)
  have hconv : ComputableInPolyTime (id : Constraint → Constraint)
      (encPi (encPi encBool)) encConstraintTable := .of_finite _
  have heval' : ComputableInPolyTime
      (fun p : Constraint × (SelectedAlphabet × SelectedAlphabet) => p.1 p.2.1 p.2.2)
      (encPair (encPi (encPi encBool)) (encPair encSelectedAlphabet encSelectedAlphabet))
      encBool := by
    exact (isPolyTime_constraintTableEval encSelectedAlphabet).comp
      ((hconv.comp (fst _ _)).prod (snd _ _))
  have hfstEnc := fst (encoding (encConstraintTable (α := SelectedAlphabet)))
    (encList encSelectedAlphabet)
  have hsndEnc := snd (encoding (encConstraintTable (α := SelectedAlphabet)))
    (encList encSelectedAlphabet)
  have hamplify := isPolyTime_amplify (input := encAmplifyState) (enc := encConstraintTable)
    (alphabet := encSelectedAlphabet) (labelEncoding := labelEncoding)
    (graph := Prod.fst) (eval := id) (rotate := rotate) hfstEnc hcost heval' fallback T q
  have hpow := isPolyTime_powerPreprocess (output := encConstraintTable) (eval := id)
    hfstEnc hcost heval' fallback T q (FinEnum.toList (PowerLabel D T q))
  have hpowLabels := isPolyTime_powerPreprocessLabels (alphabet := encSelectedAlphabet)
    (labelEncoding := labelEncoding) hfstEnc hsndEnc hcost fallback defaultSelectedAlphabet T
  have hstep : ComputableInPolyTime (amplifyIterStep fallback rotate T q)
      encAmplifyState encAmplifyState :=
    hamplify.prod (isPolyTime_composeSelectedLabels (fun _ => defaultSelectedAlphabet)
      hpow hpowLabels)
  have hiter := iterate
    (show ComputableInPolyTime (fun x => Nat.clog 2 (graph x).edges.length) input encUnary by
      fun_prop)
    (hgraph.prod hlabels) hstep (polyBounded_amplifyStateBound hgraph factor descriptorBound)
    fun x i hi => by
      have hfst : ((amplifyIterStep fallback rotate T q)^[i] (graph x, labels x)).1 =
          (amplify id fallback rotate T q)^[i] (graph x) := by
        simpa [amplifyIter] using fst_amplifyIterStep fallback rotate T q i (graph x) (labels x)
      have hgr := iterate_length_encoding_le (valid := WellFormed) factor descriptorBound
        (fun g _ => g.wellFormed_amplify id fallback family rotate hrotate T q)
        (fun _ h => h) (fun _ _ edge _ => length_constraintTable_le edge.constraint)
        (fun g _ => hgrowth g) (hwellFormed x) hi
      have hsz_bound : ∀ m, ((amplify id fallback rotate T q)^[m] (graph x)).vertices +
          ((amplify id fallback rotate T q)^[m] (graph x)).edges.length ≤
          max factor 1 ^ m * ((graph x).vertices + (graph x).edges.length) := by
        intro m
        induction m with
        | zero => simp
        | succ m ih =>
          rw [Function.iterate_succ_apply', pow_succ', mul_assoc]
          exact (hgrowth _).trans (Nat.mul_le_mul (Nat.le_max_left _ _) ih)
      have hl_enc :
          (encList encSelectedAlphabet
            ((amplifyIterStep fallback rotate T q)^[i] (graph x, labels x)).2).length ≤
            43 * (max factor 1 ^ Nat.clog 2 (graph x).edges.length *
              ((graph x).vertices + (graph x).edges.length)) := by
        refine (length_encList_le encSelectedAlphabet _ fun a _ =>
          length_encSelectedAlphabet a).trans ?_
        change (amplifyIterLabels fallback rotate T q i (graph x) (labels x)).length *
          (2 * 21 + 1) ≤ _
        rw [length_amplifyIterLabels fallback rotate T q i (hlabelLen x), amplifyIter]
        calc ((amplify id fallback rotate T q)^[i] (graph x)).vertices * (2 * 21 + 1)
            ≤ (max factor 1 ^ i * ((graph x).vertices + (graph x).edges.length)) * 43 :=
              Nat.mul_le_mul_right 43 ((Nat.le_add_right _ _).trans (hsz_bound i))
          _ ≤ (max factor 1 ^ Nat.clog 2 (graph x).edges.length *
              ((graph x).vertices + (graph x).edges.length)) * 43 :=
              Nat.mul_le_mul_right 43 (Nat.mul_le_mul_right _
                (Nat.pow_le_pow_right (Nat.le_max_right _ _) hi))
          _ = _ := by ring
      rw [← hfst] at hgr
      simp only [length_encPair]
      omega
  unfold amplifyIterLabels
  exact hsndEnc.comp hiter

end AmplifyLabels

/-! ### Concrete arithmetic amplification and `gapGraph` witness compilation -/

section ArithmeticAmplifyLabels

/-- Local `FinEnum` instance for `ZMod 257` used during `arithmeticAmplify` witness compilation. -/
local instance instFinEnumZMod257Witness : FinEnum (ZMod 257) :=
  FinEnum.ofEquiv (Fin 257) (ZMod.finEquiv 257).toEquiv.symm

attribute [local instance] HadamardTester.instFinEnumBool
  Cslib.PCP.HadamardTester.Rand.finEnum SelectedComposeSlot.finEnum

open ConstraintGraph.Amplification.Arithmetic

local notation "Constraint" => (SelectedAlphabet → SelectedAlphabet → Bool)

/-- Lift vertex labels of `g` through the concrete `arithmeticAmplify` pipeline. -/
def arithmeticAmplifyLabels (g : Graph Constraint) (labels : List SelectedAlphabet) :
    List SelectedAlphabet :=
  amplifyIterLabels (fun _ _ => true) RotationMap.arithmeticExpanderRotate walkLength killRate
    (Nat.clog 2 g.edges.length) g labels

@[simp]
theorem length_arithmeticAmplifyLabels {g : Graph Constraint} {labels : List SelectedAlphabet}
    (hlen : labels.length = g.vertices) :
    (arithmeticAmplifyLabels g labels).length = g.arithmeticAmplify.vertices := by
  unfold arithmeticAmplifyLabels arithmeticAmplify
  exact length_amplifyIterLabels (fun _ _ => true) RotationMap.arithmeticExpanderRotate walkLength
    killRate (Nat.clog 2 g.edges.length) hlen

/-- Concrete arithmetic amplification preserves satisfaction of explicit label lists. -/
theorem satisfies_arithmeticAmplifyLabels {g : Graph Constraint} {labels : List SelectedAlphabet}
    (hsat : ∀ e, (g.toGraph id).Satisfies (fun v => labels.getD v defaultSelectedAlphabet) e)
    (e : Fin g.arithmeticAmplify.edges.length) :
    (g.arithmeticAmplify.toGraph id).Satisfies
      (fun v => (arithmeticAmplifyLabels g labels).getD v defaultSelectedAlphabet) e := by
  unfold arithmeticAmplify at e ⊢
  unfold arithmeticAmplifyLabels
  exact satisfies_amplifyIterLabels (fun _ _ => true) RotationMap.arithmeticExpander
    RotationMap.arithmeticExpanderRotate RotationMap.arithmeticExpanderRotate_eq
    walkLength killRate (Nat.clog 2 g.edges.length) hsat e

/-- Concrete arithmetic label compilation runs in polynomial time. -/
@[fun_prop]
theorem isPolyTime_arithmeticAmplifyLabels {Input : Type} {input : Input ↪ List Bool}
    {graph : Input → Graph Constraint} {labels : Input → List SelectedAlphabet}
    (hgraph : ComputableInPolyTime graph input (encoding encConstraintTable))
    (hlabels : ComputableInPolyTime labels input (encList encSelectedAlphabet))
    (hwellFormed : ∀ x, (graph x).WellFormed)
    (hlabelLen : ∀ x, (labels x).length = (graph x).vertices) :
    ComputableInPolyTime (fun x => arithmeticAmplifyLabels (graph x) (labels x))
      input (encList encSelectedAlphabet) := by
  have hcost := _root_.Cslib.RotationMap.polytime_arithmeticExpanderRotate
    (encFinEnum (RotationMap.AffinePlaneFamilyLabel (ZMod 257) 257))
  exact isPolyTime_amplifyIterLabels_clog hgraph hlabels hwellFormed hlabelLen
    RotationMap.arithmeticExpander RotationMap.arithmeticExpanderRotate
    RotationMap.arithmeticExpanderRotate_eq (by fun_prop)
    (fun _ _ => true) walkLength killRate

end ArithmeticAmplifyLabels

/-! ### Packing a label list into a binary PCP proof -/

/-- Pack a vertex-label list into consecutive `width`-bit proof blocks. -/
def proofOfLabelList {α : Type} {width : ℕ} (encode : α → Fin width → Bool)
    (labels : List α) : List Bool :=
  labels.flatMap fun a => List.ofFn (encode a)

/-- When `labels.length = vertices`, packing `labels` equals `proofOfLabels`. -/
theorem proofOfLabelList_eq_proofOfLabels {α : Type} {width : ℕ}
    (encode : α → Fin width → Bool) (default : α) (labels : List α) :
    proofOfLabelList encode labels =
      proofOfLabels width labels.length encode (fun v => labels.getD v default) := by
  rw [proofOfLabelList, proofOfLabels, BitString.ofFn_blocksEquiv_symm, List.flatMap_def]
  congr 1
  symm
  refine List.ext_getElem (by simp) fun i hi₁ _ => ?_
  simp [List.getD_eq_getElem?_getD]

/-- Bit-packing a list of labels from a fixed finite alphabet runs in polynomial time. -/
theorem isPolyTime_proofOfLabelList {α Input : Type} [Finite α] {width : ℕ}
    {input : Input ↪ List Bool} {alphabet : α ↪ List Bool}
    (encode : α → Fin width → Bool) {labels : Input → List α}
    (hlabels : ComputableInPolyTime labels input (encList alphabet)) :
    ComputableInPolyTime (fun x => proofOfLabelList encode (labels x)) input encBits := by
  have henc : ComputableInPolyTime (fun a : α => List.ofFn (encode a)) alphabet encBits :=
    .of_finite _
  unfold proofOfLabelList
  exact ComputableInPolyTime.flatMapToBitsWithInput hlabels
    (henc.comp (ComputableInPolyTime.snd input alphabet))

end Encoded.Graph

namespace Encoded

open Cslib.Logic.PL Turing.MultiTapeTM

attribute [local instance] HadamardTester.instFinEnumBool

/-- Compile a `SAT.npRelation` witness `w` for CNF formula `φ` into vertex labels of
`gapGraph φ`. -/
def gapGraphLabels (φ : CNF ℕ) (w : List Bool) : List SelectedAlphabet :=
  Graph.arithmeticAmplifyLabels (Graph.ofCompactCNF φ.to3CNF).composeSelectedEnumerated
    (composeSelectedLabels (fun _ => false) (Graph.ofCompactCNF φ.to3CNF)
      (ofCompactCNFLabels φ w))

/-- The compiled `gapGraphLabels` list matches `(gapGraph φ).vertices`. -/
@[simp]
theorem length_gapGraphLabels (φ : CNF ℕ) (w : List Bool) :
    (gapGraphLabels φ w).length = (gapGraph φ).vertices := by
  rw [gapGraphLabels, gapGraph]
  exact Graph.length_arithmeticAmplifyLabels (length_composeSelectedLabels _ _ _)

/-- A `SAT.npRelation` witness compiles to satisfying vertex labels for `gapGraph φ`. -/
theorem satisfies_gapGraphLabels {φ : CNF ℕ} {w : List Bool}
    (hw : SAT.npRelation.IsWitness φ w) (e : Fin (gapGraph φ).edges.length) :
    ((gapGraph φ).toGraph id).Satisfies
      (fun v => (gapGraphLabels φ w).getD v defaultSelectedAlphabet) e := by
  rw [gapGraphLabels]
  unfold gapGraph at e ⊢
  exact Graph.satisfies_arithmeticAmplifyLabels
    (satisfies_composeSelectedLabels (fun _ => false)
      (Graph.wellFormed_ofCompactCNF φ.to3CNF)
      (satisfies_ofCompactCNFLabels hw)) e

/-- Compiling `gapGraphLabels` from a polynomial-time CNF formula and SAT witness runs in
polynomial time. -/
@[fun_prop]
theorem isPolyTime_gapGraphLabels {Input : Type} {input : Input ↪ List Bool}
    {formula : Input → CNF ℕ} {witness : Input → List Bool}
    (hformula : ComputableInPolyTime formula input encCNF)
    (hwitness : ComputableInPolyTime witness input encBits) :
    ComputableInPolyTime (fun x => gapGraphLabels (formula x) (witness x))
      input (encList encSelectedAlphabet) := by
  have h3 := Graph.isPolyTime_composeSelectedEnumerated
    (Graph.isPolyTime_ofCompactCNF ((CNF.isPolyTime_to3CNF encNat).comp hformula))
  have hl := isPolyTime_composeSelectedLabels (fun _ => false)
    (Graph.isPolyTime_ofCompactCNF ((CNF.isPolyTime_to3CNF encNat).comp hformula))
    (isPolyTime_ofCompactCNFLabels.comp (hformula.prod hwitness))
  exact Graph.isPolyTime_arithmeticAmplifyLabels h3 hl
    (fun x => (Graph.wellFormed_ofCompactCNF (formula x).to3CNF).composeSelectedEnumerated)
    (fun x => by simp)

end Encoded

end Cslib.PCP
