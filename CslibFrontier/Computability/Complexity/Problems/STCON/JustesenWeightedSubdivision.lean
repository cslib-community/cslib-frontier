/-
Copyright (c) 2026 Christian Reitwiessner, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.STCON.WeightedSubdivisionSpace
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Justesen
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.JustesenBit
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.NatSize
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Composition.Recompute
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Words

/-!
# Justesen-weighted subdivision queries for STCON

The callback evaluates the actual Justesen code bit from a retained field context, then
uses the existing retained-rank weight and same-input layered adjacency. Its seed width
comes from the binary exclusive rank limit, so even an arbitrary encoded request cannot
request more seed positions than the encoded context can pay for. On initialized requests,
the limit is a power of two and this width is exactly the number of Justesen code bits.
The context initializer combines the native seed-search and field routines on the same
original word. A valid binary rank fits in the same logarithmic encoded-length budget.
The flat entry uses the chain bound retained in that context. For initialized contexts and
valid IDs, the decoded reply is available at the common clock three.
-/

public section

namespace Cslib.Complexity.STCON

open Cslib.Code.JustesenFamily Cslib.Reachability.Hoza Cslib.LayeredDigraph.Subdivision
open _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.MultiTapeTM.ComputableInSpace
open _root_.Turing.MultiTapeNTM.ConfigurationGraph _root_.Turing.QueryMachine.Subdivision

variable {k : ℕ} {State : Type} [Fintype State]

/-- The retained graph parameters, Justesen field context and candidate rank for an edge query. -/
structure JustesenSubdivisionContext where
  /-- Graph parameters and the exclusive rank limit. -/
  parameters : SeedSearchParameters
  /-- Field data shared by all code-bit requests. -/
  field : FieldContext
  /-- The current candidate rank in binary. -/
  rank : ℕ

/-- Framed search parameters and field context, followed by the binary candidate rank. -/
enc_structure encJustesenSubdivisionContext : JustesenSubdivisionContext where
  parameters : encSeedSearchParameters, field : encFieldContext, rank : encNat

/-- Project the retained subdivision size within the context's workspace budget. -/
theorem encJustesenSubdivisionContext_subdivision_budget
    {α : Type} {encIn : α ↪ List Bool} {budget : α → ℕ}
    {ctx : α → JustesenSubdivisionContext}
    (hctx : ComputableInSpace ctx encIn encJustesenSubdivisionContext budget) :
    ComputableInSpace (fun a => (ctx a).parameters.search.subdivision)
      encIn encSubdivisionSize budget :=
  encSeedSearchSize_subdivision_budget
    (encSeedSearchParameters_search_budget (encJustesenSubdivisionContext_parameters_budget hctx))

/-- Initialize the context for weighted adjacency from the original word and candidate rank. -/
@[expose] noncomputable def configurationJustesenSubdivisionContext
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) (w : List Bool) (rank : ℕ) :
    JustesenSubdivisionContext :=
  ⟨configurationSeedSearchParameters ntm c w, configurationFieldContext ntm c w, rank⟩

/-- Logarithmic-space producers of the original word and binary rank yield a native
initializer for the complete weighted-adjacency context. -/
theorem configurationJustesenSubdivisionContext_inLogSpace
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) {α : Type} {enc : α ↪ List Bool}
    {word : α → List Bool} {rank : α → ℕ}
    (hword : ComputableInLogSpace word enc encBits)
    (hrank : ComputableInLogSpace rank enc encNat) :
    ComputableInLogSpace (fun a => configurationJustesenSubdivisionContext ntm c (word a) (rank a))
      enc encJustesenSubdivisionContext :=
  (((configurationSeedSearchParameters_inLogSpace ntm c).comp hword).pair
    (((configurationFieldContext_inLogSpace ntm c).comp hword).pair hrank)).congr fun _ => rfl

/-- A valid rank and the initialized parameter and field encodings together fit in logarithmic
length in the original STCON word. -/
theorem length_configurationJustesenSubdivisionContext_le_log
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) :
    ∃ C, ∀ (w : List Bool) (rank : ℕ),
      rank < (configurationSeedSearchParameters ntm c w).search.seedLimit →
      (encJustesenSubdivisionContext (configurationJustesenSubdivisionContext ntm c w rank)).length
        ≤ C * (Nat.log2 w.length + 1) := by
  obtain ⟨P, hP⟩ := length_configurationSeedSearchParameters_le_log ntm c
  obtain ⟨F, hF⟩ := length_configurationFieldContext_le_log ntm c
  refine ⟨3 * P + 2 * F + 2, fun w rank hrank => ?_⟩
  have hr := (length_encNat_mono hrank.le).trans
    ((encSeedSearchSize_seedLimit_length_le _).trans (encSeedSearchParameters_search_length_le _))
  have hp := hP w
  have hf := hF w
  simp only [configurationJustesenSubdivisionContext, encJustesenSubdivisionContext_apply,
    encJustesenSubdivisionContextFields, length_encPair, Nat.add_mul, Nat.mul_assoc]
  omega

private def seedWidth (ctx : JustesenSubdivisionContext) : ℕ :=
  ctx.parameters.search.seedLimit.size - 1

private def codeBit (p : JustesenSubdivisionContext × ℕ) (index : ℕ) : Bool :=
  p.1.field.indexedBit p.2 index

/-- Pending, suspended, or returned state of the concrete weighted adjacency callback. -/
abbrev JustesenSubdivisionState :=
  (Query JustesenSubdivisionContext ⊕ Bool) ⊕
    ((Query JustesenSubdivisionContext ⊕ Bool) × (LayeredQuery ⊕ Bool))

/-- Tagged caller state with the layered callee state during a suspended call. -/
abbrev encJustesenSubdivisionState : JustesenSubdivisionState ↪ List Bool :=
  encCallback encJustesenSubdivisionContext encLayeredCallback

/-- Enter weighted adjacency with two binary IDs and the retained chain bound. -/
@[expose] def justesenSubdivisionEdgeStart :
    JustesenSubdivisionContext × ℕ × ℕ → JustesenSubdivisionState :=
  fun (ctx, u, v) => flatCallbackStart ⟨ctx, ctx.parameters.search.subdivision.chainBound, u, v⟩

/-- Entering the callback uses linear workspace in the retained context and two binary IDs. -/
theorem justesenSubdivisionEdgeStart_inSpace :
    let enc := encPair encJustesenSubdivisionContext (encPair encNat encNat)
    ComputableInSpace justesenSubdivisionEdgeStart enc encJustesenSubdivisionState
      (fun p => (enc p).length) := by
  let encIDs := encPair encNat encNat
  have hctx := fst encJustesenSubdivisionContext encIDs
  have hids := snd encJustesenSubdivisionContext encIDs
  exact (budget_comp_linear (flatCallbackStart_inSpace _ _)
    (encFlatQuery_mk_budget encJustesenSubdivisionContext hctx
      (encSubdivisionSize_chainBound_budget
        (encJustesenSubdivisionContext_subdivision_budget hctx))
      (budget_comp_linear (fst encNat encNat) hids)
      (budget_comp_linear (snd encNat encNat) hids))).of_enc_eq fun _ => rfl

/-- Weighted adjacency using the native Justesen bit evaluator and the retained seed rank. -/
noncomputable def justesenWeightedSubdivisionCallback (ntm : MultiTapeNTM k Bool State) :
    QueryMachine JustesenSubdivisionState :=
  weightedSubdivisionCallback ntm (fun ctx => ctx.parameters.graph)
    JustesenSubdivisionContext.rank seedWidth codeBit

/-- The native callback components use linear workspace in their encoded requests. -/
theorem justesenWeightedSubdivisionCallback_parts_inSpace (ntm : MultiTapeNTM k Bool State) :
    let M := justesenWeightedSubdivisionCallback ntm
    let enc := encJustesenSubdivisionState
    ComputableInSpace M.query enc encNat (fun s => (enc s).length) ∧
    ComputableInSpace M.next (QueryMachine.encStateRead enc) enc
      (fun p => (QueryMachine.encStateRead enc p).length) ∧
    ComputableInSpace M.halted enc encBool (fun s => (enc s).length) ∧
    ComputableInSpace M.emit (QueryMachine.encStateRead enc) encBits
      (fun p => (QueryMachine.encStateRead enc p).length) ∧
    ComputableInSpace M.finish enc encBits (fun s => (enc s).length) := by
  let : Inhabited JustesenSubdivisionContext :=
    ⟨⟨seedSearchParameters ⟨0, 0, 0, 0⟩, ⟨0, 0, []⟩, 0⟩⟩
  let enc := encJustesenSubdivisionContext
  have hid := budget_id (enc := enc) (.refl _)
  have hp := encJustesenSubdivisionContext_parameters_budget hid
  have hsize : seedWidth ≼ fun ctx => (enc ctx).length := .of_le fun ctx => by
    rw [seedWidth, ← length_encNat_eq_size]
    exact (Nat.sub_le _ _).trans ((encSeedSearchSize_seedLimit_length_le _).trans
      ((encSeedSearchParameters_search_length_le _).trans
        (encJustesenSubdivisionContext_parameters_length_le ctx)))
  have hctxLabel := fst (encPair enc encNat) encNat
  have hbit := budget_comp_linear fieldContext_indexedBit_inSpace (budget_prod
    (budget_prod (encJustesenSubdivisionContext_field_budget
      (budget_comp_linear (fst enc encNat) hctxLabel))
      (budget_comp_linear (snd enc encNat) hctxLabel))
    (snd (encPair enc encNat) encNat))
  exact weightedSubdivisionCallback_parts_inSpace ntm enc _ _ _ codeBit
    (encSeedSearchParameters_graph_budget hp) (encJustesenSubdivisionContext_rank_budget hid)
    (budget_natPred (budget_comp_linear natSize
      (encSeedSearchSize_seedLimit_budget (encSeedSearchParameters_search_budget hp)))) hsize hbit

/-- At valid scan IDs, every live callback state through return fits the encoded retained
context plus logarithmic overhead in the original input length. -/
theorem configurationJustesenWeightedSubdivisionCallback_states_le
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) :
    ∃ C, ∀ (w : List Bool) (ctx : JustesenSubdivisionContext),
      ctx.parameters.graph = layeredParameters ntm c w.length →
      ∀ (u v : ℕ),
        let size := (configurationSeedSearchSetup ntm c w).parameters.search.subdivision
        u < size.vertexCount → v < size.vertexCount →
        let q : FlatQuery JustesenSubdivisionContext := ⟨ctx, size.chainBound, u, v⟩
        let M := justesenWeightedSubdivisionCallback ntm
        ∀ t ≤ 3,
          (encJustesenSubdivisionState (M.runFrom w (flatCallbackStart q) t)).length ≤
            C * ((encJustesenSubdivisionContext ctx).length + (Nat.log2 w.length + 1)) :=
  configurationWeightedSubdivisionCallback_states_le ntm c encJustesenSubdivisionContext
    (fun ctx => ctx.parameters.graph) JustesenSubdivisionContext.rank seedWidth codeBit

/-- At valid initialized scan IDs and a valid candidate rank, the first halt returns the
generated subdivision edge. The retained field context is the one for the initial graph. -/
theorem configurationJustesenWeightedSubdivisionCallback_agrees
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) (w : List Bool) :
    let I := configurationInstance ntm c w
    let size := (configurationSeedSearchSetup ntm c w).parameters.search.subdivision
    let index := configurationSubdivisionIndex ntm c w
    ∀ (u v : Fin size.vertexCount) (seed : Fin (2 ^ codeLength I.n (I.n - 1))),
      let ctx := configurationJustesenSubdivisionContext ntm c w seed.val
      let M := justesenWeightedSubdivisionCallback ntm
      let start := flatCallbackStart ⟨ctx, size.chainBound, u.val, v.val⟩
      (∀ t < 3, M.halted (M.runFrom w start t) = false) ∧
      ∃ answer, M.runFrom w start 3 = .inl (.inr answer) ∧
        M.halted (M.runFrom w start 3) = true ∧
        (answer = true ↔ (graph (layeredDigraph I)
          (generatedWeight ((BitString.equivFin _).symm seed)) size.chainBound).Adj
          (index.symm u) (index.symm v)) := by
  intro I size index u v seed ctx
  have hwidth : seedWidth ctx = codeLength I.n (I.n - 1) := by
    change (2 ^ codeLength I.n (I.n - 1) : ℕ).size - 1 = _
    rw [Nat.size_pow, Nat.add_sub_cancel]
  exact configurationWeightedSubdivisionCallback_agrees ntm c w ctx
    (fun ctx => ctx.parameters.graph) JustesenSubdivisionContext.rank seedWidth codeBit rfl
    u v seed rfl hwidth (fieldContext_indexedBit_eq (index.symm u).vertex.2)

/-- An initialized edge call first halts at clock three and returns the generated subdivision
adjacency verdict. Every live or returned state up to that clock has logarithmic encoded
length in the original word, uniformly over valid seed ranks and vertex IDs. -/
theorem configurationJustesenSubdivisionEdge_contract
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) :
    ∃ C, ∀ w : List Bool,
      let I := configurationInstance ntm c w
      let size := (configurationSeedSearchSetup ntm c w).parameters.search.subdivision
      let index := configurationSubdivisionIndex ntm c w
      ∀ (seed : Fin (2 ^ codeLength I.n (I.n - 1))) (u v : Fin size.vertexCount),
        let ctx := configurationJustesenSubdivisionContext ntm c w seed.val
        let M := justesenWeightedSubdivisionCallback ntm
        let start := justesenSubdivisionEdgeStart (ctx, u.val, v.val)
        (∀ t < 3, M.halted (M.runFrom w start t) = false) ∧
          M.halted (M.runFrom w start 3) = true ∧
          (callbackVerdict (M.runFrom w start 3) = true ↔
            (graph (layeredDigraph I)
              (generatedWeight ((BitString.equivFin _).symm seed)) size.chainBound).Adj
                (index.symm u) (index.symm v)) ∧
          ∀ t ≤ 3, (encJustesenSubdivisionState (M.runFrom w start t)).length ≤
            C * (Nat.log2 w.length + 1) := by
  obtain ⟨C, hC⟩ := configurationJustesenWeightedSubdivisionCallback_states_le ntm c
  obtain ⟨D, hD⟩ := length_configurationJustesenSubdivisionContext_le_log ntm c
  refine ⟨C * (D + 1), fun w => ?_⟩
  intro I size index seed u v ctx M start
  have hbound : ctx.parameters.search.subdivision.chainBound = size.chainBound :=
    congrArg (fun p : SeedSearchParameters => p.search.subdivision.chainBound)
      (configurationSeedSearchSetup_endpoints ntm c w).1.symm
  rw [show start = flatCallbackStart ⟨ctx, size.chainBound, u.val, v.val⟩ by
    dsimp only [start, justesenSubdivisionEdgeStart]; rw [hbound]]
  obtain ⟨hbefore, answer, hrun, hhalt, hedge⟩ :=
    configurationJustesenWeightedSubdivisionCallback_agrees ntm c w u v seed
  have h3 : M.runFrom w (flatCallbackStart ⟨ctx, size.chainBound, u.val, v.val⟩) 3 =
      .inl (.inr answer) := hrun
  refine ⟨hbefore, hhalt, by rw [h3]; exact hedge,
    fun t ht => (hC w ctx rfl u.val v.val u.isLt v.isLt t ht).trans ?_⟩
  simpa only [Nat.mul_assoc, Nat.add_mul, Nat.one_mul] using
    Nat.mul_le_mul_left C (Nat.add_le_add_right (hD w seed.val seed.isLt) _)

/-- Initialize the adjacency context from the encoded input and a valid binary rank,
including the logarithmic bound on the encoded output. -/
theorem configurationJustesenSubdivisionContext_inSpace
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) {α : Type} {enc : α ↪ List Bool} {rank : α → ℕ}
    (hrank : ComputableInLogSpace rank enc encNat)
    (hvalid : ∀ a, rank a < (configurationSeedSearchParameters ntm c (enc a)).search.seedLimit) :
    ComputableInSpace (fun a => configurationJustesenSubdivisionContext ntm c (enc a) (rank a))
      enc encJustesenSubdivisionContext (fun a => Nat.log2 (enc a).length) := by
  have hword : ComputableInLogSpace (fun a => enc a) enc encBits := .of_eq fun _ => rfl
  obtain ⟨D, hlen⟩ := length_configurationJustesenSubdivisionContext_le_log ntm c
  exact (configurationJustesenSubdivisionContext_inLogSpace ntm c hword
    hrank).inSpace_of_length_log ⟨D, fun a => hlen (enc a) (rank a) (hvalid a)⟩

/-- The generated subdivision adjacency transported to its canonical finite vertex IDs. -/
@[expose] noncomputable def configurationJustesenSubdivisionAdjacent
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) (w : List Bool) :
    let I := configurationInstance ntm c w
    let size := (configurationSeedSearchSetup ntm c w).parameters.search.subdivision
    Fin (2 ^ codeLength I.n (I.n - 1)) → Fin size.vertexCount → Fin size.vertexCount → Bool :=
  fun seed u v =>
    let I := configurationInstance ntm c w
    let size := (configurationSeedSearchSetup ntm c w).parameters.search.subdivision
    let index := configurationSubdivisionIndex ntm c w
    let G := graph (layeredDigraph I) (generatedWeight ((BitString.equivFin _).symm seed))
      size.chainBound
    @decide (G.Adj (index.symm u) (index.symm v)) (Classical.propDecidable _)

/-- At clock three the initialized callback has halted with the typed subdivision adjacency. -/
theorem configurationJustesenSubdivisionEdge_halts_and_agrees
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) (w : List Bool) :
    let I := configurationInstance ntm c w
    let size := (configurationSeedSearchSetup ntm c w).parameters.search.subdivision
    ∀ (seed : Fin (2 ^ codeLength I.n (I.n - 1))) (u v : Fin size.vertexCount),
      let ctx := configurationJustesenSubdivisionContext ntm c w seed.val
      let M := justesenWeightedSubdivisionCallback ntm
      let final := M.runFrom w (justesenSubdivisionEdgeStart (ctx, u.val, v.val)) 3
      M.halted final = true ∧
        callbackVerdict final = configurationJustesenSubdivisionAdjacent ntm c w seed u v := by
  intro I size seed u v ctx M final
  obtain ⟨_, hcall⟩ := configurationJustesenSubdivisionEdge_contract ntm c
  refine ⟨(hcall w seed u v).2.1, Bool.eq_iff_iff.mpr ?_⟩
  simpa only [configurationJustesenSubdivisionAdjacent, decide_eq_true_eq] using
    (hcall w seed u v).2.2.1

end Cslib.Complexity.STCON
