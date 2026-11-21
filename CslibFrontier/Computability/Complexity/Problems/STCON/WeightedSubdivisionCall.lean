/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.STCON.SubdivisionCall
public import CslibFrontier.Computability.Complexity.Problems.STCON.SubdivisionEndpoints
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Subdivision.HozaWeight

/-!
# Weighted adjacency calls for layered STCON

The callback reads the original input through the layered adjacency machine and evaluates
the departure weight from a retained seed rank. The scan supplies flat IDs numbered by
`subdivisionIndex` and starts the call with `flatCallbackStart`.

## Main definitions

* `Cslib.Complexity.STCON.weightedSubdivisionCallback`: the weighted adjacency machine.

## Main results

* `Cslib.Complexity.STCON.weightedSubdivisionCallback_agrees`: on valid indexed vertices the
  first halt returns adjacency in the generated subdivision, given the correct code bits.
* `Cslib.Complexity.STCON.weightedSubdivisionCallback_parts_inSpace`: native component bounds
  given the compact context projections and a certified code-bit routine.
* `Cslib.Complexity.STCON.weightedSubdivisionCallback_states_le`: the live-state cost adds the
  framed compact request and the logarithmic cost of layered adjacency on valid IDs.
-/

public section

namespace Cslib.Complexity.STCON

open Cslib.Code.JustesenFamily Cslib.Reachability.Hoza Cslib.LayeredDigraph.Subdivision
open _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.MultiTapeTM.ComputableInSpace
open _root_.Turing.QueryMachine.Subdivision
open _root_.Turing.MultiTapeNTM.ConfigurationGraph

variable {k : ℕ} {State Context : Type} [Fintype State]

/-- Use the same retained graph width for edge coordinates and for source-weight evaluation. -/
noncomputable def weightedSubdivisionCallback (ntm : MultiTapeNTM k Bool State)
    (params : Context → LayeredParameters) (rank seedWidth : Context → ℕ)
    (code : Context × ℕ → ℕ → Bool) :
    QueryMachine ((Query Context ⊕ Bool) ⊕ ((Query Context ⊕ Bool) × (LayeredQuery ⊕ Bool))) :=
  callback (layeredCallback ntm) (subdivisionLayeredCall params)
    (sourceWeight (fun ctx => (params ctx).width) rank seedWidth code)
    (Sum.elim (fun _ => false) id)

/-- Linear-space components for the caller, including the original-input read and weighted
return transition. The numeric seed width is charged to the encoded context. -/
theorem weightedSubdivisionCallback_parts_inSpace [Inhabited Context]
    (ntm : MultiTapeNTM k Bool State) (encContext : Context ↪ List Bool)
    (params : Context → LayeredParameters) (rank seedWidth : Context → ℕ)
    (code : Context × ℕ → ℕ → Bool)
    (hp : ComputableInSpace params encContext encLayeredParameters
      (fun ctx => (encContext ctx).length))
    (hr : ComputableInSpace rank encContext encNat (fun ctx => (encContext ctx).length))
    (hs : ComputableInSpace seedWidth encContext encNat (fun ctx => (encContext ctx).length))
    (hsize : seedWidth ≼ fun ctx => (encContext ctx).length)
    (hc : let enc := encPair (encPair encContext encNat) encNat
      ComputableInSpace (fun p : (Context × ℕ) × ℕ => code p.1 p.2)
        enc encBool (fun p => (enc p).length)) :
    let M := weightedSubdivisionCallback ntm params rank seedWidth code
    let enc := encCallback encContext encLayeredCallback
    ComputableInSpace M.query enc encNat (fun s => (enc s).length) ∧
    ComputableInSpace M.next (QueryMachine.encStateRead enc) enc
      (fun p => (QueryMachine.encStateRead enc p).length) ∧
    ComputableInSpace M.halted enc encBool (fun s => (enc s).length) ∧
    ComputableInSpace M.emit (QueryMachine.encStateRead enc) encBits
      (fun p => (QueryMachine.encStateRead enc p).length) ∧
    ComputableInSpace M.finish enc encBits (fun s => (enc s).length) := by
  obtain ⟨hq, hn, hh, _, _⟩ := layeredCallback_parts_inSpace ntm
  have ha := sumElim (budget_const (encIn := encLayeredQuery) (encB := encBool) false (.refl _))
    (budget_id (enc := encBool) (.refl _))
  exact callback_parts_inSpace encContext encLayeredCallback (layeredCallback ntm)
    (subdivisionLayeredCall params) _ (Sum.elim (fun _ => false) id)
    (subdivisionLayeredCall_inSpace encContext params hp)
    (sourceWeight_inSpace encContext _ rank seedWidth code
      (encLayeredParameters_width_budget hp) hr hs hsize hc) ha hq hn hh

private theorem flatRequest_eq (I : STCONInstance) (ctx : Context) {bound : ℕ}
    (a b : Vertex (Fin ((I.n - 1) + 1) × Fin I.n) bound) :
    decodeFlatQuery ⟨ctx, bound, (subdivisionIndex I bound a).val,
      (subdivisionIndex I bound b).val⟩ =
      ⟨ctx, (finProdFinEquiv a.vertex).val, (finProdFinEquiv b.vertex).val,
        a.offset.val, b.offset.val⟩ := by
  rw [subdivisionIndex_apply, subdivisionIndex_apply, decodeFlatQuery_flatIndex]

private theorem indexedRequest_eq (ntm : MultiTapeNTM k Bool State) (c : ℕ) (w : List Bool)
    (params : Context → LayeredParameters) (ctx : Context)
    (hp : params ctx = layeredParameters ntm c w.length)
    (u v : Fin (((configurationInstance ntm c w).n - 1) + 1) ×
      Fin (configurationInstance ntm c w).n) (i j : ℕ) :
    let coords := layeredCoordinates (configurationInstance ntm c w)
    subdivisionLayeredCall params ⟨ctx, (finProdFinEquiv u).val, (finProdFinEquiv v).val, i, j⟩ =
      .inl (layeredQueryRequest ntm c w (coords.symm u) (coords.symm v)) := by
  simpa only [Equiv.apply_symm_apply] using subdivisionLayeredCall_eq ntm c w
    ((layeredCoordinates _).symm u) ((layeredCoordinates _).symm v) i j params ctx hp

private theorem layeredCall_first_halt (ntm : MultiTapeNTM k Bool State) (w : List Bool)
    (req : LayeredQuery) :
    (∀ t < 1, (layeredCallback ntm).halted
      ((layeredCallback ntm).runFrom w (.inl req) t) = false) ∧
    (layeredCallback ntm).halted ((layeredCallback ntm).runFrom w (.inl req) 1) = true := by
  refine ⟨fun t ht => ?_, ?_⟩
  · rw [Nat.lt_one_iff.mp ht]
    rfl
  · rw [show (1 : ℕ) = 0 + 1 from rfl, layeredCallback_runFrom]
    rfl

/-- The call first halts at clock three and returns the edge predicate of the generated
subdivision. The source code bits agree with the chosen generator on valid indices. -/
theorem weightedSubdivisionCallback_agrees (ntm : MultiTapeNTM k Bool State)
    (c : ℕ) (w : List Bool) (ctx : Context) (params : Context → LayeredParameters)
    (rank seedWidth : Context → ℕ) (code : Context × ℕ → ℕ → Bool)
    (hp : params ctx = layeredParameters ntm c w.length) {bound : ℕ}
    (a b : Vertex (Fin (((configurationInstance ntm c w).n - 1) + 1) ×
      Fin (configurationInstance ntm c w).n) bound)
    (seed : Fin (2 ^ codeLength (configurationInstance ntm c w).n
      ((configurationInstance ntm c w).n - 1)))
    (hr : rank ctx = seed.val)
    (hs : seedWidth ctx = codeLength (configurationInstance ntm c w).n
      ((configurationInstance ntm c w).n - 1))
    (hc : ∀ i : Fin (codeLength (configurationInstance ntm c w).n
      ((configurationInstance ntm c w).n - 1)),
      code (ctx, a.vertex.2.val) i.val = indexedCodewordMod a.vertex.2 i) :
    let I := configurationInstance ntm c w
    let index := subdivisionIndex I bound
    let M := weightedSubdivisionCallback ntm params rank seedWidth code
    let start := flatCallbackStart ⟨ctx, bound, (index a).val, (index b).val⟩
    (∀ t < 3, M.halted (M.runFrom w start t) = false) ∧
    ∃ answer, M.runFrom w start 3 = .inl (.inr answer) ∧
      M.halted (M.runFrom w start 3) = true ∧
      (answer = true ↔ (graph (layeredDigraph I)
        (generatedWeight ((BitString.equivFin _).symm seed)) bound).Adj a b) := by
  let I := configurationInstance ntm c w
  let u := (layeredCoordinates I).symm a.vertex
  let v := (layeredCoordinates I).symm b.vertex
  let q : Query Context := ⟨ctx, (finProdFinEquiv a.vertex).val, (finProdFinEquiv b.vertex).val,
    a.offset.val, b.offset.val⟩
  let weight := sourceWeight (fun ctx => (params ctx).width) rank seedWidth code
  have hreq : subdivisionLayeredCall params q = .inl (layeredQueryRequest ntm c w u v) :=
    indexedRequest_eq ntm c w params ctx hp a.vertex b.vertex a.offset.val b.offset.val
  obtain ⟨edge, hrun, hedge⟩ := layeredCallback_agrees ntm c w u v
  have hw : weight q = generatedWeight ((BitString.equivFin _).symm seed) a.vertex :=
    sourceWeight_eq_generatedWeight (fun ctx => (params ctx).width) rank seedWidth
      code ctx seed a.vertex _ _ _ (by rw [hp]; rfl) hr hs hc
  have htime := layeredCall_first_halt ntm w (layeredQueryRequest ntm c w u v)
  rw [← hreq] at htime
  dsimp only
  rw [flatCallbackStart, flatRequest_eq]
  have hfinal : (weightedSubdivisionCallback ntm params rank seedWidth code).runFrom w
      (.inl (.inl q)) 3 = .inl (.inr (edgeQuery q (weight q) edge)) := by
    rw [weightedSubdivisionCallback, callback_runFrom _ _ _ _ _ _ 1 htime.1 htime.2, hreq, hrun]
    rfl
  obtain ⟨hbefore, hafter⟩ := callback_first_halt _ _ weight
    (Sum.elim (fun _ => false) id) w q 1 htime.1 htime.2
  refine ⟨hbefore, _, hfinal, hafter, ?_⟩
  rw [hw]
  exact edgeQuery_agrees (layeredDigraph I)
    (finProdFinEquiv.toEmbedding.trans Fin.valEmbedding) _ bound ctx a b edge hedge

/-- Through the return clock, the state holds a framed compact request and a logarithmic
original-edge state. In particular, a logarithmic decoded-request bound composes with this
bound without charging a copy of the original word. -/
theorem weightedSubdivisionCallback_states_le (ntm : MultiTapeNTM k Bool State)
    (c : ℕ) (w : List Bool) (encContext : Context ↪ List Bool)
    (ctx : Context) (params : Context → LayeredParameters)
    (rank seedWidth : Context → ℕ) (code : Context × ℕ → ℕ → Bool)
    (hp : params ctx = layeredParameters ntm c w.length) {bound : ℕ}
    (a b : Vertex (Fin (((configurationInstance ntm c w).n - 1) + 1) ×
      Fin (configurationInstance ntm c w).n) bound)
    (t : ℕ) (ht : t ≤ 3) :
    let index := subdivisionIndex (configurationInstance ntm c w) bound
    let flat : FlatQuery Context := ⟨ctx, bound, (index a).val, (index b).val⟩
    let M := weightedSubdivisionCallback ntm params rank seedWidth code
    (encCallback encContext encLayeredCallback (M.runFrom w (flatCallbackStart flat) t)).length ≤
      2 * (encQuery encContext (decodeFlatQuery flat)).length +
        12 * (radixExponent State c * Fintype.card (Register k) + 1) *
          (Nat.log2 (w.length + 1) + 1) + 16 := by
  let coords := layeredCoordinates (configurationInstance ntm c w)
  let u := coords.symm a.vertex
  let v := coords.symm b.vertex
  let req := layeredQueryRequest ntm c w u v
  have hreq := indexedRequest_eq ntm c w params ctx hp a.vertex b.vertex
    a.offset.val b.offset.val
  dsimp only at hreq ⊢
  rw [flatCallbackStart, flatRequest_eq]
  have htime := layeredCall_first_halt ntm w req
  have hstate (i : ℕ) := layeredCallback_states_le_log ntm c w u v i
  rw [← hreq] at htime hstate
  have h := callback_states_le encContext encLayeredCallback (layeredCallback ntm)
    (subdivisionLayeredCall params)
    (sourceWeight (fun ctx => (params ctx).width) rank seedWidth code)
    (Sum.elim (fun _ => false) id) w _ 1 _ _
    htime.1 htime.2 le_rfl (fun i _ => hstate i) t ht
  exact h.trans (by omega)

end Cslib.Complexity.STCON
