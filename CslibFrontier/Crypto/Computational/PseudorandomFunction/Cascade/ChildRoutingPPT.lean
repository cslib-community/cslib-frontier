/-
Copyright (c) 2026 Samuel Schlesinger, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.PseudorandomFunction.Cascade.ChildRouting
public import CslibFrontier.Languages.Probabilistic.Oracle.Substitution
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Finite
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Computability.Probabilistic.Memoize
import CslibFrontier.Computability.Probabilistic.Oracle.Parameter
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Languages.Probabilistic.Oracle.Support
import CslibFrontier.Languages.Probabilistic.Simulation

/-!
# Strict polynomial time for adaptive cascade routing

The router uses natural-number child channels. An encoded request sends a channel number and
the next block on a single word-oracle port. This lets a single finite machine handle all
security parameters and cuts, while each routed query still reads only a bounded reply prefix.

## Main definitions

* `Cslib.Crypto.encodedCascadeChildRouter` runs the cascade router on the single word port.

## Main results

* `Cslib.Crypto.isOraclePPTOn_encodedCascadeChildRouter` certifies strict oracle PPT with a
  unary security parameter and cut depth.

## References

* [BonehShoup2023], v0.6, Section 4.6.1 (printed pp. 152–154) and Section 6.4.2
  (printed pp. 229–230), for the adjacent-hybrid routing step.
-/

public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM

/-- Use the existing adaptive router with each child query sent as an encoded word to the
single external port. -/
@[expose]
noncomputable def encodedCascadeChildRouter (valid : List Bool → Bool) (inLen : ℕ → ℕ)
    (family : List Bool → List Bool → List Bool) (n depth : ℕ)
    (program : WordOracleComp Unit Bool) : WordOracleComp Unit Bool :=
  ProbOracleComp.simulate
    (fun request => ProbOracleComp.query (spec := fun _ : Unit × List Bool => List Bool)
      ((), encCascadeChildRequest request))
    (cascadeChildRouter valid inLen family n depth program)

/-- Framed parent list, followed by the short-word memoization cache. -/
private enc_structure encRouterState : CascadeChildRouterState where
  parents : (encList encBits), shortLabels : (encMemoCache encBits encBits)

private abbrev RouterCaller := (ℕ × List Bool) × ℕ

/-- Framed security parameter and auxiliary word, followed by unary depth. -/
private abbrev encRouterCaller : RouterCaller ↪ List Bool :=
  encPair (encPair encUnary encBits) encUnary

private abbrev RouterCall := RouterCaller × (Unit × List Bool) × CascadeChildRouterState

/-- The caller data, framed unit port and query word, then the router state. -/
private abbrev encRouterCall : RouterCall ↪ List Bool :=
  encHandlerCall encRouterCaller (encFinEnum Unit) encRouterState

private abbrev forwardChild (request : ℕ × List Bool) : WordOracleComp Unit (List Bool) :=
  ProbOracleComp.query (spec := fun _ : Unit × List Bool => List Bool)
    ((), encCascadeChildRequest request)

private theorem encodedRouter_eq_interpret (valid : List Bool → Bool) (inLen : ℕ → ℕ)
    (family : List Bool → List Bool → List Bool) (n depth : ℕ)
    (program : WordOracleComp Unit Bool) :
    encodedCascadeChildRouter valid inLen family n depth program =
      Prod.fst <$> (OracleComp.interpret
        (OracleComp.sumHandler (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
          (fun request state => ProbOracleComp.simulate forwardChild
            (cascadeChildRoute valid inLen family n depth request.2 state)))
        program).run ⟨[], []⟩ := by
  have hom : IsMonadHom (WordOracleComp ℕ) (WordOracleComp Unit)
      (fun {_} => ProbOracleComp.simulate forwardChild) :=
    .mk' (ProbOracleComp.simulate_pure _) (ProbOracleComp.simulate_bind _)
  unfold encodedCascadeChildRouter cascadeChildRouter
  rw [ProbOracleComp.simulate_map, OracleComp.map_run_interpret hom]
  congr 3 with request state : 2
  cases request with
  | inl k =>
    change ProbOracleComp.simulate forwardChild
      (StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)) state) = _
    simp [StateT.lift]
  | inr q => rfl

private theorem isOraclePPTOn_route
    {valid : ℕ → List Bool → Bool} {inLen : ℕ → ℕ}
    {family : List Bool → List Bool → List Bool}
    (hvalid : ComputableInPolyTime (fun p : ℕ × List Bool => valid p.1 p.2)
      (encPair encUnary encBits) encBool)
    (hIn : ComputableInPolyTime inLen encUnary encUnary)
    (hCascade : ComputableInPolyTime (fun p : List Bool × List Bool =>
      cascadeFamily inLen family p.1 p.2) (encPair encBits encBits) encBits) :
    IsOraclePPTOn encRouterCall (encPair encBits encRouterState)
      (fun x : RouterCall => ProbOracleComp.simulate forwardChild
        (cascadeChildRoute (valid x.1.1.1) inLen family x.1.1.1 x.1.2 x.2.1.2 x.2.2)) := by
  let hcaller := ComputableInPolyTime.fst encRouterCaller
    (encPair (encPair (encFinEnum Unit) encBits) encRouterState)
  let hport := ComputableInPolyTime.snd encRouterCaller
    (encPair (encPair (encFinEnum Unit) encBits) encRouterState)
  let hn := hcaller.fst'.fst'
  let hq := hport.fst'.snd'
  let hstate := hport.snd'
  let hcache := encRouterState_shortLabels_polyTime hstate
  let hparents := encRouterState_parents_polyTime hstate
  let hwidth := hIn.comp hn
  let hcut := hcaller.snd'.unary_mul' hwidth
  let hparent := hq.bitsTakeWithInput hcut
  let hsuffix := hq.bitsDropWithInput hcut
  have hchannel : ComputableInPolyTime (fun x : RouterCall =>
      x.2.2.parents.idxOf (x.2.1.2.take (x.1.2 * inLen x.1.1.1))) encRouterCall encUnary := by
    rw [lawful_beq_subsingleton (List.instBEq : BEq (List Bool)) instBEqOfDecidableEq]
    exact ComputableInPolyTime.idxOfWithInput hparents hparent
  let hcount := (ComputableInPolyTime.length encBits).comp hparents
  let hadd := ComputableInPolyTime.listAppend' hparents
    (ComputableInPolyTime.cons' hparent (.const []))
  let hupdated := (hchannel.unary_eq' hcount).ite_decide hadd hparents
  let hblock := hsuffix.bitsTakeWithInput hwidth
  let hrest := hsuffix.bitsDropWithInput hwidth
  have hword : ComputableInPolyTime (fun x : RouterCall =>
      let cut := x.1.2 * inLen x.1.1.1
      encCascadeChildRequest (x.2.2.parents.idxOf (x.2.1.2.take cut),
        (x.2.1.2.drop cut).take (inLen x.1.1.1))) encRouterCall encBits :=
    (hchannel.prod hblock).of_enc_eq (fun _ => encBits_apply _)
  simp only [cascadeChildRoute, apply_ite, ProbOracleComp.simulate_pure,
    ProbOracleComp.simulate_bind, ProbOracleComp.simulate_query, ProbOracleComp.simulate_sample]
  refine IsOraclePPTOn.cond (hvalid.comp (hn.prod hq)) ?_
    (((ComputableInPolyTime.const ([] : List Bool)).prod hstate).isPPTOn.isOraclePPTOn)
  refine IsOraclePPTOn.ite (hcut.unary_lt' hq.length_bits_comp) ?_ ?_
  · let hin := ComputableInPolyTime.fst encRouterCall encBits
    let hreply := ComputableInPolyTime.snd encRouterCall encBits
    let finish (x : RouterCall) (reply : List Bool) :=
      let cut := x.1.2 * inLen x.1.1.1
      let parent := x.2.1.2.take cut
      let parents := if x.2.2.parents.idxOf parent = x.2.2.parents.length then
          x.2.2.parents ++ [parent] else x.2.2.parents
      (cascadeFamily inLen family reply ((x.2.1.2.drop cut).drop (inLen x.1.1.1)),
        { x.2.2 with parents })
    have hfinish : ComputableInPolyTime (fun p => finish p.1 p.2)
        (encPair encRouterCall encBits) (encPair encBits encRouterState) :=
      (hCascade.comp (hreply.prod (hrest.comp hin))).prod
        (encRouterState_mk_polyTime (hupdated.comp hin) (hcache.comp hin))
    simpa only [forwardChild, finish, bind_pure_comp, Functor.map_map, Function.comp_def] using
      (IsOraclePPTOn.query_take () hword hn).map_with (f := finish) hfinish
  · have hshort := IsPPTOn.memoize (compute := fun (x : RouterCall) (_ : List Bool) =>
        BitString.sampleList x.1.1.1) hn.sampleList hq hcache
    let hin := ComputableInPolyTime.fst encRouterCall
      (encPair encBits (encMemoCache encBits encBits))
    let hout := ComputableInPolyTime.snd encRouterCall
      (encPair encBits (encMemoCache encBits encBits))
    let hfinish := hout.fst'.prod (encRouterState_mk_polyTime (hparents.comp hin) hout.snd')
    simpa only [cachedRandomFunctionOracle, cachedSamplerOracle, ↓reduceIte,
      ProbOracleComp.sample_map, bind_pure_comp] using
      (hshort.isOraclePPTOn (Operation := Unit)).map_with
        (f := fun x out => (out.1, CascadeChildRouterState.mk x.2.2.parents out.2)) hfinish

private theorem route_bounds (valid : List Bool → Bool) (inLen : ℕ → ℕ)
    (family : List Bool → List Bool → List Bool) (n depth : ℕ) (query : List Bool)
    (hLen : ∀ key block, block.length = inLen key.length → (family key block).length = key.length)
    (state : CascadeChildRouterState) (result : List Bool × CascadeChildRouterState)
    (hwidth : ∀ entry ∈ state.shortLabels, entry.2.length ≤ n)
    (hresult : result ∈ OracleComp.support (ProbOracleComp.simulate forwardChild
      (cascadeChildRoute valid inLen family n depth query state))) :
    (∀ entry ∈ result.2.shortLabels, entry.2.length ≤ n) ∧ result.1.length ≤ n ∧
      (encRouterState result.2).length ≤
        (encRouterState state).length + 4 * query.length + 2 * n + 3 := by
  simp only [cascadeChildRoute, apply_ite, ProbOracleComp.simulate_pure,
    ProbOracleComp.simulate_bind, ProbOracleComp.simulate_query, ProbOracleComp.simulate_sample]
    at hresult
  split at hresult
  · split at hresult
    · obtain ⟨reply, _, hreply⟩ := OracleComp.mem_supportWith_bind_iff.mp hresult
      simp only [OracleComp.supportWith_pure, Set.mem_singleton_iff] at hreply
      subst result
      refine ⟨hwidth, (length_cascadeFamily hLen _ _).trans_le (List.length_take_le _ _), ?_⟩
      split
      · have h := List.length_take_le' (depth * inLen n) query
        simp only [encRouterState_apply, length_encPair, length_encList, List.map_append,
          List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil,
          encBits_apply]
        omega
      · change (encRouterState state).length ≤ _
        omega
    · obtain ⟨⟨label, cache⟩, hcache, hreply⟩ := OracleComp.mem_supportWith_bind_iff.mp hresult
      simp only [OracleComp.supportWith_pure, Set.mem_singleton_iff] at hreply
      subst result
      change (label, cache) ∈ OracleComp.support (ProbOracleComp.sample (spec :=
        fun _ : Unit × List Bool => List Bool)
          (cachedRandomFunctionOracle (fun _ => true) n query state.shortLabels)) at hcache
      rw [ProbOracleComp.support_sample, eval_cachedSamplerOracle,
        BitString.eval_sampleList] at hcache
      simp only [cachedDistOracle, ↓reduceIte] at hcache
      obtain ⟨hlabel, hwidth', hgrowth⟩ := memoize_call_size_le encBits encBits
        (fun _ => BitString.uniformList n) query state.shortLabels n
        (by simpa only [encBits_apply] using hwidth)
        (fun word hw => by simpa only [encBits_apply] using
          (BitString.length_of_mem_support_uniformList hw).le) (label, cache) hcache
      simp only [encBits_apply] at hlabel hwidth'
      refine ⟨hwidth', hlabel, ?_⟩
      simp only [encRouterState_apply, length_encPair, encBits_apply] at hgrowth ⊢
      omega
  · simp only [OracleComp.support, OracleComp.supportWith_pure, Set.mem_singleton_iff] at hresult
    subst result
    refine ⟨hwidth, Nat.zero_le _, ?_⟩
    change (encRouterState state).length ≤ _
    omega

/-- The encoded router is strict oracle PPT, uniformly in the security parameter, auxiliary word
and cut depth. The base family is polynomial-time and preserves key width on full blocks. -/
theorem isOraclePPTOn_encodedCascadeChildRouter
    {valid : ℕ → List Bool → Bool} {inLen : ℕ → ℕ}
    {family : List Bool → List Bool → List Bool} {adversary : OracleDistinguisher}
    (hvalid : ComputableInPolyTime (fun p : ℕ × List Bool => valid p.1 p.2)
      (encPair encUnary encBits) encBool)
    (hIn : ComputableInPolyTime inLen encUnary encUnary)
    (hLen : ∀ key block, block.length = inLen key.length → (family key block).length = key.length)
    (hEval : ComputableInPolyTime (fun p : List Bool × List Bool => family p.1 p.2)
      (encPair encBits encBits) encBits)
    (hA : IsOraclePPT encBool adversary) :
    IsOraclePPTOn (encPair (encPair encUnary encBits) encUnary) encBool
      (fun p : (ℕ × List Bool) × ℕ =>
        encodedCascadeChildRouter (valid p.1.1) inLen family p.1.1 p.2
          (adversary p.1.1 p.1.2)) := by
  let hn := (ComputableInPolyTime.fst encRouterCaller encBits).fst'.fst'
  let hq := (ComputableInPolyTime.snd encRouterCaller encBits).length_bits_comp
  let hresources := (((ComputableInPolyTime.const 4).unary_mul' hq).unary_add'
    ((ComputableInPolyTime.const 2).unary_mul' hn)).unary_add' (.const 3)
  have hrun := hA.run_interpret_preprocess_open
    (input := encRouterCaller) (operationEncoding := encFinEnum Unit)
    (stateEncoding := encRouterState)
    (handler := fun (p : RouterCaller) q state => ProbOracleComp.simulate forwardChild
      (cascadeChildRoute (valid p.1.1) inLen family p.1.1 p.2 q.2 state))
    (prepare := Prod.fst) (initial := fun _ => ⟨[], []⟩)
    (resources := fun p query => 4 * query.length + 2 * p.1.1 + 3)
    (ComputableInPolyTime.fst _ _)
    (isOraclePPTOn_route hvalid hIn (computableInPolyTime_cascadeFamily hIn hLen hEval))
    (.const _) (fun p state => ∀ entry ∈ state.shortLabels, entry.2.length ≤ p.1.1)
    (fun _ => by simp) hresources
    (fun p q state hwidth result hs => by
      obtain ⟨hcache, hreply, hgrowth⟩ :=
        route_bounds (valid p.1.1) inLen family p.1.1 p.2 q.2 hLen state result hwidth hs
      exact ⟨hcache, by omega, by omega⟩)
  refine (hrun.map (ComputableInPolyTime.fst _ _)).congr ?_
  intro p State oracle s
  rw [encodedRouter_eq_interpret]

end Cslib.Crypto
