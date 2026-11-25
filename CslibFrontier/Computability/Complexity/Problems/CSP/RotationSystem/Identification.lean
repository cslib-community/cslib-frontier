/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.CSP.RotationSystem.VariableDarts
public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.VertexMergeGenus
public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.CertificateCornerSwap
import CslibFrontier.Foundations.Data.List.IdxOfIdentification
import CslibFrontier.Computability.Complexity.Problems.CSP.RotationSystem.ArgumentOrderTable

/-!
# Actual incidence transport for identification of two variable names

A map with precisely the selected-pair kernel on occurring labels matches the generic
vertex merge after actual dense naming. All indexed argument ends remain in place; labels
outside the occurring set are unrestricted. Cofaciality and argument-end conditions are
separate obligations of an ordered realization, not consequences of arbitrary renaming.
-/

public section

namespace Cslib.Complexity.CSP

open Cslib.Logic.PL Graph Graph.RotationSystem

variable {Rel V W : Type} [DecidableEq V] [DecidableEq W]

/-- Retain edge/end positions when transporting a generic merge to the actual renamed CSP. -/
@[expose] def identificationDartEquiv (F : CSP Rel V) (f : V → W)
    (h k : Dart (incidenceGraph F)) :
    Dart (mergeGraph h k) ≃ Dart (incidenceGraph (F.relabel f)) :=
  (mergeDartEquiv h k).symm.trans (relabelDartEquiv F f)

/-- The selected-pair kernel is required only on actually occurring names. Dense renaming
and repeated source labels are accounted for internally, without a free-port injection. -/
theorem identificationDartEquiv_vertex_eq_iff (F : CSP Rel V) (f : V → W) (x y : V)
    (hx : x ∈ F.vars) (hy : y ∈ F.vars) (h k : Dart (incidenceGraph F))
    (hh : h.vertex = F.distinctVars.idxOf x) (hk : k.vertex = F.distinctVars.idxOf y)
    (hkernel : ∀ a ∈ F.vars, ∀ b ∈ F.vars,
      f a = f b ↔ Function.update id y x a = Function.update id y x b)
    (a b : Dart (mergeGraph h k)) :
    (identificationDartEquiv F f h k a).vertex = (identificationDartEquiv F f h k b).vertex ↔
      a.vertex = b.vertex := by
  obtain ⟨a, rfl⟩ := (mergeDartEquiv h k).surjective a
  obtain ⟨b, rfl⟩ := (mergeDartEquiv h k).surjective b
  simp only [identificationDartEquiv, Equiv.trans_apply, Equiv.symm_apply_apply]
  obtain ⟨o, ho⟩ := exists_incidenceDart a
  obtain ⟨p, hp⟩ := exists_incidenceDart b
  have hm (q : F.Occurrence) : q.var ∈ F.distinctVars := CSP.mem_distinctVars.mpr q.var_mem
  have hmt (q : F.Occurrence) : f q.var ∈ (F.relabel f).distinctVars := by
    rw [CSP.mem_distinctVars, CSP.vars_relabel]
    exact List.mem_map_of_mem q.var_mem
  have hidx_lt {W' : Type} [DecidableEq W'] (G : CSP Rel W') {v : W'} (hv : v ∈ G.distinctVars) :
      G.distinctVars.idxOf v < G.numVars :=
    CSP.length_distinctVars (F := G) ▸ List.idxOf_lt_length_of_mem hv
  have hxlt := hidx_lt F (CSP.mem_distinctVars.mpr hx)
  have hylt := hidx_lt F (CSP.mem_distinctVars.mpr hy)
  have himage (q : F.Occurrence) : Function.update id (F.distinctVars.idxOf y)
      (F.distinctVars.idxOf x) (F.distinctVars.idxOf q.var) < F.numVars := by
    by_cases he : F.distinctVars.idxOf q.var = F.distinctVars.idxOf y
    · simpa [he] using hxlt
    · simpa [Function.update_of_ne he] using hidx_lt F (hm q)
  have hc (i : ℕ) : Function.update id (F.distinctVars.idxOf y)
      (F.distinctVars.idxOf x) (F.numVars + i) = F.numVars + i :=
    Function.update_of_ne (by omega) _ id
  have hto := hidx_lt _ (hmt o)
  have htp := hidx_lt _ (hmt p)
  have hio := himage o
  have hip := himage p
  rw [← ho, ← hp, vertex_relabelDartEquiv, vertex_relabelDartEquiv,
    vertex_mergeDartEquiv, vertex_mergeDartEquiv, hh, hk,
    vertex_incidenceDart, vertex_incidenceDart]
  cases a.2 <;> cases b.2 <;> simp only [Bool.false_eq_true, ite_false, ite_true, hc]
  · rw [List.idxOf_inj (hmt o), hkernel _ o.var_mem _ p.var_mem,
      List.idxOf_update_id_eq_iff _ _ _ _ _ (hm o) (hm p)]
  all_goals omega

/-- The coordinate transport retains the literal binary dart index. -/
theorem index_identificationDartEquiv (F : CSP Rel V) (f : V → W)
    (h k : Dart (incidenceGraph F)) (d : Dart (mergeGraph h k)) :
    (identificationDartEquiv F f h k d).index = d.index := rfl

/-- Actual edge reversal is retained by the merge-to-renamed-CSP transport. -/
theorem reverse_identificationDartEquiv (F : CSP Rel V) (f : V → W)
    (h k : Dart (incidenceGraph F)) (d : Dart (mergeGraph h k)) :
    identificationDartEquiv F f h k d.reverse =
      (identificationDartEquiv F f h k d).reverse := rfl

/-- Construct the actual renamed CSP rotation by the selected outgoing-corner swap and
positional dense-name transport. The label map need only have the selected-pair kernel
on occurring names; distinct old variables need not remain distinct in the target. -/
@[expose] def identifyVariablesRotation (F : CSP Rel V) (f : V → W) (x y : V)
    (hx : x ∈ F.vars) (hy : y ∈ F.vars) (hxy : x ≠ y)
    (h k : Dart (incidenceGraph F))
    (hh : h.vertex = F.distinctVars.idxOf x) (hk : k.vertex = F.distinctVars.idxOf y)
    (hkernel : ∀ a ∈ F.vars, ∀ b ∈ F.vars,
      f a = f b ↔ Function.update id y x a = Function.update id y x b)
    (rho : RotationSystem (incidenceGraph F)) : RotationSystem (incidenceGraph (F.relabel f)) :=
  (rho.mergeVertices h k (by
    rw [hh, hk]
    exact fun he => hxy ((List.idxOf_inj (CSP.mem_distinctVars.mpr hx)).mp he))).transport
      (identificationDartEquiv F f h k)
      (identificationDartEquiv_vertex_eq_iff F f x y hx hy h k hh hk hkernel)

/-- Numerical genus is preserved on the actual target CSP when the chosen existing
corners are cofacial. The target proof is derived from generic surgery and the actual
source/target endpoint guards, not assumed as an embedding provider. -/
theorem numericalGenusZero_identifyVariablesRotation (F : CSP Rel V) (f : V → W) (x y : V)
    (hx : x ∈ F.vars) (hy : y ∈ F.vars) (hxy : x ≠ y)
    (h k : Dart (incidenceGraph F))
    (hh : h.vertex = F.distinctVars.idxOf x) (hk : k.vertex = F.distinctVars.idxOf y)
    (hkernel : ∀ a ∈ F.vars, ∀ b ∈ F.vars,
      f a = f b ↔ Function.update id y x a = Function.update id y x b)
    (rho : RotationSystem (incidenceGraph F)) (hr : rho.NumericalGenusZero)
    (hf : rho.faceNext.SameCycle h k) :
    (identifyVariablesRotation F f x y hx hy hxy h k hh hk hkernel rho).NumericalGenusZero := by
  have hdiff : h.vertex ≠ k.vertex := by
    rw [hh, hk]
    exact fun he => hxy ((List.idxOf_inj (CSP.mem_distinctVars.mpr hx)).mp he)
  have hg := rho.numericalGenusZero_mergeVertices (incidenceVertices_declared F) hr h k hdiff hf
  exact (rho.mergeVertices h k hdiff).numericalGenusZero_transport
    (identificationDartEquiv F f h k)
    (identificationDartEquiv_vertex_eq_iff F f x y hx hy h k hh hk hkernel)
    (reverse_identificationDartEquiv F f h k)
    (mergeGraph_endpoints_declared h k (incidenceVertices_declared F))
    (incidenceVertices_declared (F.relabel f)) hg

/-- The literal successor is the old forward rotation after swapping just the two selected
outgoing corners. The positional target coordinate map does not reflect either block. -/
theorem rotate_identifyVariablesRotation (F : CSP Rel V) (f : V → W) (x y : V)
    (hx : x ∈ F.vars) (hy : y ∈ F.vars) (hxy : x ≠ y)
    (h k : Dart (incidenceGraph F))
    (hh : h.vertex = F.distinctVars.idxOf x) (hk : k.vertex = F.distinctVars.idxOf y)
    (hkernel : ∀ a ∈ F.vars, ∀ b ∈ F.vars,
      f a = f b ↔ Function.update id y x a = Function.update id y x b)
    (rho : RotationSystem (incidenceGraph F)) (d : Dart (incidenceGraph F)) :
    (identifyVariablesRotation F f x y hx hy hxy h k hh hk hkernel rho).rotate
        (relabelDartEquiv F f d) =
      relabelDartEquiv F f (rho.rotate (Equiv.swap h k d)) := by
  simp [identifyVariablesRotation, transport, identificationDartEquiv, mergeVertices]

/-- Swapping variable-side outgoing corners retains every original relation's directed
argument cycle. Both end-tag hypotheses are explicit: swapping constraint corners would
not have this property at arbitrary arity. -/
theorem respectsArgumentOrder_identifyVariablesRotation (F : CSP Rel V) (f : V → W) (x y : V)
    (hx : x ∈ F.vars) (hy : y ∈ F.vars) (hxy : x ≠ y)
    (h k : Dart (incidenceGraph F))
    (hh : h.vertex = F.distinctVars.idxOf x) (hk : k.vertex = F.distinctVars.idxOf y)
    (hkernel : ∀ a ∈ F.vars, ∀ b ∈ F.vars,
      f a = f b ↔ Function.update id y x a = Function.update id y x b)
    (hs : h.2 = false) (ks : k.2 = false)
    (rho : RotationSystem (incidenceGraph F)) (ho : RespectsArgumentOrder rho) :
    RespectsArgumentOrder (identifyVariablesRotation F f x y hx hy hxy h k hh hk hkernel rho) := by
  let tau := identifyVariablesRotation F f x y hx hy hxy h k hh hk hkernel rho
  have hc : verifyArgumentOrder F (RotationCertificate.ofRotation rho) = true := by
    refine (verifyArgumentOrder_eq_true_iff
      (RotationCertificate.verifyRotation_ofRotation rho (incidenceVertices_declared F))).mpr ?_
    rwa [RotationCertificate.decode_ofRotation rho (incidenceVertices_declared F)]
  have he : verifyArgumentOrder (F.relabel f) (RotationCertificate.ofRotation tau) = true := by
    rw [verifyArgumentOrder_relabel, verifyArgumentOrder_congr F
      (RotationCertificate.ofRotation tau) (RotationCertificate.ofRotation rho) ?_, hc]
    intro i hi
    let d : Dart (incidenceGraph F) :=
      (⟨i, by simpa only [incidenceGraph_edges, List.length_map] using hi⟩, true)
    have hd : d ≠ h := fun he => by simpa [d, hs] using congrArg Prod.snd he
    have kd : d ≠ k := fun he => by simpa [d, ks] using congrArg Prod.snd he
    change (RotationCertificate.ofRotation tau).successor.getD d.index 0 =
      (RotationCertificate.ofRotation rho).successor.getD d.index 0
    dsimp only [tau]
    rw [← index_relabelDartEquiv F f d, RotationCertificate.getD_ofRotation,
      rotate_identifyVariablesRotation, Equiv.swap_apply_of_ne_of_ne hd kd,
      index_relabelDartEquiv, index_relabelDartEquiv, RotationCertificate.getD_ofRotation]
  simpa only [RotationCertificate.decode_ofRotation tau
    (incidenceVertices_declared (F.relabel f))] using
    (verifyArgumentOrder_eq_true_iff (RotationCertificate.verifyRotation_ofRotation tau
      (incidenceVertices_declared (F.relabel f)))).mp he

/-- Complete generated-table identity for actual incidence identification: dense-name
transport retains positions, so only the two selected outgoing entries are exchanged. -/
theorem ofRotation_identifyVariablesRotation (F : CSP Rel V) (f : V → W) (x y : V)
    (hx : x ∈ F.vars) (hy : y ∈ F.vars) (hxy : x ≠ y)
    (h k : Dart (incidenceGraph F))
    (hh : h.vertex = F.distinctVars.idxOf x) (hk : k.vertex = F.distinctVars.idxOf y)
    (hkernel : ∀ a ∈ F.vars, ∀ b ∈ F.vars,
      f a = f b ↔ Function.update id y x a = Function.update id y x b)
    (rho : RotationSystem (incidenceGraph F)) :
    RotationCertificate.ofRotation
        (identifyVariablesRotation F f x y hx hy hxy h k hh hk hkernel rho) =
      (RotationCertificate.ofRotation rho).swapSuccessors h.index k.index := by
  unfold identifyVariablesRotation
  rw [ofRotation_transport _ _ _ (index_identificationDartEquiv F f h k)]
  exact ofRotation_mergeVertices rho h k _

end Cslib.Complexity.CSP
