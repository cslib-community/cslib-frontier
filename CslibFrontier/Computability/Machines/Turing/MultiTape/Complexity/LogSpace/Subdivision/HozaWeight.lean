/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Reachability.MinIsolation.Generator.SeedRank
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Subdivision
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Retained-rank source weights for subdivision

A subdivision request carries the flat label of its original source vertex. The
quotient and remainder by the original graph width provide the layer for scaling
and the column for the code-bit routine. The retained-rank evaluator computes the
source weight, independently of either chain offset.

The workspace bound is linear in the encoded request when the supplied numeric
seed width fits that budget and the code-bit routine has its own linear certificate.
-/

public section

namespace Turing.QueryMachine.Subdivision

open MultiTapeTM ComputableInSpace
open Cslib Cslib.Reachability.Hoza Cslib.Code.JustesenFamily

variable {Context : Type}

private def weightRequest (width rank seedWidth : Context → ℕ) (q : Query Context) :
    SeedRank.WeightRequest (Context × ℕ) :=
  ⟨⟨(q.context, q.fromLabel % width q.context), rank q.context, seedWidth q.context⟩,
    q.fromLabel / width q.context⟩

/-- Evaluate the weight of the original source of a subdivision edge request. The code-bit
routine receives the retained context, original column and requested bit index. -/
def sourceWeight (width rank seedWidth : Context → ℕ) (code : Context × ℕ → ℕ → Bool)
    (q : Query Context) : ℕ :=
  SeedRank.weightRank code (weightRequest width rank seedWidth q)

/-- At a valid flat source label, the callback computes the isolation generator's
weight for the retained seed rank when the supplied code bits agree with the generator. -/
theorem sourceWeight_eq_generatedWeight {w n : ℕ} (width rank seedWidth : Context → ℕ)
    (code : Context × ℕ → ℕ → Bool) (ctx : Context) (seed : Fin (2 ^ codeLength w n))
    (z : Fin (n + 1) × Fin w) (target fromOffset toOffset : ℕ)
    (hw : width ctx = w) (hr : rank ctx = seed.val) (hs : seedWidth ctx = codeLength w n)
    (hcode : ∀ i : Fin (codeLength w n), code (ctx, z.2.val) i.val = indexedCodewordMod z.2 i) :
    sourceWeight width rank seedWidth code
      ⟨ctx, (finProdFinEquiv z).val, target, fromOffset, toOffset⟩ =
        generatedWeight ((BitString.equivFin _).symm seed) z := by
  have hz := finProdFinEquiv.symm_apply_apply z
  have hl : (finProdFinEquiv z).val / w = z.1.val := congrArg (fun p => p.1.val) hz
  have hc : (finProdFinEquiv z).val % w = z.2.val := congrArg (fun p => p.2.val) hz
  simp only [sourceWeight, weightRequest, hw, hr, hs, hl, hc]
  exact SeedRank.weightRank_eq_generatedWeight code (ctx, z.2.val) seed z hcode

/-- The source weight is an admissible native component of the subdivision callback.
The bound on the numeric seed width charges the accumulator even when the encoded
rank is short. -/
theorem sourceWeight_inSpace [Inhabited Context] (encContext : Context ↪ List Bool)
    (width rank seedWidth : Context → ℕ) (code : Context × ℕ → ℕ → Bool)
    (hw : ComputableInSpace width encContext encNat (fun c => (encContext c).length))
    (hr : ComputableInSpace rank encContext encNat (fun c => (encContext c).length))
    (hs : ComputableInSpace seedWidth encContext encNat (fun c => (encContext c).length))
    (hsize : seedWidth ≼ fun c => (encContext c).length)
    (hc : let encCode := encPair (encPair encContext encNat) encNat
      ComputableInSpace (fun p : (Context × ℕ) × ℕ => code p.1 p.2)
        encCode encBool (fun p => (encCode p).length)) :
    ComputableInSpace (sourceWeight width rank seedWidth code) (encQuery encContext) encNat
      (fun q => (encQuery encContext q).length) := by
  let encQ := encQuery encContext
  let encCodeContext := encPair encContext encNat
  have hid := budget_id (enc := encQ) (S := fun q => (encQ q).length) (.refl _)
  have hctx := encQuery_context_budget encContext hid
  have hlabel := encQuery_fromLabel_budget encContext hid
  have hwidth := budget_comp_linear hw hctx
  have hseed := SeedRank.encRequest_mk_budget encCodeContext
    (budget_prod hctx (budget_natMod hlabel hwidth))
    (budget_comp_linear hr hctx) (budget_comp_linear hs hctx)
  have hreq : ComputableInSpace (weightRequest width rank seedWidth) encQ
      (SeedRank.encWeightRequest encCodeContext) (fun q => (encQ q).length) :=
    SeedRank.encWeightRequest_mk_budget encCodeContext hseed (budget_natDiv hlabel hwidth)
  have hwidthSize := (hsize.comp (Query.context : Query Context → Context)).trans hctx.length_le
  have h := budget_comp (SeedRank.weightRank_inSpace encCodeContext code hc) hreq
    (hreq.length_le.add hwidthSize)
  exact h

end Turing.QueryMachine.Subdivision
