/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.EdgeCSP.Blossom.Optimality
public import CslibFrontier.Algorithms.Lean.EdgeCSP.Blossom.Size
public import CslibFrontier.Algorithms.Lean.EdgeCSP.Forest.Blossom
public import CslibFrontier.Algorithms.Lean.EdgeCSP.Forest.Optimality

/-!
# One improvement through blossom contraction

The whole algorithm of [KazdaKolmogorovRolinek2018], arXiv:1602.03124v6,
Algorithm 1 (printed p. 10) and Section 5.3 (printed pp. 11–13), organized to return
one improvement. Each call performs one fresh search and at most one recursive child call.
A child improvement is lifted and returned immediately. A child optimum transfers through
Lemma 42; the preparation has the original defect count. This arrangement avoids recursively
optimizing a contracted child before restarting a local optimization loop.

The explicit depth parameter makes the function total even on malformed input. For an edge
instance with even delta-matroid constraints and valid labels, a depth exceeding
`contractionMeasure` suffices. This module proves semantic correctness and termination;
encoded native resource bounds belong to the executable implementation.

The recursion organization and its bookkeeping are original; the search, preparation,
contraction and lifting are the existing constructions from the cited source.
-/

public section

namespace Cslib.Logic.PL.CSP.Solver

open Table

/-- Return one valid labeling with exactly two fewer defects, or certify optimality by
returning `none`. The latter interpretation requires the depth and model hypotheses of
`improve_spec`; depth exhaustion on arbitrary raw inputs simply returns `none`. -/
@[expose] def improve : (depth : ℕ) → (F : CSP Table ℕ) →
    OccurrenceLabeling F Bool → Option (OccurrenceLabeling F Bool)
  | 0, _, _ => none
  | depth + 1, _F, f =>
    match Forest.search sem f with
    | .exhausted _ => none
    | .augment m => some (m.walk.flip f)
    | .blossom m => do
      let b ← m.blossomData
      let prepared := b.prepare.flip f
      let comparison ← improve depth (Blossom.contract prepared (Blossom.internal b.cycle))
        (Blossom.reference prepared (Blossom.internal b.cycle))
      Blossom.liftComparison prepared b.cycle comparison

private theorem blossom_contract_hyps {F : CSP Table ℕ} {f : OccurrenceLabeling F Bool}
    {m : Forest.Meeting F} (hF : EdgeInstance F) (hf : ValidLabeling sem f)
    (hM : EdgeInstance.EvenConstraints sem F) (hs : Forest.search sem f = .blossom m) :
    ∃ b, m.blossomData = some b ∧
      let prepared := b.prepare.flip f
      let vs := Blossom.internal b.cycle
      b.cycle.IsBlossom sem prepared ∧ ValidLabeling sem prepared ∧
      (defects prepared).card = (defects f).card ∧
      (Blossom.contract prepared vs).contractionMeasure < F.contractionMeasure ∧
      EdgeInstance (Blossom.contract prepared vs) ∧
      ValidLabeling sem (Blossom.reference prepared vs) ∧
      EdgeInstance.EvenConstraints sem (Blossom.contract prepared vs) := by
  obtain ⟨b, hb, hblossom, hprepared, hcount⟩ :=
    Forest.search_blossom_correct sem f hF hf hM hs
  have hne := Blossom.touched_ne_nil b.cycle hblossom.steps_ne_nil
  exact ⟨b, hb, hblossom, hprepared, hcount, Blossom.contractionMeasure_contract_lt hF hblossom,
    Blossom.edge_contract hF _ _, Blossom.valid_reference hprepared _ hne,
    Blossom.even_contract hprepared hM _ hne⟩

/-- An adequately funded call either certifies optimality or removes exactly two defects.
All contraction and lifting obligations are derived internally from the fresh search. -/
theorem improve_spec (depth : ℕ) (F : CSP Table ℕ) (f : OccurrenceLabeling F Bool)
    (hd : F.contractionMeasure < depth) (hF : EdgeInstance F)
    (hf : ValidLabeling sem f) (hM : EdgeInstance.EvenConstraints sem F) :
    match improve depth F f with
    | none => IsOptimalLabeling sem f
    | some g => ValidLabeling sem g ∧ (defects g).card + 2 = (defects f).card := by
  induction depth generalizing F with
  | zero => omega
  | succ depth ih =>
    cases hs : Forest.search sem f with
    | exhausted es =>
      simpa only [improve, hs] using
        Forest.search_exhausted_isOptimalLabeling sem f hF hf hM hs
    | augment m =>
      simpa only [improve, hs] using (Forest.search_augment_correct sem f hF hf hM hs).2
    | blossom m =>
      obtain ⟨b, hb, hblossom, hprepared, hcount, hdec, hF', href, hM'⟩ :=
        blossom_contract_hyps hF hf hM hs
      have hchild := ih _ _ (by omega) hF' href hM'
      cases hc : improve depth (Blossom.contract (b.prepare.flip f) (Blossom.internal b.cycle))
          (Blossom.reference (b.prepare.flip f) (Blossom.internal b.cycle)) with
      | none =>
        rw [hc] at hchild
        have ho := Blossom.isOptimal_of_reference hF hblossom hprepared hM hchild
        have horig : IsOptimalLabeling sem f := ⟨hf, fun g hg => hcount ▸ ho.2 g hg⟩
        simpa only [improve, hs, hb, Option.bind_eq_bind, Option.bind_some, hc, Option.bind_none]
          using horig
      | some g =>
        rw [hc] at hchild
        obtain ⟨result, hr, hv, hn⟩ := Blossom.liftComparison_spec hF hblossom hprepared hM
          g hchild.1 (by have := hchild.2; omega)
        simpa only [improve, hs, hb, Option.bind_eq_bind, Option.bind_some, hc, hr, hcount]
          using And.intro hv hn

/-- Sufficient contraction budgets give exactly the same deterministic improvement, including
its outside changes. Depth affects only malformed or inadequately funded executions. -/
theorem improve_depth_eq (F : CSP Table ℕ) (f : OccurrenceLabeling F Bool)
    (hF : EdgeInstance F) (hf : ValidLabeling sem f)
    (hM : EdgeInstance.EvenConstraints sem F) (a b : ℕ)
    (ha : F.contractionMeasure < a) (hb : F.contractionMeasure < b) :
    improve a F f = improve b F f := by
  induction a generalizing F b with
  | zero => omega
  | succ a ih =>
    cases b with
    | zero => omega
    | succ b =>
      cases hs : Forest.search sem f with
      | exhausted _ | augment _ => simp only [improve, hs]
      | blossom m =>
        obtain ⟨data, hd, _, _, _, hlt, hF', href, hM'⟩ := blossom_contract_hyps hF hf hM hs
        have he := ih _ _ hF' href hM' b (by omega) (by omega)
        simp only [improve, hs, hd, Option.bind_eq_bind, Option.bind_some]
        exact congrArg (fun r => r.bind (Blossom.liftComparison (data.prepare.flip f) data.cycle))
          he

end Cslib.Logic.PL.CSP.Solver
