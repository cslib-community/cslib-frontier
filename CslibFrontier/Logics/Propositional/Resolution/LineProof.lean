/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.LineProof
public import CslibFrontier.Logics.Propositional.Resolution.Proof

/-!
# Resolution proofs as `LineProof` derivations and semantic refutations

This module characterizes `Cslib.Logic.PL.CNF.IsProof` as a `Cslib.Logic.PL.LineProof` over the
binary resolution rule set `Cslib.Logic.PL.CNF.resolutionRules`, making the generic DAG proof
combinators (`LineProof.simulate`, `LineProof.toSemanticRefutation`) available on resolution proofs.

In particular, reversing a resolution refutation and mapping each clause to its set of satisfying
assignments immediately gives a semantic refutation
(`Cslib.Logic.PL.CNF.IsProof.isSemanticRefutation`) in the sense of
[Krajíček, Definition 4.1][Krajicek1997].

## Main definitions

* `Cslib.Logic.PL.CNF.resolutionRules`: the binary resolution inference rules over `Clause V`.

## Main results

* `Cslib.Logic.PL.CNF.isProof_iff_lineProof`: `φ.IsProof ls` holds iff `ls` is a `LineProof`
  from `{c | c ∈ φ}` under `CNF.resolutionRules V`.
* `Cslib.Logic.PL.CNF.IsProof.isSemanticRefutation`: resolution refutations induce semantic
  refutations of the same length.

## References

* [J. Krajíček, *Interpolation theorems, lower bounds for proof systems, and independence results
  for bounded arithmetic*][Krajicek1997]
* [J. A. Robinson, *A machine-oriented logic based on the resolution principle*][Robinson1965]
-/

public section

namespace Cslib.Logic.PL

variable {V : Type*} [DecidableEq V]

/-- The inference rules of propositional resolution: from `c₁` containing `(v, true)` and `c₂`
containing `(v, false)`, infer `c₁.resolvent c₂ v`. -/
@[expose] def CNF.resolutionRules (V : Type*) [DecidableEq V] : Set (LineRule (Clause V)) :=
  {r | ∃ c₁ c₂ v, (v, true) ∈ c₁ ∧ (v, false) ∈ c₂ ∧ r = ⟨[c₁, c₂], c₁.resolvent c₂ v⟩}

/-- Every resolution rule has two premises. -/
theorem CNF.resolutionRules_premises_length_le {r : LineRule (Clause V)}
    (hr : r ∈ CNF.resolutionRules V) : r.premises.length ≤ 2 := by
  obtain ⟨_, _, _, -, -, rfl⟩ := hr
  simp

/-- Every resolution rule preserves clause satisfaction. -/
theorem CNF.resolutionRules_sound {r : LineRule (Clause V)} (hr : r ∈ CNF.resolutionRules V)
    {σ : V → Bool} (hp : ∀ c ∈ r.premises, c.eval σ = true) : r.concl.eval σ = true := by
  obtain ⟨c₁, c₂, v, -, -, rfl⟩ := hr
  exact Clause.eval_resolvent v (hp c₁ (by simp)) (hp c₂ (by simp))

/-- **Resolution proofs as `LineProof` derivations.** -/
theorem CNF.isProof_iff_lineProof {φ : CNF V} {ls : List (Clause V)} :
    φ.IsProof ls ↔ LineProof (CNF.resolutionRules V) {c | c ∈ φ} ls := by
  constructor
  · intro h
    induction h with
    | nil => exact .nil
    | mem _ hc ih => exact ih.hyp hc
    | @resolvent ls c₁ c₂ v _ h₁ h₂ hv₁ hv₂ ih =>
      exact ih.step ⟨c₁, c₂, v, hv₁, hv₂, rfl⟩ (by simp [h₁, h₂])
  · intro h
    induction h with
    | nil => exact .nil
    | hyp _ hc ih => exact ih.mem hc
    | step _ hr hp ih =>
      obtain ⟨c₁, c₂, v, hv₁, hv₂, rfl⟩ := hr
      exact ih.resolvent v (hp c₁ (by simp)) (hp c₂ (by simp)) hv₁ hv₂

/-- **Resolution refutations are semantic refutations** [Krajíček, Section 4][Krajicek1997]:
reading a resolution refutation from its first line and sending each clause to its satisfying
assignments gives a semantic refutation with the same number of lines. -/
theorem CNF.IsProof.isSemanticRefutation {φ : CNF V} {ls : List (Clause V)}
    {init : Set (Set (V → Bool))} (h : φ.IsProof ls)
    (hφ : ∀ c ∈ φ, {σ | c.eval σ = true} ∈ init) (hnil : [] ∈ ls) :
    IsSemanticRefutation init fun j : Fin ls.reverse.length => {σ | ls.reverse[j].eval σ = true} :=
  (CNF.isProof_iff_lineProof.1 h).toSemanticRefutation hφ
    (fun _ hr => CNF.resolutionRules_premises_length_le hr)
    (fun _ hr _ hp => CNF.resolutionRules_sound hr hp) hnil (by simp)

end Cslib.Logic.PL
