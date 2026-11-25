/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Tape.RunSum
import CslibFrontier.Foundations.LinearAlgebra.Matrix.ListProd

/-!
# The value of an automaton is a clause sum

At the code of an input, the clause sum of the run clauses is the value of the automaton
(`Tape.runVal_eq_domainClauseSum`). The reason is that the certificates of runs correspond to
the pairs of a matched run and a sequence of states from the initial to the final state, with one
certificate for each pair (`Tape.existsUnique_good`).

## Main results

* `Tape.existsUnique_good`, `Tape.runVal_eq_domainClauseSum`.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  module `Paper.CircuitPhi` (`lem_circuit_assignment`, `lem_circuit_value`)
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Tape

open Finset

variable {F : Type*} [CommRing F] {Γ S Q : Type} [DecidableEq Γ] [DecidableEq S] {n t M N : ℕ}

/-- The assignment of the hidden variables made of letters `o`, states `q`, places `P` and
contents `c`. -/
private def RunAssignment.mk (o : Fin t → Letter S (Fin n) Γ) (q : Fin (t + 1) → Q)
    (P : Ch S (Fin n) → Fin (t + 1) → Fin M) (c : S → Fin M → Option Γ) :
    RunAssignment Γ S Q n t M
  | .letter τ => o τ
  | .state τ => q τ
  | .place z τ => P z τ
  | .content s p => c s p

/-- **The certificates of a matched run.** For a matched run `o` with states `q` from `i` to `e`
there is exactly one certificate with these letters and states, and every certificate comes from
such a run. -/
theorem existsUnique_good (i e : Q) (u : Fin n → List Γ) (hM : N + t < M)
    (hN : (wordOf (List.ofFn u)).length ≤ N) (o : Fin t → Letter S (Fin n) Γ)
    (q : Fin (t + 1) → Q) :
    ((Matched (List.ofFn o) u ∧ q 0 = i ∧ q (Fin.last t) = e) →
      ∃! g : RunAssignment Γ S Q n t M, (g.letter = o ∧ g.state = q) ∧
        Good i e (code N u) g.letter g.state g.place g.content) ∧
    ∀ g : RunAssignment Γ S Q n t M, g.letter = o → g.state = q →
      Good i e (code N u) g.letter g.state g.place g.content →
        Matched (List.ofFn o) u ∧ q 0 = i ∧ q (Fin.last t) = e := by
  refine ⟨fun ⟨h, hi, he⟩ => ?_, fun g h1 h2 hg =>
    h1 ▸ h2 ▸ ⟨hg.matched (by omega), hg.first, hg.last⟩⟩
  obtain ⟨P, c, hg⟩ := exists_good hM hN h hi he
  refine existsUnique_of_exists_of_unique ⟨RunAssignment.mk o q P c, ⟨rfl, rfl⟩, hg⟩ ?_
  rintro g g' ⟨⟨a1, a2⟩, hg⟩ ⟨⟨a1', a2'⟩, hg'⟩
  have h1 := a1.trans a1'.symm
  have h2 := a2.trans a2'.symm
  funext d
  rcases d with τ | τ | ⟨z, τ⟩ | ⟨s, p⟩
  · exact congrFun h1 τ
  · exact congrFun h2 τ
  · apply Fin.ext
    change (g.place z τ : ℕ) = g'.place z τ
    rw [hg.place z τ, hg'.place z τ, hg.place_zero, hg'.place_zero, h1]
  · change g.content s p = g'.content s p
    rw [hg.contents s false p, hg'.contents s false p, h1]

open scoped Classical in
/-- **The value of an automaton is a clause sum**: at the code of the input `u`, the clause sum
of the run clauses with the matrix entries of `mu` as weights is the value of `mu` on `u`. -/
theorem runVal_eq_domainClauseSum [Fintype Γ] [Fintype S] [Fintype Q] [DecidableEq Q]
    (mu : Letter S (Fin n) Γ → Matrix Q Q F) (i e : Q) (u : Fin n → List Γ) (hM : N + t < M)
    (hN : (wordOf (List.ofFn u)).length ≤ N) :
    domainClauseSum (runLits (Γ := Γ) (S := S) (n := n) (t := t) (M := M) (N := N) i e)
      (runWeights mu) (code N u) = runVal mu i e t u := by
  have hl : domainClauseSum (runLits (Γ := Γ) (S := S) (n := n) (t := t) (M := M) (N := N) i e)
      (runWeights mu) (code N u) = ∑ g : RunAssignment Γ S Q n t M,
        if Good i e (code N u) g.letter g.state g.place g.content then
          ∏ τ, mu (g.letter τ) (g.state τ.castSucc) (g.state τ.succ) else 0 := by
    unfold domainClauseSum
    refine sum_congr rfl fun (g : RunAssignment Γ S Q n t M) _ => ?_
    rw [Fintype.prod_sum_type, ← mul_boole]
    exact congrArg₂ (· * ·)
      ((prod_congr rfl fun _ _ => by congr).trans (prod_stepLits mu (code N u) g))
      ((prod_congr rfl fun _ _ => by congr).trans (prod_ruleLits (F := F) i e (code N u) g))
  have hr : runVal mu i e t u = ∑ y : (Fin t → Letter S (Fin n) Γ) × (Fin (t + 1) → Q),
      if Matched (List.ofFn y.1) u ∧ y.2 0 = i ∧ y.2 (Fin.last t) = e then
        ∏ τ, mu (y.1 τ) (y.2 τ.castSucc) (y.2 τ.succ) else 0 := by
    unfold runVal
    rw [Fintype.sum_prod_type]
    refine sum_congr rfl fun o _ => ?_
    by_cases ho : Matched (List.ofFn o) u
    · rw [ite_eq_left ho, List.map_ofFn, Matrix.list_prod_ofFn_apply]
      exact sum_congr rfl fun _ _ => by simp [ho]
    · simp [ho]
  rw [hl, hr, ← sum_filter, ← sum_filter]
  refine sum_bij (fun g _ => (g.letter, g.state)) ?_ ?_ ?_ fun _ _ => rfl
  · exact fun g hg => mem_filter.mpr
      ⟨mem_univ _, (existsUnique_good i e u hM hN _ _).2 g rfl rfl (mem_filter.mp hg).2⟩
  · intro g hg g' hg' heq
    obtain ⟨h1, h2⟩ := Prod.mk.inj heq
    exact ((existsUnique_good i e u hM hN _ _).1
      ((existsUnique_good i e u hM hN _ _).2 g' rfl rfl (mem_filter.mp hg').2)).unique
      ⟨⟨h1, h2⟩, (mem_filter.mp hg).2⟩ ⟨⟨rfl, rfl⟩, (mem_filter.mp hg').2⟩
  · rintro ⟨o, q⟩ hy
    obtain ⟨g, ⟨⟨h1, h2⟩, hg⟩, -⟩ := (existsUnique_good i e u hM hN o q).1 (mem_filter.mp hy).2
    exact ⟨g, mem_filter.mpr ⟨mem_univ _, hg⟩, Prod.ext h1 h2⟩

end Cslib.Circuits.Arithmetic.Separation.Tape
