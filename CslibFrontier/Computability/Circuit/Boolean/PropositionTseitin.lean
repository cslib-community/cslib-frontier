/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.Tseitin
public import CslibFrontier.Logics.Propositional.TseitinCNF
import Mathlib.Data.List.GetD

/-! # The two Tseitin transformations agree

A proposition over the atoms `Fin n` compiles to a De Morgan gate list on `n` inputs
(`Cslib.Logic.PL.Proposition.deMorganCode`): an atom `i` is input wire `i`, `⊥` is a constant gate,
`∧` and `∨` are gates, and `A → B` is the gate `¬A ∨ B`, written with a negation gate and a
disjunction gate. The list is well formed (`Proposition.isCodeFrom_deMorganCode`) and its output
wire carries the value of the proposition (`Proposition.evalOutput_deMorganCode`).

So the Tseitin transformation of the proposition (`Cslib.Logic.PL.Proposition.tseitinCNF`) and the
Tseitin formula of its gate list with the output fixed to `true`
(`Cslib.Circuits.Boolean.tseitinSatCNF`) have the same models on the atoms: for every valuation
`v` of the atoms, `A.tseitinCNF` has a model restricting to `v` exactly when the circuit formula
with the inputs fixed to `v` is satisfiable, and both hold exactly when `A` is true at `v`
(`Proposition.exists_eval_tseitinCNF_iff_satisfiable_tseitinSatCNF`). The two formulas differ in
their auxiliary variables (subformulas against wires, with an extra wire for each implication) and
in the shape of their clauses, so this projection to the atoms is the sense in which they are
equivalent.

## Main definitions

* `Cslib.Logic.PL.Proposition.DeMorganCode`: a gate list and its output wire.
* `Cslib.Logic.PL.Proposition.deMorganCode`: the gate list of a proposition and its output wire.

## Main results

* `Cslib.Logic.PL.Proposition.isCodeFrom_deMorganCode`: the gate list is well formed.
* `Cslib.Logic.PL.Proposition.evalOutput_deMorganCode`: its output is the value of the proposition.
* `Cslib.Logic.PL.Proposition.exists_eval_tseitinCNF_iff_satisfiable_tseitinSatCNF`: the two
  Tseitin transformations have the same models on the atoms.

## References

This compilation and the comparison are original.
-/

@[expose] public section

namespace Cslib.Logic.PL.Proposition

open Cslib.Circuits Cslib.Circuits.Boolean

variable {n : ℕ}

/-- A De Morgan gate list and the wire carrying its value. -/
structure DeMorganCode where
  /-- The gates, in order. -/
  gates : List (Op × List ℕ)
  /-- The wire carrying the value. -/
  output : ℕ

/-- The De Morgan gate list of a proposition over `Fin n`, numbered from gate `k` (wire `n + k`)
on, and the wire carrying its value: an atom `i` is input wire `i`, `⊥` is a constant gate, `∧`
and `∨` are gates after the gates of their arguments, and `A → B` is `¬A ∨ B`. -/
def deMorganCode : Proposition (Fin n) → ℕ → DeMorganCode
  | atom i, _ => ⟨[], i⟩
  | falsum, k => ⟨[(.const false, [])], n + k⟩
  | and A B, k =>
    let a := A.deMorganCode k
    let b := B.deMorganCode (k + a.gates.length)
    ⟨a.gates ++ b.gates ++ [(.and, [a.output, b.output])],
      n + k + a.gates.length + b.gates.length⟩
  | or A B, k =>
    let a := A.deMorganCode k
    let b := B.deMorganCode (k + a.gates.length)
    ⟨a.gates ++ b.gates ++ [(.or, [a.output, b.output])],
      n + k + a.gates.length + b.gates.length⟩
  | imp A B, k =>
    let a := A.deMorganCode k
    let b := B.deMorganCode (k + a.gates.length)
    ⟨a.gates ++ b.gates ++
        [(.not, [a.output]), (.or, [n + k + a.gates.length + b.gates.length, b.output])],
      n + k + a.gates.length + b.gates.length + 1⟩

/-- The output wire of the gate list of a proposition, numbered from gate `k` on, is an input or
one of its gates. -/
theorem output_deMorganCode_lt (A : Proposition (Fin n)) (k : ℕ) :
    (A.deMorganCode k).output < n + k + (A.deMorganCode k).gates.length := by
  induction A generalizing k with
  | atom i => simp only [deMorganCode]; omega
  | falsum => simp [deMorganCode]
  | and A B ihA ihB | or A B ihA ihB | imp A B ihA ihB =>
    simp only [deMorganCode, List.length_append, List.length_cons, List.length_nil]
    omega

/-- **The gate list of a proposition is well formed**: numbered from gate `k` on, its gates read
only the inputs and earlier gates. -/
theorem isCodeFrom_deMorganCode (A : Proposition (Fin n)) (k : ℕ) :
    Program.IsCodeFrom signature n k (A.deMorganCode k).gates := by
  induction A generalizing k with
  | atom i => exact trivial
  | falsum => exact ⟨⟨rfl, by simp⟩, trivial⟩
  | and A B ihA ihB | or A B ihA ihB | imp A B ihA ihB =>
    have hA := output_deMorganCode_lt A k
    have hB := output_deMorganCode_lt B (k + (A.deMorganCode k).gates.length)
    simp only [deMorganCode]
    rw [Program.isCodeFrom_append, Program.isCodeFrom_append]
    refine ⟨⟨ihA k, ihB _⟩, ?_⟩
    first
      | exact ⟨⟨rfl, by
          simp only [List.mem_cons, List.not_mem_nil, or_false, List.length_append]
          rintro _ (rfl | rfl) <;> omega⟩, trivial⟩
      | exact ⟨⟨rfl, by
          simp only [List.mem_singleton, List.length_append]
          rintro _ rfl
          omega⟩,
        ⟨rfl, by
          simp only [List.mem_cons, List.not_mem_nil, or_false, List.length_append]
          rintro _ (rfl | rfl) <;> omega⟩, trivial⟩

/-- The value of a gate appended after the gates `gates`. -/
private theorem getD_evalCode_append_singleton (x : List Bool) (gates : List (Op × List ℕ))
    (g : Op × List ℕ) {w : ℕ} (hw : w = x.length + gates.length) :
    (evalCode interpretation false x (gates ++ [g])).getD w false =
      interpretation g.1 fun a =>
        g.2[a.val]?.elim false ((evalCode interpretation false x gates).getD · false) := by
  rw [evalCode_append_singleton, List.getD_append_right _ _ _ _ (by simp [hw])]
  simp [hw]

/-- **The output wire carries the value of the proposition**: after any gates `pre` numbered
before it, on inputs `x` of length `n`, the gate list of `A` gives its output wire the value of
`A` at the valuation reading the inputs. -/
theorem getD_evalCode_deMorganCode (A : Proposition (Fin n)) (x : List Bool) (hx : x.length = n)
    (pre : List (Op × List ℕ)) :
    (evalCode interpretation false x (pre ++ (A.deMorganCode pre.length).gates)).getD
        (A.deMorganCode pre.length).output false =
      A.eval fun i : Fin n => x.getD i false := by
  induction A generalizing pre with
  | atom i =>
    simpa only [deMorganCode, List.append_nil, eval_atom_bool] using
      getD_evalCode_of_lt _ _ _ _ (by omega)
  | falsum =>
    dsimp only [deMorganCode]
    rw [eval_falsum_bool, getD_evalCode_append_singleton _ _ _ (by omega)]
    rfl
  | and A B ihA ihB | or A B ihA ihB | imp A B ihA ihB =>
    have hlt_a := output_deMorganCode_lt A pre.length
    have hlt_b := output_deMorganCode_lt B (pre.length + (A.deMorganCode pre.length).gates.length)
    have hva := ihA pre
    have hvb := ihB (pre ++ (A.deMorganCode pre.length).gates)
    simp only [List.length_append] at hvb
    simp only [deMorganCode, ← List.append_assoc, eval_and_bool, eval_or_bool, eval_imp_bool]
    generalize A.deMorganCode pre.length = a at *
    generalize B.deMorganCode (pre.length + a.gates.length) = b at *
    have hva' : (evalCode interpretation false x (pre ++ a.gates ++ b.gates)).getD a.output false =
        A.eval fun i : Fin n => x.getD i false := by
      rwa [Cslib.Circuits.Boolean.getD_evalCode_append_of_lt
        (by simp only [List.length_append]; omega)]
    first
      | (rw [getD_evalCode_append_singleton _ _ _ (by simp only [List.length_append]; omega)]
         clear ihA ihB hva; simp_all [interpretation])
      | (rw [show ∀ (l : List (Op × List ℕ)) (g₁ g₂ : Op × List ℕ),
           l ++ [g₁, g₂] = l ++ [g₁] ++ [g₂] from fun _ _ _ => by simp]
         have hnot := getD_evalCode_append_singleton x (pre ++ a.gates ++ b.gates)
           (Op.not, [a.output]) (w := n + pre.length + a.gates.length + b.gates.length)
           (by simp only [List.length_append]; omega)
         have hb₂ : (evalCode interpretation false x
             (pre ++ a.gates ++ b.gates ++ [(Op.not, [a.output])])).getD b.output false =
             B.eval fun i : Fin n => x.getD i false := by
           rwa [Cslib.Circuits.Boolean.getD_evalCode_append_of_lt
             (by simp only [List.length_append]; omega)]
         rw [getD_evalCode_append_singleton _ _ _
           (by simp only [List.length_append, List.length_singleton]; omega)]
         clear ihA ihB hva hvb; simp_all [interpretation])

/-- **The output of the gate list of a proposition is its value.** -/
theorem evalOutput_deMorganCode (A : Proposition (Fin n)) (v : Fin n → Bool) :
    evalOutput (List.ofFn v) (A.deMorganCode 0).gates (A.deMorganCode 0).output = A.eval v := by
  have h := getD_evalCode_deMorganCode A (List.ofFn v) (by simp) []
  simp only [evalOutput, List.nil_append, List.length_nil] at h ⊢
  exact h.trans (congrArg A.eval (funext fun i => by simp))

/-- **The two Tseitin transformations agree on the atoms.** For a proposition `A` over `Fin n` and
a valuation `v` of its atoms, the Tseitin transformation `A.tseitinCNF` has a model whose
restriction to the atoms is `v` exactly when the circuit Tseitin formula of the gate list of `A`,
with the output fixed to `true` and the inputs fixed to `v`, is satisfiable. -/
theorem exists_eval_tseitinCNF_iff_satisfiable_tseitinSatCNF (A : Proposition (Fin n))
    (v : Fin n → Bool) :
    (∃ σ, A.tseitinCNF.eval σ = true ∧ σ ∘ Sum.inl = v) ↔
      (tseitinSatCNF (List.ofFn v) n (A.deMorganCode 0).gates
        (A.deMorganCode 0).output).Satisfiable := by
  rw [satisfiable_tseitinSatCNF_iff (isCodeFrom_deMorganCode A 0) (by simp)
    (by simpa using output_deMorganCode_lt A 0)]
  refine ⟨?_, ?_⟩
  · rintro ⟨σ, hσ, rfl⟩
    exact ⟨List.ofFn _, by simp, List.prefix_refl _,
      (evalOutput_deMorganCode A _).trans ((eval_tseitinCNF_eq_true_iff σ A).1 hσ).1⟩
  · rintro ⟨y, hy, hpre, hout⟩
    obtain rfl := hpre.eq_of_length (by simp [hy])
    rw [evalOutput_deMorganCode] at hout
    exact ⟨tseitinExtend v, (eval_tseitinCNF_tseitinExtend v A).trans hout, rfl⟩

end Cslib.Logic.PL.Proposition
