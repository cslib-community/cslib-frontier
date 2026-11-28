/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.RealArithmetic
public import CslibFrontier.Computability.Complexity.Reduction
import CslibFrontier.Computability.Complexity.CookLevin.Completeness
import CslibFrontier.Computability.Complexity.Problems.SAT.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Sum

/-!
# Real complexity classes defined by polynomial-time reductions

`ExistsReal enc` and `ExistsForallReal enc` are the polynomial-time many-one downward
closures of ETR and existential–universal real truth. Reductions are total on source
instances. Specializing to raw bitstrings recovers the classes in `edemaine/lean-canny`'s
formal abstract at `970f28a5ecefc1327402ade16c068aa4b1b2c183`.
Hardness and completeness use `PolyTimeHard` and `PolyTimeComplete` directly.
This module provides the class definitions and the lower bounds `NP ⊆ ∃ℝ ⊆ ∃∀ℝ`; their
counting-hierarchy upper bounds are separate.

`NP ⊆ ∃ℝ` says that ETR is NP-hard, which is standard. The proof reduces `SAT`, which is
NP-hard by Cook–Levin: a literal `(v, b)` becomes `x = 0` when `b` holds and `x ≠ 0` otherwise,
where the coordinate `x` numbers `v` by its first occurrence, so that the unary variable ranks
of the ETR word stay below the number of literals. ETR's Boolean connectives make constraints
`x (x - 1) = 0` unnecessary. For `∃ℝ ⊆ ∃∀ℝ`, an ETR word is a two-block sentence with an empty
universal block and an existential block as long as the word.

## Main definitions

* `Cslib.Complexity.ExistsReal`: problems reducible to existential real truth.
* `Cslib.Complexity.ExistsForallReal`: problems reducible to two-block real truth.

## Main results

* `Cslib.Complexity.NP_subset_ExistsReal`: every NP problem reduces to ETR.
* `Cslib.Complexity.ExistsReal_subset_ExistsForallReal`: ETR reduces to two-block real truth.
-/

public section
namespace Cslib.Complexity

open Turing.MultiTapeTM

/-- Problems polynomial-time many-one reducible to the encoded ETR language. -/
@[expose] def ExistsReal {α : Type} (enc : α ↪ List Bool) : Set (Set α) :=
  {L | PolyTimeReducible enc encBits L ETR}

/-- Problems polynomial-time many-one reducible to encoded existential–universal real truth. -/
@[expose] def ExistsForallReal {α : Type} (enc : α ↪ List Bool) : Set (Set α) :=
  {L | PolyTimeReducible enc encBits L ExistsForallTheory}

/-! ### `NP ⊆ ∃ℝ` -/

section NPHard

open Cslib.Logic.PL Cslib.Logic.RealArithmetic

/-- The real formula of a literal `(v, b)` under a coordinate map `ρ`: `x_{ρ v} = 0` when `b`
holds, and its negation otherwise. -/
private def literalFormula {n : ℕ} (ρ : ℕ → Fin n) (l : Literal ℕ) : Formula n :=
  if l.2 then .eqZero (.var (ρ l.1)) else .not (.eqZero (.var (ρ l.1)))

/-- The real formula of a CNF formula: conjunctions of disjunctions of literal formulas. -/
private def cnfFormula {n : ℕ} (ρ : ℕ → Fin n) (φ : CNF ℕ) : Formula n :=
  φ.foldr (fun c acc => .and (c.foldr (fun l acc => .or (literalFormula ρ l) acc) .false) acc)
    (.not .false)

private theorem mem_solutionSet_cnfFormula {n : ℕ} (ρ : ℕ → Fin n) (φ : CNF ℕ)
    (x : Fin n → ℝ) :
    x ∈ (cnfFormula ρ φ).solutionSet ↔ φ.eval (fun v => decide (x (ρ v) = 0)) = true := by
  have hl (l : Literal ℕ) : x ∈ (literalFormula ρ l).solutionSet ↔
      Literal.eval (fun v => decide (x (ρ v) = 0)) l = true := by
    obtain ⟨v, b⟩ := l
    cases b <;> simp [literalFormula, Formula.solutionSet, Term.eval]
  induction φ with
  | nil => simp [cnfFormula, Formula.solutionSet]
  | cons c φ ih =>
    simp only [cnfFormula, List.foldr_cons] at ih ⊢
    simp only [Formula.solutionSet, Set.mem_inter_iff, ih, CNF.eval_cons, Bool.and_eq_true]
    refine and_congr_left fun _ => ?_
    induction c with
    | nil => simp [Formula.solutionSet]
    | cons l c ihc => simp only [List.foldr_cons, Formula.solutionSet, Set.mem_union, hl, ihc,
        Clause.eval_cons, Bool.or_eq_true]

/-- Number a variable by its first occurrence in `φ`. -/
private def coordinate (φ : CNF ℕ) (v : ℕ) : Fin (φ.vars.length + 1) :=
  ⟨φ.vars.idxOf v, Nat.lt_succ_of_le List.idxOf_le_length⟩

private theorem solutionSet_nonempty_cnfFormula (φ : CNF ℕ) :
    (cnfFormula (coordinate φ) φ).solutionSet.Nonempty ↔ φ ∈ SAT := by
  refine ⟨fun ⟨x, hx⟩ => ⟨_, (mem_solutionSet_cnfFormula _ φ x).1 hx⟩, fun ⟨σ, hσ⟩ => ?_⟩
  refine ⟨fun i => bif σ (φ.vars.getD i 0) then 0 else 1,
    (mem_solutionSet_cnfFormula _ φ _).2 ((CNF.eval_congr fun v hv => ?_).trans hσ)⟩
  have hlt := List.idxOf_lt_length_iff.2 hv
  simp only [coordinate, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt,
    Option.getD_some, List.getElem_idxOf hlt]
  cases σ v <;> simp

/-- The word of the term `x_i`: one framed variable token with unary rank `i`. -/
private def variableWord (i : ℕ) : List Bool := encList encTermToken [.inr (.inl i)]

private theorem encTerm_var {n : ℕ} (i : Fin n) : encTerm n (.var i) = variableWord i := by
  simp [encTerm_apply, encTerm_tokens, variableWord, encTermToken,
    EncodingPolicy.BinaryIntUnaryFin.fin, encFinEnum_fin_apply]

/-- Prefix tokens of `literalFormula`, with variable ranks given by `r`. -/
private def literalTokens (r : ℕ → ℕ) (l : Literal ℕ) : List FormulaToken :=
  if l.2 then [.inr (.inl (variableWord (r l.1)))]
  else [.inr (.inr (.inr (.inl ()))), .inr (.inl (variableWord (r l.1)))]

/-- Prefix tokens of a clause's disjunction, with variable ranks given by `r`. -/
private def clauseTokens (r : ℕ → ℕ) (c : Clause ℕ) : List FormulaToken :=
  (c.flatMap fun l => .inr (.inr (.inr (.inr (.inr ())))) :: literalTokens r l) ++ [.inl ()]

/-- Prefix tokens of `cnfFormula`, with variable ranks given by `r`. -/
private def cnfTokens (r : ℕ → ℕ) (φ : CNF ℕ) : List FormulaToken :=
  φ.flatMap (fun c => .inr (.inr (.inr (.inr (.inl ())))) :: clauseTokens r c) ++
    [.inr (.inr (.inr (.inl ()))), .inl ()]

private theorem encFormula_tokens_cnfFormula {n : ℕ} (ρ : ℕ → Fin n) (φ : CNF ℕ) :
    (encFormula_tokens n (cnfFormula ρ φ)).map FormulaToken.encodeTerms =
      cnfTokens (fun v => ρ v) φ := by
  have hl (l : Literal ℕ) : (encFormula_tokens n (literalFormula ρ l)).map
      FormulaToken.encodeTerms = literalTokens (fun v => ρ v) l := by
    obtain ⟨v, b⟩ := l
    cases b <;> simp only [literalFormula, literalTokens, ite_true, ite_false, Bool.false_eq_true,
      encFormula_tokens, List.map_cons, List.map_nil, List.append_nil, FormulaToken.encodeTerms,
      Sum.map_inl, Sum.map_inr, encTerm_var, id]
  have hc (c : Clause ℕ) : (encFormula_tokens n
      (c.foldr (fun l acc => .or (literalFormula ρ l) acc) .false)).map FormulaToken.encodeTerms =
      clauseTokens (fun v => ρ v) c := by
    induction c with
    | nil => rfl
    | cons l c ih =>
      simp only [clauseTokens, List.foldr_cons, List.flatMap_cons] at ih ⊢
      simp only [encFormula_tokens, List.map_cons, List.map_append, hl, ih, List.append_assoc]
      rfl
  induction φ with
  | nil => rfl
  | cons c φ ih =>
    simp only [cnfFormula, cnfTokens, List.foldr_cons, List.flatMap_cons] at ih ⊢
    simp only [encFormula_tokens, List.map_cons, List.map_append, hc, ih, List.append_assoc]
    rfl

private theorem computableInPolyTime_variableWord :
    ComputableInPolyTime variableWord encUnary encBits :=
  ComputableInPolyTime.encoding_comp (output := encList encTermToken)
    (f := fun k : ℕ => [(.inr (.inl k) : TermToken)]) (by fun_prop)

private theorem computableInPolyTime_literalTokens {γ : Type} {input : γ ↪ List Bool}
    {φ : γ → CNF ℕ} {l : γ → Literal ℕ} (hφ : ComputableInPolyTime φ input encCNF)
    (hl : ComputableInPolyTime l input (encPair encNat encBool)) :
    ComputableInPolyTime (fun x => literalTokens ((φ x).vars.idxOf ·) (l x)) input
      (encList encFormulaToken) := by
  have hword : ComputableInPolyTime (fun x => variableWord ((φ x).vars.idxOf (l x).1)) input
      encBits :=
    computableInPolyTime_variableWord.comp (ComputableInPolyTime.idxOfWithInput (by fun_prop)
      (by fun_prop))
  unfold literalTokens
  fun_prop

private theorem computableInPolyTime_cnfTokens :
    ComputableInPolyTime (fun φ : CNF ℕ => cnfTokens (φ.vars.idxOf ·) φ) encCNF
      (encList encFormulaToken) := by
  have hlit : ComputableInPolyTime
      (fun q : (CNF ℕ × Clause ℕ) × Literal ℕ => literalTokens (q.1.1.vars.idxOf ·) q.2)
      (encPair (encPair encCNF (encList (encPair encNat encBool))) (encPair encNat encBool))
      (encList encFormulaToken) :=
    computableInPolyTime_literalTokens (by fun_prop) (by fun_prop)
  unfold cnfTokens clauseTokens
  fun_prop

/-- The polynomial-time reduction from `SAT` to `ETR` (standard): a literal `(v, b)` becomes
`x_v = 0` or `x_v ≠ 0` according to `b`, with variables numbered by first occurrence. -/
private theorem polyTimeReducible_SAT_ETR : PolyTimeReducible encCNF encBits SAT ETR := by
  refine ⟨fun φ => encList encFormulaToken (cnfTokens (φ.vars.idxOf ·) φ),
    computableInPolyTime_cnfTokens.of_enc_eq fun _ => rfl, fun φ => ?_⟩
  have hword : encList encFormulaToken (cnfTokens (φ.vars.idxOf ·) φ) =
      encFormula _ (cnfFormula (coordinate φ) φ) := by
    rw [← (formulaTokensDecoder.decode_eq_some_iff _ _).1
      (formulaTokensDecoder_decode_encFormula _), encFormula_tokens_cnfFormula]
    rfl
  change φ ∈ SAT ↔ encList encFormulaToken (cnfTokens (φ.vars.idxOf ·) φ) ∈ ETR
  rw [hword, encFormula_mem_ETR, solutionSet_nonempty_cnfFormula]

/-- **`NP ⊆ ∃ℝ`**: every problem in `NP`, under any encoding, reduces in polynomial time to
ETR; equivalently, ETR is `NP`-hard (standard). The proof composes Cook–Levin with a reduction
from `SAT` that writes a literal `(v, b)` as `x = 0` or `x ≠ 0` according to `b`. -/
theorem NP_subset_ExistsReal {α : Type} {enc : α ↪ List Bool} : NP enc ⊆ ExistsReal enc :=
  fun A hA => (CookLevin.SAT_npHard enc A hA).trans polyTimeReducible_SAT_ETR

end NPHard

/-! ### `∃ℝ ⊆ ∃∀ℝ` -/

section ExistsForall

open Cslib.Logic.RealArithmetic

/-- ETR reduces to two-block real truth: a word becomes the sentence with an existential block
as long as the word and an empty universal block. -/
private theorem polyTimeReducible_ETR_ExistsForallTheory :
    PolyTimeReducible encBits encBits ETR ExistsForallTheory := by
  refine ⟨fun w => encPair encUnary encBits (w.length, w),
    (ComputableInPolyTime.length_bits.prod .id').of_enc_eq fun _ => rfl, fun w => ?_⟩
  constructor
  · intro hw
    obtain ⟨n, p, -, hp⟩ := Set.mem_iUnion.mp hw
    have hword : encFormula (w.length + 0) (Formula.ofWord w) = w :=
      (encFormula_ofWord w).trans <| by
        rw [normalizeFormulaWord, ite_eq_left (hp ▸ validFormulaWord_encFormula p)]
    obtain ⟨x, hx⟩ := (mem_ETR_iff_ofWord w).1 hw
    have hmem : encPair encUnary encBits (w.length, encFormula (w.length + 0) (Formula.ofWord w))
        ∈ ExistsForallTheory :=
      (encFormula_mem_ExistsForallTheory (r := w.length) (s := 0) _).2 ⟨x, fun y => ?_⟩
    · rwa [hword] at hmem
    · rwa [show Fin.addCases (motive := fun _ => ℝ) x y = x from
        funext fun i => Fin.addCases_left (n := 0) i]
  · intro hw
    obtain ⟨r, s, p, ⟨x, hx⟩, heq⟩ := Set.mem_iUnion₂.mp hw
    obtain ⟨-, rfl⟩ := Prod.mk.inj ((encPair encUnary encBits).injective heq)
    exact (encFormula_mem_ETR p).2 ⟨_, hx 0⟩

/-- **`∃ℝ ⊆ ∃∀ℝ`**: every problem reducible to ETR reduces to existential–universal real
truth, through the sentence with an empty universal block. -/
theorem ExistsReal_subset_ExistsForallReal {α : Type} {enc : α ↪ List Bool} :
    ExistsReal enc ⊆ ExistsForallReal enc :=
  fun _ hL => PolyTimeReducible.trans hL polyTimeReducible_ETR_ExistsForallTheory

end ExistsForall

end Cslib.Complexity
