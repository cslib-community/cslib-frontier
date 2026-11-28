/-
Copyright (c) 2026 Samuel Schlesinger, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.IP.TQBF.Protocol
import CslibFrontier.Probability.PMF.Bind
import Mathlib.Algebra.Polynomial.Roots

/-!
# The interactive proof for quantified Boolean formulas, on a stream of tokens

A machine running the verifier of `Cslib.Complexity.QBFProtocol.verify` reads the arithmetic
formula as a list of tokens in prefix order (`Cslib.Logic.PL.ArithQBF.tokens`): the claims it has
still to check form a stack, and the claim on top of the stack is about the subformula whose tokens
start the remaining list. The arithmetization of a quantified Boolean formula `φ` has as tokens
those of `φ`, with the linearizations of the variables of `xs` inserted before every quantifier
(`Cslib.Logic.PL.QBF.tokens_arithmetize`).

This file gives the recursive form of that machine (`Cslib.Complexity.QBFProtocol.verifyAt`).
It differs from `Cslib.Complexity.QBFProtocol.verify` in two ways: it reads the same number
`D + 1` of coefficients in every round, so that it need not compute the degree of each body, and
its queries also carry the tokens that follow the current subformula, so that they determine the
remaining list of tokens of the machine. Its soundness bound uses the uniform degree: if the
syntactic largest round degree `maxRoundDegree e` is at most `D`, every prover is accepted on a
false claim with probability at most `ops e * D * ε` instead of `roundDegree e * ε`
(`Cslib.Complexity.QBFProtocol.acceptProb_verifyAt_le`), with `ops e` the number of operators. A
stateless prover whose replies agree with the true values and restrictions on every query about a
subformula all of whose variables lie in a list `xs` is accepted with certainty on every true
claim about a formula whose variables lie in `xs` and whose largest round degree
`maxRoundDegree e` is at most `D` (`Cslib.Complexity.QBFProtocol.run_verifyAt_of_agreesAt`).

## Main definitions

* `Cslib.Logic.PL.ArithQBF.Kind`, `Cslib.Logic.PL.ArithQBF.tokens`: the tokens of an arithmetic
  formula.
* `Cslib.Logic.PL.QBF.expandToken`: the tokens of the arithmetization for a token of a formula.
* `Cslib.Complexity.QBFProtocol.verifyAt`: the verifier with uniform degree and contextual queries.
* `Cslib.Complexity.QBFProtocol.honestReplyAt`: the honest replies.
* `Cslib.Complexity.QBFProtocol.IsChild`, `Cslib.Complexity.QBFProtocol.IsSub`: the children and
  the subformulas of a formula.
* `Cslib.Complexity.QBFProtocol.firstLen`: where the first formula of a list of tokens ends.

## Main results

* `Cslib.Logic.PL.ArithQBF.tokens_append_inj`: tokens in prefix order determine the formula.
* `Cslib.Logic.PL.QBF.tokens_arithmetize`: the tokens of the arithmetization.
* `Cslib.Complexity.QBFProtocol.exists_isSub_drop_tokens`: every suffix of the tokens begins with
  the tokens of a subformula.
* `Cslib.Complexity.QBFProtocol.firstLen_tokens_append`: the first formula of a list of tokens ends
  where its own tokens end.
* `Cslib.Complexity.QBFProtocol.acceptProb_verifyAt_le`: soundness.
* `Cslib.Complexity.QBFProtocol.run_verifyAt_of_agreesAt_of_closed`: perfect completeness from a
  family of queries closed under taking children.
* `Cslib.Complexity.QBFProtocol.run_verifyAt_of_agreesAt`: perfect completeness.

## References

* [A. Shamir, *IP = PSPACE*][Shamir1992]
* [A. Shen, *IP = SPACE: simplified proof*][Shen1992]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Logic.PL

/-! ### Tokens -/

/-- The kinds of nodes of an arithmetic formula. -/
inductive ArithQBF.Kind where
  /-- A variable. -/
  | var
  /-- The constant `1`. -/
  | top
  /-- The constant `0`. -/
  | bot
  /-- Negation. -/
  | not
  /-- Conjunction. -/
  | and
  /-- Disjunction. -/
  | or
  /-- Existential quantification. -/
  | ex
  /-- Universal quantification. -/
  | all
  /-- Linearization. -/
  | lin
  deriving DecidableEq

instance : Fintype ArithQBF.Kind :=
  ⟨{.var, .top, .bot, .not, .and, .or, .ex, .all, .lin}, fun k => by cases k <;> simp⟩

namespace ArithQBF

/-- The tokens of an arithmetic formula in prefix order: the kind of each node, with its variable
for variables and operators, and `0` for the other nodes. -/
def tokens : ArithQBF ℕ → List (Kind × ℕ)
  | .var v => [(.var, v)]
  | .top => [(.top, 0)]
  | .bot => [(.bot, 0)]
  | .not e => (.not, 0) :: tokens e
  | .bin .and e₁ e₂ => (.and, 0) :: (tokens e₁ ++ tokens e₂)
  | .bin .or e₁ e₂ => (.or, 0) :: (tokens e₁ ++ tokens e₂)
  | .op .ex v e => (.ex, v) :: tokens e
  | .op .all v e => (.all, v) :: tokens e
  | .op .lin v e => (.lin, v) :: tokens e

/-- Interpret an arithmetic-formula token as its constructor, rejecting nonzero payloads on
constants and connectives. -/
def readToken : Kind × ℕ → Option (Cslib.PrefixParser.Step (ArithQBF ℕ))
  | (.var, v) => some (.atom (.var v))
  | (.top, 0) => some (.atom .top)
  | (.bot, 0) => some (.atom .bot)
  | (.not, 0) => some (.unary .not)
  | (.and, 0) => some (.binary (.bin .and))
  | (.or, 0) => some (.binary (.bin .or))
  | (.ex, v) => some (.unary (.op .ex v))
  | (.all, v) => some (.unary (.op .all v))
  | (.lin, v) => some (.unary (.op .lin v))
  | _ => none

/-- Parsing an arithmetic formula's tokens recovers it and leaves the suffix untouched. -/
theorem parseFuel_tokens (e : ArithQBF ℕ) (rest : List (Kind × ℕ)) (fuel : ℕ)
    (hf : e.tokens.length ≤ fuel) :
    Cslib.PrefixParser.parseFuel readToken fuel (e.tokens ++ rest) = some (e, rest) := by
  induction e generalizing fuel rest with
  | var _ | top | bot =>
    cases fuel <;> simp_all [tokens, Cslib.PrefixParser.parseFuel, readToken]
  | not e ih =>
    cases fuel with
    | zero => simp [tokens] at hf
    | succ fuel =>
      simp only [tokens, List.length_cons] at hf
      simp only [tokens, List.cons_append, Cslib.PrefixParser.parseFuel, readToken]
      rw [ih rest fuel (Nat.le_of_succ_le_succ hf)]
      rfl
  | bin op e₁ e₂ ih₁ ih₂ =>
    cases fuel with
    | zero => cases op <;> simp [tokens] at hf
    | succ fuel =>
      cases op <;> simp only [tokens, List.length_cons, List.length_append] at hf ⊢ <;>
        simp only [List.cons_append, List.append_assoc, Cslib.PrefixParser.parseFuel, readToken] <;>
        rw [ih₁ (e₂.tokens ++ rest) fuel
          (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_of_succ_le_succ hf))] <;>
        dsimp only [Bind.bind, Option.bind] <;>
        rw [ih₂ rest fuel
          (Nat.le_trans (Nat.le_add_left _ _) (Nat.le_of_succ_le_succ hf))] <;> rfl
  | op op _ e ih =>
    cases fuel with
    | zero => cases op <;> simp [tokens] at hf
    | succ fuel =>
      cases op <;> simp only [tokens, List.length_cons] at hf ⊢ <;>
        simp only [List.cons_append, Cslib.PrefixParser.parseFuel, readToken] <;>
        rw [ih rest fuel (Nat.le_of_succ_le_succ hf)] <;> rfl

/-- **Tokens in prefix order determine the formula**, and what follows them. -/
theorem tokens_append_inj {e e' : ArithQBF ℕ} {r r' : List (Kind × ℕ)}
    (h : e.tokens ++ r = e'.tokens ++ r') : e = e' ∧ r = r' :=
  Cslib.PrefixParser.append_injective parseFuel_tokens h

private theorem tokens_lins (xs : List ℕ) (e : ArithQBF ℕ) :
    (lins xs e).tokens = xs.map (fun x => (Kind.lin, x)) ++ e.tokens := by
  induction xs with
  | nil => rfl
  | cons x xs ih => rw [lins_cons, tokens, ih, List.map_cons, List.cons_append]

end ArithQBF

namespace QBF

/-- The kind of the node of the arithmetization for a node of a quantified Boolean formula. -/
def Kind.arith : Kind → ArithQBF.Kind
  | .var => .var
  | .top => .top
  | .bot => .bot
  | .not => .not
  | .and => .and
  | .or => .or
  | .ex => .ex
  | .all => .all

/-- The tokens of the arithmetization for a token of a formula: a quantifier is preceded by the
linearizations of the variables of `xs`. -/
def expandToken (xs : List ℕ) (t : Kind × ℕ) : List (ArithQBF.Kind × ℕ) :=
  (if t.1.isQuantifier then xs.map fun x => (ArithQBF.Kind.lin, x) else []) ++ [(t.1.arith, t.2)]

/-- **The tokens of the arithmetization** are those of the formula, with the linearizations of
the variables of `xs` inserted before every quantifier. -/
theorem tokens_arithmetize (xs : List ℕ) (φ : QBF ℕ) :
    (φ.arithmetize xs).tokens = φ.tokens.flatMap (expandToken xs) := by
  induction φ <;> simp [arithmetize, ArithQBF.tokens, ArithQBF.tokens_lins, tokens, expandToken,
    Kind.isQuantifier, Kind.arith, *]

end QBF

end Cslib.Logic.PL

namespace Cslib.Logic.PL.ArithQBF.Kind

/-- The number of arguments of a node of an arithmetic formula. -/
def arity : ArithQBF.Kind → ℕ
  | .var | .top | .bot => 0
  | .not | .ex | .all | .lin => 1
  | .and | .or => 2

end Cslib.Logic.PL.ArithQBF.Kind

namespace Cslib.Complexity.QBFProtocol

open Cslib.Logic.PL Polynomial
open Cslib.ProbOracleComp (runWith acceptProbWith)
open scoped ENNReal

variable {F : Type}

/-! ### The verifier on a stream of tokens -/

/-- A query of the verifier on a stream of tokens. -/
structure QueryAt (F : Type) where
  /-- The current subformula. -/
  formula : ArithQBF ℕ
  /-- The tokens that follow the current subformula. -/
  rest : List (ArithQBF.Kind × ℕ)
  /-- The current point. -/
  point : ℕ → F

variable [CommRing F] [DecidableEq F] (sampler : ProbComp F) (D : ℕ)

/-- **The verifier on a stream of tokens**, checking the claim that `e`, followed by the tokens
`rest`, has value `c` at `r`. It is `Cslib.Complexity.QBFProtocol.verify` with `D + 1`
coefficients read in every round and with the tokens `rest` sent along with every query. -/
def verifyAt : ArithQBF ℕ → List (ArithQBF.Kind × ℕ) → (ℕ → F) → F →
    ProbOracleComp (fun _ : QueryAt F => List F) Bool
  | .var v, _, r, c => pure (decide (r v = c))
  | .top, _, _, c => pure (decide (c = 1))
  | .bot, _, _, c => pure (decide (c = 0))
  | .not e, rest, r, c => verifyAt e rest r (1 - c)
  | .bin o e₁ e₂, rest, r, c => do
    let l ← ProbOracleComp.query (spec := fun _ : QueryAt F => List F) ⟨.bin o e₁ e₂, rest, r⟩
    if o.apply (l.getD 0 0) (l.getD 1 0) = c then
      let b ← verifyAt e₁ (e₂.tokens ++ rest) r (l.getD 0 0)
      if b then verifyAt e₂ rest r (l.getD 1 0) else pure false
    else pure false
  | .op o v e, rest, r, c => do
    let l ← ProbOracleComp.query (spec := fun _ : QueryAt F => List F) ⟨.op o v e, rest, r⟩
    let s := l.take (D + 1)
    if o.apply (r v) (evalCoeffList 0 s) (evalCoeffList 1 s) = c then
      let z ← ProbOracleComp.sample sampler
      verifyAt e rest (Function.update r v z) (evalCoeffList z s)
    else pure false

/-! ### Soundness -/

/-- **Soundness of the verifier on a stream of tokens**: if the sampler gives every element
probability at most `ε` and the body of every operator of `e` has degree at most `D` in its
variable, every prover is accepted on a false claim with probability at most `ops e * D * ε`. -/
theorem acceptProb_verifyAt_le [IsDomain F] {ε : ℝ≥0∞}
    (hsampler : ∀ z, ProbComp.eval sampler z ≤ ε) {S : Type}
    (respond : QueryAt F → StateT S PMF (List F)) (e : ArithQBF ℕ) (hD : e.maxRoundDegree ≤ D)
    {rest : List (ArithQBF.Kind × ℕ)} {r : ℕ → F} {c : F} (hc : e.eval r ≠ c) (s : S) :
    acceptProbWith respond (verifyAt sampler D e rest r c) s ≤ (e.ops * D : ℕ) * ε := by
  induction e generalizing rest r c s with
  | var v =>
    rw [verifyAt, decide_eq_false (show r v ≠ c from hc), ProbOracleComp.acceptProbWith_pure]
    exact zero_le
  | top =>
    rw [verifyAt, decide_eq_false (show c ≠ 1 from Ne.symm hc), ProbOracleComp.acceptProbWith_pure]
    exact zero_le
  | bot =>
    rw [verifyAt, decide_eq_false (show c ≠ 0 from Ne.symm hc), ProbOracleComp.acceptProbWith_pure]
    exact zero_le
  | not e ih =>
    rw [verifyAt, ArithQBF.ops]
    exact ih hD (fun h => hc (by rw [ArithQBF.eval_not, h, sub_sub_cancel])) s
  | bin o e₁ e₂ ih₁ ih₂ =>
    rw [ArithQBF.maxRoundDegree, max_le_iff] at hD
    rw [verifyAt, ArithQBF.ops, Nat.add_mul, Nat.cast_add, add_mul]
    refine acceptProbWith_query_ite_le respond _ _ (fun l hcheck s => ?_) s
    refine acceptProbWith_bind_ite_le_add respond ?_ s
    by_cases h₁ : e₁.eval r = l.getD 0 0
    · exact .inr (ih₂ hD.2 fun h₂ => hc (by rw [ArithQBF.eval_bin, h₁, h₂, hcheck]))
    · exact .inl (ih₁ hD.1 h₁)
  | op o v e ih =>
    rw [ArithQBF.maxRoundDegree, max_le_iff] at hD
    rw [verifyAt]
    refine (acceptProbWith_query_ite_le respond _ _ (fun l hcheck s => ?_) s).trans_eq
      (by rw [ArithQBF.ops, Nat.add_one_mul, Nat.cast_add, add_mul, add_comm])
    set L := l.take (D + 1)
    have hL (z : F) : evalCoeffList z L = (ofCoeffList L).eval z := (eval_ofCoeffList z _).symm
    have hg (z : F) := e.eval_restrict r v z
    refine acceptProbWith_sample_le sampler respond hsampler (p := ofCoeffList L)
      (g := e.restrict r v) (fun h => hc ?_) ((natDegree_ofCoeffList_le L).trans (by
        rw [List.length_take]; omega)) ((e.natDegree_restrict_le r v).trans hD.1) fun z hz => ?_
    · rw [ArithQBF.eval_op, ← hg, ← hg, ← h, ← hL, ← hL, hcheck]
    · rw [hL]
      exact ih hD.2 (fun h => hz (by rw [hg, h])) s

/-! ### Completeness -/

/-- The honest reply to a query about `e` at `r`: the values of the two arguments of a binary
connective, and the `D + 1` first coefficients of the restriction of the body of an operator. -/
noncomputable def honestReplyAt (e : ArithQBF ℕ) (r : ℕ → F) : List F :=
  match e with
  | .bin _ e₁ e₂ => [e₁.eval r, e₂.eval r]
  | .op _ v e => coeffsBelow (e.restrict r v) (D + 1)
  | _ => []

/-- A reply agrees with the honest reply to a query about `e` at `r` on what the verifier reads:
the first two entries for a binary connective, the first `D + 1` for an operator. -/
def AgreesAt (l : List F) (e : ArithQBF ℕ) (r : ℕ → F) : Prop :=
  match e with
  | .bin _ e₁ e₂ => l.getD 0 0 = e₁.eval r ∧ l.getD 1 0 = e₂.eval r
  | .op _ v e => l.take (D + 1) = coeffsBelow (e.restrict r v) (D + 1)
  | _ => True

omit [DecidableEq F] in
theorem agreesAt_honestReplyAt (e : ArithQBF ℕ) (r : ℕ → F) :
    AgreesAt D (honestReplyAt D e r) e r := by
  cases e with
  | bin o e₁ e₂ => exact ⟨rfl, rfl⟩
  | op o v e => exact List.take_of_length_le (by rw [honestReplyAt, length_coeffsBelow])
  | _ => trivial

/-- **Perfect completeness of the verifier on a stream of tokens, from a closed family of
queries.** Let `P e rest` be a property of a subformula and the tokens that follow it that passes
from a node to its children (`hnot`, `hbin`, `hop`). A stateless prover whose reply to every query
satisfying `P` agrees with the honest reply makes the verifier accept with certainty every true
claim `P e rest` about a formula whose operators have bodies of degree at most `D` in their
variable. -/
theorem run_verifyAt_of_agreesAt_of_closed (f : QueryAt F → List F)
    (P : ArithQBF ℕ → List (ArithQBF.Kind × ℕ) → Prop)
    (hnot : ∀ e rest, P (.not e) rest → P e rest)
    (hbin : ∀ o e₁ e₂ rest, P (.bin o e₁ e₂) rest → P e₁ (e₂.tokens ++ rest) ∧ P e₂ rest)
    (hop : ∀ o v e rest, P (.op o v e) rest → P e rest)
    (hf : ∀ q : QueryAt F, P q.formula q.rest → AgreesAt D (f q) q.formula q.point)
    (e : ArithQBF ℕ) (hD : e.maxRoundDegree ≤ D) (rest : List (ArithQBF.Kind × ℕ))
    (he : P e rest) (r : ℕ → F) (s : Unit) :
    runWith (fun q s => PMF.pure (f q, s)) (verifyAt sampler D e rest r (e.eval r)) s =
      PMF.pure (true, s) := by
  induction e generalizing rest r with
  | var _ | top | bot =>
    simp only [verifyAt, ArithQBF.eval_var, ArithQBF.eval_top, ArithQBF.eval_bot, decide_true,
      ProbOracleComp.runWith_pure]
  | not e ih => rw [verifyAt, ArithQBF.eval_not, sub_sub_cancel, ih hD rest (hnot _ _ he) r]
  | bin o e₁ e₂ ih₁ ih₂ =>
    rw [ArithQBF.maxRoundDegree, max_le_iff] at hD
    obtain ⟨he₁, he₂⟩ := hbin o e₁ e₂ rest he
    obtain ⟨h₁, h₂⟩ := hf ⟨.bin o e₁ e₂, rest, r⟩ he
    rw [verifyAt, ProbOracleComp.runWith_bind, ProbOracleComp.runWith_query]
    simp only [PMF.pure_bind, h₁, h₂, ArithQBF.eval_bin, ↓reduceIte]
    rw [ProbOracleComp.runWith_bind, ih₁ hD.1 _ he₁ r, PMF.pure_bind]
    exact ih₂ hD.2 _ he₂ r
  | op o v e ih =>
    rw [ArithQBF.maxRoundDegree, max_le_iff] at hD
    have hlist : (f ⟨.op o v e, rest, r⟩).take (D + 1) = coeffsBelow (e.restrict r v) (D + 1) :=
      hf ⟨.op o v e, rest, r⟩ he
    rw [verifyAt, ProbOracleComp.runWith_bind, ProbOracleComp.runWith_query]
    have hval (z : F) : evalCoeffList z (coeffsBelow (e.restrict r v) (D + 1)) =
        e.eval (Function.update r v z) := by
      rw [← eval_ofCoeffList, ofCoeffList_coeffsBelow (Nat.lt_succ_of_le
        ((e.natDegree_restrict_le r v).trans hD.1)), ArithQBF.eval_restrict]
    simp only [PMF.pure_bind, hlist, hval, ArithQBF.eval_op, ↓reduceIte]
    rw [ProbOracleComp.runWith_bind, ProbOracleComp.runWith_sample, PMF.bind_map]
    simp only [Function.comp_def, ih hD.2 rest (hop _ _ _ _ he)]
    exact PMF.bind_const _ _

/-- **Perfect completeness of the verifier on a stream of tokens.** A stateless prover whose reply
to every query about a subformula all of whose variables lie in `xs` agrees with the honest reply
makes the verifier accept with certainty every true claim about a formula whose variables lie in
`xs` and whose operators have bodies of degree at most `D` in their variable. -/
theorem run_verifyAt_of_agreesAt (f : QueryAt F → List F) (xs : List ℕ)
    (hf : ∀ q : QueryAt F, (∀ w ∈ q.formula.vars, w ∈ xs) → AgreesAt D (f q) q.formula q.point)
    (e : ArithQBF ℕ) (he : ∀ w ∈ e.vars, w ∈ xs) (hD : e.maxRoundDegree ≤ D)
    (rest : List (ArithQBF.Kind × ℕ)) (r : ℕ → F) (s : Unit) :
    runWith (fun q s => PMF.pure (f q, s)) (verifyAt sampler D e rest r (e.eval r)) s =
      PMF.pure (true, s) :=
  run_verifyAt_of_agreesAt_of_closed sampler D f (fun e _ => ∀ w ∈ e.vars, w ∈ xs)
    (fun _ _ h => h) (fun _ _ _ _ h =>
      ⟨fun w hw => h w (List.mem_append_left _ hw), fun w hw => h w (List.mem_append_right _ hw)⟩)
    (fun _ v _ _ h w hw => h w (List.mem_cons_of_mem v hw)) hf e hD rest he r s

/-! ### Children and subformulas -/

/-- `e'` is a child of `e`: the argument of a negation, one argument of a binary connective, or
the body of an operator. -/
inductive IsChild : ArithQBF ℕ → ArithQBF ℕ → Prop
  /-- The argument of a negation. -/
  | not (e : ArithQBF ℕ) : IsChild e e.not
  /-- The first argument of a binary connective. -/
  | bin_left (o : ArithQBF.Connective) (e₁ e₂ : ArithQBF ℕ) : IsChild e₁ (.bin o e₁ e₂)
  /-- The second argument of a binary connective. -/
  | bin_right (o : ArithQBF.Connective) (e₁ e₂ : ArithQBF ℕ) : IsChild e₂ (.bin o e₁ e₂)
  /-- The body of an operator. -/
  | op (o : ArithQBF.Operator) (v : ℕ) (e : ArithQBF ℕ) : IsChild e (.op o v e)

namespace IsChild

variable {e e' : ArithQBF ℕ}

/-- A child has at most as many operators as its parent. -/
theorem ops_le (h : IsChild e' e) : e'.ops ≤ e.ops := by
  cases h <;> simp only [ArithQBF.ops] <;> omega

/-- A child has round degrees at most those of its parent. -/
theorem maxRoundDegree_le (h : IsChild e' e) : e'.maxRoundDegree ≤ e.maxRoundDegree := by
  cases h <;> simp only [ArithQBF.maxRoundDegree, le_max_iff, le_refl, true_or, or_true]

/-- The variables of a child are variables of its parent. -/
theorem vars_subset (h : IsChild e' e) : ∀ w ∈ e'.vars, w ∈ e.vars := by
  intro w hw
  cases h <;> simp_all [ArithQBF.vars]

/-- The tokens of a child are a strictly shorter sublist of the tokens of the formula. -/
theorem tokens_sublist (h : IsChild e' e) :
    e'.tokens.Sublist e.tokens ∧ e'.tokens.length < e.tokens.length := by
  cases h with
  | not e => exact ⟨(List.sublist_cons_self _ _), by simp [ArithQBF.tokens]⟩
  | bin_left o e₁ e₂ =>
    cases o <;> exact ⟨(List.sublist_append_left _ _).cons _, by simp [ArithQBF.tokens]⟩
  | bin_right o e₁ e₂ =>
    cases o <;> exact ⟨(List.sublist_append_right _ _).cons _, by simp [ArithQBF.tokens]⟩
  | op o v e =>
    cases o <;> exact ⟨List.sublist_cons_self _ _, by simp [ArithQBF.tokens]⟩

end IsChild

/-- `e'` is a subformula of `e`: it is reached from `e` by taking arguments and bodies. -/
abbrev IsSub : ArithQBF ℕ → ArithQBF ℕ → Prop := Relation.ReflTransGen IsChild

namespace IsSub

variable {e e' : ArithQBF ℕ}

/-- A subformula has at most as many operators as the formula. -/
theorem ops_le : Relation.ReflTransGen IsChild e' e → e'.ops ≤ e.ops := by
  intro h
  induction h with
  | refl => exact le_rfl
  | tail _ hc ih => exact ih.trans hc.ops_le

/-- A subformula has round degrees at most those of the formula. -/
theorem maxRoundDegree_le :
    Relation.ReflTransGen IsChild e' e → e'.maxRoundDegree ≤ e.maxRoundDegree := by
  intro h
  induction h with
  | refl => exact le_rfl
  | tail _ hc ih => exact ih.trans hc.maxRoundDegree_le

/-- The variables of a subformula are variables of the formula. -/
theorem vars_subset : Relation.ReflTransGen IsChild e' e → ∀ w ∈ e'.vars, w ∈ e.vars := by
  intro h
  induction h with
  | refl => exact fun _ hw => hw
  | tail _ hc ih => exact fun w hw => hc.vars_subset w (ih w hw)

end IsSub

/-- Every formula has a token. -/
theorem _root_.Cslib.Logic.PL.ArithQBF.tokens_ne_nil (e : ArithQBF ℕ) : e.tokens ≠ [] := by
  cases e with
  | bin o _ _ => cases o <;> simp [ArithQBF.tokens]
  | op o _ _ => cases o <;> simp [ArithQBF.tokens]
  | _ => simp [ArithQBF.tokens]

/-- **Prefix notation**: every suffix of the tokens of a formula, from a position inside them,
begins with the tokens of a subformula. -/
theorem exists_isSub_drop_tokens (e : ArithQBF ℕ) {i : ℕ} (hi : i < e.tokens.length) :
    ∃ (e' : ArithQBF ℕ) (rest : List (ArithQBF.Kind × ℕ)),
      IsSub e' e ∧ e.tokens.drop i = e'.tokens ++ rest := by
  induction e generalizing i with
  | var v =>
    obtain rfl : i = 0 := by simpa [ArithQBF.tokens] using hi
    exact ⟨_, [], Relation.ReflTransGen.refl, by simp⟩
  | top =>
    obtain rfl : i = 0 := by simpa [ArithQBF.tokens] using hi
    exact ⟨_, [], Relation.ReflTransGen.refl, by simp⟩
  | bot =>
    obtain rfl : i = 0 := by simpa [ArithQBF.tokens] using hi
    exact ⟨_, [], Relation.ReflTransGen.refl, by simp⟩
  | not e ih =>
    cases i with
    | zero => exact ⟨_, [], Relation.ReflTransGen.refl, by simp⟩
    | succ j =>
      have hj : j < e.tokens.length := by simpa [ArithQBF.tokens] using hi
      obtain ⟨e', rest, hs, hd⟩ := ih hj
      exact ⟨e', rest, hs.tail (IsChild.not e), by simpa [ArithQBF.tokens] using hd⟩
  | bin o e₁ e₂ ih₁ ih₂ =>
    cases i with
    | zero => exact ⟨_, [], Relation.ReflTransGen.refl, by simp⟩
    | succ j =>
      have hlen : (ArithQBF.bin o e₁ e₂).tokens.length =
          e₁.tokens.length + e₂.tokens.length + 1 := by
        cases o <;> simp [ArithQBF.tokens]
      have key : (ArithQBF.bin o e₁ e₂).tokens.drop (j + 1) = (e₁.tokens ++ e₂.tokens).drop j := by
        cases o <;> simp [ArithQBF.tokens]
      by_cases hj : j < e₁.tokens.length
      · obtain ⟨e', rest, hs, hd⟩ := ih₁ hj
        refine ⟨e', rest ++ e₂.tokens, hs.tail (IsChild.bin_left o e₁ e₂), ?_⟩
        rw [key, List.drop_append_of_le_length hj.le, hd, List.append_assoc]
      · have hj' : j - e₁.tokens.length < e₂.tokens.length := by omega
        obtain ⟨e', rest, hs, hd⟩ := ih₂ hj'
        refine ⟨e', rest, hs.tail (IsChild.bin_right o e₁ e₂), ?_⟩
        rw [key, List.drop_append, List.drop_eq_nil_of_le (not_lt.1 hj), List.nil_append, hd]
  | op o v e ih =>
    cases i with
    | zero => exact ⟨_, [], Relation.ReflTransGen.refl, by simp⟩
    | succ j =>
      have hj : j < e.tokens.length := by cases o <;> simpa [ArithQBF.tokens] using hi
      obtain ⟨e', rest, hs, hd⟩ := ih hj
      exact ⟨e', rest, hs.tail (IsChild.op o v e), by cases o <;> simpa [ArithQBF.tokens] using hd⟩

/-- The kind of the token of a binary connective. -/
def connKind : ArithQBF.Connective → ArithQBF.Kind
  | .and => .and
  | .or => .or

/-- The kind of the token of an operator. -/
def opKind : ArithQBF.Operator → ArithQBF.Kind
  | .ex => .ex
  | .all => .all
  | .lin => .lin

/-- The tokens of a binary connective. -/
theorem tokens_bin (o : ArithQBF.Connective) (e₁ e₂ : ArithQBF ℕ) :
    (ArithQBF.bin o e₁ e₂).tokens = (connKind o, 0) :: (e₁.tokens ++ e₂.tokens) := by
  cases o <;> rfl

/-- The tokens of an operator. -/
theorem tokens_op (o : ArithQBF.Operator) (v : ℕ) (e : ArithQBF ℕ) :
    (ArithQBF.op o v e).tokens = (opKind o, v) :: e.tokens := by
  cases o <;> rfl

/-! ### Where the first formula of a list of tokens ends -/

/-- One step of the scan for the end of the first formula: with `need` formulas still to read, a
token with `a` arguments changes it to `need - 1 + a`, and the count of tokens read grows by one,
unless `need` is already `0`. -/
def firstStep (st : ℕ × ℕ) (t : ArithQBF.Kind × ℕ) : ℕ × ℕ :=
  if st.1 = 0 then st else (st.1 - 1 + t.1.arity, st.2 + 1)

/-- **Where the first complete formula of a list of tokens ends**: the number of tokens read by a
scan that starts needing one formula. -/
def firstLen (ts : List (ArithQBF.Kind × ℕ)) : ℕ := (ts.foldl firstStep (1, 0)).2

theorem firstStep_succ (n c : ℕ) (t : ArithQBF.Kind × ℕ) :
    firstStep (n + 1, c) t = (n + t.1.arity, c + 1) := by
  simp [firstStep]

theorem foldl_firstStep_tokens (e : ArithQBF ℕ) : ∀ n c : ℕ,
    e.tokens.foldl firstStep (n + 1, c) = (n, c + e.tokens.length) := by
  induction e with
  | var v => intro n c; simp [ArithQBF.tokens, firstStep_succ, ArithQBF.Kind.arity]
  | top => intro n c; simp [ArithQBF.tokens, firstStep_succ, ArithQBF.Kind.arity]
  | bot => intro n c; simp [ArithQBF.tokens, firstStep_succ, ArithQBF.Kind.arity]
  | not e ih =>
    intro n c
    simp only [ArithQBF.tokens, List.foldl_cons, firstStep_succ, ArithQBF.Kind.arity,
      List.length_cons, ih]
    congr 1; omega
  | bin o e₁ e₂ ih₁ ih₂ =>
    intro n c
    have h₁ := ih₁ (n + 1) (c + 1)
    have h₂ := ih₂ n (c + 1 + e₁.tokens.length)
    have hfold : (e₁.tokens ++ e₂.tokens).foldl firstStep (n + 1 + 1, c + 1) =
        (n, c + 1 + e₁.tokens.length + e₂.tokens.length) := by
      rw [List.foldl_append, h₁, h₂]
    cases o <;>
      simp only [ArithQBF.tokens, List.foldl_cons, firstStep_succ, ArithQBF.Kind.arity,
        List.length_cons, List.length_append] <;>
      (change List.foldl firstStep (n + 1 + 1, c + 1) _ = _) <;>
      rw [hfold] <;> (congr 1; omega)
  | op o v e ih =>
    intro n c
    cases o <;>
      simp only [ArithQBF.tokens, List.foldl_cons, firstStep_succ, ArithQBF.Kind.arity,
        List.length_cons, ih] <;>
      (congr 1; omega)

theorem foldl_firstStep_zero (rest : List (ArithQBF.Kind × ℕ)) (c : ℕ) :
    rest.foldl firstStep (0, c) = (0, c) := by
  induction rest with
  | nil => rfl
  | cons t rest ih => simpa [firstStep] using ih

/-- **The first formula of a list of tokens ends where its own tokens end**: whatever follows
them. -/
theorem firstLen_tokens_append (e : ArithQBF ℕ) (rest : List (ArithQBF.Kind × ℕ)) :
    firstLen (e.tokens ++ rest) = e.tokens.length := by
  unfold firstLen
  rw [List.foldl_append, show ((1 : ℕ), (0 : ℕ)) = (0 + 1, 0) from rfl, foldl_firstStep_tokens,
    foldl_firstStep_zero]
  simp

end Cslib.Complexity.QBFProtocol
