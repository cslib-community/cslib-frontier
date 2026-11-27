/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Alternation.TQBF
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Computability.Complexity.Classes.Alternation.Savitch
import CslibFrontier.Computability.Complexity.Classes.Inclusions
import CslibFrontier.Computability.Complexity.Classes.Space.TQBF.PolyTime
import CslibFrontier.Computability.Complexity.CookLevin.PolyTime
import CslibFrontier.Logics.Propositional.CNF.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NormalForm

/-!
# `TQBF` in alternating prenex conjunctive normal form

A quantified Boolean formula is in **alternating prenex conjunctive normal form** when it is
`∃ x₁, ∀ y₁, ⋯, ∃ xₙ, ∀ yₙ, ψ` for a formula `ψ` in conjunctive normal form
(`Cslib.Logic.PL.QBF.rounds`, `Cslib.Logic.PL.QBF.ofCNF`). `TQBFCNF` is the set of instances
`x : PrenexCNF` consisting of a list `x.rounds` of rounds `(xᵢ, yᵢ)` and a formula `x.matrix`
whose prenex formula is a true closed formula (`Cslib.Complexity.TQBF`).
The game played on such a formula is Sipser's FORMULA-GAME [Sipser, Theorem 8.11][Sipser2013],
the starting point of the textbook `PSPACE`-hardness proofs of games such as Generalized Geography
[Sipser, Theorem 8.14][Sipser2013].

`TQBFCNF` is `PSPACE`-complete (`Cslib.Complexity.TQBFCNF_pspaceComplete`): it is in `PSPACE`
because writing the formula is polynomial-time, and it is `PSPACE`-hard because the formulas of
games (`Cslib.Complexity.TQBF.gameFormula`), which every problem in `PSPACE` reduces to
(`Cslib.Complexity.exists_isGameVerifier_of_mem_PSPACE`), are already almost in this form: rounds
over the moves, then existential quantifiers over the variables of a Cook–Levin tableau and the
conjunction of the tableau with equivalences linking its certificate variables to the moves. Each
equivalence `a ↔ b` is written as the two clauses `¬a ∨ b` and `a ∨ ¬b`, and each existential
quantifier `∃ v` becomes the round `∃ v, ∀ d` over a fixed variable `d` that occurs nowhere else,
which does not change the value (`Cslib.Logic.PL.QBF.eval_rounds_map_pair`).

## Main definitions

* `Cslib.Complexity.PrenexCNF`, `Cslib.Complexity.encPrenexCNF`, `Cslib.Complexity.TQBFCNF`:
  alternating prenex CNF instances, their encoding, and the problem of true closed instances.
* `Cslib.Complexity.TQBF.prenexPairs`, `Cslib.Complexity.TQBF.prenexMatrix`,
  `Cslib.Complexity.TQBF.prenexReduce`: the formula of a game in alternating prenex conjunctive
  normal form.

## Main results

* `Cslib.Complexity.TQBF.eval_prenex`, `Cslib.Complexity.TQBF.closed_prenex`: the normal form of
  the formula of a game has its value and is closed.
* `Cslib.Complexity.TQBF.prenexReduce_mem_TQBFCNF_iff`,
  `Cslib.Complexity.TQBF.computableInPolyTime_prenexReduce`: the normal form is correct and
  polynomial-time.
* `Cslib.Complexity.TQBFCNF_mem_PSPACE`, `Cslib.Complexity.TQBFCNF_pspaceHard`,
  `Cslib.Complexity.TQBFCNF_pspaceComplete`: `TQBFCNF` is `PSPACE`-complete.

## References

* [M. Sipser, *Introduction to the Theory of Computation*, Section 8.3][Sipser2013]
* [L. Stockmeyer, A. Meyer, *Word problems requiring exponential time*][StockmeyerMeyer1973]
-/

public section

namespace Cslib.Complexity

open _root_.Turing _root_.Turing.MultiTapeTM Cslib.Logic.PL

/-- An instance of `TQBFCNF`: a list `rounds` of alternating `(∃ xᵢ, ∀ yᵢ)` variable pairs together
with a quantifier-free body `matrix` in conjunctive normal form. -/
@[ext]
structure PrenexCNF where
  /-- Alternating quantifier rounds `(x₁, y₁), …, (xₙ, yₙ)`, read as `∃ x₁, ∀ y₁, …, ∃ xₙ, ∀ yₙ`. -/
  rounds : List (ℕ × ℕ)
  /-- The quantifier-free body `ψ` in conjunctive normal form. -/
  matrix : CNF ℕ
  deriving DecidableEq

/-- Encoding of `PrenexCNF`: the framed list of `(∃, ∀)` binary variable pairs
(`encList (encPair encNat encNat)`) followed by `Cslib.Complexity.encCNF` of the matrix, preserving
the exact encoded words of `encPair (encList (encPair encNat encNat)) encCNF`. -/
enc_structure encPrenexCNF : PrenexCNF where
  rounds : (encList (encPair encNat encNat)), matrix : encCNF

/-- **True closed formulas in alternating prenex conjunctive normal form**: the instances
`⟨rounds, ψ⟩ : PrenexCNF` such that `∃ x₁, ∀ y₁, ⋯, ∃ xₙ, ∀ yₙ, ψ` is a true closed formula. -/
def TQBFCNF : Set PrenexCNF := {x | QBF.rounds x.rounds (QBF.ofCNF x.matrix) ∈ TQBF}

/-- An instance `x` belongs to `TQBFCNF` iff `QBF.rounds x.rounds (QBF.ofCNF x.matrix) ∈ TQBF`. -/
theorem mem_TQBFCNF {x : PrenexCNF} :
    x ∈ TQBFCNF ↔ QBF.rounds x.rounds (QBF.ofCNF x.matrix) ∈ TQBF :=
  Iff.rfl

/-- `⟨ps, ψ⟩ ∈ TQBFCNF` iff `QBF.rounds ps (QBF.ofCNF ψ) ∈ TQBF`. -/
@[simp]
theorem mk_mem_TQBFCNF {ps : List (ℕ × ℕ)} {ψ : CNF ℕ} :
    (⟨ps, ψ⟩ : PrenexCNF) ∈ TQBFCNF ↔ QBF.rounds ps (QBF.ofCNF ψ) ∈ TQBF :=
  Iff.rfl

namespace TQBF

open ComputableInPolyTime

variable {γ : Type} {encIn : γ ↪ List Bool}

/-- Rounds of quantifiers are polynomial-time in the rounds and the body. -/
@[fun_prop]
theorem computableInPolyTime_rounds {ps : γ → List (ℕ × ℕ)} {φ : γ → QBF ℕ}
    (hps : Turing.MultiTapeTM.ComputableInPolyTime ps encIn (encList (encPair encNat encNat)))
    (hφ : Turing.MultiTapeTM.ComputableInPolyTime φ encIn encQBF) :
    Turing.MultiTapeTM.ComputableInPolyTime (fun x => QBF.rounds (ps x) (φ x)) encIn encQBF :=
  computableInPolyTime_of_tokens
    (l := fun x => (ps x).flatMap (fun p => [(QBF.Kind.ex, p.1), (QBF.Kind.all, p.2)]) ++
      (φ x).tokens) (by fun_prop) fun _ => QBF.tokens_rounds ..

section Prenex

variable {k : ℕ} {State : Type} [Fintype State]

/-- A variable of the blocks of level `0` that no formula of a game uses: the first variable of
the midpoint block of level `0`. -/
private def dummyVar : ℕ := blockVar 2 0 0

private theorem dummyVar_ne_tabVar (v : CookLevin.Var k State) : dummyVar ≠ tabVar v := fun h => by
  have := blockVar_mod_two 2 0 0
  have := tabVar_mod_two v
  rw [dummyVar] at h; omega

private theorem dummyVar_ne_certVar (w j : ℕ) : dummyVar ≠ certVar w j := fun h => by
  unfold dummyVar certVar at h
  split_ifs at h
  all_goals exact absurd (blockVar_inj (by norm_num) (by norm_num) h).1 (by norm_num)

/-- The rounds of the normal form of the formula of a game: those over the moves, then a round
`∃ v, ∀ dummyVar` for each variable `v` of the formula of level `0`. -/
noncomputable def prenexPairs (tab : CNF (CookLevin.Var k State)) (w : ℕ) : List (ℕ × ℕ) :=
  gamePairs w ++ (baseVars tab w).map fun v => (v, dummyVar)

private theorem mem_vars_prenexMatrix {tab : CNF (CookLevin.Var k State)} {w x : ℕ}
    (hx : x ∈ (prenexMatrix tab w).vars) :
    (∃ j < 2 * w, x = tabVar (CookLevin.Var.cert (k := k) (State := State) j) ∨
      x = certVar w j) ∨ ∃ v ∈ tab.vars, x = tabVar v := by
  simp only [prenexMatrix, CNF.vars, List.flatten_append, List.map_append, List.mem_append,
    List.mem_map, List.mem_flatten] at hx
  rcases hx with ⟨l, ⟨c, hc, hl⟩, rfl⟩ | ⟨l, ⟨c, hc, hl⟩, rfl⟩
  · simp only [certLinkCNF, linkCNF, List.mem_flatMap, List.mem_range, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    obtain ⟨j, hj, rfl | rfl⟩ := hc
    all_goals
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      exact hl.elim (fun h => .inl ⟨j, hj, .inl (congrArg Prod.fst h)⟩)
        (fun h => .inl ⟨j, hj, .inr (congrArg Prod.fst h)⟩)
  · simp only [CNF.relabel, List.mem_map] at hc
    obtain ⟨c', hc', rfl⟩ := hc
    simp only [Clause.relabel, List.mem_map] at hl
    obtain ⟨l', hl', rfl⟩ := hl
    exact .inr ⟨l'.1, List.mem_map.2 ⟨l', List.mem_flatten.2 ⟨c', hc', hl'⟩, rfl⟩, rfl⟩

private theorem dummyVar_notMem_freeVars (tab : CNF (CookLevin.Var k State)) (w : ℕ) :
    dummyVar ∉ (QBF.ofCNF (prenexMatrix tab w)).freeVars := by
  rw [QBF.mem_freeVars_ofCNF]
  rintro hx
  rcases mem_vars_prenexMatrix hx with ⟨_, -, h | h⟩ | ⟨_, -, h⟩
  exacts [dummyVar_ne_tabVar _ h, dummyVar_ne_certVar _ _ h, dummyVar_ne_tabVar _ h]

/-- **The normal form of the formula of a game has its value.** -/
theorem eval_prenex (tab : CNF (CookLevin.Var k State)) (w : ℕ) (σ : ℕ → Bool) :
    (QBF.rounds (prenexPairs tab w) (QBF.ofCNF (prenexMatrix tab w))).eval σ =
      (gameFormula tab w).eval σ := by
  rw [prenexPairs, QBF.rounds_append, gameFormula]
  refine QBF.eval_rounds_congr (fun τ => ?_) _ σ
  rw [QBF.eval_rounds_map_pair (dummyVar_notMem_freeVars tab w), baseFormula]
  exact QBF.eval_exs_congr (eval_prenexMatrix tab w) _ τ

/-- **The normal form of the formula of a game is closed.** -/
theorem closed_prenex (tab : CNF (CookLevin.Var k State)) (w : ℕ) :
    (QBF.rounds (prenexPairs tab w) (QBF.ofCNF (prenexMatrix tab w))).Closed := by
  refine Finset.eq_empty_of_forall_notMem fun x hx => ?_
  rw [QBF.mem_freeVars_rounds, QBF.mem_freeVars_ofCNF] at hx
  obtain ⟨hx, hnot⟩ := hx
  apply hnot
  have hbase (h : x ∈ baseVars tab w) : x ∈ QBF.roundVars (prenexPairs tab w) := by
    simp only [prenexPairs, QBF.roundVars, List.flatMap_append, List.mem_append, List.flatMap_map,
      List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
    exact .inr ⟨x, h, .inl rfl⟩
  rcases mem_vars_prenexMatrix hx with ⟨j, hj, rfl | rfl⟩ | ⟨v, hv, rfl⟩
  · exact hbase (List.mem_append_right _ (List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩))
  · have : certVar w j ∈ QBF.roundVars (gamePairs w) := by
      rw [roundVars_gamePairs]
      unfold certVar
      split_ifs with hjw
      · exact List.mem_append_left _ (List.mem_map.2 ⟨j, List.mem_range.2 hjw, rfl⟩)
      · exact List.mem_append_right _ (List.mem_map.2 ⟨j - w, List.mem_range.2 (by omega), rfl⟩)
    simpa only [prenexPairs, QBF.roundVars, List.flatMap_append, List.mem_append] using Or.inl this
  · exact hbase (List.mem_append_left _ (List.mem_map.2 ⟨v, hv, rfl⟩))

end Prenex

section Reduction

variable {α : Type} (enc : α ↪ List Bool) (p : Polynomial ℕ)

/-- The Cook–Levin tableau of the formula of a game (`gameReduce`). -/
private noncomputable def gameTableau {kV : ℕ} {StateV : Type} [Fintype StateV]
    [DecidableEq StateV] (tmV : MultiTapeTM kV Bool StateV) (cV dV : ℕ) (a : α) :
    CNF (CookLevin.Var kV StateV) :=
  CookLevin.tableau tmV (frame (enc a)) (2 * p.eval (enc a).length)
    (cV * (2 * (enc a).length + 2 * p.eval (enc a).length + 2) ^ dV)

/-- **The reduction of a game to `TQBFCNF`**: the formula of the game (`gameReduce`) in
alternating prenex conjunctive normal form. -/
noncomputable def prenexReduce {kV : ℕ} {StateV : Type} [Fintype StateV] [DecidableEq StateV]
    (tmV : MultiTapeTM kV Bool StateV) (cV dV : ℕ) (a : α) : PrenexCNF :=
  ⟨prenexPairs (gameTableau enc p tmV cV dV a) (p.eval (enc a).length),
    prenexMatrix (gameTableau enc p tmV cV dV a) (p.eval (enc a).length)⟩

variable {enc p}

/-- The normal form of the formula of a game is in `TQBFCNF` exactly when the formula is in
`TQBF`. -/
theorem prenexReduce_mem_TQBFCNF_iff {kV : ℕ} {StateV : Type} [Fintype StateV]
    [DecidableEq StateV] (tmV : MultiTapeTM kV Bool StateV) (cV dV : ℕ) (a : α) :
    prenexReduce enc p tmV cV dV a ∈ TQBFCNF ↔ gameReduce enc p tmV cV dV a ∈ TQBF := by
  rw [prenexReduce, gameTableau, mk_mem_TQBFCNF,
    mem_TQBF_iff_of_closed (closed_prenex _ _) (fun _ => false), gameReduce,
    mem_TQBF_iff_of_closed (closed_gameFormula _ _) (fun _ => false), eval_prenex]

/-- **The reduction of a game to `TQBFCNF` is polynomial-time.** -/
theorem computableInPolyTime_prenexReduce {kV : ℕ} {StateV : Type} [Fintype StateV]
    [DecidableEq StateV] (tmV : MultiTapeTM kV Bool StateV) (cV dV : ℕ) :
    Turing.MultiTapeTM.ComputableInPolyTime (prenexReduce enc p tmV cV dV) enc encPrenexCNF := by
  have htab := CookLevin.computableInPolyTime_tableau tmV
  have hframe := bitsFrame enc
  have hp : ComputableInPolyTime (fun a => p.eval (enc a).length) enc encUnary :=
    (unary_eval p).comp (encoding_length enc)
  have hvars : ComputableInPolyTime (CNF.vars (V := CookLevin.Var kV StateV))
      (encList (encList (encPair CookLevin.encVar encBool))) (encList CookLevin.encVar) :=
    CNF.computableInPolyTime_vars _
  have htabVar := computableInPolyTime_tabVar (k := kV) (State := StateV)
  have hcertVar := CookLevin.computableInPolyTime_cert (k := kV) (State := StateV)
  have hcert : ComputableInPolyTime (fun q : ℕ × ℕ => certVar q.1 q.2)
      (encPair encUnary encUnary) encNat :=
    computableInPolyTime_certVar (.fst _ _) (.snd _ _)
  have htableau : ComputableInPolyTime (gameTableau enc p tmV cV dV) enc
      (encList (encList (encPair CookLevin.encVar encBool))) := by
    unfold gameTableau
    fun_prop
  have hbase : ComputableInPolyTime
      (fun q : CNF (CookLevin.Var kV StateV) × ℕ => baseVars q.1 q.2)
      (encPair (encList (encList (encPair CookLevin.encVar encBool))) encUnary)
      (encList encNat) := by
    unfold baseVars
    fun_prop
  have hgamePairs : ComputableInPolyTime gamePairs encUnary
      (encList (encPair encNat encNat)) := by
    unfold gamePairs
    fun_prop
  exact encPrenexCNF_mk_polyTime
    ((listAppend (encPair encNat encNat)).comp ((hgamePairs.comp hp).prod
      ((map ((id' (encIn := encNat)).prod (const (encOut := encNat) dummyVar))).comp
        (hbase.comp (htableau.prod hp)))))
    (computableInPolyTime_prenexMatrix htableau hp)

end Reduction

end TQBF

/-- `TQBFCNF` is in `PSPACE`: writing the formula is polynomial-time. -/
theorem TQBFCNF_mem_PSPACE : TQBFCNF ∈ PSPACE encPrenexCNF :=
  PolyTimeReducible.mem_PSPACE
    ⟨fun x => QBF.rounds x.rounds (QBF.ofCNF x.matrix), by fun_prop, fun _ => Iff.rfl⟩
    TQBF_mem_PSPACE

/-- **`TQBFCNF` is `PSPACE`-hard**: a problem in `PSPACE` is a game of polynomially many moves
with a polynomial-time winning condition, whose formula is put in alternating prenex conjunctive
normal form. -/
theorem TQBFCNF_pspaceHard : PSPACEHard encPrenexCNF TQBFCNF := by
  intro α enc A hA
  obtain ⟨p, V, hV, h⟩ := exists_isGameVerifier_of_mem_PSPACE hA
  obtain ⟨cV, dV, kV, StateV, hfiniteV, tmV, htmV⟩ :=
    Turing.MultiTapeTM.Internal.NormalForm.polyTime hV
  have := Fintype.ofFinite StateV
  classical
  exact ⟨TQBF.prenexReduce enc p tmV cV dV,
    (TQBF.computableInPolyTime_prenexReduce tmV cV dV),
    fun a => (h a).trans
      ((TQBF.gameReduce_mem_TQBF_iff htmV a).symm.trans
        (TQBF.prenexReduce_mem_TQBFCNF_iff tmV cV dV a).symm)⟩

/-- **`TQBF` in alternating prenex conjunctive normal form is `PSPACE`-complete**
[Sipser, Section 8.3][Sipser2013]. -/
theorem TQBFCNF_pspaceComplete : PSPACEComplete encPrenexCNF TQBFCNF :=
  ⟨TQBFCNF_mem_PSPACE, TQBFCNF_pspaceHard⟩

end Cslib.Complexity
