/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.Approximation.MaxExactThreeSAT
public import CslibFrontier.Computability.Complexity.Problems.XORSAT

/-!
# A gap problem on linear systems over GF(2) is NP-hard

`GapLin L s` is Goldreich's `gapLin_{L,s}` [Goldreich2007DraftR5], §10.1.1 (printed p. 462).
Its instances are systems of linear equations over GF(2) (`Cslib.Complexity.XORSAT.System`,
equations with repeated variables allowed, under the existing XOR-SAT encoding). The
yes-instances are the systems in which some assignment satisfies at least the proportion `L` of
the equations, the no-instances those in which no assignment satisfies the proportion `s` of the
equations or more. Proportions count equations with multiplicity. The no-instances also require
`s ≤ L`, which keeps the two sets disjoint, as in `Cslib.Complexity.PromiseProblem.gapMax`.

Following the guideline of [Goldreich2007DraftR5], Exercise 10.5 (printed p. 496), a clause
`ℓ₁ ∨ ℓ₂ ∨ ℓ₃` of exactly three, not necessarily distinct, literals is mapped to the seven
equations stating that the literals of a nonempty subset of the three positions sum to one
(`Cslib.Complexity.GapLin.clauseEquations`). An assignment that satisfies the clause satisfies
exactly four of these equations, and one that falsifies it satisfies none
(`Cslib.Complexity.GapLin.countSat_clauseEquations`). Hence a satisfiable formula is mapped to a
system in which some assignment satisfies `4 / 7` of the equations, and a formula in which every
assignment satisfies at most the proportion `s₀` of the clauses to a system in which every
assignment satisfies at most `4 / 7 · s₀` of the equations. Starting from the NP-hardness of
MAX-E3SAT (`Cslib.Complexity.GapExactThreeSAT_npHard`, with `s₀ = 1 - 1 / (3 * 2 ^ 77)`) gives
NP-hardness of `gapLin_{L,s}` with `L = 4 / 7` and `s = 4 / 7 · (1 - 1 / (6 * 2 ^ 77))`, so
`1 / 2 < s < L < 1`. This is Exercise 10.5, a weak version of Goldreich's Theorem 10.9 (Håstad's
`gapLin_{1-ε, 1/2+ε}`), which is not formalized here.

## Main definitions

* `Cslib.Complexity.GapLin`: the gap problem `gapLin_{L,s}`.
* `Cslib.Complexity.GapLin.clauseEquations`: the seven equations of a clause.
* `Cslib.Complexity.GapLin.reduce`: the reduction from MAX-E3SAT.

## Main results

* `Cslib.Complexity.GapLin.countSat_clauseEquations`: four of seven, or none.
* `Cslib.Complexity.polyTimeReducible_GapExactThreeSAT_GapLin`: MAX-E3SAT with soundness `s₀`
  reduces to `gapLin_{4/7, s}` for every `4 / 7 · s₀ < s ≤ 4 / 7`.
* `Cslib.Complexity.GapLin_npHard`: `gapLin_{4/7, 4/7 · (1 - 1 / (6 * 2 ^ 77))}` is NP-hard.
* `Cslib.Complexity.exists_GapLin_npHard`: Goldreich's Exercise 10.5, for some constants
  `1 / 2 < s < L < 1`, `gapLin_{L,s}` is NP-hard.

## References

* [O. Goldreich, *Computational Complexity: A Conceptual Perspective*, draft of April 2007,
  Exercise 10.5 (printed p. 496) and §10.1.1 (printed p. 462)][Goldreich2007DraftR5]
-/

public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM

/-- **The gap problem `gapLin_{L,s}`** [Goldreich2007DraftR5], §10.1.1: on systems of linear
equations over GF(2), the yes-instances are the systems in which some assignment satisfies at
least the proportion `L` of the equations, and the no-instances the systems in which no
assignment satisfies the proportion `s` of the equations or more. Proportions count equations with
multiplicity; the empty system has proportion zero. The no-instances also require `s ≤ L`, so
that the two sets are disjoint. -/
@[expose] def GapLin (L s : ℝ) : PromiseProblem XORSAT.System where
  yes := {F | ∃ a : ℕ → Bool, L ≤ (F.countSat a : ℝ) / F.length}
  no := {F | s ≤ L ∧ ∀ a : ℕ → Bool, (F.countSat a : ℝ) / F.length < s}
  disjoint := Set.disjoint_left.2 fun _ ⟨a, ha⟩ ⟨hsL, hno⟩ =>
    (hsL.trans ha).not_gt (hno a)

variable {L s : ℝ} {F : XORSAT.System}

/-- The yes-instances of `GapLin L s`. -/
theorem mem_yes_GapLin :
    F ∈ (GapLin L s).yes ↔ ∃ a : ℕ → Bool, L ≤ (F.countSat a : ℝ) / F.length :=
  Iff.rfl

/-- The no-instances of `GapLin L s`. -/
theorem mem_no_GapLin :
    F ∈ (GapLin L s).no ↔ s ≤ L ∧ ∀ a : ℕ → Bool, (F.countSat a : ℝ) / F.length < s :=
  Iff.rfl

namespace GapLin

/-- The equation over GF(2) stating that the listed literals sum to one: its variables are those
of the literals, and its right-hand side absorbs the negations. -/
@[expose] def oddEquation (ls : Clause ℕ) : AffineEquation ℕ :=
  ⟨ls.map Prod.fst, !(ls.map fun l => !l.2).sum⟩

/-- A literal evaluates to its variable plus one exactly when it is negated. -/
private theorem literal_eval_eq (σ : ℕ → Bool) (l : Literal ℕ) :
    Literal.eval σ l = σ l.1 + !l.2 := by
  rcases l with ⟨v, b⟩
  simp only [Literal.eval]
  cases b <;> cases σ v <;> rfl

/-- `oddEquation ls` holds exactly when an odd number of the literals are true. -/
theorem holds_oddEquation (σ : ℕ → Bool) (ls : Clause ℕ) :
    (oddEquation ls).Holds σ ↔ (ls.map (Literal.eval σ)).sum = true := by
  have hsum : (ls.map (Literal.eval σ)).sum =
      ((ls.map Prod.fst).map σ).sum + (ls.map fun l => !l.2).sum := by
    induction ls with
    | nil => rfl
    | cons l ls ih =>
      simp only [List.map_cons, List.sum_cons, ih, literal_eval_eq]
      abel
  simp only [AffineEquation.Holds, oddEquation, hsum]
  cases ((ls.map Prod.fst).map σ).sum <;> cases (ls.map fun l => !l.2).sum <;> decide

/-- **The seven equations of a clause**, the map of Exercise 2.24 that the guideline of
[Goldreich2007DraftR5], Exercise 10.5 applies: for a clause `ℓ₁ ∨ ℓ₂ ∨ ℓ₃`, one equation
`∑ i ∈ I, ℓᵢ = 1` for each nonempty `I ⊆ {1, 2, 3}`. Missing literals of shorter clauses are read
as `x₀`; the semantics is used only for clauses of exactly three literals. -/
@[expose] def clauseEquations (c : Clause ℕ) : XORSAT.System :=
  let x := c.headD (0, true)
  let y := c.tail.headD (0, true)
  let z := c.tail.tail.headD (0, true)
  [[x], [y], [z], [x, y], [x, z], [y, z], [x, y, z]].map oddEquation

/-- Every clause yields seven equations. -/
theorem length_clauseEquations (c : Clause ℕ) : (clauseEquations c).length = 7 :=
  rfl

/-- Of the seven sums of a nonempty subset of three bits, four are odd if some bit is set, and none
otherwise. -/
private theorem countP_sum_seven (p q r : Bool) :
    [[p], [q], [r], [p, q], [p, r], [q, r], [p, q, r]].countP (fun l => l.sum) =
      if (p || q || r) then 4 else 0 := by
  cases p <;> cases q <;> cases r <;> rfl

/-- **Four of seven, or none**: an assignment that satisfies a clause of three literals satisfies
exactly four of its seven equations, and one that falsifies it satisfies none. -/
theorem countSat_clauseEquations (σ : ℕ → Bool) (a b c : Literal ℕ) :
    (clauseEquations [a, b, c]).countSat σ = if Clause.eval σ [a, b, c] then 4 else 0 := by
  have hpred : (fun e : AffineEquation ℕ => decide (e.Holds σ)) ∘ oddEquation =
      (fun l : List Bool => l.sum) ∘ List.map (Literal.eval σ) :=
    funext fun _ => by simp only [Function.comp_apply, holds_oddEquation, Bool.decide_eq_true]
  simp only [clauseEquations, List.headD_cons, List.tail_cons]
  rw [AffineSystem.countSat, List.countP_map, hpred, ← List.countP_map]
  simp only [List.map_cons, List.map_nil, countP_sum_seven]
  simp [Clause.eval, Bool.or_assoc]

/-- On formulas with clauses of exactly three literals, the equations satisfied are four per
satisfied clause. -/
theorem countSat_flatMap_clauseEquations (σ : ℕ → Bool) {φ : CNF ℕ}
    (h3 : ∀ c ∈ φ, c.length = 3) :
    AffineSystem.countSat (φ.flatMap clauseEquations) σ = 4 * φ.countP (Clause.eval σ) := by
  induction φ with
  | nil => rfl
  | cons c φ ih =>
    obtain ⟨a, b, d, rfl⟩ := List.length_eq_three.1 (h3 c List.mem_cons_self)
    have ih := ih fun c hc => h3 c (List.mem_cons_of_mem _ hc)
    have hsat := countSat_clauseEquations σ a b d
    simp only [AffineSystem.countSat, List.flatMap_cons, List.countP_append,
      List.countP_cons] at ih hsat ⊢
    rw [ih, hsat]
    split <;> omega

/-- A formula yields seven equations per clause. -/
theorem length_flatMap_clauseEquations (φ : CNF ℕ) :
    (φ.flatMap clauseEquations).length = 7 * φ.length := by
  induction φ with
  | nil => rfl
  | cons c φ ih =>
    rw [List.flatMap_cons, List.length_append, ih, length_clauseEquations, List.length_cons]
    ring

/-- A formula is replaced by the single clause `x₀ ∨ x₀ ∨ x₀` when it has no clauses, so that a
satisfiable formula always yields equations. -/
@[expose] def nonempty (φ : CNF ℕ) : CNF ℕ :=
  if φ.isEmpty then [[(0, true), (0, true), (0, true)]] else φ

/-- **The reduction from MAX-E3SAT to `gapLin`** [Goldreich2007DraftR5], Exercise 10.5: the seven
equations of every clause, after replacing the empty formula by `x₀ ∨ x₀ ∨ x₀`. -/
@[expose] def reduce (φ : CNF ℕ) : XORSAT.System :=
  (nonempty φ).flatMap clauseEquations

/-- On formulas with clauses of exactly three literals, the proportion of satisfied equations is
`4 / 7` times the proportion of satisfied clauses. -/
private theorem countSat_div_length (σ : ℕ → Bool) {φ : CNF ℕ} (h3 : ∀ c ∈ φ, c.length = 3) :
    (AffineSystem.countSat (φ.flatMap clauseEquations) σ : ℝ) / (φ.flatMap clauseEquations).length =
      4 / 7 * ((φ.countP (Clause.eval σ) : ℝ) / φ.length) := by
  rw [countSat_flatMap_clauseEquations σ h3, length_flatMap_clauseEquations]
  push_cast
  rcases eq_or_ne (φ.length : ℝ) 0 with h | h
  · simp [h]
  · field_simp

private theorem nonempty_spec {φ : CNF ℕ} (h3 : ∀ c ∈ φ, c.length = 3) :
    (∀ c ∈ nonempty φ, c.length = 3) ∧ 0 < (nonempty φ).length ∧
      (φ.Satisfiable → (nonempty φ).Satisfiable) := by
  unfold nonempty
  split_ifs with he
  · refine ⟨fun c hc => ?_, by simp, fun _ => ⟨fun _ => true, rfl⟩⟩
    rw [List.mem_singleton.1 hc]
    rfl
  · exact ⟨h3, List.length_pos_iff.2 fun h0 => he (by simp [h0]), id⟩

/-- A satisfiable formula with clauses of exactly three literals is mapped to a system in which
some assignment satisfies `4 / 7` of the equations. -/
theorem exists_countSat_reduce {φ : CNF ℕ} (hφ : φ ∈ ExactThreeSAT) :
    ∃ σ : ℕ → Bool, ((reduce φ).countSat σ : ℝ) / (reduce φ).length = 4 / 7 := by
  obtain ⟨h3, hpos, hsat⟩ := nonempty_spec hφ.1
  obtain ⟨σ, hσ⟩ := hsat hφ.2
  refine ⟨σ, ?_⟩
  rw [reduce, countSat_div_length σ h3,
    List.countP_eq_length.2 fun c hc => (CNF.eval_eq_true_iff σ _).1 hσ c hc,
    div_self (by exact_mod_cast hpos.ne'), mul_one]

/-- If every assignment falsifies at least the proportion `1 - s₀` of the clauses, then every
assignment satisfies at most `4 / 7 · s₀` of the equations. -/
theorem countSat_reduce_le {φ : CNF ℕ} {s₀ : ℝ} (h3 : ∀ c ∈ φ, c.length = 3) (hs₀ : s₀ < 1)
    (hφ : 1 - s₀ ≤ φ.unsatVal) (σ : ℕ → Bool) :
    ((reduce φ).countSat σ : ℝ) / (reduce φ).length ≤ 4 / 7 * s₀ := by
  have hpos : 0 < φ.length := CNF.length_pos_of_unsatVal_pos (by linarith)
  have hne : nonempty φ = φ :=
    ite_eq_right (by simpa [List.isEmpty_iff] using List.ne_nil_of_length_pos hpos)
  rw [reduce, hne, countSat_div_length σ h3]
  have hunsat := (CNF.le_unsatVal_iff φ).1 hφ σ
  have hsplit : (φ.countP (Clause.eval σ) : ℝ) + φ.countUnsat σ = φ.length := by
    have := List.length_eq_countP_add_countP (Clause.eval σ) (l := φ)
    simp only [CNF.countUnsat]
    exact_mod_cast (by simpa using this.symm)
  have hlen : (0 : ℝ) < φ.length := mod_cast hpos
  rw [le_div_iff₀ hlen] at hunsat
  have := (div_le_iff₀ hlen).2 (by linarith : (φ.countP (Clause.eval σ) : ℝ) ≤ s₀ * φ.length)
  linarith

end GapLin

open GapLin

/-- The reduction is polynomial-time. -/
theorem GapLin.computableInPolyTime_reduce :
    ComputableInPolyTime reduce encCNF XORSAT.encoding := by
  have := XORSAT.computableInPolyTime_sum
  have hodd : ComputableInPolyTime oddEquation (encList (encPair encNat encBool))
      (encAffineEquation encNat) := by
    unfold oddEquation
    fun_prop
  have hclause : ComputableInPolyTime clauseEquations (encList (encPair encNat encBool))
      XORSAT.encoding := by
    unfold clauseEquations XORSAT.encoding
    fun_prop
  have hne : ComputableInPolyTime nonempty encCNF encCNF :=
    ComputableInPolyTime.ite
      (by
        unfold encCNF
        exact (ListEncoding.isEmpty (enc₁ := encList (encPair encNat encBool))
          (enc := encList (encList (encPair encNat encBool)))).computableInPolyTime)
      (.const _) (ComputableInPolyTime.id' (encIn := encCNF))
  unfold reduce XORSAT.encoding
  unfold encCNF at hne
  unfold XORSAT.encoding at hclause
  fun_prop

/-- **MAX-E3SAT reduces to `gapLin`** [Goldreich2007DraftR5], Exercise 10.5: for soundness
`s₀ < 1` of MAX-E3SAT and every `4 / 7 · s₀ < s ≤ 4 / 7`, `GapLin.reduce` maps satisfiable
formulas to systems in which some assignment satisfies `4 / 7` of the equations, and formulas in
which every assignment falsifies at least `1 - s₀` of the clauses to systems in which no
assignment satisfies `s` of the equations. -/
theorem polyTimeReducible_GapExactThreeSAT_GapLin {s₀ : ℝ} (hs₀ : s₀ < 1) (hs : 4 / 7 * s₀ < s)
    (hsL : s ≤ 4 / 7) :
    PromiseProblem.PolyTimeReducible encCNF XORSAT.encoding (GapExactThreeSAT s₀)
      (GapLin (4 / 7) s) := by
  refine ⟨reduce, computableInPolyTime_reduce, fun φ hφ => ?_, fun φ hφ => ?_⟩
  · obtain ⟨σ, hσ⟩ := exists_countSat_reduce (by rwa [yes_GapExactThreeSAT] at hφ)
    exact ⟨σ, hσ.ge⟩
  · obtain ⟨h3, hunsat⟩ := (mem_no_GapExactThreeSAT hs₀).1 hφ
    exact ⟨hsL, fun σ => (countSat_reduce_le h3 hs₀ hunsat σ).trans_lt hs⟩

/-- **`gapLin` is NP-hard** [Goldreich2007DraftR5], Exercise 10.5: distinguishing systems of
linear equations over GF(2) in which some assignment satisfies `4 / 7` of the equations from those
in which no assignment satisfies the proportion `4 / 7 · (1 - 1 / (6 * 2 ^ 77))` of them is
NP-hard. -/
theorem GapLin_npHard :
    PromiseProblem.NPHard XORSAT.encoding (GapLin (4 / 7) (4 / 7 * (1 - 1 / (6 * 2 ^ 77)))) :=
  GapExactThreeSAT_npHard.trans
    (polyTimeReducible_GapExactThreeSAT_GapLin (by norm_num) (by norm_num) (by norm_num))

/-- **Goldreich, Exercise 10.5** (a weak version of Theorem 10.9) [Goldreich2007DraftR5]: for some
constants `1 / 2 < s < L < 1`, the problem `gapLin_{L,s}` is NP-hard. -/
theorem exists_GapLin_npHard :
    ∃ L s : ℝ, 1 / 2 < s ∧ s < L ∧ L < 1 ∧ PromiseProblem.NPHard XORSAT.encoding (GapLin L s) :=
  ⟨4 / 7, 4 / 7 * (1 - 1 / (6 * 2 ^ 77)), by norm_num, by norm_num, by norm_num, GapLin_npHard⟩

end Cslib.Complexity
