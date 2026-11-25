/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Query.BinarySearch
public import CslibFrontier.Algorithms.Lean.Query.SumQuery
public import CslibFrontier.Computability.Complexity.Classes.Oracle.BoundedQuery
public import CslibFrontier.Computability.Complexity.Classes.Oracle.PolyTime
public import CslibFrontier.Computability.Complexity.FineGrained.MaxSAT.Histogram
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Option
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Logics.Propositional.CNF.ModelCount
import CslibFrontier.Logics.Propositional.CNF.Eval
import CslibFrontier.Computability.Complexity.Classes.NP.Closure
import CslibFrontier.Computability.Complexity.Classes.NP.Image
import CslibFrontier.Computability.Complexity.Classes.Oracle.Closure
import CslibFrontier.Computability.Complexity.Classes.Oracle.Monotone
import CslibFrontier.Computability.Complexity.Problems.SAT.PolyTime
import CslibFrontier.Computability.Complexity.Problems.SAT.Units
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Bounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List.Size
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.BinarySizeFacts
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Automation
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Tactic.EncLen

/-!
# Threshold optimization by binary search and witness recovery

Optimization over a bounded integer objective `[0, bound x]` reduces to logarithmic threshold
decision queries followed by witness search at the optimal threshold
[Papadimitriou, Section 17.1][Papadimitriou94], [Arora and Barak, Section 2.5][AroraBarak09].

1. **Threshold-probe query optimization (`MaxThresholdSpec`, `MinThresholdSpec`)**:
   pure bisection via `Cslib.Algorithms.Lean.lowerBound` and query-monad programs (`maxOptQ`,
   `minOptQ`, `maxOptWitnessQ`, `minOptWitnessQ` over `Cslib.Query.ProbeQuery` and
   `ThresholdWitnessQuery`) find the exact maximum or minimum feasible objective value (or `none`
   when no valid witness exists) using at most `Nat.log 2 (bound x + 1) + 1` threshold decision
   queries (`SumQuery.countInl`) and at most `1` witness query (`SumQuery.countInr`, `0` when
   infeasible).
2. **Native oracle binary search (`bisectProgram`,
   `computableInPolyTimeWithOracleQueries_bisect`)**: a fixed-iteration adaptive `WordQueryComp`
   loop over `[lo x, hi x)` runs `(hi x - lo x).size` rounds, agrees identically with
   `lowerBound`, makes at most `(hi x - lo x).size ≤ Nat.log 2 (hi x - lo x) + 1` oracle
   requests (all at midpoints in `[lo x, hi x)`), and is strict oracle PPT (`IsOraclePPTOn`) even
   for exponentially large binary bounds `hi x`. Sequencing with an oracle witness-recovery
   program (`ComputableInPolyTimeWithOracleQueries.bind_with`) recovers both the optimal value
   and an optimal witness, collapsing to plain `ComputableInPolyTime` when the oracle lies in `P`.
3. **Max-SAT optimization and optimal assignment recovery (`MaxSATThreshold`, `solveMaxSAT`)**:
   for `φ : CNF ℕ`, binary search over `MaxSATQuery` (`[1, φ.length + 1)`) finds the maximum
   satisfied-clause count `maxClauseScore φ`, and variable-by-variable partial evaluation over
   `φ.distinctVars` recovers an assignment achieving `maxClauseScore φ` in at most
   `φ.length.size + φ.numVars ≤ (Nat.log 2 φ.length + 1) + φ.numVars` queries to the `NP`
   language `MaxSATThreshold`, with every queried instance no longer than `⟨φ, φ.length⟩`.

The Max-SAT client here works in `P^NP`: instances are bare `φ : CNF ℕ`, every assignment
`ℕ → Bool` is admissible, the query `MaxSATQuery` carries a binary target, and the oracle is the
`NP` language `MaxSATThreshold` itself. `FineGrained.MaxSAT.Reduction` instead fixes a declared
variable count (`MaxSAT.StructInstance`, assignments in `BitString n`), takes a unary cutoff
(`MaxSAT.ThresholdQuery`), and compiles each threshold query through `MaxSAT.thresholdCircuit` to a
3-CNF for a supplied fixed-width `k`-SAT solver. The two optima agree on well-formed instances:
`MaxSAT.maxClauseScore_eq_optimum` gives `maxClauseScore φ = MaxSAT.optimum (n, φ)` when every
variable of `φ` is below `n`.

## Main definitions

* `Cslib.Complexity.BisectInterval`, `Cslib.Complexity.bisectStep`: interval state and single
  bisection step.
* `Cslib.Complexity.OracleThresholdQuery`, `Cslib.Complexity.OptSolution`: typed query and
  value-witness structures with encodings `encOracleThresholdQuery` and `encOptSolution`.
* `Cslib.Complexity.WitnessQuery`, `Cslib.Complexity.ThresholdWitnessQuery`: witness-at-threshold
  query signature and combined decision/witness query signature.
* `Cslib.Complexity.MaxThresholdSpec`, `Cslib.Complexity.MinThresholdSpec`: bounded maximization
  and minimization threshold specifications with pure and `FreeM` query solvers (`maxOpt`,
  `minOpt`, `maxOptWitness`, `minOptWitness`, `maxOptQ`, `minOptQ`, `maxOptWitnessQ`,
  `minOptWitnessQ`).
* `Cslib.Complexity.bisectProgram`: native adaptive oracle bisection program.
* `Cslib.Complexity.MaxSATQuery`, `Cslib.Complexity.MaxSATSolution`,
  `Cslib.Complexity.MaxSATThreshold`, `Cslib.Complexity.MaxSAT.solveMaxSAT`: Max-SAT threshold
  language and oracle optimization-with-witness solver.

## Main results

* `Cslib.Complexity.iterate_bisectStep_eq_lowerBound`: `(hi - lo).size` bisection steps equal
  `lowerBound`.
* `Cslib.Complexity.MaxThresholdSpec.maxOptWitness_spec`,
  `Cslib.Complexity.MaxThresholdSpec.maxOptWitnessQ_query_bounds`,
  `Cslib.Complexity.MinThresholdSpec.minOptWitness_spec`,
  `Cslib.Complexity.MinThresholdSpec.minOptWitnessQ_query_bounds`: correctness and
  `⌊log₂ (bound x + 1)⌋ + 1` decision-query plus `1` witness-query bounds for maximization and
  minimization with witness recovery.
* `Cslib.Complexity.ComputableInPolyTimeWithOracleQueries.bind_with`: query-bounded sequential
  oracle composition.
* `Cslib.Complexity.computableInPolyTimeWithOracleQueries_bisect`: polynomial-time oracle
  bisection with explicit query count `(hi x - lo x).size ≤ Nat.log 2 (hi x - lo x) + 1` and
  midpoint query-length control.
* `Cslib.Complexity.MaxSAT.computableInPolyTimeWithOracleQueries_solveMaxSAT`,
  `Cslib.Complexity.MaxSAT.solveMaxSAT_spec`,
  `Cslib.Complexity.MaxSAT.computableInPolyTime_solveMaxSAT_of_mem_P`: Max-SAT optimal value
  and optimal assignment recovery relative to `MaxSATThreshold ∈ NP` and when
  `encMaxSATQuery '' MaxSATThreshold ∈ P encBits`.
* `Cslib.Complexity.MaxSAT.maxClauseScore_eq_optimum`: on declared-range formulas, the
  binary-search optimum equals the fine-grained `MaxSAT.optimum`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [C. H. Papadimitriou, *Computational Complexity*][Papadimitriou94]
-/

public section

namespace Cslib

/-- Every request made during `n` rounds of `OracleComp.iterate` arises from `step` at a state
satisfying any invariant preserved by `interpret (m := Id) answer`. -/
theorem OracleComp.mem_queriesWith_iterate {ι State : Type} {spec : OracleSpec.{0, 0} ι}
    (answer : (q : ι) → spec q) {step : State → OracleComp spec State} {st₀ : State}
    {inv : State → Prop} (hinv0 : inv st₀)
    (hpres : ∀ st, inv st → inv (interpret (m := Id) answer (step st)))
    {n : ℕ} {q : ι} (hq : q ∈ queriesWith answer (iterate n step st₀)) :
    ∃ st, inv st ∧ q ∈ queriesWith answer (step st) := by
  induction n generalizing st₀ with
  | zero => simp at hq
  | succ n ih =>
    rw [iterate_succ_bind, queriesWith_bind, List.mem_append] at hq
    rcases hq with hfirst | hrest
    · exact ⟨st₀, hinv0, hfirst⟩
    · exact ih (hpres st₀ hinv0) hrest

namespace Complexity

open Cslib.Algorithms.Lean Cslib.Query Cslib.Logic.PL Probability Turing.MultiTapeTM

/-! ### Structures and encodings -/

/-- Active half-open interval `[lo, hi)` maintained during threshold binary search. -/
structure BisectInterval where
  /-- Inclusive lower bound of the remaining search interval. -/
  lo : ℕ
  /-- Exclusive upper bound of the remaining search interval. -/
  hi : ℕ
  deriving DecidableEq, Repr

/-- Framed binary-pair encoding of `BisectInterval`. -/
enc_structure encBisectInterval : BisectInterval where
  lo : encNat, hi : encNat

/-- An instance `inst` paired with an integer objective threshold `target`. -/
structure OracleThresholdQuery (α : Type) where
  /-- Underlying problem instance. -/
  inst : α
  /-- Candidate objective threshold. -/
  target : ℕ
  deriving DecidableEq, Repr

/-- Encoding of `OracleThresholdQuery α` as the framed pair of `encA` and binary `encNat`. -/
@[expose]
def encOracleThresholdQuery {α : Type} (encA : α ↪ List Bool) :
    OracleThresholdQuery α ↪ List Bool :=
  ⟨fun q => encPair encA encNat (q.inst, q.target), fun x y h => by
    have h' := (encPair encA encNat).injective h
    cases x; cases y; simp_all⟩

@[simp] theorem encOracleThresholdQuery_apply {α : Type} (encA : α ↪ List Bool)
    (q : OracleThresholdQuery α) :
    encOracleThresholdQuery encA q = encPair encA encNat (q.inst, q.target) :=
  rfl

private theorem computableInDegree_thresholdQueryFields {α : Type} (encA : α ↪ List Bool) :
    ComputableInDegree (fun q : OracleThresholdQuery α => (q.inst, q.target))
      (encOracleThresholdQuery encA) (encPair encA encNat) 1 1 :=
  ComputableInDegree.of_eq fun _ => rfl

/-- Projecting `OracleThresholdQuery.inst` is polynomial-time. -/
@[scoped fun_prop]
theorem encOracleThresholdQuery_inst_polyTime {α γ : Type} {encA : α ↪ List Bool}
    {encIn : γ ↪ List Bool} {g : γ → OracleThresholdQuery α}
    (h : ComputableInPolyTime g encIn (encOracleThresholdQuery encA)) :
    ComputableInPolyTime (fun a => (g a).inst) encIn encA :=
  (ComputableInDegree.fst' (computableInDegree_thresholdQueryFields encA)).computableInPolyTime.comp
    h

/-- Projecting `OracleThresholdQuery.target` is polynomial-time. -/
@[scoped fun_prop]
theorem encOracleThresholdQuery_target_polyTime {α γ : Type} {encA : α ↪ List Bool}
    {encIn : γ ↪ List Bool} {g : γ → OracleThresholdQuery α}
    (h : ComputableInPolyTime g encIn (encOracleThresholdQuery encA)) :
    ComputableInPolyTime (fun a => (g a).target) encIn encNat :=
  (ComputableInDegree.snd' (computableInDegree_thresholdQueryFields encA)).computableInPolyTime.comp
    h

/-- Constructing an `OracleThresholdQuery` from polynomial-time components is polynomial-time. -/
@[scoped fun_prop]
theorem encOracleThresholdQuery_mk_polyTime {α γ : Type} {encA : α ↪ List Bool}
    {encIn : γ ↪ List Bool} {inst : γ → α} {target : γ → ℕ}
    (hi : ComputableInPolyTime inst encIn encA)
    (ht : ComputableInPolyTime target encIn encNat) :
    ComputableInPolyTime (fun a => OracleThresholdQuery.mk (inst a) (target a))
      encIn (encOracleThresholdQuery encA) :=
  (hi.prod ht).of_enc_eq fun _ => rfl

/-- An optimal objective value paired with a witness attaining it. -/
structure OptSolution (β : Type) where
  /-- Optimal objective value. -/
  optValue : ℕ
  /-- Witness attaining `optValue`. -/
  witness : β
  deriving DecidableEq, Repr

/-- Encoding of `OptSolution β` as the framed pair of binary `encNat` and `encB`. -/
@[expose]
def encOptSolution {β : Type} (encB : β ↪ List Bool) : OptSolution β ↪ List Bool :=
  ⟨fun s => encPair encNat encB (s.optValue, s.witness), fun x y h => by
    have h' := (encPair encNat encB).injective h
    cases x; cases y; simp_all⟩

@[simp] theorem encOptSolution_apply {β : Type} (encB : β ↪ List Bool) (s : OptSolution β) :
    encOptSolution encB s = encPair encNat encB (s.optValue, s.witness) :=
  rfl

private theorem computableInDegree_optSolutionFields {β : Type} (encB : β ↪ List Bool) :
    ComputableInDegree (fun s : OptSolution β => (s.optValue, s.witness))
      (encOptSolution encB) (encPair encNat encB) 1 1 :=
  ComputableInDegree.of_eq fun _ => rfl

/-- Projecting `OptSolution.optValue` is polynomial-time. -/
@[scoped fun_prop]
theorem encOptSolution_optValue_polyTime {β γ : Type} {encB : β ↪ List Bool}
    {encIn : γ ↪ List Bool} {g : γ → OptSolution β}
    (h : ComputableInPolyTime g encIn (encOptSolution encB)) :
    ComputableInPolyTime (fun a => (g a).optValue) encIn encNat :=
  (ComputableInDegree.fst' (computableInDegree_optSolutionFields encB)).computableInPolyTime.comp h

/-- Projecting `OptSolution.witness` is polynomial-time. -/
@[scoped fun_prop]
theorem encOptSolution_witness_polyTime {β γ : Type} {encB : β ↪ List Bool}
    {encIn : γ ↪ List Bool} {g : γ → OptSolution β}
    (h : ComputableInPolyTime g encIn (encOptSolution encB)) :
    ComputableInPolyTime (fun a => (g a).witness) encIn encB :=
  (ComputableInDegree.snd' (computableInDegree_optSolutionFields encB)).computableInPolyTime.comp h

/-- Constructing an `OptSolution` from polynomial-time components is polynomial-time. -/
@[scoped fun_prop]
theorem encOptSolution_mk_polyTime {β γ : Type} {encB : β ↪ List Bool}
    {encIn : γ ↪ List Bool} {v : γ → ℕ} {w : γ → β}
    (hv : ComputableInPolyTime v encIn encNat)
    (hw : ComputableInPolyTime w encIn encB) :
    ComputableInPolyTime (fun a => OptSolution.mk (v a) (w a)) encIn (encOptSolution encB) :=
  (hv.prod hw).of_enc_eq fun _ => rfl

/-! ### Pure bisection iteration and `lowerBound` bridge -/

/-- One pure step of bisection on `[iv.lo, iv.hi)` for a Boolean test `test`. -/
def bisectStep (test : ℕ → Bool) (iv : BisectInterval) : BisectInterval :=
  if iv.lo < iv.hi then
    let mid := (iv.lo + iv.hi) / 2
    if test mid then ⟨mid + 1, iv.hi⟩ else ⟨iv.lo, mid⟩
  else iv

private theorem bisectStep_width_le (test : ℕ → Bool) (iv : BisectInterval) :
    (bisectStep test iv).hi - (bisectStep test iv).lo ≤ (iv.hi - iv.lo) / 2 := by
  unfold bisectStep; dsimp only
  split_ifs <;> first | omega | (dsimp only; omega)

private theorem iterate_bisectStep_width_le (test : ℕ → Bool) (k : ℕ) (iv : BisectInterval) :
    ((bisectStep test)^[k] iv).hi - ((bisectStep test)^[k] iv).lo ≤ (iv.hi - iv.lo) / 2 ^ k := by
  induction k generalizing iv with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    exact (ih _).trans ((Nat.div_le_div_right (bisectStep_width_le test iv)).trans
      (by rw [Nat.div_div_eq_div_mul, ← pow_succ']))

/-- **Correctness of fixed-count bisection.** If `test` is antitone on `[lo, hi)`, iterating
`bisectStep test` `(hi - lo).size` times from `⟨lo, hi⟩` yields an index `k` in `[lo, max lo hi]`
such that `test` holds on `[lo, k)` and fails on `[k, hi)`. -/
theorem iterate_bisectStep_spec {test : ℕ → Bool} {lo hi : ℕ}
    (hmono : ∀ m m', lo ≤ m → m ≤ m' → m' < hi → test m' = true → test m = true) :
    let k := ((bisectStep test)^[(hi - lo).size] ⟨lo, hi⟩).lo
    lo ≤ k ∧ k ≤ max lo hi ∧
      (∀ m, lo ≤ m → m < k → test m = true) ∧
      (∀ m, k ≤ m → m < hi → test m = false) := by
  have hinv : ∀ s,
      let iv := (bisectStep test)^[s] ⟨lo, hi⟩
      lo ≤ iv.lo ∧ iv.lo ≤ max lo hi ∧ (iv.lo < iv.hi → iv.hi ≤ hi) ∧
        (∀ m, lo ≤ m → m < iv.lo → test m = true) ∧
        (∀ m, max iv.lo iv.hi ≤ m → m < hi → test m = false) := fun s => by
    induction s with
    | zero => exact ⟨le_rfl, le_max_left _ _, fun _ => le_rfl, fun _ h1 h2 => by simp at *; omega,
        fun _ h1 h2 => by simp at *; omega⟩
    | succ s ih =>
      obtain ⟨h1, h2, h3, h4, h5⟩ := ih
      rw [Function.iterate_succ_apply']
      set iv := (bisectStep test)^[s] ⟨lo, hi⟩
      unfold bisectStep; dsimp only; split_ifs with hlt hb
      · have hhi := h3 hlt; simp only
        refine ⟨by omega, by omega, fun _ => hhi, fun m hm hmk => ?_, fun m hm => h5 m (by omega)⟩
        rcases Nat.lt_or_ge m iv.lo with hmlo | hmge
        · exact h4 m hm hmlo
        · exact hmono m ((iv.lo + iv.hi) / 2) hm (by omega) (by omega) hb
      · have hhi := h3 hlt; simp only
        refine ⟨h1, h2, fun _ => by omega, h4, fun m hm hmk => ?_⟩
        rcases Nat.lt_or_ge m iv.hi with hmhi | _
        · exact Bool.eq_false_iff.mpr fun htm =>
            hb (hmono ((iv.lo + iv.hi) / 2) m (by omega) (by omega) hmk htm)
        · exact h5 m (by omega) hmk
      · exact ⟨h1, h2, h3, h4, h5⟩
  obtain ⟨h1, h2, -, h4, h5⟩ := hinv (hi - lo).size
  have hw := (iterate_bisectStep_width_le test (hi - lo).size ⟨lo, hi⟩).trans_eq
    (Nat.div_eq_of_lt (Nat.lt_size_self (hi - lo)))
  exact ⟨h1, h2, h4, fun m hm hmk => h5 m (by omega) hmk⟩

/-- **Fixed-count bisection equals `lowerBound`** on every antitone test. -/
theorem iterate_bisectStep_eq_lowerBound (t : ℕ → Bool) {lo hi : ℕ}
    (hmono : ∀ m m', lo ≤ m → m ≤ m' → m' < hi → t m' = true → t m = true) :
    ((bisectStep t)^[(hi - lo).size] ⟨lo, hi⟩).lo = lowerBound t lo hi := by
  obtain ⟨h1, h2, h3, h4⟩ := iterate_bisectStep_spec (test := t) hmono
  obtain ⟨g1, g2, g3, g4⟩ := lowerBound_spec t hmono
  rcases Nat.lt_or_ge lo hi with hlt | hge
  · by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hk | hk
    · exact Bool.noConfusion ((g3 _ h1 hk).symm.trans (h4 _ le_rfl (by omega)))
    · exact Bool.noConfusion ((h3 _ g1 hk).symm.trans (g4 _ le_rfl (by omega)))
  · omega

/-! ### Bounded maximization and minimization in the threshold-probe query model -/

/-- Witness-search query signature for threshold optimization: `WitnessQuery.find q` requests a
witness achieving threshold `q : ℕ`, returning a value in `β`. -/
inductive WitnessQuery (β : Type) : Type → Type where
  /-- Request a candidate witness at threshold `q`. -/
  | find (q : ℕ) : WitnessQuery β β

/-- Lift `WitnessQuery.find q` into `FreeM (WitnessQuery β) β`. -/
abbrev WitnessQuery.ask {β : Type} (q : ℕ) : FreeM (WitnessQuery β) β :=
  FreeM.lift (.find q)

/-- Build a `WitnessQuery β` oracle from `ℕ → β`. -/
@[expose] def WitnessQuery.oracleOf {β : Type} (f : ℕ → β) :
    {ι : Type} → WitnessQuery β ι → ι
  | _, .find q => f q

@[simp] theorem WitnessQuery.oracleOf_find {β : Type} (f : ℕ → β) (q : ℕ) :
    WitnessQuery.oracleOf f (.find q) = f q := rfl

/-- Combined query signature for threshold optimization with witness recovery: `.inl (.probe q)`
queries threshold feasibility (`Bool`) and `.inr (.find q)` requests a witness (`β`) at threshold
`q`. -/
abbrev ThresholdWitnessQuery (β : Type) : Type → Type :=
  SumQuery ProbeQuery (WitnessQuery β)

/-- Combine a pure threshold predicate `probe : ℕ → Bool` and witness finder `find : ℕ → β` into
an oracle for `ThresholdWitnessQuery β`. -/
@[expose] def ThresholdWitnessQuery.oracleOf {β : Type} (probe : ℕ → Bool) (find : ℕ → β) :
    {ι : Type} → ThresholdWitnessQuery β ι → ι :=
  SumQuery.combine (ProbeQuery.oracleOf probe) (WitnessQuery.oracleOf find)

@[simp] theorem ThresholdWitnessQuery.oracleOf_probe {β : Type}
    (probe : ℕ → Bool) (find : ℕ → β) (q : ℕ) :
    ThresholdWitnessQuery.oracleOf probe find (.inl (.probe q)) = probe q := rfl

@[simp] theorem ThresholdWitnessQuery.oracleOf_find {β : Type}
    (probe : ℕ → Bool) (find : ℕ → β) (q : ℕ) :
    ThresholdWitnessQuery.oracleOf probe find (.inr (.find q)) = find q := rfl

/-- Specification of a bounded integer maximization problem on instances `α` and witnesses `β`:
valid witnesses of `x` have integer score bounded by `bound x`. -/
structure MaxThresholdSpec (α β : Type) where
  /-- Feasibility predicate for candidate witnesses of an instance. -/
  valid : α → β → Prop
  /-- Objective score of a candidate witness. -/
  score : α → β → ℕ
  /-- Upper bound on achievable scores for each instance. -/
  bound : α → ℕ
  /-- Every valid witness has score at most `bound x`. -/
  score_le_bound : ∀ x w, valid x w → score x w ≤ bound x

namespace MaxThresholdSpec

variable {α β : Type} (S : MaxThresholdSpec α β)

/-- Threshold decision predicate: some valid witness of `x` achieves score at least `q`. -/
@[expose]
def atLeast (x : α) (q : ℕ) : Prop :=
  ∃ w, S.valid x w ∧ q ≤ S.score x w

theorem atLeast_antitone {x : α} {q q' : ℕ} (hle : q ≤ q') (hq' : S.atLeast x q') :
    S.atLeast x q := by
  obtain ⟨w, hw, hsc⟩ := hq'
  exact ⟨w, hw, hle.trans hsc⟩

theorem not_atLeast_succ_bound (x : α) : ¬ S.atLeast x (S.bound x + 1) := by
  rintro ⟨w, hw, hsc⟩
  have := S.score_le_bound x w hw
  omega

/-- Pure bisection for the exact maximum score of `x` (or `none` if `x` has no valid witness) on
`[0, S.bound x + 1)`. -/
@[expose] def maxOpt (probe : α → ℕ → Bool) (x : α) : Option ℕ :=
  let k := lowerBound (probe x) 0 (S.bound x + 1)
  if k = 0 then none else some (k - 1)

/-- Correctness of `maxOpt`: returns `none` iff no valid witness exists, and `some v` when `v` is
the exact maximum score over valid witnesses. -/
theorem maxOpt_spec {probe : α → ℕ → Bool} {x : α}
    (hprobe : ∀ q, q ≤ S.bound x → (probe x q = true ↔ S.atLeast x q)) :
    (S.maxOpt probe x = none ↔ ¬ ∃ w, S.valid x w) ∧
      ∀ v, S.maxOpt probe x = some v →
        v ≤ S.bound x ∧ S.atLeast x v ∧ ∀ w, S.valid x w → S.score x w ≤ v := by
  obtain ⟨hlo, hhi, htrue, hfalse⟩ := lowerBound_spec (probe x) (lo := 0) (hi := S.bound x + 1)
    fun m m' _ hmm' hm' ht => (hprobe m (by omega)).mpr
      (S.atLeast_antitone hmm' ((hprobe m' (by omega)).mp ht))
  unfold maxOpt
  dsimp only
  set k := lowerBound (probe x) 0 (S.bound x + 1)
  refine ⟨?_, fun v hv => ?_⟩
  · split_ifs with hk0
    · exact iff_of_true rfl fun ⟨w, hw⟩ => Bool.noConfusion
        (((hprobe 0 (Nat.zero_le _)).mpr ⟨w, hw, Nat.zero_le _⟩).symm.trans
          (hfalse 0 (by omega) (by omega)))
    · refine ⟨by simp, fun hno => ?_⟩
      obtain ⟨w, hw, -⟩ := (hprobe 0 (Nat.zero_le _)).mp (htrue 0 (Nat.zero_le _) (by omega))
      exact hno ⟨w, hw⟩
  · split_ifs at hv with hk0
    rcases Option.some.inj hv with rfl
    refine ⟨by omega, (hprobe (k - 1) (by omega)).mp (htrue (k - 1) (Nat.zero_le _) (by omega)),
      fun w hw => ?_⟩
    by_contra! hgt
    have := S.score_le_bound x w hw
    exact Bool.noConfusion
      (((hprobe k (by omega)).mpr ⟨w, hw, by omega⟩).symm.trans (hfalse k le_rfl (by omega)))

/-- Pure recovery of both the maximum score and an optimal witness by running `maxOpt` and invoking
`findWitness` once at the optimal threshold. -/
@[expose] def maxOptWitness (probe : α → ℕ → Bool) (findWitness : α → ℕ → β) (x : α) :
    Option (OptSolution β) :=
  match S.maxOpt probe x with
  | none => none
  | some v => some ⟨v, findWitness x v⟩

/-- Correctness of `maxOptWitness`. -/
theorem maxOptWitness_spec {probe : α → ℕ → Bool} {findWitness : α → ℕ → β}
    {x : α} (hprobe : ∀ q, q ≤ S.bound x → (probe x q = true ↔ S.atLeast x q))
    (hwit : ∀ q, q ≤ S.bound x → S.atLeast x q →
      S.valid x (findWitness x q) ∧ q ≤ S.score x (findWitness x q)) :
    (S.maxOptWitness probe findWitness x = none ↔ ¬ ∃ w, S.valid x w) ∧
      ∀ sol, S.maxOptWitness probe findWitness x = some sol →
        sol.optValue ≤ S.bound x ∧ S.valid x sol.witness ∧
          S.score x sol.witness = sol.optValue ∧
          ∀ w, S.valid x w → S.score x w ≤ sol.optValue := by
  obtain ⟨hnone, hsome⟩ := S.maxOpt_spec hprobe
  unfold maxOptWitness
  cases hm : S.maxOpt probe x with
  | none =>
    simp only [true_iff, reduceCtorEq, IsEmpty.forall_iff, implies_true, and_true]
    exact hnone.mp hm
  | some v =>
    obtain ⟨hv_le, hat, hmax⟩ := hsome v hm
    obtain ⟨hvw, hvsc⟩ := hwit v hv_le hat
    simp only [reduceCtorEq, false_iff, Option.some.injEq, forall_eq']
    exact ⟨fun hno => hno ⟨_, hvw⟩, hv_le, hvw, le_antisymm (hmax _ hvw) hvsc, hmax⟩

/-- Query-monad maximization program on `[0, S.bound x + 1)` over `ProbeQuery`. -/
@[expose] def maxOptQ (x : α) : FreeM ProbeQuery (Option ℕ) :=
  (fun k => if k = 0 then none else some (k - 1)) <$> lowerBoundQ 0 (S.bound x + 1)

@[simp] theorem eval_maxOptQ (oracle : {ι : Type} → ProbeQuery ι → ι) (x : α) :
    (S.maxOptQ x).eval oracle = S.maxOpt (fun _ q => oracle (.probe q)) x := by
  simp only [maxOptQ, maxOpt, FreeM.eval_map, eval_lowerBoundQ]

/-- `maxOptQ x` makes at most `Nat.log 2 (S.bound x + 1) + 1` threshold probes. -/
theorem countQueries_maxOptQ_le (oracle : {ι : Type} → ProbeQuery ι → ι) (x : α) :
    (S.maxOptQ x).countQueries oracle ≤ Nat.log 2 (S.bound x + 1) + 1 := by
  simpa only [maxOptQ, FreeM.countQueries_map, Nat.sub_zero] using
    countQueries_lowerBoundQ_le oracle 0 (S.bound x + 1)

/-- Query-monad maximization with witness recovery over `ThresholdWitnessQuery β`: makes at most
`Nat.log 2 (S.bound x + 1) + 1` threshold decision queries (`countInl`) and at most `1` witness
query (`countInr`, `0` when infeasible). -/
@[expose] def maxOptWitnessQ (x : α) :
    FreeM (ThresholdWitnessQuery β) (Option (OptSolution β)) := do
  let k ← lowerBoundBy (fun q => SumQuery.liftInl (.probe q)) 0 (S.bound x + 1)
  if k = 0 then
    pure none
  else
    (fun w => some (OptSolution.mk (k - 1) w)) <$> SumQuery.liftInr (.find (k - 1))

@[simp] theorem eval_maxOptWitnessQ (oracle : {ι : Type} → ThresholdWitnessQuery β ι → ι) (x : α) :
    (S.maxOptWitnessQ x).eval oracle =
      S.maxOptWitness (fun _ q => oracle (.inl (.probe q)))
        (fun _ q => oracle (.inr (.find q))) x := by
  simp only [maxOptWitnessQ, maxOptWitness, maxOpt, FreeM.eval_bind, eval_lowerBoundBy,
    FreeM.eval_lift]
  split_ifs <;> simp only [FreeM.eval_pure, FreeM.eval_map, FreeM.eval_lift]

/-- Exact witness-query count of `maxOptWitnessQ`: `1` when a valid witness is returned
(`eval = some _`), and `0` when infeasible (`eval = none`). -/
@[simp] theorem countInr_maxOptWitnessQ (oracle : {ι : Type} → ThresholdWitnessQuery β ι → ι)
    (x : α) :
    SumQuery.countInr oracle (S.maxOptWitnessQ x) =
      if ((S.maxOptWitnessQ x).eval oracle).isSome then 1 else 0 := by
  have hinr_bisect : SumQuery.countInr oracle
      (lowerBoundBy (fun q => SumQuery.liftInl (.probe q)) 0 (S.bound x + 1)) = 0 :=
    Nat.eq_zero_of_le_zero <| by
      simpa only [SumQuery.countInr, zero_mul] using
        cost_lowerBoundBy_le oracle SumQuery.weightInr
          (fun q => SumQuery.liftInl (.probe q)) (c := 0) (lo := 0) (hi := S.bound x + 1)
          fun _ _ _ => by simp only [FreeM.cost_lift, SumQuery.weightInr, le_rfl]
  simp only [maxOptWitnessQ, SumQuery.countInr_bind, FreeM.eval_bind, eval_lowerBoundBy,
    FreeM.eval_lift, hinr_bisect, zero_add]
  by_cases hk : lowerBound (fun m => oracle (.inl (.probe m))) 0 (S.bound x + 1) = 0
  · simp only [hk, ↓reduceIte, SumQuery.countInr_pure, FreeM.eval_pure, Option.isSome_none,
      Bool.false_eq_true]
  · simp only [hk, ↓reduceIte, SumQuery.countInr_map, SumQuery.countInr_liftInr, FreeM.eval_map,
      FreeM.eval_lift, Option.isSome_some]

/-- **Query-complexity bounds for `maxOptWitnessQ`**: at most `Nat.log 2 (S.bound x + 1) + 1`
threshold decision queries (`countInl`), at most `1` witness query (`countInr`), and at most
`Nat.log 2 (S.bound x + 1) + 2` total queries. -/
theorem maxOptWitnessQ_query_bounds (oracle : {ι : Type} → ThresholdWitnessQuery β ι → ι)
    (x : α) :
    SumQuery.countInl oracle (S.maxOptWitnessQ x) ≤ Nat.log 2 (S.bound x + 1) + 1 ∧
      SumQuery.countInr oracle (S.maxOptWitnessQ x) ≤ 1 ∧
      (S.maxOptWitnessQ x).countQueries oracle ≤ Nat.log 2 (S.bound x + 1) + 2 := by
  have hinl_bisect : SumQuery.countInl oracle
      (lowerBoundBy (fun q => SumQuery.liftInl (.probe q)) 0 (S.bound x + 1)) ≤
      Nat.log 2 (S.bound x + 1) + 1 := by
    simpa only [SumQuery.countInl, one_mul, Nat.sub_zero] using
      cost_lowerBoundBy_le oracle SumQuery.weightInl
        (fun q => SumQuery.liftInl (.probe q)) (c := 1) (lo := 0) (hi := S.bound x + 1)
        fun _ _ _ => by simp only [FreeM.cost_lift, SumQuery.weightInl, le_rfl]
  have hinl : SumQuery.countInl oracle (S.maxOptWitnessQ x) ≤ Nat.log 2 (S.bound x + 1) + 1 := by
    simp only [maxOptWitnessQ, SumQuery.countInl_bind, eval_lowerBoundBy, FreeM.eval_lift]
    split_ifs <;>
      simp only [SumQuery.countInl_pure, SumQuery.countInl_map, SumQuery.countInl_liftInr,
        add_zero, hinl_bisect]
  have hinr : SumQuery.countInr oracle (S.maxOptWitnessQ x) ≤ 1 := by
    rw [S.countInr_maxOptWitnessQ oracle x]
    split_ifs <;> omega
  have htot := SumQuery.countInl_add_countInr oracle (S.maxOptWitnessQ x)
  exact ⟨hinl, hinr, by omega⟩

/-- **Weighted query-cost bound for `maxOptWitnessQ`**: if decision probes at `q ≤ S.bound x` have
weight at most `cp` and witness queries at `q ≤ S.bound x` have weight at most `cw`, then
`maxOptWitnessQ x` has cost at most `cp * (Nat.log 2 (S.bound x + 1) + 1) + cw`. -/
theorem cost_maxOptWitnessQ_le (oracle : {ι : Type} → ThresholdWitnessQuery β ι → ι)
    (weight : {ι : Type} → ThresholdWitnessQuery β ι → ℕ) {x : α} {cp cw : ℕ}
    (hcp : ∀ q, q ≤ S.bound x → weight (.inl (.probe q)) ≤ cp)
    (hcw : ∀ q, q ≤ S.bound x → weight (.inr (.find q)) ≤ cw) :
    (S.maxOptWitnessQ x).cost oracle weight ≤
      cp * (Nat.log 2 (S.bound x + 1) + 1) + cw := by
  have hbase : (lowerBoundBy (fun q => SumQuery.liftInl (.probe q)) 0 (S.bound x + 1)).cost
      oracle weight ≤ cp * (Nat.log 2 (S.bound x + 1) + 1) := by
    simpa only [Nat.sub_zero] using
      cost_lowerBoundBy_le oracle weight (fun q => SumQuery.liftInl (.probe q))
        (c := cp) (lo := 0) (hi := S.bound x + 1) fun m _ hm => by
        simpa only [FreeM.cost_lift] using hcp m (by omega)
  simp only [maxOptWitnessQ, FreeM.cost_bind, eval_lowerBoundBy, FreeM.eval_lift]
  set k := lowerBound (fun m => oracle (.inl (.probe m))) 0 (S.bound x + 1)
  have hk_hi : k ≤ S.bound x + 1 := by
    have := (lowerBound_bounds (fun m => oracle (.inl (.probe m))) 0 (S.bound x + 1)).2
    omega
  split_ifs with hk0
  · simp only [FreeM.cost_pure, add_zero]
    omega
  · simp only [FreeM.cost_map, FreeM.cost_lift]
    have hw := hcw (k - 1) (by omega)
    omega

end MaxThresholdSpec

/-- Specification of a bounded integer minimization problem on instances `α` and witnesses `β`:
valid witnesses of `x` have integer cost bounded by `bound x`. -/
structure MinThresholdSpec (α β : Type) where
  /-- Feasibility predicate for candidate witnesses of an instance. -/
  valid : α → β → Prop
  /-- Objective cost of a candidate witness. -/
  cost : α → β → ℕ
  /-- Upper bound on the cost of valid witnesses. -/
  bound : α → ℕ
  /-- Every valid witness has cost at most `bound x`. -/
  cost_le_bound : ∀ x w, valid x w → cost x w ≤ bound x

namespace MinThresholdSpec

variable {α β : Type} (S : MinThresholdSpec α β)

/-- Threshold decision predicate: some valid witness of `x` has cost at most `q`. -/
@[expose]
def atMost (x : α) (q : ℕ) : Prop :=
  ∃ w, S.valid x w ∧ S.cost x w ≤ q

theorem atMost_monotone {x : α} {q q' : ℕ} (hle : q ≤ q') (hq : S.atMost x q) :
    S.atMost x q' := by
  obtain ⟨w, hw, hc⟩ := hq
  exact ⟨w, hw, hc.trans hle⟩

/-- Pure bisection for the exact minimum cost of `x` (or `none` if `x` has no valid witness) by
bisecting the negated threshold predicate on `[0, S.bound x + 1)`. -/
@[expose] def minOpt (probe : α → ℕ → Bool) (x : α) : Option ℕ :=
  let k := lowerBound (fun q => !(probe x q)) 0 (S.bound x + 1)
  if k ≤ S.bound x then some k else none

/-- Correctness of `minOpt`: returns `none` iff no valid witness exists, and `some v` when `v` is
the exact minimum cost over valid witnesses. -/
theorem minOpt_spec {probe : α → ℕ → Bool} {x : α}
    (hprobe : ∀ q, q ≤ S.bound x → (probe x q = true ↔ S.atMost x q)) :
    (S.minOpt probe x = none ↔ ¬ ∃ w, S.valid x w) ∧
      ∀ v, S.minOpt probe x = some v →
        v ≤ S.bound x ∧ S.atMost x v ∧ ∀ w, S.valid x w → v ≤ S.cost x w := by
  obtain ⟨-, hhi, htrue, hfalse⟩ := lowerBound_spec (fun q => !(probe x q))
    (lo := 0) (hi := S.bound x + 1) fun m m' _ hmm' hm' ht => by
      simp only [Bool.not_eq_true'] at ht ⊢
      exact Bool.eq_false_iff.mpr fun hm => Bool.noConfusion
        (ht.symm.trans ((hprobe m' (by omega)).mpr (S.atMost_monotone hmm'
          ((hprobe m (by omega)).mp hm))))
  set k := lowerBound (fun q => !(probe x q)) 0 (S.bound x + 1) with hk_def
  have hge_k : ∀ w, S.valid x w → k ≤ S.cost x w := fun w hw => Nat.le_of_not_lt fun hlt => by
    have ht := htrue (S.cost x w) (Nat.zero_le _) hlt
    simp only [Bool.not_eq_true'] at ht
    exact Bool.noConfusion
      (ht.symm.trans ((hprobe _ (S.cost_le_bound x w hw)).mpr ⟨w, hw, le_rfl⟩))
  unfold minOpt
  dsimp only
  rw [← hk_def]
  split_ifs with hle
  · have hf := hfalse k le_rfl (by omega)
    simp only [Bool.not_eq_false'] at hf
    obtain ⟨w₀, hw₀, hcw₀⟩ := (hprobe k hle).mp hf
    simp only [false_iff, Option.some.injEq, forall_eq']
    exact ⟨fun hne => hne ⟨w₀, hw₀⟩, hle, ⟨w₀, hw₀, hcw₀⟩, hge_k⟩
  · simp only [true_iff, IsEmpty.forall_iff, implies_true, and_true]
    exact fun ⟨w, hw⟩ => absurd (le_trans (hge_k w hw) (S.cost_le_bound x w hw)) hle

/-- Pure recovery of both the minimum cost and an optimal witness. -/
@[expose] def minOptWitness (probe : α → ℕ → Bool) (findWitness : α → ℕ → β) (x : α) :
    Option (OptSolution β) :=
  match S.minOpt probe x with
  | none => none
  | some v => some ⟨v, findWitness x v⟩

/-- Correctness of `minOptWitness`. -/
theorem minOptWitness_spec {probe : α → ℕ → Bool} {findWitness : α → ℕ → β}
    {x : α} (hprobe : ∀ q, q ≤ S.bound x → (probe x q = true ↔ S.atMost x q))
    (hwit : ∀ q, q ≤ S.bound x → S.atMost x q →
      S.valid x (findWitness x q) ∧ S.cost x (findWitness x q) ≤ q) :
    (S.minOptWitness probe findWitness x = none ↔ ¬ ∃ w, S.valid x w) ∧
      ∀ sol, S.minOptWitness probe findWitness x = some sol →
        sol.optValue ≤ S.bound x ∧ S.valid x sol.witness ∧
          S.cost x sol.witness = sol.optValue ∧
          ∀ w, S.valid x w → sol.optValue ≤ S.cost x w := by
  obtain ⟨hnone, hsome⟩ := S.minOpt_spec hprobe
  unfold minOptWitness
  cases hm : S.minOpt probe x with
  | none =>
    simp only [true_iff, reduceCtorEq, IsEmpty.forall_iff, implies_true, and_true]
    exact hnone.mp hm
  | some v =>
    obtain ⟨hv_le, hat, hmin⟩ := hsome v hm
    obtain ⟨hvw, hvsc⟩ := hwit v hv_le hat
    simp only [reduceCtorEq, false_iff, Option.some.injEq, forall_eq']
    exact ⟨fun hno => hno ⟨_, hvw⟩, hv_le, hvw, le_antisymm hvsc (hmin _ hvw), hmin⟩

/-- Query-monad minimization program on `[0, S.bound x + 1)` over `ProbeQuery`. -/
@[expose] def minOptQ (x : α) : FreeM ProbeQuery (Option ℕ) :=
  (fun k => if k ≤ S.bound x then some k else none) <$>
    lowerBoundBy (fun q => Bool.not <$> ProbeQuery.ask q) 0 (S.bound x + 1)

@[simp] theorem eval_minOptQ (oracle : {ι : Type} → ProbeQuery ι → ι) (x : α) :
    (S.minOptQ x).eval oracle = S.minOpt (fun _ q => oracle (.probe q)) x := by
  simp only [minOptQ, minOpt, FreeM.eval_map, eval_lowerBoundBy, ProbeQuery.eval_ask]

/-- `minOptQ x` makes at most `Nat.log 2 (S.bound x + 1) + 1` threshold probes. -/
theorem countQueries_minOptQ_le (oracle : {ι : Type} → ProbeQuery ι → ι) (x : α) :
    (S.minOptQ x).countQueries oracle ≤ Nat.log 2 (S.bound x + 1) + 1 := by
  simpa only [minOptQ, FreeM.countQueries_map, one_mul, Nat.sub_zero] using
    countQueries_lowerBoundBy_le oracle (fun q => Bool.not <$> ProbeQuery.ask q)
      (c := 1) (lo := 0) (hi := S.bound x + 1) fun _ _ _ => by
      simp only [FreeM.countQueries_map, FreeM.countQueries_lift, le_rfl]

/-- Query-monad minimization with witness recovery over `ThresholdWitnessQuery β`: makes at most
`Nat.log 2 (S.bound x + 1) + 1` threshold decision queries (`countInl`) and at most `1` witness
query (`countInr`, `0` when infeasible). -/
@[expose] def minOptWitnessQ (x : α) :
    FreeM (ThresholdWitnessQuery β) (Option (OptSolution β)) := do
  let k ← lowerBoundBy (fun q => Bool.not <$> SumQuery.liftInl (.probe q)) 0 (S.bound x + 1)
  if k ≤ S.bound x then
    (fun w => some (OptSolution.mk k w)) <$> SumQuery.liftInr (.find k)
  else
    pure none

@[simp] theorem eval_minOptWitnessQ (oracle : {ι : Type} → ThresholdWitnessQuery β ι → ι) (x : α) :
    (S.minOptWitnessQ x).eval oracle =
      S.minOptWitness (fun _ q => oracle (.inl (.probe q)))
        (fun _ q => oracle (.inr (.find q))) x := by
  simp only [minOptWitnessQ, minOptWitness, minOpt, FreeM.eval_bind, eval_lowerBoundBy,
    FreeM.eval_map, FreeM.eval_lift]
  split_ifs <;> simp only [FreeM.eval_map, FreeM.eval_lift, FreeM.eval_pure]

/-- Exact witness-query count of `minOptWitnessQ`: `1` when a valid witness is returned
(`eval = some _`), and `0` when infeasible (`eval = none`). -/
@[simp] theorem countInr_minOptWitnessQ (oracle : {ι : Type} → ThresholdWitnessQuery β ι → ι)
    (x : α) :
    SumQuery.countInr oracle (S.minOptWitnessQ x) =
      if ((S.minOptWitnessQ x).eval oracle).isSome then 1 else 0 := by
  have hinr_bisect : SumQuery.countInr oracle
      (lowerBoundBy (fun q => Bool.not <$> SumQuery.liftInl (.probe q)) 0 (S.bound x + 1)) = 0 :=
    Nat.eq_zero_of_le_zero <| by
      simpa only [SumQuery.countInr, zero_mul] using
        cost_lowerBoundBy_le oracle SumQuery.weightInr
          (fun q => Bool.not <$> SumQuery.liftInl (.probe q))
          (c := 0) (lo := 0) (hi := S.bound x + 1) fun _ _ _ => by
          simp only [FreeM.cost_map, FreeM.cost_lift, SumQuery.weightInr, le_rfl]
  simp only [minOptWitnessQ, SumQuery.countInr_bind, FreeM.eval_bind, eval_lowerBoundBy,
    FreeM.eval_map, FreeM.eval_lift, hinr_bisect, zero_add]
  by_cases hk : lowerBound (fun m => !oracle (.inl (.probe m))) 0 (S.bound x + 1) ≤ S.bound x
  · simp only [hk, ↓reduceIte, SumQuery.countInr_map, SumQuery.countInr_liftInr, FreeM.eval_map,
      FreeM.eval_lift, Option.isSome_some]
  · simp only [hk, ↓reduceIte, SumQuery.countInr_pure, FreeM.eval_pure, Option.isSome_none,
      Bool.false_eq_true]

/-- **Query-complexity bounds for `minOptWitnessQ`**: at most `Nat.log 2 (S.bound x + 1) + 1`
threshold decision queries (`countInl`), at most `1` witness query (`countInr`), and at most
`Nat.log 2 (S.bound x + 1) + 2` total queries. -/
theorem minOptWitnessQ_query_bounds (oracle : {ι : Type} → ThresholdWitnessQuery β ι → ι)
    (x : α) :
    SumQuery.countInl oracle (S.minOptWitnessQ x) ≤ Nat.log 2 (S.bound x + 1) + 1 ∧
      SumQuery.countInr oracle (S.minOptWitnessQ x) ≤ 1 ∧
      (S.minOptWitnessQ x).countQueries oracle ≤ Nat.log 2 (S.bound x + 1) + 2 := by
  have hinl_bisect : SumQuery.countInl oracle
      (lowerBoundBy (fun q => Bool.not <$> SumQuery.liftInl (.probe q)) 0 (S.bound x + 1)) ≤
      Nat.log 2 (S.bound x + 1) + 1 := by
    simpa only [SumQuery.countInl, one_mul, Nat.sub_zero] using
      cost_lowerBoundBy_le oracle SumQuery.weightInl
        (fun q => Bool.not <$> SumQuery.liftInl (.probe q))
        (c := 1) (lo := 0) (hi := S.bound x + 1) fun _ _ _ => by
        simp only [FreeM.cost_map, FreeM.cost_lift, SumQuery.weightInl, le_rfl]
  have hinl : SumQuery.countInl oracle (S.minOptWitnessQ x) ≤ Nat.log 2 (S.bound x + 1) + 1 := by
    simp only [minOptWitnessQ, SumQuery.countInl_bind, eval_lowerBoundBy, FreeM.eval_map,
      FreeM.eval_lift]
    split_ifs <;>
      simp only [SumQuery.countInl_pure, SumQuery.countInl_map, SumQuery.countInl_liftInr,
        add_zero, hinl_bisect]
  have hinr : SumQuery.countInr oracle (S.minOptWitnessQ x) ≤ 1 := by
    rw [S.countInr_minOptWitnessQ oracle x]
    split_ifs <;> omega
  have htot := SumQuery.countInl_add_countInr oracle (S.minOptWitnessQ x)
  exact ⟨hinl, hinr, by omega⟩

/-- **Weighted query-cost bound for `minOptWitnessQ`**: if decision probes at `q ≤ S.bound x` have
weight at most `cp` and witness queries at `q ≤ S.bound x` have weight at most `cw`, then
`minOptWitnessQ x` has cost at most `cp * (Nat.log 2 (S.bound x + 1) + 1) + cw`. -/
theorem cost_minOptWitnessQ_le (oracle : {ι : Type} → ThresholdWitnessQuery β ι → ι)
    (weight : {ι : Type} → ThresholdWitnessQuery β ι → ℕ) {x : α} {cp cw : ℕ}
    (hcp : ∀ q, q ≤ S.bound x → weight (.inl (.probe q)) ≤ cp)
    (hcw : ∀ q, q ≤ S.bound x → weight (.inr (.find q)) ≤ cw) :
    (S.minOptWitnessQ x).cost oracle weight ≤
      cp * (Nat.log 2 (S.bound x + 1) + 1) + cw := by
  have hbase : (lowerBoundBy (fun q => Bool.not <$> SumQuery.liftInl (.probe q))
      0 (S.bound x + 1)).cost oracle weight ≤ cp * (Nat.log 2 (S.bound x + 1) + 1) := by
    simpa only [Nat.sub_zero] using
      cost_lowerBoundBy_le oracle weight
        (fun q => Bool.not <$> SumQuery.liftInl (.probe q))
        (c := cp) (lo := 0) (hi := S.bound x + 1) fun m _ hm => by
        simpa only [FreeM.cost_map, FreeM.cost_lift] using hcp m (by omega)
  simp only [minOptWitnessQ, FreeM.cost_bind, eval_lowerBoundBy, FreeM.eval_map, FreeM.eval_lift]
  split_ifs with hle
  · simp only [FreeM.cost_map, FreeM.cost_lift]
    have hw := hcw _ hle
    omega
  · simp only [FreeM.cost_pure, add_zero]
    omega

end MinThresholdSpec

/-! ### Sequential composition for query-bounded oracle programs -/

namespace ComputableInPolyTimeWithOracleQueries

/-- **Query-bounded sequential composition.** If `first` computes `f : α → β` with at most `r₁ |a|`
requests and `second` computes `g : α × β → γ` with at most `r₂ |encPair input middle (a, b)|`
requests, and the intermediate encoding length is bounded by `midLen |a|`, then `a ↦ g a (f a)`
is computable in polynomial time relative to `A` with at most `r₁ |a| + r₂ (midLen |a|)`
requests. -/
theorem bind_with {α β γ : Type} {A : Set (List Bool)} {r₁ r₂ midLen : ℕ → ℕ}
    {input : α ↪ List Bool} {middle : β ↪ List Bool} {output : γ ↪ List Bool}
    {f : α → β} {g : α → β → γ}
    (hf : ComputableInPolyTimeWithOracleQueries A r₁ f input middle)
    (hg : ComputableInPolyTimeWithOracleQueries A r₂ (fun p : α × β => g p.1 p.2)
      (encPair input middle) output)
    (hr₂ : Monotone r₂)
    (hmid : ∀ a, (encPair input middle (a, f a)).length ≤ midLen (input a).length) :
    ComputableInPolyTimeWithOracleQueries A (fun n => r₁ n + r₂ (midLen n))
      (fun a => g a (f a)) input output := by
  obtain ⟨p₁, hp₁_cert, hp₁⟩ := hf
  obtain ⟨p₂, hp₂_cert, hp₂⟩ := hg
  refine ⟨fun a => p₁ a >>= fun b => p₂ (a, b), ?_, fun a => ⟨?_, ?_⟩⟩
  · simpa only [OracleComp.interpret_bind] using hp₁_cert.bind_with hp₂_cert
  · rw [OracleComp.interpret_bind]
    change OracleComp.interpret (m := Id) (languageOracle A)
      (p₂ (a, OracleComp.interpret (m := Id) (languageOracle A) (p₁ a))) = g a (f a)
    rw [(hp₁ a).1, (hp₂ (a, f a)).1]
  · rw [OracleComp.queriesWith_bind, List.length_append, (hp₁ a).1]
    exact Nat.add_le_add (hp₁ a).2 ((hp₂ (a, f a)).2.trans (hr₂ (hmid a)))

/-- Preprocess the input of a query-bounded oracle computation when the preprocessing map stretches
encoded lengths by at most `stretch`. -/
theorem preprocess {α β γ : Type} {A : Set (List Bool)} {r stretch : ℕ → ℕ}
    {input : α ↪ List Bool} {middle : β ↪ List Bool} {output : γ ↪ List Bool}
    {f : β → γ} {g : α → β}
    (hf : ComputableInPolyTimeWithOracleQueries A r f middle output)
    (hg : ComputableInPolyTime g input middle)
    (hr : Monotone r)
    (hstretch : ∀ a, (middle (g a)).length ≤ stretch (input a).length) :
    ComputableInPolyTimeWithOracleQueries A (fun n => r (stretch n)) (fun a => f (g a))
      input output := by
  obtain ⟨prog, hcert, hprog⟩ := hf
  exact ⟨fun a => prog (g a), hcert.preprocess hg, fun a =>
    ⟨(hprog (g a)).1, (hprog (g a)).2.trans (hr (hstretch a))⟩⟩

end ComputableInPolyTimeWithOracleQueries

/-! ### Native oracle bisection program -/

/-- One adaptive step of oracle bisection: if `iv.lo < iv.hi`, query `req a ((iv.lo + iv.hi) / 2)`
via `queryBit` and narrow `iv`; otherwise leave `iv` unchanged without querying. -/
def bisectStepProgram {α : Type} (req : α → ℕ → List Bool) (a : α) (iv : BisectInterval) :
    WordQueryComp Unit BisectInterval :=
  if iv.lo < iv.hi then
    let mid := (iv.lo + iv.hi) / 2
    (fun b => if b then ⟨mid + 1, iv.hi⟩ else ⟨iv.lo, mid⟩) <$> queryBit (req a mid)
  else pure iv

/-- Adaptive oracle bisection on `[lo a, hi a)`: iterate `bisectStepProgram` `(hi a - lo a).size`
times and return the final `lo`. -/
def bisectProgram {α : Type} (req : α → ℕ → List Bool) (lo hi : α → ℕ) (a : α) :
    WordQueryComp Unit ℕ :=
  BisectInterval.lo <$>
    OracleComp.iterate ((hi a - lo a).size) (bisectStepProgram req a) ⟨lo a, hi a⟩

open Classical in
/-- Against `languageOracle A`, one step of `bisectStepProgram` is `bisectStep`. -/
theorem interpret_bisectStepProgram {α : Type} (A : Set (List Bool)) (req : α → ℕ → List Bool)
    (a : α) (iv : BisectInterval) :
    OracleComp.interpret (m := Id) (languageOracle A) (bisectStepProgram req a iv) =
      bisectStep (fun m => decide (req a m ∈ A)) iv := by
  unfold bisectStepProgram bisectStep
  split_ifs
  · rw [OracleComp.interpret_map, interpret_queryBit]
    rfl
  · rfl

open Classical in
/-- Against `languageOracle A`, `bisectProgram` computes
`((bisectStep ...)^[(hi a - lo a).size] ⟨lo a, hi a⟩).lo`. -/
theorem interpret_bisectProgram {α : Type} (A : Set (List Bool)) (req : α → ℕ → List Bool)
    (lo hi : α → ℕ) (a : α) :
    OracleComp.interpret (m := Id) (languageOracle A) (bisectProgram req lo hi a) =
      ((bisectStep (fun m => decide (req a m ∈ A)))^[(hi a - lo a).size] ⟨lo a, hi a⟩).lo := by
  rw [bisectProgram, OracleComp.interpret_map, OracleComp.interpret_id_iterate]
  have hfun : (fun iv => OracleComp.interpret (m := Id) (languageOracle A)
      (bisectStepProgram req a iv)) = bisectStep (fun m => decide (req a m ∈ A)) :=
    funext (interpret_bisectStepProgram A req a)
  exact congrArg (fun f => (f^[(hi a - lo a).size] ⟨lo a, hi a⟩).lo) hfun

/-- `bisectProgram` makes at most `(hi a - lo a).size` requests (hence at most
`Nat.log 2 (hi a - lo a) + 1`). -/
theorem length_queriesWith_bisectProgram_le {α : Type}
    (answer : Unit × List Bool → List Bool) (req : α → ℕ → List Bool) (lo hi : α → ℕ) (a : α) :
    (OracleComp.queriesWith answer (bisectProgram req lo hi a)).length ≤ (hi a - lo a).size := by
  rw [bisectProgram, OracleComp.queriesWith_map]
  have hstep : ∀ iv, (OracleComp.queriesWith answer (bisectStepProgram req a iv)).length ≤ 1 := by
    intro iv
    unfold bisectStepProgram
    split_ifs <;> simp
  simpa using OracleComp.length_queriesWith_iterate_le answer hstep ((hi a - lo a).size)
    ⟨lo a, hi a⟩

/-- Every word queried by `bisectProgram` is `req a m` for a midpoint `lo a ≤ m < hi a`. -/
theorem mem_queriesWith_bisectProgram {α : Type}
    (answer : Unit × List Bool → List Bool) (req : α → ℕ → List Bool) (lo hi : α → ℕ) (a : α)
    {q : Unit × List Bool}
    (hq : q ∈ OracleComp.queriesWith answer (bisectProgram req lo hi a)) :
    ∃ m, lo a ≤ m ∧ m < hi a ∧ q = ((), req a m) := by
  rw [bisectProgram, OracleComp.queriesWith_map] at hq
  obtain ⟨iv, ⟨hlo, hhi⟩, hq_step⟩ := Cslib.OracleComp.mem_queriesWith_iterate answer
    (inv := fun iv : BisectInterval => lo a ≤ iv.lo ∧ (iv.lo < iv.hi → iv.hi ≤ hi a))
    ⟨le_rfl, fun _ => le_rfl⟩
    (fun iv ⟨hlo, hhi⟩ => by
      unfold bisectStepProgram
      split_ifs with hlt
      · have hhi' := hhi hlt
        rw [OracleComp.interpret_map]
        cases (OracleComp.interpret (m := Id) answer
          (queryBit (req a ((iv.lo + iv.hi) / 2))) : Bool)
        · refine ⟨hlo, fun _ => ?_⟩
          dsimp only [Functor.map]
          simp only [Bool.false_eq_true, ↓reduceIte]; omega
        · refine ⟨?_, fun _ => hhi'⟩
          dsimp only [Functor.map]
          simp only [↓reduceIte]; omega
      · exact ⟨hlo, hhi⟩) hq
  unfold bisectStepProgram at hq_step
  split_ifs at hq_step with hlt
  · simp only [queryBit, OracleComp.queriesWith_map, OracleComp.queriesWith_query,
      List.mem_singleton] at hq_step
    exact ⟨(iv.lo + iv.hi) / 2, by omega, by have := hhi hlt; omega, hq_step⟩
  · simp at hq_step

open ComputableInPolyTime in
private theorem isOraclePPTOn_bisectStepProgram {α : Type} {encA : α ↪ List Bool}
    {req : α → ℕ → List Bool}
    (hreq : ComputableInPolyTime (fun q : OracleThresholdQuery α => req q.inst q.target)
      (encOracleThresholdQuery encA) encBits) :
    IsOraclePPTOn (encPair encA encBisectInterval) encBisectInterval
      (fun pair => OracleComp.interpret ProbOracleComp.query
        (bisectStepProgram req pair.1 pair.2)) := by
  have hmid : ComputableInPolyTime (fun p : α × BisectInterval => (p.2.lo + p.2.hi) / 2)
      (encPair encA encBisectInterval) encNat :=
    (binary_shiftRight' (binary_add' (encBisectInterval_lo_polyTime (snd _ _))
      (encBisectInterval_hi_polyTime (snd _ _))) (const 1)).of_enc_eq fun _ => by
      rw [Nat.shiftRight_eq_div_pow, pow_one]
  have hword : ComputableInPolyTime
      (fun p : α × BisectInterval => req p.1 ((p.2.lo + p.2.hi) / 2))
      (encPair encA encBisectInterval) encBits :=
    hreq.comp (encOracleThresholdQuery_mk_polyTime (fst _ _) hmid)
  have hcond : ComputableInPolyTime (fun p : α × BisectInterval => decide (p.2.lo < p.2.hi))
      (encPair encA encBisectInterval) encBool :=
    binary_lt' (encBisectInterval_lo_polyTime (snd _ _)) (encBisectInterval_hi_polyTime (snd _ _))
  have hmid' := hmid.comp (fst (encPair encA encBisectInterval) encBool)
  have hbranch : ComputableInPolyTime
      (fun p : (α × BisectInterval) × Bool =>
        let mid := (p.1.2.lo + p.1.2.hi) / 2
        if p.2 then BisectInterval.mk (mid + 1) p.1.2.hi else ⟨p.1.2.lo, mid⟩)
      (encPair (encPair encA encBisectInterval) encBool) encBisectInterval :=
    (ite' (snd _ _)
      (encBisectInterval_mk_polyTime (binary_add' hmid' (const 1))
        (encBisectInterval_hi_polyTime ((snd _ _).comp (fst _ _))))
      (encBisectInterval_mk_polyTime
        (encBisectInterval_lo_polyTime ((snd _ _).comp (fst _ _))) hmid')).of_enc_eq fun p => by
      cases p.2 <;> rfl
  have hyes := (isOraclePPTOn_queryBit hword).map_with
    (f := fun (p : α × BisectInterval) (b : Bool) =>
      let mid := (p.2.lo + p.2.hi) / 2
      if b then BisectInterval.mk (mid + 1) p.2.hi else BisectInterval.mk p.2.lo mid)
    hbranch
  refine (IsOraclePPTOn.ite (condition := fun p : α × BisectInterval => p.2.lo < p.2.hi)
    hcond hyes (snd encA encBisectInterval).isOraclePPTOn).congr fun p State oracle s => ?_
  unfold bisectStepProgram
  split_ifs <;> simp only [OracleComp.interpret_map, OracleComp.interpret_pure]

/-- `bisectProgram` is strict oracle PPT whenever `lo`, `hi`, and the threshold request builder
`req` are polynomial-time. -/
theorem isOraclePPTOn_bisectProgram {α : Type} {encA : α ↪ List Bool}
    {req : α → ℕ → List Bool} {lo hi : α → ℕ}
    (hreq : ComputableInPolyTime (fun q : OracleThresholdQuery α => req q.inst q.target)
      (encOracleThresholdQuery encA) encBits)
    (hlo : ComputableInPolyTime lo encA encNat)
    (hhi : ComputableInPolyTime hi encA encNat) :
    IsOraclePPTOn encA encNat
      (fun a => OracleComp.interpret ProbOracleComp.query (bisectProgram req lo hi a)) := by
  open ComputableInPolyTime in
  obtain ⟨cL, dL, hlenL⟩ := hlo.polyBounded_length.exists_le
  obtain ⟨cH, dH, hlenH⟩ := hhi.polyBounded_length.exists_le
  have hsize : PolyBounded (fun a => (encA a).length)
      (fun a => 4 * (cL * ((encA a).length + 1) ^ dL + cH * ((encA a).length + 1) ^ dH) + 4) := by
    growth_poly
  have hit := IsOraclePPTOn.iterateWith_spec (input := encA)
    (stateEncoding := encBisectInterval)
    (count := fun a => (hi a - lo a).size)
    (initial := fun a => BisectInterval.mk (lo a) (hi a))
    (step := fun a iv => OracleComp.interpret ProbOracleComp.query (bisectStepProgram req a iv))
    (binary_size.comp (binary_sub' hhi hlo)) (encBisectInterval_mk_polyTime hlo hhi)
    (isOraclePPTOn_bisectStepProgram hreq)
    (fun a _ iv => iv.lo ≤ max (lo a) (hi a) ∧ iv.hi ≤ max (lo a) (hi a))
    (fun a => ⟨le_max_left _ _, le_max_right _ _⟩)
    (fun a _ iv _ ⟨h1, h2⟩ next hnext => by
      unfold bisectStepProgram at hnext; split_ifs at hnext with hlt
      · rw [OracleComp.interpret_map] at hnext
        obtain ⟨b, -, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hnext
        cases b <;> simp only [↓reduceIte, Bool.false_eq_true] <;> exact ⟨by omega, by omega⟩
      · simp only [OracleComp.interpret_pure] at hnext
        exact (by simpa [OracleComp.support] using hnext : next = iv) ▸ ⟨h1, h2⟩)
    hsize
    (fun a _ iv _ ⟨h1, h2⟩ => by
      have hcap : (encNat (max (lo a) (hi a))).length ≤
          cL * ((encA a).length + 1) ^ dL + cH * ((encA a).length + 1) ^ dH := by
        rcases max_choice (lo a) (hi a) with heq | heq <;> rw [heq]
        · exact (hlenL a).trans (Nat.le_add_right _ _)
        · exact (hlenH a).trans (Nat.le_add_left _ _)
      have h1' := (length_encNat_mono h1).trans hcap
      have h2' := (length_encNat_mono h2).trans hcap
      simp only [encBisectInterval_apply, encBisectIntervalFields]; enc_len)
  simpa only [bisectProgram, OracleComp.interpret_map, OracleComp.interpret_iterate] using
    hit.1.map (by fun_prop : ComputableInPolyTime BisectInterval.lo encBisectInterval encNat)

open Classical in
/-- **Polynomial-time oracle bisection with logarithmic query count.** Given polynomial-time
endpoints `lo, hi : α → ℕ` and threshold request builder `req`,
`((bisectStep ...)^[(hi a - lo a).size] ⟨lo a, hi a⟩).lo` is computable in polynomial time
relative to `A` with at most `r |encA a|` requests whenever
`(hi a - lo a).size ≤ r (encA a).length`. -/
theorem computableInPolyTimeWithOracleQueries_bisect {α : Type} {encA : α ↪ List Bool}
    (A : Set (List Bool)) {req : α → ℕ → List Bool} {lo hi : α → ℕ} {r : ℕ → ℕ}
    (hreq : ComputableInPolyTime (fun q : OracleThresholdQuery α => req q.inst q.target)
      (encOracleThresholdQuery encA) encBits)
    (hlo : ComputableInPolyTime lo encA encNat)
    (hhi : ComputableInPolyTime hi encA encNat)
    (hr : ∀ a, (hi a - lo a).size ≤ r (encA a).length) :
    ComputableInPolyTimeWithOracleQueries A r
      (fun a => ((bisectStep (fun m => decide (req a m ∈ A)))^[(hi a - lo a).size]
        ⟨lo a, hi a⟩).lo)
      encA encNat :=
  ⟨bisectProgram req lo hi, isOraclePPTOn_bisectProgram hreq hlo hhi, fun a =>
    ⟨interpret_bisectProgram A req lo hi a,
      (length_queriesWith_bisectProgram_le (languageOracle A) req lo hi a).trans (hr a)⟩⟩

/-! ### Max-SAT threshold optimization and optimal assignment recovery -/

/-- A CNF formula paired with a target number of satisfied clauses. -/
structure MaxSATQuery where
  /-- Formula in conjunctive normal form over natural-number variables. -/
  formula : CNF ℕ
  /-- Target number of satisfied clauses (counted with multiplicity). -/
  target : ℕ
  deriving DecidableEq, Repr

/-- Framed encoding of `MaxSATQuery` (`encCNF` paired with binary `encNat`). -/
enc_structure encMaxSATQuery : MaxSATQuery where
  formula : encCNF, target : encNat

/-- Optimal Max-SAT result: maximum satisfied-clause count paired with a raw assignment bitstring
for `SAT.assignment`. -/
structure MaxSATSolution where
  /-- Maximum number of clauses of `φ` simultaneously satisfiable. -/
  optValue : ℕ
  /-- Bitstring of length `φ.vars.length` read by `SAT.assignment φ`. -/
  assignmentBits : List Bool
  deriving DecidableEq, Repr

/-- Framed encoding of `MaxSATSolution` (binary `encNat` paired with `encBits`). -/
enc_structure encMaxSATSolution : MaxSATSolution where
  optValue : encNat, assignmentBits : encBits

/-- The threshold decision language for unweighted Max-SAT: `q ∈ MaxSATThreshold` iff some
assignment satisfies at least `q.target` clauses of `q.formula`. -/
def MaxSATThreshold : Set MaxSATQuery :=
  {q | ∃ σ : ℕ → Bool, q.target ≤ q.formula.countP (Clause.eval σ)}

theorem mem_MaxSATThreshold_iff {q : MaxSATQuery} :
    q ∈ MaxSATThreshold ↔ ∃ σ : ℕ → Bool, q.target ≤ q.formula.countP (Clause.eval σ) :=
  Iff.rfl

namespace MaxSAT

/-- Polynomial-time NP verifier for `MaxSATThreshold`. -/
def thresholdVerifier (p : MaxSATQuery × List Bool) : Bool :=
  decide (p.1.target ≤ p.1.formula.countP (Clause.eval (SAT.assignment p.1.formula p.2)))

theorem isVerifier_threshold :
    IsVerifier encMaxSATQuery Polynomial.X thresholdVerifier MaxSATThreshold := by
  refine IsVerifier.of_padding (fun q w _ h => ?_) fun q hq => ?_
  · simp only [thresholdVerifier, decide_eq_true_eq] at h
    exact ⟨_, h⟩
  · obtain ⟨σ, hσ⟩ := hq
    have hvars : q.formula.vars.length ≤ (encMaxSATQuery q).length := by
      have h1 := SAT.length_vars_le q.formula
      simp only [encMaxSATQuery_apply, encMaxSATQueryFields]
      exact h1.trans (length_le_encPair_left encCNF encNat (q.formula, q.target))
    refine ⟨q.formula.vars.map σ, by simpa using hvars, fun k => ?_⟩
    simp only [thresholdVerifier, decide_eq_true_eq]
    refine hσ.trans (CNF.countP_eval_congr fun v hv => ?_).le
    exact (SAT.assignment_vars_map_append _ σ _ hv).symm

@[fun_prop]
theorem computableInPolyTime_thresholdVerifier :
    ComputableInPolyTime thresholdVerifier (encPair encMaxSATQuery encBits) encBool := by
  open ComputableInPolyTime in
  have hφ := encMaxSATQuery_formula_polyTime (fst encMaxSATQuery encBits)
  exact binary_le' (encMaxSATQuery_target_polyTime (fst _ _)) (unary_to_binary.comp
    (countPWithInput hφ (SAT.computableInPolyTime_clause.comp
      (((hφ.comp (fst _ _)).prod ((snd _ _).comp (fst _ _))).prod (snd _ _)))))

/-- `MaxSATThreshold` belongs to `NP`. -/
theorem mem_NP_threshold : MaxSATThreshold ∈ NP encMaxSATQuery :=
  ⟨Polynomial.X, thresholdVerifier, computableInPolyTime_thresholdVerifier, isVerifier_threshold⟩

/-- Specification of unweighted Max-SAT as a `MaxThresholdSpec`. -/
def thresholdSpec : MaxThresholdSpec (CNF ℕ) (ℕ → Bool) where
  valid _ _ := True
  score φ σ := φ.countP (Clause.eval σ)
  bound φ := φ.length
  score_le_bound _ _ _ := List.countP_le_length

open Classical in
/-- The exact maximum number of simultaneously satisfiable clauses of `φ`. -/
noncomputable def maxClauseScore (φ : CNF ℕ) : ℕ :=
  lowerBound (fun q => decide (MaxSATQuery.mk φ q ∈ MaxSATThreshold)) 1 (φ.length + 1) - 1

private theorem maxSATThreshold_mono (φ : CNF ℕ) {m m' : ℕ} (hmm' : m ≤ m')
    [Decidable (MaxSATQuery.mk φ m' ∈ MaxSATThreshold)]
    [Decidable (MaxSATQuery.mk φ m ∈ MaxSATThreshold)]
    (ht : decide (MaxSATQuery.mk φ m' ∈ MaxSATThreshold) = true) :
    decide (MaxSATQuery.mk φ m ∈ MaxSATThreshold) = true := by
  simp only [decide_eq_true_eq, mem_MaxSATThreshold_iff] at ht ⊢
  obtain ⟨σ, hσ⟩ := ht; exact ⟨σ, hmm'.trans hσ⟩

/-- `maxClauseScore φ` is attained by some assignment and upper-bounds every assignment's score. -/
theorem maxClauseScore_spec (φ : CNF ℕ) :
    maxClauseScore φ ≤ φ.length ∧
      (∃ σ : ℕ → Bool, φ.countP (Clause.eval σ) = maxClauseScore φ) ∧
      ∀ σ : ℕ → Bool, φ.countP (Clause.eval σ) ≤ maxClauseScore φ := by
  classical
  set t : ℕ → Bool := fun q => decide (MaxSATQuery.mk φ q ∈ MaxSATThreshold)
  obtain ⟨hlo, hhi, htrue, hfalse⟩ := lowerBound_spec t (lo := 1) (hi := φ.length + 1)
    fun _ _ _ hmm' _ ht => maxSATThreshold_mono φ hmm' ht
  set k := lowerBound t 1 (φ.length + 1)
  have hupper (σ : ℕ → Bool) : φ.countP (Clause.eval σ) ≤ k - 1 := by
    by_contra! hgt
    have := List.countP_le_length (l := φ) (p := Clause.eval σ)
    have hf := hfalse k le_rfl (by omega)
    simp only [t, decide_eq_false_iff_not, mem_MaxSATThreshold_iff] at hf
    exact hf ⟨σ, by omega⟩
  obtain ⟨σ, hσ⟩ : ∃ σ : ℕ → Bool, k - 1 ≤ φ.countP (Clause.eval σ) := by
    rcases Nat.eq_or_lt_of_le hlo with hk1 | hgt1
    · exact ⟨fun _ => false, by omega⟩
    · simpa only [t, decide_eq_true_eq, mem_MaxSATThreshold_iff] using
        htrue (k - 1) (by omega) (by omega)
  exact ⟨by change k - 1 ≤ φ.length; omega, ⟨σ, le_antisymm (hupper σ) hσ⟩, hupper⟩

/-- Every declared-range assignment score is below `maxClauseScore φ`, for any declared variable
count `n`. -/
theorem optimum_le_maxClauseScore (n : ℕ) (φ : CNF ℕ) : optimum (n, φ) ≤ maxClauseScore φ := by
  obtain ⟨x, hx⟩ := exists_score_eq_optimum (n, φ)
  rw [← hx]
  exact (maxClauseScore_spec φ).2.2 (assignment n x)

/-- When every variable of `φ` is below `n`, the binary-search value `maxClauseScore φ` over
`ℕ → Bool` equals the declared-variable optimum `MaxSAT.optimum (n, φ)` over `BitString n` from
`FineGrained.MaxSAT.Histogram`. Without the hypothesis, undeclared variables read `false` in
`MaxSAT.score`, so the inequality `optimum_le_maxClauseScore` can be strict. -/
theorem maxClauseScore_eq_optimum {n : ℕ} {φ : CNF ℕ} (hφ : ∀ v ∈ φ.vars, v < n) :
    maxClauseScore φ = optimum (n, φ) := by
  refine le_antisymm ?_ (optimum_le_maxClauseScore n φ)
  obtain ⟨-, ⟨σ, hσ⟩, -⟩ := maxClauseScore_spec φ
  rw [← hσ]
  refine le_of_eq_of_le ?_ (score_le_optimum (n, φ) fun i => σ i)
  exact CNF.countP_eval_congr fun v hv => by simp [assignment, hφ v hv]

/-! ### Variable-by-variable witness recovery under partial assignments -/

/-- Number of clauses of `φ` already satisfied by at least one fixed literal in `answers`. -/
def satisfiedBy (answers : List (Literal ℕ)) (φ : CNF ℕ) : ℕ :=
  φ.countP fun c => c.any fun l => answers.any (· == l)

/-- Residual CNF after dropping clauses satisfied by `answers` and removing falsified literals. -/
def applyPartial (answers : List (Literal ℕ)) (φ : CNF ℕ) : CNF ℕ :=
  (φ.filter fun c => !c.any fun l => answers.any (· == l)).map fun c =>
    c.filter fun l => !answers.any (· == (l.1, !l.2))

/-- Lookup the Boolean assigned to `v` in `answers` (defaulting to `false`). -/
def lookupVar (answers : List (Literal ℕ)) (v : ℕ) : Bool :=
  match answers.find? (fun l => l.1 == v) with
  | some l => l.2
  | none => false

private theorem lookupVar_eq_of_mem {answers : List (Literal ℕ)}
    (hnodup : (answers.map Prod.fst).Nodup) {v : ℕ} {b : Bool} (hmem : (v, b) ∈ answers) :
    lookupVar answers v = b := by
  induction answers with
  | nil => simp at hmem
  | cons hd tl ih =>
    rw [List.map_cons, List.nodup_cons] at hnodup
    unfold lookupVar at ih ⊢
    rcases List.mem_cons.mp hmem with rfl | htl
    · simp
    · have hne : hd.1 ≠ v := fun h => hnodup.1 (h ▸ List.mem_map_of_mem (f := Prod.fst) htl)
      rw [List.find?_cons_of_neg (by simp [hne])]
      exact ih hnodup.2 htl

private theorem countP_eval_eq_satisfiedBy_add_applyPartial {answers : List (Literal ℕ)}
    {σ : ℕ → Bool} (hagree : ∀ l ∈ answers, σ l.1 = l.2) (φ : CNF ℕ) :
    φ.countP (Clause.eval σ) =
      satisfiedBy answers φ + (applyPartial answers φ).countP (Clause.eval σ) := by
  induction φ with
  | nil => rfl
  | cons c cs ih =>
    simp only [satisfiedBy, applyPartial] at ih ⊢
    by_cases hsat : (c.any fun l => answers.any (· == l)) = true
    · obtain ⟨l, hlc, hla⟩ := List.any_eq_true.mp hsat
      obtain ⟨l', hl'a, heq⟩ := List.any_eq_true.mp hla
      obtain rfl : l' = l := beq_iff_eq.mp heq
      have heval_c : Clause.eval σ c = true := (Clause.eval_eq_true_iff σ c).mpr
        ⟨l', hlc, by have := hagree l' hl'a; rcases l' with ⟨_, false | true⟩ <;> simp_all⟩
      rw [List.filter_cons_of_neg
        (p := fun c : Clause ℕ => !c.any fun l => answers.any (· == l)) (by simp [hsat])]
      simp only [List.countP_cons, heval_c, hsat, ↓reduceIte]
      omega
    · have hsatF : (c.any fun l => answers.any (· == l)) = false := Bool.eq_false_iff.mpr hsat
      have heval_eq :
          Clause.eval σ (c.filter fun l => !answers.any (· == (l.1, !l.2))) = Clause.eval σ c := by
        refine Bool.eq_iff_iff.mpr ?_
        simp only [Clause.eval_eq_true_iff, List.mem_filter, Bool.not_eq_true', List.any_eq_false]
        refine ⟨fun ⟨l, ⟨hlc, _⟩, hl⟩ => ⟨l, hlc, hl⟩, fun ⟨l, hlc, hl⟩ => ?_⟩
        refine ⟨l, ⟨hlc, fun l' hl'a hcontra => ?_⟩, hl⟩
        obtain rfl : l' = (l.1, !l.2) := beq_iff_eq.mp hcontra
        have := hagree (l.1, !l.2) hl'a; cases l.2 <;> simp [this] at hl
      rw [List.filter_cons_of_pos
        (p := fun c : Clause ℕ => !c.any fun l => answers.any (· == l)) (by simp [hsatF]),
        List.map_cons]
      simp only [List.countP_cons, hsatF, Bool.false_eq_true, ↓reduceIte, heval_eq]
      omega

private theorem not_mem_vars_applyPartial {answers : List (Literal ℕ)} {φ : CNF ℕ} {v : ℕ}
    (hv : v ∈ answers.map Prod.fst) : v ∉ (applyPartial answers φ).vars := by
  obtain ⟨⟨v', b⟩, hmem, rfl⟩ := List.mem_map.mp hv
  intro hcontra
  obtain ⟨_, hc', b', hb'⟩ := CNF.mem_vars.mp hcontra
  simp only [applyPartial, List.mem_map, List.mem_filter, Bool.not_eq_true',
    List.any_eq_false] at hc'
  obtain ⟨c, ⟨_, hnot_sat⟩, rfl⟩ := hc'
  simp only [List.mem_filter, Bool.not_eq_true', List.any_eq_false] at hb'
  rcases eq_or_ne b b' with rfl | hne
  · exact hnot_sat (v', b) hb'.1 (List.any_eq_true.mpr ⟨(v', b), hmem, beq_iff_eq.mpr rfl⟩)
  · refine hb'.2 (v', !b') ?_ (beq_iff_eq.mpr rfl)
    cases b <;> cases b' <;> simp_all

/-- Querying `MaxSATThreshold` on `(applyPartial answers φ, target - satisfiedBy answers φ)`
characterizes whether `answers` extends to a full assignment satisfying at least `target`
clauses of `φ`. -/
theorem mem_MaxSATThreshold_applyPartial_iff {answers : List (Literal ℕ)}
    (hnodup : (answers.map Prod.fst).Nodup) (φ : CNF ℕ) (target : ℕ) :
    MaxSATQuery.mk (applyPartial answers φ) (target - satisfiedBy answers φ) ∈ MaxSATThreshold ↔
      ∃ σ : ℕ → Bool, (∀ l ∈ answers, σ l.1 = l.2) ∧ target ≤ φ.countP (Clause.eval σ) := by
  refine ⟨fun ⟨τ, hτ⟩ => ?_, fun ⟨σ, hagree, hσ⟩ => ⟨σ, ?_⟩⟩
  · let σ : ℕ → Bool := fun u => if u ∈ answers.map Prod.fst then lookupVar answers u else τ u
    have hagree : ∀ l ∈ answers, σ l.1 = l.2 := fun ⟨u, b⟩ hm => by
      simp only [σ, List.mem_map_of_mem (f := Prod.fst) hm, ↓reduceIte,
        lookupVar_eq_of_mem hnodup hm]
    have hcongr : (applyPartial answers φ).countP (Clause.eval σ) =
        (applyPartial answers φ).countP (Clause.eval τ) :=
      CNF.countP_eval_congr fun u hu =>
        ite_eq_right_iff.mpr fun hm => absurd hm (fun h => not_mem_vars_applyPartial h hu)
    exact ⟨σ, hagree, by
      dsimp only at hτ; rw [countP_eval_eq_satisfiedBy_add_applyPartial hagree φ, hcongr]; omega⟩
  · dsimp only; rw [countP_eval_eq_satisfiedBy_add_applyPartial hagree φ] at hσ; omega

/-- Encoded length of `applyPartial answers φ` never exceeds that of `φ`. -/
theorem length_encCNF_applyPartial_le (answers : List (Literal ℕ)) (φ : CNF ℕ) :
    (encCNF (applyPartial answers φ)).length ≤ (encCNF φ).length :=
  (length_encList_map_le _ _ fun _ _ => length_encList_sublist _ List.filter_sublist).trans
    (length_encList_sublist _ List.filter_sublist)

/-- Query tested at one step of `MaxSAT` witness recovery. -/
def recoverQuery (q : MaxSATQuery) (answers : List (Literal ℕ)) : MaxSATQuery :=
  let v := q.formula.distinctVars.getD answers.length 0
  let cand := answers ++ [(v, true)]
  ⟨applyPartial cand q.formula, q.target - satisfiedBy cand q.formula⟩

theorem length_encMaxSATQuery_recoverQuery_le (q : MaxSATQuery) (answers : List (Literal ℕ)) :
    (encMaxSATQuery (recoverQuery q answers)).length ≤ (encMaxSATQuery q).length := by
  simp only [recoverQuery, encMaxSATQuery_apply, encMaxSATQueryFields]
  have h1 := length_encCNF_applyPartial_le
    (answers ++ [(q.formula.distinctVars.getD answers.length 0, true)]) q.formula
  have h2 := length_encNat_mono (Nat.sub_le q.target
    (satisfiedBy (answers ++ [(q.formula.distinctVars.getD answers.length 0, true)]) q.formula))
  enc_len

/-- Pure step of `MaxSAT` witness recovery over `q.formula.distinctVars`. -/
def recoverStep (D : MaxSATQuery → Bool) (q : MaxSATQuery) (answers : List (Literal ℕ)) :
    List (Literal ℕ) :=
  if answers.length < q.formula.distinctVars.length then
    let v := q.formula.distinctVars.getD answers.length 0
    answers ++ [(v, D (recoverQuery q answers))]
  else answers

/-- Adaptive oracle step of `MaxSAT` witness recovery. -/
def recoverStepProgram (q : MaxSATQuery) (answers : List (Literal ℕ)) :
    WordQueryComp Unit (List (Literal ℕ)) :=
  if answers.length < q.formula.distinctVars.length then
    let v := q.formula.distinctVars.getD answers.length 0
    (fun b => answers ++ [(v, b)]) <$> queryBit (encMaxSATQuery (recoverQuery q answers))
  else pure answers

/-- Adaptive oracle program recovering an assignment for `q : MaxSATQuery` in `q.formula.numVars`
queries. -/
def recoverProgram (q : MaxSATQuery) : WordQueryComp Unit (List Bool) :=
  (fun answers => q.formula.vars.map (lookupVar answers)) <$>
    OracleComp.iterate q.formula.numVars (recoverStepProgram q) []

open Classical in
/-- Pure witness-recovery function matching `recoverProgram` against `MaxSATThreshold`. -/
noncomputable def recoverBits (D : MaxSATQuery → Bool) (q : MaxSATQuery) : List Bool :=
  q.formula.vars.map
    (lookupVar ((recoverStep D q)^[q.formula.numVars] []))

open Classical in
theorem interpret_recoverProgram (A : Set (List Bool)) (q : MaxSATQuery) :
    OracleComp.interpret (m := Id) (languageOracle A) (recoverProgram q) =
      recoverBits (fun r => decide (encMaxSATQuery r ∈ A)) q := by
  rw [recoverProgram, OracleComp.interpret_map, OracleComp.interpret_id_iterate, recoverBits]
  have hfun : (fun answers => OracleComp.interpret (m := Id) (languageOracle A)
      (recoverStepProgram q answers)) =
      recoverStep (fun r => decide (encMaxSATQuery r ∈ A)) q := by
    funext answers
    unfold recoverStepProgram recoverStep
    split_ifs
    · rw [OracleComp.interpret_map, interpret_queryBit]
      rfl
    · rfl
  exact congrArg (fun f => q.formula.vars.map (lookupVar (f^[q.formula.numVars] []))) hfun

theorem length_queriesWith_recoverProgram_le
    (answer : Unit × List Bool → List Bool) (q : MaxSATQuery) :
    (OracleComp.queriesWith answer (recoverProgram q)).length ≤ CNF.numVars q.formula := by
  rw [recoverProgram, OracleComp.queriesWith_map]
  have hstep : ∀ ans, (OracleComp.queriesWith answer (recoverStepProgram q ans)).length ≤ 1 := by
    intro ans
    unfold recoverStepProgram
    split_ifs <;> simp
  simpa using OracleComp.length_queriesWith_iterate_le answer hstep (CNF.numVars q.formula) []

theorem mem_queriesWith_recoverProgram_length_le
    (answer : Unit × List Bool → List Bool) (q : MaxSATQuery) {req : Unit × List Bool}
    (hreq : req ∈ OracleComp.queriesWith answer (recoverProgram q)) :
    req.2.length ≤ (encMaxSATQuery q).length := by
  rw [recoverProgram, OracleComp.queriesWith_map] at hreq
  obtain ⟨ans, -, hstep⟩ := Cslib.OracleComp.mem_queriesWith_iterate answer
    (inv := fun _ => True) trivial (fun _ _ => trivial) hreq
  unfold recoverStepProgram at hstep
  split_ifs at hstep
  · simp only [queryBit, OracleComp.queriesWith_map, OracleComp.queriesWith_query,
      List.mem_singleton] at hstep
    subst hstep
    exact length_encMaxSATQuery_recoverQuery_le q ans
  · simp at hstep

private theorem recover_append_map_fst {ans : List (Literal ℕ)} {φ : CNF ℕ} {i : ℕ}
    (hlt : i < φ.distinctVars.length) (hinv : ans.map Prod.fst = φ.distinctVars.take i)
    (b : Bool) :
    (ans ++ [(φ.distinctVars.getD ans.length 0, b)]).map Prod.fst =
      φ.distinctVars.take (i + 1) := by
  have hlen : ans.length = i := by
    have := congrArg List.length hinv
    rw [List.length_map, List.length_take] at this; omega
  rw [List.map_append, hinv, List.map_singleton, List.take_add_one, hlen,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some,
    Option.toList_some]

/-- If `q ∈ MaxSATThreshold` and `D` decides `MaxSATThreshold` on queries no longer than `q`,
`recoverBits D q` yields an assignment satisfying at least `q.target` clauses of `q.formula`. -/
theorem target_le_countP_recoverBits {D : MaxSATQuery → Bool} {q : MaxSATQuery}
    (hD : ∀ r, (encMaxSATQuery r).length ≤ (encMaxSATQuery q).length →
      (D r = true ↔ r ∈ MaxSATThreshold))
    (hq : q ∈ MaxSATThreshold) :
    q.target ≤ q.formula.countP (Clause.eval (SAT.assignment q.formula (recoverBits D q))) := by
  have hnodup_dv : q.formula.distinctVars.Nodup := CNF.nodup_distinctVars q.formula
  have hloop : ∀ i, i ≤ q.formula.distinctVars.length →
      let ans := (recoverStep D q)^[i] []
      ans.map Prod.fst = q.formula.distinctVars.take i ∧
        ∃ σ : ℕ → Bool, (∀ l ∈ ans, σ l.1 = l.2) ∧
          q.target ≤ q.formula.countP (Clause.eval σ) := fun i hi => by
    induction i with
    | zero => obtain ⟨σ, hσ⟩ := hq; exact ⟨rfl, σ, fun _ h => by simp at h, hσ⟩
    | succ i ih =>
      obtain ⟨hfst, σ, hagree, hσ⟩ := ih (by omega)
      set ans := (recoverStep D q)^[i] []
      have hlen : ans.length = i := by
        have := congrArg List.length hfst; rw [List.length_map, List.length_take] at this; omega
      have hlt : i < q.formula.distinctVars.length := by omega
      have hlt_a : ans.length < q.formula.distinctVars.length := by omega
      rw [Function.iterate_succ_apply', recoverStep, ite_eq_left hlt_a]
      have hstep := fun b => recover_append_map_fst hlt hfst b
      have hnodup_cand : ((ans ++ [(q.formula.distinctVars.getD ans.length 0, true)]).map
          Prod.fst).Nodup := hstep true ▸ hnodup_dv.take
      have hqlen := length_encMaxSATQuery_recoverQuery_le q ans
      refine ⟨hstep _, ?_⟩
      cases hb : D (recoverQuery q ans)
      · have hnot : recoverQuery q ans ∉ MaxSATThreshold :=
          fun hm => Bool.noConfusion (hb.symm.trans ((hD _ hqlen).mpr hm))
        rw [recoverQuery, mem_MaxSATThreshold_applyPartial_iff hnodup_cand] at hnot
        have hagree_ext : ∀ b, σ (q.formula.distinctVars.getD ans.length 0) = b →
            ∀ l ∈ ans ++ [(q.formula.distinctVars.getD ans.length 0, b)], σ l.1 = l.2 :=
          fun b hbv l hl => (List.mem_append.mp hl).elim (hagree l) fun hm => by
            obtain rfl := List.mem_singleton.mp hm; exact hbv
        have hσv : σ (q.formula.distinctVars.getD ans.length 0) = false :=
          Bool.eq_false_iff.mpr fun ht => hnot ⟨σ, hagree_ext true ht, hσ⟩
        exact ⟨σ, hagree_ext false hσv, hσ⟩
      · exact (mem_MaxSATThreshold_applyPartial_iff hnodup_cand _ _).mp ((hD _ hqlen).mp hb)
  have hnv : q.formula.numVars = q.formula.distinctVars.length :=
    (CNF.length_distinctVars q.formula).symm
  obtain ⟨hfst, σ, hagree, hσ⟩ := hloop q.formula.numVars (by omega)
  rw [hnv, List.take_length, ← hnv] at hfst
  set ans := (recoverStep D q)^[q.formula.numVars] []
  have hcongr : q.formula.countP (Clause.eval (SAT.assignment q.formula (recoverBits D q))) =
      q.formula.countP (Clause.eval σ) := CNF.countP_eval_congr fun v hv => by
    have hbits : SAT.assignment q.formula (recoverBits D q) v = lookupVar ans v :=
      SAT.assignment_vars_map _ _ hv
    rw [hbits]
    obtain ⟨⟨v', b⟩, hmem, rfl⟩ := List.mem_map.mp (hfst ▸ CNF.mem_distinctVars.mpr hv)
    exact (lookupVar_eq_of_mem (hfst ▸ hnodup_dv) hmem).trans (hagree (v', b) hmem).symm
  exact hcongr ▸ hσ

open ComputableInPolyTime in
private theorem computableInPolyTime_nextRecoverVar :
    ComputableInPolyTime
      (fun p : MaxSATQuery × List (Literal ℕ) => p.1.formula.distinctVars.getD p.2.length 0)
      (encPair encMaxSATQuery (encList (encPair encNat encBool))) encNat :=
  listGetDWithInput
    (SAT.computableInPolyTime_distinctVars.comp (encMaxSATQuery_formula_polyTime (fst _ _)))
    ((length_list _).comp (snd _ _)) 0

open ComputableInPolyTime in
private theorem computableInPolyTime_recoverQuery :
    ComputableInPolyTime (fun p : MaxSATQuery × List (Literal ℕ) => recoverQuery p.1 p.2)
      (encPair encMaxSATQuery (encList (encPair encNat encBool))) encMaxSATQuery := by
  let ELit := encPair encNat encBool
  let E := encPair encMaxSATQuery (encList ELit)
  have hφ : ComputableInPolyTime (fun p : MaxSATQuery × List (Literal ℕ) => p.1.formula)
      E (encList (encList ELit)) :=
    encMaxSATQuery_formula_polyTime (fst _ _)
  have hcand : ComputableInPolyTime (fun p : MaxSATQuery × List (Literal ℕ) =>
      p.2 ++ [(p.1.formula.distinctVars.getD p.2.length 0, true)]) E (encList ELit) :=
    listAppend' (snd _ _) (cons' (computableInPolyTime_nextRecoverVar.prod (const true)) (const []))
  have hlitEq : ComputableInPolyTime (fun x : Literal ℕ × Literal ℕ => x.1 == x.2)
      (encPair ELit ELit) encBool :=
    (bool_and' (decide_eq' (encB := encNat) (fst ELit ELit).fst' (snd ELit ELit).fst')
      (decide_eq' (encB := encBool) (fst ELit ELit).snd' (snd ELit ELit).snd')).of_enc_eq
      fun ⟨⟨_, _⟩, ⟨_, _⟩⟩ => congrArg encBool (Bool.eq_iff_iff.mpr (by simp))
  have hclauseSat : ComputableInPolyTime
      (fun x : List (Literal ℕ) × Clause ℕ => x.2.any fun l => x.1.any (· == l))
      (encPair (encList ELit) (encList ELit)) encBool :=
    anyWithInput (snd _ _) (anyWithInput ((fst _ _).comp (fst _ _))
      (hlitEq.comp ((snd _ _).prod ((snd _ _).comp (fst _ _)))))
  have hf1 := filterWithInput
    (test := fun (p : MaxSATQuery × List (Literal ℕ)) (c : Clause ℕ) =>
      !c.any fun l =>
        (p.2 ++ [(p.1.formula.distinctVars.getD p.2.length 0, true)]).any (· == l))
    hφ (bool_not.comp (hclauseSat.comp ((hcand.comp (fst _ _)).prod (snd _ _))))
  have hnegLit : ComputableInPolyTime (fun y : ((MaxSATQuery × List (Literal ℕ)) × Clause ℕ) ×
      Literal ℕ => (y.2.1, !y.2.2)) (encPair (encPair E (encList ELit)) ELit) ELit :=
    (snd _ _).fst'.prod (bool_not.comp (snd _ _).snd')
  have hkeepLit := bool_not.comp (anyWithInput
    (test := fun (y : ((MaxSATQuery × List (Literal ℕ)) × Clause ℕ) × Literal ℕ)
      (m : Literal ℕ) => m == (y.2.1, !y.2.2))
    ((hcand.comp (fst _ _)).comp (fst _ _)) (hlitEq.comp ((snd _ _).prod (hnegLit.comp (fst _ _)))))
  have hap : ComputableInPolyTime (fun p : MaxSATQuery × List (Literal ℕ) =>
      applyPartial (p.2 ++ [(p.1.formula.distinctVars.getD p.2.length 0, true)]) p.1.formula)
      E (encList (encList ELit)) :=
    mapWithInput hf1 (filterWithInput (snd _ _) hkeepLit)
  exact encMaxSATQuery_mk_polyTime hap
    (binary_sub' (encMaxSATQuery_target_polyTime (fst _ _))
      (unary_to_binary.comp (countPWith hclauseSat hcand hφ)))

open ComputableInPolyTime in
private theorem isOraclePPTOn_recoverStepProgram :
    IsOraclePPTOn (encPair encMaxSATQuery (encList (encPair encNat encBool)))
      (encList (encPair encNat encBool))
      (fun pair => OracleComp.interpret ProbOracleComp.query
        (recoverStepProgram pair.1 pair.2)) := by
  let EL := encList (encPair encNat encBool)
  have hcond : ComputableInPolyTime
      (fun p : MaxSATQuery × List (Literal ℕ) =>
        decide (p.2.length < p.1.formula.distinctVars.length))
      (encPair encMaxSATQuery EL) encBool :=
    unary_lt.comp (((length_list _).comp (snd _ _)).prod ((length_list _).comp
      (SAT.computableInPolyTime_distinctVars.comp (encMaxSATQuery_formula_polyTime (fst _ _)))))
  have hpost : ComputableInPolyTime
      (fun p : (MaxSATQuery × List (Literal ℕ)) × Bool =>
        p.1.2 ++ [(p.1.1.formula.distinctVars.getD p.1.2.length 0, p.2)])
      (encPair (encPair encMaxSATQuery EL) encBool) EL :=
    listAppend' ((snd _ _).comp (fst _ _))
      (cons' ((computableInPolyTime_nextRecoverVar.comp (fst _ _)).prod (snd _ _)) (const []))
  refine (IsOraclePPTOn.ite (condition := fun p : MaxSATQuery × List (Literal ℕ) =>
      p.2.length < p.1.formula.distinctVars.length) hcond
    ((isOraclePPTOn_queryBit computableInPolyTime_recoverQuery.encoding_comp).map_with
      (f := fun p b => p.2 ++ [(p.1.formula.distinctVars.getD p.2.length 0, b)]) hpost)
    (snd encMaxSATQuery EL).isOraclePPTOn).congr fun p State oracle s => ?_
  unfold recoverStepProgram; split_ifs <;>
    simp only [OracleComp.interpret_map, OracleComp.interpret_pure]

open ComputableInPolyTime in
/-- `recoverProgram` is strict oracle PPT on `encMaxSATQuery`. -/
theorem isOraclePPTOn_recoverProgram :
    IsOraclePPTOn encMaxSATQuery encBits
      (fun q => OracleComp.interpret ProbOracleComp.query (recoverProgram q)) := by
  let EL := encList (encPair encNat encBool)
  have hsize : PolyBounded (fun q : MaxSATQuery => (encMaxSATQuery q).length)
      (fun q => (encMaxSATQuery q).length * (4 * (encMaxSATQuery q).length + 5)) := by growth_poly
  have hit := IsOraclePPTOn.iterateWith_spec (input := encMaxSATQuery) (stateEncoding := EL)
    (count := fun q => CNF.numVars q.formula) (initial := fun _ => [])
    (step := fun q ans => OracleComp.interpret ProbOracleComp.query (recoverStepProgram q ans))
    (SAT.computableInPolyTime_numVars.comp (encMaxSATQuery_formula_polyTime id'))
    (const []) isOraclePPTOn_recoverStepProgram
    (fun q i ans => ans.map Prod.fst = q.formula.distinctVars.take i) (fun _ => rfl)
    (fun q i ans hi hinv next hnext => by
      have hnv := (CNF.length_distinctVars q.formula).symm
      have hlen : ans.length = i := by
        have := congrArg List.length hinv; rw [List.length_map, List.length_take] at this; omega
      unfold recoverStepProgram at hnext
      rw [ite_eq_left (by omega), OracleComp.interpret_map] at hnext
      obtain ⟨b, -, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hnext
      exact recover_append_map_fst (by omega) hinv b)
    hsize
    (fun q i ans hi hinv => by
      have hnv := (CNF.length_distinctVars q.formula).symm
      have hlen : ans.length ≤ CNF.numVars q.formula := by
        have := congrArg List.length hinv; rw [List.length_map, List.length_take] at this; omega
      have hcnf_le : (encCNF q.formula).length ≤ (encMaxSATQuery q).length :=
        length_le_encPair_left encCNF encNat (q.formula, q.target)
      have hnv_le : CNF.numVars q.formula ≤ (encMaxSATQuery q).length :=
        ((CNF.numVars_le_length_vars q.formula).trans (SAT.length_vars_le q.formula)).trans hcnf_le
      have hmem : ∀ l ∈ ans, l.1 ∈ q.formula.vars := fun l hl =>
        CNF.mem_distinctVars.mp (List.mem_of_mem_take (hinv ▸ List.mem_map_of_mem hl))
      exact (SAT.length_encList_le_of_mem_vars hmem).trans
        (Nat.mul_le_mul (hlen.trans hnv_le) (by omega)))
  have heq_var : ComputableInPolyTime
      (fun p : ((MaxSATQuery × List (Literal ℕ)) × ℕ) × Literal ℕ => p.2.1 == p.1.2)
      (encPair (encPair (encPair encMaxSATQuery EL) encNat) (encPair encNat encBool)) encBool :=
    (decide_eq' (encB := encNat) ((fst encNat encBool).comp (snd _ _))
      ((snd (encPair encMaxSATQuery EL) encNat).comp (fst _ _))).of_enc_eq fun ⟨⟨_, _⟩, ⟨_, _⟩⟩ =>
      congrArg encBool (Bool.eq_iff_iff.mpr (by simp))
  have hget : ComputableInPolyTime
      (fun o : Option (Literal ℕ) => match o with | some l => l.2 | none => false)
      (encOption (encPair encNat encBool)) encBool :=
    (ite' (by fun_prop : ComputableInPolyTime Option.isSome
        (encOption (encPair encNat encBool)) encBool)
      (by fun_prop : ComputableInPolyTime (fun o : Option (Literal ℕ) => (o.getD (0, false)).2)
        (encOption (encPair encNat encBool)) encBool)
      (const false)).of_enc_eq fun o => by cases o <;> rfl
  have hlookup := hget.comp (findWithInput
    (test := fun (x : (MaxSATQuery × List (Literal ℕ)) × ℕ) (l : Literal ℕ) => l.1 == x.2)
    (list := fun x : (MaxSATQuery × List (Literal ℕ)) × ℕ => x.1.2)
    ((snd encMaxSATQuery (encList (encPair encNat encBool))).comp (fst _ _)) heq_var)
  have hpost : ComputableInPolyTime
      (fun p : MaxSATQuery × List (Literal ℕ) => p.1.formula.vars.map (lookupVar p.2))
      (encPair encMaxSATQuery EL) encBits :=
    listToBits.comp (mapWithInput
      (SAT.computableInPolyTime_vars.comp (encMaxSATQuery_formula_polyTime (fst _ _))) hlookup)
  simpa only [recoverProgram, OracleComp.interpret_map, OracleComp.interpret_iterate] using
    hit.1.map_with (f := fun q ans => q.formula.vars.map (lookupVar ans)) hpost

/-- Combined adaptive oracle program solving Max-SAT optimization and optimal witness recovery:
bisect on `[1, φ.length + 1)`, subtract `1` for `optValue`, and run
`recoverProgram ⟨φ, optValue⟩`. -/
def solveMaxSATProgram (φ : CNF ℕ) : WordQueryComp Unit MaxSATSolution := do
  let k ← bisectProgram (fun ψ m => encMaxSATQuery ⟨ψ, m⟩) (fun _ => 1) (fun ψ => ψ.length + 1) φ
  let opt := k - 1
  let bits ← recoverProgram ⟨φ, opt⟩
  return ⟨opt, bits⟩

open Classical in
/-- Pure function computed by `solveMaxSATProgram` against an oracle language `A`. -/
noncomputable def solveMaxSAT (A : Set (List Bool)) (φ : CNF ℕ) : MaxSATSolution :=
  OracleComp.interpret (m := Id) (languageOracle A) (solveMaxSATProgram φ)

/-- `solveMaxSATProgram φ` makes at most `φ.length.size + φ.numVars` queries (hence at most
`(Nat.log 2 φ.length + 1) + φ.numVars`), and every queried word has encoded length at most
`(encMaxSATQuery ⟨φ, φ.length⟩).length`. -/
theorem solveMaxSATProgram_query_bounds (answer : Unit × List Bool → List Bool) (φ : CNF ℕ) :
    (OracleComp.queriesWith answer (solveMaxSATProgram φ)).length ≤
      φ.length.size + CNF.numVars φ ∧
    ∀ req ∈ OracleComp.queriesWith answer (solveMaxSATProgram φ),
      req.2.length ≤ (encMaxSATQuery ⟨φ, φ.length⟩).length := by
  unfold solveMaxSATProgram
  rw [OracleComp.queriesWith_bind]
  set k : ℕ := OracleComp.interpret (m := Id) answer
    (bisectProgram (fun ψ m => encMaxSATQuery ⟨ψ, m⟩) (fun _ => 1) (fun ψ => ψ.length + 1) φ)
  have hk_bound : k ≤ φ.length + 1 := by
    suffices ∀ s (iv : BisectInterval), iv.lo ≤ φ.length + 1 → iv.hi ≤ φ.length + 1 →
        ((fun st => OracleComp.interpret (m := Id) answer
          (bisectStepProgram (fun ψ m => encMaxSATQuery ⟨ψ, m⟩) φ st))^[s] iv).lo ≤
          φ.length + 1 by
      simp only [k, bisectProgram, OracleComp.interpret_map, OracleComp.interpret_id_iterate]
      exact this _ _ (Nat.le_add_left 1 φ.length) le_rfl
    intro s
    induction s with
    | zero => exact fun _ h1 _ => h1
    | succ s ih =>
      intro iv h1 h2
      rw [Function.iterate_succ_apply]
      unfold bisectStepProgram
      split_ifs with hlt
      · rw [OracleComp.interpret_map]
        cases (OracleComp.interpret (m := Id) answer _ : Bool)
        · refine ih _ h1 ?_
          dsimp only [Functor.map]
          simp only [Bool.false_eq_true, ↓reduceIte]; omega
        · refine ih _ ?_ h2
          dsimp only [Functor.map]
          simp only [↓reduceIte]; omega
      · exact ih iv h1 h2
  refine ⟨?_, fun req hreq => ?_⟩
  · have h1 := length_queriesWith_bisectProgram_le answer
      (fun ψ m => encMaxSATQuery ⟨ψ, m⟩) (fun _ => 1) (fun ψ => ψ.length + 1) φ
    simp only [Nat.add_sub_cancel] at h1
    rw [List.length_append, OracleComp.queriesWith_bind, OracleComp.queriesWith_pure,
      List.append_nil]
    exact Nat.add_le_add h1 (length_queriesWith_recoverProgram_le answer ⟨φ, k - 1⟩)
  · rcases List.mem_append.mp hreq with h1 | h2
    · obtain ⟨m, _, hm_lt, rfl⟩ := mem_queriesWith_bisectProgram answer
        (fun ψ m => encMaxSATQuery ⟨ψ, m⟩) (fun _ => 1) (fun ψ => ψ.length + 1) φ h1
      have hm_le := length_encNat_mono (show m ≤ φ.length by omega)
      simp only [encMaxSATQuery_apply, encMaxSATQueryFields]; enc_len
    · rw [OracleComp.queriesWith_bind, OracleComp.queriesWith_pure, List.append_nil] at h2
      refine (mem_queriesWith_recoverProgram_length_le answer ⟨φ, k - 1⟩ h2).trans ?_
      have hk_enc := length_encNat_mono (show k - 1 ≤ φ.length by omega)
      simp only [encMaxSATQuery_apply, encMaxSATQueryFields]; enc_len

/-- **Correctness of `solveMaxSAT` against `encMaxSATQuery '' MaxSATThreshold`.** Recovers both
`optValue = maxClauseScore φ` and an assignment achieving `maxClauseScore φ`. -/
theorem solveMaxSAT_spec (φ : CNF ℕ) :
    let sol := solveMaxSAT (encMaxSATQuery '' MaxSATThreshold) φ
    sol.optValue = maxClauseScore φ ∧
      φ.countP (Clause.eval (SAT.assignment φ sol.assignmentBits)) = maxClauseScore φ ∧
      ∀ σ : ℕ → Bool, φ.countP (Clause.eval σ) ≤ sol.optValue := by
  classical
  set A := encMaxSATQuery '' MaxSATThreshold
  have hmem_iff (r : MaxSATQuery) : decide (encMaxSATQuery r ∈ A) = true ↔ r ∈ MaxSATThreshold := by
    rw [decide_eq_true_iff, encMaxSATQuery.injective.mem_set_image]
  set k_val : ℕ := OracleComp.interpret (m := Id) (languageOracle A)
    (bisectProgram (fun ψ m => encMaxSATQuery ⟨ψ, m⟩) (fun _ => 1) (fun ψ => ψ.length + 1) φ)
  have hbisect : k_val - 1 = maxClauseScore φ := by
    have hfn : (fun m => decide (encMaxSATQuery ⟨φ, m⟩ ∈ A)) =
        fun m => decide (MaxSATQuery.mk φ m ∈ MaxSATThreshold) :=
      funext fun m => Bool.eq_iff_iff.mpr
        ((hmem_iff ⟨φ, m⟩).trans decide_eq_true_iff.symm)
    rw [show k_val = _ from interpret_bisectProgram A _ _ _ φ, maxClauseScore, hfn,
      iterate_bisectStep_eq_lowerBound _ fun _ _ _ hmm' _ ht => maxSATThreshold_mono φ hmm' ht]
  have hsol : solveMaxSAT A φ =
      ⟨maxClauseScore φ, recoverBits (fun r => decide (encMaxSATQuery r ∈ A))
        ⟨φ, maxClauseScore φ⟩⟩ := by
    rw [← hbisect]; simp only [solveMaxSAT, solveMaxSATProgram, OracleComp.interpret_bind,
      interpret_recoverProgram, OracleComp.interpret_pure]; rfl
  dsimp only; rw [hsol]
  obtain ⟨_, ⟨σ₀, hσ₀⟩, hupper⟩ := maxClauseScore_spec φ
  exact ⟨rfl, le_antisymm (hupper _)
    (target_le_countP_recoverBits (q := ⟨φ, maxClauseScore φ⟩)
      (fun r _ => hmem_iff r) ⟨σ₀, hσ₀.symm.le⟩), hupper⟩

/-- **Polynomial-time oracle certificate for `solveMaxSAT`** relative to any oracle `A`, making
at most `2 * |encCNF φ| + 1` requests (and per-instance `φ.length.size + φ.numVars`). -/
theorem computableInPolyTimeWithOracleQueries_solveMaxSAT (A : Set (List Bool)) :
    ComputableInPolyTimeWithOracleQueries A (fun n => 2 * n + 1) (solveMaxSAT A)
      encCNF encMaxSATSolution := by
  open ComputableInPolyTime in
  have hb_cert := isOraclePPTOn_bisectProgram (req := fun ψ m => encMaxSATQuery ⟨ψ, m⟩)
    (encMaxSATQuery_mk_polyTime (encOracleThresholdQuery_inst_polyTime id')
      (encOracleThresholdQuery_target_polyTime id')).encoding_comp (const 1)
    (binary_add' (unary_to_binary.comp (SAT.computableInPolyTime_length id')) (const 1))
  have hrec_pair : IsOraclePPTOn (encPair encCNF encNat) encMaxSATSolution
      (fun p : CNF ℕ × ℕ => do
        let bits ← OracleComp.interpret ProbOracleComp.query (recoverProgram ⟨p.1, p.2 - 1⟩)
        pure (MaxSATSolution.mk (p.2 - 1) bits)) := by
    simpa only [← bind_pure_comp] using
      (isOraclePPTOn_recoverProgram.preprocess
        (encMaxSATQuery_mk_polyTime (fst _ _) (binary_sub' (snd _ _) (const 1)))).map_with
        (f := fun p bits => MaxSATSolution.mk (p.2 - 1) bits)
        (encMaxSATSolution_mk_polyTime (binary_sub' ((snd _ _).comp (fst _ _)) (const 1)) (snd _ _))
  refine ⟨solveMaxSATProgram, (hb_cert.bind_with (second := fun (ψ : CNF ℕ) (k : ℕ) => do
      let bits ← OracleComp.interpret ProbOracleComp.query (recoverProgram ⟨ψ, k - 1⟩)
      pure (MaxSATSolution.mk (k - 1) bits)) hrec_pair).congr fun _ _ _ _ => ?_,
    fun φ => ⟨rfl, ?_⟩⟩
  · simp only [solveMaxSATProgram, OracleComp.interpret_bind, OracleComp.interpret_pure]
    rfl
  · have hqb := (solveMaxSATProgram_query_bounds (languageOracle A) φ).1
    have hlen_le : φ.length ≤ (encCNF φ).length := SizedListEncoding.length_le (encA :=
      encList (encPair encNat encBool)) (encL := encList (encList (encPair encNat encBool))) φ
    have hsize_le : φ.length.size ≤ (encCNF φ).length :=
      (Nat.size_le_size hlen_le).trans (Nat.size_le.mpr Nat.lt_two_pow_self)
    have hnv_le : CNF.numVars φ ≤ (encCNF φ).length :=
      (CNF.numVars_le_length_vars φ).trans (SAT.length_vars_le φ)
    dsimp only
    omega

/-- If `encMaxSATQuery '' MaxSATThreshold ∈ P encBits`, then `solveMaxSAT` computes both the exact
maximum satisfied-clause count and an optimal assignment in polynomial time. -/
theorem computableInPolyTime_solveMaxSAT_of_mem_P
    (hP : encMaxSATQuery '' MaxSATThreshold ∈ P encBits) :
    ComputableInPolyTime (solveMaxSAT (encMaxSATQuery '' MaxSATThreshold))
      encCNF encMaxSATSolution :=
  (computableInPolyTimeWithOracleQueries_solveMaxSAT
    (encMaxSATQuery '' MaxSATThreshold)).computableInPolyTimeWithOracle.computableInPolyTime hP

end MaxSAT

end Complexity

end Cslib
