/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.Code.SelfCorrection
public import CslibFrontier.Foundations.Data.Matrix.Permanent.Line
public import CslibFrontier.Languages.Probabilistic.Oracle.QueryCount
public import CslibFrontier.Languages.Probabilistic.Oracle.Run
public import CslibFrontier.Languages.Probabilistic.Vector
public import CslibFrontier.Probability.Concentration
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.List.MinMax
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.ToReal
import CslibFrontier.Probability.PMF.Uniform

/-!
# Lipton's random self-reduction of the permanent

Given an oracle `O : Matrix (Fin n) (Fin n) F → F` over a finite field `F` that agrees with the
matrix permanent on most matrices, Lipton's random self-reduction (R. J. Lipton, *New directions in
testing*, 1991; [Arora and Barak][AroraBarak09], Theorem 8.30) recovers `A.permanent` in the worst
case for every matrix `A : Matrix (Fin n) (Fin n) F`:

1. **Single-trial interpolation (`liptonPermanentTrial`).** Choose `n + 1` distinct nonzero nodes
   `ν : Fin (n + 1) ↪ F` (which exist whenever `n + 2 ≤ Fintype.card F`, and in particular under
   `3 * n < Fintype.card F` for `1 ≤ n`). Sample `R : Matrix (Fin n) (Fin n) F` uniformly at
   random, query `O (A + ν i • R)` at each `i : Fin (n + 1)`, and combine the replies with the
   Lagrange weights `Cslib.Code.lagrangeWeight ν i` at `0`.
   - Since `t ↦ (A + t • R).permanent` has degree at most `n`
     (`Matrix.exists_natDegree_le_eval_eq_permanent_add_smul`), Lagrange interpolation recovers
     `A.permanent` whenever all `n + 1` queried points avoid the oracle's error set
     (`lagrangeDecode_permanent`).
   - Because `ν i ≠ 0`, each query `A + ν i • R` is individually uniform over
     `Matrix (Fin n) (Fin n) F` (`map_add_smul_uniformOfFintype`, `eval_map_add_smul_uniform`).
   - By the union bound over the `n + 1` queries (`card_lagrangeDecode_permanent_ne_le`), the
     single-trial algorithm makes `n + 1` oracle queries (`isQueryBounded_liptonPermanentTrial`,
     `length_transcript_liptonPermanentTrial`) and outputs `A.permanent` with probability at least
     `1 - (n + 1) / (3 * n)` whenever `#{M | O M ≠ M.permanent} ≤ |F|^{n²} / (3 * n)`
     (`liptonPermanentTrial_prob_ge`, `liptonPermanentTrial_prob_toReal_ge`).

2. **Plurality amplification (`liptonPermanentPlurality`).** Repeating `liptonPermanentTrial ν A`
   for `k` independent trials and taking the plurality (`plurality 0`) makes `k * (n + 1)` queries
   (`isQueryBounded_liptonPermanentPlurality`, `length_transcript_liptonPermanentPlurality`) and
   drives the failure probability down to `exp (-2 * k * γ²) ≤ 2^{-(2 * γ² * k)}` whenever a
   single trial succeeds with margin `γ` above `1 / 2`
   (`liptonPermanentPlurality_prob_toReal_ge_of_margin`).
   - Under the draft's `#{M | O M ≠ M.permanent} ≤ |F|^{n²} / (3 * n)` hypothesis, the union-bound
     single-trial failure rate `(n + 1) / (3 * n)` is `2 / 3` at `n = 1`, `1 / 2` at `n = 2`, and
     at most `4 / 9 = 1 / 2 - 1 / 18` for `3 ≤ n`, giving success probability at least
     `1 - 2^{-k / 162}` (`liptonPermanentPlurality_prob_toReal_ge`).
   - Under `#{M | O M ≠ M.permanent} ≤ |F|^{n²} / (4 * n)` for `2 ≤ n`, the margin is `γ = 1 / 8`,
     giving `1 - 2^{-k / 32}` (`liptonPermanentPlurality_prob_toReal_ge_of_four_mul`); under
     `#{M | O M ≠ M.permanent} ≤ |F|^{n²} / (3 * (n + 1))` for all `n`, the margin is `γ = 1 / 6`,
     giving `1 - 2^{-k / 18}` (`liptonPermanentPlurality_prob_toReal_ge_of_three_mul_succ`).

## Model notes

* **Probabilistic oracle model:** algorithms are expressed in the native `Cslib.ProbOracleComp`
  monad over the typed query interface `PermanentOracleSpec n F`. This is a query-complexity
  milestone: finite-field arithmetic and matrix addition/scaling are performed in `F` rather than
  charged as bit-level Turing machine steps.
* **Precision choice for high probability:** "with high probability" in Arora–Barak Theorem 8.30 is
  made precise by the `k`-trial plurality wrapper `liptonPermanentPlurality k ν A` achieving
  success probability `≥ 1 - 2^{-Ω(k)}` with explicit constants.

## References

* R. J. Lipton, *New directions in testing*, DIMACS Series in Discrete Mathematics and Theoretical
  Computer Science 2 (1991), 191–202.
* [S. Arora and B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09],
  Theorem 8.30 (2007 draft, printed p. 168 / PDF p. 184)
-/

@[expose] public section

namespace Cslib.Complexity

open Finset Polynomial Probability
open scoped ENNReal

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}

/-! ### Uniformity along an affine line and algebraic self-correction -/

/-- For a nonzero scalar `c : F` and base point `x : V` in a module over `F`, the affine map
`v ↦ x + c • v` is a bijection on `V`. -/
def affineLineEquiv {V : Type*} [AddCommGroup V] [Module F V] (x : V) {c : F} (hc : c ≠ 0) :
    V ≃ V where
  toFun v := x + c • v
  invFun w := c⁻¹ • (w - x)
  left_inv v := by simp [smul_smul, inv_mul_cancel₀ hc]
  right_inv w := by simp [smul_smul, mul_inv_cancel₀ hc]

omit [Fintype F] [DecidableEq F] in
@[simp]
theorem affineLineEquiv_apply {V : Type*} [AddCommGroup V] [Module F V] (x : V) {c : F}
    (hc : c ≠ 0) (v : V) : affineLineEquiv x hc v = x + c • v := rfl

omit [Fintype F] [DecidableEq F] in
/-- If `v` is uniformly distributed on a finite vector space `V` over `F` and `c ≠ 0`, then
`x + c • v` is uniformly distributed on `V`. -/
theorem map_add_smul_uniformOfFintype {V : Type*} [AddCommGroup V] [Module F V] [Fintype V]
    [Nonempty V] (x : V) {c : F} (hc : c ≠ 0) :
    (PMF.uniformOfFintype V).map (fun v => x + c • v) = PMF.uniformOfFintype V :=
  Cslib.Probability.PMF.uniformOfFintype_map_equiv (affineLineEquiv x hc)

omit [Fintype F] [DecidableEq F] in
/-- Sampling `v` uniformly from `V` and returning `x + c • v` for `c ≠ 0` has the uniform law on
`V`. -/
theorem eval_map_add_smul_uniform {V : Type} [AddCommGroup V] [Module F V] [Fintype V]
    [Nonempty V] (x : V) {c : F} (hc : c ≠ 0) :
    ProbComp.eval ((fun v => x + c • v) <$> ProbComp.uniform V) = PMF.uniformOfFintype V := by
  rw [ProbComp.eval_map, ProbComp.eval_uniform, map_add_smul_uniformOfFintype x hc]

omit [Field F] [DecidableEq F] in
/-- The number of `n × n` matrices over `F` is `|F|^{n²}`. -/
@[simp]
theorem card_matrix_fin : Fintype.card (Matrix (Fin n) (Fin n) F) = Fintype.card F ^ (n * n) := by
  change Fintype.card (Fin n → Fin n → F) = _
  rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, ← pow_mul]

omit [Fintype F] [DecidableEq F] in
/-- **Lagrange interpolation along any line recovers the permanent.** For any `n + 1` distinct
evaluation nodes `ν : Fin (n + 1) ↪ F` and matrices `A, R : Matrix (Fin n) (Fin n) F`,
interpolating `(A + ν i • R).permanent` at `0` yields `A.permanent`. -/
theorem lagrangeDecode_permanent (ν : Fin (n + 1) ↪ F) (A R : Matrix (Fin n) (Fin n) F) :
    Code.lagrangeDecode ν Matrix.permanent A R = A.permanent :=
  Code.lagrangeDecode_eq_of_exists_natDegree_le ν
    (by simpa using Matrix.exists_natDegree_le_eval_eq_permanent_add_smul A R)

/-- **Error count for Lipton's line interpolation.** For any `n + 1` distinct nonzero nodes
`ν : Fin (n + 1) ↪ F` and oracle `O : Matrix (Fin n) (Fin n) F → F`, at most
`(n + 1) * #{M | O M ≠ M.permanent}` directions `R` make `Code.lagrangeDecode ν O A R` differ from
`A.permanent`. -/
theorem card_lagrangeDecode_permanent_ne_le (ν : Fin (n + 1) ↪ F) (hν : ∀ i, ν i ≠ 0)
    (O : Matrix (Fin n) (Fin n) F → F) (A : Matrix (Fin n) (Fin n) F) :
    #{R | Code.lagrangeDecode ν O A R ≠ A.permanent} ≤
      (n + 1) * #{M | O M ≠ M.permanent} :=
  Code.card_lagrangeDecode_ne_le_of_forall_eq ν hν (lagrangeDecode_permanent ν A) O

omit [Field F] [DecidableEq F] in
/-- The draft's field-size condition `3 * n < Fintype.card F` (for `1 ≤ n`) implies
`n + 2 ≤ Fintype.card F`. -/
theorem add_two_le_card_of_three_mul_lt (hn : 1 ≤ n) (hcard : 3 * n < Fintype.card F) :
    n + 2 ≤ Fintype.card F := by
  omega

omit [DecidableEq F] in
/-- Whenever `d + 2 ≤ Fintype.card F`, there exist `d + 1` distinct nonzero elements in `F`. -/
theorem exists_nonzero_nodes_of_le_card {d : ℕ} (hcard : d + 2 ≤ Fintype.card F) :
    ∃ ν : Fin (d + 1) ↪ F, ∀ i, ν i ≠ 0 := by
  classical
  have hle : d + 1 ≤ #(univ.erase (0 : F)) := by
    rw [card_erase_of_mem (mem_univ 0), card_univ]
    omega
  obtain ⟨s, hs, hscard⟩ := exists_subset_card_eq hle
  let e : Fin (d + 1) ≃ s := (s.equivFinOfCardEq hscard).symm
  refine ⟨⟨fun i => (e i).1, fun i j hij => e.injective (Subtype.ext hij)⟩, fun i => ?_⟩
  exact ne_of_mem_erase (hs (e i).2)

omit [DecidableEq F] in
/-- Canonical choice of `d + 1` distinct nonzero evaluation nodes in `F` when
`d + 2 ≤ Fintype.card F`. -/
noncomputable def nonzeroNodes {d : ℕ} (hcard : d + 2 ≤ Fintype.card F) : Fin (d + 1) ↪ F :=
  (exists_nonzero_nodes_of_le_card hcard).choose

omit [DecidableEq F] in
theorem nonzeroNodes_ne_zero {d : ℕ} (hcard : d + 2 ≤ Fintype.card F) (i : Fin (d + 1)) :
    nonzeroNodes hcard i ≠ 0 :=
  (exists_nonzero_nodes_of_le_card hcard).choose_spec i

/-! ### Native `ProbOracleComp` single-trial algorithm -/

/-- Query interface for an oracle computing a function `Matrix (Fin n) (Fin n) F → F`. -/
abbrev PermanentOracleSpec (n : ℕ) (F : Type) : Matrix (Fin n) (Fin n) F → Type :=
  fun _ => F

/-- **Lipton's single-trial random self-reduction for the permanent**
([Arora and Barak][AroraBarak09], Theorem 8.30).
Draws a uniform random matrix `R : Matrix (Fin n) (Fin n) F`, queries the oracle at the `n + 1`
points `A + ν i • R` along the random line through `A`, and returns the Lagrange interpolation at
`0`.

This is a query-complexity milestone in `ProbOracleComp`: field arithmetic and matrix
addition/scaling are performed in `F` rather than charged on a bit-level Turing tape. -/
noncomputable def liptonPermanentTrial (ν : Fin (n + 1) ↪ F)
    (A : Matrix (Fin n) (Fin n) F) :
    ProbOracleComp (PermanentOracleSpec n F) F := do
  let R ← ProbOracleComp.sample (ProbComp.uniform (Matrix (Fin n) (Fin n) F))
  let y ← OracleComp.pi (fun i : Fin (n + 1) => ProbOracleComp.query (A + ν i • R))
  return ∑ i : Fin (n + 1), Code.lagrangeWeight ν i * y i

section PiHelpers

variable {Query : Type} {spec : Query → Type}

/-- Running `OracleComp.pi` against an oracle runs each coordinate program in order. -/
theorem run_pi {m : ℕ} {α : Fin m → Type}
    (programs : (i : Fin m) → ProbOracleComp spec (α i))
    (O : (q : Query) → ProbComp (spec q)) :
    ProbOracleComp.run (OracleComp.pi programs) O =
      OracleComp.pi (fun i => ProbOracleComp.run (programs i) O) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [OracleComp.pi_succ, ProbOracleComp.run_bind, ProbOracleComp.run_map,
      ih (fun i => programs i.succ)]

/-- Running a tuple of external queries against a deterministic oracle returns the tuple of
answers. -/
theorem run_pi_query {m : ℕ} (q : Fin m → Query) (O : (x : Query) → spec x) :
    ProbOracleComp.run
      (OracleComp.pi (fun i : Fin m => ProbOracleComp.query (spec := spec) (q i)))
      (fun x => pure (O x)) = pure (fun i => O (q i)) := by
  induction m with
  | zero =>
    change (pure (fun i : Fin 0 => i.elim0) : ProbComp ((i : Fin 0) → spec (q i))) = _
    congr 1
    funext i
    exact i.elim0
  | succ m ih =>
    simp only [OracleComp.pi_succ, ProbOracleComp.run_bind, ProbOracleComp.run_query,
      ProbOracleComp.run_map, ih (fun i => q i.succ), pure_bind, map_pure]
    congr 1
    funext i
    exact Fin.cases rfl (fun _ => rfl) i

/-- A tuple of `m` external queries makes at most `m` external queries. -/
theorem isQueryBounded_pi_query {m : ℕ} (q : Fin m → Query) :
    ProbOracleComp.IsQueryBounded
      (OracleComp.pi (fun i : Fin m => ProbOracleComp.query (spec := spec) (q i))) m := by
  induction m with
  | zero => exact OracleComp.IsCostBounded.pure _ 0
  | succ m ih =>
    rw [OracleComp.pi_succ]
    refine OracleComp.IsCostBounded.mono (n := 1 + m) ?_ (by omega)
    refine (ProbOracleComp.IsQueryBounded.query (q 0)).bind fun _ => ?_
    exact (OracleComp.isCostBounded_map_iff _ _ _).mpr (ih (fun i => q i.succ))

/-- Every supported stateful execution of a tuple of `m` external queries logs a transcript of
exact length `m`. -/
theorem length_transcript_pi_query {m : ℕ} {State : Type}
    (oracle : (q : Query) → StateT State PMF (spec q)) (q : Fin m → Query)
    {s s' : State} {result : (i : Fin m) → spec (q i)}
    {transcript : OracleComp.Transcript spec}
    (hmem : (result, s', transcript) ∈
      (ProbOracleComp.runWith (OracleComp.withTranscript oracle)
        (OracleComp.pi (fun i : Fin m => ProbOracleComp.query (spec := spec) (q i)))
        (s, [])).support) :
    transcript.length = m := by
  induction m generalizing s s' transcript with
  | zero =>
    simp only [OracleComp.pi_zero, ProbOracleComp.runWith_pure, PMF.mem_support_pure_iff,
      Prod.mk.injEq] at hmem
    rcases hmem with ⟨-, -, rfl⟩
    rfl
  | succ m ih =>
    simp only [OracleComp.pi_succ, ProbOracleComp.runWith_bind, ProbOracleComp.runWith_query,
      ProbOracleComp.runWith_map, PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at hmem
    obtain ⟨⟨first, s₁, seen⟩, hfirst, ⟨rest, s₂, total⟩, hrest, heq⟩ := hmem
    simp only [Prod.map, id_eq, Prod.mk.injEq] at heq
    rcases heq with ⟨-, rfl, rfl⟩
    simp only [OracleComp.withTranscript, PMF.mem_support_map_iff] at hfirst
    obtain ⟨⟨ans, next⟩, -, hfirst_eq⟩ := hfirst
    cases hfirst_eq
    rw [ProbOracleComp.run_interpret_withTranscript_append, PMF.mem_support_map_iff] at hrest
    obtain ⟨⟨rest', final, fresh⟩, hfresh, hrest_eq⟩ := hrest
    cases hrest_eq
    have hlen := ih (fun i => q i.succ) hfresh
    simp [hlen]

end PiHelpers

omit [DecidableEq F] in
/-- Against a deterministic oracle `O`, running `liptonPermanentTrial ν A` samples a uniform
direction `R` and computes `Code.lagrangeDecode ν O A R`. -/
@[simp]
theorem run_liptonPermanentTrial (ν : Fin (n + 1) ↪ F) (A : Matrix (Fin n) (Fin n) F)
    (O : Matrix (Fin n) (Fin n) F → F) :
    (liptonPermanentTrial ν A).run (fun M => pure (O M)) =
      Code.lagrangeDecode ν O A <$> ProbComp.uniform (Matrix (Fin n) (Fin n) F) := by
  simp only [liptonPermanentTrial, bind_pure_comp, ProbOracleComp.run_bind,
    ProbOracleComp.run_sample, ProbOracleComp.run_map, run_pi_query, map_pure]
  rfl

omit [DecidableEq F] in
/-- Evaluating `liptonPermanentTrial ν A` against a deterministic oracle `O` pushes the uniform
distribution on `Matrix (Fin n) (Fin n) F` forward along `Code.lagrangeDecode ν O A`. -/
theorem eval_run_liptonPermanentTrial (ν : Fin (n + 1) ↪ F) (A : Matrix (Fin n) (Fin n) F)
    (O : Matrix (Fin n) (Fin n) F → F) :
    ProbComp.eval ((liptonPermanentTrial ν A).run (fun M => pure (O M))) =
      (PMF.uniformOfFintype (Matrix (Fin n) (Fin n) F)).map (Code.lagrangeDecode ν O A) := by
  rw [run_liptonPermanentTrial, ProbComp.eval_map, ProbComp.eval_uniform]

omit [DecidableEq F] in
/-- `liptonPermanentTrial ν A` makes at most `n + 1` oracle queries on every execution path. -/
theorem isQueryBounded_liptonPermanentTrial (ν : Fin (n + 1) ↪ F)
    (A : Matrix (Fin n) (Fin n) F) :
    (liptonPermanentTrial ν A).IsQueryBounded (n + 1) := by
  unfold liptonPermanentTrial
  refine OracleComp.IsCostBounded.mono (n := 0 + (n + 1)) ?_ (by omega)
  refine (ProbOracleComp.IsQueryBounded.sample _).bind fun R => ?_
  simp only [bind_pure_comp]
  exact (OracleComp.isCostBounded_map_iff _ _ _).mpr
    (isQueryBounded_pi_query (fun i : Fin (n + 1) => A + ν i • R))

omit [DecidableEq F] in
/-- **Exact query count of `liptonPermanentTrial`.** Every supported stateful execution of
`liptonPermanentTrial ν A` makes exactly `n + 1` external oracle queries. -/
theorem length_transcript_liptonPermanentTrial {State : Type}
    (oracle : (M : Matrix (Fin n) (Fin n) F) → StateT State PMF F)
    (ν : Fin (n + 1) ↪ F) (A : Matrix (Fin n) (Fin n) F)
    {s s' : State} {result : F} {transcript : OracleComp.Transcript (PermanentOracleSpec n F)}
    (hmem : (result, s', transcript) ∈
      (ProbOracleComp.runWith (OracleComp.withTranscript oracle)
        (liptonPermanentTrial ν A) (s, [])).support) :
    transcript.length = n + 1 := by
  simp only [liptonPermanentTrial, bind_pure_comp, ProbOracleComp.runWith_sample_bind,
    ProbOracleComp.runWith_map, PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at hmem
  obtain ⟨R, -, ⟨y, s₂, tr⟩, hy, heq⟩ := hmem
  simp only [Prod.map, id_eq, Prod.mk.injEq] at heq
  rcases heq with ⟨-, rfl, rfl⟩
  exact length_transcript_pi_query oracle (fun i : Fin (n + 1) => A + ν i • R) hy

/-- **Single-trial failure probability bound.** Against a deterministic oracle `O`, the probability
that `liptonPermanentTrial ν A` outputs a value different from `A.permanent` is at most
`((n + 1) * #{M | O M ≠ M.permanent}) / |F|^{n²}`. -/
theorem toOuterMeasure_run_liptonPermanentTrial_ne_le (ν : Fin (n + 1) ↪ F)
    (hν : ∀ i, ν i ≠ 0) (O : Matrix (Fin n) (Fin n) F → F) (A : Matrix (Fin n) (Fin n) F) :
    (ProbComp.eval ((liptonPermanentTrial ν A).run (fun M => pure (O M)))).toOuterMeasure
        {y | y ≠ A.permanent} ≤
      (((n + 1) * #{M | O M ≠ M.permanent} : ℕ) : ℝ≥0∞) /
        (Fintype.card F ^ (n * n) : ℕ) := by
  classical
  rw [eval_run_liptonPermanentTrial, PMF.toOuterMeasure_map_apply,
    Cslib.Probability.PMF.toOuterMeasure_uniformOfFintype, card_matrix_fin, ← div_eq_mul_inv]
  refine ENNReal.div_le_div_right ?_ _
  rw [Set.preimage_ofPred_eq]
  exact_mod_cast card_lagrangeDecode_permanent_ne_le ν hν O A

/-- **Single-trial success probability bound in terms of the oracle's error count.** -/
theorem one_sub_le_eval_run_liptonPermanentTrial (ν : Fin (n + 1) ↪ F)
    (hν : ∀ i, ν i ≠ 0) (O : Matrix (Fin n) (Fin n) F → F) (A : Matrix (Fin n) (Fin n) F) :
    1 - (((n + 1) * #{M | O M ≠ M.permanent} : ℕ) : ℝ≥0∞) /
        (Fintype.card F ^ (n * n) : ℕ) ≤
      ProbComp.eval ((liptonPermanentTrial ν A).run (fun M => pure (O M))) A.permanent := by
  set p := ProbComp.eval ((liptonPermanentTrial ν A).run (fun M => pure (O M)))
  have hcompl := Cslib.Probability.PMF.toOuterMeasure_add_compl_ennreal p ({A.permanent} : Set F)
  rw [PMF.toOuterMeasure_apply_singleton] at hcompl
  have hcompl_set : ({A.permanent} : Set F)ᶜ = {y | y ≠ A.permanent} := rfl
  rw [hcompl_set] at hcompl
  have hle := toOuterMeasure_run_liptonPermanentTrial_ne_le ν hν O A
  have hne_top := Cslib.Probability.PMF.toOuterMeasure_ne_top p {y | y ≠ A.permanent}
  calc 1 - (((n + 1) * #{M | O M ≠ M.permanent} : ℕ) : ℝ≥0∞) / (Fintype.card F ^ (n * n) : ℕ)
      ≤ 1 - p.toOuterMeasure {y | y ≠ A.permanent} := tsub_le_tsub_left hle 1
    _ = p A.permanent := by rw [← hcompl, ENNReal.add_sub_cancel_right hne_top]

/-- **Arora–Barak Theorem 8.30 (single-trial endpoint):** if `O` errs on at most
`|F|^{n²} / (3 * n)` matrices and `ν : Fin (n + 1) ↪ F` are `n + 1` distinct nonzero nodes, then
`liptonPermanentTrial ν A` outputs `A.permanent` with probability at least
`1 - (n + 1) / (3 * n)` for every `A`. -/
theorem liptonPermanentTrial_prob_ge (ν : Fin (n + 1) ↪ F) (hν : ∀ i, ν i ≠ 0)
    (O : Matrix (Fin n) (Fin n) F → F)
    (hO : #{M | O M ≠ M.permanent} ≤ Fintype.card F ^ (n * n) / (3 * n))
    (A : Matrix (Fin n) (Fin n) F) :
    1 - (n + 1 : ℝ≥0∞) / (3 * n : ℕ) ≤
      ProbComp.eval ((liptonPermanentTrial ν A).run (fun M => pure (O M))) A.permanent := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · refine (tsub_le_tsub_left ?_ 1).trans (one_sub_le_eval_run_liptonPermanentTrial ν hν O A)
    have hmul : #{M | O M ≠ M.permanent} * (3 * n) ≤ Fintype.card F ^ (n * n) :=
      Nat.mul_le_of_le_div _ _ _ hO
    have h3n0 : ((3 * n : ℕ) : ℝ≥0∞) ≠ 0 := by positivity
    have h3ntop : ((3 * n : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
    refine ENNReal.div_le_of_le_mul ?_
    calc (((n + 1) * #{M | O M ≠ M.permanent} : ℕ) : ℝ≥0∞)
        = (n + 1 : ℝ≥0∞) * (#{M | O M ≠ M.permanent} : ℕ) *
            ((3 * n : ℕ) * ((3 * n : ℕ) : ℝ≥0∞)⁻¹) := by
          rw [ENNReal.mul_inv_cancel h3n0 h3ntop, mul_one]; push_cast; ring
      _ = (n + 1 : ℝ≥0∞) / (3 * n : ℕ) *
            ((#{M | O M ≠ M.permanent} * (3 * n) : ℕ) : ℝ≥0∞) := by
          rw [div_eq_mul_inv]; push_cast; ring
      _ ≤ (n + 1 : ℝ≥0∞) / (3 * n : ℕ) * (Fintype.card F ^ (n * n) : ℕ) := by
          gcongr

/-- Real-valued single-trial failure probability bound in terms of the oracle's error count. -/
theorem toOuterMeasure_run_liptonPermanentTrial_ne_toReal_le (ν : Fin (n + 1) ↪ F)
    (hν : ∀ i, ν i ≠ 0) (O : Matrix (Fin n) (Fin n) F → F) (A : Matrix (Fin n) (Fin n) F) :
    ((ProbComp.eval ((liptonPermanentTrial ν A).run (fun M => pure (O M)))).toOuterMeasure
        {y | y ≠ A.permanent}).toReal ≤
      ((n + 1) * #{M | O M ≠ M.permanent} : ℝ) / (Fintype.card F ^ (n * n) : ℝ) := by
  have hle := toOuterMeasure_run_liptonPermanentTrial_ne_le ν hν O A
  have htop : (((n + 1) * #{M | O M ≠ M.permanent} : ℕ) : ℝ≥0∞) /
      (Fintype.card F ^ (n * n) : ℕ) ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by positivity)
  have hreal := ENNReal.toReal_mono htop hle
  rw [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast] at hreal
  exact_mod_cast hreal

/-- Real-valued single-trial success probability bound in terms of the oracle's error count. -/
theorem one_sub_le_eval_run_liptonPermanentTrial_toReal (ν : Fin (n + 1) ↪ F)
    (hν : ∀ i, ν i ≠ 0) (O : Matrix (Fin n) (Fin n) F → F) (A : Matrix (Fin n) (Fin n) F) :
    1 - ((n + 1) * #{M | O M ≠ M.permanent} : ℝ) / (Fintype.card F ^ (n * n) : ℝ) ≤
      (ProbComp.eval ((liptonPermanentTrial ν A).run (fun M => pure (O M)))
        A.permanent).toReal := by
  set p := ProbComp.eval ((liptonPermanentTrial ν A).run (fun M => pure (O M)))
  have hcompl := Cslib.Probability.PMF.toOuterMeasure_toReal_add_compl p ({A.permanent} : Set F)
  rw [PMF.toOuterMeasure_apply_singleton] at hcompl
  have hcompl_set : ({A.permanent} : Set F)ᶜ = {y | y ≠ A.permanent} := rfl
  rw [hcompl_set] at hcompl
  linarith [toOuterMeasure_run_liptonPermanentTrial_ne_toReal_le ν hν O A]

/-- Real-valued form of `liptonPermanentTrial_prob_ge`: for `1 ≤ n` and
`#{M | O M ≠ M.permanent} ≤ |F|^{n²} / (3 * n)`, the single-trial algorithm outputs `A.permanent`
with probability at least `1 - (n + 1) / (3 * n)`. -/
theorem liptonPermanentTrial_prob_toReal_ge (hn : 1 ≤ n) (ν : Fin (n + 1) ↪ F)
    (hν : ∀ i, ν i ≠ 0) (O : Matrix (Fin n) (Fin n) F → F)
    (hO : #{M | O M ≠ M.permanent} ≤ Fintype.card F ^ (n * n) / (3 * n))
    (A : Matrix (Fin n) (Fin n) F) :
    1 - (n + 1 : ℝ) / (3 * n) ≤
      (ProbComp.eval ((liptonPermanentTrial ν A).run (fun M => pure (O M)))
        A.permanent).toReal := by
  have hmul : (#{M | O M ≠ M.permanent} : ℝ) * (3 * n) ≤ (Fintype.card F : ℝ) ^ (n * n) := by
    exact_mod_cast Nat.mul_le_of_le_div _ _ _ hO
  have hN : (0 : ℝ) < (Fintype.card F : ℝ) ^ (n * n) := by positivity
  have h3n : (0 : ℝ) < 3 * n := by positivity
  have hdiv : ((n + 1) * #{M | O M ≠ M.permanent} : ℝ) / (Fintype.card F ^ (n * n) : ℝ) ≤
      (n + 1 : ℝ) / (3 * n) := by
    rw [div_le_div_iff₀ hN h3n]
    nlinarith
  linarith [one_sub_le_eval_run_liptonPermanentTrial_toReal ν hν O A]

/-! ### Plurality amplification over `k` independent trials -/

/-- The most frequent element of `xs`, breaking ties in favor of the earliest element of `xs`
achieving the maximum frequency, or `default` when `xs` is empty. -/
def plurality {α : Type*} [DecidableEq α] (default : α) (xs : List α) : α :=
  (xs.argmax (fun x => xs.count x)).getD default

/-- Two distinct elements appear at most `xs.length` times in total. -/
theorem count_add_count_le_length_of_ne {α : Type*} [DecidableEq α] (xs : List α) {a b : α}
    (hab : a ≠ b) : xs.count a + xs.count b ≤ xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rw [List.count_cons, List.count_cons, List.length_cons]
    by_cases hxa : x = a
    · subst hxa
      have hxb : (x == b) = false := beq_eq_false_iff_ne.mpr hab
      simp only [beq_self_eq_true, ↓reduceIte, hxb, Bool.false_eq_true]
      omega
    · have hxa' : (x == a) = false := beq_eq_false_iff_ne.mpr hxa
      have hxb' : (if x == b then 1 else 0) ≤ 1 := by split_ifs <;> omega
      simp only [hxa', Bool.false_eq_true, ↓reduceIte]
      omega

/-- Whenever `a` appears strictly more than half the time in `xs`, `plurality default xs = a`. -/
theorem plurality_eq_of_length_lt_two_mul_count {α : Type*} [DecidableEq α] (default : α)
    {xs : List α} {a : α} (h : xs.length < 2 * xs.count a) :
    plurality default xs = a := by
  have hpos : 0 < xs.count a := by omega
  have ha : a ∈ xs := List.count_pos_iff.mp hpos
  have hne : xs ≠ [] := List.ne_nil_of_mem ha
  unfold plurality
  rcases hm : xs.argmax (fun x => xs.count x) with _ | m
  · exact (hne (List.argmax_eq_none.mp hm)).elim
  · simp only [Option.getD_some]
    have hle : xs.count a ≤ xs.count m := List.le_of_mem_argmax ha hm
    by_contra hma
    have hsum := count_add_count_le_length_of_ne xs (Ne.symm hma)
    omega

private theorem count_true_map_beq {α : Type*} [DecidableEq α] (xs : List α) (a : α) :
    (xs.map (· == a)).count true = xs.count a := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [List.count_cons, ih]

private theorem eval_map_beq_true {α : Type} [DecidableEq α] (program : ProbComp α) (a : α) :
    ProbComp.eval ((· == a) <$> program) true = ProbComp.eval program a := by
  rw [ProbComp.eval_map, PMF.map_apply, tsum_eq_single a]
  · simp
  · intro b hba
    simp [beq_iff_eq, hba]

private theorem countTrue_le_mean_sub (count : ℕ) (program : ProbComp Bool) {ε : ℝ} (hε : 0 ≤ ε) :
    ((ProbComp.eval (OracleComp.countTrue count program)).toOuterMeasure {successes |
      (successes : ℝ) ≤ count * (ProbComp.eval program true).toReal - ε}).toReal ≤
        Real.exp (-2 * ε ^ 2 / count) := by
  rw [ProbComp.eval_countTrue, PMF.toOuterMeasure_map_apply]
  have h := Cslib.Probability.PMF.pi_sum_le_mean_sub (fun _ : Fin count => ProbComp.eval program)
    (fun _ bit => (bit.toNat : ℝ)) (bound := 1) (by norm_num)
    (by intro i bit _; cases bit <;> norm_num) hε
  simpa [Set.preimage_ofPred_eq, Nat.cast_sum, Fintype.sum_bool] using h

private theorem exp_neg_le_two_rpow_neg {x : ℝ} (hx : 0 ≤ x) :
    Real.exp (-x) ≤ (2 : ℝ) ^ (-x) := by
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), Real.exp_le_exp]
  have hlog : Real.log 2 ≤ 1 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    linarith [Real.add_one_le_exp 1]
  nlinarith

/-- **Plurality concentration for `k` independent trials.** If a closed probabilistic program
`program : ProbComp α` outputs `a` with probability at least `1 / 2 + γ` (for `0 ≤ γ`), then the
plurality of `k` independent runs differs from `a` with probability at most
`exp (-2 * k * γ²)`. -/
theorem toOuterMeasure_plurality_replicate_ne_toReal_le {α : Type} [DecidableEq α]
    (default a : α) (k : ℕ) (program : ProbComp α) {γ : ℝ} (hγ : 0 ≤ γ)
    (hp : 1 / 2 + γ ≤ (ProbComp.eval program a).toReal) :
    ((ProbComp.eval (plurality default <$> OracleComp.replicate k program)).toOuterMeasure
        {y | y ≠ a}).toReal ≤ Real.exp (-2 * k * γ ^ 2) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [Nat.cast_zero, mul_zero, zero_mul, Real.exp_zero]
    exact Cslib.Probability.PMF.toOuterMeasure_toReal_le_one _ _
  have hcount := countTrue_le_mean_sub k ((· == a) <$> program) (ε := k * γ) (by positivity)
  rw [eval_map_beq_true] at hcount
  have hexp : -2 * ((k : ℝ) * γ) ^ 2 / k = -2 * k * γ ^ 2 := by
    have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
    field_simp
  rw [hexp] at hcount
  refine le_trans ?_ hcount
  simp only [OracleComp.countTrue, OracleComp.replicate_map, Functor.map_map, ProbComp.eval_map,
    PMF.toOuterMeasure_map_apply]
  have hsub : (ProbComp.eval (OracleComp.replicate k program)).toOuterMeasure
      (plurality default ⁻¹' {y | y ≠ a}) ≤
      (ProbComp.eval (OracleComp.replicate k program)).toOuterMeasure
        ((fun xs : List α => (xs.map (· == a)).count true) ⁻¹'
          {successes | (successes : ℝ) ≤ k * (ProbComp.eval program a).toReal - k * γ}) := by
    rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply]
    refine tsum_le_tsum fun xs => ?_
    by_cases hsupp : xs ∈ (ProbComp.eval (OracleComp.replicate k program)).support
    · have hlen : xs.length = k := ((ProbComp.mem_support_replicate_iff k program xs).mp hsupp).1
      by_cases hxs : xs ∈ plurality default ⁻¹' {y | y ≠ a}
      · have hmem' : xs ∈ (fun xs : List α => (xs.map (· == a)).count true) ⁻¹'
            {successes : ℕ | (successes : ℝ) ≤ k * (ProbComp.eval program a).toReal - k * γ} := by
          simp only [Set.mem_preimage, Set.mem_ofPred_eq, count_true_map_beq] at hxs ⊢
          have hle_len : 2 * xs.count a ≤ k := by
            rw [← hlen]
            by_contra hlt
            exact hxs (plurality_eq_of_length_lt_two_mul_count default (not_le.mp hlt))
          have hle_real : (2 : ℝ) * xs.count a ≤ k := by exact_mod_cast hle_len
          nlinarith
        rw [Set.indicator_of_mem hxs, Set.indicator_of_mem hmem']
      · rw [Set.indicator_of_notMem hxs]
        exact zero_le
    · have h0 : ProbComp.eval (OracleComp.replicate k program) xs = 0 :=
        (PMF.apply_eq_zero_iff _ _).mpr hsupp
      simp [Set.indicator_apply, h0]
  exact ENNReal.toReal_mono (Cslib.Probability.PMF.toOuterMeasure_ne_top _ _) hsub

/-- **Plurality success probability for `k` independent trials.** If `program` outputs `a` with
probability at least `1 / 2 + γ` (`0 ≤ γ`), then the plurality of `k` independent runs outputs `a`
with probability at least `1 - exp (-2 * k * γ²) ≥ 1 - 2^{-(2 * γ² * k)}`. -/
theorem one_sub_exp_le_eval_plurality_replicate_toReal {α : Type} [DecidableEq α]
    (default a : α) (k : ℕ) (program : ProbComp α) {γ : ℝ} (hγ : 0 ≤ γ)
    (hp : 1 / 2 + γ ≤ (ProbComp.eval program a).toReal) :
    1 - Real.exp (-2 * k * γ ^ 2) ≤
      (ProbComp.eval (plurality default <$> OracleComp.replicate k program) a).toReal := by
  set p := ProbComp.eval (plurality default <$> OracleComp.replicate k program)
  have hcompl := Cslib.Probability.PMF.toOuterMeasure_toReal_add_compl p ({a} : Set α)
  rw [PMF.toOuterMeasure_apply_singleton] at hcompl
  have hcompl_set : ({a} : Set α)ᶜ = {y | y ≠ a} := rfl
  rw [hcompl_set] at hcompl
  linarith [toOuterMeasure_plurality_replicate_ne_toReal_le default a k program hγ hp]

/-- Base-`2` exponential form of `one_sub_exp_le_eval_plurality_replicate_toReal`. -/
theorem one_sub_two_rpow_le_eval_plurality_replicate_toReal {α : Type} [DecidableEq α]
    (default a : α) (k : ℕ) (program : ProbComp α) {γ : ℝ} (hγ : 0 ≤ γ)
    (hp : 1 / 2 + γ ≤ (ProbComp.eval program a).toReal) :
    1 - (2 : ℝ) ^ (-(2 * γ ^ 2 * k)) ≤
      (ProbComp.eval (plurality default <$> OracleComp.replicate k program) a).toReal := by
  have hexp : Real.exp (-2 * k * γ ^ 2) ≤ (2 : ℝ) ^ (-(2 * γ ^ 2 * k)) := by
    rw [show -2 * (k : ℝ) * γ ^ 2 = -(2 * γ ^ 2 * k) by ring]
    exact exp_neg_le_two_rpow_neg (by positivity)
  linarith [one_sub_exp_le_eval_plurality_replicate_toReal default a k program hγ hp]

/-- **Lipton's amplified random self-reduction for the permanent**
([Arora and Barak][AroraBarak09], Theorem 8.30).
Runs `k` independent trials of `liptonPermanentTrial ν A` and returns the plurality of their
outputs (defaulting to `0` when `k = 0`).

"With high probability" in Arora–Barak Theorem 8.30 is made precise here as error at most
`2^{-Ω(k)}` after `k` independent trials; this is a precision choice on the amplification
wrapper. -/
noncomputable def liptonPermanentPlurality (k : ℕ) (ν : Fin (n + 1) ↪ F)
    (A : Matrix (Fin n) (Fin n) F) :
    ProbOracleComp (PermanentOracleSpec n F) F :=
  plurality 0 <$> OracleComp.replicate k (liptonPermanentTrial ν A)

section ReplicateHelpers

variable {Query α : Type} {spec : Query → Type}

/-- Running `OracleComp.replicate` against an oracle repeats the run of the underlying program. -/
@[simp]
theorem run_replicate (k : ℕ) (program : ProbOracleComp spec α)
    (O : (q : Query) → ProbComp (spec q)) :
    ProbOracleComp.run (OracleComp.replicate k program) O =
      OracleComp.replicate k (ProbOracleComp.run program O) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp [OracleComp.replicate_succ, ih]

/-- Repeating a `q`-query-bounded program `k` times makes at most `k * q` queries. -/
theorem isQueryBounded_replicate (k : ℕ) {program : ProbOracleComp spec α} {q : ℕ}
    (hq : program.IsQueryBounded q) :
    ProbOracleComp.IsQueryBounded (OracleComp.replicate k program) (k * q) := by
  induction k with
  | zero =>
    rw [Nat.zero_mul]
    exact OracleComp.IsCostBounded.pure _ 0
  | succ k ih =>
    rw [OracleComp.replicate_succ]
    refine OracleComp.IsCostBounded.mono (n := q + k * q) ?_ (by simp [Nat.succ_mul, Nat.add_comm])
    refine hq.bind fun _ => ?_
    exact (OracleComp.isCostBounded_map_iff _ _ _).mpr ih

/-- If every supported execution of `program` makes exactly `q` external queries, then every
supported execution of `OracleComp.replicate k program` makes exactly `k * q` external queries. -/
theorem length_transcript_replicate {State : Type}
    (oracle : (x : Query) → StateT State PMF (spec x)) (k : ℕ)
    {program : ProbOracleComp spec α} {q : ℕ}
    (hq : ∀ {s s' : State} {result : α} {tr : OracleComp.Transcript spec},
      (result, s', tr) ∈
        (ProbOracleComp.runWith (OracleComp.withTranscript oracle) program (s, [])).support →
        tr.length = q)
    {s s' : State} {results : List α} {transcript : OracleComp.Transcript spec}
    (hmem : (results, s', transcript) ∈
      (ProbOracleComp.runWith (OracleComp.withTranscript oracle)
        (OracleComp.replicate k program) (s, [])).support) :
    transcript.length = k * q := by
  induction k generalizing s s' results transcript with
  | zero =>
    simp only [OracleComp.replicate_zero, ProbOracleComp.runWith_pure, PMF.mem_support_pure_iff,
      Prod.mk.injEq] at hmem
    rcases hmem with ⟨-, -, rfl⟩
    simp
  | succ k ih =>
    simp only [OracleComp.replicate_succ, ProbOracleComp.runWith_bind, ProbOracleComp.runWith_map,
      PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at hmem
    obtain ⟨⟨first, s₁, seen⟩, hfirst, ⟨rest, s₂, total⟩, hrest, heq⟩ := hmem
    simp only [Prod.map, id_eq, Prod.mk.injEq] at heq
    rcases heq with ⟨-, rfl, rfl⟩
    rw [ProbOracleComp.run_interpret_withTranscript_append, PMF.mem_support_map_iff] at hrest
    obtain ⟨⟨rest', final, fresh⟩, hfresh, hrest_eq⟩ := hrest
    cases hrest_eq
    have h1 := hq hfirst
    have h2 := ih hfresh
    simp [h1, h2, Nat.succ_mul, Nat.add_comm]

end ReplicateHelpers

/-- Running `liptonPermanentPlurality k ν A` against a deterministic oracle `O` takes the plurality
of `k` independent runs of `liptonPermanentTrial ν A`. -/
@[simp]
theorem run_liptonPermanentPlurality (k : ℕ) (ν : Fin (n + 1) ↪ F)
    (A : Matrix (Fin n) (Fin n) F) (O : Matrix (Fin n) (Fin n) F → F) :
    (liptonPermanentPlurality k ν A).run (fun M => pure (O M)) =
      plurality 0 <$>
        OracleComp.replicate k ((liptonPermanentTrial ν A).run (fun M => pure (O M))) := by
  rw [liptonPermanentPlurality, ProbOracleComp.run_map, run_replicate]

/-- `liptonPermanentPlurality k ν A` makes at most `k * (n + 1)` oracle queries. -/
theorem isQueryBounded_liptonPermanentPlurality (k : ℕ) (ν : Fin (n + 1) ↪ F)
    (A : Matrix (Fin n) (Fin n) F) :
    (liptonPermanentPlurality k ν A).IsQueryBounded (k * (n + 1)) :=
  (OracleComp.isCostBounded_map_iff _ _ _).mpr
    (isQueryBounded_replicate k (isQueryBounded_liptonPermanentTrial ν A))

/-- Every supported stateful execution of `liptonPermanentPlurality k ν A` makes exactly
`k * (n + 1)` external oracle queries. -/
theorem length_transcript_liptonPermanentPlurality {State : Type}
    (oracle : (M : Matrix (Fin n) (Fin n) F) → StateT State PMF F)
    (k : ℕ) (ν : Fin (n + 1) ↪ F) (A : Matrix (Fin n) (Fin n) F)
    {s s' : State} {result : F} {transcript : OracleComp.Transcript (PermanentOracleSpec n F)}
    (hmem : (result, s', transcript) ∈
      (ProbOracleComp.runWith (OracleComp.withTranscript oracle)
        (liptonPermanentPlurality k ν A) (s, [])).support) :
    transcript.length = k * (n + 1) := by
  simp only [liptonPermanentPlurality, ProbOracleComp.runWith_map, PMF.mem_support_map_iff] at hmem
  obtain ⟨⟨xs, s₂, tr⟩, hxs, heq⟩ := hmem
  simp only [Prod.map, id_eq, Prod.mk.injEq] at heq
  rcases heq with ⟨-, rfl, rfl⟩
  exact length_transcript_replicate oracle k (length_transcript_liptonPermanentTrial oracle ν A) hxs

/-- **General plurality corollary for Lipton's algorithm.** Whenever the single-trial error bound
`((n + 1) * #{M | O M ≠ M.permanent}) / |F|^{n²}` is at most `1 / 2 - γ` (for `0 ≤ γ`), the
`k`-trial plurality algorithm outputs `A.permanent` with probability at least
`1 - 2^{-(2 * γ² * k)}`. -/
theorem liptonPermanentPlurality_prob_toReal_ge_of_margin (k : ℕ) (ν : Fin (n + 1) ↪ F)
    (hν : ∀ i, ν i ≠ 0) (O : Matrix (Fin n) (Fin n) F → F) {γ : ℝ} (hγ : 0 ≤ γ)
    (hmargin : ((n + 1) * #{M | O M ≠ M.permanent} : ℝ) / (Fintype.card F ^ (n * n) : ℝ) ≤
      1 / 2 - γ)
    (A : Matrix (Fin n) (Fin n) F) :
    1 - (2 : ℝ) ^ (-(2 * γ ^ 2 * k)) ≤
      (ProbComp.eval ((liptonPermanentPlurality k ν A).run (fun M => pure (O M)))
        A.permanent).toReal := by
  rw [run_liptonPermanentPlurality]
  refine one_sub_two_rpow_le_eval_plurality_replicate_toReal 0 A.permanent k _ hγ ?_
  linarith [one_sub_le_eval_run_liptonPermanentTrial_toReal ν hν O A]

/-- **Arora–Barak Theorem 8.30 (plurality corollary under `|F|^{n²} / (3 * n)` error):**
for `3 ≤ n` and an oracle `O` with `#{M | O M ≠ M.permanent} ≤ |F|^{n²} / (3 * n)`, the single
trial succeeds with probability at least `1 - (n + 1) / (3 * n) ≥ 5 / 9 = 1 / 2 + 1 / 18`, and the
plurality of `k` independent trials outputs `A.permanent` with probability at least
`1 - 2^{-k / 162}`. -/
theorem liptonPermanentPlurality_prob_toReal_ge (hn : 3 ≤ n) (k : ℕ) (ν : Fin (n + 1) ↪ F)
    (hν : ∀ i, ν i ≠ 0) (O : Matrix (Fin n) (Fin n) F → F)
    (hO : #{M | O M ≠ M.permanent} ≤ Fintype.card F ^ (n * n) / (3 * n))
    (A : Matrix (Fin n) (Fin n) F) :
    1 - (2 : ℝ) ^ (-((k : ℝ) / 162)) ≤
      (ProbComp.eval ((liptonPermanentPlurality k ν A).run (fun M => pure (O M)))
        A.permanent).toReal := by
  have h1 : 1 ≤ n := by omega
  have htrial := liptonPermanentTrial_prob_toReal_ge h1 ν hν O hO A
  have hn_real : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have h3n_pos : (0 : ℝ) < 3 * n := by positivity
  have hfrac : (n + 1 : ℝ) / (3 * n) ≤ 4 / 9 := by
    rw [div_le_iff₀ h3n_pos]
    linarith
  rw [run_liptonPermanentPlurality, show -((k : ℝ) / 162) = -(2 * (1 / 18 : ℝ) ^ 2 * k) by ring]
  refine one_sub_two_rpow_le_eval_plurality_replicate_toReal 0 A.permanent k _ (by norm_num) ?_
  linarith

/-- `ℝ≥0∞`-valued form of `liptonPermanentPlurality_prob_toReal_ge` for `3 ≤ n`. -/
theorem liptonPermanentPlurality_prob_ge (hn : 3 ≤ n) (k : ℕ) (ν : Fin (n + 1) ↪ F)
    (hν : ∀ i, ν i ≠ 0) (O : Matrix (Fin n) (Fin n) F → F)
    (hO : #{M | O M ≠ M.permanent} ≤ Fintype.card F ^ (n * n) / (3 * n))
    (A : Matrix (Fin n) (Fin n) F) :
    ENNReal.ofReal (1 - (2 : ℝ) ^ (-((k : ℝ) / 162))) ≤
      ProbComp.eval ((liptonPermanentPlurality k ν A).run (fun M => pure (O M))) A.permanent := by
  rw [ENNReal.ofReal_le_iff_le_toReal (PMF.apply_ne_top _ _)]
  exact liptonPermanentPlurality_prob_toReal_ge hn k ν hν O hO A

/-- **Plurality corollary for `2 ≤ n` under `|F|^{n²} / (4 * n)` oracle error:**
each trial succeeds with probability at least `1 - (n + 1) / (4 * n) ≥ 5 / 8 = 1 / 2 + 1 / 8`, so
the plurality of `k` independent trials outputs `A.permanent` with probability at least
`1 - 2^{-k / 32}`. -/
theorem liptonPermanentPlurality_prob_toReal_ge_of_four_mul (hn : 2 ≤ n) (k : ℕ)
    (ν : Fin (n + 1) ↪ F) (hν : ∀ i, ν i ≠ 0) (O : Matrix (Fin n) (Fin n) F → F)
    (hO : #{M | O M ≠ M.permanent} ≤ Fintype.card F ^ (n * n) / (4 * n))
    (A : Matrix (Fin n) (Fin n) F) :
    1 - (2 : ℝ) ^ (-((k : ℝ) / 32)) ≤
      (ProbComp.eval ((liptonPermanentPlurality k ν A).run (fun M => pure (O M)))
        A.permanent).toReal := by
  have hmul : (#{M | O M ≠ M.permanent} : ℝ) * (4 * n) ≤ (Fintype.card F : ℝ) ^ (n * n) := by
    exact_mod_cast Nat.mul_le_of_le_div _ _ _ hO
  have hN : (0 : ℝ) < (Fintype.card F : ℝ) ^ (n * n) := by positivity
  have hn_real : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have h4n : (0 : ℝ) < 4 * n := by positivity
  have hdiv : ((n + 1) * #{M | O M ≠ M.permanent} : ℝ) / (Fintype.card F ^ (n * n) : ℝ) ≤
      1 / 2 - 1 / 8 := by
    have h1 : ((n + 1) * #{M | O M ≠ M.permanent} : ℝ) / (Fintype.card F ^ (n * n) : ℝ) ≤
        (n + 1 : ℝ) / (4 * n) := by
      rw [div_le_div_iff₀ hN h4n]
      nlinarith
    have h2 : (n + 1 : ℝ) / (4 * n) ≤ 3 / 8 := by
      rw [div_le_iff₀ h4n]
      linarith
    linarith
  rw [show -((k : ℝ) / 32) = -(2 * (1 / 8 : ℝ) ^ 2 * k) by ring]
  exact liptonPermanentPlurality_prob_toReal_ge_of_margin k ν hν O (by norm_num) hdiv A

/-- **Plurality corollary for all `n` under `|F|^{n²} / (3 * (n + 1))` oracle error:**
each trial succeeds with probability at least `2 / 3 = 1 / 2 + 1 / 6`, so the plurality of `k`
independent trials outputs `A.permanent` with probability at least `1 - 2^{-k / 18}`. -/
theorem liptonPermanentPlurality_prob_toReal_ge_of_three_mul_succ (k : ℕ)
    (ν : Fin (n + 1) ↪ F) (hν : ∀ i, ν i ≠ 0) (O : Matrix (Fin n) (Fin n) F → F)
    (hO : #{M | O M ≠ M.permanent} ≤ Fintype.card F ^ (n * n) / (3 * (n + 1)))
    (A : Matrix (Fin n) (Fin n) F) :
    1 - (2 : ℝ) ^ (-((k : ℝ) / 18)) ≤
      (ProbComp.eval ((liptonPermanentPlurality k ν A).run (fun M => pure (O M)))
        A.permanent).toReal := by
  have hmul : (#{M | O M ≠ M.permanent} : ℝ) * (3 * (n + 1)) ≤ (Fintype.card F : ℝ) ^ (n * n) := by
    exact_mod_cast Nat.mul_le_of_le_div _ _ _ hO
  have hN : (0 : ℝ) < (Fintype.card F : ℝ) ^ (n * n) := by positivity
  have h3n : (0 : ℝ) < 3 * (n + 1) := by positivity
  have hdiv : ((n + 1) * #{M | O M ≠ M.permanent} : ℝ) / (Fintype.card F ^ (n * n) : ℝ) ≤
      1 / 2 - 1 / 6 := by
    have h1 : ((n + 1) * #{M | O M ≠ M.permanent} : ℝ) / (Fintype.card F ^ (n * n) : ℝ) ≤
        (n + 1 : ℝ) / (3 * (n + 1)) := by
      rw [div_le_div_iff₀ hN h3n]
      nlinarith
    have h2 : (n + 1 : ℝ) / (3 * (n + 1)) = 1 / 3 := by
      have hn1 : (n + 1 : ℝ) ≠ 0 := by positivity
      field_simp
    linarith
  rw [show -((k : ℝ) / 18) = -(2 * (1 / 6 : ℝ) ^ 2 * k) by ring]
  exact liptonPermanentPlurality_prob_toReal_ge_of_margin k ν hν O (by norm_num) hdiv A

end Cslib.Complexity
