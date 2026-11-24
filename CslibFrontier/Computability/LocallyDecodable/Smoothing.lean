/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.LocallyDecodable.Basic
import CslibFrontier.Languages.Probabilistic.SampleEach
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Tactic.ENNRealToReal
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Locally decodable codes are smooth

Katz and Trevisan [KatzTrevisan2000, Theorem 1] observed that a local decoder can be made smooth: a
`(q, δ, ε)` local decoder yields a `(q, q / δ, ε)` smooth decoder (restated as [Kerenidis and
de Wolf, Theorem 9][KerenidisDeWolf2004], arXiv:quant-ph/0208062v2, for non-adaptive decoders).
The decoder reads at most `q` positions in expectation, so at most `δ |P|` positions are *heavy*,
read more than `q / (δ |P|)` times in expectation (`Code.card_heavyPositions_le`). The smooth
decoder runs the local decoder but answers the queries to heavy positions itself, from a fixed word
`z`, without reading them (`Code.mask`). Run on the codeword `C x`, it behaves as the local decoder
run on the word that agrees with `z` on the heavy positions and with `C x` elsewhere, which differs
from `C x` on at most `δ |P|` positions, so it still outputs each bit with probability `1 / 2 + ε`;
and it reads no heavy position, while it reads every other position as often as the local decoder,
whose reads do not depend on the word, does against `z`.

For decoders with oblivious reads (`Code.HasObliviousReads`)—which includes every non-adaptive
decoder (`Code.hasObliviousReads_nonadaptive`, `Code.hasObliviousReads_nonadaptivePlan`) and every
one-query decoder (`Code.hasObliviousReads_of_isQueryBounded_one`)—smoothing incurs no loss in
advantage (`Code.isSmoothDecoder_mask_heavyPositions`).

For an arbitrary adaptive `q`-query decoder over a finite nonempty alphabet `Γ`, guessing the
answers to the first `q - 1` queries uniformly at random (aborting to a fair coin flip on any
mismatch, and padding early stops to match the attenuation factor) yields an explicit non-adaptive
query plan (`Code.NonadaptivePlan`, `Code.nonadaptivize`) whose output bias is scaled by exactly
`|Γ| ^ -(q - 1)` (`Code.toReal_decodeLaw_nonadaptivize`) [Yekhanin2012]. Masking its heavy
positions therefore smooths any adaptive `(q, δ, ε)` local decoder into a non-adaptive
`(q, q / δ, ε / |Γ| ^ (q - 1))` smooth decoder (`Code.IsLocalDecoder.isSmoothDecoder_adaptive`,
`Code.IsLocallyDecodable.isSmoothCode`). Smoothness is measured here by expected reads, which bounds
the probability of reading each position.

## Main definitions

* `Cslib.Code.mask`: answer the queries to some positions from a fixed word.
* `Cslib.Code.heavyPositions`: the positions read more often than a threshold.
* `Cslib.Code.NonadaptivePlan`, `Cslib.Code.nonadaptivePlan`: non-adaptive query plans with at most
  `q` optional queries and their execution as a `ProbOracleComp`.
* `Cslib.Code.nonadaptivizePlan`, `Cslib.Code.nonadaptivize`: adaptive-to-non-adaptive reduction
  scaling output bias by `|Γ| ^ -(q - 1)`.

## Main results

* `Cslib.Code.isSmoothDecoder_mask_heavyPositions`: **local decoders with oblivious reads become
  smooth** after masking their heavy positions [KatzTrevisan2000].
* `Cslib.Code.IsLocalDecoder.isSmoothCode`: a locally decodable code with an oblivious-read
  decoder is smooth.
* `Cslib.Code.IsLocalDecoder.isSmoothCode_of_one`: every one-query locally decodable code is
  smooth.
* `Cslib.Code.toReal_decodeLaw_nonadaptivize`: exact output-law attenuation of `nonadaptivize`.
* `Cslib.Code.IsLocalDecoder.nonadaptivize`: every adaptive `(q, δ, ε)` local decoder yields a
  non-adaptive `(q, δ, ε / |Γ| ^ (q - 1))` local decoder.
* `Cslib.Code.isSmoothDecoder_mask_nonadaptivePlan`: masking a non-adaptive local decoder yields a
  non-adaptive smooth decoder with no advantage loss.
* `Cslib.Code.IsLocallyDecodable.isSmoothCode`: **every `(q, δ, ε)` locally decodable code**,
  adaptive or not, is a `(q, q / δ, ε / |Γ| ^ (q - 1))` smooth code.

## References

* [J. Katz, L. Trevisan, *On the efficiency of local decoding procedures for error-correcting
  codes*][KatzTrevisan2000]
* [I. Kerenidis, R. de Wolf, *Exponential lower bound for 2-query locally decodable codes via a
  quantum argument*][KerenidisDeWolf2004], numbering of arXiv:quant-ph/0208062v2
* [S. Yekhanin, *Locally decodable codes*][Yekhanin2012]
-/

public section

open scoped ENNReal

namespace Cslib.Code

open OracleComp ProbOracleComp

variable {ι P Γ α : Type}

section Oblivious

variable [DecidableEq P]

/-- Answer a query to the position `j` from `z` if `j ∈ H`, and query it otherwise. -/
private noncomputable def maskAnswer (H : Finset P) (z : P → Γ) (j : P) :
    ProbOracleComp (fun _ : P => Γ) Γ :=
  if j ∈ H then pure (z j) else ProbOracleComp.query j

/-- Answer a query to a position of `H` from the word `z`, and pass every other call through. -/
private noncomputable def maskHandler (H : Finset P) (z : P → Γ) :
    (q : ℕ ⊕ P) → ProbOracleComp (fun _ : P => Γ) (probOracleSpec (fun _ : P => Γ) q) :=
  sumHandler (fun n => OracleComp.query (spec := probOracleSpec fun _ : P => Γ) (.inl n))
    (maskAnswer H z)

/-- Run `program`, answering its queries to the positions of `H` from the word `z` instead of
querying them. -/
noncomputable def mask (H : Finset P) (z : P → Γ) (program : ProbOracleComp (fun _ : P => Γ) α) :
    ProbOracleComp (fun _ : P => Γ) α :=
  interpret (maskHandler H z) program

/-- The word that agrees with `z` on `H` and with `y` elsewhere. -/
def splice (H : Finset P) (z y : P → Γ) : P → Γ := fun j => if j ∈ H then z j else y j

section Mask

variable (H : Finset P) (z : P → Γ)

/-- Masking makes no more queries. -/
theorem isQueryBounded_mask {program : ProbOracleComp (fun _ : P => Γ) α} {q : ℕ}
    (hq : program.IsQueryBounded q) : (mask H z program).IsQueryBounded q := by
  refine hq.interpret fun q' => ?_
  cases q' with
  | inl n => exact IsCostBounded.query (Sum.inl n)
  | inr j =>
    change IsCostBounded _ (maskAnswer H z j) 1
    rw [maskAnswer]
    split_ifs
    · exact (IsCostBounded.pure _ 0).mono (Nat.zero_le _)
    · exact IsQueryBounded.query j

private theorem evalWith_maskHandler (y : P → Γ) :
    (fun q' => evalWith (wordOracle y) (maskHandler H z q')) = wordOracle (splice H z y) := by
  funext q'
  cases q' with
  | inl n => exact evalWith_query _ _
  | inr j =>
    change evalWith (wordOracle y) (maskAnswer H z j) = PMF.pure (splice H z y j)
    rw [maskAnswer]
    by_cases hj : j ∈ H
    · rw [ite_eq_left hj, evalWith_pure, splice, ite_eq_left hj]
    · rw [ite_eq_right hj, splice, ite_eq_right hj, ← decodeLaw_eq, decodeLaw_query]

private theorem expectedCost_maskHandler (y : P → Γ) (j : P) (q' : ℕ ⊕ P) :
    expectedCost (wordOracle y) (readCost j) (maskHandler H z q') =
      if j ∈ H then 0 else readCost j q' := by
  cases q' with
  | inl n =>
    change expectedCost (wordOracle y) (readCost j) (OracleComp.query (.inl n)) = _
    rw [expectedCost_query, readCost_inl, ite_self]
  | inr j' =>
    change expectedCost (wordOracle y) (readCost j) (maskAnswer H z j') = _
    rw [readCost_inr, maskAnswer]
    by_cases hj' : j' ∈ H
    · rw [ite_eq_left hj', expectedCost_pure]
      by_cases hj : j ∈ H
      · rw [ite_eq_left hj]
      · rw [ite_eq_right hj, ite_eq_right fun h : j' = j => hj (h ▸ hj')]
    · rw [ite_eq_right hj', ProbOracleComp.query, expectedCost_query, readCost_inr]
      by_cases hj : j ∈ H
      · rw [ite_eq_left hj, ite_eq_right fun h : j' = j => hj' (h ▸ hj)]
      · rw [ite_eq_right hj]

/-- The masked program run against `y` is the program run against `y` spliced with `z` on `H`. -/
theorem decodeLaw_mask (program : ProbOracleComp (fun _ : P => Γ) α) (y : P → Γ) :
    decodeLaw (mask H z program) y = decodeLaw program (splice H z y) := by
  rw [decodeLaw_eq, decodeLaw_eq, mask, evalWith_interpret, evalWith_maskHandler]

/-- The masked program reads no position of `H`, and reads every other position as often as the
program run against the spliced word. -/
theorem expectedReads_mask (program : ProbOracleComp (fun _ : P => Γ) α) (y : P → Γ) (j : P) :
    expectedReads (mask H z program) y j =
      if j ∈ H then 0 else expectedReads program (splice H z y) j := by
  rw [expectedReads_eq, mask, expectedCost_interpret, evalWith_maskHandler]
  by_cases hj : j ∈ H
  · have hcost : (fun q' => expectedCost (wordOracle y) (readCost j) (maskHandler H z q')) = 0 := by
      funext q'
      rw [expectedCost_maskHandler, ite_eq_left hj, Pi.zero_apply]
    rw [hcost, expectedCost_zero, ite_eq_left hj]
  · have hcost : (fun q' => expectedCost (wordOracle y) (readCost j) (maskHandler H z q')) =
        readCost j := by
      funext q'
      rw [expectedCost_maskHandler, ite_eq_right hj]
    rw [hcost, ite_eq_right hj, expectedReads_eq]

/-- The spliced word differs from `y` only on `H`. -/
theorem hammingDist_splice_le [Fintype P] [DecidableEq Γ] (y : P → Γ) :
    hammingDist (splice H z y) y ≤ H.card := by
  refine Finset.card_le_card fun j hj => ?_
  rw [Finset.mem_filter] at hj
  by_contra hjH
  exact hj.2 (by rw [splice, ite_eq_right hjH])

end Mask

/-! ### Heavy positions -/

section Heavy

variable [Fintype P]

/-- The positions that `program`, run against `z`, reads more than `c / |P|` times in
expectation. -/
noncomputable def heavyPositions (program : ProbOracleComp (fun _ : P => Γ) α) (z : P → Γ)
    (c : ℝ) : Finset P :=
  {j | c / (Fintype.card P : ℝ) < (expectedReads program z j).toReal}

/-- **Few positions are heavy**: a program making at most `q` queries reads more than
`q / (δ |P|)` times in expectation at most `δ |P|` positions. -/
theorem card_heavyPositions_le {program : ProbOracleComp (fun _ : P => Γ) α} {q : ℕ}
    (hq : program.IsQueryBounded q) (z : P → Γ) {δ : ℝ} (hδ : 0 < δ) :
    ((heavyPositions program z (q / δ)).card : ℝ) ≤ δ * Fintype.card P := by
  set H := heavyPositions program z (q / δ)
  have hHn : (H.card : ℝ) ≤ Fintype.card P := by exact_mod_cast Finset.card_le_univ H
  set n : ℝ := (Fintype.card P : ℝ)
  set w : P → ℝ := fun j => (expectedReads program z j).toReal
  have hsum : ∑ j, w j ≤ q := by
    -- `ennreal_to_real` finds the summands finite by `hfin`.
    have hfin := expectedReads_ne_top hq z
    ennreal_to_real using sum_expectedReads_le hq z
  have hsumH : ∑ j ∈ H, w j ≤ q :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ H)
      fun _ _ _ => ENNReal.toReal_nonneg).trans hsum
  by_contra hcon
  rw [not_le] at hcon
  have hn : 0 < n := by nlinarith
  have hne : H.Nonempty := by
    rw [← Finset.card_pos]
    exact_mod_cast (mul_nonneg hδ.le hn.le).trans_lt hcon
  have hlt : ∑ _j ∈ H, (q / δ / n) < ∑ j ∈ H, w j :=
    Finset.sum_lt_sum_of_nonempty hne fun j hj => (Finset.mem_filter.mp hj).2
  rw [Finset.sum_const, nsmul_eq_mul] at hlt
  have hq0 : (0 : ℝ) < q := by
    have : (0 : ℝ) ≤ q / δ / n := div_nonneg (div_nonneg (Nat.cast_nonneg _) hδ.le) hn.le
    nlinarith
  have : (q : ℝ) ≤ H.card * (q / δ / n) := by
    rw [show (H.card : ℝ) * (q / δ / n) = q * (H.card / (δ * n)) by field_simp]
    have : 1 ≤ (H.card : ℝ) / (δ * n) := by
      rw [le_div_iff₀ (mul_pos hδ hn)]
      linarith
    nlinarith
  linarith

end Heavy

/-! ### Smoothing -/

section Smoothing

variable [Fintype P] [DecidableEq Γ]

/-- **Katz–Trevisan smoothing** [KatzTrevisan2000, Theorem 1], as restated in [Kerenidis and
de Wolf, Theorem 9][KerenidisDeWolf2004] (arXiv:quant-ph/0208062v2): a `(q, δ, ε)` local decoder
whose reads do not depend on the received word becomes a `(q, q / δ, ε)` smooth decoder when the
queries to its heavy positions are answered from a fixed word `z` instead.

Source mapping. The source states that every `(q, δ, ε)` locally decodable code is a
`(q, q / δ, ε)` smooth code, for non-adaptive decoders (Definitions 1 and 3 there), with smoothness
bounding the probability of querying each position. Here the hypothesis is that the reads are
oblivious (`HasObliviousReads`), which holds for every non-adaptive decoder
(`hasObliviousReads_nonadaptive`) and for every one-query decoder, adaptive or not
(`hasObliviousReads_of_isQueryBounded_one`); general adaptive decoders are not covered. The
conclusion bounds expected reads, which is at least as strong as the source's read-probability
bound. -/
theorem isSmoothDecoder_mask_heavyPositions {C : (ι → Bool) → P → Γ} {q : ℕ} {δ ε : ℝ}
    {A : LocalDecoder ι P Γ} (hA : IsLocalDecoder C q δ ε A) (hobl : ∀ i, HasObliviousReads (A i))
    (hδ : 0 < δ) (z : P → Γ) :
    IsSmoothDecoder C q (q / δ) ε fun i => mask (heavyPositions (A i) z (q / δ)) z (A i) where
  isQueryBounded i := isQueryBounded_mask _ _ (hA.isQueryBounded i)
  correct x i := by
    rw [decodeLaw_mask]
    refine hA.correct x _ i ?_
    exact (Nat.cast_le.mpr (hammingDist_splice_le _ z (C x))).trans
      (card_heavyPositions_le (hA.isQueryBounded i) z hδ)
  smooth x i j := by
    rw [expectedReads_mask]
    split_ifs with hj
    · rw [ENNReal.toReal_zero]
      exact div_nonneg (div_nonneg (Nat.cast_nonneg _) hδ.le) (Nat.cast_nonneg _)
    · rw [(hobl i).expectedReads_eq _ z]
      simpa [heavyPositions] using hj

/-- A locally decodable code with an oblivious-read decoder is smooth. -/
theorem IsLocalDecoder.isSmoothCode {C : (ι → Bool) → P → Γ} {q : ℕ} {δ ε : ℝ}
    {A : LocalDecoder ι P Γ} (hA : IsLocalDecoder C q δ ε A) (hobl : ∀ i, HasObliviousReads (A i))
    (hδ : 0 < δ) : IsSmoothCode C q (q / δ) ε :=
  (isSmoothDecoder_mask_heavyPositions hA hobl hδ (C fun _ => false)).isSmoothCode

end Smoothing

/-! ### Decoders making one query -/

section OneQuery

/-- A program making no query reads no position. -/
theorem expectedReads_eq_zero_of_isQueryBounded_zero {program : ProbOracleComp (fun _ : P => Γ) α}
    (hq : program.IsQueryBounded 0) (y : P → Γ) (j : P) : expectedReads program y j = 0 := by
  rw [expectedReads_eq]
  exact expectedCost_eq_zero_of_isCostBounded _ _ hq fun q' hq' => by
    cases q' with
    | inl n => exact readCost_inl j n
    | inr j' => simp at hq'

omit [DecidableEq P] in
/-- A program making no query has the same output law against every word. -/
theorem decodeLaw_eq_of_isQueryBounded_zero {program : ProbOracleComp (fun _ : P => Γ) α}
    (hq : program.IsQueryBounded 0) (y y' : P → Γ) :
    decodeLaw program y = decodeLaw program y' := by
  induction program using OracleComp.induction with
  | pure a => rw [decodeLaw_pure, decodeLaw_pure]
  | query_bind q' cont ih =>
    rw [PFunctor.FreeM.bind_eq_bind]
    obtain ⟨hle, hcont⟩ := IsCostBounded.liftBind_iff.mp hq
    cases q' with
    | inl n =>
      rw [decodeLaw_bind, decodeLaw_bind, decodeLaw_query_inl, decodeLaw_query_inl]
      exact congrArg _ (funext fun a => ih a ((hcont a).mono (by omega)))
    | inr j => simp at hle

/-- **A decoder making one query has oblivious reads**: the position it reads is chosen before it
reads anything. -/
theorem hasObliviousReads_of_isQueryBounded_one {program : ProbOracleComp (fun _ : P => Γ) α}
    (hq : program.IsQueryBounded 1) : HasObliviousReads program := by
  refine hasObliviousReads_iff.mpr fun y y' j => ?_
  suffices h : ∀ n ≤ 1, program.IsQueryBounded n →
      expectedReads program y j = expectedReads program y' j from h 1 le_rfl hq
  clear hq
  intro n hn hqn
  induction program using OracleComp.induction generalizing n with
  | pure a => rw [expectedReads_pure, expectedReads_pure]
  | query_bind q' cont ih =>
    rw [PFunctor.FreeM.bind_eq_bind]
    obtain ⟨hle, hcont⟩ := IsCostBounded.liftBind_iff.mp hqn
    rw [expectedReads_query_bind, expectedReads_query_bind]
    cases q' with
    | inl m =>
      congr 1
      exact tsum_congr fun a => congrArg _ (ih a n hn ((hcont a).mono (by simp)))
    | inr j' =>
      have h0 (a : Γ) : ProbOracleComp.IsQueryBounded (cont a) 0 := by
        have h := (hcont a).mono (m := 0) (by simp only [Sum.elim_inr] at hle ⊢; omega)
        exact h
      simp only [expectedReads_eq_zero_of_isQueryBounded_zero (h0 _), mul_zero]

end OneQuery

section Smoothing

variable [Fintype P] [DecidableEq Γ]

/-- **One-query locally decodable codes are smooth**, the case `q = 1` of
[KatzTrevisan2000, Theorem 1] (see `isSmoothDecoder_mask_heavyPositions`): a `(1, δ, ε)` local
decoder, adaptive or not, yields a `(1, 1 / δ, ε)` smooth decoder. -/
theorem IsLocalDecoder.isSmoothCode_of_one {C : (ι → Bool) → P → Γ} {δ ε : ℝ}
    {A : LocalDecoder ι P Γ} (hA : IsLocalDecoder C 1 δ ε A) (hδ : 0 < δ) :
    IsSmoothCode C 1 (1 / δ) ε := by
  simpa using hA.isSmoothCode (fun i => hasObliviousReads_of_isQueryBounded_one
    (hA.isQueryBounded i)) hδ

end Smoothing

end Oblivious

/-! ### Non-adaptive query plans -/

/-- A deterministic non-adaptive query plan making at most `q` queries: slot `k` queries `j` when
`queries k = some j` and is skipped when `queries k = none`, and `decide` computes the output bit
from the symbols read. -/
structure NonadaptivePlan (P Γ : Type) (q : ℕ) where
  /-- Position queried in each of the `q` slots, or `none` to skip the slot. -/
  queries : Fin q → Option P
  /-- Deterministic decision rule applied to the symbols read. -/
  decide : (Fin q → Option Γ) → Bool

namespace NonadaptivePlan

variable {q : ℕ}

instance [Finite P] [Finite Γ] : Finite (NonadaptivePlan P Γ q) := by
  refine Finite.of_injective (fun plan => (plan.queries, plan.decide)) fun a b h => ?_
  cases a
  cases b
  simp only [Prod.mk.injEq] at h
  rw [h.1, h.2]

/-- Evaluate a non-adaptive query plan against a received word `y`. -/
def eval (plan : NonadaptivePlan P Γ q) (y : P → Γ) : Bool :=
  plan.decide fun k => (plan.queries k).map y

/-- The set of positions queried by a non-adaptive query plan. -/
def querySet [DecidableEq P] (plan : NonadaptivePlan P Γ q) : Finset P :=
  Finset.univ.biUnion fun k => (plan.queries k).toFinset

theorem mem_querySet_iff [DecidableEq P] (plan : NonadaptivePlan P Γ q) (j : P) :
    j ∈ plan.querySet ↔ ∃ k, plan.queries k = some j := by
  simp [querySet]

theorem card_querySet_le [DecidableEq P] (plan : NonadaptivePlan P Γ q) :
    plan.querySet.card ≤ q := by
  calc
    plan.querySet.card ≤ ∑ k : Fin q, (plan.queries k).toFinset.card := Finset.card_biUnion_le
    _ ≤ ∑ _k : Fin q, 1 := Finset.sum_le_sum fun k _ => by cases plan.queries k <;> simp
    _ = q := by simp

/-- The output of a non-adaptive plan depends only on the received word on its query set. -/
theorem eval_eq_of_eqOn [DecidableEq P] (plan : NonadaptivePlan P Γ q) {y y' : P → Γ}
    (h : ∀ j ∈ plan.querySet, y j = y' j) : plan.eval y = plan.eval y' := by
  simp only [eval]
  congr 1
  funext k
  cases hk : plan.queries k with
  | none => rfl
  | some j =>
    simp only [Option.map_some]
    exact congrArg some (h j ((mem_querySet_iff plan j).mpr ⟨k, hk⟩))

/-- Evaluate a non-adaptive plan given only the symbols on its query set. -/
def restrictEval [DecidableEq P] (plan : NonadaptivePlan P Γ q) (w : plan.querySet → Γ) : Bool :=
  plan.decide fun k =>
    match hk : plan.queries k with
    | none => none
    | some j => some (w ⟨j, (mem_querySet_iff plan j).mpr ⟨k, hk⟩⟩)

theorem restrictEval_restrict [DecidableEq P] (plan : NonadaptivePlan P Γ q) (y : P → Γ) :
    plan.restrictEval (plan.querySet.restrict y) = plan.eval y := by
  simp only [restrictEval, eval]
  congr 1
  funext k
  split <;> simp_all [Finset.restrict]

/-- Mask the positions in `H` using the fixed word `z`: queries to `H` are skipped and answered
directly from `z`. -/
def mask [DecidableEq P] (H : Finset P) (z : P → Γ) (plan : NonadaptivePlan P Γ q) :
    NonadaptivePlan P Γ q where
  queries k := match plan.queries k with
    | none => none
    | some j => if j ∈ H then none else some j
  decide vals := plan.decide fun k => match plan.queries k with
    | none => none
    | some j => if j ∈ H then some (z j) else vals k

theorem eval_mask [DecidableEq P] (H : Finset P) (z : P → Γ) (plan : NonadaptivePlan P Γ q)
    (y : P → Γ) : (plan.mask H z).eval y = plan.eval (splice H z y) := by
  simp only [eval, mask]
  congr 1
  funext k
  cases hk : plan.queries k with
  | none => rfl
  | some j =>
    by_cases hj : j ∈ H <;> simp [splice, hj]

theorem querySet_mask [DecidableEq P] (H : Finset P) (z : P → Γ) (plan : NonadaptivePlan P Γ q) :
    (plan.mask H z).querySet = plan.querySet \ H := by
  ext j
  simp only [mem_querySet_iff, Finset.mem_sdiff, mask]
  constructor
  · rintro ⟨k, hk⟩
    cases hqk : plan.queries k with
    | none => simp [hqk] at hk
    | some j' =>
      by_cases hj' : j' ∈ H
      · simp [hqk, hj'] at hk
      · simp only [hqk, hj', ↓reduceIte, Option.some.injEq] at hk
        subst hk
        exact ⟨⟨k, hqk⟩, hj'⟩
  · rintro ⟨⟨k, hqk⟩, hj⟩
    exact ⟨k, by simp [hqk, hj]⟩

/-- Convert a fixed-tuple non-adaptive decision `(Q, output)` into a `NonadaptivePlan`. -/
noncomputable def ofTuple [Nonempty Γ] (Q : Fin q → P) (output : (Fin q → Γ) → Bool) :
    NonadaptivePlan P Γ q where
  queries k := some (Q k)
  decide vals := output fun k => (vals k).getD (Classical.arbitrary Γ)

theorem eval_ofTuple [Nonempty Γ] (Q : Fin q → P) (output : (Fin q → Γ) → Bool) (y : P → Γ) :
    (ofTuple Q output).eval y = output (y ∘ Q) := by
  rw [eval, ofTuple]
  rfl

end NonadaptivePlan

section NonadaptivePlanProg

variable {q : ℕ}

/-- Query a single optional position: `none` makes no query. -/
private def readOption (o : Option P) : ProbOracleComp (fun _ : P => Γ) (Option Γ) :=
  match o with
  | none => pure none
  | some j => some <$> ProbOracleComp.query j

/-- Query `q` optional positions in order, returning the optional symbols read. -/
private def readAllOption :
    {q : ℕ} → (Fin q → Option P) → ProbOracleComp (fun _ : P => Γ) (Fin q → Option Γ)
  | 0, _ => pure Fin.elim0
  | _ + 1, Q => do
    let a ← readOption (Q 0)
    let rest ← readAllOption (Fin.tail Q)
    pure (Fin.cons a rest)

/-- Run a distribution over non-adaptive query plans as a local-decoder program. -/
def nonadaptivePlan (planLaw : ProbComp (NonadaptivePlan P Γ q)) :
    ProbOracleComp (fun _ : P => Γ) Bool := do
  let plan ← sample planLaw
  let answers ← readAllOption plan.queries
  pure (plan.decide answers)

private theorem isQueryBounded_readOption (o : Option P) :
    (readOption (Γ := Γ) o).IsQueryBounded 1 := by
  cases o with
  | none => exact (IsCostBounded.pure _ 0).mono (Nat.zero_le _)
  | some j =>
    change IsCostBounded _ (ProbOracleComp.query j >>= fun a => pure (some a)) 1
    exact ((IsQueryBounded.query j).bind fun _ => .pure _ 0).mono (by omega)

private theorem isQueryBounded_readAllOption (Q : Fin q → Option P) :
    (readAllOption (Γ := Γ) Q).IsQueryBounded q := by
  induction q with
  | zero => exact .pure _ 0
  | succ q ih =>
    simp only [readAllOption]
    exact ((isQueryBounded_readOption (Q 0)).bind fun _ =>
      (ih (Fin.tail Q)).bind fun _ => .pure _ 0).mono (by omega)

theorem isQueryBounded_nonadaptivePlan (planLaw : ProbComp (NonadaptivePlan P Γ q)) :
    (nonadaptivePlan planLaw).IsQueryBounded q := by
  have h := (IsQueryBounded.sample (spec := fun _ : P => Γ) planLaw).bind fun plan =>
    (isQueryBounded_readAllOption (Γ := Γ) plan.queries).bind fun answers =>
      .pure (plan.decide answers) 0
  rw [Nat.zero_add, Nat.add_zero] at h
  exact h

private theorem decodeLaw_readOption (o : Option P) (y : P → Γ) :
    decodeLaw (readOption o) y = PMF.pure (o.map y) := by
  cases o with
  | none => simp [readOption]
  | some j => simp [readOption]

private theorem decodeLaw_readAllOption (Q : Fin q → Option P) (y : P → Γ) :
    decodeLaw (readAllOption Q) y = PMF.pure (fun k => (Q k).map y) := by
  induction q with
  | zero =>
    rw [readAllOption, decodeLaw_pure]
    congr 1 with k : 1
    exact k.elim0
  | succ q ih =>
    simp only [readAllOption, decodeLaw_bind, decodeLaw_readOption, PMF.pure_bind, ih,
      decodeLaw_pure]
    congr 1
    exact Fin.cons_self_tail fun k => (Q k).map y

theorem decodeLaw_nonadaptivePlan (planLaw : ProbComp (NonadaptivePlan P Γ q)) (y : P → Γ) :
    decodeLaw (nonadaptivePlan planLaw) y =
      (ProbComp.eval planLaw).map fun plan => plan.eval y := by
  simp only [nonadaptivePlan, decodeLaw_bind, decodeLaw_sample, decodeLaw_readAllOption,
    PMF.pure_bind, decodeLaw_pure]
  rfl

private theorem expectedReads_readOption [DecidableEq P] (o : Option P) (y : P → Γ) (j : P) :
    expectedReads (readOption (Γ := Γ) o) y j = if o = some j then 1 else 0 := by
  cases o with
  | none => simp [readOption]
  | some j' =>
    rw [readOption, expectedReads_eq, expectedCost_map, ← expectedReads_eq, expectedReads_query]
    simp

private theorem expectedReads_readAllOption [DecidableEq P] (Q : Fin q → Option P) (y : P → Γ)
    (j : P) :
    expectedReads (readAllOption (Γ := Γ) Q) y j = ∑ k, if Q k = some j then 1 else 0 := by
  induction q with
  | zero => simp [readAllOption]
  | succ q ih =>
    simp only [readAllOption, expectedReads_bind, expectedReads_readOption, expectedReads_pure,
      add_zero, mul_zero, tsum_zero, ih, decodeLaw_readOption, decodeLaw_readAllOption]
    rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul, Fin.sum_univ_succ]
    rfl

theorem expectedReads_nonadaptivePlan [DecidableEq P] (planLaw : ProbComp (NonadaptivePlan P Γ q))
    (y : P → Γ) (j : P) :
    expectedReads (nonadaptivePlan planLaw) y j =
      ∑' plan, ProbComp.eval planLaw plan * ∑ k, if plan.queries k = some j then 1 else 0 := by
  simp only [nonadaptivePlan, expectedReads_bind, expectedReads_sample, zero_add, decodeLaw_sample,
    expectedReads_readAllOption, expectedReads_pure, mul_zero, tsum_zero, add_zero]

theorem hasObliviousReads_nonadaptivePlan [DecidableEq P]
    (planLaw : ProbComp (NonadaptivePlan P Γ q)) :
    HasObliviousReads (nonadaptivePlan planLaw) :=
  hasObliviousReads_iff.mpr fun _ _ _ => by
    rw [expectedReads_nonadaptivePlan, expectedReads_nonadaptivePlan]

theorem decodeLaw_nonadaptivePlan_mask [DecidableEq P] (H : Finset P) (z : P → Γ)
    (planLaw : ProbComp (NonadaptivePlan P Γ q)) (y : P → Γ) :
    decodeLaw (nonadaptivePlan (NonadaptivePlan.mask H z <$> planLaw)) y =
      decodeLaw (nonadaptivePlan planLaw) (splice H z y) := by
  rw [decodeLaw_nonadaptivePlan, decodeLaw_nonadaptivePlan, ProbComp.eval_map, PMF.map_comp]
  congr 1 with plan
  exact NonadaptivePlan.eval_mask H z plan y

theorem expectedReads_nonadaptivePlan_mask [DecidableEq P] (H : Finset P) (z : P → Γ)
    (planLaw : ProbComp (NonadaptivePlan P Γ q)) (y : P → Γ) (j : P) :
    expectedReads (nonadaptivePlan (NonadaptivePlan.mask H z <$> planLaw)) y j =
      if j ∈ H then 0 else expectedReads (nonadaptivePlan planLaw) y j := by
  rw [expectedReads_nonadaptivePlan, expectedReads_nonadaptivePlan, ProbComp.eval_map,
    Probability.PMF.tsum_map_mul]
  have hqmask (plan : NonadaptivePlan P Γ q) (k : Fin q) :
      ((plan.mask H z).queries k = some j) ↔ (j ∉ H ∧ plan.queries k = some j) := by
    simp only [NonadaptivePlan.mask]
    cases plan.queries k with
    | none => simp
    | some j' =>
      by_cases hj' : j' ∈ H
      · simp only [hj', ↓reduceIte, reduceCtorEq, Option.some.injEq, false_iff, not_and]
        rintro hj rfl
        exact hj hj'
      · simp only [hj', ↓reduceIte, Option.some.injEq, iff_and_self]
        rintro rfl
        exact hj'
  by_cases hj : j ∈ H
  · rw [ite_eq_left hj]
    refine (tsum_congr fun plan => ?_).trans tsum_zero
    have hzero : (∑ k, if (plan.mask H z).queries k = some j then (1 : ℝ≥0∞) else 0) = 0 :=
      Finset.sum_eq_zero fun k _ => by simp [hqmask plan k, hj]
    rw [hzero, mul_zero]
  · rw [ite_eq_right hj]
    refine tsum_congr fun plan => congrArg _ (Finset.sum_congr rfl fun k _ => ?_)
    simp [hqmask plan k, hj]

/-- Convert a `Code.nonadaptive` decoder into an equivalent `NonadaptivePlan` sampler. -/
noncomputable def nonadaptivePlanOf {R : Type} [Nonempty Γ] (coins : ProbComp R)
    (Q : R → Fin q → P) (output : R → (Fin q → Γ) → Bool) : ProbComp (NonadaptivePlan P Γ q) :=
  (fun r => NonadaptivePlan.ofTuple (Q r) (output r)) <$> coins

theorem decodeLaw_nonadaptivePlanOf {R : Type} [Nonempty Γ] (coins : ProbComp R)
    (Q : R → Fin q → P) (output : R → (Fin q → Γ) → Bool) (y : P → Γ) :
    decodeLaw (nonadaptivePlan (nonadaptivePlanOf coins Q output)) y =
      decodeLaw (nonadaptive coins Q output) y := by
  rw [decodeLaw_nonadaptivePlan, decodeLaw_nonadaptive, nonadaptivePlanOf, ProbComp.eval_map,
    PMF.map_comp]
  rfl

theorem expectedReads_nonadaptivePlanOf [DecidableEq P] {R : Type} [Nonempty Γ] (coins : ProbComp R)
    (Q : R → Fin q → P) (output : R → (Fin q → Γ) → Bool) (y : P → Γ) (j : P) :
    expectedReads (nonadaptivePlan (nonadaptivePlanOf coins Q output)) y j =
      expectedReads (nonadaptive coins Q output) y j := by
  rw [expectedReads_nonadaptivePlan, expectedReads_nonadaptive, nonadaptivePlanOf,
    ProbComp.eval_map, Probability.PMF.tsum_map_mul]
  refine tsum_congr fun r => congrArg _ (Finset.sum_congr rfl fun k _ => ?_)
  simp [NonadaptivePlan.ofTuple]

end NonadaptivePlanProg

/-! ### Adaptive-to-non-adaptive reduction and general smoothing -/

section Adaptive

open Probability

/-- Strip unreachable external query branches from a zero-query program to obtain a closed
probabilistic computation. -/
private def stripQueries {α : Type} :
    (prog : ProbOracleComp (fun _ : P => Γ) α) → prog.IsQueryBounded 0 → ProbComp α
  | .pure a, _ => pure a
  | .liftBind (.inl k) cont, hq => do
    let c ← ProbComp.unifFin k
    stripQueries (cont c) ((IsCostBounded.liftBind_iff.mp hq).2 c)
  | .liftBind (.inr _) _, hq =>
    False.elim (by have h := (IsCostBounded.liftBind_iff.mp hq).1; simp at h)

private theorem eval_stripQueries {α : Type} (prog : ProbOracleComp (fun _ : P => Γ) α)
    (hq : prog.IsQueryBounded 0) (y : P → Γ) :
    ProbComp.eval (stripQueries prog hq) = decodeLaw prog y := by
  induction prog with
  | pure a =>
    change ProbComp.eval (pure a) = decodeLaw (pure a) y
    rw [ProbComp.eval_pure, decodeLaw_pure]
  | liftBind q' cont ih =>
    cases q' with
    | inl k =>
      change ProbComp.eval (ProbComp.unifFin k >>= fun c => stripQueries (cont c) _) =
        decodeLaw (OracleComp.query (.inl k) >>= cont) y
      rw [ProbComp.eval_bind, ProbComp.eval_unifFin, decodeLaw_bind, decodeLaw_query_inl]
      change (ProbComp.unifOracle k).bind _ = (ProbComp.unifOracle k).bind _
      congr 1
      funext c
      exact ih c _
    | inr j =>
      have h := (IsCostBounded.liftBind_iff.mp hq).1
      simp at h

/-- Output `b` with probability `|Γ| ^ (-k)` and a uniform bit otherwise. -/
private noncomputable def attenuate [Fintype Γ] [Nonempty Γ] [DecidableEq Γ]
    (k : ℕ) (b : Bool) : ProbComp Bool := do
  let gs ← ProbComp.uniform (Fin k → Γ)
  let u ← ProbComp.uniform Bool
  pure (if ∀ t, gs t = Classical.arbitrary Γ then b else u)

private theorem toReal_eval_attenuate [Fintype Γ] [Nonempty Γ] [DecidableEq Γ]
    (k : ℕ) (b b' : Bool) :
    (ProbComp.eval (attenuate (Γ := Γ) k b) b').toReal =
      1 / 2 + ((if b = b' then (1 : ℝ) else 0) - 1 / 2) / (Fintype.card Γ : ℝ) ^ k := by
  set γ₀ : Γ := Classical.arbitrary Γ
  set g₀ : Fin k → Γ := fun _ => γ₀
  have hcard : (Fintype.card (Fin k → Γ) : ℝ) = (Fintype.card Γ : ℝ) ^ k := by simp
  have hpos : (0 : ℝ) < (Fintype.card Γ : ℝ) ^ k := by positivity
  have heval : ProbComp.eval (attenuate (Γ := Γ) k b) =
      (PMF.uniformOfFintype (Fin k → Γ)).bind fun gs =>
        (PMF.uniformOfFintype Bool).map fun u => if ∀ t, gs t = γ₀ then b else u := by
    simp only [attenuate, ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_pure]
    rfl
  rw [heval, Probability.PMF.toReal_uniformOfFintype_bind_apply, Finset.expect_eq_sum_div_card,
    Finset.card_univ, hcard]
  have hterm (gs : Fin k → Γ) :
      (((PMF.uniformOfFintype Bool).map fun u => if ∀ t, gs t = γ₀ then b else u) b').toReal =
        if gs = g₀ then (if b = b' then (1 : ℝ) else 0) else 1 / 2 := by
    by_cases hgs : gs = g₀
    · subst hgs
      have hfun : (fun u : Bool => if ∀ t : Fin k, g₀ t = γ₀ then b else u) = fun _ => b :=
        funext fun _ => ite_eq_left fun _ => rfl
      have hconst : (PMF.uniformOfFintype Bool).map (fun _ : Bool => b) = PMF.pure b :=
        PMF.map_const (PMF.uniformOfFintype Bool) b
      rw [ite_eq_left rfl, hfun, hconst]
      by_cases hbb : b = b'
      · subst hbb; simp
      · simp [hbb, Ne.symm hbb]
    · have hnot : ¬ ∀ t : Fin k, gs t = γ₀ := fun h => hgs (funext h)
      simp only [hnot, hgs, ↓reduceIte]
      have hid : (PMF.uniformOfFintype Bool).map (fun u : Bool => u) =
          PMF.uniformOfFintype Bool := PMF.map_id _
      rw [hid, PMF.uniformOfFintype_apply]
      norm_num
  simp_rw [hterm]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ g₀), ite_eq_left rfl]
  have hrest : ∑ gs ∈ Finset.univ.erase g₀,
      (if gs = g₀ then (if b = b' then (1 : ℝ) else 0) else 1 / 2) =
        ((Fintype.card Γ : ℝ) ^ k - 1) * (1 / 2) := by
    rw [Finset.sum_congr rfl fun gs hgs => ite_eq_right (Finset.ne_of_mem_erase hgs)]
    rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ g₀), Finset.card_univ,
      nsmul_eq_mul]
    have h1 : 1 ≤ Fintype.card (Fin k → Γ) := Fintype.card_pos
    rw [Nat.cast_sub h1, Nat.cast_one, hcard]
  rw [hrest]
  field_simp [hpos.ne']
  ring

/-- Convert any `q`-query adaptive decoder program into a non-adaptive query-plan sampler by
guessing the answers to the first `q - 1` queries uniformly at random, outputting a fair coin on
any mismatch, and matching the attenuation factor on early stops [Yekhanin2012]. -/
noncomputable def nonadaptivizePlan [Fintype Γ] [Nonempty Γ] [DecidableEq Γ] :
    (q : ℕ) → (prog : ProbOracleComp (fun _ : P => Γ) Bool) → prog.IsQueryBounded q →
      ProbComp (NonadaptivePlan P Γ q)
  | 0, prog, hq => do
    let b ← stripQueries prog hq
    pure ⟨Fin.elim0, fun _ => b⟩
  | 1, .pure b, _ =>
    pure ⟨fun _ => none, fun _ => b⟩
  | 1, .liftBind (.inl k) cont, hq => do
    let c ← ProbComp.unifFin k
    nonadaptivizePlan 1 (cont c) ((IsCostBounded.liftBind_iff.mp hq).2 c)
  | 1, .liftBind (.inr j) cont, hq => do
    let f ← ProbComp.sampleEach fun a =>
      stripQueries (cont a) ((IsCostBounded.liftBind_iff.mp hq).2 a)
    pure ⟨fun _ => some j, fun vals => match vals 0 with | some σ => f σ | none => false⟩
  | q + 2, .pure b, _ => do
    let out ← attenuate (Γ := Γ) (q + 1) b
    pure ⟨fun _ => none, fun _ => out⟩
  | q + 2, .liftBind (.inl k) cont, hq => do
    let c ← ProbComp.unifFin k
    nonadaptivizePlan (q + 2) (cont c) ((IsCostBounded.liftBind_iff.mp hq).2 c)
  | q + 2, .liftBind (.inr j) cont, hq => do
    let guess ← ProbComp.uniform Γ
    let u ← ProbComp.uniform Bool
    let rest ← nonadaptivizePlan (q + 1) (cont guess)
      ((IsCostBounded.liftBind_iff.mp hq).2 guess)
    pure ⟨Fin.cons (some j) rest.queries,
      fun vals => if vals 0 = some guess then rest.decide (Fin.tail vals) else u⟩

/-- The non-adaptive decoder program obtained from an adaptive `q`-query program by guessing the
first `q - 1` answers. -/
@[expose] noncomputable def nonadaptivize [Fintype Γ] [Nonempty Γ] [DecidableEq Γ] (q : ℕ)
    (prog : ProbOracleComp (fun _ : P => Γ) Bool) (hq : prog.IsQueryBounded q) :
    ProbOracleComp (fun _ : P => Γ) Bool :=
  nonadaptivePlan (nonadaptivizePlan q prog hq)

/-- **Exact output law of the adaptive-to-non-adaptive reduction**: `nonadaptivize` scales the
deviation of every output probability from `1 / 2` by `|Γ| ^ -(q - 1)`. In particular, `q ≤ 1`
incurs no loss. -/
theorem toReal_decodeLaw_nonadaptivize [Fintype Γ] [Nonempty Γ] [DecidableEq Γ]
    {q : ℕ} {prog : ProbOracleComp (fun _ : P => Γ) Bool} (hq : prog.IsQueryBounded q)
    (y : P → Γ) (b : Bool) :
    (decodeLaw (nonadaptivize q prog hq) y b).toReal =
      1 / 2 + ((decodeLaw prog y b).toReal - 1 / 2) / (Fintype.card Γ : ℝ) ^ (q - 1) := by
  induction prog generalizing q with
  | pure b₀ =>
    have hpure : decodeLaw (PFunctor.FreeM.pure b₀ : ProbOracleComp (fun _ : P => Γ) Bool) y =
        PMF.pure b₀ := decodeLaw_pure y b₀
    cases q with
    | zero =>
      simp only [nonadaptivize, decodeLaw_nonadaptivePlan, nonadaptivizePlan, stripQueries,
        ProbComp.eval_bind, ProbComp.eval_pure, PMF.pure_bind, PMF.pure_map, NonadaptivePlan.eval,
        hpure, Nat.zero_sub, pow_zero, div_one]
      ring
    | succ q =>
      cases q with
      | zero =>
        simp only [nonadaptivize, decodeLaw_nonadaptivePlan, nonadaptivizePlan, ProbComp.eval_pure,
          PMF.pure_map, NonadaptivePlan.eval, hpure, Nat.sub_self, pow_zero, div_one]
        ring
      | succ q =>
        simp only [nonadaptivize, decodeLaw_nonadaptivePlan, nonadaptivizePlan, ProbComp.eval_bind,
          ProbComp.eval_pure, PMF.map_bind, PMF.pure_map, NonadaptivePlan.eval, PMF.bind_pure,
          hpure, Nat.add_sub_cancel]
        rw [toReal_eval_attenuate]
        by_cases hbb : b₀ = b
        · subst hbb; simp
        · simp [hbb, Ne.symm hbb]
  | liftBind q' cont ih =>
    cases q with
    | zero =>
      rw [nonadaptivize, decodeLaw_nonadaptivePlan, nonadaptivizePlan, ProbComp.eval_bind,
        PMF.map_bind]
      simp only [ProbComp.eval_pure, PMF.pure_map, NonadaptivePlan.eval, PMF.bind_pure,
        eval_stripQueries _ hq y, Nat.zero_sub, pow_zero, div_one]
      ring
    | succ q =>
      cases q with
      | zero =>
        cases q' with
        | inl k =>
          have hlaw : decodeLaw (nonadaptivize 1 (.liftBind (.inl k) cont) hq) y =
              (ProbComp.unifOracle k).bind fun c =>
                decodeLaw (nonadaptivize 1 (cont c)
                  ((IsCostBounded.liftBind_iff.mp hq).2 c)) y := by
            simp only [nonadaptivize, decodeLaw_nonadaptivePlan, nonadaptivizePlan,
              ProbComp.eval_bind, ProbComp.eval_unifFin, PMF.map_bind]
            rfl
          have hprog : decodeLaw (.liftBind (.inl k) cont) y =
              (ProbComp.unifOracle k).bind fun c => decodeLaw (cont c) y := by
            change decodeLaw (OracleComp.query (.inl k) >>= cont) y = _
            rw [decodeLaw_bind, decodeLaw_query_inl]
          rw [hlaw, hprog, Probability.PMF.bind_apply_toReal, Probability.PMF.bind_apply_toReal]
          simp only [Nat.sub_self, pow_zero, div_one, add_sub_cancel]
          refine Finset.sum_congr rfl fun c _ => congrArg _ ?_
          simpa using ih c ((IsCostBounded.liftBind_iff.mp hq).2 c)
        | inr j =>
          have hlaw : decodeLaw (nonadaptivize 1 (.liftBind (.inr j) cont) hq) y =
              decodeLaw (cont (y j)) y := by
            rw [nonadaptivize, decodeLaw_nonadaptivePlan, nonadaptivizePlan, ProbComp.eval_bind,
              ProbComp.eval_sampleEach, PMF.map_bind]
            simp only [ProbComp.eval_pure, PMF.pure_map, NonadaptivePlan.eval]
            change (Probability.PMF.pi _).map (fun f => f (y j)) = _
            rw [Probability.PMF.pi_map_eval]
            exact eval_stripQueries (cont (y j)) _ y
          have hprog : decodeLaw (.liftBind (.inr j) cont) y = decodeLaw (cont (y j)) y := by
            change decodeLaw (OracleComp.query (.inr j) >>= cont) y = _
            rw [decodeLaw_bind, decodeLaw_query_inr, PMF.pure_bind]
          rw [hlaw, hprog, Nat.sub_self, pow_zero, div_one]
          ring
      | succ q =>
        cases q' with
        | inl k =>
          have hlaw : decodeLaw (nonadaptivize (q + 2) (.liftBind (.inl k) cont) hq) y =
              (ProbComp.unifOracle k).bind fun c =>
                decodeLaw (nonadaptivize (q + 2) (cont c)
                  ((IsCostBounded.liftBind_iff.mp hq).2 c)) y := by
            simp only [nonadaptivize, decodeLaw_nonadaptivePlan, nonadaptivizePlan,
              ProbComp.eval_bind, ProbComp.eval_unifFin, PMF.map_bind]
            rfl
          have hprog : decodeLaw (.liftBind (.inl k) cont) y =
              (ProbComp.unifOracle k).bind fun c => decodeLaw (cont c) y := by
            change decodeLaw (OracleComp.query (.inl k) >>= cont) y = _
            rw [decodeLaw_bind, decodeLaw_query_inl]
          rw [hlaw, hprog, Probability.PMF.bind_apply_toReal, Probability.PMF.bind_apply_toReal]
          have hstep : ∑ c, ((ProbComp.unifOracle k) c).toReal *
              (decodeLaw (nonadaptivize (q + 2) (cont c)
                ((IsCostBounded.liftBind_iff.mp hq).2 c)) y b).toReal =
              ∑ c, ((ProbComp.unifOracle k) c).toReal *
                (1 / 2 + ((decodeLaw (cont c) y b).toReal - 1 / 2) /
                  (Fintype.card Γ : ℝ) ^ (q + 2 - 1)) :=
            Finset.sum_congr rfl fun c _ => congrArg _
              (ih c (q := q + 2) ((IsCostBounded.liftBind_iff.mp hq).2 c))
          rw [hstep]
          have hsum1 : ∑ c, ((ProbComp.unifOracle k) c).toReal = 1 := Probability.PMF.sum_toReal _
          simp only [mul_add, Finset.sum_add_distrib]
          congr 1
          · rw [← Finset.sum_mul, hsum1, one_mul]
          · simp_rw [← mul_div_assoc, mul_sub]
            rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum1, one_mul]
        | inr j =>
          have hprog : decodeLaw (.liftBind (.inr j) cont) y = decodeLaw (cont (y j)) y := by
            change decodeLaw (OracleComp.query (.inr j) >>= cont) y = _
            rw [decodeLaw_bind, decodeLaw_query_inr, PMF.pure_bind]
          have hcont_yj : ProbOracleComp.IsQueryBounded (cont (y j)) (q + 1) :=
            (IsCostBounded.liftBind_iff.mp hq).2 (y j)
          have hlaw : decodeLaw (nonadaptivize (q + 2) (.liftBind (.inr j) cont) hq) y =
              (PMF.uniformOfFintype Γ).bind fun guess =>
                if guess = y j then
                  decodeLaw (nonadaptivize (q + 1) (cont (y j)) hcont_yj) y
                else PMF.uniformOfFintype Bool := by
            rw [nonadaptivize, decodeLaw_nonadaptivePlan, nonadaptivizePlan, ProbComp.eval_bind,
              ProbComp.eval_uniform, PMF.map_bind]
            congr 1 with guess
            rw [ProbComp.eval_bind, ProbComp.eval_uniform, PMF.map_bind]
            by_cases hgy : guess = y j
            · subst hgy
              have hstep (u : Bool) :
                  (ProbComp.eval (nonadaptivizePlan (q + 1) (cont (y j)) hcont_yj >>= fun rest =>
                    pure (NonadaptivePlan.mk (Fin.cons (some j) rest.queries)
                      fun vals => if vals 0 = some (y j) then rest.decide (Fin.tail vals)
                        else u))).map (fun plan => plan.eval y) =
                    decodeLaw (nonadaptivize (q + 1) (cont (y j)) hcont_yj) y := by
                rw [ProbComp.eval_bind, PMF.map_bind, nonadaptivize, decodeLaw_nonadaptivePlan]
                congr 1 with rest
                rw [ProbComp.eval_pure, PMF.pure_map]
                congr 1
                simp only [NonadaptivePlan.eval, Fin.cons_zero, Option.map_some, ↓reduceIte]
                rfl
              simp only [↓reduceIte, hstep, PMF.bind_const]
            · have hne : some (y j) ≠ some guess := fun h => hgy (Option.some.inj h).symm
              have hstep (u : Bool) :
                  (ProbComp.eval (nonadaptivizePlan (q + 1) (cont guess)
                    ((IsCostBounded.liftBind_iff.mp hq).2 guess) >>= fun rest =>
                      pure (NonadaptivePlan.mk (Fin.cons (some j) rest.queries)
                        fun vals => if vals 0 = some guess then rest.decide (Fin.tail vals)
                          else u))).map (fun plan => plan.eval y) = PMF.pure u := by
                rw [ProbComp.eval_bind, PMF.map_bind]
                have hconst (rest : NonadaptivePlan P Γ (q + 1)) :
                    (ProbComp.eval (pure (NonadaptivePlan.mk (Fin.cons (some j) rest.queries)
                      fun vals => if vals 0 = some guess then rest.decide (Fin.tail vals)
                        else u))).map (fun plan => plan.eval y) = PMF.pure u := by
                  rw [ProbComp.eval_pure, PMF.pure_map]
                  congr 1
                  simp only [NonadaptivePlan.eval, Fin.cons_zero, Option.map_some, hne, ↓reduceIte]
                simp only [hconst, PMF.bind_const]
              simp only [hgy, ↓reduceIte, hstep, PMF.bind_pure]
          rw [hlaw, hprog, Probability.PMF.toReal_uniformOfFintype_bind_apply,
            Finset.expect_eq_sum_div_card, Finset.card_univ]
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (y j)), ite_eq_left rfl]
          have hih := ih (y j) (q := q + 1) hcont_yj
          rw [hih]
          have hrest : ∑ guess ∈ Finset.univ.erase (y j),
              ((if guess = y j then
                decodeLaw (nonadaptivize (q + 1) (cont (y j)) hcont_yj) y
              else PMF.uniformOfFintype Bool) b).toReal =
                ((Fintype.card Γ : ℝ) - 1) * (1 / 2) := by
            have hbool : ((PMF.uniformOfFintype Bool) b).toReal = 1 / 2 := by
              rw [PMF.uniformOfFintype_apply]
              norm_num
            rw [Finset.sum_congr rfl fun guess hguess => by
              rw [ite_eq_right (Finset.ne_of_mem_erase hguess), hbool]]
            rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ (y j)),
              Finset.card_univ, nsmul_eq_mul]
            have h1 : 1 ≤ Fintype.card Γ := Fintype.card_pos
            rw [Nat.cast_sub h1, Nat.cast_one]
          rw [hrest]
          have hΓ : (0 : ℝ) < Fintype.card Γ := by exact_mod_cast Fintype.card_pos
          simp only [Nat.add_sub_cancel]
          rw [pow_succ]
          field_simp [hΓ.ne']
          ring

/-- **Adaptive-to-non-adaptive reduction for local decoders** [Yekhanin2012]: every `(q, δ, ε)`
local decoder (adaptive or not) yields a non-adaptive `(q, δ, ε / |Γ| ^ (q - 1))` local decoder. -/
theorem IsLocalDecoder.nonadaptivize [Fintype P] [Fintype Γ] [Nonempty Γ] [DecidableEq Γ]
    {C : (ι → Bool) → P → Γ} {q : ℕ} {δ ε : ℝ} {A : LocalDecoder ι P Γ}
    (hA : IsLocalDecoder C q δ ε A) :
    IsLocalDecoder C q δ (ε / (Fintype.card Γ : ℝ) ^ (q - 1))
      fun i => Code.nonadaptivize q (A i) (hA.isQueryBounded i) where
  isQueryBounded i := isQueryBounded_nonadaptivePlan _
  correct x y i hy := by
    rw [toReal_decodeLaw_nonadaptivize]
    have hc := hA.correct x y i hy
    have hpos : (0 : ℝ) < (Fintype.card Γ : ℝ) ^ (q - 1) := by positivity
    have hdiv : ε / (Fintype.card Γ : ℝ) ^ (q - 1) ≤
        ((decodeLaw (A i) y (x i)).toReal - 1 / 2) / (Fintype.card Γ : ℝ) ^ (q - 1) :=
      div_le_div_of_nonneg_right (by linarith) hpos.le
    linarith

/-- Masking the heavy positions of a non-adaptive local decoder produces an explicit non-adaptive
`(q, q / δ, ε)` smooth decoder with no loss in advantage [KatzTrevisan2000, Theorem 1]. -/
theorem isSmoothDecoder_mask_nonadaptivePlan [Fintype P] [DecidableEq P] [DecidableEq Γ]
    {C : (ι → Bool) → P → Γ} {q : ℕ} {δ ε : ℝ}
    {planLaw : ι → ProbComp (NonadaptivePlan P Γ q)}
    (hA : IsLocalDecoder C q δ ε fun i => nonadaptivePlan (planLaw i))
    (hδ : 0 < δ) (z : P → Γ) :
    IsSmoothDecoder C q (q / δ) ε fun i =>
      nonadaptivePlan (NonadaptivePlan.mask
        (heavyPositions (nonadaptivePlan (planLaw i)) z (q / δ)) z <$> planLaw i) where
  isQueryBounded i := isQueryBounded_nonadaptivePlan _
  correct x i := by
    rw [decodeLaw_nonadaptivePlan_mask]
    refine hA.correct x _ i ?_
    exact (Nat.cast_le.mpr (hammingDist_splice_le _ z (C x))).trans
      (card_heavyPositions_le (hA.isQueryBounded i) z hδ)
  smooth x i j := by
    rw [expectedReads_nonadaptivePlan_mask]
    split_ifs with hj
    · rw [ENNReal.toReal_zero]
      exact div_nonneg (div_nonneg (Nat.cast_nonneg _) hδ.le) (Nat.cast_nonneg _)
    · rw [(hasObliviousReads_nonadaptivePlan _).expectedReads_eq _ z]
      simpa [heavyPositions] using hj

/-- **Adaptive Katz–Trevisan smoothing**: every `(q, δ, ε)` local decoder (adaptive or not) over a
finite nonempty alphabet `Γ` yields an explicit non-adaptive `(q, q / δ, ε / |Γ| ^ (q - 1))` smooth
decoder, combining the adaptive-to-non-adaptive reduction [Yekhanin2012] with heavy-position
masking [KatzTrevisan2000, Theorem 1]. -/
theorem IsLocalDecoder.isSmoothDecoder_adaptive [Fintype P] [DecidableEq P] [Fintype Γ] [Nonempty Γ]
    [DecidableEq Γ] {C : (ι → Bool) → P → Γ} {q : ℕ} {δ ε : ℝ} {A : LocalDecoder ι P Γ}
    (hA : IsLocalDecoder C q δ ε A) (hδ : 0 < δ) (z : P → Γ) :
    IsSmoothDecoder C q (q / δ) (ε / (Fintype.card Γ : ℝ) ^ (q - 1)) fun i =>
      nonadaptivePlan (NonadaptivePlan.mask
        (heavyPositions (Code.nonadaptivize q (A i) (hA.isQueryBounded i)) z (q / δ)) z <$>
          nonadaptivizePlan q (A i) (hA.isQueryBounded i)) :=
  isSmoothDecoder_mask_nonadaptivePlan hA.nonadaptivize hδ z

/-- **Every locally decodable code is smooth**: an arbitrary (possibly adaptive) `(q, δ, ε)`
locally decodable code over a finite nonempty alphabet `Γ` is a `(q, q / δ, ε / |Γ| ^ (q - 1))`
smooth code. -/
theorem IsLocallyDecodable.isSmoothCode [Fintype P] [DecidableEq P] [Fintype Γ] [Nonempty Γ]
    [DecidableEq Γ] {C : (ι → Bool) → P → Γ} {q : ℕ} {δ ε : ℝ} (hC : IsLocallyDecodable C q δ ε)
    (hδ : 0 < δ) :
    IsSmoothCode C q (q / δ) (ε / (Fintype.card Γ : ℝ) ^ (q - 1)) := by
  obtain ⟨A, hA⟩ := isLocallyDecodable_iff.mp hC
  exact (hA.isSmoothDecoder_adaptive hδ (C fun _ => false)).isSmoothCode

end Adaptive

end Cslib.Code
