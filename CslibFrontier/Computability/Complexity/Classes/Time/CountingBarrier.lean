/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Hierarchy.NondeterministicTime
public import CslibFrontier.Computability.Complexity.Classes.PH.Collapse
public import CslibFrontier.Computability.Complexity.Classes.PP.Bit
public import CslibFrontier.Computability.Complexity.Classes.PP.Closure
public import CslibFrontier.Computability.Complexity.Classes.Time.RandomAccessATM
public import CslibFrontier.Computability.Complexity.Classes.Toda

/-!
# Counting, separation barriers, and exact conditional reductions

This module formalizes the structural barriers surrounding the target containment
`Σ₂TIME(T) ⊆ Σ₃TIME(T / √(log T))`, together with the exact conditional reduction showing which
missing lemmas would imply it:

1. **Toda / counting-flattening barrier (Hint 3)**: Putting arbitrary polynomial-time counting
   bit-tests `{a | (f a).testBit (q |enc a|) = true}` (`f ∈ #P`) inside a fixed level `Σₖᵖ` of the
   polynomial hierarchy collapses `PH` to `Σₖᵖ` (`Cslib.Complexity.PH = SigmaP k`), because Toda's
   theorem (`PH ⊆ BP·⊕P` and `exists_SharpP_testBit_of_mem_BPOp_ParityP`) already reduces every
   language in `PH` to a single bit test of a `#P` function. In particular, placing `#P` bits in
   `Σ₃ᵖ` collapses `PH` to `Σ₃ᵖ`, and placing them in `NP` (`Σ₁ᵖ`) collapses `PH` to `NP`.
2. **Random-access elimination and separation barrier**: Simulating `t` adaptive random-access
   queries `input[queries ans u v w i]?` (`i : Fin t`) sequentially can be expressed with one
   additional universal quantifier block (`∃ u ∀ v ∃ (w, ans) ∀ i`, i.e., `Σ₄` in time
   `O(n + t)`), proved by strong induction along causal prefixes `j < i`. At `T(n) = n^2`, `n` is
   `o(n^2 / √(log n))`, so random-access elimination keeps the target bound within
   `O(n^2 / √(log n))`. Consequently, combining the target containment with sequential PH collapse
   (for example under `NTIME_seq(n) = coNTIME_seq(n)` via translational padding) would violate the
   sharp nondeterministic time hierarchy `NTIME_seq(n^2 / √(log n)) ⊂ NTIME_seq(n^2)`
   (Žák 1983 / SFM 1978), refuting `NTIME_seq(n) = coNTIME_seq(n)`. Contrast this with the
   unconditional coarse polynomial NTIME hierarchy already proved in cslib-frontier
   (`Cslib.Complexity.NTIME_succ_pow_ssubset_NTIME_succ_pow_of_le`).
3. **Exact non-vacuous conditional reductions (Remaining Lemmas A & B)**: Formally isolating
   * **Lemma A (`HasSwitchCompression`)**: compressing winning switch witnesses `c` to computable
     length `s n ≤ O(F n)` with a `Σ₃TIME` reachability predicate `E ∈ Σ₃TIME(tE)` satisfying
     `tE ≤ O(n + F n)` on short pairs, and
   * **Lemma B (`HasTwoBlockRejection`)**: deciding continuation rejection `B ∈ Σ₂TIME(tB)` within
     `tB ≤ O(n + F n)` on short pairs,
   and proving `remaining_lemmas_imply_containment` via `mem_SigmaThreeTIME_of_composition_of_le`
   that (A) and (B) together place `A ∈ Σ₃TIME(F)`. We also formalize the clocked `RAATM`
   selector-bit counterpart (`RASwitchCompression`, `RATwoBlockRejection`,
   `RA_remaining_lemmas_imply_containment`) for random-access bounds where `F(T) < n`.

## Main results

* `Cslib.Complexity.countingBitInSigmaP_collapses_PH_to_SigmaP`: `#P` bit tests in `Σₖᵖ` collapse
  `PH` to `Σₖᵖ`.
* `Cslib.Complexity.countingBitInSigmaP_three_collapses_PH_to_SigmaP_three`: special case `k = 3`,
  `PH = Σ₃ᵖ`.
* `Cslib.Complexity.PP_subset_SigmaP_inter_PiP_of_countingBitInSigmaP`: `#P` bit tests in `Σₖᵖ`
  imply `PP ⊆ Σₖᵖ ∩ Πₖᵖ`.
* `Cslib.Complexity.countingBitInSigmaP_one_collapses_PH_to_NP`: `#P` bit tests in `NP` collapse
  `PH` to `NP`.
* `Cslib.Complexity.adaptiveQueryTrace`, `Cslib.Complexity.RA_query_log_elimination`: exact
  equivalence eliminating `t` adaptive random-access queries into one inner `∀` transcript check.
* `Cslib.Complexity.separation_barrier_contradiction`: combining target speedup with linear
  `NTIME = coNTIME` padding collapse contradicts a sharp `n^2 / √(log n)` vs `n^2` NTIME gap.
* `Cslib.Complexity.remaining_lemmas_imply_containment`: conditional proof that switch-state
  compression (`HasSwitchCompression`) plus two-block rejection (`HasTwoBlockRejection`) yields
  `A ∈ SigmaThreeTIME enc F`.
* `Cslib.Complexity.RA_remaining_lemmas_imply_containment`: clocked finite-state `RAATM`
  selector-bit composition under `RASwitchCompression` and `RATwoBlockRejection`.

## References

* [S. Toda, *PP is as hard as the polynomial-time hierarchy*][Toda1991]
* [S. Žák, *A Turing machine time hierarchy*][Zak1983]
* J. I. Seiferas, M. J. Fischer, A. R. Meyer, *Separating nondeterministic time complexity
  classes*, JACM, 1978
-/

public section

namespace Cslib.Complexity

/-! ### Part I: Toda / Counting-Flattening Barrier (Hint 3) -/

section TodaCountingBarrier

/-- Hypothesis `(CB_k)`: every bit at a polynomial position of every `#P` function belongs to
level `Σₖᵖ` of the polynomial hierarchy, uniformly over all encodings `enc : α ↪ List Bool`. -/
@[expose] def CountingBitInSigmaP (k : ℕ) : Prop :=
  ∀ {α : Type} (enc : α ↪ List Bool) (f : α → ℕ),
    f ∈ SharpP enc → ∀ q : Polynomial ℕ,
      {a | (f a).testBit (Polynomial.eval (enc a).length q) = true} ∈ SigmaP k enc

/-- If every polynomial-time counting bit lies in `Σₖᵖ`, then by Toda's theorem (`PH ⊆ BP·⊕P`
and `exists_SharpP_testBit_of_mem_BPOp_ParityP`), **the entire polynomial hierarchy collapses to
`Σₖᵖ`**: `PH = Σₖᵖ`. -/
theorem countingBitInSigmaP_collapses_PH_to_SigmaP {k : ℕ} (hCB : CountingBitInSigmaP k) :
    ∀ {α : Type} (enc : α ↪ List Bool), PH enc = SigmaP k enc := by
  intro α enc
  refine Set.Subset.antisymm (fun L hL => ?_) (SigmaP_subset_PH k)
  obtain ⟨f, hf, q, hLbit⟩ := exists_SharpP_testBit_of_mem_BPOp_ParityP (PH_subset_BPOp_ParityP hL)
  have hmem : {a | (f a).testBit (Polynomial.eval (enc a).length q) = true} ∈ SigmaP k enc :=
    hCB enc f hf q
  have heq : L = {a | (f a).testBit (Polynomial.eval (enc a).length q) = true} := by
    ext a
    simpa [Set.mem_ofPred_eq] using hLbit a
  rwa [heq]

/-- Special case `k = 3`: putting arbitrary `#P` counting bits in `Σ₃ᵖ` collapses `PH = Σ₃ᵖ`. -/
theorem countingBitInSigmaP_three_collapses_PH_to_SigmaP_three (hCB : CountingBitInSigmaP 3) :
    ∀ {α : Type} (enc : α ↪ List Bool), PH enc = SigmaP 3 enc :=
  countingBitInSigmaP_collapses_PH_to_SigmaP hCB

/-- Under `(CB_k)`, every `PP` language lies in `Σₖᵖ ∩ Πₖᵖ`, because `PP` is closed under
complement (`compl_mem_PP`) and each `PP` language is one bit of a `#P` function
(`exists_SharpP_testBit_of_mem_PP`). -/
theorem PP_subset_SigmaP_inter_PiP_of_countingBitInSigmaP {k : ℕ} (hCB : CountingBitInSigmaP k) :
    ∀ {α : Type} (enc : α ↪ List Bool), PP enc ⊆ SigmaP k enc ∩ PiP k enc := by
  intro α enc A hA
  have hSig : A ∈ SigmaP k enc := by
    obtain ⟨f, hf, q, hbit⟩ := exists_SharpP_testBit_of_mem_PP hA
    have hmem := hCB enc f hf q
    have heq : A = {a | (f a).testBit (Polynomial.eval (enc a).length q) = true} := by
      ext a
      exact hbit a
    rwa [heq]
  have hPi : A ∈ PiP k enc := by
    obtain ⟨f, hf, q, hbit⟩ := exists_SharpP_testBit_of_mem_PP (compl_mem_PP hA)
    have hmem := hCB enc f hf q
    have heq : Aᶜ = {a | (f a).testBit (Polynomial.eval (enc a).length q) = true} := by
      ext a
      exact hbit a
    exact compl_mem_SigmaP_iff.mp (heq ▸ hmem)
  exact ⟨hSig, hPi⟩

/-- Special case `k = 1`: putting `#P` counting bits in `NP` (`Σ₁ᵖ`) collapses `PH = NP`. -/
theorem countingBitInSigmaP_one_collapses_PH_to_NP (hCB : CountingBitInSigmaP 1) :
    ∀ {α : Type} (enc : α ↪ List Bool), PH enc = NP enc := by
  intro _ enc
  exact (countingBitInSigmaP_collapses_PH_to_SigmaP hCB enc).trans SigmaP_one

/-- Special case `k = 0`: putting `#P` counting bits in `P` (`Σ₀ᵖ`) collapses `PH = P`. -/
theorem countingBitInSigmaP_zero_collapses_PH_to_P (hCB : CountingBitInSigmaP 0) :
    ∀ {α : Type} (enc : α ↪ List Bool), PH enc = P enc := by
  intro α enc
  exact (countingBitInSigmaP_collapses_PH_to_SigmaP hCB enc).trans SigmaP_zero

end TodaCountingBarrier

/-! ### Part II: Random-Access Elimination and Sharp-Gap Separation Barrier -/

section SeparationBarrier

/-- Canonical adaptive query-answer trace determined step-by-step from causal prefixes `j < i`. -/
@[expose] def adaptiveQueryTrace {U V W : Type} {t : ℕ} (input : List Bool)
    (queries : (Fin t → Option Bool) → U → V → W → Fin t → ℕ)
    (u : U) (v : V) (w : W) (i : ℕ) : Option Bool :=
  if hi : i < t then
    let prev : Fin t → Option Bool := fun j =>
      if _hj : j.val < i then adaptiveQueryTrace input queries u v w j.val else none
    input[queries prev u v w ⟨i, hi⟩]?
  else none
termination_by i

/-- Fixed-point equation satisfied by `adaptiveQueryTrace` whenever `queries` depends causally
only on prior replies `j.val < i.val`. -/
theorem adaptiveQueryTrace_eq {U V W : Type} {t : ℕ} (input : List Bool)
    (queries : (Fin t → Option Bool) → U → V → W → Fin t → ℕ)
    (hcausal : ∀ a₁ a₂ u v w (i : Fin t),
      (∀ j : Fin t, j.val < i.val → a₁ j = a₂ j) →
      queries a₁ u v w i = queries a₂ u v w i)
    (u : U) (v : V) (w : W) (i : Fin t) :
    adaptiveQueryTrace input queries u v w i.val =
      input[queries (fun j => adaptiveQueryTrace input queries u v w j.val) u v w i]? := by
  rw [adaptiveQueryTrace]
  simp only [i.isLt, ↓reduceDIte]
  rw [hcausal _ (fun j => adaptiveQueryTrace input queries u v w j.val) u v w i]
  intro j hj
  simp [hj]

/-- **Exact adaptive RA query-log elimination (`Σ₃ → Σ₄`)**: a `Σ₃` protocol making `t`
adaptive random-access input queries `queries ans u v w i` (depending causally only on answers
to indices `j < i`) is equivalent to guessing an explicit reply log `ans : Fin t → Option Bool`
inside the inner existential block `∃ (w, ans)` and using one inner universal quantifier
`∀ i : Fin t` to check consistency sequentially against `input`. -/
theorem RA_query_log_elimination {U V W : Type} {t : ℕ} (input : List Bool)
    (queries : (Fin t → Option Bool) → U → V → W → Fin t → ℕ)
    (hcausal : ∀ a₁ a₂ u v w (i : Fin t),
      (∀ j : Fin t, j.val < i.val → a₁ j = a₂ j) →
      queries a₁ u v w i = queries a₂ u v w i)
    (stepCheck : (Fin t → Option Bool) → U → V → W → Bool) :
    (∃ u : U, ∀ v : V, ∃ w : W,
      stepCheck (fun i => adaptiveQueryTrace input queries u v w i.val) u v w = true) ↔
      ∃ u : U, ∀ v : V, ∃ (w : W) (ans : Fin t → Option Bool),
        stepCheck ans u v w = true ∧ ∀ i : Fin t, ans i = input[queries ans u v w i]? := by
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨u, fun v => ?_⟩
    obtain ⟨w, hw⟩ := hu v
    refine ⟨w, fun i => adaptiveQueryTrace input queries u v w i.val, hw, fun i => ?_⟩
    exact adaptiveQueryTrace_eq input queries hcausal u v w i
  · rintro ⟨u, hu⟩
    refine ⟨u, fun v => ?_⟩
    obtain ⟨w, ans, hcheck, hagree⟩ := hu v
    have hdet : ∀ n : ℕ, (hn : n < t) →
        ans ⟨n, hn⟩ = adaptiveQueryTrace input queries u v w n := by
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ih =>
        intro hn
        rw [hagree ⟨n, hn⟩, adaptiveQueryTrace_eq input queries hcausal u v w ⟨n, hn⟩]
        rw [hcausal ans (fun j => adaptiveQueryTrace input queries u v w j.val) u v w ⟨n, hn⟩]
        intro j hj
        exact ih j.val hj j.isLt
    have hans : ans = fun i => adaptiveQueryTrace input queries u v w i.val :=
      funext fun i => hdet i.val i.isLt
    rw [hans] at hcheck
    exact ⟨w, hcheck⟩

/-- At `T(n) = n ^ 2`, sequential scan time `n` is strictly dominated by `T(n) / √(log₂(T(n) + 2))`
once `n ≥ 4`. Hence `O(n + F(n^2)) = O(F(n^2))`, so RA elimination into sequential `Σ₄` preserves
the `O(T / √(log T))` bound at quadratic time (unlike `T(n) = n`, where sequential input discovery
forces `Ω(n)`). -/
theorem linear_le_sq_div_sqrt_log {n : ℕ} (hn : 4 ≤ n) :
    n ≤ n ^ 2 / Nat.sqrt (Nat.log 2 (n ^ 2 + 2)) := by
  have hlog_pos : 1 ≤ Nat.log 2 (n ^ 2 + 2) := by
    by_contra h0
    have hz : Nat.log 2 (n ^ 2 + 2) = 0 := by omega
    have hlt := Nat.lt_pow_succ_log_self (by omega : 1 < 2) (n ^ 2 + 2)
    rw [hz] at hlt
    have : 4 ≤ n ^ 2 := by nlinarith
    omega
  have hs_pos : 1 ≤ Nat.sqrt (Nat.log 2 (n ^ 2 + 2)) := Nat.sqrt_pos.mpr hlog_pos
  have hpow : Nat.log 2 (n ^ 2 + 2) ≤ n ^ 2 + 2 := Nat.log_le_self 2 (n ^ 2 + 2)
  have hs_le_sq : Nat.sqrt (Nat.log 2 (n ^ 2 + 2)) ≤ n := by
    have hsq_le : Nat.sqrt (Nat.log 2 (n ^ 2 + 2)) * Nat.sqrt (Nat.log 2 (n ^ 2 + 2)) ≤
        Nat.log 2 (n ^ 2 + 2) := Nat.sqrt_le _
    by_contra hgt
    have hlt : n + 1 ≤ Nat.sqrt (Nat.log 2 (n ^ 2 + 2)) := by omega
    have hmul : (n + 1) * (n + 1) ≤ Nat.log 2 (n ^ 2 + 2) :=
      (Nat.mul_le_mul hlt hlt).trans hsq_le
    nlinarith
  exact (Nat.le_div_iff_mul_le hs_pos).mpr (by nlinarith)

/-- A sharp bounded-gap nondeterministic time hierarchy hypothesis `HasSharpNTimeGap t₁ t₂`:
`NTIME_seq(t₁) ⊂ NTIME_seq(t₂)` (e.g., Žák 1983 / SFM 1978 with `t₁(n) = n + n^2 / √(log n)` and
`t₂(n) = n^2`). Compare with `Cslib.Complexity.NTIME_succ_pow_ssubset_NTIME_succ_pow_of_le` for a
polynomial separation unconditionally formalized in cslib-frontier. -/
@[expose] def HasSharpNTimeGap (t₁ t₂ : ℕ → ℕ) : Prop :=
  NTIME Turing.MultiTapeTM.encBits t₁ ⊂ NTIME Turing.MultiTapeTM.encBits t₂

/-- Concrete coarse separation theorem from cslib-frontier for comparison with `HasSharpNTimeGap`:
every polynomial degree jump `6 * d + 14 ≤ e` strictly separates sequential `NTIME`. -/
theorem polynomial_NTIME_gap_witness {d e : ℕ} (h : 6 * d + 14 ≤ e) :
    HasSharpNTimeGap (fun n => (n + 1) ^ d) (fun n => (n + 1) ^ e) :=
  NTIME_succ_pow_ssubset_NTIME_succ_pow_of_le h

/-- **Separation Barrier Contradiction**:
Suppose we fix an intermediate sequential `Σ₄` class `SeqSigma4 t`, a source time `T`, and a
sublogarithmic speedup `F` satisfying:
1. `NTIME encBits T ⊆ RASigmaTwoTime T` (`NTIME_seq ⊆ Σ₂TIME_Idx`);
2. the target containment `RASigmaTwoTime T ⊆ RASigmaThreeTime F`;
3. random-access elimination `RASigmaThreeTime F ⊆ SeqSigma4 (fun n => n + F n)`;
4. a sharp sequential nondeterministic time hierarchy `HasSharpNTimeGap (fun n => n + F n) T`.

Then any linear-time collapse hypothesis `LinearCollapse` strong enough to compress
`SeqSigma4 (fun n => n + F n)` down to `NTIME encBits (fun n => n + F n)` (for instance via
`NTIME_seq(id) = coNTIME_seq(id)` and translational padding) is **refuted** (`¬ LinearCollapse`). -/
theorem separation_barrier_contradiction {T F : ℕ → ℕ}
    {SeqSigma4 : (ℕ → ℕ) → Set (Set (List Bool))}
    {LinearCollapse : Prop}
    (h_src : NTIME Turing.MultiTapeTM.encBits T ⊆ RASigmaTwoTime T)
    (h_target : RASigmaTwoTime T ⊆ RASigmaThreeTime F)
    (h_elim : RASigmaThreeTime F ⊆ SeqSigma4 (fun n => n + F n))
    (h_collapse : LinearCollapse →
      SeqSigma4 (fun n => n + F n) ⊆ NTIME Turing.MultiTapeTM.encBits (fun n => n + F n))
    (h_sharp : HasSharpNTimeGap (fun n => n + F n) T) :
    ¬ LinearCollapse := by
  intro hC
  have hsub :
      NTIME Turing.MultiTapeTM.encBits T ⊆ NTIME Turing.MultiTapeTM.encBits (fun n => n + F n) :=
    h_src.trans (h_target.trans (h_elim.trans (h_collapse hC)))
  exact (ssubset_iff_subset_ne.mp h_sharp).2 (Set.Subset.antisymm h_sharp.subset hsub)

end SeparationBarrier

/-! ### Part III: Exact Non-Vacuous Conditional Reductions (Remaining Lemmas A & B) -/

section ConditionalReductions

/-- **Remaining Lemma A (`HasSwitchCompression`, sequential `SigmaThreeTIME` form)**:
`A` admits switch summaries `c` of computable length `|c| ≤ s |enc a| ≤ O(F |enc a|)`, a `Σ₃TIME`
reachability predicate `E ∈ Σ₃TIME(tE)` with `tE ≤ O(n + F n)` on short pairs `(a, c)`, and a
continuation rejection relation `B` preserving `a ∈ A ↔ ∃ c, (a, c) ∈ E ∧ (a, c) ∉ B`. -/
@[expose] def HasSwitchCompression {α : Type} (enc : α ↪ List Bool) (F : ℕ → ℕ)
    (A : Set α) (s tE : ℕ → ℕ) (E B : Set (α × List Bool)) : Prop :=
  (∃ Cs : ℕ, (∀ n, s n ≤ Cs * F n + Cs) ∧
    Turing.MultiTapeTM.ComputableInO (fun x : List Bool => s x.length)
      Turing.MultiTapeTM.encBits Turing.MultiTapeTM.encUnary
      (fun x => x.length + F x.length) (fun x => x.length + F x.length)) ∧
  E ∈ SigmaThreeTIME (Turing.MultiTapeTM.encPair enc Turing.MultiTapeTM.encBits) tE ∧
  (∃ KE : ℕ, ∀ a (c : List Bool), c.length ≤ s (enc a).length →
    tE (Turing.MultiTapeTM.encPair enc Turing.MultiTapeTM.encBits (a, c)).length ≤
      KE * ((enc a).length + F (enc a).length) + KE) ∧
  (∀ a (c : List Bool), (a, c) ∈ E → c.length ≤ s (enc a).length) ∧
  (∀ a, a ∈ A ↔ ∃ c : List Bool, (a, c) ∈ E ∧ (a, c) ∉ B)

/-- **Remaining Lemma B (`HasTwoBlockRejection`, sequential `SigmaTwoTIME` form)**:
The continuation rejection relation `B` from a compressed switch summary belongs to `Σ₂TIME(tB)`
with `tB ≤ O(n + F n)` on short pairs `(a, c)`. -/
@[expose] def HasTwoBlockRejection {α : Type} (enc : α ↪ List Bool) (F s tB : ℕ → ℕ)
    (B : Set (α × List Bool)) : Prop :=
  B ∈ SigmaTwoTIME (Turing.MultiTapeTM.encPair enc Turing.MultiTapeTM.encBits) tB ∧
  ∃ KB : ℕ, ∀ a (c : List Bool), c.length ≤ s (enc a).length →
    tB (Turing.MultiTapeTM.encPair enc Turing.MultiTapeTM.encBits (a, c)).length ≤
      KB * ((enc a).length + F (enc a).length) + KB

/-- **Non-vacuous Conditional Speedup Theorem (`Lemma A + Lemma B ⟹ Σ₃TIME(F)`)**:
Whenever a language `A` satisfies resource-bounded switch compression (`HasSwitchCompression`) and
resource-bounded two-block rejection (`HasTwoBlockRejection`) with `n ≤ F n`, `A` belongs to
`SigmaThreeTIME enc F`. Because every set in `SigmaThreeTIME enc F` is decidable by a linear-time
verifier, neither hypothesis holds vacuously on undecidable sets. -/
theorem remaining_lemmas_imply_containment {α : Type} {enc : α ↪ List Bool}
    {F : ℕ → ℕ} {A : Set α} {s tE tB : ℕ → ℕ} {E B : Set (α × List Bool)}
    (hF_dom : ∀ n, n ≤ F n)
    (hA : HasSwitchCompression enc F A s tE E B)
    (hB : HasTwoBlockRejection enc F s tB B) :
    A ∈ SigmaThreeTIME enc F := by
  rcases hA with ⟨⟨Cs, hs_le, hs⟩, hE, ⟨KE, htE⟩, hdom, hiff⟩
  rcases hB with ⟨hB_mem, KB, htB⟩
  exact mem_SigmaThreeTIME_of_composition_of_le (Cs := Cs) (KE := KE) (KB := KB)
    hF_dom hs_le hs hE htE hB_mem htB hdom hiff

/-- Clocked deterministic `RAATM` verifier running on input `x` with pre-loaded auxiliary tape
`aux` within time bound `t`. -/
@[expose] def RADetVerify {k : ℕ} {State : Type} (M : RAATM (k + 1) State)
    (x aux : List Bool) (t : ℕ) : Bool :=
  (M.runCoins x (RACfg.initWithAux M.q₀ (Nat.succ_pos k) aux) (List.replicate t false)).accept

/-- **Remaining Lemma A (Random-Access `RAATM` form)**:
Every compressed switch `c` has length `|c| ≤ s |x| = O(F(T |x|))`, and reachability is decided
by a single finite-state deterministic `RAATM` `ME` running in `O(F(T |x|))` steps on bounded
bit-string blocks `u, v, w` of length `≤ ℓE |x| = O(F(T |x|))`. -/
@[expose] def RASwitchCompression (T F : ℕ → ℕ) (L : Set (List Bool)) (s : ℕ → ℕ)
    (B : List Bool → List Bool → Prop) : Prop :=
  ∃ (Cs KE cE₁ cE₂ kE : ℕ) (ℓE : ℕ → ℕ) (StateE : Type) (_ : Finite StateE)
    (ME : RAATM (kE + 1) StateE),
    ME.IsDeterministic ∧
    (∀ n, s n ≤ Cs * F (T n) + Cs) ∧
    (∀ n, ℓE n ≤ KE * F (T n) + KE) ∧
    (∀ (x c u v w : List Bool), c.length ≤ s x.length → u.length ≤ ℓE x.length →
      v.length ≤ ℓE x.length → w.length ≤ ℓE x.length →
      let aux := Turing.MultiTapeTM.encPair Turing.MultiTapeTM.encBits encSigmaThreeWitness
        (c, ⟨u, v, w⟩)
      (ME.runCoins x (RACfg.initWithAux ME.q₀ (Nat.succ_pos kE) aux)
        (List.replicate (cE₁ * F (T x.length) + cE₂) false)).state = none) ∧
    ∀ x : List Bool, x ∈ L ↔
      ∃ c : List Bool, c.length ≤ s x.length ∧
        (∃ u : List Bool, u.length ≤ ℓE x.length ∧
          ∀ v : List Bool, v.length ≤ ℓE x.length →
            ∃ w : List Bool, w.length ≤ ℓE x.length ∧
              RADetVerify ME x
                (Turing.MultiTapeTM.encPair Turing.MultiTapeTM.encBits encSigmaThreeWitness
                  (c, ⟨u, v, w⟩))
                (cE₁ * F (T x.length) + cE₂) = true) ∧
        ¬ B x c

/-- **Remaining Lemma B (Random-Access `RAATM` form)**:
Continuation rejection `B x c` from a switch summary `c` is decided by a finite-state
deterministic `RAATM` `MB` running in `O(F(T |x|))` steps on bounded blocks `p, q` of length
`≤ ℓB |x| = O(F(T |x|))`. -/
@[expose] def RATwoBlockRejection (T F s : ℕ → ℕ)
    (B : List Bool → List Bool → Prop) : Prop :=
  ∃ (KB cB₁ cB₂ kB : ℕ) (ℓB : ℕ → ℕ) (StateB : Type) (_ : Finite StateB)
    (MB : RAATM (kB + 1) StateB),
    MB.IsDeterministic ∧
    (∀ n, ℓB n ≤ KB * F (T n) + KB) ∧
    (∀ (x c p q : List Bool), c.length ≤ s x.length → p.length ≤ ℓB x.length →
      q.length ≤ ℓB x.length →
      let aux := Turing.MultiTapeTM.encPair Turing.MultiTapeTM.encBits
        (Turing.MultiTapeTM.encPair Turing.MultiTapeTM.encBits Turing.MultiTapeTM.encBits)
        (c, (p, q))
      (MB.runCoins x (RACfg.initWithAux MB.q₀ (Nat.succ_pos kB) aux)
        (List.replicate (cB₁ * F (T x.length) + cB₂) false)).state = none) ∧
    ∀ (x c : List Bool), c.length ≤ s x.length →
      (B x c ↔ ∃ p : List Bool, p.length ≤ ℓB x.length ∧
        ∀ q : List Bool, q.length ≤ ℓB x.length →
          RADetVerify MB x
            (Turing.MultiTapeTM.encPair Turing.MultiTapeTM.encBits
              (Turing.MultiTapeTM.encPair Turing.MultiTapeTM.encBits Turing.MultiTapeTM.encBits)
              (c, (p, q)))
            (cB₁ * F (T x.length) + cB₂) = true)

/-- **Conditional Random-Access Speedup Theorem (`RASwitchCompression + RATwoBlockRejection`)**:
Combining resource-bounded RA switch compression and RA two-block rejection via
`selectorBit_composition` places `L` into an explicit 3-block `∃ ∀ ∃` protocol with
`O(F(T |x|))`-bit witnesses/challenges evaluated by clocked finite-state deterministic `RAATM`
verifiers halting in `O(F(T |x|))` steps. -/
theorem RA_remaining_lemmas_imply_containment {T F s : ℕ → ℕ} {L : Set (List Bool)}
    {B : List Bool → List Bool → Prop}
    (hA : RASwitchCompression T F L s B) (hB : RATwoBlockRejection T F s B) :
    ∃ (Cs KE cE₁ cE₂ kE KB cB₁ cB₂ kB : ℕ) (ℓE ℓB : ℕ → ℕ)
      (StateE : Type) (_ : Finite StateE) (ME : RAATM (kE + 1) StateE)
      (StateB : Type) (_ : Finite StateB) (MB : RAATM (kB + 1) StateB),
      ME.IsDeterministic ∧ MB.IsDeterministic ∧
      (∀ n, s n ≤ Cs * F (T n) + Cs) ∧
      (∀ n, ℓE n ≤ KE * F (T n) + KE) ∧
      (∀ n, ℓB n ≤ KB * F (T n) + KB) ∧
      (∀ (x c u v w : List Bool), c.length ≤ s x.length → u.length ≤ ℓE x.length →
        v.length ≤ ℓE x.length → w.length ≤ ℓE x.length →
        (ME.runCoins x (RACfg.initWithAux ME.q₀ (Nat.succ_pos kE)
          (Turing.MultiTapeTM.encPair Turing.MultiTapeTM.encBits encSigmaThreeWitness
            (c, ⟨u, v, w⟩)))
          (List.replicate (cE₁ * F (T x.length) + cE₂) false)).state = none) ∧
      (∀ (x c p q : List Bool), c.length ≤ s x.length → p.length ≤ ℓB x.length →
        q.length ≤ ℓB x.length →
        (MB.runCoins x (RACfg.initWithAux MB.q₀ (Nat.succ_pos kB)
          (Turing.MultiTapeTM.encPair Turing.MultiTapeTM.encBits
            (Turing.MultiTapeTM.encPair Turing.MultiTapeTM.encBits Turing.MultiTapeTM.encBits)
            (c, (p, q))))
          (List.replicate (cB₁ * F (T x.length) + cB₂) false)).state = none) ∧
      ∀ x : List Bool, x ∈ L ↔
        ∃ cu : {c : List Bool // c.length ≤ s x.length} ×
            {u : List Bool // u.length ≤ ℓE x.length},
          ∀ svp : (side : Bool) × cond side {p : List Bool // p.length ≤ ℓB x.length}
              {v : List Bool // v.length ≤ ℓE x.length},
            ∃ wq : cond svp.1 {q : List Bool // q.length ≤ ℓB x.length}
                {w : List Bool // w.length ≤ ℓE x.length},
              selectorEval
                (fun (_ : Unit) (cs : {c : List Bool // c.length ≤ s x.length}) u v w =>
                  RADetVerify ME x
                    (Turing.MultiTapeTM.encPair Turing.MultiTapeTM.encBits encSigmaThreeWitness
                      (cs.1, ⟨u.1, v.1, w.1⟩))
                    (cE₁ * F (T x.length) + cE₂))
                (fun (_ : Unit) (cs : {c : List Bool // c.length ≤ s x.length}) p q =>
                  RADetVerify MB x
                    (Turing.MultiTapeTM.encPair Turing.MultiTapeTM.encBits
                      (Turing.MultiTapeTM.encPair Turing.MultiTapeTM.encBits
                        Turing.MultiTapeTM.encBits)
                      (cs.1, (p.1, q.1)))
                    (cB₁ * F (T x.length) + cB₂))
                Unit.unit cu svp wq := by
  rcases hA with ⟨Cs, KE, cE₁, cE₂, kE, ℓE, StateE, hfinE, ME, hMEdet, hs_le, hℓE_le,
    hMEhalt, hAspec⟩
  rcases hB with ⟨KB, cB₁, cB₂, kB, ℓB, StateB, hfinB, MB, hMBdet, hℓB_le, hMBhalt, hBspec⟩
  refine ⟨Cs, KE, cE₁, cE₂, kE, KB, cB₁, cB₂, kB, ℓE, ℓB, StateE, hfinE, ME, StateB, hfinB, MB,
    hMEdet, hMBdet, hs_le, hℓE_le, hℓB_le, hMEhalt, hMBhalt, fun x => ?_⟩
  let A₀ : Set Unit := Set.ofPred (fun _ : Unit => x ∈ L)
  have hiff : ∀ u₀ : Unit, u₀ ∈ A₀ ↔
      ∃ cs : {c : List Bool // c.length ≤ s x.length},
        (∃ u : {u : List Bool // u.length ≤ ℓE x.length},
          ∀ v : {v : List Bool // v.length ≤ ℓE x.length},
            ∃ w : {w : List Bool // w.length ≤ ℓE x.length},
              RADetVerify ME x
                (Turing.MultiTapeTM.encPair Turing.MultiTapeTM.encBits encSigmaThreeWitness
                  (cs.1, ⟨u.1, v.1, w.1⟩))
                (cE₁ * F (T x.length) + cE₂) = true) ∧
        ¬ (∃ p : {p : List Bool // p.length ≤ ℓB x.length},
          ∀ q : {q : List Bool // q.length ≤ ℓB x.length},
            RADetVerify MB x
              (Turing.MultiTapeTM.encPair Turing.MultiTapeTM.encBits
                (Turing.MultiTapeTM.encPair Turing.MultiTapeTM.encBits Turing.MultiTapeTM.encBits)
                (cs.1, (p.1, q.1)))
              (cB₁ * F (T x.length) + cB₂) = true) := by
    intro _
    simp only [A₀, Set.mem_ofPred_eq, hAspec x]
    constructor
    · rintro ⟨c, hc, ⟨u, hu, hE⟩, hnotB⟩
      refine ⟨⟨c, hc⟩, ⟨⟨u, hu⟩, fun v => ?_⟩, ?_⟩
      · obtain ⟨w, hw, hwE⟩ := hE v.1 v.2
        exact ⟨⟨w, hw⟩, hwE⟩
      · rintro ⟨⟨p, hp⟩, hq⟩
        exact hnotB ((hBspec x c hc).mpr ⟨p, hp, fun q hq' => hq ⟨q, hq'⟩⟩)
    · rintro ⟨⟨c, hc⟩, ⟨⟨u, hu⟩, hE⟩, hnotp⟩
      refine ⟨c, hc, ⟨u, hu, fun v hv => ?_⟩, ?_⟩
      · obtain ⟨⟨w, hw⟩, hwE⟩ := hE ⟨v, hv⟩
        exact ⟨w, hw, hwE⟩
      · rintro hBc
        rw [hBspec x c hc] at hBc
        obtain ⟨p, hp, hq⟩ := hBc
        exact hnotp ⟨⟨p, hp⟩, fun q => hq q.1 q.2⟩
  have hsel := selectorBit_composition
    (α := Unit)
    (C := {c : List Bool // c.length ≤ s x.length})
    (U := {u : List Bool // u.length ≤ ℓE x.length})
    (V := {v : List Bool // v.length ≤ ℓE x.length})
    (W := {w : List Bool // w.length ≤ ℓE x.length})
    (P := {p : List Bool // p.length ≤ ℓB x.length})
    (Q := {q : List Bool // q.length ≤ ℓB x.length})
    (A := A₀)
    (E := fun (_ : Unit) (cs : {c : List Bool // c.length ≤ s x.length}) u v w =>
      RADetVerify ME x
        (Turing.MultiTapeTM.encPair Turing.MultiTapeTM.encBits encSigmaThreeWitness
          (cs.1, ⟨u.1, v.1, w.1⟩))
        (cE₁ * F (T x.length) + cE₂))
    (B := fun (_ : Unit) (cs : {c : List Bool // c.length ≤ s x.length}) p q =>
      RADetVerify MB x
        (Turing.MultiTapeTM.encPair Turing.MultiTapeTM.encBits
          (Turing.MultiTapeTM.encPair Turing.MultiTapeTM.encBits Turing.MultiTapeTM.encBits)
          (cs.1, (p.1, q.1)))
        (cB₁ * F (T x.length) + cB₂))
    hiff ()
  simp only [A₀, Set.mem_ofPred_eq] at hsel
  exact hsel

end ConditionalReductions

end Cslib.Complexity
