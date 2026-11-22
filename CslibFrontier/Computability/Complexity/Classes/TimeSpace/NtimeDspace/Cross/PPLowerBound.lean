/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cross.Corollaries
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cross.CountingFinal

/-!
# Corollary 1.2 (iv): PP linear-time lower bound

This module proves the unbounded-error probabilistic time lower bound of Corollary 1.2 (iv)
against the stable simulation interface `PPSimulation`:

There is a language `L ∈ DSPACE[n]` such that every probabilistic machine deciding `L` or `Lᶜ`
with unbounded error (all coin branches halting) takes, for some `C ≥ 1`, at least
`n·⌊√⌊log₂ n⌋⌋ / C` steps on some input of every large length `n`.

Writing this against `PPSimulation` ensures that pipeline refactors cannot break it mid-way.

## Main definitions

* `PPSimulation`: the stable interface hypothesis that `PPTIME[t] ⊆ DSPACE[t / √log t]`.

## Main results

* `pptime_lower_bound_of_simulation`: the lower bound for any probabilistic machine from
`PPSimulation`.
* `exists_dspace_linear_pptime_lower_bound`: Corollary 1.2 (iv) lower bound statement.

## References

* The paper (`separating-ntime-from-space.tex`), §1, Corollary 1.2 (iv) (`cor:sep`).
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.Cross

open Filter Cslib Cslib.Complexity _root_.Turing _root_.Turing.MultiTapeTM

/-- The stable interface hypothesis for `PPTIME` simulation:
every language in `PPTIME[t]` is decided in simultaneous time `2^(C·SqrtLog t(n))` and
space `C·SqrtLog t(n)`. -/
def PPSimulation : Prop :=
  ∀ (t : ℕ → ℕ), (∀ n, n ≤ t n) →
    ∀ {A : Set (List Bool)}, A ∈ PPTIME encBits t → DecidedInSqrtLog t A

/-- From `PPSimulation`, every probabilistic machine deciding `hardLanguage` or its complement
with unbounded error runs for more than `n·⌊√⌊log₂ n⌋⌋ / C` steps on some input of every large `n`.
-/
theorem pptime_lower_bound_of_simulation (h : PPSimulation) {k : ℕ} {State : Type}
    [Finite State] (ptm : MultiTapePTM k Bool State) {B : Set (List Bool)}
    (hB : B = hardLanguage ∨ B = hardLanguageᶜ)
    (hdec : ∀ x, ∃ T,
      (∀ final ∈ (ProbComp.eval (ptm.runClosedConfigFrom T (ptm.initialConfig x))).support,
        final.tapes.state = none) ∧
      (x ∈ B ↔ 1 / 2 < ProbComp.eval (ptm.runClosed T x) [true])) :
    ∃ C, 1 ≤ C ∧ ∀ᶠ n in atTop,
      ∃ x : List Bool, x.length = n ∧
        ¬ (∀ final ∈ (ProbComp.eval (ptm.runClosedConfigFrom (n * Nat.sqrt n.log2 / C)
            (ptm.initialConfig x))).support,
            final.tapes.state = none) := by
  classical
  by_contra hcon
  push Not at hcon
  -- the minimal halting clock `T(x)` for each input `x`
  have hex (x : List Bool) : ∃ T,
      (∀ final ∈ (ProbComp.eval (ptm.runClosedConfigFrom T (ptm.initialConfig x))).support,
        final.tapes.state = none) ∧
      (x ∈ B ↔ 1 / 2 < ProbComp.eval (ptm.runClosed T x) [true]) := hdec x
  set T : ℕ → ℕ := fun n => max (maxOnLength (fun x => Nat.find (hex x)) n) n
  have hrun (x : List Bool) :
      (∀ final ∈ (ProbComp.eval (ptm.runClosedConfigFrom (T x.length)
          (ptm.initialConfig x))).support,
        final.tapes.state = none) ∧
      (x ∈ B ↔ 1 / 2 < ProbComp.eval (ptm.runClosed (T x.length) x) [true]) := by
    have hfind := Nat.find_spec (hex x)
    have hle : Nat.find (hex x) ≤ T x.length :=
      (le_maxOnLength (fun x => Nat.find (hex x)) x).trans (le_max_left _ _)
    refine ⟨?_, ?_⟩
    · have hhalt := (halted_support_iff ptm x _).mp hfind.1
      exact (halted_support_iff ptm x _).mpr (halted_mono ptm x hle hhalt)
    · rw [hfind.2]
      have hprob : ProbComp.eval (ptm.runClosed (Nat.find (hex x)) x) =
                   ProbComp.eval (ptm.runClosed (T x.length) x) :=
        (ptm.eval_runClosed_eq_of_halted x hle hfind.1).symm
      rw [← hprob]
  have hTn : ∀ n, n ≤ T n := fun n => le_max_right _ _
  have hBT : B ∈ PPTIME encBits T := by
    refine ⟨1, 0, k, State, inferInstance, ptm, fun x => ?_⟩
    simp only [encBits_apply, one_mul, add_zero]
    exact hrun x
  obtain ⟨C₀, hC₀⟩ := h T hTn hBT
  -- so `hardLanguage ∈ DSPACE[SqrtLog T* + log n]`
  set f : ℕ → ℕ := fun n => SqrtLog (T n) + n.log2 + 1 with hf
  have hLf : hardLanguage ∈ DSPACE encBits f := by
    rcases hB with rfl | rfl
    · refine mem_DSPACE_iff.mpr ⟨C₀, 0, _, ComputableInTimeAndSpace.mono hC₀ (fun _ => le_rfl)
        fun a => ?_⟩
      simp only [encBits_apply, hf, add_zero]
      exact Nat.mul_le_mul_left _ (by omega)
    · obtain ⟨c, t', hc⟩ := exists_decidable_compl hC₀
      rw [compl_compl] at hc
      refine mem_DSPACE_iff.mpr ⟨c * (C₀ + 1), 0, t', ComputableInTimeAndSpace.mono hc
        (fun _ => le_rfl) fun a => ?_⟩
      simp only [encBits_apply, hf, add_zero]
      rw [Nat.mul_assoc]
      refine Nat.mul_le_mul_left c ?_
      nlinarith
  -- and `f` is frequently `o(n)`
  refine setOf_spaceDiagonal_notMem_DSPACE_of_frequently (f := f) (G := fun n => n)
    (fun _ => le_rfl) (fun c => ?_) hLf
  have hfreq := hcon (4 * c + 4) (by omega)
  have hr : ∀ᶠ n : ℕ in atTop, 4 * c + 4 ≤ Nat.sqrt n.log2 :=
    tendsto_atTop.mp tendsto_sqrt_log2 _
  refine (hfreq.and_eventually (hr.and (sqrtLog_sublinear (8 * c + 8)))).mono ?_
  rintro n ⟨hall, hrn, _hsl⟩
  set r := Nat.sqrt n.log2 with _hr_def
  have hr0 : 0 < r := by omega
  have htime : maxOnLength (fun x => Nat.find (hex x)) n ≤ n * r / (4 * c + 4) := by
    refine maxOnLength_le fun x hx => ?_
    have := hall x hx
    refine Nat.find_le ⟨this, ?_⟩
    have hle : Nat.find (hex x) ≤ n * r / (4 * c + 4) ∨ n * r / (4 * c + 4) ≤ Nat.find (hex x) :=
        le_total _ _
    rcases hle with h1 | h2
    · have hfind := Nat.find_spec (hex x)
      have hprob := ptm.eval_runClosed_eq_of_halted x h1 hfind.1
      rw [hprob]
      exact hfind.2
    · have hfind := Nat.find_spec (hex x)
      have hprob := (ptm.eval_runClosed_eq_of_halted x h2 this).symm
      rw [hprob]
      exact hfind.2
  have e₁ : n * r / (4 * c + 4) / r = n / (4 * c + 4) := by
    rw [Nat.div_div_eq_div_mul, Nat.mul_div_mul_right _ _ hr0]
  have hTle : T n / r ≤ n / (4 * c + 4) + n / r := by
    rcases le_total (maxOnLength (fun x => Nat.find (hex x)) n) n with hle | hle
    · have hTeq : T n = n := Nat.max_eq_right hle
      rw [hTeq]
      exact Nat.le_add_left _ _
    · have hTeq : T n = maxOnLength (fun x => Nat.find (hex x)) n := Nat.max_eq_left hle
      rw [hTeq]
      exact (Nat.div_le_div_right htime).trans (e₁ ▸ Nat.le_add_right _ _)
  have hSqrtT : SqrtLog (T n) ≤ n / (4 * c + 4) + n / r + 1 :=
    (sqrtLog_le_div_of_le (hTn n) hr0).trans (Nat.add_le_add_right hTle 1)
  have hq₁ : 4 * (c * (n / (4 * c + 4))) ≤ n := by
    have := Nat.div_mul_le_self n (4 * c + 4)
    nlinarith
  have hq₂ : 4 * (c * (n / r)) ≤ n := by
    have : n / r ≤ n / (4 * c + 4) := Nat.div_le_div_left hrn (by omega)
    nlinarith
  have hlog := log2_add_one_le_sqrtLog n
  have hq₃ : 4 * (c * SqrtLog n + 2 * c) ≤ n := by nlinarith
  have hfn : c * f n + c ≤ c * (n / (4 * c + 4)) + c * (n / r) + (c * SqrtLog n + 2 * c) := by
    have := Nat.mul_le_mul_left c hSqrtT
    have := Nat.mul_le_mul_left c hlog
    simp only [hf]
    nlinarith
  show c * f n + c ≤ n
  omega

/-- Unconditional proof of `PPSimulation` from the crossing simulation of Theorem 7.1. -/
theorem ppSimulation : PPSimulation := fun _t ht _ hA =>
  pptime_decided Crossing.cubeClockedBits ht hA

/-- **Corollary 1.2 (iv), PP Lower Bound**:
There is a language in `DSPACE[n]` such that every probabilistic machine deciding it
or its complement with unbounded error (every coin branch halting) has a constant `C ≥ 1`
such that, for all large `n`, it runs for more than `n · ⌊√⌊log₂ n⌋⌋ / C` steps on some
input of length `n`. -/
theorem exists_dspace_linear_pptime_lower_bound :
    ∃ L : Set (List Bool), L ∈ DSPACE encBits (fun n => n) ∧
      ∀ (k : ℕ) (State : Type) [Finite State] (ptm : MultiTapePTM k Bool State)
        (B : Set (List Bool)), (B = L ∨ B = Lᶜ) →
        (∀ x, ∃ T,
          (∀ final ∈ (ProbComp.eval (ptm.runClosedConfigFrom T (ptm.initialConfig x))).support,
            final.tapes.state = none) ∧
          (x ∈ B ↔ 1 / 2 < ProbComp.eval (ptm.runClosed T x) [true])) →
        ∃ C, 1 ≤ C ∧ ∀ᶠ n in atTop,
          ∃ x : List Bool, x.length = n ∧
            ¬ (∀ final ∈ (ProbComp.eval (ptm.runClosedConfigFrom (n * Nat.sqrt n.log2 / C)
                (ptm.initialConfig x))).support,
                final.tapes.state = none) :=
  ⟨hardLanguage, hardLanguage_mem_DSPACE, fun _ _ _ ptm _ hB hdec =>
    pptime_lower_bound_of_simulation ppSimulation ptm hB hdec⟩

end Cslib.Complexity.NtimeDspace.Cross

namespace Cslib.Complexity.NtimeDspace.Crossing

/-- **Corollary 1.2 (iv), PP Lower Bound**:
There is a language in `DSPACE[n]` such that every probabilistic machine deciding it
or its complement with unbounded error (every coin branch halting) has a constant `C ≥ 1`
such that, for all large `n`, it runs for more than `n · ⌊√⌊log₂ n⌋⌋ / C` steps on some
input of length `n`. -/
abbrev exists_dspace_linear_pptime_lower_bound :=
  NtimeDspace.Cross.exists_dspace_linear_pptime_lower_bound

end Cslib.Complexity.NtimeDspace.Crossing
