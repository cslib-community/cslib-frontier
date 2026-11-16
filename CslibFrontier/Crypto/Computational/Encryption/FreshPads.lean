/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Control.Monad.Memoize
public import CslibFrontier.Languages.Probabilistic.UntilBad.Flag
public import CslibFrontier.Probability.BitString

/-!
# Fresh pads for a one-block random-IV cipher over a random function

A randomized one-block counter-mode cipher over a function `f` encrypts a plaintext `p` as
`r ++ (f r ⊕ p)` for a fresh `m`-bit IV `r`. When `f` is a random function, sampled lazily, the
encryption oracle is `lazyPadOracle`: the pad of an IV is drawn once and remembered. Replacing the
remembered pad by a fresh one at every query gives `freshPadOracle`. The two oracles differ only
when an IV repeats, so after `Q` queries the probability of any final event moves by at most
`Q.choose 2 / 2 ^ m` (`lazyPadOracle_bind_apply_le`). This is the step from the "faithful" to the
"forgetful gnome" in [BonehShoup2023], Section 5.4.1 (proof of Theorem 5.2, Games 2 and 3,
pp. 186–187), and the step (9.13) of the proof of Theorem 9.3 (Section 9.4.4, p. 375).

Both oracles are generic in what is encrypted: a query `msg` is answered only when `valid msg`;
it draws coins `a ← coins msg`, encrypts the plaintext `plaintext msg a`, and records
`record msg a r pad` in a log of type `σ`. The state is the random-function cache, the log and a
flag that is raised when an IV repeats.

## Main definitions

* `Cslib.Crypto.lazyPadOracle`: the encryption oracle over a lazily sampled random function.
* `Cslib.Crypto.freshPadOracle`: the same oracle with a fresh pad at every query.

## Main results

* `Cslib.Crypto.lazyPadOracle_bind_apply_le`: for a program with at most `Q` queries, any final
  event has probability under `lazyPadOracle` at most its probability under `freshPadOracle` plus
  `Q.choose 2 / 2 ^ m`.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 5.4.1 (pp. 186–187) and Section 9.4.4 (p. 375).
-/

public section

namespace Cslib.Crypto

open Cslib.Probability OracleComp
open scoped ENNReal

variable {α σ : Type}

/-- The encryption oracle of a one-block random-IV cipher over a lazily sampled random function
with `m`-bit IVs and pads. A query `msg` with `valid msg` draws coins `a ← coins msg` and an IV
`r`, looks up or draws the pad of `r` in the cache, answers `r ++ (pad ⊕ plaintext msg a)`, adds
`record msg a r pad` to the log, and raises the flag if `r` was already in the cache. Any other
query is answered with `[]`. -/
@[expose]
noncomputable def lazyPadOracle (m : ℕ) (valid : List Bool → Bool) (coins : List Bool → PMF α)
    (plaintext : List Bool → α → List Bool)
    (record : List Bool → α → List Bool → List Bool → σ → σ) (request : Unit × List Bool) :
    StateT ((List (List Bool × List Bool) × σ) × Bool) PMF (List Bool) :=
  fun st =>
    if valid request.2 then
      (coins request.2).bind fun a =>
        (BitString.uniformList m).bind fun r =>
          (memoize (fun _ => BitString.uniformList m) r st.1.1).map fun res =>
            (r ++ List.zipWith xor (res.1.take m) (plaintext request.2 a),
              ((res.2, record request.2 a r res.1 st.1.2),
                st.2 || (st.1.1.lookup r).isSome))
    else
      PMF.pure ([], st)

/-- `lazyPadOracle` with a fresh pad at every query: the pad is drawn anew even when the IV is in
the cache, and `(r, pad)` is added to the cache. -/
@[expose]
noncomputable def freshPadOracle (m : ℕ) (valid : List Bool → Bool) (coins : List Bool → PMF α)
    (plaintext : List Bool → α → List Bool)
    (record : List Bool → α → List Bool → List Bool → σ → σ) (request : Unit × List Bool) :
    StateT ((List (List Bool × List Bool) × σ) × Bool) PMF (List Bool) :=
  fun st =>
    if valid request.2 then
      (coins request.2).bind fun a =>
        (BitString.uniformList m).bind fun r =>
          (BitString.uniformList m).map fun pad =>
            (r ++ List.zipWith xor (pad.take m) (plaintext request.2 a),
              (((r, pad) :: st.1.1, record request.2 a r pad st.1.2),
                st.2 || (st.1.1.lookup r).isSome))
    else
      PMF.pure ([], st)

section

variable (m : ℕ) (valid : List Bool → Bool) (coins : List Bool → PMF α)
  (plaintext : List Bool → α → List Bool)
  (record : List Bool → α → List Bool → List Bool → σ → σ)

private theorem isFlagMonotone_lazyPadOracle :
    OracleComp.IsFlagMonotone (lazyPadOracle m valid coins plaintext record) := by
  intro request s x hx
  unfold lazyPadOracle at hx
  by_cases hv : valid request.2 = true
  · simp only [hv, ↓reduceIte, Bool.true_or] at hx
    obtain ⟨a, -, hx⟩ := (PMF.mem_support_bind_iff _ _ _).mp hx
    obtain ⟨r, -, hx⟩ := (PMF.mem_support_bind_iff _ _ _).mp hx
    obtain ⟨res, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hx
    rfl
  · simp only [hv, Bool.false_eq_true, ↓reduceIte, PMF.mem_support_pure_iff] at hx
    subst x
    rfl

private theorem isFlagMonotone_freshPadOracle :
    OracleComp.IsFlagMonotone (freshPadOracle m valid coins plaintext record) := by
  intro request s x hx
  unfold freshPadOracle at hx
  by_cases hv : valid request.2 = true
  · simp only [hv, ↓reduceIte, Bool.true_or] at hx
    obtain ⟨a, -, hx⟩ := (PMF.mem_support_bind_iff _ _ _).mp hx
    obtain ⟨r, -, hx⟩ := (PMF.mem_support_bind_iff _ _ _).mp hx
    obtain ⟨pad, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hx
    rfl
  · simp only [hv, Bool.false_eq_true, ↓reduceIte, PMF.mem_support_pure_iff] at hx
    subst x
    rfl

/-- From an unflagged state the two oracles give every unflagged outcome the same probability. -/
private theorem lazyPadOracle_apply_false (request : Unit × List Bool)
    (s : List (List Bool × List Bool) × σ) (x : List Bool) (s' : List (List Bool × List Bool) × σ) :
    lazyPadOracle m valid coins plaintext record request (s, false) (x, (s', false)) =
      freshPadOracle m valid coins plaintext record request (s, false) (x, (s', false)) := by
  unfold lazyPadOracle freshPadOracle
  simp only [Bool.false_or]
  by_cases hv : valid request.2 = true
  · simp only [hv, ↓reduceIte, PMF.bind_apply]
    refine tsum_congr fun a => congrArg (_ * ·) ?_
    refine tsum_congr fun r => congrArg (_ * ·) ?_
    cases hlookup : s.1.lookup r with
    | some pad₀ =>
      refine ((PMF.apply_eq_zero_iff _ _).mpr fun hx => ?_).trans
        ((PMF.apply_eq_zero_iff _ _).mpr fun hx => ?_).symm <;>
      · obtain ⟨res, -, hres⟩ := (PMF.mem_support_map_iff _ _ _).mp hx
        have h1 := congrArg (fun x => x.2.2) hres
        simp at h1
    | none =>
      have hmem : memoize (fun _ => BitString.uniformList m) r s.1 =
          (BitString.uniformList m).map (fun pad => (pad, (r, pad) :: s.1)) := by
        simp [memoize_of_none, hlookup, PMF.map, Function.comp_def,
          Probability.PMF.monad_bind_eq_bind, Probability.PMF.monad_pure_eq_pure]
      rw [hmem, PMF.map_comp]
      rfl
  · simp [hv]

/-- One fresh-pad query from an unflagged state raises the flag with probability at most
`cache.length / 2 ^ m`. -/
private theorem step_bad_freshPadOracle_le (request : Unit × List Bool)
    (s : List (List Bool × List Bool) × σ) :
    (freshPadOracle m valid coins plaintext record request (s, false)).toOuterMeasure
        {x | OracleComp.FlagBad x.2} ≤
      (s.1.length : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ m) := by
  have hset : {x : List Bool × ((List (List Bool × List Bool) × σ) × Bool) |
      OracleComp.FlagBad x.2} = (fun x : List Bool × ((List (List Bool × List Bool) × σ) × Bool) =>
        x.2.2) ⁻¹' {true} := by
    ext x
    simp [OracleComp.FlagBad]
  rw [hset, ← PMF.toOuterMeasure_map_apply]
  unfold freshPadOracle
  by_cases hv : valid request.2 = true
  · simp only [hv, ↓reduceIte, Bool.false_or, PMF.map_bind, PMF.map_comp, Function.comp_def,
      PMF.bind_const]
    have hmap : ((BitString.uniformList m).bind fun r =>
        PMF.map (fun _ : List Bool => (s.1.lookup r).isSome) (BitString.uniformList m)) =
        (BitString.uniformList m).map fun r => (s.1.lookup r).isSome := by
      simp only [PMF.map, Function.comp_def, PMF.bind_const]
    rw [hmap, PMF.toOuterMeasure_map_apply]
    exact BitString.toOuterMeasure_lookup_uniformList_le m s.1
  · simp only [hv, Bool.false_eq_true, ↓reduceIte, PMF.pure_map]
    rw [PMF.toOuterMeasure_apply_singleton]
    simp

/-- One fresh-pad query adds at most one entry to the cache. -/
private theorem length_cache_freshPadOracle_le (request : Unit × List Bool)
    (st : (List (List Bool × List Bool) × σ) × Bool)
    (x : List Bool × ((List (List Bool × List Bool) × σ) × Bool))
    (hx : x ∈ (freshPadOracle m valid coins plaintext record request st).support) :
    x.2.1.1.length ≤ st.1.1.length + 1 := by
  unfold freshPadOracle at hx
  by_cases hv : valid request.2 = true
  · simp only [hv, ↓reduceIte] at hx
    obtain ⟨a, -, hx⟩ := (PMF.mem_support_bind_iff _ _ _).mp hx
    obtain ⟨r, -, hx⟩ := (PMF.mem_support_bind_iff _ _ _).mp hx
    obtain ⟨pad, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hx
    simp
  · simp only [hv, Bool.false_eq_true, ↓reduceIte, PMF.mem_support_pure_iff] at hx
    subst x
    exact Nat.le_add_right _ _

/-- **Lazy pads against fresh pads.** For a program with at most `Q` encryption queries, started
from the empty cache, the log `log₀` and a lowered flag, every final event has probability under
`lazyPadOracle` at most its probability under `freshPadOracle` plus `Q.choose 2 / 2 ^ m`: the two
oracles agree until an IV repeats, and with fresh pads that happens with probability at most
`Q.choose 2 / 2 ^ m`. -/
theorem lazyPadOracle_bind_apply_le {β : Type}
    {program : ProbOracleComp (fun _ : Unit × List Bool => List Bool) β} {Q : ℕ}
    (hq : program.IsQueryBounded Q) (log₀ : σ)
    (next : β × ((List (List Bool × List Bool) × σ) × Bool) → PMF Bool) :
    ((ProbOracleComp.runWith (lazyPadOracle m valid coins plaintext record) program
        (([], log₀), false)).bind next) true ≤
      ((ProbOracleComp.runWith (freshPadOracle m valid coins plaintext record) program
          (([], log₀), false)).bind next) true + (Q.choose 2 : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ m) := by
  have hiub : ProbOracleComp.IdenticalUntilBad (lazyPadOracle m valid coins plaintext record)
      (freshPadOracle m valid coins plaintext record) OracleComp.FlagBad :=
    ProbOracleComp.IdenticalUntilBad.of_flag (isFlagMonotone_lazyPadOracle m valid coins
      plaintext record) (isFlagMonotone_freshPadOracle m valid coins plaintext record)
      (lazyPadOracle_apply_false m valid coins plaintext record)
  refine (hiub.bind_apply_le program _ next true).trans (add_le_add le_rfl ?_)
  rw [hiub.bad_eq]
  have h := ProbOracleComp.toOuterMeasure_bad_choose_two_le
    (handler := freshPadOracle m valid coins plaintext record) (bad := OracleComp.FlagBad)
    (fun st : (List (List Bool × List Bool) × σ) × Bool => st.1.1.length) ((1 : ℝ≥0∞) / 2 ^ m)
    (fun q st hst => by
      have hst' : st = (st.1, false) := Prod.ext rfl (Bool.eq_false_iff.mpr hst)
      rw [hst']
      exact step_bad_freshPadOracle_le m valid coins plaintext record q st.1)
    (fun q st _ x hx _ => length_cache_freshPadOracle_le m valid coins plaintext record q st x hx)
    hq (s := (([], log₀), false)) (by simp [OracleComp.FlagBad])
  simpa using h

end

end Cslib.Crypto
