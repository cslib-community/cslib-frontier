/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cross.GeneralFinal
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cross.PPLowerBound

/-!
# Nondeterministic time in sublinear deterministic space

Every nondeterministic multitape Turing machine running in time `t(n) ≥ n` can be simulated
deterministically in space `O(t / √log t)`, in time `2 ^ O(t / √log t)`; `t` need not be
constructible ([Cruz2026], Theorem 1.1). With the space hierarchy theorem
(`Cslib.Complexity.DSPACE_ssubset_DSPACE`) this separates nondeterministic linear time from
deterministic linear space, `NTIME[n] ⊊ DSPACE[n]` (Corollary 1.2). The simulation computes every
bit of the number of accepting computations, so the same bound holds for unbounded-error and
bounded-error probabilistic time (Theorem 7.1), and `PPTIME[n] ⊊ DSPACE[n]`.

Machines are the multitape machines of `Cslib.Complexity.NTIME`, `PPTIME`, `BPTIME`, `DSPACE`
and `NSPACE`, on bit words (`Turing.MultiTapeTM.encBits`). The bound `t / √log t` is written
`t n / ⌊√⌊log₂ (t n)⌋⌋ + 1`; the `+ 1` keeps it positive when `⌊√⌊log₂ (t n)⌋⌋ = 0`.

The proof lives in `Cslib.Complexity.NtimeDspace` and follows the paper. The number of accepting
computations of a machine is a sum, over the schedules of its head movements, of values of sparse
networks on blocks of `O(t / log t)` steps (§2). Each value is computed by evaluating, depth
first and one bit at a time, an integer formula built from signed decompositions of walks on the
Boolean cube (§§3–6, `Cslib.Complexity.NtimeDspace.Cube`), by a program whose intermediate values
are below `2 ^ O(t / √log t)` (`Cslib.Complexity.NtimeDspace.ProgLang`). Doubling clocks detect
when every computation has halted, so `t` need not be constructible
(`Cslib.Complexity.NtimeDspace.Cross.generalSimulation`).

## Main results

* `Cslib.Complexity.exists_decidableInTimeAndSpace_of_mem_NTIME_div_sqrt_log`: Theorem 1.1, one
  machine in simultaneous time `2 ^ O(t / √log t)` and space `O(t / √log t)`.
* `Cslib.Complexity.NTIME_subset_DSPACE_div_sqrt_log`: Theorem 1.1 as a class inclusion.
* `Cslib.Complexity.NTIME_ssubset_DSPACE`, `Cslib.Complexity.NTIME_ssubset_NSPACE`,
  `Cslib.Complexity.NTIME_id_ssubset_DSPACE_id`: Corollary 1.2 (i).
* `Cslib.Complexity.NTIME_mul_sqrt_log_subset_DSPACE`: Corollary 1.2 (ii).
* `Cslib.Complexity.exists_mem_DSPACE_id_ntime_lower_bound`: Corollary 1.2 (iii).
* `Cslib.Complexity.PPTIME_subset_DSPACE_div_sqrt_log`,
  `Cslib.Complexity.BPTIME_subset_DSPACE_div_sqrt_log`: Theorem 7.1 for `PPTIME` and `BPTIME`.
* `Cslib.Complexity.PPTIME_ssubset_DSPACE`, `Cslib.Complexity.PPTIME_id_ssubset_DSPACE_id`,
  `Cslib.Complexity.BPTIME_id_ssubset_DSPACE_id`,
  `Cslib.Complexity.exists_mem_DSPACE_id_pptime_lower_bound`: Corollary 1.2 (iv).

Theorem 7.1 for `⊕TIME`, `Mod_qTIME` and `C₌TIME`, Corollary 7.2 (counting 3-SAT) and Remark 8.3
(relativization) are in `Cslib.Complexity.NtimeDspace.Cross`.

## References

* [C. Cruz, *Separating Nondeterministic Time from Deterministic Space*][Cruz2026]
* [J. Hopcroft, W. Paul, L. Valiant, *On Time Versus Space*][HopcroftPaulValiant1977]
-/

public section

namespace Cslib.Complexity

open _root_.Turing.MultiTapeTM NtimeDspace.Cross NtimeDspace.Crossing

/-- **Theorem 1.1** ([Cruz2026]). For every `t(n) ≥ n`, not necessarily constructible, every
language in `NTIME[t]` is decided by one deterministic machine in simultaneous time
`2 ^ (C * (t / ⌊√⌊log₂ t⌋⌋ + 1))` and space `C * (t / ⌊√⌊log₂ t⌋⌋ + 1)`. -/
theorem exists_decidableInTimeAndSpace_of_mem_NTIME_div_sqrt_log (t : ℕ → ℕ) (ht : ∀ n, n ≤ t n)
    {A : Set (List Bool)} (hA : A ∈ NTIME encBits t) :
    ∃ C, DecidableInTimeAndSpace A encBits
      (fun a => 2 ^ (C * (t a.length / Nat.sqrt (t a.length).log2 + 1)))
      (fun a => C * (t a.length / Nat.sqrt (t a.length).log2 + 1)) :=
  generalSimulation t ht hA

/-- **Theorem 1.1** ([Cruz2026]), as a class inclusion: `NTIME[t] ⊆ DSPACE[t / √log t]` for
every `t(n) ≥ n`. -/
theorem NTIME_subset_DSPACE_div_sqrt_log {t : ℕ → ℕ} (ht : ∀ n, n ≤ t n) :
    NTIME encBits t ⊆ DSPACE encBits (fun n => t n / Nat.sqrt (t n).log2 + 1) :=
  ntime_subset_dspace_sqrtLog_of_general generalSimulation ht

/-- **Corollary 1.2 (i)** ([Cruz2026]): `NTIME[t] ⊊ DSPACE[t]` for every space-constructible
`t(n) ≥ n`. -/
theorem NTIME_ssubset_DSPACE {t : ℕ → ℕ} (hsc : SpaceConstructible t) (ht : ∀ n, n ≤ t n) :
    NTIME encBits t ⊂ DSPACE encBits t :=
  ntime_ssubset_dspace_of_general generalSimulation hsc ht

/-- **Corollary 1.2 (i)** ([Cruz2026]), nondeterministic space: `NTIME[t] ⊊ NSPACE[t]` for every
space-constructible `t(n) ≥ n`. -/
theorem NTIME_ssubset_NSPACE {t : ℕ → ℕ} (hsc : SpaceConstructible t) (ht : ∀ n, n ≤ t n) :
    NTIME encBits t ⊂ NSPACE encBits t :=
  ntime_ssubset_nspace_of_general generalSimulation hsc ht

/-- **Corollary 1.2 (i)** ([Cruz2026]) in linear time: `NTIME[n] ⊊ DSPACE[n]`. -/
theorem NTIME_id_ssubset_DSPACE_id : NTIME encBits (fun n => n) ⊂ DSPACE encBits (fun n => n) :=
  NTIME_ssubset_DSPACE spaceConstructible_id fun _ => le_rfl

/-- **Corollary 1.2 (ii)** ([Cruz2026]): `NTIME[t · √log t] ⊆ DSPACE[t]` for every `t(n) ≥ n`,
with `√log t = ⌊√⌊log₂ (t n)⌋⌋`. -/
theorem NTIME_mul_sqrt_log_subset_DSPACE {t : ℕ → ℕ} (ht : ∀ n, n ≤ t n) :
    NTIME encBits (fun n => t n * Nat.sqrt (Nat.log2 (t n))) ⊆ DSPACE encBits t :=
  ntime_mul_sqrtLog_subset_dspace generalSimulation ht

/-- **Corollary 1.2 (iii)** ([Cruz2026]): a language in `DSPACE[n]` such that every
nondeterministic machine deciding it or its complement takes, for some `C ≥ 1`, at least
`n · ⌊√⌊log₂ n⌋⌋ / C` steps on some input of every large length `n`. -/
theorem exists_mem_DSPACE_id_ntime_lower_bound :
    ∃ L : Set (List Bool), L ∈ DSPACE encBits (fun n => n) ∧
      ∀ (k : ℕ) (State : Type) [Finite State] (ntm : _root_.Turing.MultiTapeNTM k Bool State)
        (B : Set (List Bool)), (B = L ∨ B = Lᶜ) →
        (∀ x, (∃ t, ntm.RunsInTime x t) ∧ (x ∈ B ↔ ntm.Accepts x)) →
        ∃ C, 1 ≤ C ∧ ∀ᶠ n in Filter.atTop,
          ∃ x : List Bool, x.length = n ∧ ¬ ntm.RunsInTime x (n * Nat.sqrt n.log2 / C) :=
  exists_dspace_linear_ntime_lower_bound generalSimulation

/-- **Theorem 7.1 for `PPTIME`** ([Cruz2026]): `PPTIME[t] ⊆ DSPACE[t / √log t]` for every
`t(n) ≥ n`. -/
theorem PPTIME_subset_DSPACE_div_sqrt_log {t : ℕ → ℕ} (ht : ∀ n, n ≤ t n) :
    PPTIME encBits t ⊆ DSPACE encBits (fun n => t n / Nat.sqrt (t n).log2 + 1) :=
  pptime_subset_dspace cubeClockedBits ht

/-- **Theorem 7.1 for `BPTIME`** ([Cruz2026]): `BPTIME[t] ⊆ DSPACE[t / √log t]` for every
`t(n) ≥ n`. -/
theorem BPTIME_subset_DSPACE_div_sqrt_log {t : ℕ → ℕ} (ht : ∀ n, n ≤ t n) :
    BPTIME encBits t ⊆ DSPACE encBits (fun n => t n / Nat.sqrt (t n).log2 + 1) :=
  bptime_subset_dspace cubeClockedBits ht

/-- **Corollary 1.2 (iv)** ([Cruz2026]): `PPTIME[t] ⊊ DSPACE[t]` for every space-constructible
`t(n) ≥ n`. -/
theorem PPTIME_ssubset_DSPACE {t : ℕ → ℕ} (hsc : SpaceConstructible t) (ht : ∀ n, n ≤ t n) :
    PPTIME encBits t ⊂ DSPACE encBits t :=
  lt_of_le_of_lt (PPTIME_subset_DSPACE_div_sqrt_log ht)
    (DSPACE_ssubset_DSPACE hsc (fun n => (Nat.log2_le_self n).trans (ht n))
      (eventually_sqrtLog_comp_gap ht))

/-- **Corollary 1.2 (iv)** ([Cruz2026]) in linear time: `PPTIME[n] ⊊ DSPACE[n]`. -/
theorem PPTIME_id_ssubset_DSPACE_id :
    PPTIME encBits (fun n => n) ⊂ DSPACE encBits (fun n => n) :=
  PPTIME_ssubset_DSPACE spaceConstructible_id fun _ => le_rfl

/-- **Corollary 1.2 (iv)** ([Cruz2026]) for bounded error: `BPTIME[n] ⊊ DSPACE[n]`. -/
theorem BPTIME_id_ssubset_DSPACE_id :
    BPTIME encBits (fun n => n) ⊂ DSPACE encBits (fun n => n) :=
  lt_of_le_of_lt (BPTIME_subset_DSPACE_div_sqrt_log fun _ => le_rfl)
    (DSPACE_ssubset_DSPACE spaceConstructible_id (fun n => Nat.log2_le_self n)
      (eventually_sqrtLog_comp_gap fun _ => le_rfl))

/-- **Corollary 1.2 (iv)** ([Cruz2026]), the lower bound of (iii) for probabilistic machines: the
language of `exists_mem_DSPACE_id_ntime_lower_bound` is such that every probabilistic machine
deciding it or its complement with unbounded error, all of whose runs halt, has, for some
`C ≥ 1`, a run longer than `n · ⌊√⌊log₂ n⌋⌋ / C` on some input of every large length `n`. -/
theorem exists_mem_DSPACE_id_pptime_lower_bound :
    ∃ L : Set (List Bool), L ∈ DSPACE encBits (fun n => n) ∧
      ∀ (k : ℕ) (State : Type) [Finite State] (ptm : _root_.Turing.MultiTapePTM k Bool State)
        (B : Set (List Bool)), (B = L ∨ B = Lᶜ) →
        (∀ x, ∃ T,
          (∀ final ∈ (ProbComp.eval (ptm.runClosedConfigFrom T (ptm.initialConfig x))).support,
            final.tapes.state = none) ∧
          (x ∈ B ↔ 1 / 2 < ProbComp.eval (ptm.runClosed T x) [true])) →
        ∃ C, 1 ≤ C ∧ ∀ᶠ n in Filter.atTop,
          ∃ x : List Bool, x.length = n ∧
            ¬ (∀ final ∈ (ProbComp.eval (ptm.runClosedConfigFrom (n * Nat.sqrt n.log2 / C)
                (ptm.initialConfig x))).support,
                final.tapes.state = none) :=
  ⟨hardLanguage, hardLanguage_mem_DSPACE, fun _ _ _ ptm _ hB hdec =>
    pptime_lower_bound_of_simulation ppSimulation ptm hB hdec⟩

end Cslib.Complexity
