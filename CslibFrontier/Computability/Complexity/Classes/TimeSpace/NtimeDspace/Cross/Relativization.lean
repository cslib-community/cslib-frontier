/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Hierarchy.Space
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cross.SqrtLogSublinear
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Oracle.BSAComp
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Oracle.NSimComp
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Oracle.OneQuery

/-!
# Remark 8.3: the separation does not relativize

Oracle machines are CSLib/Complexitylib multi-tape machines over `{0,1}` with a write-only query
tape that counts toward space, erased by each query, and query states answered by successor states
(`Cslib.Complexity.NtimeDspace.Oracle.OracleTM`, `Cslib.Complexity.NtimeDspace.Oracle.OracleNTM`).
The relativized classes `TIMEO`,
`NTIMEO`, `SPACEO` copy Complexitylib's `DTIME`, `NTIME`, `DSPACE` clause for clause and coincide
with them on machines that never use the oracle
(`Cslib.Complexity.NtimeDspace.Oracle.DTIME_eq_oracleFree`,
`Cslib.Complexity.NtimeDspace.Oracle.NTIME_eq_oracleFree`,
`Cslib.Complexity.NtimeDspace.Oracle.DSPACE_eq_oracleFree`). The oracle
is `Cslib.Complexity.NtimeDspace.Oracle.BSA`, the queries `⟨M'⟩ # x # 1^b` such that the machine
described by `M'`
accepts `x` within space `b` (configurations described within `b` bits; see that file for the
relation to the paper's one-binary-tape convention).

The remark's argument, formalized:

1. *One query decides any language in `SPACE[n]` in linear time*:
   `space_subset_dtime_bsa : DSPACE[n] ⊆ TIME^BSA[n]`.
2. *Deterministic time is within nondeterministic time and within space*:
   `time_subset_ntime_oracle`, `Cslib.Complexity.NtimeDspace.Oracle.TIMEO_subset_SPACEO`.
3. *A space-`s` machine with oracle `BSA` asks queries of length at most `s`, each answerable in
   space `O(s)` without the oracle*: `dspace_bsa_subset_dspace : SPACE^BSA[s] ⊆ SPACE[s]` for
   `s(n) ≥ log₂ n + 1` (`BSA` is decidable in linear space,
   `Cslib.Complexity.NtimeDspace.Oracle.computableInSpace_BSA`,
   and `Cslib.Complexity.NtimeDspace.Oracle.SPACEO_subset_DSPACE`).
4. *The space hierarchy theorem*: `SPACE[n/√log n] ⊊ SPACE[n]`
   (Complexitylib's `Cslib.Complexity.DSPACE_ssubset_DSPACE`).

5. *Trying the choice strings one at a time*: `ntime_subset_dspace_oracle`:
   `NTIME^A[n] ⊆ SPACE^A[n]` for every oracle `A` decidable in linear space, in particular for `BSA`
   (`Cslib.Complexity.NtimeDspace.Oracle.NTIMEO_subset_DSPACE`: the choice numbers `r < B^T` are
   tried one at a time, each by a universal simulation of the choice run).

Hence `relativization_equalities_bsa`: `TIME^BSA[n] = NTIME^BSA[n] = SPACE^BSA[n]` (and
`relativization_collapse_bsa`: both equal `SPACE[n]`), and `separation_does_not_relativize_bsa`:
the relativized Theorem 1.1, `NTIME^BSA[n] ⊆ SPACE^BSA[n/√log n]`, is false.

As in the paper, the final step goes through step 3 at the sublinear bound `n/√log n` and the
unrelativized space hierarchy theorem, and step 5 is stated for oracles decidable in linear space.

## Main results

* `space_subset_dtime_bsa`, `time_subset_ntime_oracle`, `dspace_bsa_subset_dspace`.
* `ntime_subset_dspace_oracle`: `NTIME^A[n] ⊆ SPACE^A[n]` for `A` decidable in linear space.
* `relativization_equalities_bsa`: `TIME^BSA[n] = NTIME^BSA[n]` and `NTIME^BSA[n] = SPACE^BSA[n]`.
* `relativization_collapse_bsa`: `TIME^BSA[n] = SPACE^BSA[n]`, `SPACE^BSA[n] = SPACE[n]` and
  `SPACE[n] ⊆ NTIME^BSA[n]`.
* `separation_does_not_relativize_bsa`: `¬ NTIME^BSA[n] ⊆ SPACE^BSA[n/√log n]`.
-/

public section

namespace Cslib.Complexity.NtimeDspace.Cross.Relativization

open NtimeDspace.Oracle Cslib.Complexity _root_.Turing.MultiTapeTM

/-- **Step 2.** Deterministic oracle time is within nondeterministic oracle time, for every
oracle. -/
theorem time_subset_ntime_oracle (A : Set (List Bool)) (t : ℕ → ℕ) : TIMEO A t ⊆ NTIMEO A t :=
  TIMEO_subset_NTIMEO A t

/-- **Step 1.** One query to `BSA` decides any language in linear space, in linear time. -/
theorem space_subset_dtime_bsa : DSPACE encBits (fun n => n) ⊆ TIMEO BSA (fun n => n) :=
  DSPACE_subset_TIMEO_BSA

/-- `SPACE[n] ⊆ NTIME^BSA[n]`. -/
theorem space_subset_ntime_bsa : DSPACE encBits (fun n => n) ⊆ NTIMEO BSA (fun n => n) :=
  space_subset_dtime_bsa.trans (time_subset_ntime_oracle BSA _)

/-- **Step 3.** A deterministic machine with oracle `BSA` working within space `O(s)`, query tape
included, is simulated without the oracle within space `O(s)`, for `s(n) ≥ log₂ n + 1`. -/
theorem dspace_bsa_subset_dspace {s : ℕ → ℕ} (hlog : ∀ n, n.log2 + 1 ≤ s n) :
    SPACEO BSA s ⊆ DSPACE encBits s :=
  SPACEO_subset_DSPACE computableInSpace_BSA hlog

lemma SPACEO_mono {A : Set (List Bool)} {s₁ s₂ : ℕ → ℕ} (h : ∀ n, s₁ n ≤ s₂ n) :
    SPACEO A s₁ ⊆ SPACEO A s₂ := by
  rintro L ⟨c₁, c₂, k, State, hfin, M, t, hM⟩
  exact ⟨c₁, c₂, k, State, hfin, M, t,
    hM.mono (fun _ => le_rfl) fun x => Nat.add_le_add_right (Nat.mul_le_mul_left _ (h _)) _⟩

/-- `SPACE^BSA[n] = SPACE[n]`. -/
theorem spaceo_bsa_eq_dspace : SPACEO BSA (fun n => n) = DSPACE encBits (fun n => n) := by
  refine Set.Subset.antisymm ?_ (DSPACE_subset_SPACEO BSA _)
  calc SPACEO BSA (fun n => n) ⊆ SPACEO BSA (fun n => n + 1) := SPACEO_mono fun n => by omega
    _ ⊆ DSPACE encBits (fun n => n + 1) :=
        dspace_bsa_subset_dspace fun n => by have := Nat.log2_le_self n; omega
    _ ⊆ DSPACE encBits (fun n => n) := DSPACE_mono_of_le_mul_add (C := 1) fun n => by omega

/-- **Remark 8.3, the collapse:** `TIME^BSA[n] = SPACE^BSA[n] = SPACE[n] ⊆ NTIME^BSA[n]`. -/
theorem relativization_collapse_bsa :
    TIMEO BSA (fun n => n) = SPACEO BSA (fun n => n) ∧
      SPACEO BSA (fun n => n) = DSPACE encBits (fun n => n) ∧
      DSPACE encBits (fun n => n) ⊆ NTIMEO BSA (fun n => n) := by
  refine ⟨Set.Subset.antisymm (TIMEO_subset_SPACEO BSA _) ?_, spaceo_bsa_eq_dspace,
    space_subset_ntime_bsa⟩
  rw [spaceo_bsa_eq_dspace]
  exact space_subset_dtime_bsa

/-- **Step 5.** `NTIME^A[n] ⊆ SPACE^A[n]` for every oracle `A` decidable in linear space: the
choice strings are tried one at a time (and the oracle is not even needed). -/
theorem ntime_subset_dspace_oracle {A : Set (List Bool)}
    (hA : open scoped Classical in
      ComputableInSpace (fun w => decide (w ∈ A)) encBits encBool fun w => w.length) :
    NTIMEO A (fun n => n) ⊆ SPACEO A (fun n => n) :=
  (NTIMEO_subset_DSPACE hA).trans (DSPACE_subset_SPACEO A _)

/-- `NTIME^BSA[n] ⊆ SPACE[n]`. -/
theorem ntime_bsa_subset_dspace : NTIMEO BSA (fun n => n) ⊆ DSPACE encBits (fun n => n) :=
  NTIMEO_subset_DSPACE computableInSpace_BSA

/-- **Remark 8.3, the displayed equality:** `TIME^BSA[n] = NTIME^BSA[n] = SPACE^BSA[n]`. -/
theorem relativization_equalities_bsa :
    TIMEO BSA (fun n => n) = NTIMEO BSA (fun n => n) ∧
      NTIMEO BSA (fun n => n) = SPACEO BSA (fun n => n) := by
  refine ⟨Set.Subset.antisymm (time_subset_ntime_oracle BSA _)
      (ntime_bsa_subset_dspace.trans space_subset_dtime_bsa),
    Set.Subset.antisymm (spaceo_bsa_eq_dspace ▸ ntime_bsa_subset_dspace) ?_⟩
  rw [spaceo_bsa_eq_dspace]
  exact space_subset_ntime_bsa

/-- **Remark 8.3: Theorem 1.1 does not relativize.** Relative to `BSA`, the inclusion
`NTIME[n] ⊆ SPACE[n/√log n]` of Theorem 1.1 fails: `NTIME^BSA[n] ⊄ SPACE^BSA[n/√log n]`, with
the bound `n / ⌊√⌊log₂ n⌋⌋ + 1` of `Cslib.Complexity.NTIME_subset_DSPACE_div_sqrt_log` at
`t(n) = n`. -/
theorem separation_does_not_relativize_bsa :
    ¬ NTIMEO BSA (fun n => n) ⊆ SPACEO BSA (fun n => n / Nat.sqrt n.log2 + 1) := by
  intro h
  have hsub : DSPACE encBits (fun n => n) ⊆ DSPACE encBits SqrtLog :=
    (space_subset_ntime_bsa.trans h).trans (dspace_bsa_subset_dspace log2_add_one_le_sqrtLog)
  have hss : DSPACE encBits SqrtLog ⊂ DSPACE encBits (fun n => n) :=
    DSPACE_ssubset_DSPACE spaceConstructible_id (fun n => Nat.log2_le_self n) sqrtLog_sublinear
  exact hss.2 hsub

end Cslib.Complexity.NtimeDspace.Cross.Relativization
