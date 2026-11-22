/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Space.Nondeterministic
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cross.Hierarchy
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cross.ScaleInterface
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Composition.SmallSpace

/-!
# Corollary 1.2 from Theorem 1.1 for every time bound

All results here are conditional on `GeneralSimulation`, Theorem 1.1 for every `t(n) ≥ n` in
simultaneous time `2^(C·SqrtLog (t n))` and space `C·SqrtLog (t n)`, where
`SqrtLog m = m / ⌊√⌊log₂ m⌋⌋ + 1` (`generalSimulation_of_clocked` derives it from the clocked
counter).

* Theorem 1.1 as a class inclusion: `NTIME[t] ⊆ DSPACE[t / √log t]`
  (`ntime_subset_dspace_sqrtLog_of_general`).
* Corollary 1.2 (i): for space-constructible `t(n) ≥ n`, `NTIME[t] ⊊ DSPACE[t]`,
  `NTIME[t] ⊊ NSPACE[t]` and `NTIME[t] ≠ NSPACE[t]` (`ntime_ssubset_dspace_of_general`,
  `ntime_ssubset_nspace_of_general`, `ntime_ne_nspace_of_general`). `NSPACE` is Complexitylib's
  (`Cslib.Complexity.NSPACE`): one finite-state binary nondeterministic machine, every computation
  prefix within `c₁ * s n + c₂` work cells, every branch halting. Deterministic machines are
  nondeterministic ones (`DSPACE_subset_NSPACE`, through `MultiTapeTM.toMultiTapeNTM`).
* Corollary 1.2 (ii): `NTIME[t·√log t] ⊆ DSPACE[t]` for every `t(n) ≥ n`
  (`ntime_mul_sqrtLog_subset_dspace`), with `√log t = ⌊√⌊log₂ (t n)⌋⌋`.
* Corollary 1.2 (iii): the diagonal language within linear space, `hardLanguage ∈ DSPACE[n]`,
  and every nondeterministic machine deciding it or its complement runs for more than
  `n·⌊√⌊log₂ n⌋⌋ / C` steps on some input of every large length `n`, for some `C ≥ 1`
  (`exists_dspace_linear_ntime_lower_bound`). The proof is the paper's (Appendix A): the machine's
  worst-case running time `T*` puts the language in `NTIME[T*]`, Theorem 1.1 decides it in space
  `O(T* / √log T*)`, and the almost-everywhere hierarchy theorem for a single language
  (`setOf_spaceDiagonal_notMem_DSPACE_of_frequently`) forbids this when `T*` is frequently below
  `n √log n / C` for every `C`.
* The same inclusion and Corollary 1.2 (i) at any scale `D` with `Scale D`, from
  `GeneralSimulationAt D` (`ntime_subset_dspace_of_generalAt`, `ntime_ssubset_dspace_of_generalAt`,
  `ntime_ssubset_nspace_of_generalAt`); other scales, such as `D = RootLog 3`, give other bounds.
* At `t(n) = n`, the statements of `Crossing.ntime_subset_dspace_sqrtLog`,
  `Crossing.ntime_decidable_sqrtLog` and `Crossing.ntime_ssubset_dspace`
  (`CslibFrontier/Computability/Complexity/Classes/TimeSpace/NtimeDspace/Cross/Theorem.lean`)
  follow from `GeneralSimulation` (`ntime_subset_dspace_sqrtLog_linear`, …), as a sanity check.

## Models

Time is Complexitylib's nondeterministic time (`Cslib.Complexity.NTIME`,
`Turing.MultiTapeNTM.RunsInTime`: every computation path of at least `t` steps ends halted), and
space is Complexitylib's deterministic space (`Cslib.Complexity.DSPACE`). Constants are natural
numbers: "for some `c > 0`, at least `c n √log n` steps" becomes "for some `C ≥ 1`, not within
`n ⌊√⌊log₂ n⌋⌋ / C` steps".
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.Cross

open Cslib.Complexity _root_.Turing _root_.Turing.MultiTapeTM Filter

/-! ### Nondeterministic space -/

/-- **Deterministic space is within nondeterministic space**: a deterministic machine is a
nondeterministic one with one computation path
(`Turing.MultiTapeTM.ComputableInTimeAndSpace.exists_decidesInSpace`), with the same space
bound. -/
theorem DSPACE_subset_NSPACE {α : Type} {enc : α ↪ List Bool} {s : ℕ → ℕ} :
    DSPACE enc s ⊆ NSPACE enc s := by
  rintro A ⟨c₁, c₂, t, h⟩
  obtain ⟨g, hg, hA⟩ := decidableInTimeAndSpace_iff.mp h
  obtain ⟨k, State, hfin, ntm, hd⟩ := hg.exists_decidesInSpace hA
  exact ⟨k, State, hfin, ntm, c₁, c₂, hd⟩

/-- A nonvacuity check for `NSPACE`: the diagonal language within space `G` is in `NSPACE[G]`. -/
theorem setOf_spaceDiagonal_mem_NSPACE {G : ℕ → ℕ} (hG : SpaceConstructible G)
    (hn : ∀ n, n ≤ G n) : {x | spaceDiagonal G x = true} ∈ NSPACE encBits G :=
  DSPACE_subset_NSPACE (setOf_spaceDiagonal_mem_DSPACE
      hG fun n => (Nat.log2_le_self n).trans (hn n))

/-! ### Theorem 1.1 as a class inclusion -/

/-- **Theorem 1.1:** `NTIME[t] ⊆ DSPACE[t / √log t]` for every `t(n) ≥ n`. -/
theorem ntime_subset_dspace_sqrtLog_of_general (h : GeneralSimulation) {t : ℕ → ℕ}
    (ht : ∀ n, n ≤ t n) : NTIME encBits t ⊆ DSPACE encBits (fun n => SqrtLog (t n)) := by
  intro A hA
  obtain ⟨C, hC⟩ := h t ht hA
  exact mem_DSPACE_iff.mpr ⟨C, 0, _, hC⟩

/-- `c · SqrtLog (t n) + c ≤ t n` eventually, for every `c`, when `t(n) ≥ n`. -/
theorem eventually_sqrtLog_comp_gap {t : ℕ → ℕ} (ht : ∀ n, n ≤ t n) (c : ℕ) :
    ∀ᶠ n in atTop, c * SqrtLog (t n) + c ≤ t n :=
  (tendsto_atTop_mono ht tendsto_id).eventually (sqrtLog_sublinear c)

/-! ### Corollary 1.2 (i) -/

/-- **Corollary 1.2 (i):** `NTIME[t] ⊊ DSPACE[t]` for every space-constructible `t(n) ≥ n`. -/
theorem ntime_ssubset_dspace_of_general (h : GeneralSimulation) {t : ℕ → ℕ}
    (hsc : SpaceConstructible t) (ht : ∀ n, n ≤ t n) : NTIME encBits t ⊂ DSPACE encBits t :=
  lt_of_le_of_lt (ntime_subset_dspace_sqrtLog_of_general h ht)
    (DSPACE_ssubset_DSPACE hsc (fun n => (Nat.log2_le_self n).trans (ht n))
        (eventually_sqrtLog_comp_gap ht))

/-- The witness of Corollary 1.2 (i): the diagonal language within space `t` is in `NSPACE[t]`
(and `DSPACE[t]`) but not in `NTIME[t]`. -/
theorem setOf_spaceDiagonal_notMem_NTIME (h : GeneralSimulation) {t : ℕ → ℕ}
    (ht : ∀ n, n ≤ t n) : {x | spaceDiagonal t x = true} ∉ NTIME encBits t := fun hmem =>
  setOf_spaceDiagonal_notMem_DSPACE_of_frequently ht
    (fun c => (eventually_sqrtLog_comp_gap ht c).frequently)
    (ntime_subset_dspace_sqrtLog_of_general h ht hmem)

/-- **Corollary 1.2 (i), nondeterministic space:** `NTIME[t] ⊊ NSPACE[t]` for every
space-constructible `t(n) ≥ n`. -/
theorem ntime_ssubset_nspace_of_general (h : GeneralSimulation) {t : ℕ → ℕ}
    (hsc : SpaceConstructible t) (ht : ∀ n, n ≤ t n) : NTIME encBits t ⊂ NSPACE encBits t :=
  lt_of_lt_of_le (ntime_ssubset_dspace_of_general h hsc ht) DSPACE_subset_NSPACE

/-- **Corollary 1.2 (i):** `NTIME[t] ≠ NSPACE[t]` for every space-constructible `t(n) ≥ n`. -/
theorem ntime_ne_nspace_of_general (h : GeneralSimulation) {t : ℕ → ℕ}
    (hsc : SpaceConstructible t) (ht : ∀ n, n ≤ t n) : NTIME encBits t ≠ NSPACE encBits t :=
  (ntime_ssubset_nspace_of_general h hsc ht).ne

/-! ### At a general scale -/

/-- Theorem 1.1 at a scale `D`, as a class inclusion: `NTIME[t] ⊆ DSPACE[D ∘ t]` for every
`t(n) ≥ n`. -/
theorem ntime_subset_dspace_of_generalAt {D : ℕ → ℕ} (h : GeneralSimulationAt D) {t : ℕ → ℕ}
    (ht : ∀ n, n ≤ t n) : NTIME encBits t ⊆ DSPACE encBits (fun n => D (t n)) := by
  intro A hA
  obtain ⟨C, hC⟩ := h t ht hA
  exact mem_DSPACE_iff.mpr ⟨C, 0, _, hC⟩

/-- Corollary 1.2 (i) at a scale `D`: `NTIME[t] ⊊ DSPACE[t]` for every space-constructible
`t(n) ≥ n`. -/
theorem ntime_ssubset_dspace_of_generalAt {D : ℕ → ℕ} (hD : Scale D) (h : GeneralSimulationAt D)
    {t : ℕ → ℕ} (hsc : SpaceConstructible t) (ht : ∀ n, n ≤ t n) :
    NTIME encBits t ⊂ DSPACE encBits t :=
  lt_of_le_of_lt (ntime_subset_dspace_of_generalAt h ht)
    (DSPACE_ssubset_DSPACE hsc
        (fun n => (Nat.log2_le_self n).trans (ht n)) fun c => (tendsto_atTop_mono ht tendsto_id).eventually (hD.sublinear c))

/-- Corollary 1.2 (i) at a scale `D`, nondeterministic space: `NTIME[t] ⊊ NSPACE[t]`. -/
theorem ntime_ssubset_nspace_of_generalAt {D : ℕ → ℕ} (hD : Scale D) (h : GeneralSimulationAt D)
    {t : ℕ → ℕ} (hsc : SpaceConstructible t) (ht : ∀ n, n ≤ t n) :
    NTIME encBits t ⊂ NSPACE encBits t :=
  lt_of_lt_of_le (ntime_ssubset_dspace_of_generalAt hD h hsc ht) DSPACE_subset_NSPACE

/-! ### Corollary 1.2 (ii) -/

/-- `SqrtLog m ≤ m / ⌊√⌊log₂ m₀⌋⌋ + 1` for `m₀ ≤ m` with `⌊√⌊log₂ m₀⌋⌋ > 0`. -/
theorem sqrtLog_le_div_of_le {m₀ m : ℕ} (h : m₀ ≤ m) (h0 : 0 < Nat.sqrt m₀.log2) :
    SqrtLog m ≤ m / Nat.sqrt m₀.log2 + 1 :=
  Nat.add_le_add_right (Nat.div_le_div_left (Nat.sqrt_le_sqrt (log2_mono h)) h0) 1

/-- **Corollary 1.2 (ii):** `NTIME[t·√log t] ⊆ DSPACE[t]` for every `t(n) ≥ n`, with
`√log t = ⌊√⌊log₂ (t n)⌋⌋`. -/
theorem ntime_mul_sqrtLog_subset_dspace (h : GeneralSimulation) {t : ℕ → ℕ}
    (ht : ∀ n, n ≤ t n) :
    NTIME encBits (fun n => t n * Nat.sqrt (Nat.log2 (t n))) ⊆ DSPACE encBits t := by
  -- below the smallest `t`, where `√log t = 0`, raise the time bound to `t`
  have hT : ∀ n, n ≤ max (t n * Nat.sqrt (Nat.log2 (t n))) (t n) :=
    fun n => (ht n).trans (le_max_right _ _)
  refine (NTIME_mono fun n => le_max_left _ (t n)).trans
    ((ntime_subset_dspace_sqrtLog_of_general h hT).trans
      (DSPACE_mono_of_le_mul_add (C := 1) fun n => ?_))
  rcases Nat.eq_zero_or_pos (Nat.sqrt (t n).log2) with h0 | h0
  · rw [h0, Nat.mul_zero, Nat.max_eq_right (Nat.zero_le _)]
    unfold SqrtLog
    rw [h0, Nat.div_zero]
    omega
  · have hmax : max (t n * Nat.sqrt (t n).log2) (t n) = t n * Nat.sqrt (t n).log2 :=
      Nat.max_eq_left (Nat.le_mul_of_pos_right _ h0)
    rw [hmax]
    refine (sqrtLog_le_div_of_le (Nat.le_mul_of_pos_right _ h0) h0).trans ?_
    rw [Nat.mul_div_cancel _ h0]
    omega

/-! ### Corollary 1.2 (iii) -/

/-- `n + 1` has at most `⌊log₂ n⌋ + 2` binary digits. -/
theorem length_encNat_succ_le (n : ℕ) : (encNat (n + 1)).length ≤ n.log2 + 2 := by
  rw [encNat_apply, Nat.size_eq_bits_len, Nat.size_le]
  have := Nat.lt_log2_self (n := n)
  rw [pow_succ]
  omega

/-- **Complements of deterministic deciders**, with a logarithmic overhead: negate the answer
(`Turing.MultiTapeTM.ComputableInTimeAndSpace.comp_space` with `Bool.not`). -/
theorem exists_decidable_compl {B : Set (List Bool)} {t s : List Bool → ℕ}
    (h : DecidableInTimeAndSpace B encBits t s) :
    ∃ c t', DecidableInTimeAndSpace Bᶜ encBits t' (fun a => c * (s a + a.length.log2 + 1)) := by
  obtain ⟨g, hg, hB⟩ := decidableInTimeAndSpace_iff.mp h
  obtain ⟨tn, sn, -, -, hnot⟩ := ComputableInPolyTime.bool_not
  obtain ⟨c, hc⟩ := hg.comp_space hnot
  refine ⟨c * (sn 1 + 6), _, decidableInTimeAndSpace_iff.mpr ⟨_, hc.mono (fun _ => le_rfl)
    fun a => ?_, fun a => ?_⟩⟩
  · have hb : ∀ b, (encBool b).length = 1 := fun _ => rfl
    simp only [encBits_apply, hb]
    have h1 := length_encNat_succ_le a.length
    have h2 : (encNat (1 + 1)).length = 2 := by decide
    rw [h2, Nat.mul_assoc]
    refine Nat.mul_le_mul_left c ?_
    nlinarith
  · simp only [Set.mem_compl_iff, hB a, Function.comp_apply, Bool.not_eq_true']
    cases g a <;> simp

/-- **The language of Corollary 1.2 (iii):** the diagonal language within linear space. -/
def hardLanguage : Set (List Bool) := {x | spaceDiagonal (fun n => n) x = true}

/-- The language of Corollary 1.2 (iii) is in `DSPACE[n]`. -/
theorem hardLanguage_mem_DSPACE : hardLanguage ∈ DSPACE encBits (fun n => n) :=
  setOf_spaceDiagonal_mem_DSPACE spaceConstructible_id (fun n => Nat.log2_le_self n)

/-- **Corollary 1.2 (iii) for one machine.** Every nondeterministic machine deciding the diagonal
language within linear space, or its complement (every branch halting, acceptance by some
computation path), has a constant `C ≥ 1` such that for all large `n` some input of length `n`
makes it run for more than `n·⌊√⌊log₂ n⌋⌋ / C` steps. -/
theorem ntime_lower_bound_of_general (h : GeneralSimulation) {k : ℕ} {State : Type}
    [Finite State] (ntm : MultiTapeNTM k Bool State) {B : Set (List Bool)}
    (hB : B = hardLanguage ∨ B = hardLanguageᶜ)
    (hdec : ∀ x, (∃ t, ntm.RunsInTime x t) ∧ (x ∈ B ↔ ntm.Accepts x)) :
    ∃ C, 1 ≤ C ∧ ∀ᶠ n in atTop,
      ∃ x : List Bool, x.length = n ∧ ¬ ntm.RunsInTime x (n * Nat.sqrt n.log2 / C) := by
  classical
  by_contra hcon
  push Not at hcon
  -- the worst-case running time `T*` of the machine, at least `n`
  set T : ℕ → ℕ := fun n => max (maxOnLength (fun x => Nat.find (hdec x).1) n) n with hT
  have hrun (x : List Bool) : ntm.RunsInTime x (T x.length) :=
    (Nat.find_spec (hdec x).1).mono
      ((le_maxOnLength (fun x => Nat.find (hdec x).1) x).trans (le_max_left _ _))
  have hTn : ∀ n, n ≤ T n := fun n => le_max_right _ _
  have hBT : B ∈ NTIME encBits T :=
    ⟨1, 0, k, State, inferInstance, ntm, fun a => ⟨by simpa using hrun a, (hdec a).2⟩⟩
  obtain ⟨C₀, hC₀⟩ := h T hTn hBT
  -- so the language is in `DSPACE[SqrtLog T* + log n]`
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
  rintro n ⟨hall, hrn, hsl⟩
  set r := Nat.sqrt n.log2 with hr_def
  have hr0 : 0 < r := by omega
  -- the running time at length `n` is at most `n r / (4c + 4)`
  have htime : maxOnLength (fun x => Nat.find (hdec x).1) n ≤ n * r / (4 * c + 4) :=
    maxOnLength_le fun x hx => Nat.find_min' _ (hall x hx)
  have e₁ : n * r / (4 * c + 4) / r = n / (4 * c + 4) := by
    rw [Nat.div_div_eq_div_mul, Nat.mul_div_mul_right _ _ hr0]
  have hTle : T n / r ≤ n / (4 * c + 4) + n / r := by
    rcases le_total (maxOnLength (fun x => Nat.find (hdec x).1) n) n with hle | hle
    · have hTeq : T n = n := Nat.max_eq_right hle
      rw [hTeq]
      exact Nat.le_add_left _ _
    · have hTeq : T n = maxOnLength (fun x => Nat.find (hdec x).1) n := Nat.max_eq_left hle
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

/-- **Corollary 1.2 (iii).** There is a language in `DSPACE[n]` such that every nondeterministic
machine deciding it or its complement (every branch halting) has a constant `C ≥ 1` such that, for
all large `n`, it runs for more than `n·⌊√⌊log₂ n⌋⌋ / C` steps on some input of length `n`. -/
theorem exists_dspace_linear_ntime_lower_bound (h : GeneralSimulation) :
    ∃ L : Set (List Bool), L ∈ DSPACE encBits (fun n => n) ∧
      ∀ (k : ℕ) (State : Type) [Finite State] (ntm : MultiTapeNTM k Bool State)
        (B : Set (List Bool)), (B = L ∨ B = Lᶜ) →
        (∀ x, (∃ t, ntm.RunsInTime x t) ∧ (x ∈ B ↔ ntm.Accepts x)) →
        ∃ C, 1 ≤ C ∧ ∀ᶠ n in atTop,
          ∃ x : List Bool, x.length = n ∧ ¬ ntm.RunsInTime x (n * Nat.sqrt n.log2 / C) :=
  ⟨hardLanguage, hardLanguage_mem_DSPACE, fun _ _ _ ntm _ hB hdec =>
    ntime_lower_bound_of_general h ntm hB hdec⟩

/-! ### The linear case, against
`CslibFrontier/Computability/Complexity/Classes/TimeSpace/NtimeDspace/Cross/Theorem.lean` -/

/-- `Crossing.ntime_decidable_sqrtLog` from `GeneralSimulation`. -/
theorem ntime_decidable_sqrtLog_linear (h : GeneralSimulation) {A : Set (List Bool)}
    (hA : A ∈ NTIME encBits (fun n => n)) :
    ∃ C, DecidableInTimeAndSpace A encBits
      (fun a => 2 ^ (C * (a.length / Nat.sqrt a.length.log2 + 1)))
      (fun a => C * (a.length / Nat.sqrt a.length.log2 + 1)) :=
  h (fun n => n) (fun _ => le_rfl) hA

/-- `Crossing.ntime_subset_dspace_sqrtLog` from `GeneralSimulation`. -/
theorem ntime_subset_dspace_sqrtLog_linear (h : GeneralSimulation) :
    NTIME encBits (fun n => n) ⊆ DSPACE encBits (fun n => n / Nat.sqrt n.log2 + 1) :=
  ntime_subset_dspace_sqrtLog_of_general h (fun _ => le_rfl)

/-- `Crossing.ntime_ssubset_dspace` from `GeneralSimulation`. -/
theorem ntime_ssubset_dspace_linear (h : GeneralSimulation) :
    NTIME encBits (fun n => n) ⊂ DSPACE encBits (fun n => n) :=
  ntime_ssubset_dspace_of_general h spaceConstructible_id (fun _ => le_rfl)

end Cslib.Complexity.NtimeDspace.Cross
