/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.AuxPDA.Counting
public import CslibFrontier.Computability.Complexity.Classes.LogSpace
public import CslibFrontier.Computability.Complexity.Classes.LogSpace.Counting
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.HaltingTime
import CslibFrontier.Foundations.Data.Nat.AffineBound

/-!
# Auxiliary pushdown complexity classes: `LogCFL`, `UAuxPDA`, and `coUAuxPDA`

This module defines the time- and space-bounded auxiliary pushdown complexity classes
`Cslib.Complexity.AuxPDATimeSpace` and `Cslib.Complexity.UAuxPDATimeSpace`, together with their
logarithmic-space, polynomial-time specializations:

* `Cslib.Complexity.LogCFL`: languages decided by a finite-state, finite-stack-alphabet binary
  auxiliary pushdown automaton (`Turing.AuxPDA`) within logarithmic work space `O(log n)` (stack
  uncharged) and a polynomial all-branches clock (Sudborough's characterization of `LogCFL` as
  `AuxPDA(O(log n), poly)`).
* `Cslib.Complexity.UAuxPDA`: the unambiguous counterpart using a counting auxiliary pushdown
  automaton (`Turing.CountingAuxPDA`) with logarithmic work space, a polynomial all-branches clock,
  one accepting branch on members, and zero on nonmembers, mirroring `Cslib.Complexity.UL` and
  `Cslib.Complexity.USPACE`.
* `Cslib.Complexity.coUAuxPDA`: complements of problems in `UAuxPDA`.

This is original library development for cslib-frontier #7920 (Work Package 3); the equivalence
between Sudborough's `AuxPDA(log n, poly)` characterization and logspace reducibility to
context-free languages, as well as the uniform equality `LogCFL = UAuxPDA = coUAuxPDA`, remain
tracked in #7920.

## Main definitions

* `Cslib.Complexity.AuxPDATimeSpace`: nondeterministic `AuxPDA` time-space classes.
* `Cslib.Complexity.UAuxPDATimeSpace`: unambiguous counting `AuxPDA` time-space classes.
* `Cslib.Complexity.LogCFL`: `AuxPDA(O(log n), poly)`.
* `Cslib.Complexity.UAuxPDA`: unambiguous `AuxPDA(O(log n), poly)`.
* `Cslib.Complexity.coUAuxPDA`: complements of problems in `UAuxPDA`.

## Main results

* `Cslib.Complexity.AuxPDATimeSpace_mono_of_le_mul_add`, `Cslib.Complexity.AuxPDATimeSpace_mono`,
  `Cslib.Complexity.UAuxPDATimeSpace_mono_of_le_mul_add`,
  `Cslib.Complexity.UAuxPDATimeSpace_mono`: monotone resource closure absorbing affine constants.
* `Cslib.Complexity.UAuxPDATimeSpace_subset_AuxPDATimeSpace`,
  `Cslib.Complexity.UAuxPDA_subset_LogCFL`: forgetting branch multiplicity places unambiguous
  `AuxPDA` classes inside their nondeterministic counterparts.
* `Cslib.Complexity.mem_LogCFL_iff_exists_mem_AuxPDATimeSpace`,
  `Cslib.Complexity.mem_UAuxPDA_iff_exists_mem_UAuxPDATimeSpace`: polynomial-clock union
  characterizations.
* `Cslib.Complexity.compl_mem_coUAuxPDA_iff`, `Cslib.Complexity.coUAuxPDA_eq_UAuxPDA_iff`:
  complement duality for `coUAuxPDA`.
* `Cslib.Complexity.NL_subset_LogCFL`: embedding `NL` into `LogCFL` via an unused stack and the
  logarithmic-space polynomial halting clock.
* `Cslib.Complexity.UL_subset_UAuxPDA`: count-preserving embedding of `UL` into `UAuxPDA`.

## References

* [K. Reinhardt, E. Allender, *Making Nondeterminism Unambiguous*][ReinhardtAllender2000]
* [W. M. Hoza, *Nondeterministic and Unambiguous Logarithmic Space*][Hoza2026NLUL]
* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
-/

@[expose] public section

namespace Cslib.Complexity

open _root_.Turing _root_.Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool} {A : Set α}

/-- Problems decided by one finite-state, finite-stack-alphabet binary `AuxPDA` within work space
`O(s n)` (stack uncharged) and all-branches clock `O(t n)` on encoded instances of length `n`. -/
def AuxPDATimeSpace (enc : α ↪ List Bool) (s t : ℕ → ℕ) : Set (Set α) :=
  {A | ∃ (k : ℕ) (StackSym State : Type) (_ : Finite StackSym) (_ : Finite State)
    (M : AuxPDA k Bool StackSym State) (cs₁ cs₂ ct₁ ct₂ : ℕ),
    M.DecidesInTimeAndSpace enc A
      (fun a => cs₁ * s (enc a).length + cs₂)
      (fun a => ct₁ * t (enc a).length + ct₂)}

/-- Problems decided unambiguously by one finite-state, finite-stack-alphabet binary
`CountingAuxPDA` within work space `O(s n)` (stack uncharged) and all-branches clock `O(t n)`:
exactly one accepting branch on members and zero on nonmembers. -/
def UAuxPDATimeSpace (enc : α ↪ List Bool) (s t : ℕ → ℕ) : Set (Set α) :=
  {A | ∃ (k : ℕ) (StackSym State : Type) (_ : Finite StackSym) (_ : Finite State)
    (M : CountingAuxPDA k Bool StackSym State) (cs₁ cs₂ ct₁ ct₂ : ℕ) (f : α → ℕ),
    M.CountsInTimeAndSpace enc f
      (fun a => cs₁ * s (enc a).length + cs₂)
      (fun a => ct₁ * t (enc a).length + ct₂) ∧
    (∀ a, f a ≤ 1) ∧ ∀ a, a ∈ A ↔ 0 < f a}

/-- **`LogCFL` via `AuxPDA(O(log n), poly)`** (Sudborough's characterization): problems decided by
one finite-state, finite-stack-alphabet binary `AuxPDA` within logarithmic work space
`c * (Nat.log2 n + 1)` (stack uncharged) and a polynomial all-branches clock. -/
def LogCFL (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ (k : ℕ) (StackSym State : Type) (_ : Finite StackSym) (_ : Finite State)
    (M : AuxPDA k Bool StackSym State) (c : ℕ) (t : α → ℕ),
    PolyBounded (fun a => (enc a).length) t ∧
    M.DecidesInTimeAndSpace enc A (fun a => c * (Nat.log2 (enc a).length + 1)) t}

/-- **Unambiguous `AuxPDA(O(log n), poly)`**: problems decided by one finite-state,
finite-stack-alphabet binary `CountingAuxPDA` within logarithmic work space `c * (Nat.log2 n + 1)`
and a polynomial all-branches clock, having one accepting branch on members and zero on
nonmembers. -/
def UAuxPDA (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ (k : ℕ) (StackSym State : Type) (_ : Finite StackSym) (_ : Finite State)
    (M : CountingAuxPDA k Bool StackSym State) (c : ℕ) (t : α → ℕ) (f : α → ℕ),
    PolyBounded (fun a => (enc a).length) t ∧
    M.CountsInTimeAndSpace enc f (fun a => c * (Nat.log2 (enc a).length + 1)) t ∧
    (∀ a, f a ≤ 1) ∧ ∀ a, a ∈ A ↔ 0 < f a}

/-- Complements of problems in `UAuxPDA enc`, under the same encoding. -/
def coUAuxPDA (enc : α ↪ List Bool) : Set (Set α) :=
  {A | Aᶜ ∈ UAuxPDA enc}

/-! ### Monotone resource closure -/

/-- `AuxPDATimeSpace` absorbs affine factors in both space and time bounds. -/
theorem AuxPDATimeSpace_mono_of_le_mul_add {s₁ s₂ t₁ t₂ : ℕ → ℕ} {Cs Ct : ℕ}
    (hs : ∀ n, s₁ n ≤ Cs * s₂ n + Cs) (ht : ∀ n, t₁ n ≤ Ct * t₂ n + Ct) :
    AuxPDATimeSpace enc s₁ t₁ ⊆ AuxPDATimeSpace enc s₂ t₂ := by
  rintro A ⟨k, StackSym, State, hst, hfin, M, cs₁, cs₂, ct₁, ct₂, hM⟩
  exact ⟨k, StackSym, State, hst, hfin, M, cs₁ * Cs, cs₁ * Cs + cs₂, ct₁ * Ct, ct₁ * Ct + ct₂,
    hM.mono
      (fun _ => Nat.mul_add_le_mul_add_of_le_mul_add (hs _) cs₁ cs₂)
      (fun _ => Nat.mul_add_le_mul_add_of_le_mul_add (ht _) ct₁ ct₂)⟩

/-- `AuxPDATimeSpace` is monotone in both space and time bounds. -/
theorem AuxPDATimeSpace_mono {s₁ s₂ t₁ t₂ : ℕ → ℕ}
    (hs : ∀ n, s₁ n ≤ s₂ n) (ht : ∀ n, t₁ n ≤ t₂ n) :
    AuxPDATimeSpace enc s₁ t₁ ⊆ AuxPDATimeSpace enc s₂ t₂ :=
  AuxPDATimeSpace_mono_of_le_mul_add (Cs := 1) (Ct := 1)
    (fun n => by have := hs n; omega) (fun n => by have := ht n; omega)

/-- `UAuxPDATimeSpace` absorbs affine factors in both space and time bounds. -/
theorem UAuxPDATimeSpace_mono_of_le_mul_add {s₁ s₂ t₁ t₂ : ℕ → ℕ} {Cs Ct : ℕ}
    (hs : ∀ n, s₁ n ≤ Cs * s₂ n + Cs) (ht : ∀ n, t₁ n ≤ Ct * t₂ n + Ct) :
    UAuxPDATimeSpace enc s₁ t₁ ⊆ UAuxPDATimeSpace enc s₂ t₂ := by
  rintro A ⟨k, StackSym, State, hst, hfin, M, cs₁, cs₂, ct₁, ct₂, f, hM, hle, hA⟩
  exact ⟨k, StackSym, State, hst, hfin, M, cs₁ * Cs, cs₁ * Cs + cs₂, ct₁ * Ct, ct₁ * Ct + ct₂, f,
    hM.mono
      (fun _ => Nat.mul_add_le_mul_add_of_le_mul_add (hs _) cs₁ cs₂)
      (fun _ => Nat.mul_add_le_mul_add_of_le_mul_add (ht _) ct₁ ct₂), hle, hA⟩

/-- `UAuxPDATimeSpace` is monotone in both space and time bounds. -/
theorem UAuxPDATimeSpace_mono {s₁ s₂ t₁ t₂ : ℕ → ℕ}
    (hs : ∀ n, s₁ n ≤ s₂ n) (ht : ∀ n, t₁ n ≤ t₂ n) :
    UAuxPDATimeSpace enc s₁ t₁ ⊆ UAuxPDATimeSpace enc s₂ t₂ :=
  UAuxPDATimeSpace_mono_of_le_mul_add (Cs := 1) (Ct := 1)
    (fun n => by have := hs n; omega) (fun n => by have := ht n; omega)

/-! ### Unambiguous-to-nondeterministic inclusions and union characterizations -/

/-- Forgetting transition multiplicity places `UAuxPDATimeSpace` inside `AuxPDATimeSpace`. -/
theorem UAuxPDATimeSpace_subset_AuxPDATimeSpace {s t : ℕ → ℕ} :
    UAuxPDATimeSpace enc s t ⊆ AuxPDATimeSpace enc s t := by
  rintro A ⟨k, StackSym, State, hst, hfin, M, cs₁, cs₂, ct₁, ct₂, f, hM, -, hA⟩
  exact ⟨k, StackSym, State, hst, hfin, M.toAuxPDA, cs₁, cs₂, ct₁, ct₂,
    hM.decidesInTimeAndSpace hA⟩

/-- **`UAuxPDA ⊆ LogCFL`**: forgetting branch multiplicity turns an unambiguous logarithmic-space,
polynomial-time counting `AuxPDA` into a nondeterministic one with the same bounds. -/
theorem UAuxPDA_subset_LogCFL : UAuxPDA enc ⊆ LogCFL enc := by
  rintro A ⟨k, StackSym, State, hst, hfin, M, c, t, f, hpoly, hM, -, hA⟩
  exact ⟨k, StackSym, State, hst, hfin, M.toAuxPDA, c, t, hpoly, hM.decidesInTimeAndSpace hA⟩

private lemma le_mul_pow_add_of_polyBounded {t : α → ℕ}
    (hpoly : PolyBounded (fun a => (enc a).length) t) :
    ∃ ct d, ∀ a, t a ≤ (ct * 2 ^ d) * (enc a).length ^ d + ct * 2 ^ d := by
  obtain ⟨ct, d, hle⟩ := hpoly.exists_le
  refine ⟨ct, d, fun a => ?_⟩
  have hpow := Nat.add_one_pow_le_two_pow_mul_add d (enc a).length
  have hmul := Nat.mul_le_mul_left ct hpow
  rw [Nat.mul_add, ← Nat.mul_assoc] at hmul
  exact (hle a).trans hmul

/-- `LogCFL` is the union of `AuxPDATimeSpace enc Nat.log2 (· ^ d)` over all polynomial degrees
`d`. -/
theorem mem_LogCFL_iff_exists_mem_AuxPDATimeSpace :
    A ∈ LogCFL enc ↔ ∃ d, A ∈ AuxPDATimeSpace enc Nat.log2 (· ^ d) := by
  constructor
  · rintro ⟨k, StackSym, State, hst, hfin, M, c, t, hpoly, hM⟩
    obtain ⟨ct, d, hle⟩ := le_mul_pow_add_of_polyBounded hpoly
    exact ⟨d, k, StackSym, State, hst, hfin, M, c, c, ct * 2 ^ d, ct * 2 ^ d,
      hM.mono (fun _ => by rw [Nat.mul_add, Nat.mul_one]) hle⟩
  · rintro ⟨d, k, StackSym, State, hst, hfin, M, cs₁, cs₂, ct₁, ct₂, hM⟩
    exact ⟨k, StackSym, State, hst, hfin, M, cs₁ + cs₂, _,
      ((PolyBounded.const ct₁).mul (PolyBounded.self.pow d)).add (.const ct₂),
      hM.mono (fun _ => by nlinarith) (fun _ => le_rfl)⟩

/-- `UAuxPDA` is the union of `UAuxPDATimeSpace enc Nat.log2 (· ^ d)` over all polynomial degrees
`d`. -/
theorem mem_UAuxPDA_iff_exists_mem_UAuxPDATimeSpace :
    A ∈ UAuxPDA enc ↔ ∃ d, A ∈ UAuxPDATimeSpace enc Nat.log2 (· ^ d) := by
  constructor
  · rintro ⟨k, StackSym, State, hst, hfin, M, c, t, f, hpoly, hM, hle1, hA⟩
    obtain ⟨ct, d, hle⟩ := le_mul_pow_add_of_polyBounded hpoly
    exact ⟨d, k, StackSym, State, hst, hfin, M, c, c, ct * 2 ^ d, ct * 2 ^ d, f,
      hM.mono (fun _ => by rw [Nat.mul_add, Nat.mul_one]) hle, hle1, hA⟩
  · rintro ⟨d, k, StackSym, State, hst, hfin, M, cs₁, cs₂, ct₁, ct₂, f, hM, hle1, hA⟩
    exact ⟨k, StackSym, State, hst, hfin, M, cs₁ + cs₂, _, f,
      ((PolyBounded.const ct₁).mul (PolyBounded.self.pow d)).add (.const ct₂),
      hM.mono (fun _ => by nlinarith) (fun _ => le_rfl), hle1, hA⟩

/-! ### Complement duality for `coUAuxPDA` -/

/-- A problem belongs to `coUAuxPDA` iff its complement belongs to `UAuxPDA`. -/
theorem mem_coUAuxPDA : A ∈ coUAuxPDA enc ↔ Aᶜ ∈ UAuxPDA enc := Iff.rfl

/-- Complementing a problem in `UAuxPDA` gives a problem in `coUAuxPDA`, and conversely. -/
theorem compl_mem_coUAuxPDA_iff : Aᶜ ∈ coUAuxPDA enc ↔ A ∈ UAuxPDA enc := by
  rw [mem_coUAuxPDA, compl_compl]

/-- `coUAuxPDA` equals `UAuxPDA` iff `UAuxPDA` is closed under complement. -/
theorem coUAuxPDA_eq_UAuxPDA_iff :
    coUAuxPDA enc = UAuxPDA enc ↔ ∀ A, A ∈ UAuxPDA enc → Aᶜ ∈ UAuxPDA enc := by
  constructor
  · intro heq A hA
    exact mem_coUAuxPDA.mp (heq ▸ hA)
  · intro hclosed
    ext A
    constructor
    · intro hA
      simpa only [compl_compl] using hclosed Aᶜ (mem_coUAuxPDA.mp hA)
    · intro hA
      exact mem_coUAuxPDA.mpr (hclosed A hA)

/-! ### Embeddings of `NL` and `UL` -/

private lemma polyBounded_polyClock (enc : α ↪ List Bool) (d : ℕ) :
    PolyBounded (fun a => (enc a).length) (fun a => polyClock d (enc a).length) := by
  refine PolyBounded.of_forall_le (2 * 2 ^ d) d fun a => ?_
  simp only [polyClock, mul_pow]
  rw [← mul_assoc]

/-- **`NL ⊆ LogCFL`**: every nondeterministic logarithmic-space decider embeds into an `AuxPDA`
with an unused stack, inheriting a uniform polynomial all-branches clock from
`Turing.MultiTapeNTM.exists_runsInTime_polynomial_of_runsInSpace_log`. -/
theorem NL_subset_LogCFL : NL enc ⊆ LogCFL enc := by
  rintro A ⟨k, State, hfin, ntm, c, hdec⟩
  let : Finite State := hfin
  obtain ⟨d, hd⟩ := MultiTapeNTM.exists_runsInTime_polynomial_of_runsInSpace_log ntm c
  refine ⟨k, PUnit, State, inferInstance, hfin, AuxPDA.ofMultiTapeNTM ntm, c,
    fun a => polyClock d (enc a).length, polyBounded_polyClock enc d, fun a => ?_⟩
  obtain ⟨hspace, hacc⟩ := hdec.1 a
  obtain ⟨t, ht⟩ := hdec.2 a
  exact ⟨AuxPDA.ofMultiTapeNTM_runsInSpace_iff.mpr hspace,
    AuxPDA.ofMultiTapeNTM_runsInTime_iff.mpr (hd hspace ht),
    hacc.trans AuxPDA.ofMultiTapeNTM_accepts_iff.symm⟩

/-- **`UL ⊆ UAuxPDA`**: every unambiguous logarithmic-space counting machine embeds into a
`CountingAuxPDA` with an unused stack, preserving exact accepting branch counts at the uniform
polynomial clock. -/
theorem UL_subset_UAuxPDA : UL enc ⊆ UAuxPDA enc := by
  rintro A ⟨f, ⟨k, State, hfin, M, c, hM⟩, hle1, hA⟩
  let : Finite State := hfin
  obtain ⟨d, hd⟩ := MultiTapeNTM.exists_runsInTime_polynomial_of_runsInSpace_log M.toNTM c
  refine ⟨k, PUnit, State, inferInstance, hfin, CountingAuxPDA.ofMultiTapeCTM M, c,
    fun a => polyClock d (enc a).length, f, polyBounded_polyClock enc d, fun a => ?_, hle1, hA⟩
  obtain ⟨hspace, t, hclock, hcount⟩ := hM a
  have htPaths : M.toNTM.RunsInTime (enc a) t := fun p hp =>
    hclock.paths_halted p.toRunPath p.head_eq hp
  have hpolyPaths : M.toNTM.RunsInTime (enc a) (polyClock d (enc a).length) :=
    hd hspace htPaths
  have hpolyClock : M.HaltsWithin (polyClock d (enc a).length) (Cfg.init M.initial (enc a)) :=
    M.haltsWithin_of_paths_of_haltsWithin hclock fun p hp hlen => hpolyPaths ⟨p, hp⟩ hlen
  have hmax : M.acceptCount (polyClock d (enc a).length) (Cfg.init M.initial (enc a)) =
      M.acceptCount t (Cfg.init M.initial (enc a)) := by
    have h1 := hpolyClock.branchCount_eq (le_max_left (polyClock d (enc a).length) t) (· == [true])
    have h2 := hclock.branchCount_eq (le_max_right (polyClock d (enc a).length) t) (· == [true])
    exact h1.symm.trans h2
  refine ⟨?_, ?_, ?_⟩
  · rw [CountingAuxPDA.ofMultiTapeCTM_toAuxPDA]
    exact AuxPDA.ofMultiTapeNTM_runsInSpace_iff.mpr hspace
  · exact (CountingAuxPDA.ofMultiTapeCTM_haltsWithin_iff M _ _ []).mpr hpolyClock
  · rw [CountingAuxPDA.ofMultiTapeCTM_acceptCount]
    exact hcount.trans hmax.symm

end Cslib.Complexity
