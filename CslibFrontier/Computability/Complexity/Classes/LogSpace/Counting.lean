/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Counting
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Composition.Recompute
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.Bits
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair
public import Mathlib.Data.Nat.Prime.Defs

/-!
# Counting in logarithmic space

`SharpL` counts actual accepting branches of a logspace counting machine. Branches that
halt early are counted once, and distinct transition occurrences may lead to the same
configuration. `WeaklyUnambiguousSharpL` prohibits that collision for accepting branches.
The nondeterministic view is used only to bound workspace.

`GapL` takes differences of two such counts. `UL`, `FewL`, `LFew`, `ParityL`,
`ModkL`, `ModL`, `PL`, and `SPL` restrict or test these counts and differences.

## References

* [Complexity Zoo, symbols](https://complexityzoo.net/Complexity_Zoo:Symbols#sharpl)
* [Complexity Zoo, logarithmic-space fewness](https://complexityzoo.net/Complexity_Zoo:L#logfew)
* [Complexity Zoo, modular logarithmic space](https://complexityzoo.net/Complexity_Zoo:M#modl)
* [E. Allender and M. Ogihara, *Relationships Among PL, #L, and the Determinant*]
  (https://archive.numdam.org/item/ITA_1996__30_1_1_0/)
* [L. Fortnow, *Counting Complexity*][Fortnow1997]
-/

@[expose] public section

namespace Cslib.Complexity

open _root_.Turing _root_.Turing.MultiTapeTM

variable {α : Type}

/-- A given counting machine realizes the accepting count in logarithmic workspace.
The finite clock is chosen for each input because the count is stable after every branch halts. -/
def _root_.Turing.MultiTapeCTM.CountsInLogSpace {k : ℕ} {State : Type}
    (M : MultiTapeCTM k Bool State) (enc : α ↪ List Bool) (f : α → ℕ) : Prop :=
  ∃ c : ℕ, ∀ a,
    M.toNTM.RunsInSpace (enc a) (c * (Nat.log2 (enc a).length + 1)) ∧
      ∃ t, M.HaltsWithin t (Cfg.init M.initial (enc a)) ∧
        f a = M.acceptCount t (Cfg.init M.initial (enc a))

/-- Weak unambiguity from a configuration. Distinct accepting occurrence traces must have
different first-halting configurations. Rejecting traces may have the same endpoint. -/
def _root_.Turing.MultiTapeCTM.WeaklyUnambiguousFrom {k : ℕ} {State : Type}
    (M : MultiTapeCTM k Bool State) {input : List Bool} (cfg : Cfg k Bool State input) : Prop :=
  ∀ ⦃first second final⦄, M.runBranch cfg first = some final →
    M.runBranch cfg second = some final → final.Halted → final.output = [true] → first = second

/-- The accepting branch counts of finite logspace counting machines. -/
def SharpL (enc : α ↪ List Bool) : Set (α → ℕ) :=
  {f | ∃ (k : ℕ) (State : Type) (_ : Finite State) (M : MultiTapeCTM k Bool State),
    M.CountsInLogSpace enc f}

/-- The accepting branch counts of logspace machines whose computations are weakly unambiguous. -/
def WeaklyUnambiguousSharpL (enc : α ↪ List Bool) : Set (α → ℕ) :=
  {f | ∃ (k : ℕ) (State : Type) (_ : Finite State) (M : MultiTapeCTM k Bool State),
    M.CountsInLogSpace enc f ∧ ∀ a, M.WeaklyUnambiguousFrom (Cfg.init M.initial (enc a))}

/-- Integer-valued differences of two `SharpL` functions. -/
def GapL (enc : α ↪ List Bool) : Set (α → ℤ) :=
  {g | ∃ f₁ ∈ SharpL enc, ∃ f₂ ∈ SharpL enc, ∀ a, g a = f₁ a - f₂ a}

/-- Unambiguous logarithmic space. There is one accepting branch on members and none on
nonmembers. -/
def UL (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ f ∈ SharpL enc, (∀ a, f a ≤ 1) ∧ ∀ a, a ∈ A ↔ 0 < f a}

/-- FewP with logarithmic workspace. The number of accepting branches has a polynomial bound. -/
def FewL (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ f ∈ SharpL enc, ∃ p : Polynomial ℕ,
    (∀ a, f a ≤ p.eval (enc a).length) ∧ ∀ a, a ∈ A ↔ 0 < f a}

/-- Test a polynomially bounded logspace accepting count by a deterministic logspace predicate
on the instance paired with the binary count. -/
def LFew (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ f ∈ SharpL enc, ∃ p : Polynomial ℕ,
    (∀ a, f a ≤ p.eval (enc a).length) ∧
    ∃ R : α × ℕ → Bool, ComputableInLogSpace R (encPair enc encNat) encBool ∧
      ∀ a, a ∈ A ↔ R (a, f a) = true}

/-- LogFewNL (FewUL), as in [Allender–Reinhardt–Zhou, §5.1.1,
Definition 1][AllenderReinhardtZhou1999]. -/
def LogFewNL (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ f ∈ WeaklyUnambiguousSharpL enc, ∀ a, a ∈ A ↔ 0 < f a}

/-- Test a weakly unambiguous accepting branch count by a deterministic logspace predicate
on the instance paired with the binary count. See
[Allender–Reinhardt–Zhou, §5.1.1][AllenderReinhardtZhou1999]. -/
def LogFew (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ f ∈ WeaklyUnambiguousSharpL enc,
    ∃ R : α × ℕ → Bool, ComputableInLogSpace R (encPair enc encNat) encBool ∧
      ∀ a, a ∈ A ↔ R (a, f a) = true}

/-- Parity logarithmic space, using an odd accepting branch count on members. -/
def ParityL (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ f ∈ SharpL enc, ∀ a, a ∈ A ↔ Odd (f a)}

/-- Fixed-modulus logspace counting. For `m ≥ 2`, membership is nonzero residue modulo `m`.
The class at an invalid modulus is empty. -/
def ModkL (m : ℕ) (enc : α ↪ List Bool) : Set (Set α) :=
  {A | 2 ≤ m ∧ ∃ f ∈ SharpL enc, ∀ a, a ∈ A ↔ f a % m ≠ 0}

/-- Variable-modulus logspace counting. The modulus is the length of a unary string output in
deterministic logarithmic space and must be a positive power of a prime. Membership
uses nonzero residue of a `GapL` function, as in [Vijayaraghavan, Definition 2.6]
(https://eccc.weizmann.ac.il/report/2009/082/download/#page=4). -/
def ModL (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ f ∈ GapL enc, ∃ g : α → List Bool, ComputableInLogSpace g enc encBits ∧
    ∀ a, (∃ p e : ℕ, Nat.Prime p ∧ 0 < e ∧ g a = List.replicate (p ^ e) false) ∧
      (a ∈ A ↔ f a % (g a).length ≠ 0)}

/-- Unbounded-error probabilistic logarithmic space in its equivalent positive-gap
characterization [Allender and Ogihara, Proposition 3(1), (3),
and Theorem 6]
(https://archive.numdam.org/item/ITA_1996__30_1_1_0/). -/
def PL (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ f ∈ GapL enc, ∀ a, a ∈ A ↔ 0 < f a}

/-- Stoic probabilistic logspace, whose indicator is a `GapL` function. -/
def SPL (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ f ∈ GapL enc, (∀ a, f a = 0 ∨ f a = 1) ∧ ∀ a, a ∈ A ↔ f a = 1}

/-- Unambiguous machines satisfy the fewness bound with the constant polynomial one. -/
theorem UL_subset_FewL {enc : α ↪ List Bool} : UL enc ⊆ FewL enc := by
  rintro A ⟨f, hf, hle, hA⟩
  exact ⟨f, hf, 1, fun a => by simpa using hle a, hA⟩

/-- An unambiguous logspace machine is weakly unambiguous. -/
theorem UL_subset_LogFewNL {enc : α ↪ List Bool} : UL enc ⊆ LogFewNL enc := by
  rintro A ⟨f, ⟨k, State, finiteState, M, hcount⟩, hle, hA⟩
  refine ⟨f, ⟨k, State, finiteState, M, hcount, fun a => ?_⟩, hA⟩
  obtain ⟨c, hc⟩ := hcount
  obtain ⟨_, t, ht, hft⟩ := hc a
  intro first second final hfirst hsecond hhalt hout
  let cfg : Cfg k Bool State (enc a) := Cfg.init M.initial (enc a)
  let accepting := (M.branches t cfg).filter fun trace =>
    (M.runBranch cfg trace).any fun out => out.output == [true]
  have hcard : accepting.card ≤ 1 := by
    change M.acceptCount t (Cfg.init M.initial (enc a)) ≤ 1
    rw [← hft]
    exact hle a
  have mem (trace : List ℕ) (hrun : M.runBranch cfg trace = some final) : trace ∈ accepting := by
    refine Finset.mem_filter.mpr ⟨(M.mem_branches_iff _ _ _).mpr
      ⟨ht.length_le hrun, final, hrun, hhalt⟩, ?_⟩
    rw [hrun]
    simp [hout]
  exact Finset.card_le_one.mp hcard first (mem first hfirst) second (mem second hsecond)

end Cslib.Complexity
