/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Alternation
public import CslibFrontier.Computability.Complexity.Classes.Constructible
public import CslibFrontier.Computability.Complexity.Classes.Time
import CslibFrontier.Computability.Complexity.Classes.Alternation.LogSpaceGame
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.NatPow
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatLength
import CslibFrontier.Computability.Machines.Turing.MultiTape.OutView
import CslibFrontier.Computability.Machines.Turing.MultiTape.Run
import Mathlib.Data.Nat.Size

/-!
# Deterministic time `2 ^ O(s)` in alternating space `s`

A deterministic machine running within `c₁ * 2 ^ (c * s n) + c₂` steps is simulated by an
alternating machine within space `O(s n)`, when `s` is space-constructible and `⌊log₂ n⌋ ≤ s n`
(`Cslib.Complexity.DTIME_two_pow_mul_subset_ASPACE_of_spaceConstructible`). The alternating machine
computes the step count `T = 2 ^ E`, with `E = O(s n)`, in binary within space `O(s n)`, and plays
the local circuit-value game on the tableau of `T` steps of the deterministic machine
(`Cslib.Complexity.exists_decidesInSpace_of_runFrom`). This is
[Chandra, Kozen and Stockmeyer, Theorem 3.4][ChandraKozenStockmeyer1981],
`DTIME(T(n)) ⊆ ASPACE(c · log T(n))`, at `T(n) = 2 ^ (c * s n)` and for space-constructible bounds
only.

`ASPACE` bounds the space of every configuration reachable from the initial one, whichever player
chooses (`Turing.MultiTapeATM.RecognizesInSpace`), and asks every branch to halt. The proof of
[Chandra, Kozen and Stockmeyer, Theorem 3.4][ChandraKozenStockmeyer1981] guesses the step and the
cell existentially, without a bound, which suffices under their Definition 2.5, where only the
accepting computations of accepted instances are bounded. Under the bound of `ASPACE`, guessing the
step count, or doubling it while a game shows that the deterministic machine has not yet halted,
does not suffice: a branch cannot wait for the value of a game, so the branch that continues after
a false claim that the machine has not halted is reachable, and on it the step count grows without
bound. Here the hypothesis bounds the step count on every branch instead, as in
[Chandra, Kozen and Stockmeyer, Theorem 2.6(b)][ChandraKozenStockmeyer1981].

## Main results

* `Cslib.Complexity.DTIME_two_pow_mul_subset_ASPACE_of_spaceConstructible`:
  `DTIME(2 ^ (c * s n)) ⊆ ASPACE(s n)` for space-constructible `s` with `⌊log₂ n⌋ ≤ s n`.

## References

* [A. K. Chandra, D. C. Kozen, L. J. Stockmeyer, *Alternation*][ChandraKozenStockmeyer1981]
-/

public section

namespace Cslib.Complexity

open _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.MultiTapeTM.ComputableInSpace

variable {α : Type} {enc : α ↪ List Bool}

/-- **`DTIME(2 ^ O(s)) ⊆ ASPACE(s)` for space-constructible `s`.** This is
[Chandra, Kozen and Stockmeyer, Theorem 3.4][ChandraKozenStockmeyer1981] restricted to
space-constructible bounds, not that theorem in full: it additionally assumes `s`
space-constructible (`Cslib.Complexity.SpaceConstructible`), so that the alternating machine can
write the step count `2 ^ (c * s n)` in binary within its space bound. With `⌊log₂ n⌋ ≤ s n`, as
in the source, every problem decided by a deterministic machine within time `O(2 ^ (c * s n))` is
decided by a multi-tape alternating machine with a binary alphabet and finitely many states within
space `O(s n)`, every branch halting, on instances whose encoding under `enc` has length `n`. -/
theorem DTIME_two_pow_mul_subset_ASPACE_of_spaceConstructible {s : ℕ → ℕ}
    (hs : SpaceConstructible s) (hlog : ∀ n, Nat.log2 n ≤ s n) (c : ℕ) :
    DTIME enc (fun n => 2 ^ (c * s n)) ⊆ ASPACE enc s := by
  intro A ⟨c₁, c₂, _, k, State, hfin, tm, htm⟩
  -- the space bound `S = s n + 1` and the step count `T = 2 ^ E`
  set n : α → ℕ := fun a => (enc a).length
  set S : α → ℕ := fun a => s (n a) + 1
  set E : α → ℕ := fun a => c * s (n a) + (c₁ + c₂) + s (n a)
  set T : α → ℕ := fun a => 2 ^ E a
  obtain ⟨_, hsO⟩ := hs.computableInO
  have hsn : ComputableInSpace (fun a => s (n a)) enc encNat S :=
    ((of_inO hsO).of_encIn_eq (fun a => enc a) fun _ => rfl).mono_le fun _ => Nat.le_succ _
  have hE : ComputableInSpace E enc encNat S :=
    budget_natAdd (budget_natAdd (budget_natMul (budget_const c) hsn) (budget_const (c₁ + c₂))) hsn
  have hT : ComputableInSpace T enc encNat S := by
    refine budget_natPow_variable (budget_const 2) hE ⟨3 * (c + c₁ + c₂ + 2), fun a => ?_⟩
    have h2 : (encNat 2).length = 2 := rfl
    have hEl : (encNat (E a)).length ≤ E a := length_encNat_le_of_lt_two_pow Nat.lt_two_pow_self
    simp only [h2, E, S] at hEl ⊢
    nlinarith
  obtain ⟨C, hC⟩ : ∃ C, ∀ a, Nat.size (T a) ≤ C * S a :=
    ⟨c + c₁ + c₂ + 2, fun a => by simp only [T, S, E, Nat.size_pow]; nlinarith⟩
  have hnT (a : α) : (enc a).length < 2 * T a := by
    have hE : Nat.log2 (n a) ≤ E a := by
      have := hlog (n a)
      simp only [E]
      omega
    have h' : 2 ^ (Nat.log2 (n a) + 1) ≤ 2 * T a := by
      rw [pow_succ, mul_comm]
      exact Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by norm_num) hE)
    exact Nat.lt_log2_self.trans_le h'
  have hA (a : α) :
      a ∈ A ↔ OutView.ofList (tm.runFrom (tm.initCfg (enc a)) (T a)).output = .one true := by
    have h₁ : c₁ + c₂ < 2 ^ (c₁ + c₂) := Nat.lt_two_pow_self
    have h₂ : 1 ≤ 2 ^ (c * s (n a)) := Nat.one_le_two_pow
    have h₃ : 1 ≤ 2 ^ s (n a) := Nat.one_le_two_pow
    have hle : c₁ * 2 ^ (c * s (enc a).length) + c₂ ≤ T a :=
      calc c₁ * 2 ^ (c * s (n a)) + c₂ ≤ (c₁ + c₂) * 2 ^ (c * s (n a)) := by nlinarith
        _ ≤ 2 ^ (c₁ + c₂) * 2 ^ (c * s (n a)) := Nat.mul_le_mul_right _ h₁.le
        _ ≤ 2 ^ (c₁ + c₂) * 2 ^ (c * s (n a)) * 2 ^ s (n a) := Nat.le_mul_of_pos_right _ h₃
        _ = T a := by simp only [T, E, pow_add]; ring
    obtain ⟨-, hout⟩ := (htm a).runFrom_of_le hle
    rw [hout]
    by_cases h : a ∈ A <;> simp [h, indicator, OutView.ofList]
  obtain ⟨k', State', hfin', atm, c', hatm⟩ := exists_decidesInSpace_of_runFrom tm T S hT
    (fun a => Nat.succ_le_succ (hlog _)) ⟨C, hC⟩ hnT hA
  refine ⟨k', State', hfin', atm, c', c', hatm.mono fun a => ?_⟩
  simp only [S, n, Nat.mul_succ, le_refl]

end Cslib.Complexity
