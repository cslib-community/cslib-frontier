/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Advice
public import CslibFrontier.Computability.Complexity.Classes.BPP
public import CslibFrontier.Probability.BitString

/-!
# Randomized computation with logarithmic advice

The four advice conventions in the Complexity Zoo differ in what counts as a valid decider
and in how advice is selected. In each case `n` denotes the original input length.

## Main definitions

* `IsPolyTimeAdviceVerifier`: the common verifier and encoding convention.
* `BPPLog`: the decider has bounded error on every pair, including pairs with incorrect advice.
* `BPPMLog`: only the selected advice must give bounded error.
* `BPPRLog`: advice is drawn from a length-dependent distribution independently of the verifier's
  coins [Aaronson, §2.1 and footnote 3][Aaronson2006DeMerlinizing].
* `BPPDoubleSlashLog`: advice depends on the length and the very coins used by the verifier
  [TrevisanVadhan2002].
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

/-- Semantic BPP with logarithmic Karp–Lipton advice [KarpLipton1980]. -/
@[expose] def BPPLog : Set (Set (List Bool)) :=
  ⋃ (c : ℕ), WithAdvice (BPP (encPair encBits encBits)) fun n => c * (Nat.log2 n + 1)

/-- The verifier reads the framed advice/input pair and a separate word of private coins. -/
@[expose] def IsPolyTimeAdviceVerifier (V : (List Bool × List Bool) × List Bool → Bool) :
    Prop :=
  ComputableInPolyTime V (encPair (encPair encBits encBits) encBits) encBool

/-- Syntactic BPP with logarithmic advice. Only the selected advice word must yield the correct
answer with probability at least two thirds. -/
@[expose] def BPPMLog : Set (Set (List Bool)) :=
  {A | ∃ (c : ℕ) (p : Polynomial ℕ) (advice : ℕ → List Bool)
      (V : (List Bool × List Bool) × List Bool → Bool),
    IsPolyTimeAdviceVerifier V ∧ (∀ n, (advice n).length = c * (Nat.log2 n + 1)) ∧
      ∀ x, ∃ b, (x ∈ A ↔ b = true) ∧
        BoundedErrorAt encBits p (fun (y, r) => V ((advice y.length, y), r)) x b}

/-- Logarithmic random advice, independent of the verifier's coins. The joint probability of a
correct answer is at least two thirds on each input
[Aaronson, §2.1 and footnote 3][Aaronson2006DeMerlinizing]. -/
@[expose] def BPPRLog : Set (Set (List Bool)) :=
  {A | ∃ (c : ℕ) (p : Polynomial ℕ) (advice : ℕ → PMF (List Bool))
      (V : (List Bool × List Bool) × List Bool → Bool),
    IsPolyTimeAdviceVerifier V ∧
      (∀ n, ∀ w ∈ (advice n).support, w.length = c * (Nat.log2 n + 1)) ∧
      ∀ x, ∃ b, (x ∈ A ↔ b = true) ∧
        (2 : ENNReal) / 3 ≤ ((advice x.length).bind fun w =>
          (BitString.uniformList (p.eval x.length)).map fun r => V ((w, x), r)) b}

/-- Logarithmic randomness-dependent advice. The same advice rule applies to all inputs of each
length and is evaluated on the verifier's own random word [TrevisanVadhan2002]. -/
@[expose] def BPPDoubleSlashLog : Set (Set (List Bool)) :=
  {A | ∃ (c : ℕ) (p : Polynomial ℕ) (advice : ℕ → List Bool → List Bool)
      (V : (List Bool × List Bool) × List Bool → Bool),
    IsPolyTimeAdviceVerifier V ∧ (∀ n r, (advice n r).length = c * (Nat.log2 n + 1)) ∧
      ∀ x, ∃ b, (x ∈ A ↔ b = true) ∧
        BoundedErrorAt encBits p (fun (y, r) => V ((advice y.length r, y), r)) x b}

end Cslib.Complexity
