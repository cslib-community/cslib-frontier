/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Alternation.Space
public import CslibFrontier.Computability.Circuit.Boolean.Tableau.Basic
import CslibFrontier.Computability.Circuit.Boolean.Tableau.LocalValueGame
import CslibFrontier.Computability.Circuit.Boolean.Tableau.Space
import CslibFrontier.Computability.Complexity.Classes.Time
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpaceLib
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.InputLength
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.AlternatingQueryMachine.Compiler
import CslibFrontier.Computability.Machines.Turing.MultiTape.Run
import Mathlib.Data.Nat.Size

/-!
# The local circuit-value game in alternating logarithmic space, and `AL = P`

A machine run for `T a` steps on the instance `a` is decided by the circuit-value game on its
tableau (`Cslib.Circuits.Boolean.Tableau.ValueGame`), and the local form of that game, which keeps
the length of the input, the step count, a wire and a value but not the input itself, is an
alternating query machine (`Cslib.Circuits.Boolean.Tableau.ValueGame.localMachine`) whose states
have `O(log n + log T)` bits. Compiling it into an alternating Turing machine
(`Turing.AlternatingQueryMachine.exists_decidesInSpace`) gives an alternating decider within space
`O(S)` whenever the step count `T` is computable within space `S ≥ log₂ n + 1` and `log T = O(S)`
(`Cslib.Complexity.exists_decidesInSpace_of_runFrom`). This is a step of the inclusion
`DTIME(2 ^ O(s)) ⊆ ASPACE(s)` of
[Chandra, Kozen and Stockmeyer, Theorem 3.4][ChandraKozenStockmeyer1981].

For a polynomial-time decider the step count `(n + 2) ^ D` is computable within space
`log₂ n + 1` and has `O(log n)` bits, so `P ⊆ AL` (`Cslib.Complexity.P_subset_AL`). With
`Cslib.Complexity.AL_subset_P` this gives `AL = P` (`Cslib.Complexity.AL_eq_P`)
[Chandra, Kozen and Stockmeyer, Section 3][ChandraKozenStockmeyer1981]
[Sipser, Section 10.3][Sipser2013], with no constructibility hypothesis: the step count is a
polynomial of the input length, which the alternating machine computes within its space bound.

## Main results

* `Cslib.Complexity.exists_decidesInSpace_of_runFrom`: a run whose step count is computable within
  space `S ≥ log₂ n + 1` and has `O(S)` bits is decided by an alternating machine within space
  `O(S)`.
* `Cslib.Complexity.P_subset_AL`: `P ⊆ AL`.
* `Cslib.Complexity.AL_eq_P`: `AL = P`.

## References

* [A. K. Chandra, D. C. Kozen, L. J. Stockmeyer, *Alternation*][ChandraKozenStockmeyer1981]
* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
-/

public section

namespace Cslib.Complexity

open _root_.Turing _root_.Turing.MultiTapeTM

open Circuits Circuits.Boolean Circuits.Boolean.Tableau Circuits.Boolean.Tableau.ValueGame
open ComputableInSpace

variable {α : Type} {enc : α ↪ List Bool}

/-- The start state of the local machine, the output claim of the tableau of `T a` steps, within
any budget `S ≥ log₂ n + 1` that covers the step count. -/
private theorem start_inSpace {k : ℕ} {State : Type} [Fintype State] {T S : α → ℕ}
    (hT : ComputableInSpace T enc encNat S) (hlog : ∀ a, Nat.log2 (enc a).length + 1 ≤ S a) :
    ComputableInSpace (fun a => ((⟨(enc a).length, T a,
        outWire k State (enc a).length (T a), true⟩ : LocalClaim), (none : Option Bool)))
      enc encLocalState S := by
  have hn : ComputableInSpace (fun a => (enc a).length) enc encNat S :=
    (inputLength_inSpace enc).mono_le hlog
  have hw : ComputableInSpace (fun a => outWire k State (enc a).length (T a)) enc encNat S :=
    outWire_inSpace (k := k) (State := State) hT hn
  have hc : ComputableInSpace (fun a => (⟨(enc a).length, T a,
      outWire k State (enc a).length (T a), true⟩ : LocalClaim)) enc encLocalClaim S :=
    encLocalClaim_mk_budget hn hT hw (budget_const true)
  exact budget_prod hc (budget_const (encB := encOption encBool) none)

/-- **A run is decided in alternating space `O(S)`** when its step count `T` is computable within
space `S ≥ log₂ n + 1` and has `O(S)` bits: if the instance `a` is in `A` exactly when `tm`, run for
`T a` steps on the encoded instance, has written exactly `[true]`, and the input is shorter than
`2 * T a`, then `A` is decided by a multi-tape alternating machine with a binary alphabet and
finitely many states within space `c * S a`, every branch halting. The alternating machine plays
the local circuit-value game on the tableau of `tm`
(`Cslib.Circuits.Boolean.Tableau.ValueGame.localMachine`), compiled by
`Turing.AlternatingQueryMachine.exists_decidesInSpace`. This is a step of the inclusion
`DTIME(2 ^ O(s)) ⊆ ASPACE(s)` of
[Chandra, Kozen and Stockmeyer, Theorem 3.4][ChandraKozenStockmeyer1981], not that inclusion: the
step count must be computable within the space bound. -/
theorem exists_decidesInSpace_of_runFrom {A : Set α} {k : ℕ} {State : Type} [Finite State]
    (tm : MultiTapeTM k Bool State) (T S : α → ℕ)
    (hT : ComputableInSpace T enc encNat S) (hlog : ∀ a, Nat.log2 (enc a).length + 1 ≤ S a)
    (hsize : ∃ c, ∀ a, Nat.size (T a) ≤ c * S a) (hnT : ∀ a, (enc a).length < 2 * T a)
    (hA : ∀ a, a ∈ A ↔ OutView.ofList (tm.runFrom (tm.initCfg (enc a)) (T a)).output = .one true) :
    ∃ (k' : ℕ) (State' : Type) (_ : Finite State') (atm : MultiTapeATM k' Bool State') (c : ℕ),
      atm.DecidesInSpace enc A fun a => c * S a := by
  have := Fintype.ofFinite State
  classical
  obtain ⟨cT, hcT⟩ := hsize
  obtain ⟨cs, hcs⟩ := exists_length_le_of_replay_localMachine (tm := tm)
  let lc₀ : LocalClaim := ⟨0, 0, 0, true⟩
  have hcorrect (a : α) : a ∈ A ↔ (localMachine tm lc₀).AcceptsFrom (enc a)
      (⟨(enc a).length, T a, outWire k State (enc a).length (T a), true⟩, none) :=
    (hA a).trans ((acceptsFrom_localMachine_iff lc₀ (enc a) (T a) _ (outWire_lt _ _) true).trans
      (wins_position_outWire_iff (encLocal (enc a)) (hnT a))).symm
  have hlen (a : α) (choices : List Bool) :
      (encLocalState ((localMachine tm lc₀).replay (enc a) choices
        (⟨(enc a).length, T a, outWire k State (enc a).length (T a), true⟩, none))).length ≤
        (8 + 12 * cT + cs) * S a := by
    have h := hcs lc₀ (enc a) (T a) _ true choices (outWire_lt _ _)
    have hn : Nat.size (enc a).length ≤ S a :=
      (Nat.size_le.mpr Nat.lt_log2_self).trans (hlog a)
    have h1 : 1 ≤ S a := le_of_add_le_right (hlog a)
    have := hcT a
    nlinarith
  exact AlternatingQueryMachine.exists_decidesInSpace (localMachine tm lc₀) localQuery_inSpace
    localNext_inSpace localHalted_inSpace localAccept_inSpace localUniversal_inSpace _
    (fun a => outWire k State (enc a).length (T a) + 1)
    (fun _ choices hc => halted_replay_localMachine lc₀ (outWire_lt _ _) choices hc) hcorrect S
    hlog (start_inSpace hT hlog) ⟨_, hlen⟩

/-- A polynomial time bound `c₁ * n ^ e + c₂` is at most `(n + 2) ^ D` for some `D ≠ 0`. -/
private theorem exists_pow_bound (c₁ c₂ e : ℕ) :
    ∃ D, D ≠ 0 ∧ ∀ n, c₁ * n ^ e + c₂ ≤ (n + 2) ^ D := by
  refine ⟨e + (c₁ + c₂) + 1, by omega, fun n => ?_⟩
  have h₁ : n ^ e ≤ (n + 2) ^ e := Nat.pow_le_pow_left (by omega) e
  have h₂ : 1 ≤ (n + 2) ^ e := Nat.one_le_pow _ _ (by omega)
  have h₃ : c₁ + c₂ < 2 ^ (c₁ + c₂) := Nat.lt_two_pow_self
  have h₄ : 2 ^ (c₁ + c₂) ≤ (n + 2) ^ (c₁ + c₂) := Nat.pow_le_pow_left (by omega) _
  calc c₁ * n ^ e + c₂ ≤ (c₁ + c₂) * (n + 2) ^ e := by nlinarith
    _ ≤ (n + 2) ^ (c₁ + c₂) * (n + 2) ^ e := Nat.mul_le_mul_right _ (h₃.le.trans h₄)
    _ ≤ (n + 2) ^ (e + (c₁ + c₂) + 1) := by
      rw [← pow_add, add_comm (c₁ + c₂) e]
      exact Nat.pow_le_pow_right (by omega) (by omega)

/-- The binary length of `(n + 2) ^ D` is at most `(log₂ n + 2) * D`. -/
private theorem size_pow_le (n : ℕ) {D : ℕ} (hD : D ≠ 0) :
    Nat.size ((n + 2) ^ D) ≤ (Nat.log2 n + 2) * D := by
  rw [Nat.size_le, pow_mul]
  refine Nat.pow_lt_pow_left ?_ hD
  have h := Nat.lt_log2_self (n := n)
  have hX : 1 ≤ 2 ^ Nat.log2 n := Nat.one_le_two_pow
  rw [pow_succ] at h
  rw [pow_succ, pow_succ]
  omega

/-- **`P ⊆ AL`** [Chandra, Kozen and Stockmeyer, Section 3][ChandraKozenStockmeyer1981]
[Sipser, Section 10.3][Sipser2013]: every problem decided in polynomial time is decided by a
multi-tape alternating machine with a binary alphabet and finitely many states within space
`c * (log₂ n + 1)`, every branch halting. The alternating machine plays the local circuit-value
game on the tableau of `(n + 2) ^ D` steps of the polynomial-time decider; the step count is
computed within the space bound, so no constructibility hypothesis is needed. -/
theorem P_subset_AL : P enc ⊆ AL enc := by
  intro A hA
  obtain ⟨e, c₁, c₂, s, k, State, hfin, tm, htm⟩ := mem_P_iff_exists_mem_DTIME.mp hA
  obtain ⟨D, hD, hle⟩ := exists_pow_bound c₁ c₂ e
  have hT := budget_natPow (budget_natAdd (inputLength_inSpace enc) (budget_const 2)) D
  refine exists_decidesInSpace_of_runFrom tm (fun a => ((enc a).length + 2) ^ D) _ hT
    (fun _ => le_rfl) ⟨2 * D, fun a => ?_⟩ (fun a => ?_) (fun a => ?_)
  · have := size_pow_le (enc a).length hD
    nlinarith
  · have := Nat.le_self_pow hD ((enc a).length + 2)
    omega
  · obtain ⟨-, hout⟩ := (htm a).runFrom_of_le (hle (enc a).length)
    rw [hout]
    by_cases h : a ∈ A <;> simp [h, indicator, OutView.ofList]

/-- **`AL = P`** [Chandra, Kozen and Stockmeyer, Section 3][ChandraKozenStockmeyer1981]
[Sipser, Section 10.3][Sipser2013]: alternating logarithmic space, for multi-tape alternating
machines with a binary alphabet within space `c * (log₂ n + 1)`, every branch halting, is
deterministic polynomial time. -/
theorem AL_eq_P : AL enc = P enc :=
  le_antisymm AL_subset_P P_subset_AL

end Cslib.Complexity
