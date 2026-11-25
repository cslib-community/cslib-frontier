/-
Copyright (c) 2026 Samuel Schlesinger, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Oracle.Closure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.Replay.Simulation
import CslibFrontier.Tactic.EncLen
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Automation
import Cslib.Foundations.Data.Polynomial.Monotone

/-!
# Binary search with a language oracle

A total deterministic program recovers F < 2^N from threshold requests k ≤ F in N rounds.
The strict polynomial-time certificate charges constructing requests, reading replies, and the
binary search state; N is supplied by a polynomial-time unary computation. This general search
is shared by ordinary and relativized counting clients.

## Main results

* `Cslib.Complexity.BinarySearch.interpret_id_search`: correctness against a threshold oracle.
* `Cslib.Complexity.BinarySearch.isOraclePPTOn_search`: the uniform strict resource certificate.
-/

public section

namespace Cslib.Complexity

open Probability Turing.MultiTapeTM

variable {α : Type}

/-! ### Binary search -/

namespace BinarySearch

/-- One round of binary search for a number `F`: in the state `(lo, j)` with `j > 0` bits left,
test whether `lo + 2 ^ (j - 1) ≤ F`, and keep the half containing `F`. -/
@[expose] def step (F : ℕ) (s : ℕ × ℕ) : ℕ × ℕ :=
  if s.2 = 0 then s else (if s.1 + 2 ^ (s.2 - 1) ≤ F then s.1 + 2 ^ (s.2 - 1) else s.1, s.2 - 1)

/-- **Binary search finds `F < 2 ^ N` in `N` rounds.** -/
theorem fst_iterate_step {F N : ℕ} (hF : F < 2 ^ N) : ((step F)^[N] (0, N)).1 = F := by
  have key (t : ℕ) (ht : t ≤ N) : ∃ lo, (step F)^[t] (0, N) = (lo, N - t) ∧ lo ≤ F ∧
      F < lo + 2 ^ (N - t) := by
    induction t with
    | zero => exact ⟨0, rfl, Nat.zero_le _, by simpa using hF⟩
    | succ t ih =>
      obtain ⟨lo, hlo, hle, hlt⟩ := ih (by omega)
      obtain ⟨j, hj⟩ : ∃ j, N - t = j + 1 := ⟨N - t - 1, by omega⟩
      rw [hj, pow_succ] at hlt
      rw [Function.iterate_succ_apply', hlo, step]
      simp only [hj, Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel,
        show N - (t + 1) = j by omega]
      split_ifs with h <;> exact ⟨_, rfl, by omega, by omega⟩
  obtain ⟨lo, hlo, hle, hlt⟩ := key N le_rfl
  simp only [Nat.sub_self, pow_zero] at hlt
  simpa only [hlo] using (by omega : lo = F)

/-! ### Binary search with an oracle -/

/-- One round of binary search with the oracle: in the state `(lo, j)` with `j > 0`, ask about the
code `encPair encBits encNat (u, lo + 2 ^ (j - 1))`, and keep the half selected by the reply. -/
@[expose] def searchQuery (u : List Bool) (s : ℕ × ℕ) : WordQueryComp Unit (ℕ × ℕ) :=
  if s.2 = 0 then pure s else
    (fun reply => (if reply == [true] then s.1 + 2 ^ (s.2 - 1) else s.1, s.2 - 1)) <$>
      (List.take 1 <$> OracleComp.query ((), encPair encBits encNat (u, s.1 + 2 ^ (s.2 - 1))))

/-- Binary search in `N` rounds with the oracle, about the codes `encPair encBits encNat (u, k)`. -/
@[expose] def search (u : List Bool) (N : ℕ) : WordQueryComp Unit ℕ :=
  Prod.fst <$> OracleComp.iterate N (searchQuery u) (0, N)

/-- A round of the search as a program with private coins and word queries. -/
private theorem interpret_searchQuery (u : List Bool) (s : ℕ × ℕ) :
    OracleComp.interpret ProbOracleComp.query (searchQuery u s) =
      if s.2 = 0 then pure s else
        (fun reply => (if reply == [true] then s.1 + 2 ^ (s.2 - 1) else s.1, s.2 - 1)) <$>
          (List.take 1 <$> ProbOracleComp.query (spec := fun _ : Unit × List Bool => List Bool)
            ((), encPair encBits encNat (u, s.1 + 2 ^ (s.2 - 1)))) := by
  unfold searchQuery; split <;> simp [OracleComp.interpret_map, OracleComp.interpret_query]

open Classical in
/-- Against an oracle containing the code of `(u, k)` exactly when `k ≤ F`, a round of the search
is `BinarySearch.step F`. -/
private theorem interpret_id_searchQuery {F : ℕ} {A : Set (List Bool)} {u : List Bool}
    (hA : ∀ k, encPair encBits encNat (u, k) ∈ A ↔ k ≤ F) (s : ℕ × ℕ) :
    OracleComp.interpret (m := Id) (languageOracle A) (searchQuery u s) =
      BinarySearch.step F s := by
  unfold searchQuery BinarySearch.step
  split
  · rfl
  · change (fun reply : List Bool =>
      (if reply == [true] then s.1 + 2 ^ (s.2 - 1) else s.1, s.2 - 1))
        (List.take 1 (languageOracle A ((), encPair encBits encNat (u, s.1 + 2 ^ (s.2 - 1))))) = _
    rw [languageOracle_apply, hA]
    by_cases hm : s.1 + 2 ^ (s.2 - 1) ≤ F <;> simp [hm]

open Classical in
/-- **Binary search finds the number.** Against an oracle containing the code of `(u, k)` exactly
when `k ≤ F`, the search in `N` rounds returns `F < 2 ^ N`. -/
theorem interpret_id_search {F N : ℕ} {A : Set (List Bool)} {u : List Bool}
    (hA : ∀ k, encPair encBits encNat (u, k) ∈ A ↔ k ≤ F) (hF : F < 2 ^ N) :
    OracleComp.interpret (m := Id) (languageOracle A) (search u N) = F := by
  rw [search, OracleComp.interpret_map]
  change (OracleComp.interpret (m := Id) (languageOracle A)
    (OracleComp.iterate N (searchQuery u) (0, N))).1 = F
  simpa only [OracleComp.interpret_id_iterate, interpret_id_searchQuery hA] using
    fst_iterate_step hF

/-- **Binary search is strict oracle PPT**: `N` rounds, with `N` computed in unary, each building
one request and reading one reply bit, on states of a binary number below `2 ^ N` and a unary
counter. -/
theorem isOraclePPTOn_search {input : α ↪ List Bool} {u : α → List Bool} {N : α → ℕ}
    (hu : ComputableInPolyTime u input encBits)
    (hN : ComputableInPolyTime N input encUnary) :
    IsOraclePPTOn input encNat
      (fun a => OracleComp.interpret ProbOracleComp.query (search (u a) (N a))) := by
  simp only [search, OracleComp.interpret_map, OracleComp.interpret_iterate]
  have hstep₀ : IsOraclePPTOn (encPair encBits (encPair encNat encUnary))
      (encPair encNat encUnary) fun pair =>
        OracleComp.interpret ProbOracleComp.query (searchQuery pair.1 pair.2) := by
    simp only [interpret_searchQuery]
    exact .ite (by fun_prop)
      (ComputableInPolyTime.snd encBits (encPair encNat encUnary)).isOraclePPTOn
      (.map_with (.query_take () (by fun_prop) (by fun_prop)) (by fun_prop))
  have hpreserve (a : α) (i : ℕ) (s : ℕ × ℕ) (hi : i < N a)
      (hinv : s.2 = N a - i ∧ s.1 + 2 ^ s.2 ≤ 2 ^ N a) (next : ℕ × ℕ)
      (hnext : next ∈ OracleComp.support
        (OracleComp.interpret ProbOracleComp.query (searchQuery (u a) s))) :
      next.2 = N a - (i + 1) ∧ next.1 + 2 ^ next.2 ≤ 2 ^ N a := by
    obtain ⟨hs, hlo⟩ := hinv
    rw [interpret_searchQuery, ite_eq_right (by omega), Functor.map_map] at hnext
    obtain ⟨reply, -, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hnext
    obtain ⟨j, hj⟩ : ∃ j, s.2 = j + 1 := ⟨s.2 - 1, by omega⟩
    rw [hj, pow_succ] at hlo
    simp only [hj, Nat.add_sub_cancel]
    split_ifs <;> omega
  have hbound (a : α) (i : ℕ) (s : ℕ × ℕ) (_ : i ≤ N a)
      (hinv : s.2 = N a - i ∧ s.1 + 2 ^ s.2 ≤ 2 ^ N a) :
      (encPair encNat encUnary s).length ≤ 3 * N a + 1 := by
    have hsize : (Nat.bits s.1).length ≤ N a := by
      rw [Nat.size_eq_bits_len]
      exact Nat.size_le.2 ((Nat.lt_add_of_pos_right (Nat.two_pow_pos _)).trans_le hinv.2)
    enc_len [encNat_apply]
  exact (IsOraclePPTOn.iterateWith_spec
    (step := fun a s => OracleComp.interpret ProbOracleComp.query (searchQuery (u a) s))
    hN ((ComputableInPolyTime.const 0).prod hN)
    (hstep₀.preprocess (prepare := fun pair : α × (ℕ × ℕ) => (u pair.1, pair.2)) (by fun_prop))
    (fun a i s => s.2 = N a - i ∧ s.1 + 2 ^ s.2 ≤ 2 ^ N a)
    (fun a => ⟨by simp, by simp⟩) hpreserve
    (size := fun a => 3 * N a + 1) (by growth_poly) hbound).1.map
    (ComputableInPolyTime.fst encNat encUnary)

end BinarySearch

end Cslib.Complexity
