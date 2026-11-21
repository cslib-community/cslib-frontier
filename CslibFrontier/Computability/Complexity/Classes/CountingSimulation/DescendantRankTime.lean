/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.CountingSimulation.RootRankTime
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.CarryLookaheadCountingRawLeaves
import CslibFrontier.Foundations.Data.Nat.BinarySize

/-!
# Accumulating the native counting overhead along an ancestry branch

At every reduction of a descendant endpoint query, a branch enters a single recursive leaf
after its local counting clock. A list of such count and width pairs incurs the sum of those
clocks plus one terminal lookup. If the number of reductions and the bit lengths of their
parameters are polynomial in the binary source clock, the whole counting overhead fits in the
number of logarithmic blocks. This estimate leaves the terminal lookup with coefficient one.
-/

public section

namespace Cslib.Complexity.CountingSimulation

open _root_.Turing.MultiTapeATM

/-- The branch clock obtained by repeatedly applying the six-tape counter's additive
running-time bound to the remaining ancestry, including the finite-control transition to the
next entry. Each pair holds the count and width. -/
def ancestryClock (A D : ℕ) (requests : List (ℕ × ℕ)) (terminal : ℕ) : ℕ :=
  requests.foldr (fun p t =>
    A * (p.1.size + p.2.size + 1) ^ D + (CarrySaveCountingRoot.sizeBudget p.1 p.2 + 4) + t)
    terminal

/-- Polynomially many short recursive counting requests fit into the source block count,
while the physical running time of the final leaf is added exactly once. -/
theorem exists_ancestryClock_le_numBlocks (A D c d : ℕ) :
    ∃ C, ∀ (t terminal : ℕ) (requests : List (ℕ × ℕ)),
      let bound := c * ((t + 2).size + 1) ^ d
      requests.length ≤ bound → (∀ p ∈ requests, p.1.size + p.2.size + 1 ≤ bound) →
      ancestryClock A D requests terminal ≤ C * (numBlocks t + 1) + terminal := by
  let E := max D 1
  obtain ⟨K, hK⟩ := exists_size_pow_le_numBlocks (d * (E + 1))
  refine ⟨(A + 4) * c ^ (E + 1) * K, ?_⟩
  intro t terminal requests B hlen hparams
  have hlocal (p : ℕ × ℕ) (hp : p.1.size + p.2.size + 1 ≤ B) :
      A * (p.1.size + p.2.size + 1) ^ D + (CarrySaveCountingRoot.sizeBudget p.1 p.2 + 4) ≤
        (A + 4) * B ^ E := by
    let z := p.1.size + p.2.size + 1
    have hpos : 0 < B := by omega
    have hz : z ≤ B ^ E := hp.trans (by
      simpa only [Nat.pow_one] using Nat.pow_le_pow_right hpos (Nat.le_max_right D 1))
    have hd : z ^ D ≤ B ^ E :=
      (Nat.pow_le_pow_left hp _).trans (Nat.pow_le_pow_right hpos (Nat.le_max_left D 1))
    have hc : Nat.clog 2 p.1 ≤ p.1.size := Nat.clog_le_of_le_pow (Nat.lt_size_self _).le
    have hh := (Nat.size_le_self _).trans hc
    rw [Nat.add_mul]
    change A * z ^ D + ((Nat.clog 2 p.1).size + p.2.size + Nat.clog 2 p.1 + 4) ≤ _
    apply Nat.add_le_add (Nat.mul_le_mul_left _ hd)
    dsimp only [z] at hz
    omega
  have hsum (ps : List (ℕ × ℕ)) (hps : ∀ p ∈ ps, p.1.size + p.2.size + 1 ≤ B) :
      ancestryClock A D ps terminal ≤ (A + 4) * B ^ E * ps.length + terminal := by
    induction ps with
    | nil => simp [ancestryClock]
    | cons p ps ih =>
      have hs := ih (fun z hz => hps z (List.mem_cons_of_mem _ hz))
      have hhead := hlocal p (hps p List.mem_cons_self)
      change _ + ancestryClock A D ps terminal ≤ _
      rw [List.length_cons, Nat.mul_succ]
      omega
  calc
    ancestryClock A D requests terminal ≤ (A + 4) * B ^ E * requests.length + terminal :=
      hsum requests hparams
    _ ≤ (A + 4) * B ^ E * B + terminal :=
      Nat.add_le_add_right (Nat.mul_le_mul_left _ hlen) _
    _ = (A + 4) * c ^ (E + 1) * (((t + 2).size + 1) ^ (d * (E + 1))) + terminal := by
      rw [Nat.mul_assoc, ← Nat.pow_succ]
      simp only [B, Nat.mul_pow, Nat.pow_mul, Nat.mul_assoc]
    _ ≤ _ := Nat.add_le_add_right (by
      rw [Nat.mul_assoc ((A + 4) * c ^ (E + 1)) K]
      exact Nat.mul_le_mul_left _ (hK t)) _

/-- With one terminal root scan at its source-clock rate, the whole ancestry charge obeys
the square-root-logarithmic bound. -/
theorem exists_ancestryClock_le_target (A D c d rootRate : ℕ) :
    ∃ K, ∀ (t terminal : ℕ) (requests : List (ℕ × ℕ)),
      let bound := c * ((t + 2).size + 1) ^ d
      terminal ≤ rootRate * (numBlocks t + 1) → requests.length ≤ bound →
      (∀ p ∈ requests, p.1.size + p.2.size + 1 ≤ bound) →
      ancestryClock A D requests terminal ≤ K * (t / (Nat.log 2 (t + 2)).sqrt + 1) := by
  obtain ⟨C, hC⟩ := exists_ancestryClock_le_numBlocks A D c d
  refine ⟨2 * (C + rootRate), ?_⟩
  intro t terminal requests bound hroot hlen hparams
  have h := (hC t terminal requests hlen hparams).trans (Nat.add_le_add_left hroot _)
  rw [← Nat.add_mul] at h
  refine h.trans ?_
  rw [Nat.mul_assoc, Nat.mul_left_comm]
  have ht := Nat.succ_le_succ (numBlocks_le_div_sqrt_log_add_one t)
  have h₂ (n : ℕ) : n + 1 + 1 ≤ 2 * (n + 1) := by omega
  exact Nat.mul_le_mul_left _ (ht.trans (h₂ _))

end Cslib.Complexity.CountingSimulation
