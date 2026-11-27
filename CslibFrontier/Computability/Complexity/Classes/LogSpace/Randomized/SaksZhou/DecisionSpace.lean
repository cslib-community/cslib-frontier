/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.LogSpace.Randomized.SaksZhou.Decision
import CslibFrontier.Computability.Complexity.Classes.LogSpace.Randomized.SaksZhou.EntrySpace
public import CslibFrontier.Computability.Complexity.Classes.Space.Quantitative
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.StoredBind
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.StoredCount
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.FunProp
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.ConfigurationGraph.Routines
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram.Unary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Words

/-!
# The Saks–Zhou logarithmic-space simulation

Saks and Zhou's Theorem 1.1 [SaksZhou1999, p. 378] specializes to `S(n) = log n` for
always-halting fair-coin machines with two-sided error at most one third. The input may be any
type with an explicit bit-string encoding. Work space is measured on the tapes of the native
multitape machine as a function of the encoded input length.

The deterministic machine enumerates packed seeds, sums the rounded numerators from the initial
configuration to all accepting halts, and takes the strict majority of the resulting threshold
bits. The recursion reads one matrix entry at a time. The final counter and its loop bound fit
in the same workspace as the seeds.

## Main results

* `Turing.MultiTapePTM.ConfigurationGraph.saksZhouSeedAccepts_inSpace` computes the threshold
  bit for one packed seed.
* `Cslib.Complexity.BPL_subset_DSPACE_log2_mul_sqrt` gives the deterministic space bound
  `O(log n · √log n)`.

## References

* [M. Saks and S. Zhou, *BP_H SPACE(S) ⊆ DSPACE(S^{3/2})*][SaksZhou1999], §1, pp. 377–378,
  Theorem 1.1.
-/

public section

namespace Turing.MultiTapePTM.ConfigurationGraph

open MultiTapeNTM.ConfigurationGraph MultiTapeTM MultiTapeTM.ComputableInSpace Finset

private abbrev encSeedWord := encPair encNat encBits

private abbrev seedBudget (p : ℕ × List Bool) :=
  2 * (encNat p.1).length + saksZhouSpace p.2.length + 2

private theorem log_seed_le (p : ℕ × List Bool) :
    Nat.log2 (encSeedWord p).length ≤ seedBudget p :=
  (log2_length_encPair_le encNat encBits p).trans (by
    have := log2_le_saksZhouSpace p.2.length
    simp only [seedBudget, encBits_apply]
    omega)

private abbrev columnBudget (q : ℕ × (ℕ × List Bool)) :=
  2 * (encNat q.1).length + seedBudget q.2 + 2

private theorem log_column_le (q : ℕ × (ℕ × List Bool)) :
    Nat.log2 (encPair encNat encSeedWord q).length ≤ columnBudget q :=
  (log2_length_encPair_le encNat encSeedWord q).trans (by
    have := log_seed_le q.2
    simp only [columnBudget]
    omega)

private theorem onSeedInput {β : Type} {enc : β ↪ List Bool} {g : List Bool → β}
    (hg : ComputableInSpace g encBits enc fun w => Nat.log2 w.length) :
    ComputableInSpace (fun p : ℕ × List Bool => g p.2) encSeedWord enc seedBudget :=
  (hg.comp_logSpace_context (S := fun w : List Bool => saksZhouSpace w.length)
    (ComputableInLogSpace.snd encNat encBits)
    (.of_le fun p => (log2_le_saksZhouSpace p.2.length).trans (Nat.le_add_left _ _))
    (fun (w : List Bool) => by simpa only [encBits_apply] using log2_le_saksZhouSpace w.length))
      |>.mono_le fun p => by simp only [seedBudget]; omega

private theorem onColumn {β : Type} {enc : β ↪ List Bool} {g : ℕ × List Bool → β}
    (hg : ComputableInSpace g encSeedWord enc seedBudget) :
    ComputableInSpace (fun q : ℕ × (ℕ × List Bool) => g q.2) (encPair encNat encSeedWord) enc
      columnBudget :=
  (hg.comp_logSpace_context (ComputableInLogSpace.snd encNat encSeedWord)
    (.of_le fun _ => Nat.le_add_left _ _) log_seed_le).mono_le fun q => by
      simp only [columnBudget]; omega

variable {k : ℕ} {State : Type} [Fintype State] (M : MultiTapePTM k Bool State) (c clk : ℕ)

/-- Sum the accepting positions of the rounded row and compare with half the grid denominator.
The seed and the input word are given separately to the native machine. -/
theorem saksZhouSeedAccepts_inSpace :
    ComputableInSpace (saksZhouSeedAccepts M c clk) (encPair encNat encBits) encBool
      fun p => (encNat p.1).length + saksZhouSpace p.2.length := by
  have hn := onSeedInput
    (computableInLogSpace_bitsLength.inSpace_of_length_log length_bitsLength_log)
  have hB := radix_budget (radixExponent State c) hn
  have hN := vertexBound_budget (k := k) hB
  have hz : ComputableInSpace (fun p : ℕ × List Bool => p.1) encSeedWord encNat seedBudget :=
    ((ComputableInLogSpace.fst encNat encBits).inSpace_context
      (.of_le fun _ => Nat.le_add_right _ _))
      |>.mono_le fun p => by
        have := log2_le_saksZhouSpace p.2.length
        simp only [seedBudget, encBits_apply]
        omega
  have hj : ComputableInSpace (fun q : ℕ × (ℕ × List Bool) => q.1)
      (encPair encNat encSeedWord) encNat columnBudget :=
    ((ComputableInLogSpace.fst encNat encSeedWord).inSpace_context
      (.of_le fun _ => Nat.le_add_right _ _))
      |>.mono_le fun q => by
        have := log_seed_le q.2
        simp only [columnBudget]
        omega
  have hreq := encSaksZhouEntry_mk_budget (onColumn hz) (onColumn (startID_budget M.toNTM hB)) hj
  have heval := saksZhouEntryValue_inSpace M c clk
  have hcall := heval.comp_logSpace_context (f := fun p : SaksZhouEntry × (ℕ × (ℕ × List Bool)) =>
      (p.1, p.2.2.2)) (S := columnBudget) (by fun_prop)
    (.of_le fun p => by simp only [columnBudget, seedBudget]; omega) log_column_le
  have hentry := (hreq.bindWith hcall).weaken (.of_le_linear 6 6 fun q => by
    have := log_column_le q
    simp only [columnBudget] at *
    omega : (fun q => columnBudget q + columnBudget q +
      Nat.log2 (encPair encNat encSeedWord q).length)
      ≼ fun q => (encNat q.1).length + seedBudget q.2)
  have hbad := (bad_budget (k := k) (State := State) (onColumn hB) (onColumn hn) hj).weaken
    (.of_le_linear 2 2 fun q => by simp only [columnBudget]; omega :
      columnBudget ≼ fun q => (encNat q.1).length + seedBudget q.2)
  have hd := onSeedInput (saksZhouDenominator_inSpace clk)
  have hsum := hN.sumWith (budget_ite hbad hentry (budget_const 0)) (BigOLe.trans
    (.of_le fun p => length_encNat_mono (saksZhouAcceptNumerator_le M c clk p.1 p.2)) hd.length_le)
  exact (budget_natLt (hd.mono_le fun p => Nat.le_add_right _ _)
    (budget_natMul (budget_const 2) hsum))
    |>.weaken (.of_le_linear 4 4 fun p => by
      have := log_seed_le p
      simp only [seedBudget] at *
      omega : (fun p => seedBudget p + Nat.log2 (encSeedWord p).length) ≼
        fun p => (encNat p.1).length + saksZhouSpace p.2.length)

/-- The native strict majority of all packed seed tests uses three-halves logarithmic space. -/
theorem saksZhouMajority_inSpace :
    ComputableInSpace (fun w : List Bool => decide (saksZhouSeedCount clk w.length <
      2 * (List.range (saksZhouSeedCount clk w.length)).countP
        fun z => saksZhouSeedAccepts M c clk (z, w))) encBits encBool
      fun w => saksZhouSpace w.length :=
  ((saksZhouSeedCount_inSpace clk).majorityWith
    (saksZhouSeedAccepts_inSpace M c clk)).weaken (.of_le_linear 2 0 fun w => by
      have := log2_le_saksZhouSpace w.length
      simp only [encBits_apply]
      omega)

end Turing.MultiTapePTM.ConfigurationGraph

namespace Cslib.Complexity

open _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.MultiTapePTM.ConfigurationGraph

/-- **Saks–Zhou's logarithmic-space containment** [SaksZhou1999, Theorem 1.1, p. 378].
Every encoded language decided by an always-halting randomized logspace machine with error at
most one third is decided on the same encoding by a deterministic multitape machine using
`O(log n · √log n)` work-tape cells. The additive constant in `DSPACE` handles the empty and
one-bit input lengths. -/
theorem BPL_subset_DSPACE_log2_mul_sqrt {α : Type} {enc : α ↪ List Bool} :
    BPL enc ⊆ DSPACE enc (fun n => Nat.log2 n * Nat.sqrt (Nat.log2 n)) := by
  intro A hA
  obtain ⟨k, State, hfin, M, c, clk, hs⟩ := exists_saksZhouSeeds_of_mem_BPL hA
  have hdec := (saksZhouMajority_inSpace M c clk).of_encIn_eq enc
    fun a => (encBits_apply (enc a)).symm
  refine DSPACE_mono_of_le_mul_add (s₁ := saksZhouSpace) (C := 6) (fun n => ?_) ?_
  · let ℓ := Nat.log2 n
    change (ℓ + 1) * (Nat.sqrt (ℓ + 1) + 1) ≤ 6 * (ℓ * Nat.sqrt ℓ) + 6
    by_cases h : ℓ = 0
    · simp [h]
    · have hp : 1 ≤ Nat.sqrt ℓ := Nat.sqrt_pos.mpr (Nat.pos_of_ne_zero h)
      have ha := Nat.mul_le_mul_left ℓ hp
      have hb := Nat.sqrt_le_self ℓ
      have hc := Nat.sqrt_succ_le_succ_sqrt ℓ
      have hd := Nat.mul_le_mul_left (ℓ + 1) (Nat.add_le_add_right hc 1)
      nlinarith
  · convert setOf_mem_DSPACE_of_computableInSpace hdec (s := saksZhouSpace) fun _ => le_rfl using 1
    ext a
    obtain ⟨hspace, -, -, -, hyes, hno⟩ := hs a
    simp only [Set.mem_ofPred_eq, decide_eq_true_eq, saksZhou_majority_iff M c clk hspace]
    exact ⟨hyes, fun h => by_contra fun ha => absurd h (lt_asymm (hno ha))⟩
end Cslib.Complexity
