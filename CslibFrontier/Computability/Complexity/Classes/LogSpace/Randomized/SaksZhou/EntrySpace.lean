/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.LogSpace.Randomized.SaksZhou.Base
public import CslibFrontier.Computability.Complexity.Classes.LogSpace.Randomized.SaksZhou.SweepCorrectness
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.FunProp

/-!
# Evaluating a Saks–Zhou matrix entry in bounded space

Each suspended invocation stores a matrix address and binary counters. The original word stays
on the input tape and all levels read the same packed seed. Only the active invocation needs
workspace for generating a pseudorandom letter or for applying the rounding shift.

## Main results

* `Turing.MultiTapePTM.ConfigurationGraph.saksZhouEntryValue_inSpace` evaluates the rounded
  numerator with workspace bounded by the query length plus the three-halves power of the
  logarithm of the word length.
-/

public section

namespace Turing.MultiTapePTM.ConfigurationGraph

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInSpace Cslib.Probability.SaksZhou
open Turing.MultiTapeNTM.ConfigurationGraph
open scoped Turing.MultiTapeTM

private abbrev Input := SaksZhouEntry × List Bool
private abbrev encInput := encPair encSaksZhouEntry encBits
private abbrev encConfig := encPair encSweepFrame (encOption encNat)

private def inputBudget (a : Input) :=
  2 * (encSaksZhouEntry a.1).length + Nat.log2 a.2.length + 2
private def bodyBudget (p : SweepInput Input) := (encConfig p.1).length + inputBudget p.2

private theorem log_input_le (a : Input) : Nat.log2 (encInput a).length ≤ inputBudget a :=
  log2_length_encPair_le encSaksZhouEntry encBits a

private theorem onContext {γ : Type} {eg : γ ↪ List Bool} {f : Input → γ}
    (h : ComputableInSpace f encInput eg inputBudget) :
    ComputableInSpace (fun p : SweepInput Input => f p.2) (encSweepInput encInput) eg bodyBudget :=
  h.comp_logSpace_context (.snd _ _) (.of_le fun _ => Nat.le_add_left ..) log_input_le

private theorem config_inSpace :
    ComputableInSpace (Prod.fst : SweepInput Input → _) (encSweepInput encInput) encConfig
      bodyBudget :=
  ((ComputableInLogSpace.fst encConfig encInput).inSpace_context
    (.of_le fun _ => Nat.le_add_right ..)).mono_le fun p =>
      Nat.add_le_add_left (log_input_le p.2) _

variable {k : ℕ} {State : Type} [Fintype State] (M : MultiTapePTM k Bool State) (c clk : ℕ)

private theorem size_on_input :
    ComputableInSpace (fun p : Input => saksZhouSweepSize k State c clk p.2.length)
      encInput encSaksZhouSweepSize inputBudget :=
  (saksZhouSweepSize_inSpace_context encSaksZhouEntry k State c clk).mono_le fun p => by
    dsimp only [inputBudget]
    omega

private theorem entry_on_input :
    ComputableInSpace (Prod.fst : Input → _) encInput encSaksZhouEntry inputBudget :=
  ((ComputableInLogSpace.fst encSaksZhouEntry encBits).inSpace_context
    (.of_le fun _ => Nat.le_add_right ..)).mono_le fun p => by
      simp only [inputBudget, encBits_apply]
      omega

private theorem base_on_frame :
    ComputableInSpace (fun ((f, _), p) =>
      let B := radix (radixExponent State c) p.2.length
      let n := vertexBound (k := k) B
      if f.job.row < n ∧ f.job.column < n then
        coinCountWithSymbol M B p.2.length f.job.row f.job.column p.2[queryIndex (k := k)
          B f.job.row]? * 2 ^ (saksZhouPrecision clk p.2.length - 1)
      else 0) (encSweepInput encInput) encNat bodyBudget := by
  have hc := budget_id (enc := encConfig) (BigOLe.refl _)
  have hj := NestedLoop.encFrame_job_budget SweepJob SweepState encSweepJob encSweepState hc.fst'
  have h := saksZhouBaseCounts_inSpace_context M c clk
    (encSweepJob_row_budget hj) (encSweepJob_column_budget hj)
  have proj : ComputableInLogSpace (fun p : SweepInput Input => (p.1, p.2.2))
      (encSweepInput encInput) (encPair encConfig encBits) := by fun_prop
  have h' := h.comp_logSpace_context (S := inputBudget) proj (BigOLe.of_le fun p => by
    change (encConfig p.1).length + Nat.log2 p.2.2.length ≤
      (encConfig p.1).length + inputBudget p.2
    dsimp only [inputBudget]; omega) log_input_le
  apply h'.of_enc_eq
  rintro ⟨⟨f, o⟩, p⟩
  dsimp only
  split_ifs <;> simp_all [saksZhouBaseCounts]

private theorem body_inSpace :
    ComputableInSpace (saksZhouEntryLoop M c clk).body (encSweepInput encInput)
      (NestedLoop.encBodyOutput encSweepJob encSweepState encNat) bodyBudget := by
  have sizes := onContext (size_on_input (k := k) (State := State) c clk)
  have hd := encSaksZhouSweepSize_precision_budget sizes
  have hb := encSaksZhouSweepSize_blockWidth_budget sizes
  have hlevels := encSaksZhouSweepSize_levels_budget sizes
  have hseed := onContext (encSaksZhouEntry_seed_budget entry_on_input)
  have hreg := NestedLoop.encFrame_reg_budget SweepJob SweepState encSweepJob encSweepState
    config_inSpace.fst'
  have hdepth := NestedLoop.encFrame_level_budget SweepJob SweepState encSweepJob encSweepState
    config_inSpace.fst'
  have hwidth : (fun p : SweepInput Input => 2 * (5 * saksZhouPrecision clk p.2.2.length)) ≼
      bodyBudget := by
    apply BigOLe.of_le_linear (50 * clk) (100 * clk + 100)
    intro p
    simp only [saksZhouPrecision, bodyBudget, inputBudget]
    nlinarith
  have hn := encSaksZhouSweepSize_vertices_budget sizes
  have ht := encSaksZhouSweepSize_steps_budget sizes
  have hs := encSaksZhouSweepSize_starts_budget sizes
  have hm := encSaksZhouSweepSize_scale_budget sizes
  have hp := encSaksZhouSweepSize_denominator_budget sizes
  dsimp only [saksZhouSweepSize] at hn ht hs hm hp hb hlevels hd
  dsimp only [saksZhouEntryLoop, nisanSweepLoop]
  refine sweepLoop_body_inSpace (enc := encInput) (S := bodyBudget)
    (n := fun p : Input => vertexBound (k := k) (radix (radixExponent State c) p.2.length))
    (steps := fun p => 2 ^ saksZhouLevels clk p.2.length)
    (starts := fun p => 2 ^ (2 * (5 * saksZhouPrecision clk p.2.length)))
    (scale := fun p => 2 ^ (2 * (5 * saksZhouPrecision clk p.2.length) -
      saksZhouPrecision clk p.2.length))
    (letter := fun p x t => nisanBlockValue (2 * (5 * saksZhouPrecision clk p.2.length))
      (saksZhouLevels clk p.2.length) p.1.seed x t)
    (base := fun p j => let B := radix (radixExponent State c) p.2.length
      coinCountWithSymbol M B p.2.length j.row j.column p.2[queryIndex (k := k) B j.row]? *
        2 ^ (saksZhouPrecision clk p.2.length - 1))
    (roundValue := fun p level hits => let d := saksZhouPrecision clk p.2.length
      let b := 2 * (5 * d)
      snapCount (2 ^ d) hits (2 ^ b)
        (nisanRoundingShift b (saksZhouLevels clk p.2.length) d p.1.seed (level - 1)))
    config_inSpace hn ht hs hm ?_ ?_ ?_
  · exact budget_nisanBlockValue hb hlevels hseed (encSweepState_x_budget hreg)
      (encSweepState_t_budget hreg) hwidth
  · exact base_on_frame M c clk
  · intro hits hh
    exact computableInSpace_snapCount hp hh hs
      (budget_nisanRoundingShift hb hlevels hd hseed (budget_natPred hdepth))

private theorem length_max {α : Type} {u v S : α → ℕ}
    (hu : (fun a => (encNat (u a)).length) ≼ S)
    (hv : (fun a => (encNat (v a)).length) ≼ S) :
    (fun a => (encNat (max (u a) (v a))).length) ≼ S := by
  simpa only [max_def, apply_ite] using BigOLe.ite (fun a => u a ≤ v a) hv hu

private theorem entryBudget_le {α : Type} (clk : ℕ)
    {Q F A inputLog : α × List Bool → ℕ}
    (hF : F ≼ fun p => Nat.log2 p.2.length)
    (hA : A ≼ fun p => Nat.log2 p.2.length)
    (hlog : ∀ p, inputLog p ≤ 2 * Q p + Nat.log2 p.2.length + 2) :
    (fun p => let G := 2 * Q p + Nat.log2 p.2.length + 2
              G + (saksZhouLevels clk p.2.length * (F p + 1) + (2 * F p + A p + G + 2)) +
                inputLog p) ≼ fun p => Q p + saksZhouSpace p.2.length := by
  let B := fun p : α × List Bool => Q p + saksZhouSpace p.2.length
  have hdepth : (fun p : α × List Bool => saksZhouLevels clk p.2.length) ≼
      fun p => Nat.sqrt (Nat.log2 p.2.length + 1) :=
    ⟨2 * clk + 2, fun p => Cslib.Complexity.saksZhou_levels_le clk (Nat.log2 p.2.length)⟩
  have hrec : (fun p => saksZhouLevels clk p.2.length * (F p + 1)) ≼ B :=
    (hdepth.mul (hF.add (.const 1 _))).trans_le fun p => by
      dsimp only [B, saksZhouSpace]
      rw [Nat.mul_comm]
      omega
  have hQ : Q ≼ B := .of_le fun p => Nat.le_add_right _ _
  have hℓ : (fun p : α × List Bool => Nat.log2 p.2.length) ≼ B :=
    .of_le fun p => (log2_le_saksZhouSpace p.2.length).trans (Nat.le_add_left _ _)
  have hG : (fun p => 2 * Q p + Nat.log2 p.2.length + 2) ≼ B := by bigO
  have hinput : inputLog ≼ B := (BigOLe.of_le hlog).trans hG
  change _ ≼ B
  dsimp only
  bigO

/-- The native read-only-word evaluator computes the seeded matrix entry using the space of
the stored entry query and the Saks–Zhou three-halves logarithmic workspace. -/
theorem saksZhouEntryValue_inSpace :
    ComputableInSpace (saksZhouEntryValue M c clk) (encPair encSaksZhouEntry encBits) encNat
      (fun p => (encSaksZhouEntry p.1).length + saksZhouSpace p.2.length) := by
  let z (p : Input) := saksZhouSweepSize k State c clk p.2.length
  let root (p : Input) : SweepJob :=
    ⟨min p.1.row ((z p).vertices + 1), min p.1.column ((z p).vertices + 1)⟩
  let A (p : Input) := (encNat (z p).denominator).length
  have sizes := size_on_input (k := k) (State := State) c clk
  have hn := encSaksZhouSweepSize_vertices_budget sizes
  have hroot : ComputableInSpace root encInput encSweepJob inputBudget :=
    encSweepJob_mk_budget
      (budget_natMin (encSaksZhouEntry_row_budget entry_on_input) (budget_natSucc hn))
      (budget_natMin (encSaksZhouEntry_column_budget entry_on_input) (budget_natSucc hn))
  have hi := NestedLoop.encFrame_mk_budget SweepJob SweepState encSweepJob encSweepState
    (encSaksZhouSweepSize_levels_budget sizes) hroot (encSaksZhouSweepSize_rounds_budget sizes)
    (sweepStart_inSpace hn (encSweepJob_row_budget hroot))
  dsimp only [saksZhouSweepSize, root, z] at hi
  have hinit : ComputableInSpace (fun p : Input =>
      (saksZhouEntryLoop M c clk).entry p (z p).levels (root p)) encInput encSweepFrame
      inputBudget := by
    dsimp only [saksZhouEntryLoop, nisanSweepLoop, NestedLoop.entry, sweepLoop,
      saksZhouSweepSize, root, z]
    exact hi
  have hb := body_inSpace M c clk
  dsimp only [saksZhouEntryLoop, nisanSweepLoop] at hb hinit
  have hrun := sweepLoop_inSpace (D := fun p => (z p).levels) (S := inputBudget)
    (G := inputBudget) (answerBits := A) (enc := encInput) (root := root)
    (n := fun p => (z p).vertices) (steps := fun p => (z p).steps)
    (starts := fun p => (z p).starts) (scale := fun p => (z p).scale)
    (fun p => And.intro (min_le_right ..) (min_le_right ..))
    (fun p x t => Nat.le_of_lt (Nat.mod_lt _ (by positivity : 0 < 2 ^ (z p).blockWidth)))
    (fun p depth job _ _ _ => length_encNat_mono (saksZhouEntryLoop_run_le M c clk p depth job))
    hinit hb
  refine (hrun.weaken ?_).of_enc_eq fun p =>
    congrArg encNat (saksZhouEntryLoop_run M c clk p).symm
  have hs := saksZhouSweepSize_inSpace k State c clk
  have hM := length_max
    (length_max (encSaksZhouSweepSize_levels_budget hs).length_le
      (budget_natSucc (encSaksZhouSweepSize_vertices_budget hs)).length_le)
    (length_max (encSaksZhouSweepSize_starts_budget hs).length_le
      (encSaksZhouSweepSize_rounds_budget hs).length_le)
  exact entryBudget_le clk (((hM.add (.const 1 _)).const_mul 32).comp Prod.snd)
    ((encSaksZhouSweepSize_denominator_budget hs).length_le.comp Prod.snd) log_input_le

end Turing.MultiTapePTM.ConfigurationGraph
