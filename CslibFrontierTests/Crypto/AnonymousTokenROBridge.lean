/-
Copyright (c) 2026 Samuel Schlesinger, Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Karn Seth
-/

module

import CslibFrontier.Crypto.Protocols.AnonymousToken.Basic
import CslibFrontier.Crypto.Protocols.AnonymousToken.Conservation
import CslibFrontier.Crypto.Protocols.AnonymousToken.ROBridge
import CslibFrontier.Crypto.Protocols.FAEST.Conversion
import CslibFrontier.Crypto.Protocols.VOLE.ROExtractor
import CslibFrontier.Languages.Probabilistic.QueryCount.Sum
import CslibFrontier.Probability.PMF.Support
import Mathlib.Tactic.NormNum

/-!
# Clients for straight-line VOLEitH ROM bridges to `AnonymousToken`

Exercises `CslibFrontier.Crypto.Protocols.AnonymousToken.ROBridge` via ordinary `module` imports
across:
- End-to-end straight-line ROM bridges for `AnonymousToken.Basic`
  (`extractedForgerOfROM_isQueryBounded`, `unextractedTokenExperiment_succProbability_le_extracted`,
  `unextractedTokenExperiment_succProbability_le`) including a concrete probability-`1` forging
  client (`toyROMTokenForgingAdversary`).
- End-to-end straight-line ROM bridges for `AnonymousToken.Conservation`
  (`extractedAdversaryOfROM_isQueryBounded`,
  `unextractedConservationExperiment_succProbability_le_extracted`,
  `unextractedConservationExperiment_succProbability_le_prod_mk`) exercising `.issue`, `.spend`,
  nullifier replay rejection, and a concrete probability-`1` overspending adversary under a
  colliding commitment (`toyROMConsOverspendAdversary`), all with verified `< 1` `voleithKSBound`
  evaluations.
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.AnonymousTokenROBridge

open Cslib Cslib.Crypto Cslib.Crypto.AnonymousToken Cslib.Crypto.Protocols.VOLE
open Cslib.Probability
open Cslib.OracleComp (IsCostBounded)
open scoped ENNReal NNReal

/-- Projection relation `w 0 = stmt` on 2-bit witnesses. -/
private def toyRel (stmt : Bool) (w : BitString 2) : Bool :=
  decide (w 0 = stmt)

/-- Linear MAC pre-message: prover's bit-0 keys `pCols j 0` per VOLE tree depth `j : Fin d`. -/
private def toyMkPreMsg {d rowLen : ℕ} [NeZero rowLen] (pCols : Fin d → BitString rowLen)
    (_ _ : BitString rowLen) : Fin d → Bool :=
  fun j => pCols j 0

/-- Linear VOLE check: verifies `qCols j 0 ^^ (Δ_j && dCorr 0) = preMsg j ^^ (Δ_j && stmt)` for
every `j : Fin d`. -/
private def toyCheckRel {d rowLen : ℕ} [NeZero rowLen] (stmt : Bool)
    (qCols : Fin d → BitString rowLen) (dCorr : BitString rowLen)
    (preMsg : Fin d → Bool) (delta : Fin (2 ^ d)) : Bool :=
  decide (∀ j : Fin d,
    xor (qCols j 0) ((BitString.equivFin d).symm delta j && dCorr 0) =
      xor (preMsg j) ((BitString.equivFin d).symm delta j && stmt))

private theorem xor_mac_bit_eq (p b u s : Bool) :
    xor (xor p (b && u)) (b && xor s u) = xor p (b && s) := by
  cases p <;> cases b <;> cases u <;> cases s <;> decide

private theorem bit_eq_of_xor_mac_neq {p q b u d0 s : Bool}
    (hneq : xor d0 u ≠ s)
    (heq : xor (xor q (b && u)) (b && d0) = xor p (b && s)) :
    b = xor p q := by
  cases p <;> cases q <;> cases b <;> cases u <;> cases d0 <;> cases s <;> simp_all

private theorem toyCheckRel_complete {d rowLen : ℕ} [NeZero rowLen] (stmt : Bool)
    (w : BitString rowLen) (hw : w 0 = stmt) (pCols : Fin d → BitString rowLen)
    (u : BitString rowLen) (delta : Fin (2 ^ d)) :
    toyCheckRel stmt
      (fun j => pCols j + fun k => (BitString.equivFin d).symm delta j * u k)
      (w + u) (toyMkPreMsg pCols u (w + u)) delta = true := by
  unfold toyCheckRel toyMkPreMsg
  refine decide_eq_true fun j => ?_
  simpa [Pi.add_apply, Bool.add_eq_xor, Bool.mul_eq_and, hw] using
    xor_mac_bit_eq (pCols j 0) ((BitString.equivFin d).symm delta j) (u 0) stmt

private theorem toyCheckRel_sound_error {d rowLen : ℕ} [NeZero rowLen]
    (decWit : BitString rowLen → BitString 2)
    (hdec0 : ∀ x, decWit x 0 = x 0) :
    VOLEITHSoundnessError (d := d) (rowLen := rowLen) decWit id toyRel toyCheckRel
      ((1 : ℝ≥0) / (2 ^ d : ℝ≥0)) := by
  intro stmt rows dCorr preMsg hfalse
  let pCols := (FAEST.convertExpandedRows d rows).columns
  let u := (FAEST.convertExpandedRows d rows).u
  let delta₀ : Fin (2 ^ d) := BitString.equivFin d fun j => xor (preMsg j) (pCols j 0)
  have hneq0 : xor (dCorr 0) (u 0) ≠ stmt := by
    simp only [toyRel, hdec0, Pi.add_apply, Bool.add_eq_xor, decide_eq_false_iff_not] at hfalse
    exact hfalse
  have hsub :
      {delta : Fin (2 ^ d) |
        toyCheckRel stmt
          (FAEST.convertExpandedRows d (FAEST.verifierRows rows delta)).columns
          dCorr preMsg delta = true} ⊆ {delta₀} := by
    intro delta hmem
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff] at hmem ⊢
    simp only [toyCheckRel, decide_eq_true_eq] at hmem
    apply (BitString.equivFin d).symm.injective
    funext j
    have hj := hmem j
    have hcorr := FAEST.convertExpandedRows_correlation rows delta j
    have hj0 : (FAEST.convertExpandedRows d (FAEST.verifierRows rows delta)).columns j 0 =
        xor (pCols j 0) ((BitString.equivFin d).symm delta j && u 0) := by
      have h0 := congrFun hcorr 0
      simpa [pCols, u, Pi.add_apply, Bool.add_eq_xor, Bool.mul_eq_and] using h0
    rw [hj0] at hj
    have hbit := bit_eq_of_xor_mac_neq hneq0 hj
    change (BitString.equivFin d).symm delta j =
      (BitString.equivFin d).symm (BitString.equivFin d fun j => xor (preMsg j) (pCols j 0)) j
    rw [Equiv.symm_apply_apply]
    exact hbit
  calc
    (PMF.uniformOfFintype (Fin (2 ^ d))).toOuterMeasure
        {delta : Fin (2 ^ d) |
          toyCheckRel stmt
            (FAEST.convertExpandedRows d (FAEST.verifierRows rows delta)).columns
            dCorr preMsg delta = true}
      ≤ (PMF.uniformOfFintype (Fin (2 ^ d))).toOuterMeasure {delta₀} :=
          MeasureTheory.OuterMeasure.mono _ hsub
    _ = (((1 : ℝ≥0) / (2 ^ d : ℝ≥0) : ℝ≥0) : ℝ≥0∞) := by
          simp [PMF.uniformOfFintype_apply, Fintype.card_fin]

private theorem voleithKSBound_lt_one_of {d comLen Q_leaf Q_FS k num e : ℕ} {ε_rel : ℝ≥0}
    (hk : Q_leaf * (Q_leaf + 2 ^ d * Q_FS) ≤ 2 ^ k) (hcomp : k + 2 ≤ comLen)
    (h2 : Q_FS * num * 4 < 3 * 2 ^ e) (hε : ε_rel = (num : ℝ≥0) / (2 ^ e : ℝ≥0)) :
    (voleithKSBound d comLen Q_leaf Q_FS ε_rel : ℝ≥0∞) < 1 := by
  rw [ENNReal.coe_lt_one_iff]
  subst hε
  unfold voleithKSBound
  have hc : 2 ≤ comLen := by omega
  have h1 : Q_leaf * (Q_leaf + 2 ^ d * Q_FS) ≤ 2 ^ (comLen - 2) :=
    hk.trans (Nat.pow_le_pow_right (by decide) (by omega))
  have hpow : (2 ^ comLen : ℝ≥0) = 4 * ((2 ^ (comLen - 2) : ℕ) : ℝ≥0) := by
    have hnat : 2 ^ comLen = 4 * 2 ^ (comLen - 2) := by
      rw [show (4 : ℕ) = 2 ^ 2 by decide, ← pow_add, Nat.add_sub_of_le hc]
    have hcast : ((2 ^ comLen : ℕ) : ℝ≥0) = 4 * ((2 ^ (comLen - 2) : ℕ) : ℝ≥0) := by
      exact_mod_cast hnat
    simpa [Nat.cast_pow] using hcast
  have hnum : ((Q_leaf : ℝ≥0) * ((Q_leaf : ℝ≥0) + (2 ^ d : ℝ≥0) * (Q_FS : ℝ≥0))) /
      (2 ^ comLen : ℝ≥0) ≤ 1 / 4 := by
    rw [hpow, div_le_iff₀ (mul_pos (by norm_num) (Nat.cast_pos.mpr (pow_pos (by decide) _)))]
    have hc1 : (Q_leaf : ℝ≥0) * ((Q_leaf : ℝ≥0) + (2 ^ d : ℝ≥0) * (Q_FS : ℝ≥0)) ≤
        ((2 ^ (comLen - 2) : ℕ) : ℝ≥0) := by
      have h1' : ((Q_leaf * (Q_leaf + 2 ^ d * Q_FS) : ℕ) : ℝ≥0) ≤
          ((2 ^ (comLen - 2) : ℕ) : ℝ≥0) := by
        exact_mod_cast h1
      simpa [Nat.cast_mul, Nat.cast_add, Nat.cast_pow] using h1'
    calc
      (Q_leaf : ℝ≥0) * ((Q_leaf : ℝ≥0) + (2 ^ d : ℝ≥0) * (Q_FS : ℝ≥0))
        ≤ ((2 ^ (comLen - 2) : ℕ) : ℝ≥0) := hc1
      _ = (1 / 4 : ℝ≥0) * (4 * ((2 ^ (comLen - 2) : ℕ) : ℝ≥0)) := by ring
  have hfs : (Q_FS : ℝ≥0) * ((num : ℝ≥0) / (2 ^ e : ℝ≥0)) < 3 / 4 := by
    have hden_pos : (0 : ℝ≥0) < (2 ^ e : ℝ≥0) := pow_pos (by norm_num) _
    rw [mul_div_assoc', div_lt_iff₀ hden_pos]
    have hcast : ((Q_FS * num * 4 : ℕ) : ℝ≥0) < ((3 * 2 ^ e : ℕ) : ℝ≥0) := by exact_mod_cast h2
    have hlt4 : (Q_FS : ℝ≥0) * (num : ℝ≥0) * 4 < (3 : ℝ≥0) * (2 ^ e : ℝ≥0) := by
      simpa [Nat.cast_mul, Nat.cast_pow] using hcast
    have h4 : (0 : ℝ≥0) < 4 := by norm_num
    calc
      (Q_FS : ℝ≥0) * (num : ℝ≥0)
        = ((Q_FS : ℝ≥0) * (num : ℝ≥0) * 4) / 4 := by ring
      _ < ((3 : ℝ≥0) * (2 ^ e : ℝ≥0)) / 4 := div_lt_div_of_pos_right hlt4 h4
      _ = 3 / 4 * (2 ^ e : ℝ≥0) := by ring
  calc
    ((Q_leaf : ℝ≥0) * ((Q_leaf : ℝ≥0) + (2 ^ d : ℝ≥0) * (Q_FS : ℝ≥0))) / (2 ^ comLen : ℝ≥0) +
        (Q_FS : ℝ≥0) * ((num : ℝ≥0) / (2 ^ e : ℝ≥0))
      < (1 / 4 : ℝ≥0) + 3 / 4 := add_lt_add_of_le_of_lt hnum hfs
    _ = 1 := by norm_num


/-- Deterministic toy signature scheme certifying `Bool` targets by equality. -/
private def toySig : Signature.Scheme Unit Unit Bool Bool where
  keyGen := pure ((), ())
  sign _ t := pure t
  verify _ t sig := decide (t = sig)

private def tokTarget (_ : Bool) (o : BitString 2) : Bool := o 0

private def tokCheckRel {d : ℕ} (stmt : Bool × Bool) :
    (Fin d → BitString 2) → BitString 2 → (Fin d → Bool) → Fin (2 ^ d) → Bool :=
  toyCheckRel stmt.2

private theorem tokCheckRel_sound_error {d : ℕ} :
    VOLEITHSoundnessError (d := d) (rowLen := 2) (id : BitString 2 → BitString 2)
      id (romTokenRel tokTarget) tokCheckRel ((1 : ℝ≥0) / (2 ^ d : ℝ≥0)) := by
  intro stmt rows dCorr preMsg hfalse
  simp only [romTokenRel, tokTarget] at hfalse
  have hfalse' : toyRel stmt.2 (dCorr + (FAEST.convertExpandedRows d rows).u) = false := hfalse
  exact toyCheckRel_sound_error (d := d) (rowLen := 2) id (fun _ => rfl) stmt.2 rows dCorr preMsg
    hfalse'

/-- Concrete `AnonymousToken.Basic` unextracted ROM adversary making `1` signing query, `8` `H_leaf`
queries, and `1` `H_FS` query. -/
private def toyROMTokenAdversary :
    Unit → ProbOracleComp
      (ROMTokenSpec Bool Bool 3 2 128 2 (Fin (2 ^ 3)) ℕ (Fin 3 → Bool) (Fin (2 ^ 3)) Bool)
      (Token Bool (BitString 2) Bool) := fun _ => do
  let prf ← OracleComp.liftRight (spec₁ := unifSpec)
    (OracleComp.liftRight
      (spec₁ := ROMTokenSignSpec Bool Bool 3 128 2 (Fin (2 ^ 3)) ℕ (Fin 3 → Bool) Bool)
      (voleithProveLeafFS (id : BitString 2 → BitString 2) id id toyMkPreMsg
        0 (1 : ℕ) (fun _ => 0) (false, true) (fun _ => true)))
  let _ ← OracleComp.liftRight (spec₁ := unifSpec)
    (OracleComp.liftLeft
      (spec₂ := VOLEITHROSpec 3 2 128 2 (Bool × Bool) (Fin (2 ^ 3)) ℕ (Fin 3 → Bool)
        (Fin (2 ^ 3)))
      (OracleComp.query (⟨false, true, prf⟩ : ROMTokenRequest Bool Bool 3 128 2 (Fin (2 ^ 3)) ℕ
        (Fin 3 → Bool))))
  return ⟨⟨false, fun _ => true⟩, true⟩

private theorem toyROMTokenAdversary_req_bound (pk : Unit) :
    IsCostBounded (Sum.elim (fun _ => 0) (Sum.elim (fun _ => 1) (fun _ => 0)))
      (toyROMTokenAdversary pk) 1 := by
  unfold toyROMTokenAdversary
  change IsCostBounded _ _ (0 + (1 + 0))
  refine (IsCostBounded.liftRight
    (IsCostBounded.liftRight_of_cost_inr_eq_zero (fun _ => rfl) _)
    (fun _ => le_rfl)).bind fun _ => ?_
  exact (IsCostBounded.liftRight
    (cost := Sum.elim (fun _ => 0) (Sum.elim (fun _ => 1) (fun _ => 0)))
    (IsCostBounded.liftLeft (cost₁ := fun _ => 1) (cost := Sum.elim (fun _ => 1) (fun _ => 0))
      (IsCostBounded.query _) fun _ => le_rfl)
    fun _ => le_rfl).bind fun _ => IsCostBounded.pure _ 0

private theorem toyROMTokenAdversary_leaf_bound (pk : Unit) :
    IsCostBounded (Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0) voleithLeafCost))
      (toyROMTokenAdversary pk) 8 := by
  unfold toyROMTokenAdversary
  change IsCostBounded _ _ (2 ^ 3 + (0 + 0))
  refine (IsCostBounded.liftRight
    (IsCostBounded.liftRight
      (isCostBounded_leaf_voleithProveLeafFS id id id toyMkPreMsg 0 (1 : ℕ) (fun _ => 0)
        (false, true) (fun _ => true))
      fun _ => le_rfl)
    fun _ => le_rfl).bind fun _ => ?_
  exact (IsCostBounded.liftRight
    (IsCostBounded.liftLeft_of_cost_inl_eq_zero (fun _ => rfl) _)
    fun _ => le_rfl).bind fun _ => IsCostBounded.pure _ 0

private theorem toyROMTokenAdversary_fs_bound (pk : Unit) :
    IsCostBounded (Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0) voleithFSCost))
      (toyROMTokenAdversary pk) 1 := by
  unfold toyROMTokenAdversary
  change IsCostBounded _ _ (1 + (0 + 0))
  refine (IsCostBounded.liftRight
    (IsCostBounded.liftRight
      (isCostBounded_fs_voleithProveLeafFS id id id toyMkPreMsg 0 (1 : ℕ) (fun _ => 0)
        (false, true) (fun _ => true))
      fun _ => le_rfl)
    fun _ => le_rfl).bind fun _ => ?_
  exact (IsCostBounded.liftRight
    (IsCostBounded.liftLeft_of_cost_inl_eq_zero (fun _ => rfl) _)
    fun _ => le_rfl).bind fun _ => IsCostBounded.pure _ 0

/-- Straight-line extracted forger preserves the `1`-signing-query bound. -/
example (pk : Unit) :
    (extractedForgerOfROM (d := 3) (sdLen := 2) (comLen := 128) (rowLen := 2)
      id id id tokCheckRel toyROMTokenAdversary pk).IsQueryBounded 1 :=
  extractedForgerOfROM_isQueryBounded id id id tokCheckRel toyROMTokenAdversary
    toyROMTokenAdversary_req_bound pk

/-- Concrete `AnonymousToken.Basic` ROM-to-extracted and end-to-end EUF-CMA + binding +
straight-line extraction reductions with `voleithKSBound < 1`. -/
example :
    (romUnextractedTokenExperiment id id tokCheckRel toySig tokTarget
        toyROMTokenAdversary).succProbability ≤
      (toySig.eufCmaExperiment (targetForger tokTarget
          (extractedForgerOfROM id id id tokCheckRel toyROMTokenAdversary))).succProbability +
        (bindingExperiment toySig tokTarget
          (extractedForgerOfROM id id id tokCheckRel toyROMTokenAdversary)).succProbability +
        voleithKSBound 3 128 (8 + 1 * (2 ^ 3 - 1)) (1 + 1) ((1 : ℝ≥0) / (2 ^ 3 : ℝ≥0)) ∧
    (voleithKSBound 3 128 (8 + 1 * (2 ^ 3 - 1)) (1 + 1) ((1 : ℝ≥0) / (2 ^ 3 : ℝ≥0)) : ℝ≥0∞) <
      1 := by
  refine ⟨unextractedTokenExperiment_succProbability_le id id id toySig tokTarget tokCheckRel
    tokCheckRel_sound_error toyROMTokenAdversary toyROMTokenAdversary_req_bound
    toyROMTokenAdversary_leaf_bound toyROMTokenAdversary_fs_bound, ?_⟩
  exact voleithKSBound_lt_one_of (d := 3) (comLen := 128) (Q_leaf := 8 + 1 * (2 ^ 3 - 1))
    (Q_FS := 1 + 1) (k := 10) (num := 1) (e := 3) (ε_rel := (1 : ℝ≥0) / (2 ^ 3 : ℝ≥0))
    (by decide) (by decide) (by decide) (by simp)

example :
    (romUnextractedTokenExperiment id id tokCheckRel toySig tokTarget
        toyROMTokenAdversary).succProbability ≤
      (extractedExperiment toySig tokTarget
        (extractedForgerOfROM id id id tokCheckRel toyROMTokenAdversary)).succProbability +
        voleithKSBound 3 128 (8 + 1 * (2 ^ 3 - 1)) (1 + 1) ((1 : ℝ≥0) / (2 ^ 3 : ℝ≥0)) :=
  unextractedTokenExperiment_succProbability_le_extracted id id id toySig tokTarget tokCheckRel
    tokCheckRel_sound_error toyROMTokenAdversary toyROMTokenAdversary_req_bound
    toyROMTokenAdversary_leaf_bound toyROMTokenAdversary_fs_bound

/-- Positive-probability (`= 1`) forging adversary on `AnonymousToken.Basic`: obtains a valid
signature on `false` via VOLEitH proof verification on `message = false`, then outputs a valid
forged token on `message = true` exploiting the target collision `tokTarget true 0 = false`. -/
private def toyROMTokenForgingAdversary :
    Unit → ProbOracleComp
      (ROMTokenSpec Bool Bool 3 2 128 2 (Fin (2 ^ 3)) ℕ (Fin 3 → Bool) (Fin (2 ^ 3)) Bool)
      (Token Bool (BitString 2) Bool) := fun _ => do
  let prf ← OracleComp.liftRight (spec₁ := unifSpec)
    (OracleComp.liftRight
      (spec₁ := ROMTokenSignSpec Bool Bool 3 128 2 (Fin (2 ^ 3)) ℕ (Fin 3 → Bool) Bool)
      (voleithProveLeafFS (id : BitString 2 → BitString 2) id id toyMkPreMsg
        0 (1 : ℕ) (fun _ => 0) (false, false) (fun _ => false)))
  let msig ← OracleComp.liftRight (spec₁ := unifSpec)
    (OracleComp.liftLeft
      (spec₂ := VOLEITHROSpec 3 2 128 2 (Bool × Bool) (Fin (2 ^ 3)) ℕ (Fin 3 → Bool)
        (Fin (2 ^ 3)))
      (OracleComp.query (⟨false, false, prf⟩ : ROMTokenRequest Bool Bool 3 128 2 (Fin (2 ^ 3)) ℕ
        (Fin 3 → Bool))))
  return ⟨⟨true, fun _ => false⟩, msig.getD true⟩

private theorem toyROMTokenForgingAdversary_req_bound (pk : Unit) :
    IsCostBounded (Sum.elim (fun _ => 0) (Sum.elim (fun _ => 1) (fun _ => 0)))
      (toyROMTokenForgingAdversary pk) 1 := by
  unfold toyROMTokenForgingAdversary
  change IsCostBounded _ _ (0 + (1 + 0))
  refine (IsCostBounded.liftRight
    (IsCostBounded.liftRight_of_cost_inr_eq_zero (fun _ => rfl) _)
    (fun _ => le_rfl)).bind fun _ => ?_
  exact (IsCostBounded.liftRight
    (cost := Sum.elim (fun _ => 0) (Sum.elim (fun _ => 1) (fun _ => 0)))
    (IsCostBounded.liftLeft (cost₁ := fun _ => 1) (cost := Sum.elim (fun _ => 1) (fun _ => 0))
      (IsCostBounded.query _) fun _ => le_rfl)
    fun _ => le_rfl).bind fun _ => IsCostBounded.pure _ 0

private theorem toyROMTokenForgingAdversary_leaf_bound (pk : Unit) :
    IsCostBounded (Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0) voleithLeafCost))
      (toyROMTokenForgingAdversary pk) 8 := by
  unfold toyROMTokenForgingAdversary
  change IsCostBounded _ _ (2 ^ 3 + (0 + 0))
  refine (IsCostBounded.liftRight
    (IsCostBounded.liftRight
      (isCostBounded_leaf_voleithProveLeafFS id id id toyMkPreMsg 0 (1 : ℕ) (fun _ => 0)
        (false, false) (fun _ => false))
      fun _ => le_rfl)
    fun _ => le_rfl).bind fun _ => ?_
  exact (IsCostBounded.liftRight
    (IsCostBounded.liftLeft_of_cost_inl_eq_zero (fun _ => rfl) _)
    fun _ => le_rfl).bind fun _ => IsCostBounded.pure _ 0

private theorem toyROMTokenForgingAdversary_fs_bound (pk : Unit) :
    IsCostBounded (Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0) voleithFSCost))
      (toyROMTokenForgingAdversary pk) 1 := by
  unfold toyROMTokenForgingAdversary
  change IsCostBounded _ _ (1 + (0 + 0))
  refine (IsCostBounded.liftRight
    (IsCostBounded.liftRight
      (isCostBounded_fs_voleithProveLeafFS id id id toyMkPreMsg 0 (1 : ℕ) (fun _ => 0)
        (false, false) (fun _ => false))
      fun _ => le_rfl)
    fun _ => le_rfl).bind fun _ => ?_
  exact (IsCostBounded.liftRight
    (IsCostBounded.liftLeft_of_cost_inl_eq_zero (fun _ => rfl) _)
    fun _ => le_rfl).bind fun _ => IsCostBounded.pure _ 0

private theorem toyROMTokenForgingAdversary_succ :
    (romUnextractedTokenExperiment id id tokCheckRel toySig tokTarget
      toyROMTokenForgingAdversary).succProbability = 1 := by
  have heval :
      ProbComp.eval (romUnextractedTokenExperiment id id tokCheckRel toySig tokTarget
        toyROMTokenForgingAdversary) = PMF.pure true := by
    simp only [romUnextractedTokenExperiment, runROMUnextractedToken,
      ProbComp.eval_map, ProbComp.eval_bind, ProbComp.eval_pure, PMF.pure_bind,
      ProbOracleComp.eval_runState,
      show ProbComp.eval toySig.keyGen = PMF.pure ((), ()) from by simp [toySig]]
    have hev :
        (fun q st => ProbComp.eval (verifyGatedHandlerProg (d := 3) (sdLen := 2) (comLen := 128)
            (rowLen := 2) (Seed := Fin (2 ^ 3)) (IV := ℕ) (PreMsg := Fin 3 → Bool)
            (Chal := Fin (2 ^ 3)) id id ROMTokenRequest.stmt ROMTokenRequest.proof tokCheckRel
            none (romTokenAcceptReal toySig ((), ())) q st)) =
          verifyGatedHandler (comLen := 128) (Seed := Fin (2 ^ 3)) (IV := ℕ)
            id id ROMTokenRequest.stmt ROMTokenRequest.proof tokCheckRel none
            (fun _ => romTokenAcceptReal toySig ((), ())) :=
      funext fun q => funext fun st =>
        verifyGatedHandlerProg_eval id id ROMTokenRequest.stmt ROMTokenRequest.proof tokCheckRel
          none (romTokenAcceptReal toySig ((), ())) q st
    rw [hev, PMF.map_eq_pure_iff]
    rintro run hmem
    rw [PMF.mem_support_bind_iff] at hmem
    obtain ⟨⟨tok_out, roEnd, msgsEnd⟩, hmem, hmk⟩ := hmem
    rw [PMF.mem_support_pure_iff] at hmk
    subst hmk
    unfold toyROMTokenForgingAdversary at hmem
    rw [ProbOracleComp.runWith_bind, PMF.mem_support_bind_iff] at hmem
    obtain ⟨⟨prf, roSt₁, msgs₁⟩, hprove_mem, hrest⟩ := hmem
    rw [runWith_verifyGatedHandler_liftRight, PMF.mem_support_map_iff] at hprove_mem
    obtain ⟨⟨prf', roSt₁'⟩, hprove', hpair⟩ := hprove_mem
    simp only [Prod.mk.injEq] at hpair
    obtain ⟨rfl, rfl, rfl⟩ := hpair
    obtain ⟨hver, _, _⟩ := voleithProveLeafFS_verify_of_fresh (id : BitString 2 → BitString 2)
      id id toyMkPreMsg tokCheckRel 0 (1 : ℕ) (fun _ => 0) (false, false) (fun _ => false)
      (fun pCols u delta => toyCheckRel_complete false _ rfl pCols u delta)
      ([], []) (by simp) (by simp) hprove'
    rw [ProbOracleComp.runWith_bind, ProbOracleComp.runWith,
      OracleComp.runWith_sumHandler_liftRight, OracleComp.runWith_eq_run_interpret,
      OracleComp.liftLeft_query, OracleComp.run_interpret_query] at hrest
    simp only [verifyGatedHandler, ROMTokenRequest.stmt] at hrest
    rw [hver] at hrest
    simp only [PMF.pure_bind, ↓reduceIte, romTokenAcceptReal, toySig,
      ProbComp.eval_freeMMap, ProbComp.eval_pure, PMF.pure_map,
      ProbOracleComp.runWith_pure] at hrest
    change _ ∈ (PMF.pure _).support at hrest
    rw [PMF.mem_support_pure_iff, Prod.mk.injEq] at hrest
    obtain ⟨rfl, rfl, rfl⟩ := hrest
    dsimp only
    decide
  simp [Experiment.succProbability, Game.succProbability, heval]

/-- Non-vacuous probability-`1` reduction check on `AnonymousToken.Basic`: `1 ≤ eufCma + binding +
voleithKSBound` with `voleithKSBound < 1`. -/
example :
    1 ≤
      (toySig.eufCmaExperiment (targetForger tokTarget
          (extractedForgerOfROM id id id tokCheckRel
            toyROMTokenForgingAdversary))).succProbability +
        (bindingExperiment toySig tokTarget
          (extractedForgerOfROM id id id tokCheckRel toyROMTokenForgingAdversary)).succProbability +
        voleithKSBound 3 128 (8 + 1 * (2 ^ 3 - 1)) (1 + 1) ((1 : ℝ≥0) / (2 ^ 3 : ℝ≥0)) ∧
    (voleithKSBound 3 128 (8 + 1 * (2 ^ 3 - 1)) (1 + 1) ((1 : ℝ≥0) / (2 ^ 3 : ℝ≥0)) : ℝ≥0∞) <
      1 := by
  refine ⟨?_, ?_⟩
  · simpa only [toyROMTokenForgingAdversary_succ] using
      unextractedTokenExperiment_succProbability_le id id id toySig tokTarget tokCheckRel
        tokCheckRel_sound_error toyROMTokenForgingAdversary
        toyROMTokenForgingAdversary_req_bound toyROMTokenForgingAdversary_leaf_bound
        toyROMTokenForgingAdversary_fs_bound
  · exact voleithKSBound_lt_one_of (d := 3) (comLen := 128) (Q_leaf := 8 + 1 * (2 ^ 3 - 1))
      (Q_FS := 1 + 1) (k := 10) (num := 1) (e := 3) (ε_rel := (1 : ℝ≥0) / (2 ^ 3 : ℝ≥0))
      (by decide) (by decide) (by decide) (by simp)

/-- Generic VOLE-MAC check compiler turning any decidable `Rel` into a `1 / 2 ^ d`-sound
check predicate over `FAEST.convertExpandedRows`. -/
private abbrev macPreMsg (d rowLen : ℕ) :=
  (Fin d → BitString rowLen) × BitString rowLen

private def macCheckRel {d rowLen : ℕ} {Stmt Wit : Type}
    (decWit : BitString rowLen → Wit) (Rel : Stmt → Wit → Bool)
    (stmt : Stmt) (qCols : Fin d → BitString rowLen) (dCorr : BitString rowLen)
    (preMsg : macPreMsg d rowLen) (delta : Fin (2 ^ d)) : Bool :=
  Rel stmt (decWit preMsg.2) &&
    decide (∀ (j : Fin d) (k : Fin rowLen),
      xor (qCols j k) ((BitString.equivFin d).symm delta j && dCorr k) =
        xor (preMsg.1 j k) ((BitString.equivFin d).symm delta j && preMsg.2 k))

private theorem macCheckRel_sound_error {d rowLen : ℕ} {Stmt Wit : Type}
    (decWit : BitString rowLen → Wit) (Rel : Stmt → Wit → Bool) :
    VOLEITHSoundnessError (d := d) (rowLen := rowLen) decWit id Rel
      (macCheckRel decWit Rel) ((1 : ℝ≥0) / (2 ^ d : ℝ≥0)) := by
  intro stmt rows dCorr preMsg hfalse
  let pCols := (FAEST.convertExpandedRows d rows).columns
  let u := (FAEST.convertExpandedRows d rows).u
  by_cases hclaim : Rel stmt (decWit preMsg.2) = false
  · have hemp :
        {delta : Fin (2 ^ d) |
          macCheckRel decWit Rel stmt
            (FAEST.convertExpandedRows d (FAEST.verifierRows rows (id delta))).columns
            dCorr preMsg delta = true} = ∅ := by
      ext delta
      simp [macCheckRel, hclaim]
    rw [hemp]
    simp
  · have hclaim_t : Rel stmt (decWit preMsg.2) = true := Bool.eq_true_of_not_eq_false hclaim
    have hvec_ne : dCorr + u ≠ preMsg.2 := by
      intro heq
      rw [heq] at hfalse
      exact absurd hfalse (by simp [hclaim_t])
    have hk : ∃ k : Fin rowLen, xor (dCorr k) (u k) ≠ preMsg.2 k := by
      by_contra hall
      apply hvec_ne
      funext k
      by_contra hnk
      exact hall ⟨k, by simpa [Pi.add_apply, Bool.add_eq_xor] using hnk⟩
    obtain ⟨k₀, hk₀⟩ := hk
    let delta₀ : Fin (2 ^ d) := BitString.equivFin d fun j => xor (preMsg.1 j k₀) (pCols j k₀)
    have hsub :
        {delta : Fin (2 ^ d) |
          macCheckRel decWit Rel stmt
            (FAEST.convertExpandedRows d (FAEST.verifierRows rows (id delta))).columns
            dCorr preMsg delta = true} ⊆ {delta₀} := by
      intro delta hmem
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff] at hmem ⊢
      simp only [macCheckRel, Bool.and_eq_true, decide_eq_true_eq] at hmem
      apply (BitString.equivFin d).symm.injective
      funext j
      have hj := hmem.2 j k₀
      have hcorr := FAEST.convertExpandedRows_correlation rows delta j
      have hjk₀ : (FAEST.convertExpandedRows d (FAEST.verifierRows rows delta)).columns j k₀ =
          xor (pCols j k₀) ((BitString.equivFin d).symm delta j && u k₀) := by
        simpa [pCols, u, Pi.add_apply, Bool.add_eq_xor, Bool.mul_eq_and] using congrFun hcorr k₀
      simp only [id_eq] at hj
      rw [hjk₀] at hj
      have hbit := bit_eq_of_xor_mac_neq hk₀ hj
      change (BitString.equivFin d).symm delta j =
        (BitString.equivFin d).symm (BitString.equivFin d fun j =>
          xor (preMsg.1 j k₀) (pCols j k₀)) j
      rw [Equiv.symm_apply_apply]
      exact hbit
    calc
      (PMF.uniformOfFintype (Fin (2 ^ d))).toOuterMeasure
          {delta : Fin (2 ^ d) |
            macCheckRel decWit Rel stmt
              (FAEST.convertExpandedRows d (FAEST.verifierRows rows (id delta))).columns
              dCorr preMsg delta = true}
        ≤ (PMF.uniformOfFintype (Fin (2 ^ d))).toOuterMeasure {delta₀} :=
            MeasureTheory.OuterMeasure.mono _ hsub
      _ = (((1 : ℝ≥0) / (2 ^ d : ℝ≥0) : ℝ≥0) : ℝ≥0∞) := by
            simp [PMF.uniformOfFintype_apply, Fintype.card_fin]

private theorem xor_add_self {n : ℕ} (w u : BitString n) : w + u + u = w := by
  funext k
  simp only [Pi.add_apply, Bool.add_eq_xor]
  cases w k <;> cases u k <;> decide

private theorem macCheckRel_complete {d rowLen : ℕ} {Stmt Wit : Type}
    (decWit : BitString rowLen → Wit) (Rel : Stmt → Wit → Bool)
    (stmt : Stmt) (w : BitString rowLen) (hw : Rel stmt (decWit w) = true)
    (pCols : Fin d → BitString rowLen) (u : BitString rowLen) (delta : Fin (2 ^ d)) :
    macCheckRel decWit Rel stmt
      (fun j => pCols j + fun k => (BitString.equivFin d).symm delta j * u k)
      (w + u) (pCols, w + u + u) delta = true := by
  simp only [macCheckRel, xor_add_self, hw, Bool.true_and, decide_eq_true_eq]
  intro j k
  simpa [Pi.add_apply, Bool.add_eq_xor, Bool.mul_eq_and] using
    xor_mac_bit_eq (pCols j k) ((BitString.equivFin d).symm delta j) (u k) (w k)

private def consTestComNat (nf ctx : Bool) (amt : ℕ) (_op : Bool) : Bool × Bool × ℕ :=
  (nf, ctx, amt)

private def consTestComScheme :
    Crypto.Commitment.Scheme Unit (Bool × Bool × ℕ) (Bool × Bool × ℕ) Bool where
  keyGen := pure ()
  commit _ := fun ⟨nf, ctx, t⟩ => pure (consTestComNat nf ctx t false, false)
  verify _ := fun ⟨nf, ctx, t⟩ c o => decide (consTestComNat nf ctx t o = c)

private def consTestSig :
    Signature.Scheme Unit Unit ((Bool × Bool × ℕ) × ℕ) ((Bool × Bool × ℕ) × ℕ) where
  keyGen := pure ((), ())
  sign _ m := pure m
  verify _ m sig := decide (m = sig)

/-- Witness decoder supporting both `.issue` (`x 0 = false`) and `.spend` (`x 0 = true`). -/
private def consDualDecWit (x : BitString 2) :
    ROMConservationWitness Bool Bool ((Bool × Bool × ℕ) × ℕ) :=
  if x 0 then
    .spend ⟨5, false, 0, ((false, false, if x 1 then 5 else 0), 0), true, 0, false⟩
  else
    .issue ⟨x 1, false⟩

private def consIssueQ5 : ROMConservationQuery Bool Bool (Bool × Bool × ℕ) :=
  .issue ⟨false, 5, (false, false, 5)⟩

private def consSpendQ5 : ROMConservationQuery Bool Bool (Bool × Bool × ℕ) :=
  .spend ⟨false, false, 5, 0, (true, false, 0)⟩

/-- Direct `.issue`, `.spend`, nullifier-replay rejection, and non-overspending check on
`consDualDecWit` and `romAcceptQuery`. -/
example :
    romConservationRel consTestComNat Prod.mk consTestSig ⟨(), consIssueQ5⟩
        (consDualDecWit fun _ => false) = true ∧
    romConservationRel consTestComNat Prod.mk consTestSig ⟨(), consSpendQ5⟩
        (consDualDecWit fun _ => true) = true ∧
    romAcceptQuery [consIssueQ5] consSpendQ5 = true ∧
    romAcceptQuery [consIssueQ5, consSpendQ5] consSpendQ5 = false ∧
    romIssuedAmount [consIssueQ5, consSpendQ5] false = 5 ∧
    romSpentDebit [consIssueQ5, consSpendQ5] false = 5 := by
  decide

private def consMkPreMsg (pCols : Fin 3 → BitString 2) (u dCorr : BitString 2) :
    macPreMsg 3 2 :=
  (pCols, dCorr + u)

private def consIssueQ1 : ROMConservationQuery Bool Bool (Bool × Bool × ℕ) :=
  .issue ⟨false, 1, (false, false, 1)⟩

private def consIssueStmt1 : ROMConservationStmt Unit Bool Bool (Bool × Bool × ℕ) :=
  ⟨(), consIssueQ1⟩

private noncomputable def toyROMConsAdversary :
    Unit → ProbOracleComp (ROMConservationSpec Bool Bool (Bool × Bool × ℕ) 3 2 128 2 Unit
      (Fin (2 ^ 3)) ℕ (macPreMsg 3 2) (Fin (2 ^ 3)) ((Bool × Bool × ℕ) × ℕ)) Bool := fun _ => do
  let prf ← OracleComp.liftRight (spec₁ := unifSpec)
    (OracleComp.liftRight
      (spec₁ := ROMConservationIssuerSpec Bool Bool (Bool × Bool × ℕ) 3 128 2 (Fin (2 ^ 3)) ℕ
        (macPreMsg 3 2) ((Bool × Bool × ℕ) × ℕ))
      (voleithProveLeafFS (id : BitString 2 → BitString 2) id id consMkPreMsg 0 (1 : ℕ)
        (fun _ => 0) consIssueStmt1 (fun _ => false)))
  let _ ← OracleComp.liftRight (spec₁ := unifSpec)
    (OracleComp.liftLeft
      (spec₂ := VOLEITHROSpec 3 2 128 2
        (ROMConservationStmt Unit Bool Bool (Bool × Bool × ℕ)) (Fin (2 ^ 3)) ℕ (macPreMsg 3 2)
        (Fin (2 ^ 3)))
      (OracleComp.query ⟨consIssueQ1, prf⟩))
  return false

private theorem toyROMConsAdversary_req_bound (pk : Unit) :
    IsCostBounded (Sum.elim (fun _ => 0) (Sum.elim (fun _ => 1) (fun _ => 0)))
      (toyROMConsAdversary pk) 1 := by
  unfold toyROMConsAdversary
  change IsCostBounded _ _ (0 + (1 + 0))
  refine (IsCostBounded.liftRight
    (IsCostBounded.liftRight_of_cost_inr_eq_zero (fun _ => rfl) _)
    (fun _ => le_rfl)).bind fun _ => ?_
  exact (IsCostBounded.liftRight
    (cost := Sum.elim (fun _ => 0) (Sum.elim (fun _ => 1) (fun _ => 0)))
    (IsCostBounded.liftLeft (cost₁ := fun _ => 1) (cost := Sum.elim (fun _ => 1) (fun _ => 0))
      (IsCostBounded.query _) fun _ => le_rfl)
    fun _ => le_rfl).bind fun _ => IsCostBounded.pure _ 0

private theorem toyROMConsAdversary_leaf_bound (pk : Unit) :
    IsCostBounded (Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0) voleithLeafCost))
      (toyROMConsAdversary pk) 8 := by
  unfold toyROMConsAdversary
  change IsCostBounded _ _ (2 ^ 3 + (0 + 0))
  refine IsCostBounded.bind ?_ fun _ => ?_
  · exact IsCostBounded.liftRight
      (cost := Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0) voleithLeafCost))
      (IsCostBounded.liftRight (cost := Sum.elim (fun _ => 0) voleithLeafCost)
        (isCostBounded_leaf_voleithProveLeafFS (id : BitString 2 → BitString 2) id id
          consMkPreMsg 0 (1 : ℕ) (fun _ => 0) consIssueStmt1 (fun _ => false))
        fun _ => le_rfl)
      fun _ => le_rfl
  · exact (IsCostBounded.liftRight
      (IsCostBounded.liftLeft_of_cost_inl_eq_zero (fun _ => rfl) _)
      fun _ => le_rfl).bind fun _ => IsCostBounded.pure _ 0

private theorem toyROMConsAdversary_fs_bound (pk : Unit) :
    IsCostBounded (Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0) voleithFSCost))
      (toyROMConsAdversary pk) 1 := by
  unfold toyROMConsAdversary
  change IsCostBounded _ _ (1 + (0 + 0))
  refine IsCostBounded.bind ?_ fun _ => ?_
  · exact IsCostBounded.liftRight
      (cost := Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0) voleithFSCost))
      (IsCostBounded.liftRight (cost := Sum.elim (fun _ => 0) voleithFSCost)
        (isCostBounded_fs_voleithProveLeafFS (id : BitString 2 → BitString 2) id id
          consMkPreMsg 0 (1 : ℕ) (fun _ => 0) consIssueStmt1 (fun _ => false))
        fun _ => le_rfl)
      fun _ => le_rfl
  · exact (IsCostBounded.liftRight
      (IsCostBounded.liftLeft_of_cost_inl_eq_zero (fun _ => rfl) _)
      fun _ => le_rfl).bind fun _ => IsCostBounded.pure _ 0

/-- Extracted conservation adversary preserves the `1`-query bound. -/
example (pk : Unit) :
    (extractedAdversaryOfROM (d := 3) (sdLen := 2) (comLen := 128) (rowLen := 2)
      id consDualDecWit id
      (macCheckRel consDualDecWit (romConservationRel consTestComNat Prod.mk consTestSig))
      toyROMConsAdversary pk).IsQueryBounded 1 :=
  extractedAdversaryOfROM_isQueryBounded id consDualDecWit id
    (macCheckRel consDualDecWit (romConservationRel consTestComNat Prod.mk consTestSig))
    toyROMConsAdversary toyROMConsAdversary_req_bound pk

/-- Concrete `AnonymousToken.Conservation` ROM-to-extracted and end-to-end EUF-CMA + commitment
binding + straight-line extraction reductions using `consTestComScheme`. -/
example :
    (romUnextractedConservationExperiment id id Prod.mk
        (macCheckRel consDualDecWit (romConservationRel consTestComNat Prod.mk consTestSig))
        consTestSig toyROMConsAdversary).succProbability ≤
      (Conservation.extractedConservationExperiment consTestComNat Prod.mk consTestSig
        (extractedAdversaryOfROM id consDualDecWit id
          (macCheckRel consDualDecWit (romConservationRel consTestComNat Prod.mk consTestSig))
          toyROMConsAdversary)).succProbability +
        voleithKSBound 3 128 (8 + 1 * (2 ^ 3 - 1)) (1 + 1) ((1 : ℝ≥0) / (2 ^ 3 : ℝ≥0)) :=
  unextractedConservationExperiment_succProbability_le_extracted id consDualDecWit id consTestComNat
    Prod.mk consTestSig
    (macCheckRel consDualDecWit (romConservationRel consTestComNat Prod.mk consTestSig))
    (macCheckRel_sound_error consDualDecWit (romConservationRel consTestComNat Prod.mk consTestSig))
    toyROMConsAdversary toyROMConsAdversary_req_bound toyROMConsAdversary_leaf_bound
    toyROMConsAdversary_fs_bound

example :
    (romUnextractedConservationExperiment id id Prod.mk
        (macCheckRel consDualDecWit (romConservationRel consTestComNat Prod.mk consTestSig))
        consTestSig toyROMConsAdversary).succProbability ≤
      (consTestSig.eufCmaExperiment (targetForger (Credit.target consTestComNat Prod.mk)
          (Conservation.noteForger consTestComNat Prod.mk consTestSig
            (extractedAdversaryOfROM id consDualDecWit id
              (macCheckRel consDualDecWit (romConservationRel consTestComNat Prod.mk consTestSig))
              toyROMConsAdversary)))).succProbability +
        (consTestComScheme.bindingExperiment
          (Conservation.commitmentBindingReduction consTestComNat consTestSig
            (extractedAdversaryOfROM id consDualDecWit id
              (macCheckRel consDualDecWit (romConservationRel consTestComNat Prod.mk consTestSig))
              toyROMConsAdversary))).succProbability +
        voleithKSBound 3 128 (8 + 1 * (2 ^ 3 - 1)) (1 + 1) ((1 : ℝ≥0) / (2 ^ 3 : ℝ≥0)) :=
  unextractedConservationExperiment_succProbability_le_prod_mk id consDualDecWit id consTestComNat
    consTestComScheme (fun _ _ _ _ _ _ => rfl) consTestSig
    (macCheckRel consDualDecWit (romConservationRel consTestComNat Prod.mk consTestSig))
    (macCheckRel_sound_error consDualDecWit (romConservationRel consTestComNat Prod.mk consTestSig))
    toyROMConsAdversary toyROMConsAdversary_req_bound toyROMConsAdversary_leaf_bound
    toyROMConsAdversary_fs_bound

/-- Colliding commitment ignoring balance amounts (`(nf, ctx, 0)`), enabling overspending in the
unextracted ROM game when `issue 1` and `spend 5` share `(false, false, 0)`. -/
private def consCollidingCom (nf ctx : Bool) (_amt : ℕ) (_op : Bool) : Bool × Bool × ℕ :=
  (nf, ctx, 0)

private def consCollidingComScheme :
    Crypto.Commitment.Scheme Unit (Bool × Bool × ℕ) (Bool × Bool × ℕ) Bool where
  keyGen := pure ()
  commit _ := fun ⟨nf, ctx, t⟩ => pure (consCollidingCom nf ctx t false, false)
  verify _ := fun ⟨nf, ctx, t⟩ c o => decide (consCollidingCom nf ctx t o = c)

private def consCollidingIssueQ : ROMConservationQuery Bool Bool (Bool × Bool × ℕ) :=
  .issue ⟨false, 1, (false, false, 0)⟩

private def consCollidingSpendQ : ROMConservationQuery Bool Bool (Bool × Bool × ℕ) :=
  .spend ⟨false, false, 5, 0, (true, false, 0)⟩

private def consCollidingIssueStmt : ROMConservationStmt Unit Bool Bool (Bool × Bool × ℕ) :=
  ⟨(), consCollidingIssueQ⟩

private def consCollidingSpendStmt : ROMConservationStmt Unit Bool Bool (Bool × Bool × ℕ) :=
  ⟨(), consCollidingSpendQ⟩

/-- Positive-probability (`= 1`) unextracted ROM conservation adversary: issues `amount = 1` at
`iv = 1`, verifies the issued certificate `((false, false, 0), 0)`, and spends `debit = 5` at
`iv = 2` against `consCollidingCom` (`1 + 0 < 5`). -/
private noncomputable def toyROMConsOverspendAdversary :
    Unit → ProbOracleComp (ROMConservationSpec Bool Bool (Bool × Bool × ℕ) 3 2 128 2 Unit
      (Fin (2 ^ 3)) ℕ (macPreMsg 3 2) (Fin (2 ^ 3)) ((Bool × Bool × ℕ) × ℕ)) Bool := fun _ => do
  let prf₁ ← OracleComp.liftRight (spec₁ := unifSpec)
    (OracleComp.liftRight
      (spec₁ := ROMConservationIssuerSpec Bool Bool (Bool × Bool × ℕ) 3 128 2 (Fin (2 ^ 3)) ℕ
        (macPreMsg 3 2) ((Bool × Bool × ℕ) × ℕ))
      (voleithProveLeafFS (id : BitString 2 → BitString 2) id id consMkPreMsg 0 (1 : ℕ)
        (fun _ => 0) consCollidingIssueStmt (fun _ => false)))
  let msig₁ ← OracleComp.liftRight (spec₁ := unifSpec)
    (OracleComp.liftLeft
      (spec₂ := VOLEITHROSpec 3 2 128 2
        (ROMConservationStmt Unit Bool Bool (Bool × Bool × ℕ)) (Fin (2 ^ 3)) ℕ (macPreMsg 3 2)
        (Fin (2 ^ 3)))
      (OracleComp.query ⟨consCollidingIssueQ, prf₁⟩))
  if msig₁ == some ((false, false, 0), 0) then
    let prf₂ ← OracleComp.liftRight (spec₁ := unifSpec)
      (OracleComp.liftRight
        (spec₁ := ROMConservationIssuerSpec Bool Bool (Bool × Bool × ℕ) 3 128 2 (Fin (2 ^ 3)) ℕ
          (macPreMsg 3 2) ((Bool × Bool × ℕ) × ℕ))
        (voleithProveLeafFS (id : BitString 2 → BitString 2) id id consMkPreMsg 0 (2 : ℕ)
          (fun _ => 0) consCollidingSpendStmt (fun j => decide (j = 0))))
    let _ ← OracleComp.liftRight (spec₁ := unifSpec)
      (OracleComp.liftLeft
        (spec₂ := VOLEITHROSpec 3 2 128 2
          (ROMConservationStmt Unit Bool Bool (Bool × Bool × ℕ)) (Fin (2 ^ 3)) ℕ (macPreMsg 3 2)
          (Fin (2 ^ 3)))
        (OracleComp.query ⟨consCollidingSpendQ, prf₂⟩))
    return false
  else
    return false

private theorem toyROMConsOverspendAdversary_req_bound (pk : Unit) :
    IsCostBounded (Sum.elim (fun _ => 0) (Sum.elim (fun _ => 1) (fun _ => 0)))
      (toyROMConsOverspendAdversary pk) 2 := by
  unfold toyROMConsOverspendAdversary
  change IsCostBounded _ _ (0 + (1 + 1))
  refine (IsCostBounded.liftRight
    (IsCostBounded.liftRight_of_cost_inr_eq_zero (fun _ => rfl) _)
    (fun _ => le_rfl)).bind fun _ => ?_
  refine (IsCostBounded.liftRight
    (cost := Sum.elim (fun _ => 0) (Sum.elim (fun _ => 1) (fun _ => 0)))
    (IsCostBounded.liftLeft (cost₁ := fun _ => 1) (cost := Sum.elim (fun _ => 1) (fun _ => 0))
      (IsCostBounded.query _) fun _ => le_rfl)
    fun _ => le_rfl).bind fun msig₁ => ?_
  by_cases h : msig₁ == some ((false, false, 0), 0)
  · simp only [h, ↓reduceIte]
    change IsCostBounded _ _ (0 + (1 + 0))
    refine (IsCostBounded.liftRight
      (IsCostBounded.liftRight_of_cost_inr_eq_zero (fun _ => rfl) _)
      (fun _ => le_rfl)).bind fun _ => ?_
    exact (IsCostBounded.liftRight
      (cost := Sum.elim (fun _ => 0) (Sum.elim (fun _ => 1) (fun _ => 0)))
      (IsCostBounded.liftLeft (cost₁ := fun _ => 1) (cost := Sum.elim (fun _ => 1) (fun _ => 0))
        (IsCostBounded.query _) fun _ => le_rfl)
      fun _ => le_rfl).bind fun _ => IsCostBounded.pure _ 0
  · simp only [h, Bool.false_eq_true, ↓reduceIte]
    exact OracleComp.IsCostBounded.mono (IsCostBounded.pure _ 0) (Nat.zero_le 1)

private theorem toyROMConsOverspendAdversary_leaf_bound (pk : Unit) :
    IsCostBounded (Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0) voleithLeafCost))
      (toyROMConsOverspendAdversary pk) 16 := by
  unfold toyROMConsOverspendAdversary
  change IsCostBounded _ _ (2 ^ 3 + (0 + 8))
  refine IsCostBounded.bind ?_ fun _ => ?_
  · exact IsCostBounded.liftRight
      (cost := Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0) voleithLeafCost))
      (IsCostBounded.liftRight (cost := Sum.elim (fun _ => 0) voleithLeafCost)
        (isCostBounded_leaf_voleithProveLeafFS (id : BitString 2 → BitString 2) id id
          consMkPreMsg 0 (1 : ℕ) (fun _ => 0) consCollidingIssueStmt (fun _ => false))
        fun _ => le_rfl)
      fun _ => le_rfl
  · refine (IsCostBounded.liftRight
      (IsCostBounded.liftLeft_of_cost_inl_eq_zero (fun _ => rfl) _)
      fun _ => le_rfl).bind fun msig₁ => ?_
    by_cases h : msig₁ == some ((false, false, 0), 0)
    · simp only [h, ↓reduceIte]
      change IsCostBounded _ _ (2 ^ 3 + (0 + 0))
      refine IsCostBounded.bind ?_ fun _ => ?_
      · exact IsCostBounded.liftRight
          (cost := Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0) voleithLeafCost))
          (IsCostBounded.liftRight (cost := Sum.elim (fun _ => 0) voleithLeafCost)
            (isCostBounded_leaf_voleithProveLeafFS (id : BitString 2 → BitString 2) id id
              consMkPreMsg 0 (2 : ℕ) (fun _ => 0) consCollidingSpendStmt
              (fun j => decide (j = 0)))
            fun _ => le_rfl)
          fun _ => le_rfl
      · exact (IsCostBounded.liftRight
          (IsCostBounded.liftLeft_of_cost_inl_eq_zero (fun _ => rfl) _)
          fun _ => le_rfl).bind fun _ => IsCostBounded.pure _ 0
    · simp only [h, Bool.false_eq_true, ↓reduceIte]
      exact OracleComp.IsCostBounded.mono (IsCostBounded.pure _ 0) (Nat.zero_le 8)

private theorem toyROMConsOverspendAdversary_fs_bound (pk : Unit) :
    IsCostBounded (Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0) voleithFSCost))
      (toyROMConsOverspendAdversary pk) 2 := by
  unfold toyROMConsOverspendAdversary
  change IsCostBounded _ _ (1 + (0 + 1))
  refine IsCostBounded.bind ?_ fun _ => ?_
  · exact IsCostBounded.liftRight
      (cost := Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0) voleithFSCost))
      (IsCostBounded.liftRight (cost := Sum.elim (fun _ => 0) voleithFSCost)
        (isCostBounded_fs_voleithProveLeafFS (id : BitString 2 → BitString 2) id id
          consMkPreMsg 0 (1 : ℕ) (fun _ => 0) consCollidingIssueStmt (fun _ => false))
        fun _ => le_rfl)
      fun _ => le_rfl
  · refine (IsCostBounded.liftRight
      (IsCostBounded.liftLeft_of_cost_inl_eq_zero (fun _ => rfl) _)
      fun _ => le_rfl).bind fun msig₁ => ?_
    by_cases h : msig₁ == some ((false, false, 0), 0)
    · simp only [h, ↓reduceIte]
      change IsCostBounded _ _ (1 + (0 + 0))
      refine IsCostBounded.bind ?_ fun _ => ?_
      · exact IsCostBounded.liftRight
          (cost := Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0) voleithFSCost))
          (IsCostBounded.liftRight (cost := Sum.elim (fun _ => 0) voleithFSCost)
            (isCostBounded_fs_voleithProveLeafFS (id : BitString 2 → BitString 2) id id
              consMkPreMsg 0 (2 : ℕ) (fun _ => 0) consCollidingSpendStmt
              (fun j => decide (j = 0)))
            fun _ => le_rfl)
          fun _ => le_rfl
      · exact (IsCostBounded.liftRight
          (IsCostBounded.liftLeft_of_cost_inl_eq_zero (fun _ => rfl) _)
          fun _ => le_rfl).bind fun _ => IsCostBounded.pure _ 0
    · simp only [h, Bool.false_eq_true, ↓reduceIte]
      exact OracleComp.IsCostBounded.mono (IsCostBounded.pure _ 0) (Nat.zero_le 1)

private theorem toyROMConsOverspendAdversary_succ :
    (romUnextractedConservationExperiment id id Prod.mk
      (macCheckRel consDualDecWit (romConservationRel consCollidingCom Prod.mk consTestSig))
      consTestSig toyROMConsOverspendAdversary).succProbability = 1 := by
  have heval :
      ProbComp.eval (romUnextractedConservationExperiment id id Prod.mk
        (macCheckRel consDualDecWit (romConservationRel consCollidingCom Prod.mk consTestSig))
        consTestSig toyROMConsOverspendAdversary) = PMF.pure true := by
    simp only [romUnextractedConservationExperiment, runROMUnextractedConservation,
      ProbComp.eval_map, ProbComp.eval_bind, ProbComp.eval_pure, PMF.pure_bind,
      ProbOracleComp.eval_runState,
      show ProbComp.eval consTestSig.keyGen = PMF.pure ((), ()) from by simp [consTestSig]]
    have hev :
        (fun q st => ProbComp.eval (verifyGatedHandlerProg (d := 3) (sdLen := 2) (comLen := 128)
            (rowLen := 2) (Seed := Fin (2 ^ 3)) (IV := ℕ) (PreMsg := macPreMsg 3 2)
            (Chal := Fin (2 ^ 3)) id id (fun req => ⟨(), req.query⟩) ROMConservationRequest.proof
            (macCheckRel consDualDecWit (romConservationRel consCollidingCom Prod.mk consTestSig))
            none (romConsAcceptReal Prod.mk consTestSig ((), ())) q st)) =
          verifyGatedHandler (comLen := 128) (Seed := Fin (2 ^ 3)) (IV := ℕ)
            id id (fun req => ⟨(), req.query⟩) ROMConservationRequest.proof
            (macCheckRel consDualDecWit (romConservationRel consCollidingCom Prod.mk consTestSig))
            none (fun _ => romConsAcceptReal Prod.mk consTestSig ((), ())) :=
      funext fun q => funext fun st =>
        verifyGatedHandlerProg_eval id id (fun req => ⟨(), req.query⟩) ROMConservationRequest.proof
          (macCheckRel consDualDecWit (romConservationRel consCollidingCom Prod.mk consTestSig))
          none (romConsAcceptReal Prod.mk consTestSig ((), ())) q st
    rw [hev, PMF.map_eq_pure_iff]
    rintro run hmem
    rw [PMF.mem_support_bind_iff] at hmem
    obtain ⟨⟨ctx_out, roEnd, accEnd⟩, hmem, hmk⟩ := hmem
    rw [PMF.mem_support_pure_iff] at hmk
    subst hmk
    unfold toyROMConsOverspendAdversary at hmem
    rw [ProbOracleComp.runWith_bind, PMF.mem_support_bind_iff] at hmem
    obtain ⟨⟨prf₁, roSt₁, acc₁⟩, hprove₁_mem, hrest₁⟩ := hmem
    rw [runWith_verifyGatedHandler_liftRight, PMF.mem_support_map_iff] at hprove₁_mem
    obtain ⟨⟨prf₁', roSt₁'⟩, hprove₁', hpair₁⟩ := hprove₁_mem
    simp only [Prod.mk.injEq] at hpair₁
    obtain ⟨rfl, rfl, rfl⟩ := hpair₁
    obtain ⟨hver₁, hiv₁_leaf, hiv₁_fs⟩ := voleithProveLeafFS_verify_of_fresh
      (id : BitString 2 → BitString 2) id id consMkPreMsg
      (macCheckRel consDualDecWit (romConservationRel consCollidingCom Prod.mk consTestSig))
      0 (1 : ℕ) (fun _ => 0) ⟨(), consCollidingIssueQ⟩ (fun _ => false)
      (fun pCols u delta => by
        simpa [consMkPreMsg, id_eq] using
          macCheckRel_complete consDualDecWit
            (romConservationRel consCollidingCom Prod.mk consTestSig)
            ⟨(), consCollidingIssueQ⟩ (fun _ => false) (by decide) pCols u delta)
      ([], []) (by simp) (by simp) hprove₁'
    rw [ProbOracleComp.runWith_bind, ProbOracleComp.runWith,
      OracleComp.runWith_sumHandler_liftRight, OracleComp.runWith_eq_run_interpret,
      OracleComp.liftLeft_query, OracleComp.run_interpret_query] at hrest₁
    simp only [verifyGatedHandler] at hrest₁
    rw [hver₁] at hrest₁
    simp only [PMF.pure_bind, ↓reduceIte, romConsAcceptReal, romAcceptQuery, consTestSig,
      ROMConservationQuery.signedMessage, consCollidingIssueQ, ProbComp.eval_freeMMap,
      ProbComp.eval_pure, PMF.pure_map, List.nil_append] at hrest₁
    rw [show (some ((false, false, 0), 0) == some ((false, false, 0), 0)) = true from by decide]
      at hrest₁
    simp only [↓reduceIte] at hrest₁
    rw [ProbOracleComp.runWith_bind, PMF.mem_support_bind_iff] at hrest₁
    obtain ⟨⟨prf₂, roSt₂, acc₂⟩, hprove₂_mem, hrest₂⟩ := hrest₁
    rw [runWith_verifyGatedHandler_liftRight, PMF.mem_support_map_iff] at hprove₂_mem
    obtain ⟨⟨prf₂', roSt₂'⟩, hprove₂', hpair₂⟩ := hprove₂_mem
    simp only [Prod.mk.injEq] at hpair₂
    obtain ⟨rfl, rfl, rfl⟩ := hpair₂
    have hiv₂_leaf : ∀ e ∈ roSt₁'.1, e.1.iv ≠ (2 : ℕ) := fun e he => by
      rcases hiv₁_leaf e he with h | h <;> simp_all
    have hiv₂_fs : ∀ e ∈ roSt₁'.2, e.1.iv ≠ (2 : ℕ) := fun e he => by
      rcases hiv₁_fs e he with h | h <;> simp_all
    obtain ⟨hver₂, _, _⟩ := voleithProveLeafFS_verify_of_fresh
      (id : BitString 2 → BitString 2) id id consMkPreMsg
      (macCheckRel consDualDecWit (romConservationRel consCollidingCom Prod.mk consTestSig))
      0 (2 : ℕ) (fun _ => 0) ⟨(), consCollidingSpendQ⟩ (fun j => decide (j = 0))
      (fun pCols u delta => by
        simpa [consMkPreMsg, id_eq] using
          macCheckRel_complete consDualDecWit
            (romConservationRel consCollidingCom Prod.mk consTestSig)
            ⟨(), consCollidingSpendQ⟩ (fun j => decide (j = 0)) (by decide) pCols u delta)
      roSt₁' hiv₂_leaf hiv₂_fs hprove₂'
    rw [ProbOracleComp.runWith_bind, ProbOracleComp.runWith,
      OracleComp.runWith_sumHandler_liftRight, OracleComp.runWith_eq_run_interpret,
      OracleComp.liftLeft_query, OracleComp.run_interpret_query] at hrest₂
    simp only [verifyGatedHandler] at hrest₂
    simp only [consTestSig] at hver₂
    rw [hver₂] at hrest₂
    have hacc2 : romAcceptQuery [consCollidingIssueQ] consCollidingSpendQ = true := by decide
    simp only [consCollidingIssueQ] at hacc2
    simp only [PMF.pure_bind, ↓reduceIte, romConsAcceptReal, hacc2,
      ProbComp.eval_freeMMap, ProbComp.eval_pure, PMF.pure_map,
      ProbOracleComp.runWith_pure] at hrest₂
    change _ ∈ (PMF.pure _).support at hrest₂
    rw [PMF.mem_support_pure_iff, Prod.mk.injEq] at hrest₂
    obtain ⟨rfl, rfl, rfl⟩ := hrest₂
    dsimp only
    decide
  simp [Experiment.succProbability, Game.succProbability, heval]

/-- Non-vacuous probability-`1` overspending bound on `AnonymousToken.Conservation` under the
colliding commitment `consCollidingCom`: `1 ≤ eufCma + binding + voleithKSBound` with
`voleithKSBound < 1`. -/
example :
    1 ≤
      (consTestSig.eufCmaExperiment (targetForger (Credit.target consCollidingCom Prod.mk)
          (Conservation.noteForger consCollidingCom Prod.mk consTestSig
            (extractedAdversaryOfROM id consDualDecWit id
              (macCheckRel consDualDecWit
                (romConservationRel consCollidingCom Prod.mk consTestSig))
              toyROMConsOverspendAdversary)))).succProbability +
        (consCollidingComScheme.bindingExperiment
          (Conservation.commitmentBindingReduction consCollidingCom consTestSig
            (extractedAdversaryOfROM id consDualDecWit id
              (macCheckRel consDualDecWit
                (romConservationRel consCollidingCom Prod.mk consTestSig))
              toyROMConsOverspendAdversary))).succProbability +
        voleithKSBound 3 128 (16 + 2 * (2 ^ 3 - 1)) (2 + 2) ((1 : ℝ≥0) / (2 ^ 3 : ℝ≥0)) ∧
    (voleithKSBound 3 128 (16 + 2 * (2 ^ 3 - 1)) (2 + 2) ((1 : ℝ≥0) / (2 ^ 3 : ℝ≥0)) :
        ℝ≥0∞) < 1 := by
  refine ⟨?_, ?_⟩
  · simpa only [toyROMConsOverspendAdversary_succ] using
      unextractedConservationExperiment_succProbability_le_prod_mk id consDualDecWit id
        consCollidingCom consCollidingComScheme (fun _ _ _ _ _ _ => rfl) consTestSig
        (macCheckRel consDualDecWit (romConservationRel consCollidingCom Prod.mk consTestSig))
        (macCheckRel_sound_error consDualDecWit
          (romConservationRel consCollidingCom Prod.mk consTestSig))
        toyROMConsOverspendAdversary toyROMConsOverspendAdversary_req_bound
        toyROMConsOverspendAdversary_leaf_bound toyROMConsOverspendAdversary_fs_bound
  · exact voleithKSBound_lt_one_of (d := 3) (comLen := 128) (Q_leaf := 16 + 2 * (2 ^ 3 - 1))
      (Q_FS := 2 + 2) (k := 12) (num := 1) (e := 3) (ε_rel := (1 : ℝ≥0) / (2 ^ 3 : ℝ≥0))
      (by decide) (by decide) (by decide) (by simp)


end CslibFrontierTests.Crypto.AnonymousTokenROBridge
