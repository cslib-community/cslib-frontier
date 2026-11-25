/-
Copyright (c) 2026 Samuel Schlesinger, Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Karn Seth
-/

module

import CslibFrontier.Crypto.Protocols.FAEST.Conversion
import CslibFrontier.Crypto.Protocols.VOLE.ROExtractor
import CslibFrontier.Languages.Probabilistic.QueryCount.Sum
import CslibFrontier.Probability.PMF.Support
import Mathlib.Tactic.NormNum

/-!
# Clients for straight-line VOLEitH ROM extraction

Exercises `CslibFrontier.Crypto.Protocols.VOLE.ROExtractor` via an ordinary `module` import across
honest completeness (`voleithHonestGame_eq_pure_true`), verifier RO query bounds
(`isCostBounded_leaf_voleithVerifyROM`, `isCostBounded_fs_voleithVerifyROM`), concrete single-proof
and adaptive multi-verify knowledge soundness (`voleithKnowledgeSoundness_bound`,
`voleithMultiVerifyROM_sound_bound`) on a degree-1 linear VOLE check with `ε_rel = 1 / 2 ^ 3`, and
a numeric sanity check on `voleithKSBound` at `d = 11`, `comLen = 256`.
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.VOLEROExtractor

open Cslib Cslib.Crypto Cslib.Crypto.Protocols.VOLE
open Cslib.Probability
open Cslib.OracleComp (IsCostBounded)
open scoped ENNReal NNReal

/-! ## 1. Toy linear `leaf_hash::shake` VOLE check, completeness, and concrete soundness -/

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

/-- Honest completeness at `d = 3`, `comLen = 128`, `rowLen = 2`. -/
example :
    ((ProbOracleComp.runWith
      (voleithMemoize (d := 3) (sdLen := 2) (comLen := 128) (rowLen := 2)
        (Stmt := Bool) (Seed := Fin (2 ^ 3)) (IV := ℕ) (PreMsg := Fin 3 → Bool)
        (Chal := Fin (2 ^ 3)))
      (voleithHonestGame (id : BitString 2 → BitString 2) (id : BitString 2 → BitString 2) id
        toyMkPreMsg toyCheckRel 0 7 (fun _ => 0) true (fun _ => true))
      ([], [])).map Prod.fst) = PMF.pure true :=
  voleithHonestGame_eq_pure_true id id id toyMkPreMsg toyCheckRel 0 7 (fun _ => 0) true
    (fun _ => true) fun pCols u delta =>
      toyCheckRel_complete true (fun _ => true) rfl pCols u delta

/-- Verifier RO query budgets: `2 ^ 3 - 1 = 7` leaf queries and `1` FS query. -/
example (stmt : Bool) (prf : VOLEITHProof 3 128 2 (Fin (2 ^ 3)) ℕ (Fin 3 → Bool)) :
    IsCostBounded (Sum.elim (fun _ => 0) voleithLeafCost)
      (voleithVerifyROM (d := 3) (sdLen := 2) (Chal := Fin (2 ^ 3))
        id id toyCheckRel stmt prf) 7 ∧
    IsCostBounded (Sum.elim (fun _ => 0) voleithFSCost)
      (voleithVerifyROM (d := 3) (sdLen := 2) (Chal := Fin (2 ^ 3))
        id id toyCheckRel stmt prf) 1 := by
  refine ⟨?_, ?_⟩
  · simpa using isCostBounded_leaf_voleithVerifyROM (d := 3) (sdLen := 2) (Chal := Fin (2 ^ 3))
      id id toyCheckRel stmt prf
  · exact isCostBounded_fs_voleithVerifyROM (d := 3) (sdLen := 2) (Chal := Fin (2 ^ 3))
      id id toyCheckRel stmt prf

/-- Concrete single-proof knowledge soundness for `toyCheckRel` (`d = 3`, `comLen = 128`,
`ε_rel = 1 / 8`, prover budgets `Q_leaf = 8`, `Q_FS = 1`): `voleithKSBound < 1`. -/
example
    (P : ProbOracleComp (VOLEITHROSpec 3 2 128 2 Bool (Fin (2 ^ 3)) ℕ (Fin 3 → Bool)
        (Fin (2 ^ 3)))
      (Bool × VOLEITHProof 3 128 2 (Fin (2 ^ 3)) ℕ (Fin 3 → Bool)))
    (hleaf : IsCostBounded (Sum.elim (fun _ => 0) voleithLeafCost) P 8)
    (hfs : IsCostBounded (Sum.elim (fun _ => 0) voleithFSCost) P 1) :
    (voleithKSFailurePMF id (id : BitString 2 → BitString 2) id toyRel toyCheckRel P) true <
      1 := by
  refine (voleithKnowledgeSoundness_bound (d := 3) (sdLen := 2) (comLen := 128) (rowLen := 2)
    id id id toyRel toyCheckRel (toyCheckRel_sound_error id fun _ => rfl) P hleaf hfs).trans_lt ?_
  exact voleithKSBound_lt_one_of (d := 3) (comLen := 128) (Q_leaf := 8 + (2 ^ 3 - 1))
    (Q_FS := 1 + 1) (k := 10) (num := 1) (e := 3) (ε_rel := (1 : ℝ≥0) / (2 ^ 3 : ℝ≥0))
    (by decide) (by decide) (by decide) (by simp)

/-- Concrete adaptive multi-verify knowledge soundness (`m = 2`, `Q_leaf = 8`, `Q_FS = 1`):
`voleithKSBound < 1`. -/
example
    (A : ProbOracleComp
      (VOLEITHMultiVerifySpec 3 2 128 2 Bool (Fin (2 ^ 3)) ℕ (Fin 3 → Bool) (Fin (2 ^ 3))) Unit)
    (hm : IsCostBounded (Sum.elim (fun _ => 0) (Sum.elim (fun _ => 1) (fun _ => 0))) A 2)
    (hleaf : IsCostBounded
      (Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0) voleithLeafCost)) A 8)
    (hfs : IsCostBounded
      (Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0) voleithFSCost)) A 1) :
    ((ProbOracleComp.runWith (voleithMultiVerifyHandler (d := 3) (sdLen := 2) (comLen := 128)
        (rowLen := 2) id id id toyRel toyCheckRel) A (([], []), false)).map
      fun (_, _, bad) => bad) true < 1 := by
  refine (voleithMultiVerifyROM_sound_bound (d := 3) (sdLen := 2) (comLen := 128) (rowLen := 2)
    id id id toyRel toyCheckRel (toyCheckRel_sound_error id fun _ => rfl)
    A hm hleaf hfs).trans_lt ?_
  exact voleithKSBound_lt_one_of (d := 3) (comLen := 128) (Q_leaf := 8 + 2 * (2 ^ 3 - 1))
    (Q_FS := 1 + 2) (k := 12) (num := 1) (e := 3) (ε_rel := (1 : ℝ≥0) / (2 ^ 3 : ℝ≥0))
    (by decide) (by decide) (by decide) (by simp)

/-- Numeric sanity check on `voleithKSBound` at `d = 11`, `comLen = 256` (illustrative arithmetic
evaluation, not an ACT parameter tuple or concrete `VOLEITHSoundnessError` instance). -/
example :
    (voleithKSBound 11 256 (2 ^ 12 + 1 * (2 ^ 11 - 1)) (2 ^ 6 + 1)
      ((9 : ℝ≥0) / (2 ^ 128 : ℝ≥0)) : ℝ≥0∞) < 1 := by
  have hk : (2 ^ 12 + 1 * (2 ^ 11 - 1)) * ((2 ^ 12 + 1 * (2 ^ 11 - 1)) + 2 ^ 11 * (2 ^ 6 + 1)) ≤
      2 ^ 30 := by decide
  have h2 : (2 ^ 6 + 1) * 9 * 4 < 3 * 2 ^ 128 :=
    (by decide : (2 ^ 6 + 1) * 9 * 4 < 3 * 2 ^ 11).trans_le
      (Nat.mul_le_mul_left 3 (Nat.pow_le_pow_right (by decide) (by decide : 11 ≤ 128)))
  exact voleithKSBound_lt_one_of (d := 11) (comLen := 256) (Q_leaf := 2 ^ 12 + 1 * (2 ^ 11 - 1))
    (Q_FS := 2 ^ 6 + 1) (k := 30) (num := 9) (e := 128)
    (ε_rel := (9 : ℝ≥0) / (2 ^ 128 : ℝ≥0)) hk (by decide) h2 (by simp only [Nat.cast_ofNat])


end CslibFrontierTests.Crypto.VOLEROExtractor
