/-
Copyright (c) 2026 Samuel Schlesinger, Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Karn Seth
-/

import CslibFrontier.Crypto.Protocols.AnonymousToken.Basic
import CslibFrontier.Crypto.Protocols.AnonymousToken.Conservation
import CslibFrontier.Crypto.Protocols.FAEST.Conversion
import CslibFrontier.Crypto.Protocols.VOLE.ROExtractor
import Mathlib.Tactic.NormNum

/-!
# Clients and separation tests for straight-line VOLEitH ROM extraction

Exercises `CslibFrontier.Crypto.Protocols.VOLE.ROExtractor` across:
- Honest completeness (`voleithHonestGame_eq_pure_true`), FAEST VOLE correlation extraction
  (`extractRowsFromTrace_conversionCorrelation_valid`), verifier RO query bounds
  (`isCostBounded_leaf_voleithVerifyROM`, `isCostBounded_fs_voleithVerifyROM`), and concrete
  single-proof / adaptive multi-verify knowledge soundness (`voleithKnowledgeSoundness_bound`,
  `voleithMultiVerifyROM_sound_bound`) on a degree-1 linear VOLE check with `ε_rel = 1 / 2 ^ 3`.
- End-to-end straight-line ROM bridges for `AnonymousToken.Basic`
  (`extractedForgerOfROM_isQueryBounded`, `unextractedTokenExperiment_succProbability_le_extracted`,
  `unextractedTokenExperiment_succProbability_le`) and `AnonymousToken.Conservation`
  (`extractedAdversaryOfROM_isQueryBounded`,
  `unextractedConservationExperiment_succProbability_le_extracted`,
  `unextractedConservationExperiment_succProbability_le_prod_mk`) with verified `< 1` concrete
  `ksBound` evaluations and ACT-scale `(d = 11, comLen = 256)` numeric bounds.
- Negative / separation tests modeling PRG-based leaf commitments (`leaf_hash::aes_ctr`,
  BaumEtAl2026FAESTer): `prgLeafProver_leafCost_zero`, `prgLeafGame_leafTrace_eq_nil`,
  `prgLeafGame_eq_pure_true`, `toOuterMeasure_prgLeaf_queryLog_fails_eq_one`,
  `exists_witness_prgLeaf_queryLog_fails_eq_one` on the sound `d = 3` VOLE relation, and
  `exists_valid_prgLeaf_extract_fails_all` on an explicit colliding-commitment PRG separating
  `false ≠ true` against **every** unbounded extractor `ext : LeafTrace → Proof → Option Bool`.
-/

namespace CslibFrontierTests.Crypto.VOLEROExtractor

open Cslib Cslib.Crypto Cslib.Crypto.AnonymousToken Cslib.Crypto.Protocols.VOLE
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

private theorem ksBound_lt_one_of {d comLen Q_leaf Q_FS k num e : ℕ} {ε_rel : ℝ≥0}
    (hk : Q_leaf * (Q_leaf + 2 ^ d * Q_FS) ≤ 2 ^ k) (hcomp : k + 2 ≤ comLen)
    (h2 : Q_FS * num * 4 < 3 * 2 ^ e) (hε : ε_rel = (num : ℝ≥0) / (2 ^ e : ℝ≥0)) :
    (ksBound d comLen Q_leaf Q_FS ε_rel : ℝ≥0∞) < 1 := by
  rw [ENNReal.coe_lt_one_iff]
  subst hε
  unfold ksBound
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

/-- Extracted trace rows yield valid `FAEST.conversionCorrelation` columns. -/
example (tr : LeafTrace 3 2 128 (Fin (2 ^ 3)) ℕ) (iv : ℕ) (coms : Fin (2 ^ 3) → BitString 128)
    (hidden : Fin (2 ^ 3)) (j : Fin 3) :
    (FAEST.conversionCorrelation
      (extractRowsFromTrace (id : BitString 2 → BitString 2) tr iv coms) hidden j).Valid :=
  extractRowsFromTrace_conversionCorrelation_valid id tr iv coms hidden j

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
`ε_rel = 1 / 8`, prover budgets `Q_leaf = 8`, `Q_FS = 1`): `ksBound < 1`. -/
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
  exact ksBound_lt_one_of (d := 3) (comLen := 128) (Q_leaf := 8 + (2 ^ 3 - 1)) (Q_FS := 1 + 1)
    (k := 10) (num := 1) (e := 3) (ε_rel := (1 : ℝ≥0) / (2 ^ 3 : ℝ≥0))
    (by decide) (by decide) (by decide) (by simp)

/-- Concrete adaptive multi-verify knowledge soundness (`m = 2`, `Q_leaf = 8`, `Q_FS = 1`):
`ksBound < 1`. -/
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
  exact ksBound_lt_one_of (d := 3) (comLen := 128) (Q_leaf := 8 + 2 * (2 ^ 3 - 1)) (Q_FS := 1 + 2)
    (k := 12) (num := 1) (e := 3) (ε_rel := (1 : ℝ≥0) / (2 ^ 3 : ℝ≥0))
    (by decide) (by decide) (by decide) (by simp)

/-- ACT Spend parameters (`d = 11`, `comLen = 256`, `m = 1`, `Q_leaf = 2^12`, `Q_FS = 2^6`,
`ε_rel = 9 / 2^128`) keep straight-line extraction error `ksBound < 1`. -/
example :
    (ksBound 11 256 (2 ^ 12 + 1 * (2 ^ 11 - 1)) (2 ^ 6 + 1)
      ((9 : ℝ≥0) / (2 ^ 128 : ℝ≥0)) : ℝ≥0∞) < 1 := by
  have hk : (2 ^ 12 + 1 * (2 ^ 11 - 1)) * ((2 ^ 12 + 1 * (2 ^ 11 - 1)) + 2 ^ 11 * (2 ^ 6 + 1)) ≤
      2 ^ 30 := by decide
  have h2 : (2 ^ 6 + 1) * 9 * 4 < 3 * 2 ^ 128 :=
    (by decide : (2 ^ 6 + 1) * 9 * 4 < 3 * 2 ^ 11).trans_le
      (Nat.mul_le_mul_left 3 (Nat.pow_le_pow_right (by decide) (by decide : 11 ≤ 128)))
  exact ksBound_lt_one_of (d := 11) (comLen := 256) (Q_leaf := 2 ^ 12 + 1 * (2 ^ 11 - 1))
    (Q_FS := 2 ^ 6 + 1) (k := 30) (num := 9) (e := 128)
    (ε_rel := (9 : ℝ≥0) / (2 ^ 128 : ℝ≥0)) hk (by decide) h2 (by simp only [Nat.cast_ofNat])

/-! ## 2. Bridges to `AnonymousToken.Basic` and `AnonymousToken.Conservation` -/

private theorem isCostBounded_honestCommitLeaves {d sdLen comLen rowLen : ℕ} {Seed IV : Type}
    (expand : BitString sdLen → BitString rowLen) (iv : IV) (keys : Fin (2 ^ d) → Seed) :
    ∀ (k : ℕ) (hk : k ≤ 2 ^ d),
      IsCostBounded (fun _ : LeafQuery d Seed IV => 1)
        (honestCommitLeaves (comLen := comLen) expand iv keys k hk) k
  | 0, _ => OracleComp.IsCostBounded.pure _ 0
  | k + 1, hk => by
    unfold honestCommitLeaves
    refine (isCostBounded_honestCommitLeaves expand iv keys k (Nat.le_of_lt hk)).bind
      fun _ => ?_
    rw [show (1 : ℕ) = 1 + 0 from rfl]
    exact (OracleComp.IsCostBounded.query (spec := VOLEITHLeafSpec d sdLen comLen Seed IV)
      ⟨keys ⟨k, hk⟩, iv, ⟨k, hk⟩⟩).bind fun _ => OracleComp.IsCostBounded.pure _ 0

/-- Deterministic toy signature scheme certifying `Bool` targets by equality. -/
private def toySig : Signature.Scheme Unit Unit Bool Bool where
  keyGen := pure ((), ())
  sign _ t := pure t
  verify _ t sig := decide (t = sig)

private def tokTarget (_ : Unit) (o : BitString 2) : Bool := o 0

private def tokCheckRel {d : ℕ} (stmt : Unit × Bool) :
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
      (ROMTokenSpec Unit Bool 3 2 128 2 (Fin (2 ^ 3)) ℕ (Fin 3 → Bool) (Fin (2 ^ 3)) Bool)
      (Token Unit (BitString 2) Bool) := fun _ => do
  let iv : ℕ := 1
  let keys : Fin (2 ^ 3) → Fin (2 ^ 3) := fun _ => 0
  let (rows, coms) ← OracleComp.liftRight (spec₁ := unifSpec)
    (OracleComp.liftRight
      (spec₁ := ROMTokenSignSpec Unit Bool 3 128 2 (Fin (2 ^ 3)) ℕ (Fin 3 → Bool) Bool)
      (OracleComp.liftLeft
        (spec₂ := VOLEITHFSSpec 3 128 2 (Unit × Bool) ℕ (Fin 3 → Bool) (Fin (2 ^ 3)))
        (honestCommitLeaves (id : BitString 2 → BitString 2) iv keys (2 ^ 3) le_rfl)))
  let conv := FAEST.convertExpandedRows 3 rows
  let dCorr : BitString 2 := (fun _ => true) + conv.u
  let preMsg : Fin 3 → Bool := toyMkPreMsg conv.columns conv.u dCorr
  let delta ← OracleComp.liftRight (spec₁ := unifSpec)
    (OracleComp.liftRight
      (spec₁ := ROMTokenSignSpec Unit Bool 3 128 2 (Fin (2 ^ 3)) ℕ (Fin 3 → Bool) Bool)
      (OracleComp.liftRight (spec₁ := VOLEITHLeafSpec 3 2 128 (Fin (2 ^ 3)) ℕ)
        (OracleComp.query ⟨((), true), iv, coms, dCorr, preMsg⟩)))
  let prf : VOLEITHProof 3 128 2 (Fin (2 ^ 3)) ℕ (Fin 3 → Bool) :=
    ⟨iv, coms, dCorr, preMsg, fun idx => if idx = delta then 0 else keys idx⟩
  let _ ← OracleComp.liftRight (spec₁ := unifSpec)
    (OracleComp.liftLeft
      (spec₂ := VOLEITHROSpec 3 2 128 2 (Unit × Bool) (Fin (2 ^ 3)) ℕ (Fin 3 → Bool)
        (Fin (2 ^ 3)))
      (OracleComp.query (⟨(), true, prf⟩ : ROMTokenRequest Unit Bool 3 128 2 (Fin (2 ^ 3)) ℕ
        (Fin 3 → Bool))))
  return ⟨⟨(), fun _ => true⟩, true⟩

private theorem toyROMTokenAdversary_req_bound (pk : Unit) :
    IsCostBounded (Sum.elim (fun _ => 0) (Sum.elim (fun _ => 1) (fun _ => 0)))
      (toyROMTokenAdversary pk) 1 := by
  unfold toyROMTokenAdversary
  change IsCostBounded _ _ (0 + (0 + (1 + 0)))
  refine (IsCostBounded.liftRight
    (IsCostBounded.liftRight_of_cost_inr_eq_zero (fun _ => rfl) _)
    (fun _ => le_rfl)).bind fun _ => ?_
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
  rw [show (8 : ℕ) = 2 ^ 3 + (0 + 0) from by norm_num]
  refine (IsCostBounded.liftRight
    (IsCostBounded.liftRight
      ((isCostBounded_honestCommitLeaves (d := 3) (sdLen := 2) (comLen := 128) id 1
        (fun _ => 0) (2 ^ 3) le_rfl).liftLeft fun _ => le_rfl)
      fun _ => le_rfl)
    fun _ => le_rfl).bind fun _ => ?_
  rw [show (0 + 0 : ℕ) = 0 + (0 + 0) from rfl]
  refine (IsCostBounded.liftRight
    (IsCostBounded.liftRight
      (IsCostBounded.liftRight_of_cost_inr_eq_zero (fun _ => rfl) _)
      fun _ => le_rfl)
    fun _ => le_rfl).bind fun _ => ?_
  rw [show (0 + 0 : ℕ) = 0 + 0 from rfl]
  exact (IsCostBounded.liftRight
    (IsCostBounded.liftLeft_of_cost_inl_eq_zero (fun _ => rfl) _)
    fun _ => le_rfl).bind fun _ => IsCostBounded.pure _ 0

private theorem toyROMTokenAdversary_fs_bound (pk : Unit) :
    IsCostBounded (Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0) voleithFSCost))
      (toyROMTokenAdversary pk) 1 := by
  unfold toyROMTokenAdversary
  rw [show (1 : ℕ) = 0 + (1 + 0) from rfl]
  refine (IsCostBounded.liftRight
    (IsCostBounded.liftRight
      (IsCostBounded.liftLeft_of_cost_inl_eq_zero (fun _ => rfl) _)
      fun _ => le_rfl)
    fun _ => le_rfl).bind fun _ => ?_
  rw [show (1 + 0 : ℕ) = 1 + (0 + 0) from rfl]
  refine (IsCostBounded.liftRight
    (IsCostBounded.liftRight
      (IsCostBounded.liftRight (IsCostBounded.query _) fun _ => le_rfl)
      fun _ => le_rfl)
    fun _ => le_rfl).bind fun _ => ?_
  rw [show (0 + 0 : ℕ) = 0 + 0 from rfl]
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
straight-line extraction reductions with `ksBound < 1`. -/
example :
    (romUnextractedTokenExperiment id id tokCheckRel toySig tokTarget
        toyROMTokenAdversary).succProbability ≤
      (toySig.eufCmaExperiment (targetForger tokTarget
          (extractedForgerOfROM id id id tokCheckRel toyROMTokenAdversary))).succProbability +
        (bindingExperiment toySig tokTarget
          (extractedForgerOfROM id id id tokCheckRel toyROMTokenAdversary)).succProbability +
        ksBound 3 128 (8 + 1 * (2 ^ 3 - 1)) (1 + 1) ((1 : ℝ≥0) / (2 ^ 3 : ℝ≥0)) ∧
    (ksBound 3 128 (8 + 1 * (2 ^ 3 - 1)) (1 + 1) ((1 : ℝ≥0) / (2 ^ 3 : ℝ≥0)) : ℝ≥0∞) < 1 := by
  refine ⟨unextractedTokenExperiment_succProbability_le id id id toySig tokTarget tokCheckRel
    tokCheckRel_sound_error toyROMTokenAdversary toyROMTokenAdversary_req_bound
    toyROMTokenAdversary_leaf_bound toyROMTokenAdversary_fs_bound, ?_⟩
  have hk : (8 + 1 * (2 ^ 3 - 1)) * ((8 + 1 * (2 ^ 3 - 1)) + 2 ^ 3 * (1 + 1)) ≤ 2 ^ 10 := by
    decide
  have hcomp : 10 + 2 ≤ 128 := by decide
  have h2 : (1 + 1) * 1 * 4 < 3 * 2 ^ 3 := by decide
  exact ksBound_lt_one_of (d := 3) (comLen := 128) (Q_leaf := 8 + 1 * (2 ^ 3 - 1))
    (Q_FS := 1 + 1) (k := 10) (num := 1) (e := 3) (ε_rel := (1 : ℝ≥0) / (2 ^ 3 : ℝ≥0))
    hk hcomp h2 (by simp)

example :
    (romUnextractedTokenExperiment id id tokCheckRel toySig tokTarget
        toyROMTokenAdversary).succProbability ≤
      (extractedExperiment toySig tokTarget
        (extractedForgerOfROM id id id tokCheckRel toyROMTokenAdversary)).succProbability +
        ksBound 3 128 (8 + 1 * (2 ^ 3 - 1)) (1 + 1) ((1 : ℝ≥0) / (2 ^ 3 : ℝ≥0)) :=
  unextractedTokenExperiment_succProbability_le_extracted id id id toySig tokTarget tokCheckRel
    tokCheckRel_sound_error toyROMTokenAdversary toyROMTokenAdversary_req_bound
    toyROMTokenAdversary_leaf_bound toyROMTokenAdversary_fs_bound

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

private def consDecWit (x : BitString 2) :
    ROMConservationWitness Bool Bool ((Bool × Bool × ℕ) × ℕ) :=
  .issue ⟨x 0, x 1⟩

private noncomputable def toyROMConsAdversary :
    Unit → ProbOracleComp (ROMConservationSpec Bool Bool (Bool × Bool × ℕ) 3 2 128 2 Unit
      (Fin (2 ^ 3)) ℕ (macPreMsg 3 2) (Fin (2 ^ 3)) ((Bool × Bool × ℕ) × ℕ)) Bool := fun _ => do
  let q : ROMConservationQuery Bool Bool (Bool × Bool × ℕ) :=
    .issue ⟨false, 1, (false, false, 1)⟩
  let iv : ℕ := 1
  let keys : Fin (2 ^ 3) → Fin (2 ^ 3) := fun _ => 0
  let (rows, coms) ← OracleComp.liftRight (spec₁ := unifSpec)
    (OracleComp.liftRight
      (spec₁ := ROMConservationIssuerSpec Bool Bool (Bool × Bool × ℕ) 3 128 2 (Fin (2 ^ 3)) ℕ
        (macPreMsg 3 2) ((Bool × Bool × ℕ) × ℕ))
      (OracleComp.liftLeft
        (spec₂ := VOLEITHFSSpec 3 128 2 (ROMConservationStmt Unit Bool Bool (Bool × Bool × ℕ))
          ℕ (macPreMsg 3 2) (Fin (2 ^ 3)))
        (honestCommitLeaves (id : BitString 2 → BitString 2) iv keys (2 ^ 3) le_rfl)))
  let conv := FAEST.convertExpandedRows 3 rows
  let dCorr : BitString 2 := (fun _ => false) + conv.u
  let preMsg : macPreMsg 3 2 := (conv.columns, dCorr + conv.u)
  let delta ← OracleComp.liftRight (spec₁ := unifSpec)
    (OracleComp.liftRight
      (spec₁ := ROMConservationIssuerSpec Bool Bool (Bool × Bool × ℕ) 3 128 2 (Fin (2 ^ 3)) ℕ
        (macPreMsg 3 2) ((Bool × Bool × ℕ) × ℕ))
      (OracleComp.liftRight (spec₁ := VOLEITHLeafSpec 3 2 128 (Fin (2 ^ 3)) ℕ)
        (OracleComp.query ⟨⟨(), q⟩, iv, coms, dCorr, preMsg⟩)))
  let prf : VOLEITHProof 3 128 2 (Fin (2 ^ 3)) ℕ (macPreMsg 3 2) :=
    ⟨iv, coms, dCorr, preMsg, fun idx => if idx = delta then 0 else keys idx⟩
  let _ ← OracleComp.liftRight (spec₁ := unifSpec)
    (OracleComp.liftLeft
      (spec₂ := VOLEITHROSpec 3 2 128 2
        (ROMConservationStmt Unit Bool Bool (Bool × Bool × ℕ)) (Fin (2 ^ 3)) ℕ (macPreMsg 3 2)
        (Fin (2 ^ 3)))
      (OracleComp.query ⟨q, prf⟩))
  return false

private theorem toyROMConsAdversary_req_bound (pk : Unit) :
    IsCostBounded (Sum.elim (fun _ => 0) (Sum.elim (fun _ => 1) (fun _ => 0)))
      (toyROMConsAdversary pk) 1 := by
  unfold toyROMConsAdversary
  change IsCostBounded _ _ (0 + (0 + (1 + 0)))
  refine (IsCostBounded.liftRight
    (IsCostBounded.liftRight_of_cost_inr_eq_zero (fun _ => rfl) _)
    (fun _ => le_rfl)).bind fun _ => ?_
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
  rw [show (8 : ℕ) = 2 ^ 3 + (0 + 0) from by norm_num]
  refine (IsCostBounded.liftRight
    (IsCostBounded.liftRight
      ((isCostBounded_honestCommitLeaves (d := 3) (sdLen := 2) (comLen := 128) id 1
        (fun _ => 0) (2 ^ 3) le_rfl).liftLeft fun _ => le_rfl)
      fun _ => le_rfl)
    fun _ => le_rfl).bind fun _ => ?_
  rw [show (0 + 0 : ℕ) = 0 + (0 + 0) from rfl]
  refine (IsCostBounded.liftRight
    (IsCostBounded.liftRight
      (IsCostBounded.liftRight_of_cost_inr_eq_zero (fun _ => rfl) _)
      fun _ => le_rfl)
    fun _ => le_rfl).bind fun _ => ?_
  rw [show (0 + 0 : ℕ) = 0 + 0 from rfl]
  exact (IsCostBounded.liftRight
    (IsCostBounded.liftLeft_of_cost_inl_eq_zero (fun _ => rfl) _)
    fun _ => le_rfl).bind fun _ => IsCostBounded.pure _ 0

private theorem toyROMConsAdversary_fs_bound (pk : Unit) :
    IsCostBounded (Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0) voleithFSCost))
      (toyROMConsAdversary pk) 1 := by
  unfold toyROMConsAdversary
  rw [show (1 : ℕ) = 0 + (1 + 0) from rfl]
  refine (IsCostBounded.liftRight
    (IsCostBounded.liftRight
      (IsCostBounded.liftLeft_of_cost_inl_eq_zero (fun _ => rfl) _)
      fun _ => le_rfl)
    fun _ => le_rfl).bind fun _ => ?_
  rw [show (1 + 0 : ℕ) = 1 + (0 + 0) from rfl]
  refine (IsCostBounded.liftRight
    (IsCostBounded.liftRight
      (IsCostBounded.liftRight (IsCostBounded.query _) fun _ => le_rfl)
      fun _ => le_rfl)
    fun _ => le_rfl).bind fun _ => ?_
  rw [show (0 + 0 : ℕ) = 0 + 0 from rfl]
  exact (IsCostBounded.liftRight
    (IsCostBounded.liftLeft_of_cost_inl_eq_zero (fun _ => rfl) _)
    fun _ => le_rfl).bind fun _ => IsCostBounded.pure _ 0

/-- Extracted conservation adversary preserves the `1`-query bound. -/
example (pk : Unit) :
    (extractedAdversaryOfROM (d := 3) (sdLen := 2) (comLen := 128) (rowLen := 2)
      id consDecWit id
      (macCheckRel consDecWit (conservationRel consTestComNat Prod.mk consTestSig))
      toyROMConsAdversary pk).IsQueryBounded 1 :=
  extractedAdversaryOfROM_isQueryBounded id consDecWit id
    (macCheckRel consDecWit (conservationRel consTestComNat Prod.mk consTestSig))
    toyROMConsAdversary toyROMConsAdversary_req_bound pk

/-- Concrete `AnonymousToken.Conservation` ROM-to-extracted and end-to-end EUF-CMA + commitment
binding + straight-line extraction reductions using `consTestComScheme`. -/
example :
    (romUnextractedConservationExperiment id id Prod.mk
        (macCheckRel consDecWit (conservationRel consTestComNat Prod.mk consTestSig))
        consTestSig toyROMConsAdversary).succProbability ≤
      (Conservation.extractedConservationExperiment consTestComNat Prod.mk consTestSig
        (extractedAdversaryOfROM id consDecWit id
          (macCheckRel consDecWit (conservationRel consTestComNat Prod.mk consTestSig))
          toyROMConsAdversary)).succProbability +
        ksBound 3 128 (8 + 1 * (2 ^ 3 - 1)) (1 + 1) ((1 : ℝ≥0) / (2 ^ 3 : ℝ≥0)) :=
  unextractedConservationExperiment_succProbability_le_extracted id consDecWit id consTestComNat
    Prod.mk consTestSig
    (macCheckRel consDecWit (conservationRel consTestComNat Prod.mk consTestSig))
    (macCheckRel_sound_error consDecWit (conservationRel consTestComNat Prod.mk consTestSig))
    toyROMConsAdversary toyROMConsAdversary_req_bound toyROMConsAdversary_leaf_bound
    toyROMConsAdversary_fs_bound

example :
    (romUnextractedConservationExperiment id id Prod.mk
        (macCheckRel consDecWit (conservationRel consTestComNat Prod.mk consTestSig))
        consTestSig toyROMConsAdversary).succProbability ≤
      (consTestSig.eufCmaExperiment (targetForger (Credit.target consTestComNat Prod.mk)
          (Conservation.noteForger consTestComNat Prod.mk consTestSig
            (extractedAdversaryOfROM id consDecWit id
              (macCheckRel consDecWit (conservationRel consTestComNat Prod.mk consTestSig))
              toyROMConsAdversary)))).succProbability +
        (consTestComScheme.bindingExperiment
          (Conservation.commitmentBindingReduction consTestComNat consTestSig
            (extractedAdversaryOfROM id consDecWit id
              (macCheckRel consDecWit (conservationRel consTestComNat Prod.mk consTestSig))
              toyROMConsAdversary))).succProbability +
        ksBound 3 128 (8 + 1 * (2 ^ 3 - 1)) (1 + 1) ((1 : ℝ≥0) / (2 ^ 3 : ℝ≥0)) :=
  unextractedConservationExperiment_succProbability_le_prod_mk id consDecWit id consTestComNat
    consTestComScheme (fun _ _ _ _ _ _ => rfl) consTestSig
    (macCheckRel consDecWit (conservationRel consTestComNat Prod.mk consTestSig))
    (macCheckRel_sound_error consDecWit (conservationRel consTestComNat Prod.mk consTestSig))
    toyROMConsAdversary toyROMConsAdversary_req_bound toyROMConsAdversary_leaf_bound
    toyROMConsAdversary_fs_bound

/-! ## 3. Negative / separation tests for PRG leaf commitments (`leaf_hash::aes_ctr`) -/

private def prgLeafColliding (s : Bool) (_ : Unit) (_ : Fin (2 ^ 0)) : LeafOutput 1 1 :=
  ⟨fun _ => s, 0⟩

/-- On a colliding PRG (`com = 0` for seeds `false` and `true` at `d = 0`), local prover makes
zero `H_leaf` queries, accepts with probability `1`, and defeats **every** query-log extractor AND
**every** unbounded proof extractor `ext : LeafTrace → VOLEITHProof → Option Bool` with
probability `1`. -/
example :
    IsCostBounded
      (Sum.elim (fun _ => 0) (voleithLeafCost (d := 0) (Seed := Bool) (IV := Unit)
        (comLen := 1) (rowLen := 1) (Stmt := Unit) (PreMsg := Unit)))
      (prgLeafProver (d := 0) (sdLen := 1) (comLen := 1) (rowLen := 1) (Chal := Unit)
        id prgLeafColliding (fun w _ => w) (fun _ => 0) (fun _ _ _ => ())
        false () (fun _ => false) () false) 0 :=
  prgLeafProver_leafCost_zero id prgLeafColliding (fun w _ => w) (fun _ => 0) (fun _ _ _ => ())
    false () (fun _ => false) () false

example {b : Bool} {st : VOLEITHTraceState 0 1 1 1 Unit Bool Unit Unit Unit}
    (hmem : (b, st) ∈ (ProbOracleComp.runWith
      (voleithMemoize (d := 0) (sdLen := 1) (comLen := 1) (rowLen := 1)
        (Stmt := Unit) (Seed := Bool) (IV := Unit) (PreMsg := Unit) (Chal := Unit))
      (prgLeafGame (d := 0) (sdLen := 1) (comLen := 1) (rowLen := 1) (Chal := Unit)
        id prgLeafColliding (fun w _ => w) (fun _ => 0) (fun _ _ _ => ())
        (fun _ _ _ _ _ => true) false () (fun _ => false) () false) ([], [])).support) :
    st.1 = [] :=
  prgLeafGame_leafTrace_eq_nil id prgLeafColliding (fun w _ => w) (fun _ => 0) (fun _ _ _ => ())
    (fun _ _ _ _ _ => true) false () (fun _ => false) () false (fun _ _ _ => rfl) hmem

example :
    ((ProbOracleComp.runWith
      (voleithMemoize (d := 0) (sdLen := 1) (comLen := 1) (rowLen := 1)
        (Stmt := Unit) (Seed := Bool) (IV := Unit) (PreMsg := Unit) (Chal := Unit))
      (prgLeafGame (d := 0) (sdLen := 1) (comLen := 1) (rowLen := 1) (Chal := Unit)
        id prgLeafColliding (fun w _ => w) (fun _ => 0) (fun _ _ _ => ())
        (fun _ _ _ _ _ => true) false () (fun _ => false) () false)
      ([], [])).map Prod.fst) = PMF.pure true :=
  prgLeafGame_eq_pure_true id prgLeafColliding (fun w _ => w) (fun _ => 0) (fun _ _ _ => ())
    (fun _ _ _ _ _ => true) false () (fun _ => false) () false (fun _ _ _ => rfl)

example (extLog : LeafTrace 0 1 1 Bool Unit → Option Bool) (hne : extLog [] ≠ some false) :
    ((ProbOracleComp.runWith
      (voleithMemoize (d := 0) (sdLen := 1) (comLen := 1) (rowLen := 1)
        (Stmt := Unit) (Seed := Bool) (IV := Unit) (PreMsg := Unit) (Chal := Unit))
      (prgLeafGame (d := 0) (sdLen := 1) (comLen := 1) (rowLen := 1) (Chal := Unit)
        id prgLeafColliding (fun w _ => w) (fun _ => 0) (fun _ _ _ => ())
        (fun _ _ _ _ _ => true) false () (fun _ => false) () false)
      ([], [])).map fun (b, st) => decide (b = true ∧ extLog st.1 ≠ some false)).toOuterMeasure
        {true} = 1 :=
  toOuterMeasure_prgLeaf_queryLog_fails_eq_one id prgLeafColliding (fun w _ => w) (fun _ => 0)
    (fun _ _ _ => ()) (fun _ _ _ _ _ => true) false () (fun _ => false) () false
    (fun _ _ _ => rfl) extLog hne

example (ext : LeafTrace 0 1 1 Bool Unit → VOLEITHProof 0 1 1 Bool Unit Unit → Option Bool) :
    ∃ w : Bool, ∃ keys : Fin (2 ^ 0) → Bool,
      ((ProbOracleComp.runWith
        (voleithMemoize (d := 0) (sdLen := 1) (comLen := 1) (rowLen := 1)
          (Stmt := Unit) (Seed := Bool) (IV := Unit) (PreMsg := Unit) (Chal := Unit))
        (do
          let prf ← prgLeafProver (d := 0) (sdLen := 1) (comLen := 1) (rowLen := 1)
            (Stmt := Unit) (Seed := Bool) (IV := Unit) (PreMsg := Unit) (Chal := Unit)
            id prgLeafColliding (fun w _ => w) (fun _ => 0) (fun _ _ _ => ())
            false () keys () w
          let ok ← prgLeafVerify id prgLeafColliding (fun _ => 0) (fun _ _ _ _ _ => true) () prf
          return (ok, prf)) ([], [])).map fun ((ok, prf), st) =>
            decide (ok = true ∧ ext st.1 prf ≠ some w)).toOuterMeasure {true} = 1 := by
  refine exists_valid_prgLeaf_extract_fails_all (id : BitString 1 → BitString 1) prgLeafColliding
    (fun w _ => w) (fun _ => 0) (fun _ _ _ => ()) (fun _ _ _ _ _ => true)
    false () (fun _ => false) (fun _ => true) () false true (by decide)
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl) ?_ rfl () ?_ ext
  · ext i
    simp only [FAEST.convertExpandedRows, prgLeafColliding, id_eq, Pi.add_apply]
    decide
  · intro ()
    constructor <;> ext idx <;> simp [Fin.eq_zero idx]

/-- Query-log separation holds even on our non-trivial `1 / 8`-sound `d = 3` VOLE protocol
(`toyCheckRel`): valid witnesses `w₀ = 0` and `w₁ = (fun _ => 1)` both satisfy `toyCheckRel`
with `prgLeaf` using zero `H_leaf` queries, so every `extLog` fails on one of them with
probability `1`. -/
private def prgLeafD3 (s : Fin (2 ^ 3)) (_ : ℕ) (_ : Fin (2 ^ 3)) : LeafOutput 2 128 :=
  ⟨fun _ => decide (s.val % 2 = 1), 0⟩

example (extLog : LeafTrace 3 2 128 (Fin (2 ^ 3)) ℕ → Option (BitString 2)) :
    ∃ w : BitString 2,
      ((ProbOracleComp.runWith
        (voleithMemoize (d := 3) (sdLen := 2) (comLen := 128) (rowLen := 2)
          (Stmt := Bool) (Seed := Fin (2 ^ 3)) (IV := ℕ) (PreMsg := Fin 3 → Bool)
          (Chal := Fin (2 ^ 3)))
        (prgLeafGame (d := 3) (sdLen := 2) (comLen := 128) (rowLen := 2) (Chal := Fin (2 ^ 3))
          id prgLeafD3 id id toyMkPreMsg toyCheckRel 0 7 (fun _ => 0) true w)
        ([], [])).map fun (b, st) => decide (b = true ∧ extLog st.1 ≠ some w)).toOuterMeasure
          {true} = 1 :=
  exists_witness_prgLeaf_queryLog_fails_eq_one id prgLeafD3 id id toyMkPreMsg toyCheckRel
    0 7 (fun _ => 0) true (fun j => if j = 0 then true else false) (fun _ => true)
    (by
      intro heq
      have h := congrFun heq 1
      simp at h)
    (fun pCols u delta => toyCheckRel_complete true _ rfl pCols u delta)
    (fun pCols u delta => toyCheckRel_complete true _ rfl pCols u delta)
    extLog

end CslibFrontierTests.Crypto.VOLEROExtractor
