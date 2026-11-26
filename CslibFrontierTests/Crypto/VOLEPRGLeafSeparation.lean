/-
Copyright (c) 2026 Samuel Schlesinger, Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Karn Seth
-/

module

import CslibFrontier.Crypto.Protocols.FAEST.Conversion
import CslibFrontier.Crypto.Protocols.VOLE.PRGLeafSeparation
import CslibFrontier.Crypto.Protocols.VOLE.ROExtractor
import CslibFrontier.Probability.PMF.Support

/-!
# Non-degenerate `d = 3` separations for PRG leaf commitments (`leaf_hash::aes_ctr`)

Exercises `CslibFrontier.Crypto.Protocols.VOLE.PRGLeafSeparation` via an ordinary `module` import
using a concrete `d = 3` (`2 ^ 3 = 8` leaves) colliding PRG fixture (`prgLeafD3`):
- Zero `H_leaf` query budget and completeness: `prgLeafProver_leafCost_zero`,
  `prgLeafGame_leafTrace_eq_nil`, `prgLeafGame_eq_pure_true`, `extractWitnessFromTrace_nil`.
- Disjoint-statement query-log separation (`exists_valid_prgLeaf_queryLog_fails_Rel_eq_one`).
- Deterministic preimage-table separation under `Function.Injective id`
  (`prgLeaf_preimage_extractor_fails`).
- Unbounded proof-only separation omitting `stmt`
  (`exists_valid_prgLeaf_proofOnly_extract_fails_ge`, bound `≥ 1 / 8`).
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.VOLEPRGLeafSeparation

open Cslib Cslib.Crypto Cslib.Crypto.Protocols.VOLE
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


/-! ## 3. Non-degenerate `d = 3` separations for PRG leaf commitments (`leaf_hash::aes_ctr`) -/

/-- Colliding deterministic `d = 3` leaf PRG (`com = 0` regardless of seed, while parity of seed
determines the expanded row). -/
private def prgLeafD3 (s : Fin (2 ^ 3)) (_ : ℕ) (_ : Fin (2 ^ 3)) : LeafOutput 2 128 :=
  ⟨fun _ => decide (s.val % 2 = 1), 0⟩

/-- Honest `d = 3` PRG prover makes zero `H_leaf` queries, leaves `st.1 = []`, and passes
`prgLeafVerify` with probability `1`. -/
example :
    IsCostBounded
      (Sum.elim (fun _ => 0) (voleithLeafCost (d := 3) (Seed := Fin (2 ^ 3)) (IV := ℕ)
        (comLen := 128) (rowLen := 2) (Stmt := Bool) (PreMsg := Fin 3 → Bool)))
      (prgLeafProver (d := 3) (sdLen := 2) (comLen := 128) (rowLen := 2) (Chal := Fin (2 ^ 3))
        id prgLeafD3 id id toyMkPreMsg 0 7 (fun _ => 0) true (fun _ => true)) 0 :=
  prgLeafProver_leafCost_zero id prgLeafD3 id id toyMkPreMsg 0 7 (fun _ => 0) true (fun _ => true)

example {b : Bool} {st : VOLEITHTraceState 3 2 128 2 Bool (Fin (2 ^ 3)) ℕ (Fin 3 → Bool)
    (Fin (2 ^ 3))}
    (hmem : (b, st) ∈ (ProbOracleComp.runWith
      (voleithMemoize (d := 3) (sdLen := 2) (comLen := 128) (rowLen := 2)
        (Stmt := Bool) (Seed := Fin (2 ^ 3)) (IV := ℕ) (PreMsg := Fin 3 → Bool)
        (Chal := Fin (2 ^ 3)))
      (prgLeafGame (d := 3) (sdLen := 2) (comLen := 128) (rowLen := 2) (Chal := Fin (2 ^ 3))
        id prgLeafD3 id id toyMkPreMsg toyCheckRel 0 7 (fun _ => 0) true (fun _ => true))
      ([], [])).support) :
    st.1 = [] :=
  prgLeafGame_leafTrace_eq_nil id prgLeafD3 id id toyMkPreMsg toyCheckRel 0 7 (fun _ => 0) true
    (fun _ => true) (fun pCols u delta => toyCheckRel_complete true _ rfl pCols u delta) hmem

example :
    ((ProbOracleComp.runWith
      (voleithMemoize (d := 3) (sdLen := 2) (comLen := 128) (rowLen := 2)
        (Stmt := Bool) (Seed := Fin (2 ^ 3)) (IV := ℕ) (PreMsg := Fin 3 → Bool)
        (Chal := Fin (2 ^ 3)))
      (prgLeafGame (d := 3) (sdLen := 2) (comLen := 128) (rowLen := 2) (Chal := Fin (2 ^ 3))
        id prgLeafD3 id id toyMkPreMsg toyCheckRel 0 7 (fun _ => 0) true (fun _ => true))
      ([], [])).map Prod.fst) = PMF.pure true :=
  prgLeafGame_eq_pure_true id prgLeafD3 id id toyMkPreMsg toyCheckRel 0 7 (fun _ => 0) true
    (fun _ => true) (fun pCols u delta => toyCheckRel_complete true _ rfl pCols u delta)

/-- On an empty `H_leaf` trace, `extractWitnessFromTrace` recovers only `decWit prf.dCorr`. -/
example (prf : VOLEITHProof 3 128 2 (Fin (2 ^ 3)) ℕ (Fin 3 → Bool)) :
    extractWitnessFromTrace (id : BitString 2 → BitString 2) (id : BitString 2 → BitString 2)
      ([] : LeafTrace 3 2 128 (Fin (2 ^ 3)) ℕ) prf = prf.dCorr :=
  extractWitnessFromTrace_nil id id prf

/-- **Disjoint-statement query-log separation (`d = 3`, `1 / 8`-sound `toyCheckRel`)**: **every**
query-log extractor `extLog : LeafTrace → Option Wit` (seeing neither statement nor proof) fails
`toyRel` with probability `1` on at least one of `(false, 0)` or `(true, fun _ => true)`. -/
example (extLog : LeafTrace 3 2 128 (Fin (2 ^ 3)) ℕ → Option (BitString 2)) :
    ∃ stmt : Bool, ∃ w : BitString 2, toyRel stmt w = true ∧
      ((ProbOracleComp.runWith
        (voleithMemoize (d := 3) (sdLen := 2) (comLen := 128) (rowLen := 2)
          (Stmt := Bool) (Seed := Fin (2 ^ 3)) (IV := ℕ) (PreMsg := Fin 3 → Bool)
          (Chal := Fin (2 ^ 3)))
        (prgLeafGame (d := 3) (sdLen := 2) (comLen := 128) (rowLen := 2) (Chal := Fin (2 ^ 3))
          id prgLeafD3 id id toyMkPreMsg toyCheckRel 0 7 (fun _ => 0) stmt w)
        ([], [])).map fun (b, st) =>
          decide (b = true ∧ (extLog st.1).elim false (toyRel stmt) = false)).toOuterMeasure
            {true} = 1 := by
  refine exists_valid_prgLeaf_queryLog_fails_Rel_eq_one id prgLeafD3 id id toyMkPreMsg toyRel
    toyCheckRel 0 7 (fun _ => 0) false true (0 : BitString 2) (fun _ => true)
    (by decide) (by decide) ?_
    (fun pCols u delta => toyCheckRel_complete false _ rfl pCols u delta)
    (fun pCols u delta => toyCheckRel_complete true _ rfl pCols u delta)
    extLog
  intro w' ⟨h0, h1⟩
  simp only [toyRel, decide_eq_true_eq] at h0 h1
  exact absurd (h0.symm.trans h1) (by decide)

/-- **Preimage-table separation at `d = 3` under colliding `prgLeafD3`**: `(false, 0, fun _ => 0)`
and `(true, fun _ => true, fun idx => if idx = 0 then 1 else 0)` produce identical commitments `0`,
differing expanded masks `u`, and identical `dCorr = 0`, so **every** deterministic preimage-table
extractor `extPre` fails `toyRel` with probability `1` on one of them. -/
example :
    (fun _ : Fin (2 ^ 3) => (0 : Fin (2 ^ 3))) ≠ (fun idx => if idx = 0 then 1 else 0) ∧
    ∀ extPre : (Fin (2 ^ 3) → BitString 128) → ℕ → Fin (2 ^ 3) → Fin (2 ^ 3),
      ∃ stmt : Bool, ∃ w : BitString 2, ∃ keys : Fin (2 ^ 3) → Fin (2 ^ 3),
        toyRel stmt w = true ∧
        ((ProbOracleComp.runWith
          (voleithMemoize (d := 3) (sdLen := 2) (comLen := 128) (rowLen := 2)
            (Stmt := Bool) (Seed := Fin (2 ^ 3)) (IV := ℕ) (PreMsg := Fin 3 → Bool)
            (Chal := Fin (2 ^ 3)))
          (do
            let prf ← prgLeafProver (d := 3) (sdLen := 2) (comLen := 128) (rowLen := 2)
              (Stmt := Bool) (Seed := Fin (2 ^ 3)) (IV := ℕ) (PreMsg := Fin 3 → Bool)
              (Chal := Fin (2 ^ 3)) id prgLeafD3 id id toyMkPreMsg 0 7 keys stmt w
            let ok ← prgLeafVerify id prgLeafD3 id toyCheckRel stmt prf
            return (ok, prf)) ([], [])).map fun ((ok, prf), _) =>
              let wExt := (id : BitString 2 → BitString 2) (prf.dCorr +
                (FAEST.convertExpandedRows 3
                  (fun idx => (id : BitString 2 → BitString 2)
                    (prgLeafD3 (extPre prf.coms prf.iv idx) prf.iv idx).seedOut)).u)
              decide (ok = true ∧ toyRel stmt wExt = false)).toOuterMeasure {true} = 1 := by
  refine prgLeaf_preimage_extractor_fails id prgLeafD3 id id id toyMkPreMsg toyRel toyCheckRel
    0 7 (fun _ => 0) (fun idx => if idx = 0 then 1 else 0)
    false true (0 : BitString 2) (fun _ => true) (by decide) (by decide) ?_ Function.injective_id
    (fun pCols u delta => toyCheckRel_complete false _ rfl pCols u delta)
    (fun pCols u delta => toyCheckRel_complete true _ rfl pCols u delta)
    (fun _ => rfl) (by decide)
  intro w' ⟨h0, h1⟩
  simp only [toyRel, decide_eq_true_eq] at h0 h1
  exact absurd (h0.symm.trans h1) (by decide)

/-- **Proof-only separation at `d = 3`**: hiding leaf `deltaStar = 0`, `(false, 0, fun _ => 0)`
and `(true, fun _ => true, fun idx => if idx = 0 then 1 else 0)` emit the exact same proof at
`deltaStar = 0`, so **every** proof-only extractor `ext : LeafTrace → VOLEITHProof → Option Wit`
fails `toyRel` with probability at least `1 / 8`. -/
example (ext : LeafTrace 3 2 128 (Fin (2 ^ 3)) ℕ →
    VOLEITHProof 3 128 2 (Fin (2 ^ 3)) ℕ (Fin 3 → Bool) → Option (BitString 2)) :
    ∃ stmt : Bool, ∃ w : BitString 2, ∃ keys : Fin (2 ^ 3) → Fin (2 ^ 3),
      toyRel stmt w = true ∧
      (((Fintype.card (Fin (2 ^ 3)) : ℝ≥0∞)⁻¹) ≤
        ((ProbOracleComp.runWith
          (voleithMemoize (d := 3) (sdLen := 2) (comLen := 128) (rowLen := 2)
            (Stmt := Bool) (Seed := Fin (2 ^ 3)) (IV := ℕ) (PreMsg := Fin 3 → Bool)
            (Chal := Fin (2 ^ 3)))
          (do
            let prf ← prgLeafProver (d := 3) (sdLen := 2) (comLen := 128) (rowLen := 2)
              (Stmt := Bool) (Seed := Fin (2 ^ 3)) (IV := ℕ) (PreMsg := Fin 3 → Bool)
              (Chal := Fin (2 ^ 3)) id prgLeafD3 id id toyMkPreMsg 0 7 keys stmt w
            let ok ← prgLeafVerify id prgLeafD3 id toyCheckRel stmt prf
            return (ok, prf)) ([], [])).map fun ((ok, prf), st) =>
              decide (ok = true ∧ (ext st.1 prf).elim false (toyRel stmt) = false)).toOuterMeasure
            {true}) := by
  refine exists_valid_prgLeaf_proofOnly_extract_fails_ge id prgLeafD3 id id toyMkPreMsg toyRel
    toyCheckRel 0 7 (fun _ => 0) (fun idx => if idx = 0 then 1 else 0)
    false true (0 : BitString 2) (fun _ => true) (by decide) (by decide) ?_
    (fun pCols u delta => toyCheckRel_complete false _ rfl pCols u delta)
    (fun pCols u delta => toyCheckRel_complete true _ rfl pCols u delta)
    0 ?_ ext
  · intro w' ⟨h0, h1⟩
    simp only [toyRel, decide_eq_true_eq] at h0 h1
    exact absurd (h0.symm.trans h1) (by decide)
  · apply prgLeafProofOfDelta_eq_of
    · intro idx; rfl
    · decide
    · decide
    · intro idx hne
      by_cases h : idx = 0
      · exact absurd h hne
      · simp [h]


end CslibFrontierTests.Crypto.VOLEPRGLeafSeparation
