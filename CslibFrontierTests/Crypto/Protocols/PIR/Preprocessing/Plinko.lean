/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/
module

public import CslibFrontier.Crypto.Primitives.PRF.Invertible
public import CslibFrontier.Crypto.Protocols.PIR.Preprocessing.Plinko

@[expose] public section

/-! # Tests for Invertible PRFs and the Plinko Preprocessing PIR Scheme

Concrete smoke tests exercising:
1. `idealInvertiblePRF`, `isCorrect_idealInvertiblePRF`,
   `forwardAdvantage_idealInvertiblePRF_eq_zero`, `InvertiblePRF.composePerm`, and
   `InvertiblePRF.isCorrect_composePerm`.
2. Single-pass database streaming (`streamEntry`, `foldr_streamEntry_univ`) and
   `PlinkoState.Valid` on a concrete `2 × 2` database (`c = 2`, `w = 2`, `nReg = 2`, `nBackup = 1`).
3. Hint lookup (`findHintSlotScan`, `findHintSlot_eq_findHintSlotScan`, `getHintScan`),
   state transition (`PlinkoState.nextState`, `PlinkoState.valid_nextState`), and single/multi-query
   correctness (`PlinkoState.eval_step_plinkoScheme`, `PlinkoState.isCorrectFrom_plinkoScheme`),
   including regular hint consumption, backup hint promotion, and cache hits.
4. Single-query exact privacy (`eval_buildQuery_conditioned_eq_plinkoSim`), adaptive multi-query
   perfect privacy (`isPerfectlyPrivateWith_plinkoHybridScheme`,
   `privacyAdvantage_plinkoHybridScheme_eq_zero`), and non-adaptive transcript privacy
   (`eval_queryTranscript_plinkoHybridScheme`).
5. Database and hint updates (`updateDB`, `updateHint`, `updateState`, `applyUpdates`,
   `PlinkoState.valid_updateHint`, `PlinkoState.valid_updateState`).
-/

namespace Cslib.Crypto.Protocols.PIR.Preprocessing.Plinko.Tests

open Cslib.Crypto.PRF
open Cslib.Crypto.Protocols.PIR.Preprocessing
open Cslib.Crypto.Protocols.PIR.Preprocessing.Plinko

/-! ### 1. Invertible PRF and permutation composition smoke tests -/

/-- Canonical ideal iPRF on `Fin 3 → Fin 2` with key space `Fin 3 → Fin 2`. -/
noncomputable abbrev exampleIPRF : InvertiblePRF (Fin 3 → Fin 2) (Fin 3) (Fin 2) :=
  idealInvertiblePRF (Fin 3) (Fin 2)

example : exampleIPRF.IsCorrect := isCorrect_idealInvertiblePRF

example : exampleIPRF.IsCorrectOnGen := isCorrectOnGen_idealInvertiblePRF

/-- Composing `idealInvertiblePRF (Fin 3) (Fin 2)` with a keyed permutation family on `Fin 3`
yields a correct iPRF (Theorem 4.4 / Corollary 4.5). -/
noncomputable def examplePermIPRF :
    InvertiblePRF (Equiv.Perm (Fin 3) × (Fin 3 → Fin 2)) (Fin 3) (Fin 2) :=
  exampleIPRF.composePerm (ProbComp.uniform (Equiv.Perm (Fin 3))) id

example : examplePermIPRF.IsCorrect :=
  InvertiblePRF.isCorrect_composePerm (ProbComp.uniform (Equiv.Perm (Fin 3))) id
    isCorrect_idealInvertiblePRF

/-- For `idealInvertiblePRF (Fin 2) (Fin 2)`, any forward PRF adversary has advantage `0`. -/
example (A : Adversary (Fin 2) (Fin 2)) :
    (idealInvertiblePRF (Fin 2) (Fin 2)).forwardAdvantage A = 0 :=
  forwardAdvantage_idealInvertiblePRF_eq_zero A

/-! ### 2. Concrete 4-bit database (`c = 2` blocks × `w = 2` entries) -/

/-- Concrete 4-bit database on `Fin 2 × Fin 2`:
`db (0, 0) = true`, `db (0, 1) = false`, `db (1, 0) = true`, `db (1, 1) = true`. -/
def exampleDB : Fin 2 × Fin 2 → Bool
  | (0, 0) => true
  | (0, 1) => false
  | (1, 0) => true
  | (1, 1) => true

/-- Concrete iPRF keys for the two blocks (`nReg = 2`, `nBackup = 1`, total `3` slots). -/
def exampleKeys : Fin 2 → Fin 3 → Fin 2
  | 0, 0 => 0
  | 0, 1 => 1
  | 0, 2 => 0
  | 1, 0 => 1
  | 1, 1 => 0
  | 1, 2 => 1

/-- Regular block subsets of size `c / 2 + 1 = 2` (i.e. `Finset.univ : Finset (Fin 2)`). -/
def exampleRegBlocks : Fin 3 → Finset (Fin 2)
  | _ => Finset.univ

/-- Backup block subsets of size `c / 2 = 1` (`{0}`). -/
def exampleBackupBlocks : Fin 3 → Finset (Fin 2)
  | _ => {0}

/-- Offline preprocessing state for `exampleDB` with `nReg = 2` regular hints and `nBackup = 1`
backup hint. -/
noncomputable abbrev exampleState : PlinkoState 2 2 2 1 (Fin 3 → Fin 2) :=
  streamPreprocess exampleIPRF exampleDB exampleKeys exampleRegBlocks exampleBackupBlocks

/-- Single-pass entry streaming over `Finset.univ` produces `exampleState`. -/
example :
    (Finset.univ : Finset (Fin 2 × Fin 2)).toList.foldr
      (fun x st => streamEntry exampleIPRF x (exampleDB x) st)
      (initPlinkoState exampleKeys exampleRegBlocks exampleBackupBlocks) =
      exampleState :=
  foldr_streamEntry_univ (nReg := 2) (nBackup := 1) exampleDB exampleKeys
    exampleRegBlocks exampleBackupBlocks
    (fun α => isCorrectKey_idealInvertiblePRF (exampleKeys α))

/-- `exampleState` satisfies `PlinkoState.Valid exampleIPRF exampleDB`. -/
theorem exampleState_valid : exampleState.Valid exampleIPRF exampleDB :=
  PlinkoState.valid_streamPreprocess (nReg := 2) (nBackup := 1) exampleIPRF exampleDB exampleKeys
    exampleRegBlocks exampleBackupBlocks

/-- Slot `0` matches query `(0, 0)` and slot `1` matches query `(0, 1)`. -/
example : findHintSlotScan exampleIPRF exampleState (0, 0) = some 0 := by decide
example : findHintSlotScan exampleIPRF exampleState (0, 1) = some 1 := by decide

example : findHintSlot exampleIPRF exampleState (0, 0) = some 0 := by
  rw [findHintSlot_eq_findHintSlotScan _ _ (isCorrectKey_idealInvertiblePRF _)]
  decide

/-! ### 3. Online execution, backup promotion, and cache hits -/

/-- After answering `(0, 0)`, backup slot `2` is promoted into active hint slot `2` and `(0, 0)`
is cached with value `exampleDB (0, 0) = true`. -/
example : (exampleState.nextState exampleIPRF exampleDB (0, 0)).cache (0, 0) =
    some (true, 2) := by
  dsimp only [PlinkoState.nextState]
  rw [getHint_eq_getHintScan _ _ (isCorrectKey_idealInvertiblePRF _)]
  decide

theorem exampleState_canAnswer_00 : exampleState.CanAnswer exampleIPRF (0, 0) := by
  right
  rw [getHint_eq_getHintScan _ _ (isCorrectKey_idealInvertiblePRF _)]
  decide

/-- Single-step exact evaluation of `plinkoScheme` on `exampleState` and query `(0, 0)` outputs
`(exampleState.nextState exampleIPRF exampleDB (0, 0), exampleDB (0, 0))` with probability one. -/
example :
    ProbComp.eval ((plinkoScheme 2 2 2 1 exampleIPRF).step exampleDB exampleState (0, 0)) =
      PMF.pure (exampleState.nextState exampleIPRF exampleDB (0, 0), exampleDB (0, 0)) :=
  PlinkoState.eval_step_plinkoScheme exampleState_valid
    (isCorrectKey_idealInvertiblePRF _) exampleState_canAnswer_00

/-- Re-querying `(0, 0)` after it has been cached is answered directly from the cache, so the
2-query sequence `[(0, 0), (0, 0)]` satisfies `IsCorrectFrom`. -/
theorem exampleState_canAnswerSeq_00_00 :
    exampleState.CanAnswerSeq exampleIPRF exampleDB [(0, 0), (0, 0)] := by
  refine ⟨exampleState_canAnswer_00, ⟨Or.inl ?_, trivial⟩⟩
  dsimp only [PlinkoState.nextState]
  rw [getHint_eq_getHintScan _ _ (isCorrectKey_idealInvertiblePRF _)]
  decide

example :
    (plinkoScheme 2 2 2 1 exampleIPRF).IsCorrectFrom exampleDB exampleState [(0, 0), (0, 0)] :=
  (PlinkoState.isCorrectFrom_plinkoScheme exampleState_valid
    (fun α => isCorrectKey_idealInvertiblePRF (exampleState.keys α))
    exampleState_canAnswerSeq_00_00).1

/-! ### 4. Single-query and multi-query privacy tests -/

instance : Fact (Even 2) := ⟨⟨1, rfl⟩⟩

/-- Single-query exact privacy on `Fin 2 × Fin 2`: `buildQuery` on a conditioned regular hint has
the exact simulator distribution `plinkoSim 2 2`. -/
example (x : Fin 2 × Fin 2) :
    ProbComp.eval (do
      let P ← ProbComp.uniform (RegBlocksContaining 2 x.1)
      let o ← ProbComp.uniform (OffsetsContaining 2 2 x)
      let b ← ProbComp.uniform Bool
      let r ← ProbComp.uniform (Fin 2)
      pure (buildQuery x P.1 o.1 b r)) =
      ProbComp.eval (plinkoSim 2 2) :=
  eval_buildQuery_conditioned_eq_plinkoSim x

/-- Adaptive multi-query perfect privacy for `plinkoHybridScheme 2 2`. -/
example : (plinkoHybridScheme 2 2).IsPerfectlyPrivateWith (plinkoSim 2 2) :=
  isPerfectlyPrivateWith_plinkoHybridScheme

/-- Concrete adaptive server logging Plinko queries and maintaining a step counter. -/
def plinkoTranscriptServer : AdaptiveServer (Fin 2 × Fin 2) (PlinkoQuery 2 2) (Bool × Bool)
    (ℕ × List (PlinkoQuery 2 2)) where
  chooseQuery st := pure ((st.1 + 1, st.2), (0, 0))
  onQuery st q := pure ((st.1, q :: st.2), (decide (0 ∈ q.blocks), decide (q.offsets 0 = 0)))

example (db : Fin 2 × Fin 2 → Bool) :
    (plinkoHybridScheme 2 2).privacyAdvantage (plinkoSim 2 2) plinkoTranscriptServer
      (fun st => decide (st.2.length = 2)) db 2 (0, []) = 0 :=
  privacyAdvantage_plinkoHybridScheme_eq_zero plinkoTranscriptServer
    (fun st => decide (st.2.length = 2)) db 2 (0, [])

/-- Non-adaptive multi-query transcript privacy for `plinkoHybridScheme 2 2` on a 3-query
sequence. -/
example :
    ProbComp.eval
      ((plinkoHybridScheme 2 2).queryTranscript exampleDB [(0, 0), (1, 1), (0, 1)]) =
      ProbComp.eval (simTranscript (plinkoSim 2 2) 3) :=
  eval_queryTranscript_plinkoHybridScheme exampleDB [(0, 0), (1, 1), (0, 1)]

/-! ### 5. Database and hint updates (`UpdateDB` / `UpdateHint`) -/

/-- Updating entry `(0, 0)` of `exampleDB` to `false` via `updateDB` and `updateHint` preserves
`PlinkoState.Valid`. -/
example :
    (updateHint exampleIPRF (updateDB exampleDB (0, 0) false).1 exampleState).Valid
      exampleIPRF (updateDB exampleDB (0, 0) false).2 :=
  PlinkoState.valid_updateHint (0, 0) false exampleState_valid
    (isCorrectKey_idealInvertiblePRF (exampleState.keys 0))

/-- Batch updates via `updateState` preserve `PlinkoState.Valid` for `applyUpdates`. -/
example (updates : List ((Fin 2 × Fin 2) × Bool)) :
    (updateState exampleIPRF updates exampleState).Valid
      exampleIPRF (applyUpdates updates exampleDB) :=
  PlinkoState.valid_updateState updates exampleState_valid
    (fun α => isCorrectKey_idealInvertiblePRF (exampleState.keys α))

/--
info: 'Cslib.Crypto.Protocols.PIR.Preprocessing.Plinko.applyUpdates_nil' does not depend on any axioms
-/
#guard_msgs in
#print axioms applyUpdates_nil

end Cslib.Crypto.Protocols.PIR.Preprocessing.Plinko.Tests

end
