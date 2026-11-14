/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Protocols.BCS.Basic

/-!
# Tests for the BCS transform (`CslibFrontier.Crypto.Protocols.BCS.Basic`)

Exercises a concrete two-round (`r = 2`), depth-one (`d = 1`) public-coin IOP and its BCS transform:
1. Perfect completeness of `toyIOP` and `bcsVerify_bcsProve_eq_true`.
2. Concrete evaluation of `bcsProve` and `bcsVerify` on a valid statement-witness pair.
3. Concrete collision extraction via `bcsExtractTableCollision` and `bcs_sound_or_merkleCollision`
   when a cheating proof opens a committed leaf to the opposite bit under a colliding hash.
4. Straight-line knowledge extraction via `bcs_knowledge_or_merkleCollision`.
-/

namespace CslibFrontierTests.Crypto.BCSTransform

open Cslib.Crypto Cslib.Crypto.Protocols.BCS

/-- Encode a single-bit oracle symbol as a one-bit leaf. -/
def encSym (b : Bool) : List Bool := [b]

theorem encSym_injective : Function.Injective encSym := by
  intro a b h
  simpa [encSym] using h

/-- A constant-digest hash used to exercise collision extraction on conflicting Merkle openings. -/
def constHash (k _ : List Bool) : List Bool := k

/-- A toy Fiat–Shamir oracle returning whether the number of roots seen so far is odd. -/
def toyFS (_ : Bool) (roots : List (List Bool)) : Bool :=
  roots.length % 2 == 1

/-- Witness relation for `toyIOP`: the witness bit equals the statement bit. -/
def toyRel (x w : Bool) : Prop := x = w

instance (x w : Bool) : Decidable (toyRel x w) :=
  inferInstanceAs (Decidable (x = w))

/-- A concrete 2-round, depth-1 public-coin IOP:
* In round `0`, the honest prover writes `w` to both entries of the table.
* In round `1`, given challenge `c₀`, the honest prover writes `xor w c₀` to both entries.
* The verifier queries one entry from round `0` (selected by `c₀`) and one entry from round `1`
  (selected by `c₁`), and checks that the two answers equal `x` and `xor x c₀`. -/
def toyIOP : PublicCoinIOP 2 1 Bool Bool Bool Bool where
  proveRound j _ w prevChals :=
    if h : j.val = 0 then
      fun _ => w
    else
      have h0 : 0 < j.val := Nat.pos_of_ne_zero h
      fun _ => xor w (prevChals ⟨0, h0⟩)
  queries _ chals :=
    [(⟨0, by decide⟩, if chals ⟨0, by decide⟩ then ⟨1, by decide⟩ else ⟨0, by decide⟩),
     (⟨1, by decide⟩, if chals ⟨1, by decide⟩ then ⟨1, by decide⟩ else ⟨0, by decide⟩)]
  decide x chals answers :=
    answers == [x, xor x (chals ⟨0, by decide⟩)]

/-- `toyIOP` is perfectly complete for `toyRel`. -/
theorem toyIOP_complete : IOPCompleteness toyIOP toyRel := by
  intro x w hrel chals
  subst hrel
  simp [iopVerify, iopAnswers, iopProverOracles, prefixChallenges, toyIOP]

/-- Round-by-round doomed predicate for `toyIOP`: either no rounds have elapsed yet, or the first
round's oracle table disagrees with `x` at the position selected by `c₀`. -/
def toyDoomed (x : Bool) (tr : List (OracleTable 1 Bool × Bool)) : Prop :=
  match tr with
  | [] => True
  | (π₀, c₀) :: _ => π₀ (if c₀ then 1 else 0) ≠ x

/-- Round-by-round good-step relation for `toyIOP`: in round `0` (`tr = []`), challenge `c` selects
an entry of `π` that disagrees with `x`; later rounds preserve the round-`0` disagreement. -/
def toyGoodStep (x : Bool) (tr : List (OracleTable 1 Bool × Bool))
    (π : OracleTable 1 Bool) (c : Bool) : Prop :=
  tr = [] → π (if c then 1 else 0) ≠ x

/-- `toyIOP` satisfies `IOPRoundByRoundSoundness` with `toyDoomed` and `toyGoodStep`. -/
theorem toyIOP_rbrSound :
    IOPRoundByRoundSoundness toyIOP {false} toyDoomed toyGoodStep where
  init_doomed _ _ := trivial
  step_doomed x tr π c hdoomed hgood := by
    cases tr with
    | nil => exact hgood rfl
    | cons hd tl => exact hdoomed
  reject_of_doomed x oracles chals hdoomed := by
    change oracles 0 (if chals 0 then 1 else 0) ≠ x at hdoomed
    simp only [iopVerify, iopAnswers, toyIOP, List.map_cons, List.map_nil, beq_eq_false_iff_ne,
      ne_eq, List.cons.injEq]
    exact fun h => hdoomed h.1

-- Round-by-round soundness applied to `toyIOP`: when `x = true ∉ {false}` and the round-0 oracle
-- table is constant `false`, every challenge vector is rejected via `iopVerify_eq_false`.
example (chals : Fin 2 → Bool) :
    let oracles := bcsHonestTables toyIOP constHash [false, true] encSym toyFS true false
    iopVerify toyIOP true chals oracles = false := by
  intro oracles
  refine toyIOP_rbrSound.iopVerify_eq_false (by simp) oracles chals ?_
  intro ⟨j, hj⟩
  rcases j with _ | j
  · intro _
    decide +revert
  · intro hnil
    nomatch hnil

/-- Straight-line knowledge extractor for `toyIOP`: read entry `0` of the round-`0` oracle table. -/
def toyExtract (_ : Bool) (oracles : Fin 2 → OracleTable 1 Bool) : Bool :=
  oracles ⟨0, by decide⟩ ⟨0, by decide⟩

-- 1. Perfect completeness applied to `toyIOP`.
example (H : List Bool → List Bool → List Bool) (k : List Bool)
    (hFS : Bool → List (List Bool) → Bool) (x : Bool) :
    bcsVerify toyIOP H k encSym hFS x (bcsProve toyIOP H k encSym hFS x x) = true :=
  bcsVerify_bcsProve_eq_true toyIOP_complete H k encSym hFS rfl

-- 2. Concrete evaluation of `bcsProve` and `bcsVerify`.
example :
    bcsVerify toyIOP constHash [false, true] encSym toyFS true
      (bcsProve toyIOP constHash [false, true] encSym toyFS true true) = true := by
  decide

-- 3. Concrete collision extraction when a cheating proof opens a committed table inconsistently.
/-- A cheating proof for statement `true` that commits to the `w = false` tables under `constHash`
but claims the round-`0` and round-`1` answers for `w = true`. -/
def forgedProof : BCSProof 2 Bool where
  roots := bcsHonestRoots toyIOP constHash [false, true] encSym toyFS true false
  openings :=
    let tables := bcsHonestTables toyIOP constHash [false, true] encSym toyFS true false
    let chals := bcsHonestChallenges toyIOP constHash [false, true] encSym toyFS true false
    [⟨true, merklePath constHash [false, true] (oracleLeaves encSym 1 (tables ⟨0, by decide⟩))
        (if chals ⟨0, by decide⟩ then 1 else 0)⟩,
     ⟨xor true (chals ⟨0, by decide⟩),
        merklePath constHash [false, true] (oracleLeaves encSym 1 (tables ⟨1, by decide⟩))
          (if chals ⟨1, by decide⟩ then 1 else 0)⟩]

-- Under `constHash`, the forged proof passes `bcsVerify` for `x = true`, while `iopVerify` rejects
-- the committed `w = false` tables, so `bcsExtractTableCollision` extracts an explicit collision.
example :
    bcsVerify toyIOP constHash [false, true] encSym toyFS true forgedProof = true := by
  decide

example :
    let oracles := bcsHonestTables toyIOP constHash [false, true] encSym toyFS true false
    iopVerify toyIOP true (bcsChallenge toyFS true forgedProof.roots) oracles = false := by
  decide

example :
    let oracles := bcsHonestTables toyIOP constHash [false, true] encSym toyFS true false
    let col := bcsExtractTableCollision toyIOP constHash [false, true] encSym toyFS true
      oracles forgedProof
    isCollision constHash (fun _ _ => true) 2 [false, true] col.1 col.2 = true :=
  isCollision_of_bcsVerify_of_iopVerify_eq_false encSym_injective (fun _ => rfl) (by decide)
    (by decide) 2

-- 4. Concrete knowledge extraction on the honest tables and via `bcs_knowledge_or_merkleCollision`.
example :
    let oracles := bcsHonestTables toyIOP constHash [false, true] encSym toyFS true true
    toyRel true (toyExtract true oracles) := by
  decide

example :
    let oracles := bcsHonestTables toyIOP constHash [false, true] encSym toyFS true false
    toyRel true (toyExtract true oracles) ∨
      let col := bcsExtractTableCollision toyIOP constHash [false, true] encSym toyFS true
        oracles forgedProof
      isCollision constHash (fun _ _ => true) 2 [false, true] col.1 col.2 = true :=
  bcs_knowledge_or_merkleCollision encSym_injective (fun _ => rfl) (by decide)
    (fun h => by revert h; decide) 2

/-! ### Polynomial-time collision extraction and standard-model `CollisionResistant` reductions -/

open Cslib Cslib.Probability Turing.MultiTapeTM

/-- Constant Fiat–Shamir oracle used to exercise uniform polynomial-time reductions. -/
def constFS (_ : Bool) (_ : List (List Bool)) : Bool := false

/-- Single-round, depth-one IOP querying entry `0` of round `0` and checking equality with `x`. -/
def ksIOP : PublicCoinIOP 1 1 Bool Bool Bool Bool where
  proveRound _ _ w _ := fun _ => w
  queries _ _ := [(⟨0, by decide⟩, ⟨0, by decide⟩)]
  decide x _ answers := answers == [x]

/-- Straight-line knowledge extractor for `ksIOP` reading entry `0` of round `0`. -/
def ksExtract (_ : Bool) (oracles : Fin 1 → OracleTable 1 Bool) : Bool :=
  oracles ⟨0, by decide⟩ ⟨0, by decide⟩

theorem ksIOP_knowledgeSound : IOPKnowledgeSoundness ksIOP toyRel ksExtract := by
  intro x chals oracles hver
  simp only [iopVerify, iopAnswers, ksIOP, List.map_cons, List.map_nil, beq_iff_eq,
    List.cons.injEq, and_true] at hver
  exact hver.symm

theorem computableInPolyTime_constHash :
    ComputableInPolyTime (fun p : List Bool × List Bool => constHash p.1 p.2)
      (encPair encBits encBits) encBits :=
  ComputableInPolyTime.fst encBits encBits

theorem computableInPolyTime_ksIOP_queries :
    ComputableInPolyTime (fun p : Bool × (Fin 1 → Bool) => ksIOP.queries p.1 p.2)
      (encPair encBool (encFinFn 1 encBool)) (encList (encPair encFinUnary encFinUnary)) :=
  ComputableInPolyTime.const _

theorem computableInPolyTime_constFS :
    ComputableInPolyTime (fun p : Bool × List (List Bool) => constFS p.1 p.2)
      (encPair encBool (encList encBits)) encBool :=
  ComputableInPolyTime.const false

/-- Concrete strict-PPT table-committing BCS adversary. -/
def toyTableAdversary : BCSTableCommitAdversary 1 1 Bool Bool :=
  fun _ _ => pure
    { stmt := true
      oracles := fun _ _ => false
      proof := { roots := fun _ => [], openings := [⟨true, [[]]⟩] } }

theorem isPPTOn_toyTableAdversary :
    IsPPTOn (encPair encUnary encBits) (encBCSTableCommitOutput 1 1 Bool Bool encBool encBool)
      (fun ⟨n, k⟩ => toyTableAdversary n k) :=
  (ComputableInPolyTime.const _).tidy.isPPTOn

-- 5. Poly-time certificate for `bcsExtractTableCollision` and `isPPT_bcsTableCollisionFinder`.
example :
    ComputableInPolyTime
      (fun p : List Bool × BCSTableCommitOutput 1 1 Bool Bool =>
        bcsExtractTableCollision ksIOP constHash p.1 (fun b => encBool b) constFS
          p.2.stmt p.2.oracles p.2.proof)
      (encPair encBits (encBCSTableCommitOutput 1 1 Bool Bool encBool encBool))
      (encPair encBits encBits) :=
  computableInPolyTime_bcsExtractTableCollision computableInPolyTime_constHash (fun _ _ => rfl)
    computableInPolyTime_ksIOP_queries computableInPolyTime_constFS
    (ComputableInPolyTime.fst encBits _)
    ((encBCSTableCommitOutput_stmt_polyTime 1 1 Bool Bool encBool encBool
      (ComputableInPolyTime.snd encBits _)))
    ((encBCSTableCommitOutput_oracles_polyTime 1 1 Bool Bool encBool encBool
      (ComputableInPolyTime.snd encBits _)))
    ((encBCSTableCommitOutput_proof_polyTime 1 1 Bool Bool encBool encBool
      (ComputableInPolyTime.snd encBits _)))

example :
    IsPPT (encPair encBits encBits)
      (bcsTableCollisionFinder ksIOP constHash (fun b => encBool b) constFS toyTableAdversary) :=
  isPPT_bcsTableCollisionFinder computableInPolyTime_constHash (fun _ _ => rfl)
    computableInPolyTime_ksIOP_queries computableInPolyTime_constFS isPPTOn_toyTableAdversary

-- 6. Standard-model reductions from BCS table binding and knowledge soundness to
-- `CollisionResistant`.
example (hCR : CollisionResistant constHash) :
    Negligible (fun n => Game.succProbability (ProbComp.eval
      (bcsTableBindingGame ksIOP constHash (fun b => encBool b) constFS toyTableAdversary n))) :=
  CollisionResistant.bcsTableBinding_negligible hCR computableInPolyTime_constHash (fun _ _ => rfl)
    computableInPolyTime_ksIOP_queries computableInPolyTime_constFS isPPTOn_toyTableAdversary

example (hCR : CollisionResistant constHash) :
    Negligible (fun n => Game.succProbability (ProbComp.eval
      (bcsTableKnowledgeGame ksIOP toyRel ksExtract constHash (fun b => encBool b) constFS
        toyTableAdversary n))) :=
  CollisionResistant.bcsTableKnowledge_negligible ksIOP_knowledgeSound hCR
    computableInPolyTime_constHash (fun _ _ => rfl) computableInPolyTime_ksIOP_queries
    computableInPolyTime_constFS isPPTOn_toyTableAdversary

end CslibFrontierTests.Crypto.BCSTransform
