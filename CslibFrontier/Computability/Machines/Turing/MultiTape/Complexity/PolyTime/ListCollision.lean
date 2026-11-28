/-
Copyright (c) 2026 Samuel Schlesinger, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-!
# Polynomial-time collision checks on lists

A list of digest-message pairs contains a collision when two different messages share a digest.
The check scans pairs and compares their coordinates. Both coordinates may use arbitrary
readable encodings with lawful equality tests.
-/

public section

namespace Cslib

open Turing.MultiTapeTM

/-- Check whether two entries agree in their first (digest) coordinate and differ in their
second (message) coordinate. -/
@[expose] def hasDistinctCollision {Y M : Type} [BEq Y] [BEq M] (seen : List (Y × M)) : Bool :=
  seen.any fun p => seen.any fun q => (p.1 == q.1) && (p.2 != q.2)

/-- Testing the two coordinates of every pair of entries is polynomial-time. -/
theorem polyTime_hasDistinctCollision {Y M : Type} [BEq Y] [LawfulBEq Y] [BEq M] [LawfulBEq M]
    (encY : Y ↪ List Bool) (encM : M ↪ List Bool) :
    ComputableInPolyTime hasDistinctCollision (encList (encPair encY encM)) encBool := by
  let item := encPair encY encM
  let items := encList item
  unfold hasDistinctCollision
  apply ComputableInPolyTime.anyWithInput (encA := item) ComputableInPolyTime.id'
  apply ComputableInPolyTime.anyWithInput (encA := item) (ComputableInPolyTime.fst items item)
  have hp := (ComputableInPolyTime.snd items item).comp
    (ComputableInPolyTime.fst (encPair items item) item)
  have hq := ComputableInPolyTime.snd (encPair items item) item
  have heq := ((ComputableInPolyTime.fst encY encM).comp hp).beq
    ((ComputableInPolyTime.fst encY encM).comp hq)
  have hne := ComputableInPolyTime.bne ((ComputableInPolyTime.snd encY encM).comp hp)
    ((ComputableInPolyTime.snd encY encM).comp hq)
  exact ComputableInPolyTime.bool_and.comp (heq.prod hne)

end Cslib
