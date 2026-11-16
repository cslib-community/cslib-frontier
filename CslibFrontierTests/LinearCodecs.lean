/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: local-only (ordinary-import regression client)

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.DegreeClosure
import Lean.Elab.Command

/-! A total framed-packet repair client with a linear, rather than merely polynomial, contract.
The parser can see empty and incomplete frames; a valid packet retains its payload and suffix.
-/

-- This ordinary-import regression intentionally keeps its helper declarations private.
set_option linter.privateModule false

open Turing.MultiTapeTM

run_cmd do
  let env ← Lean.getEnv
  for n in [`Turing.MultiTapeTM.ComputableTidilyInLinearTimeAndSpace,
      `Turing.MultiTapeTM.ComputableTidilyInDegree,
      `Turing.MultiTapeTM.ComputableTidilyInPolyTime,
      `Turing.MultiTapeTM.ComputableTidilyInO] do
    if env.contains n then throwError "higher tidy calculus in the plain codec entry point: {n}"

private def repairPacket (w : List Bool) : List Bool := frame (unframe w) ++ dropFrame w

private theorem repairPacket_degree :
    ComputableInDegree repairPacket encBits encBits 1 1 := by
  have hf : ComputableInDegree frame encBits encBits 1 1 := .of_frame fun _ => rfl
  have hu : ComputableInDegree unframe encBits encBits 1 1 := .of_unframe fun _ => rfl
  have hd : ComputableInDegree dropFrame encBits encBits 1 1 := .of_dropFrame fun _ => rfl
  exact (hf.comp hu).append hd fun _ => rfl

example :
    (∃ c, ComputableInTimeAndSpace repairPacket encBits encBits
      (fun w => c * (w.length + 1)) (fun w => c * (w.length + 1))) ∧
    (∀ u v, repairPacket (frame u ++ v) = frame u ++ v) ∧
    repairPacket [] = [false] ∧ repairPacket [true] = [false] ∧
    repairPacket [false, true] = [false, true] := by
  refine ⟨ComputableInDegree.one_one_iff.mp repairPacket_degree, ?_, rfl, rfl, rfl⟩
  intro u v
  simp only [repairPacket, unframe_frame_append, dropFrame_frame_append]
