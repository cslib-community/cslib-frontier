/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, Samuel Schlesinger
-/

module
-- upstream: local-only

public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Uni.Exist
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Uni.LenU

/-! Tests of the binary-encoding, pointer-machine, and universal-program layer (M1, part 3/3):
`binaryWord` / `binaryValue_succ_carry` / `exists_carry_cut` / `carry_cut_unique`, concrete pointer
machine `Mach` with `Closed`, `Seq`/`GV` positive and negative checks, `exists_MX` lifting,
`MX.total` length evaluation, and `Mach.SumTo`. -/

namespace CslibFrontierTests.TapeUni

open Cslib.BitString (binaryValue binaryValue_succ_carry binaryWord exists_carry_cut)
open Cslib.Circuits.Arithmetic.Separation.Uni

/-! ### Big-endian binary words and carry cuts -/

/-- Check big-endian encoding of `5` in 4 bits. -/
public theorem binaryWord_4_5 : binaryWord 4 5 = [false, true, false, true] := by decide

example : binaryValue [false, true, true] + 1 = binaryValue [true, false, false] :=
  (binaryValue_succ_carry [] 2).symm

example : ∃ u k, [true, false, true] = u ++ false :: List.replicate k true :=
  exists_carry_cut (w := [true, false, true]) (by decide)

/-- Maximal all-`true` word `[true, true]` admits no `false :: true^k` decomposition (negative). -/
example : ¬ ∃ u k, [true, true] = u ++ false :: List.replicate k true := by
  rintro ⟨u, k, h⟩
  have hmem : false ∈ [true, true] := by rw [h]; simp
  simp at hmem

/-! ### Minimal pointer machine with one step `false → true` -/

private noncomputable def oneStepMach : Mach ℤ Bool Unit where
  Rl := Unit
  src := fun _ => false
  dst := fun _ => true
  rd := fun _ => none
  lk := fun _ => ()
  la := fun _ => 0
  ak := fun _ => ()
  af := fun _ _ => 0
  dr := fun _ _ => 0
  wt := fun _ => 3
  m0 := false
  mh := true
  kN := ()

private noncomputable def oneStep : oneStepMach.Step :=
  ((), fun i => if i = 8 then 1 else 0)

/-- Firing `oneStep` from `σi oneStepMach []` produces a valid sequential and global trace. -/
private theorem oneStep_gv : Mach.GV (σi oneStepMach []) [oneStep] := by
  rw [Mach.gv_iff (closed_σi oneStepMach [])]
  refine ⟨⟨rfl, ?_, rfl, ?_, by simp [oneStepMach, σi]⟩, rfl, rfl⟩
  · intro i
    fin_cases i <;> rfl
  · have hld : Mach.ld oneStep = ((), ![0, 0, 0, 0]) := by
      refine Prod.ext rfl (funext fun j => ?_)
      fin_cases j <;> rfl
    simp [σi, hld]

/-- An empty trace is rejected from `σi oneStepMach []` because `m0 = false ≠ true = mh`. -/
example : ¬ Mach.GV (P := oneStepMach) (σi oneStepMach []) [] := by
  rw [Mach.gv_iff (closed_σi oneStepMach [])]
  rintro ⟨h, _⟩
  exact Bool.false_ne_true h

/-- `exists_MX` lifts `[oneStep]` to a matched `XP` run whose total tape length equals `tU`. -/
example : ∃ x : XP oneStepMach,
    MX x [] ∧ x.steps.map nst = [oneStep] ∧
      ∑ s, (emX oneStepMach x (.tp s true)).length =
        tU (Fintype.card (Bl Unit)) 1 2 := by
  obtain ⟨x, hx, hmap⟩ := exists_MX oneStep_gv (by
    intro st hst i
    simp only [List.mem_singleton] at hst
    subst hst
    dsimp [oneStep]
    split_ifs <;> omega)
  have hsteps : x.steps.length = 1 := by
    have h := congrArg List.length hmap
    simpa using h
  have hsz : x.init.length + 1 = 2 := by
    have h := hx.size_eq
    rw [hsteps] at h
    have h2 : Nat.size (1 + 1) = 2 := by decide
    exact h.symm.trans h2
  refine ⟨x, hx, hmap, ?_⟩
  rw [hx.total, hsteps, hsz]

/-- Weight sum check via `SumTo.halt`: a halting state with no outgoing rules sums to `1`. -/
example : Mach.SumTo oneStepMach ⟨true, fun _ => 0, [], 0, []⟩ 1 0 :=
  Mach.SumTo.halt rfl rfl fun _ h => by cases h

end CslibFrontierTests.TapeUni
