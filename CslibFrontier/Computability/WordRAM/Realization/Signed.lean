/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Realization.Basic
public import CslibFrontier.Computability.WordRAM.Realization.Structure
public import CslibFrontier.Computability.WordRAM.Signed.Encoding
import CslibFrontier.Tactic.Realize

/-!
# Signed-integer `Memory.Prog` primitives over `Signed.encode`

This module provides pure-register `Memory.Prog` negation, addition, subtraction, and strict
order comparison over `Cslib.WordRAM.Signed.encode` (`2 * |z| + signBit`), together with their
`Realizes .exact`, `ValidHistory`, `memoryCost`, and `clientResult` certificates.

## Main definitions

* `Cslib.WordRAM.Realization.Signed.signedNegProg`: negation of a `Signed.encode` word.
* `Cslib.WordRAM.Realization.Signed.signedAddProg`: addition of two `Signed.encode` words.
* `Cslib.WordRAM.Realization.Signed.signedSubProg`: subtraction of two `Signed.encode` words.
* `Cslib.WordRAM.Realization.Signed.SignedLtWord`: strict `<` predicate on `Signed.encode` words.

## Main results

* `Cslib.WordRAM.Realization.Signed.signedNegProg_realizes`,
  `Cslib.WordRAM.Realization.Signed.clientResult_signedNegProg`: realization and correctness of
  signed negation.
* `Cslib.WordRAM.Realization.Signed.signedAddProg_realizes`,
  `Cslib.WordRAM.Realization.Signed.clientResult_signedAddProg`: realization and correctness of
  signed addition.
* `Cslib.WordRAM.Realization.Signed.signedSubProg_realizes`,
  `Cslib.WordRAM.Realization.Signed.clientResult_signedSubProg`: realization and correctness of
  signed subtraction.
* `Cslib.WordRAM.Realization.Signed.signedLtWord_iff`: equivalence between `SignedLtWord` and `<`
  on `ℤ`.
-/

namespace Cslib.WordRAM.Realization.Signed

open Cslib.DataStructure
open Cslib.WordRAM
open Cslib.WordRAM.Realization

private def signedValue (m s : ℕ) : ℤ := if s = 0 then m else -(m : ℤ)

private def packed (m s : ℕ) : ℕ := if m = 0 then 0 else 2 * m + s

private theorem encode_signedValue {m s : ℕ} (hs : s ≤ 1) :
    Cslib.WordRAM.Signed.encode (signedValue m s) = packed m s := by
  unfold signedValue packed Cslib.WordRAM.Signed.encode
  split_ifs <;> omega

private theorem pure_packed (m s : ℕ) :
    (if m = 0 then (pure 0 : Memory.Prog ℕ) else pure (2 * m + s)) = pure (packed m s) := by
  unfold packed; split_ifs <;> rfl

private theorem signedValue_encode (z : ℤ) :
    signedValue z.natAbs (if z < 0 then 1 else 0) = z := by
  by_cases hz : z < 0
  · simp [signedValue, hz, Int.ofNat_natAbs_of_nonpos (by omega : z ≤ 0)]
  · simp [signedValue, hz, ← Int.eq_natAbs_of_nonneg (by omega : 0 ≤ z)]

public section

/-- Negate a `Signed.encode`-packed integer in `Memory.Prog ℕ` without memory accesses. -/
@[expose] def signedNegProg (u : ℕ) : Memory.Prog ℕ :=
  if u = 0 then pure 0
  else if u % 2 = 0 then pure (u + 1)
  else pure (u - 1)

/-- Add two `Signed.encode`-packed integers in `Memory.Prog ℕ` without memory accesses. -/
@[expose] def signedAddProg (d : ℕ × ℕ) : Memory.Prog ℕ :=
  let u := Prod.fst d
  let v := Prod.snd d
  if u % 2 = v % 2 then
    if u / 2 + v / 2 = 0 then pure 0
    else pure (2 * (u / 2 + v / 2) + u % 2)
  else if u / 2 < v / 2 then
    if v / 2 - u / 2 = 0 then pure 0
    else pure (2 * (v / 2 - u / 2) + v % 2)
  else
    if u / 2 - v / 2 = 0 then pure 0
    else pure (2 * (u / 2 - v / 2) + u % 2)

/-- Subtract two `Signed.encode`-packed integers (`d.1 - d.2`) in `Memory.Prog ℕ`. -/
@[expose] def signedSubProg (d : ℕ × ℕ) : Memory.Prog ℕ := do
  let nb ← signedNegProg (Prod.snd d)
  signedAddProg (Prod.fst d, nb)

/-- Strict integer `<` predicate directly on `Signed.encode`-packed words. -/
abbrev SignedLtWord (u v : ℕ) : Prop :=
  (u % 2 = v % 2 ∧ ((u % 2 = 0 ∧ u < v) ∨ (u % 2 ≠ 0 ∧ v < u))) ∨ (u % 2 = 1 ∧ v % 2 = 0)

theorem clientState_signedNegProg {w : ℕ}
    (s : Memory.State) (u : ℕ) :
    (Memory.spec w).clientState s (signedNegProg u) = s := by
  unfold signedNegProg
  split_ifs <;> rfl

theorem validHistory_signedNegProg (w : ℕ) (s : Memory.State) (u : ℕ) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (signedNegProg u)) := by
  unfold signedNegProg
  split_ifs <;> trivial

@[simp, client_simps] theorem memoryCost_signedNegProg (u : ℕ) (s : Memory.State) :
    memoryCost (signedNegProg u) s = 0 := by
  unfold signedNegProg
  split_ifs <;> rfl

theorem clientResult_signedNegProg (s : Memory.State) (z : ℤ) :
    (Memory.spec 0).clientResult s (signedNegProg (Cslib.WordRAM.Signed.encode z)) =
      Cslib.WordRAM.Signed.encode (-z) := by
  have hz := (signedValue_encode z).symm
  set m := z.natAbs
  set sg := if z < 0 then 1 else 0
  have hsg : sg ≤ 1 := by dsimp [sg]; split_ifs <;> omega
  rw [hz, encode_signedValue hsg, show -signedValue m sg = signedValue m (1 - sg) by
    dsimp only [signedValue]; split_ifs <;> omega, encode_signedValue (by omega : 1 - sg ≤ 1)]
  unfold signedNegProg packed
  split_ifs <;> simp only [client_simps] <;> omega

theorem signedNegProg_realizes :
    Realizes .exact signedNegProg wordWords wordWords
      (fun w u _ => Fits w 2 ∧ Fits w (u + 1)) (fun _ _ => 0) := by
  unfold signedNegProg
  realize
  all_goals first | omega | exact h.1 | exact h.2.of_le (by omega)

theorem clientState_signedAddProg {w : ℕ}
    (s : Memory.State) (d : ℕ × ℕ) :
    (Memory.spec w).clientState s (signedAddProg d) = s := by
  unfold signedAddProg
  dsimp only
  split_ifs <;> rfl

theorem validHistory_signedAddProg (w : ℕ) (s : Memory.State) (d : ℕ × ℕ) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (signedAddProg d)) := by
  unfold signedAddProg
  dsimp only
  split_ifs <;> trivial

@[simp, client_simps] theorem memoryCost_signedAddProg (d : ℕ × ℕ) (s : Memory.State) :
    memoryCost (signedAddProg d) s = 0 := by
  unfold signedAddProg
  dsimp only
  split_ifs <;> rfl

theorem clientResult_signedAddProg (s : Memory.State) (a b : ℤ) :
    (Memory.spec 0).clientResult s
        (signedAddProg (Cslib.WordRAM.Signed.encode a, Cslib.WordRAM.Signed.encode b)) =
      Cslib.WordRAM.Signed.encode (a + b) := by
  have ha := (signedValue_encode a).symm
  have hb := (signedValue_encode b).symm
  unfold signedAddProg
  dsimp only
  simp only [Cslib.WordRAM.Signed.encode_div_two, Cslib.WordRAM.Signed.encode_mod_two,
    pure_packed]
  set m₁ := a.natAbs
  set s₁ := if a < 0 then 1 else 0
  set m₂ := b.natAbs
  set s₂ := if b < 0 then 1 else 0
  have hs₁ : s₁ ≤ 1 := by dsimp [s₁]; split_ifs <;> omega
  have hs₂ : s₂ ≤ 1 := by dsimp [s₂]; split_ifs <;> omega
  split_ifs <;>
    simp only [client_simps, ← encode_signedValue hs₁, ← encode_signedValue hs₂, ha, hb] <;>
    congr 1 <;> simp only [signedValue] <;> split_ifs <;> omega

theorem signedAddProg_realizes :
    Realizes .exact signedAddProg (appendWords wordWords wordWords) wordWords
      (fun w d _ => Fits w 2 ∧ Fits w (2 * (Prod.fst d / 2 + Prod.snd d / 2) + 1))
      (fun _ _ => 0) := by
  unfold signedAddProg
  realize
  all_goals first | omega | exact h.1 | exact h.2.of_le (by omega)

theorem clientState_signedSubProg {w : ℕ}
    (s : Memory.State) (d : ℕ × ℕ) :
    (Memory.spec w).clientState s (signedSubProg d) = s := by
  unfold signedSubProg
  rw [StateTransitionSpec.clientState_bind, clientState_signedNegProg, clientState_signedAddProg]

theorem clientResult_signedSubProg (s : Memory.State) (a b : ℤ) :
    (Memory.spec 0).clientResult s
        (signedSubProg (Cslib.WordRAM.Signed.encode a, Cslib.WordRAM.Signed.encode b)) =
      Cslib.WordRAM.Signed.encode (a - b) := by
  unfold signedSubProg
  rw [StateTransitionSpec.clientResult_bind, clientState_signedNegProg,
    clientResult_signedNegProg, clientResult_signedAddProg]
  rfl

theorem runClient_signedSubProg (w : ℕ) (s : Memory.State) (a b : ℤ) :
    (Memory.spec w).runClient s
        (signedSubProg (Cslib.WordRAM.Signed.encode a, Cslib.WordRAM.Signed.encode b)) =
      (Cslib.WordRAM.Signed.encode (a - b), s, []) := by
  refine Prod.ext ((clientResult_width w _ s).trans (clientResult_signedSubProg s a b))
    (Prod.ext (clientState_signedSubProg s _) ?_)
  change (Memory.spec w).clientHistory s _ = []
  unfold signedSubProg signedAddProg
  rw [StateTransitionSpec.clientHistory_bind, show (Memory.spec w).clientHistory s
    (signedNegProg (Cslib.WordRAM.Signed.encode b)) = [] by unfold signedNegProg; split_ifs <;> rfl]
  dsimp only; split_ifs <;> rfl

theorem validHistory_signedSubProg (w : ℕ) (s : Memory.State) (d : ℕ × ℕ) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (signedSubProg d)) := by
  unfold signedSubProg
  rw [validHistory_bind']
  exact ⟨validHistory_signedNegProg w s d.2,
    by rw [clientState_signedNegProg]; exact validHistory_signedAddProg w s _⟩

@[simp, client_simps] theorem memoryCost_signedSubProg (d : ℕ × ℕ) (s : Memory.State) :
    memoryCost (signedSubProg d) s = 0 := by
  unfold signedSubProg
  rw [memoryCost_bind', memoryCost_signedNegProg, clientState_signedNegProg,
    memoryCost_signedAddProg]

theorem signedSubProg_realizes :
    Realizes .exact signedSubProg (appendWords wordWords wordWords) wordWords
      (fun w d _ =>
        Fits w 2 ∧ Fits w (Prod.snd d + 1) ∧
          Fits w (2 * (Prod.fst d / 2 + Prod.snd d / 2) + 1))
      (fun _ _ => 0) := by
  unfold signedSubProg
  realize [signedNegProg_realizes, signedAddProg_realizes]
  · exact h.1
  · exact h.2.1
  · refine h.2.2.of_le ?_
    have hdiv : (Memory.spec 0).clientResult s (signedNegProg d.2) / 2 = d.2 / 2 := by
      unfold signedNegProg
      split_ifs <;> simp only [client_simps] <;> omega
    rw [hdiv]

theorem signedLtWord_iff (a b : ℤ) :
    SignedLtWord (Cslib.WordRAM.Signed.encode a) (Cslib.WordRAM.Signed.encode b) ↔ a < b := by
  unfold SignedLtWord
  simp only [Cslib.WordRAM.Signed.encode_mod_two]
  by_cases ha : a < 0 <;> by_cases hb : b < 0 <;>
    simp [ha, hb, Cslib.WordRAM.Signed.encode] <;> omega

end

end Cslib.WordRAM.Realization.Signed
