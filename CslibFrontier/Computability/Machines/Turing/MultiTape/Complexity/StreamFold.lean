/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

import Cslib.Computability.Machines.Turing.MultiTape.Combinators.AlmostConstant
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Streaming
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NormalForm
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.StreamFold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.Tidy.Basic

/-!
# Streaming fold combinator for paired framed lists

Provides `Turing.MultiTapeTM.ComputableInTimeAndSpace.streamFold_pair_list`, a quantitative
single-pass streaming fold wrapper over `(init x, elems x)` with polynomial-time callbacks and a
uniform encoded state/element size bound. Placed in its own module rather than
`Complexity.Streaming` to avoid triggering rebuilds across unrelated importers of `Streaming`.
-/

namespace Turing.MultiTapeTM

open Encodings Internal.NativeCompiler

public section

/-- Single-pass streaming fold over a framed pair-encoded list `(init x, elems x)` with
polynomial-time step/emit callbacks and uniform encoded state/element size bound `lMax x`. -/
theorem ComputableInTimeAndSpace.streamFold_pair_list {α σ β γ : Type}
    {encA : α ↪ List Bool} {encS : σ ↪ List Bool} {encB : β ↪ List Bool}
    {encIn : γ ↪ List Bool}
    (init : γ → σ) (elems : γ → List α)
    (hL : ∀ x, encIn x = encPair encS (encList encA) (init x, elems x))
    {next : σ × α → σ} {emit : σ × α → List β} {g : γ → List β}
    (hnext : ComputableInPolyTime next (encPair encS encA) encS)
    (hemit : ComputableInPolyTime emit (encPair encS encA) (encList encB))
    (hg : ∀ x, encList encB (g x) =
      streamEmit next (fun p => encList encB (emit p)) (init x) (elems x))
    {lMax : γ → ℕ}
    (hS : ∀ x j, j ≤ (elems x).length →
      (encS (streamState (init x) next (elems x) j)).length ≤ lMax x)
    (hA : ∀ x j (hj : j < (elems x).length), (encA (elems x)[j]).length ≤ lMax x) :
    ∃ c d, ComputableInTimeAndSpace g encIn (encList encB)
      (fun x => c * ((encIn x).length + ((elems x).length + 1) * (lMax x + 1) ^ d + 1))
      (fun x => c * ((lMax x + 1) ^ d + 1)) := by
  obtain ⟨cn, dn, _, _, _, tmn, htn⟩ := Internal.NormalForm.polyTime hnext
  obtain ⟨ce, de, _, _, _, tme, hte⟩ := Internal.NormalForm.polyTime hemit
  obtain ⟨cf, hf⟩ := computableInTimeAndSpace_of_const (encIn := encS) (encOut := encUnit) ()
  let d := max dn de + 1
  let K := 3 ^ d * (cn + ce + 1) + 4
  have hstep_pow : ∀ x j (hj : j < (elems x).length),
      cn * ((encPair encS encA (streamState (init x) next (elems x) j, (elems x)[j])).length +
          1) ^ dn ≤ cn * (3 ^ d * (lMax x + 1) ^ d) ∧
        ce * ((encPair encS encA (streamState (init x) next (elems x) j, (elems x)[j])).length +
            1) ^ de ≤ ce * (3 ^ d * (lMax x + 1) ^ d) := by
    intro x j hj
    have hs0 := hS x j hj.le
    have ha := hA x j hj
    have hlen_p : (encPair encS encA (streamState (init x) next (elems x) j,
        (elems x)[j])).length + 1 ≤ 3 * (lMax x + 1) := by
      rw [length_encPair]
      dsimp only
      omega
    have hpow_le : ∀ {e : ℕ}, e ≤ d →
        ((encPair encS encA (streamState (init x) next (elems x) j,
          (elems x)[j])).length + 1) ^ e ≤ 3 ^ d * (lMax x + 1) ^ d := by
      intro e he
      exact (Nat.pow_le_pow_left hlen_p e).trans
        ((Nat.pow_le_pow_right (by omega) he).trans_eq (Nat.mul_pow _ _ _))
    exact ⟨Nat.mul_le_mul_left _ (hpow_le (by omega)),
      Nat.mul_le_mul_left _ (hpow_le (by omega))⟩
  have hsf := ComputableTidilyInTimeAndSpace.streamFold_pair_sum
    (g := g) (encOut := encList encB) (encF := encUnit)
    frameValueReader (fun a => frame (encA a)) (fun a => frame_ne_nil (encA a))
    (fun a rest => read_frameValueReader (encA a) rest)
    init elems
    (fun x => by rw [hL x, encPair_apply]; rfl)
    ⟨_, _, inferInstance, tmn, htn⟩ ⟨_, _, inferInstance, tme, hte⟩
    hf.computableTidilyInTimeAndSpace
    (fun x => by simp [hg x, encUnit_apply])
    (roundCost := fun x _ => K * (lMax x + 1) ^ d)
    (sMax := fun x => K * (lMax x + 1) ^ d)
    (lMax := lMax)
    (fun x j hj => by
      have hs0 := hS x j hj.le
      have hs1 := hS x (j + 1) hj
      have ha := hA x j hj
      obtain ⟨h1, h2⟩ := hstep_pow x j hj
      have h3 : 1 ≤ (lMax x + 1) ^ d := Nat.one_le_pow _ _ (Nat.succ_pos _)
      have h4 : 2 * lMax x + lMax x + 1 ≤ 3 * (lMax x + 1) ^ d := by
        have : lMax x + 1 ≤ (lMax x + 1) ^ d := Nat.le_self_pow (by omega) _
        omega
      have hK : cn * (3 ^ d * (lMax x + 1) ^ d) + ce * (3 ^ d * (lMax x + 1) ^ d) +
          (2 * lMax x + lMax x + 1) ≤ K * (lMax x + 1) ^ d := by
        have h3pow : 3 ≤ 3 ^ d := Nat.le_self_pow (by omega) 3
        have h3mul : 3 * (lMax x + 1) ^ d ≤ 3 ^ d * (lMax x + 1) ^ d :=
          Nat.mul_le_mul_right _ h3pow
        dsimp [K]
        nlinarith only [h3mul, h4, h3]
      omega)
    (fun x j hj => by
      obtain ⟨h1, h2⟩ := hstep_pow x j hj
      calc _ ≤ cn * (3 ^ d * (lMax x + 1) ^ d) + ce * (3 ^ d * (lMax x + 1) ^ d) :=
            Nat.add_le_add h1 h2
        _ = (3 ^ d * (cn + ce)) * (lMax x + 1) ^ d := by ring
        _ ≤ K * (lMax x + 1) ^ d := Nat.mul_le_mul_right _
            ((Nat.mul_le_mul_left (3 ^ d) (Nat.le_succ (cn + ce))).trans (Nat.le_add_right _ 4)))
    hS hA
  obtain ⟨c, hc⟩ := hsf
  have hc' : ComputableInTimeAndSpace g encIn (encList encB)
      (fun x => c * (2 * cf + 2 + (encIn x).length +
        ∑ j ∈ Finset.range (elems x).length, K * (lMax x + 1) ^ d + lMax x + 1))
      (fun x => c * (0 + K * (lMax x + 1) ^ d + lMax x + 1)) :=
    ComputableTidilyInTimeAndSpace.computableInTimeAndSpace hc
  have hl (x : γ) : lMax x ≤ (lMax x + 1) ^ d :=
    (Nat.le_succ _).trans (Nat.le_self_pow (by omega) _)
  refine ⟨c * (2 * cf + K + 4), d, hc'.mono (fun x => ?_) (fun x => ?_)⟩
  · simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
    have hl := hl x
    set A := (encIn x).length
    set B := ((elems x).length + 1) * (lMax x + 1) ^ d
    have hKl : (elems x).length * (K * (lMax x + 1) ^ d) ≤ K * B := by
      calc (elems x).length * (K * (lMax x + 1) ^ d)
          = K * ((elems x).length * (lMax x + 1) ^ d) := by ring
        _ ≤ K * B := Nat.mul_le_mul_left K (Nat.mul_le_mul_right _ (Nat.le_succ _))
    have hA_le : A ≤ (2 * cf + K + 4) * A := Nat.le_mul_of_pos_left A (by omega)
    have hKB_le : (K + 1) * B ≤ (2 * cf + K + 4) * B := Nat.mul_le_mul_right B (by omega)
    have h1_le : 2 * cf + 3 ≤ (2 * cf + K + 4) * 1 := by omega
    have hc_le : 2 * cf + 2 + A + (elems x).length * (K * (lMax x + 1) ^ d) + lMax x + 1 ≤
        (2 * cf + K + 4) * (A + B + 1) := by
      have hB_ge : lMax x ≤ B := hl.trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos _))
      calc 2 * cf + 2 + A + (elems x).length * (K * (lMax x + 1) ^ d) + lMax x + 1
          ≤ (2 * cf + 3) + A + (K * B + B) := by omega
        _ = (2 * cf + 3) + A + (K + 1) * B := by ring
        _ ≤ (2 * cf + K + 4) * 1 + (2 * cf + K + 4) * A + (2 * cf + K + 4) * B := by omega
        _ = (2 * cf + K + 4) * (A + B + 1) := by ring
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_left c hc_le
  · have hpow : 1 ≤ (lMax x + 1) ^ d := Nat.one_le_pow _ _ (Nat.succ_pos _)
    rw [Nat.mul_assoc]
    apply Nat.mul_le_mul_left c
    nlinarith only [hl x, hpow]

end

end Turing.MultiTapeTM
