/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.TwoWordInput
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.ScheduleHeightWord
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Bounds
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Unary
public import CslibFrontier.Foundations.Data.Nat.BinarySize

/-!
# Outer-tree initialization fields from a short binary word

The half-length is binary and comes after a fixed framed marker. Both long fields have
deterministic, ordinary-input resource certificates linear in their output length.
-/

public section

namespace Turing.MultiTapeTM.ScheduleHeightWord

open PositionPairs MultiTapeATM.TwoWordInput

/-- A framed false marker followed by the binary half-length, with least significant bit first. -/
@[expose] def encHalf : ℕ ↪ List Bool where
  toFun n := encPair encBool encNat (false, n)
  inj' := fun _ _ h => congrArg Prod.snd ((encPair encBool encNat).injective h)

private theorem length_encHalf (n : ℕ) : (encHalf n).length = n.size + 3 := by
  change (encPair encBool encNat (false, n)).length = _
  simp only [length_encPair, encBool_apply, List.length_singleton, encNat_apply,
    ← Nat.size_eq_bits_len]
  omega

private theorem from_pair {S : Type} [Finite S] (tm : MultiTapeTM 3 Bool S)
    (f : ℕ → List Bool) (ticks : ℕ → ℕ)
    (bound : ∀ n, ticks n ≤ 18 * (n + 1))
    (len : ∀ n, (f n).length ≤ 2 * n + 1)
    (hr : ∀ (input : List Bool) (n : ℕ),
      tm.runFrom ((config input [false] (encNat n) [] 0 []).withState (some tm.q₀)) (ticks n) =
        (config input [false] [] [] 0 (f n)).withState none) :
    ComputableInO f encHalf encBits id id := by
  obtain ⟨u, Q, hQ, m, c, h⟩ :=
    exists_prepend_deterministic encBool encNat 0 1 (by decide : (0 : Fin 3) ≠ 1) tm
  let time (n : ℕ) := c * ((encHalf n).length + 1) + ticks n
  have exactTime : ComputableInTimeAndSpace f encHalf encBits time (fun n => u * (time n + 1)) := by
    refine ⟨u, Q, hQ, m, ?_⟩
    intro n
    let input := encHalf n
    let finish := config input [false] [] [] 0 (f n)
    have hw : words (0 : Fin 3) 1 (encBool false) (encNat n) = ![[false], encNat n, []] := by
      funext j
      fin_cases j <;> simp [words]
    have hz : (![0, 0, 0] : Fin 3 → ℤ) = 0 := by funext j; fin_cases j <;> rfl
    have ha := h (false, n) (ticks n) finish (by
      rw [hw]
      have hinit : (config input [false] (encNat n) [] 0 []).withState (some tm.q₀) =
          wordsCfg input (some tm.q₀) ![[false], encNat n, []] [] := by
        unfold config
        rw [hz, tapesCfg_zero_withState]
      change tm.runFrom (wordsCfg input _ _ _) (ticks n) = finish.withState none
      rw [← hinit]
      exact hr input n)
    exact ha
  let A := 4 * c + 18
  have ht (n : ℕ) : time n ≤ A * (n + 1) := by
    have hh := Nat.size_le_self n
    dsimp [time, A]
    rw [length_encHalf]
    have hc := Nat.mul_le_mul_left c (show n.size + 3 + 1 ≤ 4 * (n + 1) by omega)
    nlinarith [bound n]
  let K := (u + 1) * (A + 1)
  apply ComputableInO.of_bounds exactTime K
  · intro n
    exact (ht n).trans (Nat.mul_le_mul_right _ (by dsimp [K]; nlinarith))
  · intro n
    have hs := Nat.mul_le_mul_left u (Nat.add_le_add_right (ht n) 1)
    change u * (time n + 1) ≤ K * (n + 1)
    calc
      _ ≤ u * ((A + 1) * (n + 1)) := by
        apply Nat.mul_le_mul_left
        nlinarith [ht n]
      _ ≤ _ := by
        rw [← Nat.mul_assoc]
        exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.le_succ u))
  · intro n
    have hK : 2 ≤ K := by dsimp [K, A]; nlinarith
    exact (len n).trans (by change 2 * n + 1 ≤ K * (n + 1); nlinarith)

/-- Generate the unary frontier from a marked binary half-length. -/
theorem unary_inO :
    ComputableInO (fun n => encUnary (2 * n)) encHalf encBits id id := by
  apply from_pair (machine true) _ (fun n => 13 * n + 5 * n.size + 14)
  · intro n; have h := Nat.size_le_self n; omega
  · intro n; simp [encUnary_apply]
  · intro input n
    simpa only [encNat_apply, Cslib.BitString.lsbValue_bits, ← Nat.size_eq_bits_len,
      List.nil_append, encUnary_apply] using (runsBetween true input (encNat n) []).1

/-- Generate the full binary leaf count from the same short request. -/
theorem leafCount_inO :
    ComputableInO (fun n => encNat (2 ^ (2 * n))) encHalf encBits id id := by
  apply from_pair leafCount _ (fun n => 13 * n + 5 * n.size + 15)
  · intro n; have h := Nat.size_le_self n; omega
  · intro n; simp [encNat_apply, bits_pow]
  · intro input n
    simpa only [encNat_apply, Cslib.BitString.lsbValue_bits, ← Nat.size_eq_bits_len,
      List.nil_append] using (runsBetween_leafCount input (encNat n) []).1

end Turing.MultiTapeTM.ScheduleHeightWord
