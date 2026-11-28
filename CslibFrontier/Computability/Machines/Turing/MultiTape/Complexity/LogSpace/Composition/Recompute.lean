/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Composition.SmallSpace
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatLength
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Ring

/-!
# Logspace functions compose

Logspace functions compose without storing the intermediate value
(`Turing.MultiTapeTM.ComputableInLogSpace.comp`): Christian Reitwiessner's composition within
small space (`Turing.MultiTapeTM.ComputableInTimeAndSpace.comp_space`) recomputes each symbol of
the intermediate value when the second machine reads it, and stores only the two machines' work
tapes and counters of logarithmic length [Sipser, Section 8.5][Sipser2013].

The composed machine simulates both machines through the universal machine, so this directory,
unlike the base logspace API, depends on `Universal`. This module also registers the composition
rule of `fun_prop` for `ComputableInLogSpace`.

## Main results

* `Turing.MultiTapeTM.ComputableInLogSpace.comp`: logspace functions compose.
* `Turing.MultiTapeTM.ComputableInSpace.comp_logSpace`: a function within a workspace budget
  composes after a logspace function, within its budget plus the logarithm of the input length.
* `Turing.MultiTapeTM.comp_logSpace_of_length_log`: a logspace producer of short values
  composes with a linear-space consumer.
* `Turing.MultiTapeTM.ComputableInLogSpace.inSpace_of_length_log`: charge the encoded output
  to the logarithmic workspace budget.
* `Turing.MultiTapeTM.length_log_of_inSpace`: the composed output is short.
* `Turing.MultiTapeTM.ComputableInLogSpace.comp'`,
  `Turing.MultiTapeTM.ComputableInLogSpace.bool_not`: composition and negation in the form used by
  `fun_prop`.

## References

* [M. Sipser, *Introduction to the Theory of Computation*, Section 8.5][Sipser2013]
-/

public section

namespace Turing.MultiTapeTM

variable {α β γ : Type} {encIn : α ↪ List Bool} {encMid : β ↪ List Bool}
  {encOut : γ ↪ List Bool}

/-- The binary length of `m + 1` is logarithmic in `n` when `m` is polynomial in `n`. -/
private theorem length_encNat_succ_le {m n C d : ℕ} (h : m ≤ C * (n + 1) ^ d) :
    (encNat (m + 1)).length ≤ (Nat.size (C + 1) + d) * (Nat.log2 n + 1) := by
  rw [encNat_apply, Nat.size_eq_bits_len, Nat.size_le]
  have hpos : 0 < (n + 1) ^ d := Nat.pow_pos (Nat.succ_pos n)
  have hn : (n + 1) ^ d ≤ 2 ^ (d * (Nat.log2 n + 1)) := by
    rw [mul_comm, pow_mul]
    exact Nat.pow_le_pow_left Nat.lt_log2_self d
  calc m + 1 ≤ (C + 1) * (n + 1) ^ d := by nlinarith
    _ < 2 ^ Nat.size (C + 1) * 2 ^ (d * (Nat.log2 n + 1)) :=
        Nat.mul_lt_mul_of_lt_of_le (Nat.lt_size_self _) hn (Nat.two_pow_pos _)
    _ = 2 ^ (Nat.size (C + 1) + d * (Nat.log2 n + 1)) := (pow_add ..).symm
    _ ≤ 2 ^ ((Nat.size (C + 1) + d) * (Nat.log2 n + 1)) :=
        Nat.pow_le_pow_right (by norm_num) (by nlinarith)

/-- A logspace producer may feed a computation whose workspace on the produced inputs
is logarithmic in the original input length. Its output is written to the output tape. -/
theorem ComputableInLogSpace.comp_of_workSpace {g : β → γ} {f : α → β} {t s : β → ℕ}
    (hf : ComputableInLogSpace f encIn encMid) (hg : ComputableInTimeAndSpace g encMid encOut t s)
    (hs : ∃ K, ∀ a, s (f a) ≤ K * (Nat.log2 (encIn a).length + 1)) :
    ComputableInLogSpace (g ∘ f) encIn encOut := by
  obtain ⟨C, d, hlen⟩ := hf.polyBounded_length.exists_le
  obtain ⟨tf, cf, hf⟩ := hf
  obtain ⟨K, hK⟩ := hs
  obtain ⟨c, h⟩ := hf.comp_space hg
  let D := Nat.size (C + 1) + d
  refine ⟨_, c * (cf + K + Nat.size 2 + 1 + D + 1), h.mono (fun _ => le_rfl) fun a => ?_⟩
  have hm := length_encNat_succ_le (hlen a)
  have hn := length_encNat_succ_le (m := (encIn a).length) (n := (encIn a).length) (C := 1)
    (d := 1) (by simp)
  have hg' := hK a
  have hL : 1 ≤ Nat.log2 (encIn a).length + 1 := Nat.le_add_left _ _
  rw [Nat.mul_assoc]
  apply Nat.mul_le_mul_left
  dsimp only [D]
  generalize Nat.log2 (encIn a).length + 1 = L at *
  generalize (encNat ((encIn a).length + 1)).length = A at *
  generalize (encNat ((encMid (f a)).length + 1)).length = B at *
  nlinarith

/-- **Logspace functions compose**, without storing the intermediate value: each of its symbols is
recomputed when the second machine reads it (`ComputableInTimeAndSpace.comp_space`). The
counters for positions in the input and in the intermediate value have logarithmic length, since
the intermediate value is polynomially long. -/
theorem ComputableInLogSpace.comp {g : β → γ} {f : α → β}
    (hg : ComputableInLogSpace g encMid encOut) (hf : ComputableInLogSpace f encIn encMid) :
    ComputableInLogSpace (g ∘ f) encIn encOut := by
  obtain ⟨C, d, hlen⟩ := hf.polyBounded_length.exists_le
  obtain ⟨t, c, hg⟩ := hg
  refine hf.comp_of_workSpace hg ⟨c * (Nat.size (C + 1) + d), fun a => ?_⟩
  rw [Nat.mul_assoc]
  exact Nat.mul_le_mul_left _
    ((log2_succ_le_length_encNat _).trans (length_encNat_succ_le (hlen a)))

/-- **A function within a workspace budget, after a logspace function.** If `g` is computable
within the budget `Sg`, its value charged, and `f` in logarithmic space, then `g ∘ f` is computable
within `Sg (f a) + log₂ n` on inputs `a` of length `n`. The intermediate value `f a` may be long:
it is recomputed symbol by symbol and never stored
(`Turing.MultiTapeTM.ComputableInTimeAndSpace.comp_space`), and the counters for positions in it
have logarithmic length because it is polynomially long. With `f` a rearrangement of a pair of
stored registers and a read-only context, this substitutes the registers or the context of a
function in that form. -/
theorem ComputableInSpace.comp_logSpace {g : β → γ} {f : α → β} {Sg : β → ℕ}
    (hg : ComputableInSpace g encMid encOut Sg) (hf : ComputableInLogSpace f encIn encMid) :
    ComputableInSpace (fun a => g (f a)) encIn encOut
      fun a => Sg (f a) + Nat.log2 (encIn a).length := by
  obtain ⟨C, d, hlen⟩ := hf.polyBounded_length.exists_le
  obtain ⟨tf, cf, hf⟩ := hf
  obtain ⟨tg, cg, hg, hout⟩ := hg
  obtain ⟨c, h⟩ := hf.comp_space hg
  obtain ⟨K, hK⟩ : ∃ K, Nat.size (C + 1) + d = K := ⟨_, rfl⟩
  refine ⟨_, max (c * (cf + cg + Nat.size 2 + 1 + K + 1)) cg,
    h.mono (fun _ => le_rfl) fun a => ?_, fun a => (hout (f a)).trans ?_⟩
  · have hm := hK ▸ length_encNat_succ_le (hlen a)
    have hn := length_encNat_succ_le (m := (encIn a).length) (n := (encIn a).length) (C := 1)
      (d := 1) (by simp)
    refine (Nat.mul_le_mul_left c ?_).trans
      ((Nat.mul_assoc ..).ge.trans (Nat.mul_le_mul_right _ (le_max_left _ _)))
    have hL : 1 ≤ Nat.log2 (encIn a).length + 1 := Nat.le_add_left _ _
    rw [show Sg (f a) + Nat.log2 (encIn a).length + 1 =
      Sg (f a) + (Nat.log2 (encIn a).length + 1) by ring]
    generalize Nat.log2 (encIn a).length + 1 = L at *
    generalize (encNat ((encIn a).length + 1)).length = A at *
    generalize (encNat ((encMid (f a)).length + 1)).length = B at *
    generalize Sg (f a) = G
    nlinarith
  · exact (Nat.mul_le_mul_right _ (le_max_right _ _)).trans
      (Nat.mul_le_mul_left _ (by dsimp only; omega))

/-- Composition, in the form used by `fun_prop`. -/
@[fun_prop]
theorem ComputableInLogSpace.comp' {g : β → γ} {f : α → β}
    (hg : ComputableInLogSpace g encMid encOut) (hf : ComputableInLogSpace f encIn encMid) :
    ComputableInLogSpace (fun a => g (f a)) encIn encOut :=
  hg.comp hf

/-- Negating a computed Boolean, in the form used by `fun_prop`. -/
@[fun_prop]
theorem ComputableInLogSpace.bool_not {c : α → Bool} (hc : ComputableInLogSpace c encIn encBool) :
    ComputableInLogSpace (fun a => !c a) encIn encBool :=
  (ComputableInLogSpace.of_finite (encIn := encBool) not).comp' hc

/-- A logarithmic output-length bound lets a logspace computation charge its encoded output
to the same logarithmic budget. -/
theorem ComputableInLogSpace.inSpace_of_length_log {f : α → β}
    (h : ComputableInLogSpace f encIn encMid)
    (hlen : ∃ L, ∀ a, (encMid (f a)).length ≤ L * (Nat.log2 (encIn a).length + 1)) :
    ComputableInSpace f encIn encMid (fun a => Nat.log2 (encIn a).length) := by
  obtain ⟨time, C, hwork⟩ := h
  obtain ⟨L, hlen⟩ := hlen
  refine ⟨time, max C L, hwork.mono (fun _ => le_rfl) (fun _ => ?_), fun a => ?_⟩
  · exact Nat.mul_le_mul_right _ (le_max_left C L)
  · exact (hlen a).trans (Nat.mul_le_mul_right _ (le_max_right C L))

/-- Compose a `ComputableInLogSpace` producer whose encoded output has logarithmic length with a
`ComputableInSpace` consumer running in space linear in its input length. -/
theorem comp_logSpace_of_length_log {α β γ : Type}
    {encIn : α ↪ List Bool} {encMid : β ↪ List Bool} {encOut : γ ↪ List Bool}
    {f : α → β} {g : β → γ}
    (hf : ComputableInLogSpace f encIn encMid)
    (hlen : ∃ C, ∀ a, (encMid (f a)).length ≤ C * (Nat.log2 (encIn a).length + 1))
    (hg : ComputableInSpace g encMid encOut fun b => (encMid b).length) :
    ComputableInLogSpace (fun a => g (f a)) encIn encOut := by
  obtain ⟨C, hC⟩ := hlen
  obtain ⟨t, c, hg, _⟩ := hg
  refine hf.comp_of_workSpace hg ⟨c * (C + 1), fun a => ?_⟩
  rw [Nat.mul_assoc]
  apply Nat.mul_le_mul_left
  have h := hC a
  dsimp only
  rw [Nat.add_mul, Nat.one_mul]
  omega

/-- A linear-space `ComputableInSpace` function preserves logarithmic encoded-output length. -/
theorem length_log_of_inSpace {α β γ : Type}
    {encIn : α ↪ List Bool} {encMid : β ↪ List Bool} {encOut : γ ↪ List Bool}
    {f : α → β} {g : β → γ}
    (hlen : ∃ C, ∀ a, (encMid (f a)).length ≤ C * (Nat.log2 (encIn a).length + 1))
    (hg : ComputableInSpace g encMid encOut fun b => (encMid b).length) :
    ∃ C', ∀ a, (encOut (g (f a))).length ≤ C' * (Nat.log2 (encIn a).length + 1) := by
  obtain ⟨C, hC⟩ := hlen
  obtain ⟨_, cg, -, hglen⟩ := hg
  refine ⟨cg * (C + 1), fun a => ?_⟩
  let L := Nat.log2 (encIn a).length + 1
  have hL : 1 ≤ L := Nat.le_add_left _ _
  have hm : (encMid (f a)).length + 1 ≤ (C + 1) * L :=
    calc (encMid (f a)).length + 1
        ≤ C * L + L := Nat.add_le_add (hC a) hL
      _ = (C + 1) * L := by ring
  calc (encOut (g (f a))).length
      ≤ cg * ((encMid (f a)).length + 1) := hglen (f a)
    _ ≤ cg * ((C + 1) * L) := Nat.mul_le_mul_left cg hm
    _ = cg * (C + 1) * L := by ring

end Turing.MultiTapeTM
