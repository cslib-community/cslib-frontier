/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Words
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.QueryMachine
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram.Unary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Streaming
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpaceLib
import Mathlib.Data.Nat.Size
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatLength

/-!
# Streaming a list of values at successive indices

Polynomially many values of a function on unary parameters can be tabulated using a binary index.
Each round emits its output directly to the write-only output tape.
-/

public section

namespace Turing.MultiTapeTM

open ComputableInSpace

private def countdown : QueryMachine ℕ where
  init := 0
  query _ := 0
  next p := p.1 - 1
  emit _ := [true]
  halted n := decide (n = 0)
  finish _ := []

private theorem countdown_run (w : List Bool) (n i : ℕ) :
    countdown.runFrom w n i = n - i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [QueryMachine.runFrom_succ, ih]
    simp only [QueryMachine.step, countdown, decide_eq_true_eq]
    split <;> omega

/-- Binary-to-unary conversion can emit its entire output with workspace linear in the
number of binary input digits. -/
theorem exists_computableInTimeAndSpace_natToUnary :
    ∃ t c, ComputableInTimeAndSpace id encNat encUnary t fun n => c * ((encNat n).length + 1) := by
  have hi : ComputableInSpace id encNat encNat fun n => (encNat n).length :=
    of_inO (.of_eq fun _ => rfl)
  have hn : ComputableInSpace countdown.next (QueryMachine.encStateRead encNat) encNat
      (fun q => (QueryMachine.encStateRead encNat q).length) := by
    change ComputableInSpace (fun q : ℕ × Option Bool => q.1 - 1) _ _ _
    exact budget_comp_lin natPred linear_succ (fst encNat (encOption encBool))
  obtain ⟨t, c, h⟩ := countdown.computableInSpaceFrom (encS := encNat) (enc := encNat)
    (encOut := encUnary) (f := id) (start := id)
    (budget_const 0) hn
    (budget_const [true]) natIsZero (budget_const []) id (fun n => (encNat n).length + 1)
    (hi.weaken ⟨1, fun _ => by dsimp only; omega⟩)
    (fun n => by
      change decide (countdown.runFrom (encNat n) n n = 0) = true
      simp [countdown_run])
    (fun n i hi => by
      change decide (countdown.runFrom (encNat n) n i = 0) = false
      have hi' : i < n := hi
      simp [countdown_run, Nat.ne_of_gt (Nat.sub_pos_of_lt hi')])
    (fun n => by
      change encUnary n = _
      rw [QueryMachine.outputFrom, QueryMachine.output]
      change encUnary n = ((List.range n).map fun i =>
        if countdown.halted (countdown.runFrom _ n i) then [] else [true]).flatten ++ []
      have hr (i : ℕ) (hi : i ∈ List.range n) :
          (if countdown.halted (countdown.runFrom (encNat n) n i) then [] else [true]) = [true] := by
        change (if decide (countdown.runFrom (encNat n) n i = 0) then [] else [true]) = [true]
        simp [countdown_run, Nat.ne_of_gt (Nat.sub_pos_of_lt (List.mem_range.mp hi))]
      rw [List.map_congr_left hr]
      simp [encUnary_apply])
    (fun n => by have := Nat.log2_le_self (encNat n).length; omega)
    ⟨1, fun n i _ => by
      simp only [id_eq, countdown_run, one_mul, encNat_apply, Nat.size_eq_bits_len]
      exact (Nat.size_le_size (Nat.sub_le n i)).trans (Nat.le_succ _)⟩
  exact ⟨t, c, h⟩

private def bumpIndex {σ : Type} (p : σ × ℕ) := (p.1, p.2 + 1)

private theorem iterate_bumpIndex {σ : Type} (p : σ × ℕ) (i : ℕ) :
    bumpIndex^[i] p = (p.1, p.2 + i) := by
  induction i with
  | zero => simp
  | succ i ih => rw [Function.iterate_succ_apply', ih]; simp [bumpIndex, Nat.add_assoc]

/-- Stream the outputs of a binary-indexed computation on consecutive inputs. The initial state
contains its fixed parameter and starting index in binary. Only the round count is in unary.
The output can be longer than the working space of the emission procedure. -/
theorem ComputableInTimeAndSpace.flatMap_range_binaryIndex {σ : Type} {enc : σ ↪ List Bool}
    {emit : σ × ℕ → List Bool} {t : σ × ℕ → ℕ} {c : ℕ}
    (he : ComputableInTimeAndSpace emit (encPair enc encNat) encBits t
      (fun p => c * ((encPair enc encNat p).length + 1))) :
    ∃ u C, ComputableInTimeAndSpace
      (fun p : (σ × ℕ) × ℕ => (List.range p.2).flatMap fun i => emit (p.1.1, p.1.2 + i))
      (encPair (encPair enc encNat) encUnary) encBits u
      (fun p => C * ((enc p.1.1).length + (encNat (p.1.2 + p.2)).length + 1)) := by
  let S (p : (σ × ℕ) × ℕ) := (enc p.1.1).length + (encNat (p.1.2 + p.2)).length + 1
  have hS (p : (σ × ℕ) × ℕ) (i : ℕ) (hi : i ≤ p.2) :
      (encPair enc encNat (bumpIndex^[i] p.1)).length + 1 ≤ 2 * S p := by
    rw [iterate_bumpIndex, length_encPair]
    have hlen : (encNat (p.1.2 + i)).length ≤ (encNat (p.1.2 + p.2)).length := by
      simp only [encNat_apply, Nat.size_eq_bits_len]
      exact Nat.size_le_size (by omega)
    dsimp only [S]
    omega
  have hn : ComputableInSpace (@bumpIndex σ) (encPair enc encNat) (encPair enc encNat)
      (fun p => (encPair enc encNat p).length) := by
    change ComputableInSpace (fun p : σ × ℕ => (p.1, p.2 + 1)) _ _ _
    exact budget_prod (fst enc encNat) (budget_comp_lin natSucc linear_succ (snd enc encNat))
  obtain ⟨tn, cn, hn, _⟩ := hn
  have hf : ComputableInSpace (fun _ : σ × ℕ => ([] : List Bool)) (encPair enc encNat)
      encBits (fun _ => 0) := constZero []
  obtain ⟨tf, cf, hf, _⟩ := hf
  obtain ⟨C, h⟩ := ComputableInTimeAndSpace.iterate_unary_stream_sum hn he hf
    (R := fun p i => tn (bumpIndex^[i] p.1) + t (bumpIndex^[i] p.1) +
      (encPair enc encNat (bumpIndex^[i] p.1)).length +
      (encPair enc encNat (bumpIndex^[i + 1] p.1)).length + 1)
    (Q := fun p => (cn + c) * (2 * S p)) (B := fun p => 2 * S p)
    (fun _ _ _ => le_rfl)
    (fun p i hi => by
      rw [← Nat.add_mul]
      exact Nat.mul_le_mul_left _ (hS p i hi.le))
    (fun p i hi => (Nat.le_succ _).trans (hS p i hi))
  simp only [iterate_bumpIndex, List.append_nil, ← List.flatMap_def] at h
  refine ⟨_, C * (cf + 2 * (cn + c) + 3), h.mono (fun _ => le_rfl) fun p => ?_⟩
  change C * (cf * (0 + 1) + (cn + c) * (2 * S p) + 2 * S p + 1) ≤
    C * (cf + 2 * (cn + c) + 3) * S p
  have hs : 1 ≤ S p := by simp [S]
  rw [Nat.mul_assoc]
  apply Nat.mul_le_mul_left
  nlinarith

/-- Tabulate a binary-indexed emitter in logspace. The parameter carried between emissions
fits in logarithmic space, and each round may write a word longer than its own workspace.
The count is supplied in unary by a logspace computation. -/
theorem ComputableInLogSpace.flatMap_range {α σ : Type} {encIn : α ↪ List Bool}
    {enc : σ ↪ List Bool} {params : α → σ} {count : α → ℕ} {emit : σ × ℕ → List Bool}
    {t : σ × ℕ → ℕ} {c : ℕ}
    (hp : ComputableInSpace params encIn enc (fun a => Nat.log2 (encIn a).length))
    (hr : ComputableInLogSpace count encIn encUnary)
    (he : ComputableInTimeAndSpace emit (encPair enc encNat) encBits t
      (fun p => c * ((encPair enc encNat p).length + 1))) :
    ComputableInLogSpace (fun a => (List.range (count a)).flatMap fun i => emit (params a, i))
      encIn encBits := by
  obtain ⟨tp, cp, hp, hplen⟩ := hp
  have hpf : ComputableInLogSpace params encIn enc := ⟨tp, cp, hp⟩
  have hargs := ComputableInLogSpace.pair (ComputableInLogSpace.pair hpf
    (ComputableInLogSpace.const (encMid := encNat) 0)) hr
  obtain ⟨A, D, hcount⟩ := hr.polyBounded_length.exists_le
  obtain ⟨u, C, hu⟩ := he.flatMap_range_binaryIndex
  have hb : ∀ a, (encNat (count a)).length ≤ (Nat.size A + 2 * D + 1) *
      (Nat.log2 (encIn a).length + 1) := fun a => length_encNat_le_of_le_mul_pow
        (by simpa only [encUnary_apply, List.length_replicate] using hcount a)
  have h := hargs.comp_of_workSpace hu ⟨C * (cp + (Nat.size A + 2 * D + 1) + 1), fun a => by
    dsimp only
    rw [Nat.zero_add, Nat.mul_assoc]
    apply Nat.mul_le_mul_left
    have h₁ := hplen a
    dsimp only at h₁
    have h₂ := hb a
    rw [Nat.add_mul, Nat.add_mul, Nat.one_mul]
    omega⟩
  exact h.congr_fun fun _ => by simp

end Turing.MultiTapeTM
