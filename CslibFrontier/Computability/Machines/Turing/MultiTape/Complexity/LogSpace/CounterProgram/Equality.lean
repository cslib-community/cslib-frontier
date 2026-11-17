/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Words
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram.Step
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Frame
import CslibFrontier.Tactic.EncLen

/-!
# Equality in logarithmic space

Compare two encoded words by rereading their bits with two counters, without storing either
word. The counters are bounded by the input length. This supplies equality for the active
self-query test in bounded truth-table autoreductions.

## Main results

* `Turing.MultiTapeTM.ComputableInLogSpace.equal`: equality of two computed encoded instances.
-/

public section

namespace Turing.CounterProgram

open Instr Expr MultiTapeTM

private def equalityProgram : CounterProgram where
  code :=
    [read (mul (const 2) (reg 0)) 1 2 2,
     assign 0 (add (reg 0) (const 1)) 0,
     read (mul (const 2) (reg 1)) 3 6 6,
     read (add (mul (const 2) (reg 1)) (const 1)) 4 5 9,
     read (add (add (mul (const 2) (reg 0)) (const 1)) (reg 1)) 7 9 9,
     read (add (add (mul (const 2) (reg 0)) (const 1)) (reg 1)) 9 7 9,
     read (add (add (mul (const 2) (reg 0)) (const 1)) (reg 1)) 9 9 8,
     assign 1 (add (reg 1) (const 1)) 2,
     accept, reject]
  registers := 2

private theorem bounded {a b B : ℕ} (ha : a ≤ B) (hb : b ≤ B) :
    ∀ r ∈ [a, b], r ≤ B := by simp_all

private theorem equality_run (u v : List Bool) {B : ℕ}
    (hB : u.length + 1 ≤ B) :
    ∃ s, equalityProgram.Reaches (frame u ++ v) (equalityProgram.Running B)
      equalityProgram.init s ∧
      equalityProgram.instr s.1 = .halt (encBool (decide (u = v))) ∧
      ∀ r ∈ s.2, r ≤ B := by
  have scan : ∀ i ≤ u.length,
      equalityProgram.Reaches (frame u ++ v) (equalityProgram.Running B)
        (0, [i, 0]) (2, [u.length, 0]) := by
    intro i hi
    induction h : u.length - i generalizing i with
    | zero =>
      obtain rfl : i = u.length := by omega
      cp_step [getElem?_frame_append_length]
    | succ n ih =>
      have hiu : i < u.length := by omega
      cp_step [(getElem?_frame_append u v hiu).1]
      cp_step
      exact ih (i + 1) (by omega) (by omega)
  have loop : ∀ i ≤ u.length, ∃ s,
      equalityProgram.Reaches (frame u ++ v) (equalityProgram.Running B)
        (2, [u.length, i]) s ∧
      equalityProgram.instr s.1 = .halt (encBool (decide (u.drop i = v.drop i))) ∧
      ∀ r ∈ s.2, r ≤ B := by
    intro i hi
    induction h : u.length - i generalizing i with
    | zero =>
      obtain rfl : i = u.length := by omega
      have hregs := bounded (B := B) (a := u.length) (b := u.length) (by omega) (by omega)
      by_cases hv : u.length < v.length
      · refine ⟨(9, [u.length, u.length]), ?_, ?_, hregs⟩
        · cp_step [getElem?_frame_append_length]
          cases hb : v[u.length] <;>
            cp_step [getElem?_frame_append_boundary, List.getElem?_eq_getElem hv, hb]
        · have : v.drop u.length ≠ [] := by simp [List.drop_eq_nil_iff, hv.not_ge]
          simp [List.drop_length, this, equalityProgram, instr, Instr.reject]
      · refine ⟨(8, [u.length, u.length]), ?_, ?_, hregs⟩
        · cp_step [getElem?_frame_append_length]
          cp_step [getElem?_frame_append_boundary,
            List.getElem?_eq_none (by omega : v.length ≤ u.length)]
        · simp [List.drop_eq_nil_iff.mpr (by omega : v.length ≤ u.length), equalityProgram,
            instr, Instr.accept]
    | succ n ih =>
      have hiu : i < u.length := by omega
      have hregs := bounded (B := B) (a := u.length) (b := i) (by omega) (by omega)
      have hstep : equalityProgram.Reaches (frame u ++ v) (equalityProgram.Running B)
          (2, [u.length, i])
          (if u[i] then 4 else 5, [u.length, i]) := by
        cp_step [(getElem?_frame_append u v hiu).1]
        cases hu : u[i] <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
          cp_step [(getElem?_frame_append u v hiu).2, hu]
      by_cases hv : i < v.length
      · by_cases heq : u[i] = v[i]
        · obtain ⟨s, hs, hout, hb⟩ := ih (i + 1) (by omega) (by omega)
          refine ⟨s, hstep.trans ?_, ?_, hb⟩
          · cases hu : u[i] <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
              (cp_step [getElem?_frame_append_boundary, List.getElem?_eq_getElem hv, ← heq, hu]
               cp_step)
          · have hd : u.drop i = v.drop i ↔ u.drop (i + 1) = v.drop (i + 1) := by
              rw [← List.cons_getElem_drop_succ (l := u) (n := i) (h := hiu),
                ← List.cons_getElem_drop_succ (l := v) (n := i) (h := hv), List.cons.injEq]
              exact and_iff_right heq
            simpa only [hd] using hout
        · refine ⟨(9, [u.length, i]), hstep.trans ?_, ?_, hregs⟩
          · have hvb : v[i] = !u[i] := Bool.eq_not_iff.mpr (Ne.symm heq)
            cases hu : u[i] <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
              cp_step [getElem?_frame_append_boundary, List.getElem?_eq_getElem hv, hvb, hu,
                Bool.not_false, Bool.not_true]
          · have hd : u.drop i ≠ v.drop i := by
              rw [← List.cons_getElem_drop_succ (l := u) (n := i) (h := hiu),
                ← List.cons_getElem_drop_succ (l := v) (n := i) (h := hv)]
              exact fun hdrop => heq (List.cons.inj hdrop).1
            simp [hd, equalityProgram, instr, Instr.reject]
      · refine ⟨(9, [u.length, i]), hstep.trans ?_, ?_, hregs⟩
        · cases hu : u[i] <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
            cp_step [getElem?_frame_append_boundary,
              List.getElem?_eq_none (by omega : v.length ≤ i)]
        · have hd : u.drop i ≠ v.drop i := by
            rw [List.drop_eq_nil_iff.mpr (by omega : v.length ≤ i)]
            simp [List.drop_eq_nil_iff, hiu.not_ge]
          simp [hd, equalityProgram, instr, Instr.reject]
  obtain ⟨s, hs, hout, hb⟩ := loop 0 (Nat.zero_le _)
  exact ⟨s, (scan 0 (Nat.zero_le _)).trans hs, by simpa using hout, hb⟩

private theorem equality_logspace :
    ComputableInLogSpace (fun p : List Bool × List Bool => decide (p.1 = p.2))
      (encPair encBits encBits) encBool := by
  apply equalityProgram.computableInLogSpace_of_reaches 1
  intro p
  apply equality_run p.1 p.2
  enc_len [pow_one]

end Turing.CounterProgram

namespace Turing.MultiTapeTM.ComputableInLogSpace

/-- Equality of two logspace-computed instances, by injectivity of their common encoding. -/
@[fun_prop]
theorem equal {α β : Type} {encIn : α ↪ List Bool} {enc : β ↪ List Bool} [DecidableEq β]
    {f g : α → β} (hf : ComputableInLogSpace f encIn enc)
    (hg : ComputableInLogSpace g encIn enc) :
    ComputableInLogSpace (fun a => decide (f a = g a)) encIn encBool := by
  have hw := CounterProgram.equality_logspace.comp (pair
    (hf.congr (g := fun a => enc (f a)) fun _ => rfl)
    (hg.congr (g := fun a => enc (g a)) fun _ => rfl))
  exact hw.congr_fun fun a => by simp [enc.injective.eq_iff]

end Turing.MultiTapeTM.ComputableInLogSpace
