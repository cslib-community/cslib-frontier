/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.PH.Reduction
import CslibFrontier.Computability.Complexity.Classes.PH.Closure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Cslib.Foundations.Data.Polynomial.Monotone
import CslibFrontier.Foundations.Data.List.TakeQuantifiers

/-!
# Polynomially bounded conjunctions in the polynomial hierarchy

A polynomial number of predicates at the same level can be conjoined without adding a
quantifier block. Existential certificates are stored as consecutive fixed-width slices of
one word; universal certificates also select the index to check.
## Main results

* `mem_SigmaP_of_forall_lt`, `mem_PiP_of_forall_lt`: bounded conjunction closure,
  including level zero.

-/

public section
namespace Cslib.Complexity
open Turing.MultiTapeTM

private theorem exists_word_slices (n m : ℕ) (R : ℕ → List Bool → Prop) :
    (∃ t : List Bool, t.length = n * m ∧
      ∀ i < n, R i ((t.drop (i * m)).take m)) ↔
    ∀ i < n, ∃ w : List Bool, w.length = m ∧ R i w := by
  induction n generalizing R with
  | zero => simp
  | succ n ih =>
    constructor
    · rintro ⟨t, ht, h⟩ i hi
      refine ⟨(t.drop (i * m)).take m, ?_, h i hi⟩
      simp only [List.length_take, List.length_drop, ht, Nat.add_mul, Nat.one_mul]
      have hmul := Nat.mul_le_mul_right m hi
      simp only [Nat.succ_mul] at hmul
      omega
    · intro h
      obtain ⟨w, hw, hR⟩ := h 0 (by omega)
      obtain ⟨t, ht, hT⟩ := (ih (fun i => R (i + 1))).mpr
        (fun i hi => h (i + 1) (by omega))
      refine ⟨w ++ t, by simp [hw, ht, Nat.succ_mul, Nat.add_comm], fun i hi => ?_⟩
      cases i with
      | zero => simpa [← hw] using hR
      | succ i =>
        have heq : (w ++ t).drop ((i + 1) * m) = t.drop (i * m) := by
          rw [Nat.add_mul, Nat.one_mul, Nat.add_comm, ← hw, ← List.drop_drop,
            List.drop_left]
        rw [heq]
        exact hT i (by omega)

variable {α : Type} {enc : α ↪ List Bool} {k : ℕ}

/-- Universal levels are closed under polynomially bounded conjunctions. The index is selected
by the number of `true` bits in a universally quantified word. -/
theorem mem_PiP_of_forall_lt {N : α → ℕ}
    (hN : ComputableInPolyTime N enc encUnary) {B : Set (α × ℕ)}
    (hB : B ∈ PiP k (encPair enc encUnary)) :
    {a | ∀ i < N a, (a, i) ∈ B} ∈ PiP k enc := by
  by_cases hk : k = 0
  · subst k
    rw [PiP_zero] at hB ⊢
    obtain ⟨V, hV, hB⟩ := hB
    exact ⟨fun a => (List.range (N a)).all (fun i => V (a, i)), by fun_prop,
      fun a => by simp [hB]⟩
  have hk : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
  let C : Set (α × List Bool) :=
    {x | x.2.count true < N x.1 → (x.1, x.2.count true) ∈ B}
  have hred : PolyTimeReducible (encPair enc encBits) (encPair enc encUnary)
      {x : α × List Bool | (x.1, x.2.count true) ∈ B} B :=
    ⟨fun x => (x.1, x.2.count true), by fun_prop, fun _ => Iff.rfl⟩
  have hguard : {x : α × List Bool | ¬ x.2.count true < N x.1} ∈ P (encPair enc encBits) :=
    ⟨fun x => !(decide (x.2.count true < N x.1)), by fun_prop, by simp⟩
  have hC : C ∈ PiP k (encPair enc encBits) := by
    convert union_mem_PiP (PiP_mono (Nat.zero_le k) (PiP_zero ▸ hguard))
      (hred.mem_PiP hB) using 1
    ext x
    simp [C, or_iff_not_imp_left]
  convert mem_PiP_of_forall_length hk hN hC using 1
  ext a
  constructor
  · intro h w _ hw
    exact h _ hw
  · intro h i hi
    have hw : (List.replicate i true ++ List.replicate (N a - i) false).length = N a := by
      simp only [List.length_append, List.length_replicate]; omega
    simpa [C, List.count_replicate, hi] using h _ hw

/-- Existential levels are closed under polynomially bounded conjunctions. A single existential
word stores one padded certificate per index; the remaining universal level checks every slice. -/
theorem mem_SigmaP_of_forall_lt {N : α → ℕ}
    (hN : ComputableInPolyTime N enc encUnary) {B : Set (α × ℕ)}
    (hB : B ∈ SigmaP k (encPair enc encUnary)) :
    {a | ∀ i < N a, (a, i) ∈ B} ∈ SigmaP k enc := by
  cases k with
  | zero =>
    simpa only [SigmaP_zero, PiP_zero] using mem_PiP_of_forall_lt (k := 0) hN
      (by simpa only [SigmaP_zero, PiP_zero] using hB)
  | succ k =>
    obtain ⟨p, D, hD, hBD⟩ := mem_SigmaP_succ_iff.mp hB
    let M : α → ℕ := fun a => p.eval (2 * (enc a).length + 1 + N a)
    have hM : ComputableInPolyTime M enc encUnary :=
      (ComputableInPolyTime.unary_eval p).comp (by fun_prop)
    let C : Set ((α × List Bool) × ℕ) := {x |
      ((x.1.1, x.2), (((x.1.2.drop (x.2 * M x.1.1)).take (M x.1.1)).take
        (p.eval (encPair enc encUnary (x.1.1, x.2)).length))) ∈ D}
    have hred : PolyTimeReducible (encPair (encPair enc encBits) encUnary)
        (encPair (encPair enc encUnary) encBits) C D :=
      ⟨_, by
        have hpair : ComputableInPolyTime
            (fun x : (α × List Bool) × ℕ => (x.1.1, x.2))
            (encPair (encPair enc encBits) encUnary) (encPair enc encUnary) := by fun_prop
        have hp := (ComputableInPolyTime.unary_eval p).comp
          ((ComputableInPolyTime.encoding_length _).comp hpair)
        have hm := hM.comp (ComputableInPolyTime.fst (encPair enc encBits) encUnary).fst'
        have hoff : ComputableInPolyTime (fun x : (α × List Bool) × ℕ => x.2 * M x.1.1)
            (encPair (encPair enc encBits) encUnary) encUnary :=
          ComputableInPolyTime.unary_mul.comp ((ComputableInPolyTime.snd _ _).prod hm)
        have hword : ComputableInPolyTime (fun x : (α × List Bool) × ℕ => x.1.2)
            (encPair (encPair enc encBits) encUnary) encBits := by fun_prop
        exact hpair.prod
          (((hword.bitsDropWithInput hoff).bitsTakeWithInput hm).bitsTakeWithInput hp),
        fun _ => Iff.rfl⟩
    have hC := hred.mem_PiP hD
    have hAll := mem_PiP_of_forall_lt (hN.comp (.fst enc encBits)) hC
    have hE := mem_SigmaP_of_exists_length (k := k + 1) (by omega)
      (ComputableInPolyTime.unary_mul.comp (hN.prod hM))
      (PiP_subset_SigmaP_succ k hAll)
    convert hE using 1
    ext a
    have hle (i : ℕ) (hi : i < N a) :
        p.eval (encPair enc encUnary (a, i)).length ≤ M a := by
      apply Polynomial.eval_mono
      simp only [length_encPair, encUnary_apply, List.length_replicate]
      omega
    simp only [Set.mem_ofPred_eq, hBD, C]
    change (∀ i < N a, ∃ w : List Bool, w.length = p.eval (encPair enc encUnary (a, i)).length ∧
      ((a, i), w) ∈ D) ↔ ∃ w : List Bool, w.length = N a * M a ∧
        ∀ i < N a, ((a, i), (((w.drop (i * M a)).take (M a)).take
          (p.eval (encPair enc encUnary (a, i)).length))) ∈ D
    rw [exists_word_slices (N a) (M a)
      (fun i w => ((a, i), w.take (p.eval (encPair enc encUnary (a, i)).length)) ∈ D)]
    refine forall₂_congr fun i hi => ?_
    exact (List.exists_length_eq_take_iff
      (P := fun w => ((a, i), w) ∈ D) (hle i hi)).symm

end Cslib.Complexity
