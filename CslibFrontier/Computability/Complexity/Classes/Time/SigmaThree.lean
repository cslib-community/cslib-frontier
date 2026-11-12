/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Time.SigmaTwo
public import CslibFrontier.Computability.Complexity.Classes.PH
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.FunPropLists
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.LinearClock
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Degree.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Primitives
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.LinearPrimitives
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Tactic.EncLen
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The third level of the alternating time hierarchy: Σ₃TIME

The time-bounded alternating class `Cslib.Complexity.SigmaThreeTIME` mirrors `SigmaTwoTIME`
(`CslibFrontier.Computability.Complexity.Classes.Time.SigmaTwo`): a problem `A` lies in
`SigmaThreeTIME enc t` when some linear-time verifier `V` satisfies

`a ∈ A ↔ ∃ u, |u| = L ∧ ∀ v, |v| = L → ∃ w, |w| = L ∧ V (a, ⟨u, v, w⟩) = true`

for every padding length `L ≥ c * t (enc a).length + c`.

## Main definitions

* `Cslib.Complexity.SigmaThreeWitness`: the three witness/challenge blocks `(u, v, w)`.
* `Cslib.Complexity.encSigmaThreeWitness`: framed binary encoding of `SigmaThreeWitness`.
* `Cslib.Complexity.SigmaThreeTIME`: problems decidable by a linear-time verifier with an
  `∃ ∀ ∃` prefix of length `O(t)`.
* `Cslib.Complexity.evenBits`, `Cslib.Complexity.oddBits`, `Cslib.Complexity.interleave`:
  linear-time bit-splitting and interleaving helpers (used alongside `Turing.MultiTapeTM.unframe`).

## Main results

* `Cslib.Complexity.SigmaTwoTIME_subset_SigmaThreeTIME`: `Σ₂TIME(t) ⊆ Σ₃TIME(t)`.
* `Cslib.Complexity.compl_mem_SigmaThreeTIME_of_mem_SigmaTwoTIME`: `Π₂TIME(t) ⊆ Σ₃TIME(t)`.
* `Cslib.Complexity.SigmaThreeTIME_mono`,
  `Cslib.Complexity.SigmaThreeTIME_mono_of_le_mul_add`: monotonicity of the time bound.
* `Cslib.Complexity.mem_SigmaP_three_of_mem_SigmaThreeTIME`: polynomial-time `Σ₃TIME` lies in
  `Σ₃ᵖ` (`SigmaP 3`).
* `Cslib.Complexity.mem_SigmaThreeTIME_of_composition`,
  `Cslib.Complexity.mem_SigmaThreeTIME_of_composition_of_le`: the composition lemma flattening
  `∃ c (|c| ≤ s), E(x, c) ∧ ¬ B(x, c)` with `E ∈ Σ₃TIME` and `B ∈ Σ₂TIME` into `Σ₃TIME`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

/-- The three alternating bit-string blocks for a `Σ₃TIME` verifier: existential `u`, universal
`v`, and inner existential `w`. -/
structure SigmaThreeWitness where
  /-- Outer existential witness block. -/
  u : List Bool
  /-- Middle universal challenge block. -/
  v : List Bool
  /-- Inner existential response block. -/
  w : List Bool

/-- Framed binary encoding of `SigmaThreeWitness`. -/
enc_structure encSigmaThreeWitness : SigmaThreeWitness where
  u : encBits, v : encBits, w : encBits

/-- **The third level of the time-bounded alternating hierarchy**: `A ∈ SigmaThreeTIME enc t`
when a linear-time deterministic verifier `V` satisfies the `∃ u ∀ v ∃ w` condition for all block
lengths `L ≥ c * t (enc a).length + c`. -/
@[expose] def SigmaThreeTIME {α : Type} (enc : α ↪ List Bool) (t : ℕ → ℕ) : Set (Set α) :=
  {A | ∃ (V : α × SigmaThreeWitness → Bool) (c : ℕ),
    ComputableInO V (encPair enc encSigmaThreeWitness) encBool
      (fun x => (encPair enc encSigmaThreeWitness x).length)
      (fun x => (encPair enc encSigmaThreeWitness x).length) ∧
    ∀ a L, c * t (enc a).length + c ≤ L →
      (a ∈ A ↔ ∃ u : List Bool, u.length = L ∧
        ∀ v : List Bool, v.length = L →
          ∃ w : List Bool, w.length = L ∧ V (a, ⟨u, v, w⟩) = true)}

variable {α : Type} {enc : α ↪ List Bool}

theorem mem_SigmaThreeTIME_iff {t : ℕ → ℕ} {A : Set α} :
    A ∈ SigmaThreeTIME enc t ↔
      ∃ (V : α × SigmaThreeWitness → Bool) (c : ℕ),
        ComputableInO V (encPair enc encSigmaThreeWitness) encBool
          (fun x => (encPair enc encSigmaThreeWitness x).length)
          (fun x => (encPair enc encSigmaThreeWitness x).length) ∧
        ∀ a L, c * t (enc a).length + c ≤ L →
          (a ∈ A ↔ ∃ u : List Bool, u.length = L ∧
            ∀ v : List Bool, v.length = L →
              ∃ w : List Bool, w.length = L ∧ V (a, ⟨u, v, w⟩) = true) :=
  Iff.rfl

/-- Increasing the time bound cannot shrink `SigmaThreeTIME`. -/
theorem SigmaThreeTIME_mono {t₁ t₂ : ℕ → ℕ} (h : ∀ n, t₁ n ≤ t₂ n) :
    SigmaThreeTIME enc t₁ ⊆ SigmaThreeTIME enc t₂ := by
  intro A hA
  obtain ⟨V, c, hV, hA⟩ := hA
  refine ⟨V, c, hV, fun a L hL => hA a L ?_⟩
  exact (Nat.add_le_add_right (Nat.mul_le_mul_left c (h _)) c).trans hL

/-- Constant-factor and additive overhead preserves `SigmaThreeTIME`. -/
theorem SigmaThreeTIME_mono_of_le_mul_add {t₁ t₂ : ℕ → ℕ} {C : ℕ}
    (h : ∀ n, t₁ n ≤ C * t₂ n + C) :
    SigmaThreeTIME enc t₁ ⊆ SigmaThreeTIME enc t₂ := by
  intro A hA
  obtain ⟨V, c, hV, hA⟩ := hA
  refine ⟨V, c * (C + 1), hV, fun a L hL => hA a L ?_⟩
  have ha := Nat.mul_le_mul_left c (h (enc a).length)
  nlinarith

/-- **`Σ₂TIME(t) ⊆ Σ₃TIME(t)`**: ignore the third block. -/
theorem SigmaTwoTIME_subset_SigmaThreeTIME (enc : α ↪ List Bool) (t : ℕ → ℕ) :
    SigmaTwoTIME enc t ⊆ SigmaThreeTIME enc t := by
  intro A hA
  rw [mem_SigmaTwoTIME_iff] at hA
  obtain ⟨V, c, hV, hA⟩ := hA
  refine ⟨fun x => V (x.1, (x.2.u, x.2.v)), c, ?_, fun a L hL => ?_⟩
  · have ha : ComputableInO (fun x : α × SigmaThreeWitness => x.1)
        (encPair enc encSigmaThreeWitness) enc
        (fun x => (encPair enc encSigmaThreeWitness x).length)
        (fun x => (encPair enc encSigmaThreeWitness x).length) := by fun_prop
    have hu : ComputableInO (fun x : α × SigmaThreeWitness => x.2.u)
        (encPair enc encSigmaThreeWitness) encBits
        (fun x => (encPair enc encSigmaThreeWitness x).length)
        (fun x => (encPair enc encSigmaThreeWitness x).length) :=
      encSigmaThreeWitness_u_inO.comp_linear (ComputableInO.snd enc encSigmaThreeWitness)
    have hv : ComputableInO (fun x : α × SigmaThreeWitness => x.2.v)
        (encPair enc encSigmaThreeWitness) encBits
        (fun x => (encPair enc encSigmaThreeWitness x).length)
        (fun x => (encPair enc encSigmaThreeWitness x).length) :=
      encSigmaThreeWitness_v_inO.comp_linear (ComputableInO.snd enc encSigmaThreeWitness)
    exact hV.comp_linear ((ha.prod (hu.prod hv)).mono 3 (fun _ => by omega) (fun _ => by omega))
  · rw [hA a L hL]
    constructor
    · rintro ⟨u, hu, hvu⟩
      refine ⟨u, hu, fun v hv => ⟨List.replicate L false, by simp, hvu v hv⟩⟩
    · rintro ⟨u, hu, hvu⟩
      refine ⟨u, hu, fun v hv => ?_⟩
      obtain ⟨_, -, hw⟩ := hvu v hv
      exact hw

/-- **`Π₂TIME(t) ⊆ Σ₃TIME(t)`**: complementing a `Σ₂TIME(t)` problem flips `∃ ∀` to `∀ ∃`,
with a dummy outer existential block. -/
theorem compl_mem_SigmaThreeTIME_of_mem_SigmaTwoTIME {t : ℕ → ℕ} {A : Set α}
    (hA : A ∈ SigmaTwoTIME enc t) : Aᶜ ∈ SigmaThreeTIME enc t := by
  rw [mem_SigmaTwoTIME_iff] at hA
  obtain ⟨V, c, hV, hspec⟩ := hA
  refine ⟨fun x => !(V (x.1, (x.2.v, x.2.w))), c, ?_, fun a L hL => ?_⟩
  · have ha : ComputableInO (fun x : α × SigmaThreeWitness => x.1)
        (encPair enc encSigmaThreeWitness) enc
        (fun x => (encPair enc encSigmaThreeWitness x).length)
        (fun x => (encPair enc encSigmaThreeWitness x).length) := by fun_prop
    have hv : ComputableInO (fun x : α × SigmaThreeWitness => x.2.v)
        (encPair enc encSigmaThreeWitness) encBits
        (fun x => (encPair enc encSigmaThreeWitness x).length)
        (fun x => (encPair enc encSigmaThreeWitness x).length) :=
      encSigmaThreeWitness_v_inO.comp_linear (ComputableInO.snd enc encSigmaThreeWitness)
    have hw : ComputableInO (fun x : α × SigmaThreeWitness => x.2.w)
        (encPair enc encSigmaThreeWitness) encBits
        (fun x => (encPair enc encSigmaThreeWitness x).length)
        (fun x => (encPair enc encSigmaThreeWitness x).length) :=
      encSigmaThreeWitness_w_inO.comp_linear (ComputableInO.snd enc encSigmaThreeWitness)
    exact ComputableInO.not'
      (hV.comp_linear ((ha.prod (hv.prod hw)).mono 3 (fun _ => by omega) (fun _ => by omega)))
  · rw [Set.mem_compl_iff, hspec a L hL]
    push Not
    constructor
    · intro h
      refine ⟨List.replicate L false, by simp, fun v hv => ?_⟩
      obtain ⟨w, hw, hwv⟩ := h v hv
      exact ⟨w, hw, by simp [hwv]⟩
    · intro h v hv
      rcases h with ⟨_, -, h⟩
      obtain ⟨w, hw, hwv⟩ := h v hv
      refine ⟨w, hw, ?_⟩
      simpa using hwv

/-- Polynomial-time `SigmaThreeTIME` is contained in the third level `Σ₃ᵖ` of the polynomial
hierarchy. -/
theorem mem_SigmaP_three_of_mem_SigmaThreeTIME {k : ℕ} {A : Set α}
    (hA : A ∈ SigmaThreeTIME enc fun n => (n + 1) ^ k) : A ∈ SigmaP 3 enc := by
  obtain ⟨V, c, hV, hspec⟩ := hA
  let p : Polynomial ℕ := Polynomial.C c * (Polynomial.X + 1) ^ k + Polynomial.C c
  have hp_eval (a : α) : p.eval (enc a).length = c * ((enc a).length + 1) ^ k + c := by
    simp [p]
  let V' : α × List Bool → Bool := fun x =>
    let L := p.eval (enc x.1).length
    V (x.1, ⟨x.2.take L, (x.2.drop L).take L, (x.2.drop (2 * L)).take L⟩)
  refine ⟨[p, p, p], V', rfl, ?_, fun a => ?_⟩
  · have ha_len : ComputableInPolyTime (fun x : α × List Bool => (enc x.1).length)
        (encPair enc encBits) encUnary :=
      (ComputableInPolyTime.encoding_length enc).comp (ComputableInPolyTime.fst enc encBits)
    have hL : ComputableInPolyTime (fun x : α × List Bool => p.eval (enc x.1).length)
        (encPair enc encBits) encUnary :=
      (ComputableInPolyTime.unary_eval p).comp ha_len
    have h2L : ComputableInPolyTime (fun x : α × List Bool => 2 * p.eval (enc x.1).length)
        (encPair enc encBits) encUnary := by
      have hC : ComputableInPolyTime (fun n : ℕ => (Polynomial.C 2 * Polynomial.X).eval n)
          encUnary encUnary := ComputableInPolyTime.unary_eval (Polynomial.C 2 * Polynomial.X)
      exact (hC.comp hL).of_enc_eq fun x => by simp
    have hu : ComputableInPolyTime (fun x : α × List Bool => x.2.take (p.eval (enc x.1).length))
        (encPair enc encBits) encBits :=
      ComputableInPolyTime.bitsTakeWithInput (.snd enc encBits) hL
    have hv : ComputableInPolyTime
        (fun x : α × List Bool =>
          (x.2.drop (p.eval (enc x.1).length)).take (p.eval (enc x.1).length))
        (encPair enc encBits) encBits :=
      ComputableInPolyTime.bitsTakeWithInput
        (ComputableInPolyTime.bitsDropWithInput (.snd enc encBits) hL) hL
    have hw : ComputableInPolyTime
        (fun x : α × List Bool =>
          (x.2.drop (2 * p.eval (enc x.1).length)).take (p.eval (enc x.1).length))
        (encPair enc encBits) encBits :=
      ComputableInPolyTime.bitsTakeWithInput
        (ComputableInPolyTime.bitsDropWithInput (.snd enc encBits) h2L) hL
    have hwit : ComputableInPolyTime
        (fun x : α × List Bool =>
          SigmaThreeWitness.mk (x.2.take (p.eval (enc x.1).length))
            ((x.2.drop (p.eval (enc x.1).length)).take (p.eval (enc x.1).length))
            ((x.2.drop (2 * p.eval (enc x.1).length)).take (p.eval (enc x.1).length)))
        (encPair enc encBits) encSigmaThreeWitness :=
      encSigmaThreeWitness_mk_polyTime hu hv hw
    have hV_poly : ComputableInPolyTime V (encPair enc encSigmaThreeWitness) encBool :=
      hV.computableInPolyTime ⟨id, by fun_prop, fun _ => le_rfl⟩ ⟨id, by fun_prop, fun _ => le_rfl⟩
    exact hV_poly.comp ((ComputableInPolyTime.fst enc encBits).prod hwit)
  · rw [hspec a (p.eval (enc a).length) (hp_eval a).ge]
    simp only [List.map_cons, List.map_nil, alternation_true_cons, Alternation, List.append_nil]
    refine exists_congr fun u => and_congr_right fun hu =>
      forall_congr' fun v => forall_congr' fun hv =>
        exists_congr fun w => and_congr_right fun hw => ?_
    have h1 : (u ++ (v ++ w)).take (p.eval (enc a).length) = u := by
      rw [← hu]
      exact List.take_left
    have h2 : ((u ++ (v ++ w)).drop (p.eval (enc a).length)).take (p.eval (enc a).length) = v := by
      rw [show (u ++ (v ++ w)).drop (p.eval (enc a).length) = v ++ w from hu ▸ List.drop_left,
        ← hv]
      exact List.take_left
    have h3 :
        ((u ++ (v ++ w)).drop (2 * p.eval (enc a).length)).take (p.eval (enc a).length) = w := by
      have huv : (u ++ v).length = 2 * p.eval (enc a).length := by simp [hu, hv, two_mul]
      rw [← List.append_assoc, ← huv, List.drop_left, ← hw, List.take_length]
    dsimp only [V']
    rw [h1, h2, h3]

/-! ### Linear-time splitting and prefix-unframing transducers -/

section Transducers

/-- Even-indexed pairs' first coordinates from a bit string. -/
def evenBits : List Bool → List Bool
  | a :: _ :: xs => a :: evenBits xs
  | _ => []

/-- Even-indexed pairs' second coordinates from a bit string. -/
def oddBits : List Bool → List Bool
  | _ :: b :: xs => b :: oddBits xs
  | _ => []

/-- Interleave two equal-length bit strings bit by bit. -/
def interleave : List Bool → List Bool → List Bool
  | a :: xs, b :: ys => a :: b :: interleave xs ys
  | _, _ => []

@[simp]
theorem length_evenBits (l : List Bool) : (evenBits l).length = l.length / 2 := by
  match l with
  | [] => simp [evenBits]
  | [_] => simp [evenBits]
  | _ :: _ :: xs =>
    simp only [evenBits, List.length_cons, length_evenBits xs]
    omega

@[simp]
theorem length_oddBits (l : List Bool) : (oddBits l).length = l.length / 2 := by
  match l with
  | [] => simp [oddBits]
  | [_] => simp [oddBits]
  | _ :: _ :: xs =>
    simp only [oddBits, List.length_cons, length_oddBits xs]
    omega

theorem length_interleave {xs ys : List Bool} (h : xs.length = ys.length) :
    (interleave xs ys).length = 2 * xs.length := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all [interleave]
  | cons a xs ih =>
    cases ys with
    | nil => simp at h
    | cons b ys =>
      simp only [interleave, List.length_cons] at h ⊢
      have := ih (Nat.succ.inj h)
      omega

theorem evenBits_interleave_append {xs ys pad : List Bool} (h : xs.length = ys.length)
    (hpad : pad.length ≤ 1) : evenBits (interleave xs ys ++ pad) = xs := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil =>
      cases pad with
      | nil => rfl
      | cons b bs =>
        cases bs with
        | nil => rfl
        | cons _ _ => simp at hpad
    | cons _ _ => simp at h
  | cons a xs ih =>
    cases ys with
    | nil => simp at h
    | cons b ys =>
      simp only [interleave, List.cons_append, evenBits]
      congr 1
      exact ih (by simp_all)

theorem oddBits_interleave_append {xs ys pad : List Bool} (h : xs.length = ys.length)
    (hpad : pad.length ≤ 1) : oddBits (interleave xs ys ++ pad) = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil =>
      cases pad with
      | nil => rfl
      | cons b bs =>
        cases bs with
        | nil => rfl
        | cons _ _ => simp at hpad
    | cons _ _ => simp at h
  | cons a xs ih =>
    cases ys with
    | nil => simp at h
    | cons b ys =>
      simp only [interleave, List.cons_append, oddBits]
      congr 1
      exact ih (by simp_all)

private theorem two_mul_length_unframe_le (l : List Bool) :
    2 * (unframe l).length ≤ l.length := by
  match l with
  | [] => simp [unframe]
  | [false] => simp [unframe]
  | [true] => simp [unframe]
  | false :: _ :: _ => simp [unframe]
  | true :: _ :: xs =>
    simp only [unframe, List.length_cons]
    have := two_mul_length_unframe_le xs
    omega

private def evenBitsT : Transducer Bool (Option Bool) where
  q₀ := none
  step q b := match q with
    | none => (some b, [])
    | some a => (none, [a])
  final _ := []
  length_step_le q b := by
    rcases q with _ | a
    · cases b <;> decide
    · cases a <;> cases b <;> decide
  length_final_le _ := by decide

private theorem evenBitsT_run (l : List Bool) : evenBitsT.run none l = evenBits l := by
  match l with
  | [] => rfl
  | [a] => rfl
  | a :: b :: xs =>
    change [a] ++ evenBitsT.run none xs = a :: evenBits xs
    rw [evenBitsT_run xs]
    rfl

private def oddBitsT : Transducer Bool Bool where
  q₀ := false
  step q b := if q then (false, [b]) else (true, [])
  final _ := []
  length_step_le q b := by cases q <;> cases b <;> decide
  length_final_le _ := by decide

private theorem oddBitsT_run (l : List Bool) : oddBitsT.run false l = oddBits l := by
  match l with
  | [] => rfl
  | [a] => rfl
  | a :: b :: xs =>
    change [b] ++ oddBitsT.run false xs = b :: oddBits xs
    rw [oddBitsT_run xs]
    rfl

/-- Extract the even-indexed halves in linear time and space. -/
theorem computableInO_evenBits :
    ComputableInO evenBits encBits encBits (fun w => w.length) (fun w => w.length) :=
  (ComputableInDegree.of_transducer evenBitsT fun l => (evenBitsT_run l).symm).inO_one

/-- Extract the odd-indexed halves in linear time and space. -/
theorem computableInO_oddBits :
    ComputableInO oddBits encBits encBits (fun w => w.length) (fun w => w.length) :=
  (ComputableInDegree.of_transducer oddBitsT fun l => (oddBitsT_run l).symm).inO_one

end Transducers

/-! ### The Composition Lemma (Hint 1) -/

/-- **Composition lemma for `SigmaThreeTIME`**: if `a ∈ A` iff there is a short switch witness `c`
of length at most `s |enc a| ≤ O(t |enc a|)` (with `s` unary-computable in `O(n + t n)` time) such
that `(a, c) ∈ E` (`E ∈ Σ₃TIME(tE)`) and `(a, c) ∉ B` (`B ∈ Σ₂TIME(tB)`), where both `tE` and `tB`
on short pairs are `O(n + t n)`, then `A ∈ Σ₃TIME(n + t n)`. -/
theorem mem_SigmaThreeTIME_of_composition {A : Set α} {E B : Set (α × List Bool)}
    {t s tE tB : ℕ → ℕ} {Cs KE KB : ℕ}
    (hs_le : ∀ n, s n ≤ Cs * t n + Cs)
    (hs : ComputableInO (fun x : List Bool => s x.length) encBits encUnary
      (fun x => x.length + t x.length) (fun x => x.length + t x.length))
    (hE : E ∈ SigmaThreeTIME (encPair enc encBits) tE)
    (htE : ∀ a (c : List Bool), c.length ≤ s (enc a).length →
      tE (encPair enc encBits (a, c)).length ≤ KE * ((enc a).length + t (enc a).length) + KE)
    (hB : B ∈ SigmaTwoTIME (encPair enc encBits) tB)
    (htB : ∀ a (c : List Bool), c.length ≤ s (enc a).length →
      tB (encPair enc encBits (a, c)).length ≤ KB * ((enc a).length + t (enc a).length) + KB)
    (hdom : ∀ a (c : List Bool), (a, c) ∈ E → c.length ≤ s (enc a).length)
    (hA : ∀ a, a ∈ A ↔ ∃ c : List Bool, (a, c) ∈ E ∧ (a, c) ∉ B) :
    A ∈ SigmaThreeTIME enc (fun n => n + t n) := by
  obtain ⟨VE, cE, hVE, hEspec⟩ := hE
  rw [mem_SigmaTwoTIME_iff] at hB
  obtain ⟨VB, cB, hVB, hBspec⟩ := hB
  let cOf : α × SigmaThreeWitness → List Bool := fun x => unframe (evenBits x.2.u)
  let okLen : α × SigmaThreeWitness → Bool :=
    fun x => ((cOf x).drop (s (enc x.1).length)).isEmpty
  let V_raw : α × SigmaThreeWitness → Bool := fun x =>
    if okLen x = true then
      VE ((x.1, cOf x), ⟨oddBits x.2.u, evenBits x.2.v, evenBits x.2.w⟩) &&
        !(VB ((x.1, cOf x), (oddBits x.2.v, oddBits x.2.w)))
    else false
  -- helper bounds on extracted parts against N x
  let N : α × SigmaThreeWitness → ℕ := fun x => (encPair enc encSigmaThreeWitness x).length
  have hlen_parts (x : α × SigmaThreeWitness) :
      (enc x.1).length ≤ N x ∧ x.2.u.length ≤ N x ∧ x.2.v.length ≤ N x ∧
        x.2.w.length ≤ N x ∧ (cOf x).length ≤ N x ∧
        (oddBits x.2.u).length ≤ N x ∧ (evenBits x.2.v).length ≤ N x ∧
        (oddBits x.2.v).length ≤ N x ∧ (evenBits x.2.w).length ≤ N x ∧
        (oddBits x.2.w).length ≤ N x := by
    have hc1 := two_mul_length_unframe_le (evenBits x.2.u)
    have hc2 := length_evenBits x.2.u
    have h1 := length_evenBits x.2.v
    have h2 := length_oddBits x.2.u
    have h3 := length_oddBits x.2.v
    have h4 := length_evenBits x.2.w
    have h5 := length_oddBits x.2.w
    dsimp only [N, cOf]
    enc_len [encSigmaThreeWitness_apply]
  have hunframe : ComputableInO unframe encBits encBits
      (fun w => w.length) (fun w => w.length) :=
    (ComputableInDegree.of_unframe (f := unframe) (encIn := encBits) (encMid := encBits)
      fun _ => rfl).inO_one
  have hok_computable : ComputableInO okLen (encPair enc encSigmaThreeWitness) encBool
      (fun x => (20 + Cs) * (N x + t (enc x.1).length) + (20 + Cs))
      (fun x => (20 + Cs) * (N x + t (enc x.1).length) + (20 + Cs)) := by
    have hf : ComputableInO (fun x : α × SigmaThreeWitness => enc x.1)
        (encPair enc encSigmaThreeWitness) encBits N N :=
      (ComputableInO.of_eq (f := enc) (encIn := enc) (encMid := encBits)
        fun _ => rfl).comp_linear (ComputableInO.fst enc encSigmaThreeWitness)
    have hu : ComputableInO (fun x : α × SigmaThreeWitness => x.2.u)
        (encPair enc encSigmaThreeWitness) encBits N N :=
      encSigmaThreeWitness_u_inO.comp_linear (ComputableInO.snd enc encSigmaThreeWitness)
    have hc : ComputableInO cOf (encPair enc encSigmaThreeWitness) encBits N N :=
      hunframe.comp_linear (computableInO_evenBits.comp_linear hu)
    have hcList : ComputableInO cOf (encPair enc encSigmaThreeWitness) (encList encBool) N N :=
      (ComputableInDegree.bitsToList.inO_one).comp_linear hc
    have hsBound : ComputableInO (fun x : α × SigmaThreeWitness => s (enc x.1).length)
        (encPair enc encSigmaThreeWitness) encUnary
        (fun x => N x + ((enc x.1).length + t (enc x.1).length))
        (fun x => N x + ((enc x.1).length + t (enc x.1).length)) :=
      hs.comp' hf
    have hdrop := ComputableInO.drop' hcList hsBound
    have his := ComputableInO.isEmpty' hdrop
    refine his.mono 1 (fun x => ?_) (fun x => ?_)
    all_goals
      have hpa := (hlen_parts x).1
      have hpc := (hlen_parts x).2.2.2.2.1
      have hsl := hs_le (enc x.1).length
      have hl1 : (encList encBool (cOf x)).length ≤ (cOf x).length * 3 :=
        length_encList_le encBool (cOf x) (b := 1) fun _ _ => by simp [encBool_apply]
      have hl2 : (encList encBool ((cOf x).drop (s (enc x.1).length))).length ≤
          ((cOf x).drop (s (enc x.1).length)).length * 3 :=
        length_encList_le encBool _ (b := 1) fun _ _ => by simp [encBool_apply]
      have hdl : ((cOf x).drop (s (enc x.1).length)).length ≤ (cOf x).length := by simp
      simp only [length_encPair, encUnary_apply, List.length_replicate]
      nlinarith
  have hthen_computable : ComputableInO
      (fun x : α × SigmaThreeWitness =>
        VE ((x.1, cOf x), ⟨oddBits x.2.u, evenBits x.2.v, evenBits x.2.w⟩) &&
          !(VB ((x.1, cOf x), (oddBits x.2.v, oddBits x.2.w))))
      (encPair enc encSigmaThreeWitness) encBool N N := by
    have ha : ComputableInO (fun x : α × SigmaThreeWitness => x.1)
        (encPair enc encSigmaThreeWitness) enc N N := by fun_prop
    have hu : ComputableInO (fun x : α × SigmaThreeWitness => x.2.u)
        (encPair enc encSigmaThreeWitness) encBits N N :=
      encSigmaThreeWitness_u_inO.comp_linear (ComputableInO.snd enc encSigmaThreeWitness)
    have hv : ComputableInO (fun x : α × SigmaThreeWitness => x.2.v)
        (encPair enc encSigmaThreeWitness) encBits N N :=
      encSigmaThreeWitness_v_inO.comp_linear (ComputableInO.snd enc encSigmaThreeWitness)
    have hw : ComputableInO (fun x : α × SigmaThreeWitness => x.2.w)
        (encPair enc encSigmaThreeWitness) encBits N N :=
      encSigmaThreeWitness_w_inO.comp_linear (ComputableInO.snd enc encSigmaThreeWitness)
    have hc : ComputableInO cOf (encPair enc encSigmaThreeWitness) encBits N N :=
      hunframe.comp_linear (computableInO_evenBits.comp_linear hu)
    have hu' := computableInO_oddBits.comp_linear hu
    have hv' := computableInO_evenBits.comp_linear hv
    have hp := computableInO_oddBits.comp_linear hv
    have hw' := computableInO_evenBits.comp_linear hw
    have hq := computableInO_oddBits.comp_linear hw
    have hac : ComputableInO (fun x : α × SigmaThreeWitness => (x.1, cOf x))
        (encPair enc encSigmaThreeWitness) (encPair enc encBits)
        (fun x => N x + N x) (fun x => N x + N x) := ha.prod hc
    have hwit : ComputableInO
        (fun x : α × SigmaThreeWitness => SigmaThreeWitness.mk (oddBits x.2.u)
          (evenBits x.2.v) (evenBits x.2.w))
        (encPair enc encSigmaThreeWitness) encSigmaThreeWitness
        (fun x => N x + (N x + N x)) (fun x => N x + (N x + N x)) :=
      encSigmaThreeWitness_mk_inO hu' hv' hw'
    have hEarg : ComputableInO
        (fun x : α × SigmaThreeWitness =>
          ((x.1, cOf x), SigmaThreeWitness.mk (oddBits x.2.u) (evenBits x.2.v) (evenBits x.2.w)))
        (encPair enc encSigmaThreeWitness)
        (encPair (encPair enc encBits) encSigmaThreeWitness) N N :=
      (hac.prod hwit).mono 5 (fun _ => by omega) (fun _ => by omega)
    have hBarg : ComputableInO
        (fun x : α × SigmaThreeWitness => ((x.1, cOf x), (oddBits x.2.v, oddBits x.2.w)))
        (encPair enc encSigmaThreeWitness)
        (encPair (encPair enc encBits) (encPair encBits encBits)) N N :=
      (hac.prod (hp.prod hq)).mono 4 (fun _ => by omega) (fun _ => by omega)
    exact (ComputableInO.and' (hVE.comp_linear hEarg)
        (ComputableInO.not' (hVB.comp_linear hBarg))).mono
      2 (fun _ => by omega) (fun _ => by omega)
  have hraw : ComputableInO V_raw (encPair enc encSigmaThreeWitness) encBool
      (fun x => N x + t (enc x.1).length) (fun x => N x + t (enc x.1).length) := by
    have hfalse : ComputableInO (fun _ : α × SigmaThreeWitness => false)
        (encPair enc encSigmaThreeWitness) encBool N N :=
      (ComputableInO.const false).mono_le (fun _ => le_rfl) (fun _ => le_rfl)
    have hite := hok_computable.ite hthen_computable hfalse
    exact hite.mono (22 + Cs)
      (fun x => by split_ifs <;> nlinarith)
      (fun x => by split_ifs <;> nlinarith)
  obtain ⟨V, hV, hV_eq⟩ := hraw.exists_linear_eq_of_time_le 2
  let Ctot : ℕ := 2 * (max (2 * Cs + 3) (max (cE * KE + cE) (cB * KB + cB))) + 2
  have hCtot2 : 2 ≤ Ctot := by dsimp only [Ctot]; omega
  refine ⟨V, Ctot, hV, fun a L hL => ?_⟩
  have hV_agree (wit : SigmaThreeWitness) (hLu : wit.u.length = L) :
      V (a, wit) = V_raw (a, wit) := by
    apply hV_eq
    have ht_le_L : t (enc a).length ≤ L := by nlinarith
    have hL_le_N : L ≤ N (a, wit) := by
      dsimp only [N]
      rw [← hLu]
      enc_len [encSigmaThreeWitness_apply]
    change N (a, wit) + t (enc a).length ≤ 2 * N (a, wit) + 2
    omega
  set M := L / 2 with hM
  have hrem_le : L - 2 * M ≤ 1 := by omega
  have hM2 : L ≤ 2 * M + 1 := by omega
  have hM_s : 2 * s (enc a).length + 1 ≤ M := by
    have hs_a := hs_le (enc a).length
    have hmax := Nat.le_max_left (2 * Cs + 3) (max (cE * KE + cE) (cB * KB + cB))
    have hCtot_s : 2 * (2 * Cs + 3) + 2 ≤ Ctot := by dsimp only [Ctot]; omega
    have h1 : 2 * (2 * Cs + 3) * ((enc a).length + t (enc a).length) +
        (2 * (2 * Cs + 3) + 2) ≤ 2 * M + 1 := by nlinarith
    nlinarith
  have hM_E (c : List Bool) (hc : c.length ≤ s (enc a).length) :
      cE * tE (encPair enc encBits (a, c)).length + cE ≤ M := by
    have ht := htE a c hc
    have hmax1 := le_max_left (cE * KE + cE) (cB * KB + cB)
    have hmax2 := le_max_right (2 * Cs + 3) (max (cE * KE + cE) (cB * KB + cB))
    have hCtot_E : 2 * (cE * KE + cE) + 2 ≤ Ctot := by dsimp only [Ctot]; omega
    have h1 : 2 * (cE * KE + cE) * ((enc a).length + t (enc a).length) +
        (2 * (cE * KE + cE) + 2) ≤ 2 * M + 1 := by nlinarith
    nlinarith
  have hM_B (c : List Bool) (hc : c.length ≤ s (enc a).length) :
      cB * tB (encPair enc encBits (a, c)).length + cB ≤ M := by
    have ht := htB a c hc
    have hmax1 := le_max_right (cE * KE + cE) (cB * KB + cB)
    have hmax2 := le_max_right (2 * Cs + 3) (max (cE * KE + cE) (cB * KB + cB))
    have hCtot_B : 2 * (cB * KB + cB) + 2 ≤ Ctot := by dsimp only [Ctot]; omega
    have h1 : 2 * (cB * KB + cB) * ((enc a).length + t (enc a).length) +
        (2 * (cB * KB + cB) + 2) ≤ 2 * M + 1 := by nlinarith
    nlinarith
  have hok_iff (U : List Bool) :
      okLen (a, ⟨U, [], []⟩) = true ↔ (unframe (evenBits U)).length ≤ s (enc a).length := by
    simp [okLen, cOf, List.isEmpty_iff, List.drop_eq_nil_iff]
  constructor
  · intro ha
    obtain ⟨c, hcE, hcB⟩ := (hA a).mp ha
    have hc_le : c.length ≤ s (enc a).length := hdom a c hcE
    have hframe_le : (frame c).length ≤ M := by
      rw [length_frame]
      omega
    obtain ⟨u', hu', hEu'⟩ := (hEspec (a, c) M (hM_E c hc_le)).mp hcE
    have hcB_neg : ∀ p : List Bool, p.length = M → ∃ q : List Bool, q.length = M ∧
        VB ((a, c), (p, q)) = false := by
      intro p hp
      have hnot : ¬ (a, c) ∈ B := hcB
      rw [hBspec (a, c) M (hM_B c hc_le)] at hnot
      push Not at hnot
      obtain ⟨q, hq, hqf⟩ := hnot p hp
      exact ⟨q, hq, by simpa using hqf⟩
    let seg := frame c ++ List.replicate (M - (frame c).length) false
    have hseg_len : seg.length = M := by
      simp only [seg, List.length_append, List.length_replicate]
      omega
    let pad := List.replicate (L - 2 * M) false
    let U := interleave seg u' ++ pad
    have hU_len : U.length = L := by
      simp only [U, List.length_append, length_interleave (hseg_len.trans hu'.symm),
        hseg_len, pad, List.length_replicate]
      omega
    refine ⟨U, hU_len, fun V_chal hV_len => ?_⟩
    let v' := evenBits V_chal
    let p := oddBits V_chal
    have hv' : v'.length = M := by simp [v', hV_len, hM]
    have hp : p.length = M := by simp [p, hV_len, hM]
    obtain ⟨w', hw', hEw'⟩ := hEu' v' hv'
    obtain ⟨q, hq, hBq⟩ := hcB_neg p hp
    let W := interleave w' q ++ pad
    have hW_len : W.length = L := by
      simp only [W, List.length_append, length_interleave (hw'.trans hq.symm),
        hw', pad, List.length_replicate]
      omega
    refine ⟨W, hW_len, ?_⟩
    rw [hV_agree ⟨U, V_chal, W⟩ hU_len]
    have hpad_le : pad.length ≤ 1 := by simp [pad, hrem_le]
    have hevU : evenBits U = seg := evenBits_interleave_append (hseg_len.trans hu'.symm) hpad_le
    have hodU : oddBits U = u' := oddBits_interleave_append (hseg_len.trans hu'.symm) hpad_le
    have hc_eq : cOf (a, ⟨U, V_chal, W⟩) = c := by
      simp only [cOf, hevU, seg]
      exact unframe_frame_append c _
    have hevW : evenBits W = w' := evenBits_interleave_append (hw'.trans hq.symm) hpad_le
    have hodW : oddBits W = q := oddBits_interleave_append (hw'.trans hq.symm) hpad_le
    have hok : okLen (a, ⟨U, V_chal, W⟩) = true := by
      simpa [okLen, hc_eq] using hc_le
    simp only [V_raw, hok, ↓reduceIte, hc_eq, hodU, v', hevW, p, hodW, hEw', hBq, Bool.not_false,
      Bool.and_self]
  · rintro ⟨U, hU_len, hU⟩
    let V₀ := List.replicate L false
    have hV₀_len : V₀.length = L := List.length_replicate
    obtain ⟨W₀, -, hW₀⟩ := hU V₀ hV₀_len
    rw [hV_agree ⟨U, V₀, W₀⟩ hU_len] at hW₀
    have hok_true : okLen (a, ⟨U, V₀, W₀⟩) = true := by
      by_contra hfalse
      simp [V_raw, hfalse] at hW₀
    let c := unframe (evenBits U)
    have hc_le : c.length ≤ s (enc a).length := by
      simpa [okLen, cOf, c, List.isEmpty_iff, List.drop_eq_nil_iff] using hok_true
    let u' := oddBits U
    have hu' : u'.length = M := by simp [u', hU_len, hM]
    let pad := List.replicate (L - 2 * M) false
    have hpad_le : pad.length ≤ 1 := by simp [pad, hrem_le]
    refine (hA a).mpr ⟨c, ?_, ?_⟩
    · rw [hEspec (a, c) M (hM_E c hc_le)]
      refine ⟨u', hu', fun v' hv' => ?_⟩
      let V_chal := interleave v' (List.replicate M false) ++ pad
      have hV_len : V_chal.length = L := by
        simp only [V_chal, List.length_append,
          length_interleave (hv'.trans (List.length_replicate (n := M) (a := false)).symm),
          hv', pad, List.length_replicate]
        omega
      obtain ⟨W, hW_len, hVW⟩ := hU V_chal hV_len
      rw [hV_agree ⟨U, V_chal, W⟩ hU_len] at hVW
      have hok : okLen (a, ⟨U, V_chal, W⟩) = true := by
        simpa [okLen, cOf, c] using hc_le
      simp only [V_raw, hok, ↓reduceIte, Bool.and_eq_true, Bool.not_eq_true'] at hVW
      have hevV : evenBits V_chal = v' :=
        evenBits_interleave_append (hv'.trans List.length_replicate.symm) hpad_le
      refine ⟨evenBits W, by simp [hW_len, hM], ?_⟩
      simpa [cOf, c, u', hevV] using hVW.1
    · rw [hBspec (a, c) M (hM_B c hc_le)]
      push Not
      intro p hp
      let V_chal := interleave (List.replicate M false) p ++ pad
      have hV_len : V_chal.length = L := by
        simp only [V_chal, List.length_append,
          length_interleave ((List.length_replicate (n := M) (a := false)).trans hp.symm),
          List.length_replicate, pad]
        omega
      obtain ⟨W, hW_len, hVW⟩ := hU V_chal hV_len
      rw [hV_agree ⟨U, V_chal, W⟩ hU_len] at hVW
      have hok : okLen (a, ⟨U, V_chal, W⟩) = true := by
        simpa [okLen, cOf, c] using hc_le
      simp only [V_raw, hok, ↓reduceIte, Bool.and_eq_true, Bool.not_eq_true'] at hVW
      have hodV : oddBits V_chal = p :=
        oddBits_interleave_append (List.length_replicate.trans hp.symm) hpad_le
      refine ⟨oddBits W, by simp [hW_len, hM], ?_⟩
      simpa [cOf, c, hodV] using hVW.2

/-- Corollary of the composition lemma when the time bound `t` already dominates input length. -/
theorem mem_SigmaThreeTIME_of_composition_of_le {A : Set α} {E B : Set (α × List Bool)}
    {t s tE tB : ℕ → ℕ} {Cs KE KB : ℕ}
    (ht_dom : ∀ n, n ≤ t n)
    (hs_le : ∀ n, s n ≤ Cs * t n + Cs)
    (hs : ComputableInO (fun x : List Bool => s x.length) encBits encUnary
      (fun x => x.length + t x.length) (fun x => x.length + t x.length))
    (hE : E ∈ SigmaThreeTIME (encPair enc encBits) tE)
    (htE : ∀ a (c : List Bool), c.length ≤ s (enc a).length →
      tE (encPair enc encBits (a, c)).length ≤ KE * ((enc a).length + t (enc a).length) + KE)
    (hB : B ∈ SigmaTwoTIME (encPair enc encBits) tB)
    (htB : ∀ a (c : List Bool), c.length ≤ s (enc a).length →
      tB (encPair enc encBits (a, c)).length ≤ KB * ((enc a).length + t (enc a).length) + KB)
    (hdom : ∀ a (c : List Bool), (a, c) ∈ E → c.length ≤ s (enc a).length)
    (hA : ∀ a, a ∈ A ↔ ∃ c : List Bool, (a, c) ∈ E ∧ (a, c) ∉ B) :
    A ∈ SigmaThreeTIME enc t :=
  SigmaThreeTIME_mono_of_le_mul_add (C := 2) (fun n => by have := ht_dom n; omega)
    (mem_SigmaThreeTIME_of_composition hs_le hs hE htE hB htB hdom hA)

end Cslib.Complexity
