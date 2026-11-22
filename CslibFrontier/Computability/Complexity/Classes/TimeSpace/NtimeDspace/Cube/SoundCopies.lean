/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cube.SoundCodes

/-!
# Codes of argument tuples and of copies

* `argCode`: the code of the labels of a node; `decodeArgs_argCode`.
* `copiesCode`: the code of the copies held by some nodes; `sum_copies`: summing over the valid
  codes of copies is summing over the settings of the copies.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.Cube

open Finset

/-- The table entry of node `v` of a clique at the labels coded by `args`. -/
noncomputable def cEntry (C : Clique) (v args : ℕ) : ℤ :=
  if h : v < C.q then C.T ⟨v, h⟩ (decodeArgs C ⟨v, h⟩ args) else 0

theorem Setup.entryMean_eq (S : Setup) (chs : List ℕ) (v args : ℕ) :
    S.entryMean chs v args = cEntry (S.clique chs) v args := rfl

/-- The widths of the fields of an argument code of node `v`. -/
def argW (C : Clique) (v : ℕ) : ℕ → ℕ := fun u' =>
  if h : u' < C.q ∧ v < C.q then (if u' = v then 0 else codeWidth (budget C.a ⟨v, h.2⟩ ⟨u', h.1⟩))
  else 0

theorem argOffset_eq (C : Clique) (v u : ℕ) : argOffset C v u = Radix.off (argW C v) u := rfl

theorem argWidth_eq (C : Clique) (w : ℕ) : argWidth C w = Radix.off (argW C w) C.q := rfl

theorem slice_eq (C : Clique) (nodes : ℕ → ℕ) (ξ p : ℕ) :
    slice C nodes ξ p = Radix.dig (fun p => argWidth C (nodes p)) ξ p := rfl

theorem copiesWidth_eq (C : Clique) (nodes : ℕ → ℕ) (g : ℕ) :
    copiesWidth C nodes g = Radix.off (fun p => argWidth C (nodes p)) g := rfl

theorem argW_ne (C : Clique) (w u : Fin C.q) (h : u ≠ w) :
    argW C w u = codeWidth (budget C.a w u) := by
  unfold argW; rw [dif_pos ⟨u.isLt, w.isLt⟩, if_neg (fun e => h (Fin.ext e))]

theorem argW_self (C : Clique) (w : ℕ) : argW C w w = 0 := by
  unfold argW; split_ifs with h1 h2 <;> first | rfl | exact absurd rfl h2

/-- The field of the label to `u` in an argument code of `v`. -/
def fieldOf (C : Clique) (v u : Fin C.q) (args : ℕ) : ℕ :=
  (args / 2 ^ argOffset C v u) % 2 ^ codeWidth (budget C.a v u)

theorem fieldOf_eq (C : Clique) (v u : Fin C.q) (h : u ≠ v) (args : ℕ) :
    fieldOf C v u args = Radix.dig (argW C v) args u := by
  unfold fieldOf Radix.dig; rw [argW_ne C v u h]; rfl

theorem decodeArgs_eq (C : Clique) (v u : Fin C.q) (args : ℕ) :
    decodeArgs C v args u =
      if u = v then (0, 0) else (decodeLabel (budget C.a v u) (fieldOf C v u args)).getD
          (0, 0) := by
  unfold decodeArgs fieldOf
  by_cases h : u = v
  · simp [h]
  · simp only [h, if_false]
    cases decodeLabel _ _ <;> rfl

theorem labelWt_decodeArgs_le (C : Clique) (v u : Fin C.q) (args : ℕ) :
    labelWt (decodeArgs C v args u) ≤ budget C.a v u := by
  rw [decodeArgs_eq]
  split_ifs
  · simp [labelWt]
  · rcases hd : decodeLabel (budget C.a v u) (fieldOf C v u args) with _ | l
    · simp [labelWt]
    · exact (labelCode_decode (Nat.mod_lt _ (by positivity)) hd).1

/-! ### Argument codes -/

/-- The code of the labels of node `w`. -/
noncomputable def argCode (C : Clique) (w : Fin C.q) (lab : Fin C.q → Label) : ℕ :=
  Radix.enc (argW C w) (fun u => if hu : u < C.q then
    (if u = w.val then 0 else labelCode (budget C.a w ⟨u, hu⟩) (lab ⟨u, hu⟩)) else 0) C.q

section ArgCode

variable (C : Clique) (w : Fin C.q) (lab : Fin C.q → Label)
  (hlab : ∀ u, u ≠ w → labelWt (lab u) ≤ budget C.a w u)
include hlab

theorem argCode_digits : ∀ j < C.q, (fun u => if hu : u < C.q then
    (if u = w.val then 0 else labelCode (budget C.a w ⟨u, hu⟩) (lab ⟨u, hu⟩)) else 0) j < 2 ^ argW C
        w j := by
  intro j hj
  simp only [dif_pos hj]
  split_ifs with hjw
  · positivity
  · have hne : (⟨j, hj⟩ : Fin C.q) ≠ w := fun e => hjw (congrArg Fin.val e)
    have e : argW C w j = codeWidth (budget C.a w ⟨j, hj⟩) := argW_ne C w ⟨j, hj⟩ hne
    rw [e]
    exact labelCode_lt (hlab _ hne)

theorem argCode_lt : argCode C w lab < 2 ^ argWidth C w :=
  Radix.enc_lt _ _ _ (argCode_digits C w lab hlab)

theorem dig_argCode (u : Fin C.q) (h : u ≠ w) :
    Radix.dig (argW C w) (argCode C w lab) u = labelCode (budget C.a w u) (lab u) := by
  rw [argCode, Radix.dig_enc _ _ _ (argCode_digits C w lab hlab) u u.isLt]
  simp only [dif_pos u.isLt, if_neg (fun e => h (Fin.ext e))]

theorem decodeArgs_argCode (u : Fin C.q) (h : u ≠ w) : decodeArgs C w (argCode C w lab) u = lab
    u := by
  rw [decodeArgs_eq, if_neg h, fieldOf_eq C w u h, dig_argCode C w lab hlab u h,
    decode_labelCode (hlab u h)]
  rfl

end ArgCode

/-! ### Codes of copies -/

/-- The code of the copies `s p` held by the nodes `nodes p`. -/
noncomputable def copiesCode (C : Clique) (nodes : ℕ → ℕ) (g : ℕ) (s : Fin g → Fin C.q → Label) :
    ℕ :=
  Radix.enc (fun p => argWidth C (nodes p))
    (fun p => if hp : p < g ∧ nodes p < C.q then argCode C ⟨nodes p, hp.2⟩ (s ⟨p, hp.1⟩) else 0) g

section CopiesCode

variable (C : Clique) (nodes : ℕ → ℕ) (g : ℕ) (hn : ∀ p < g, nodes p < C.q)
include hn

theorem copiesCode_digits (s : Fin g → Fin C.q → Label)
    (hs : ∀ (p : Fin g) (u : Fin C.q), u.val ≠ nodes p →
      labelWt (s p u) ≤ budget C.a ⟨nodes p, hn p p.isLt⟩ u) :
    ∀ j < g, (fun p => if hp : p < g ∧ nodes p < C.q then argCode C ⟨nodes p, hp.2⟩ (s ⟨p, hp.1⟩)
      else 0) j < 2 ^ argWidth C (nodes j) := by
  intro j hj
  simp only [dif_pos (And.intro hj (hn j hj))]
  exact argCode_lt C _ _ fun u hu => hs ⟨j, hj⟩ u fun e => hu (Fin.ext e)

theorem slice_copiesCode (s : Fin g → Fin C.q → Label)
    (hs : ∀ (p : Fin g) (u : Fin C.q), u.val ≠ nodes p →
      labelWt (s p u) ≤ budget C.a ⟨nodes p, hn p p.isLt⟩ u) (p : Fin g) :
    slice C nodes (copiesCode C nodes g s) p = argCode C ⟨nodes p, hn p p.isLt⟩ (s p) := by
  rw [slice_eq, copiesCode, Radix.dig_enc _ _ _ (copiesCode_digits C nodes g hn s hs) p p.isLt,
    dif_pos (And.intro p.isLt (hn p p.isLt))]

theorem copiesCode_lt (s : Fin g → Fin C.q → Label)
    (hs : ∀ (p : Fin g) (u : Fin C.q), u.val ≠ nodes p →
      labelWt (s p u) ≤ budget C.a ⟨nodes p, hn p p.isLt⟩ u) :
    copiesCode C nodes g s < 2 ^ copiesWidth C nodes g :=
  Radix.enc_lt _ _ _ (copiesCode_digits C nodes g hn s hs)

theorem copyAt_copiesCode (s : Fin g → Fin C.q → Label)
    (hs : ∀ (p : Fin g) (u : Fin C.q), u.val ≠ nodes p →
      labelWt (s p u) ≤ budget C.a ⟨nodes p, hn p p.isLt⟩ u) (p : Fin g) (u : Fin C.q) :
    copyAt C nodes (copiesCode C nodes g s) p u = if u.val = nodes p then (0, 0) else s p u := by
  unfold copyAt
  rw [dif_pos ⟨hn p p.isLt, u.isLt⟩, slice_copiesCode C nodes g hn s hs]
  by_cases hu : u.val = nodes p
  · rw [if_pos hu, decodeArgs_eq, if_pos (Fin.ext hu)]
  · rw [if_neg hu, decodeArgs_argCode C _ _ (fun u' hu' => hs p u' fun e => hu' (Fin.ext e)) u
      (fun e => hu (congrArg Fin.val e))]

theorem copiesValid_copiesCode (s : Fin g → Fin C.q → Label)
    (hs : ∀ (p : Fin g) (u : Fin C.q), u.val ≠ nodes p →
      labelWt (s p u) = budget C.a ⟨nodes p, hn p p.isLt⟩ u) :
    CopiesValid C nodes g (copiesCode C nodes g s) := by
  have hs' : ∀ (p : Fin g) (u : Fin C.q), u.val ≠ nodes p →
      labelWt (s p u) ≤ budget C.a ⟨nodes p, hn p p.isLt⟩ u := fun p u hu => (hs p u hu).le
  intro p hp w u hw huw
  obtain ⟨wv, hwv⟩ := w
  simp only at hw
  subst hw
  refine ⟨s ⟨p, hp⟩ u, ?_, hs ⟨p, hp⟩ u fun e => huw (Fin.ext e)⟩
  show decodeLabel _ (fieldOf C _ u _) = _
  rw [fieldOf_eq C _ u huw, slice_copiesCode C nodes g hn s hs' ⟨p, hp⟩,
    dig_argCode C _ _ (fun u' hu' => hs' ⟨p, hp⟩ u' fun e => hu' (Fin.ext e)) u huw,
    decode_labelCode (hs' ⟨p, hp⟩ u fun e => huw (Fin.ext e))]

theorem copiesCode_copyAt (ξ : ℕ) (hξ : ξ < 2 ^ copiesWidth C nodes g)
    (hv : CopiesValid C nodes g ξ) :
    copiesCode C nodes g (fun p u => copyAt C nodes ξ p u) = ξ := by
  rw [copiesCode]
  conv_rhs => rw [← Radix.enc_dig g _ ξ hξ]
  refine Radix.enc_congr fun j hj => ?_
  rw [dif_pos (And.intro hj (hn j hj)), ← slice_eq, argCode]
  conv_rhs => rw [← Radix.enc_dig C.q (argW C (nodes j)) (slice C nodes ξ j) (Nat.mod_lt _ (by positivity))]
  refine Radix.enc_congr fun u hu => ?_
  rw [dif_pos hu]
  split_ifs with huw
  · simp only [Radix.dig, huw, argW_self, pow_zero, Nat.mod_one]
  · have hne : (⟨u, hu⟩ : Fin C.q) ≠ ⟨nodes j, hn j hj⟩ := fun e => huw (congrArg Fin.val e)
    obtain ⟨l, hl, -⟩ := hv j hj ⟨nodes j, hn j hj⟩ ⟨u, hu⟩ rfl hne
    have hl' : decodeLabel (budget C.a ⟨nodes j, hn j hj⟩ ⟨u, hu⟩)
        (fieldOf C ⟨nodes j, hn j hj⟩ ⟨u, hu⟩ (slice C nodes ξ j)) = some l := hl
    have hc : copyAt C nodes ξ j u = l := by
      unfold copyAt
      rw [dif_pos ⟨hn j hj, hu⟩, decodeArgs_eq, if_neg hne, hl']
      rfl
    simp only [hc]
    rw [(labelCode_decode (Nat.mod_lt _ (by positivity)) hl').2]
    exact fieldOf_eq C _ _ hne _

theorem copyAt_mem (ξ : ℕ) (hv : CopiesValid C nodes g ξ) (p : Fin g) (u : Fin C.q) :
    copyAt C nodes ξ p u ∈ (if u.val = nodes p then {((0 : Multiset ℕ), (0 : Multiset ℕ))}
      else labelsEq (budget C.a ⟨nodes p, hn p p.isLt⟩ u)) := by
  unfold copyAt
  rw [dif_pos ⟨hn p p.isLt, u.isLt⟩, decodeArgs_eq]
  by_cases hu : u.val = nodes p
  · rw [if_pos (Fin.ext hu), if_pos hu]; exact mem_singleton_self _
  · have hne : u ≠ ⟨nodes p, hn p p.isLt⟩ := fun e => hu (congrArg Fin.val e)
    rw [if_neg hne, if_neg hu]
    obtain ⟨l, hl, hw⟩ := hv p p.isLt ⟨nodes p, hn p p.isLt⟩ u rfl hne
    have hl' : decodeLabel (budget C.a ⟨nodes p, hn p p.isLt⟩ u)
        (fieldOf C ⟨nodes p, hn p p.isLt⟩ u (slice C nodes ξ p)) = some l := hl
    rw [hl']
    exact mem_labelsEq.mpr hw

open Classical in
/-- **Summing over the valid codes of copies is summing over the settings.** -/
theorem sum_copies (n : Fin g → Fin C.q) (hnn : ∀ p, (n p).val = nodes p.val)
    (H : (Fin g → Fin C.q → Label) → ℤ) :
    ∑ ξ ∈ range (2 ^ copiesWidth C nodes g),
        (if CopiesValid C nodes g ξ then H (fun p u => copyAt C nodes ξ p u) else 0) =
      ∑ s ∈ Fintype.piFinset (fun p => Fintype.piFinset fun u =>
        if u = n p then {((0 : Multiset ℕ), (0 : Multiset ℕ))} else labelsEq (budget C.a (n p) u)),
            H s := by
  have hn' : ∀ p : Fin g, n p = ⟨nodes p, hn p p.isLt⟩ := fun p => Fin.ext (hnn p)
  rw [← Finset.sum_filter]
  refine Finset.sum_nbij' (fun ξ p u => copyAt C nodes ξ p u) (copiesCode C nodes g) ?_ ?_ ?_ ?_
    (fun _ _ => rfl)
  · intro ξ hξ
    have hv := (mem_filter.mp hξ).2
    simp only [Fintype.mem_piFinset]
    intro p u
    have := copyAt_mem C nodes g hn ξ hv p u
    simp only [hn' p, ← Fin.val_eq_val]
    exact this
  · intro s hs
    simp only [Fintype.mem_piFinset] at hs
    have hs1 : ∀ (p : Fin g) (u : Fin C.q), u.val ≠ nodes p →
        labelWt (s p u) = budget C.a ⟨nodes p, hn p p.isLt⟩ u := by
      intro p u hu
      have := hs p u
      rw [if_neg (fun e => hu (by rw [e, hnn])), hn' p] at this
      exact mem_labelsEq.mp this
    exact mem_filter.mpr ⟨mem_range.mpr (copiesCode_lt C nodes g hn s fun p u
        hu => (hs1 p u hu).le),
      copiesValid_copiesCode C nodes g hn s hs1⟩
  · intro ξ hξ
    obtain ⟨h1, h2⟩ := mem_filter.mp hξ
    exact copiesCode_copyAt C nodes g hn ξ (mem_range.mp h1) h2
  · intro s hs
    simp only [Fintype.mem_piFinset] at hs
    have hs0 : ∀ (p : Fin g) (u : Fin C.q), u.val ≠ nodes p →
        labelWt (s p u) ≤ budget C.a ⟨nodes p, hn p p.isLt⟩ u := by
      intro p u hu
      have := hs p u
      rw [if_neg (fun e => hu (by rw [e, hnn])), hn' p] at this
      exact (mem_labelsEq.mp this).le
    funext p u
    rw [copyAt_copiesCode C nodes g hn s hs0 p u]
    split_ifs with hu
    · have := hs p u
      rw [if_pos (Fin.ext (hu.trans (hnn p).symm))] at this
      exact (mem_singleton.mp this).symm
    · rfl

end CopiesCode

end Cslib.Complexity.NtimeDspace.Cube
