/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.DescendantVertex

/-!
# Correctness of the numbered-vertex ancestry word

Each frame chooses a parent before a universal move separates the local membership and rank
check from the remaining ancestry. A packet birth uses the same exact counter for the total
retained vertices. Concatenation fixes every frame's flags before any move is chosen.

## Main results

* `Turing.MultiTapeTM.DescendantVertex.plays_program`: the fixed quantified word verifies
  exactly numerical provenance, including all invalid-index and invalid-stage cases.
-/

public section

namespace Turing.MultiTapeTM.DescendantVertex

open Cslib Cslib.BitString MultiTapeATM QuantifiedWord
open DescendantEndpoint (Frame)

private theorem plays_rank (f : Frame) (bound value : ℕ) :
    plays (fun xs => SeededVertexRank.program (rankQuery f bound value, xs) = true) []
      (SeededVertexRank.flags f.vertices) ↔ value = retained f bound := by
  exact SeededVertexRank.plays_program_iff (rankQuery f bound value)

private theorem plays_dispatch_bits (f : Frame) (fs : List Frame) (vertices vertex : ℕ)
    (origin : Origin) (cont : ℕ → Prop) (parent : Fin (2 ^ f.vertices.size)) (bit : Bool) :
    plays (fun xs => (dispatch ⟨f :: fs, vertices, vertex, origin⟩ xs).elim
      (fun b => b = true) cont) (lowBits f.vertices.size parent.val ++ [bit])
        (SeededVertexRank.flags f.vertices) ↔
      if vertex < vertices ∧ origin.stage ≤ fs.length + 1 then
        if origin.stage = fs.length + 1 then
          origin.index ≤ vertex ∧ vertex - origin.index = retained f f.vertices
        else if bit then cont parent.val
        else parent.val < f.vertices ∧ symbol f parent.val = f.group ∧
          vertex = retained f parent.val
      else False := by
  let V := fun xs => (dispatch ⟨f :: fs, vertices, vertex, origin⟩ xs).elim
    (fun b => b = true) cont
  change plays V _ _ ↔ _
  rw [plays_append_prefix V (lowBits f.vertices.size parent.val) [bit]]
  have hshift := plays_append_prefix
    (fun xs => V (lowBits f.vertices.size parent.val ++ xs)) [bit] []
      (SeededVertexRank.flags f.vertices)
  simp only [List.append_nil, List.singleton_append] at hshift
  rw [hshift]
  have ht (xs : List Bool) :
      (lowBits f.vertices.size parent.val ++ bit :: xs).take f.vertices.size =
        lowBits f.vertices.size parent.val := by
    simpa only [length_lowBits] using
      List.take_left (l₁ := lowBits f.vertices.size parent.val) (l₂ := bit :: xs)
  have hd (xs : List Bool) :
      (lowBits f.vertices.size parent.val ++ bit :: xs).drop f.vertices.size = bit :: xs := by
    simpa only [length_lowBits] using
      List.drop_left (l₁ := lowBits f.vertices.size parent.val) (l₂ := bit :: xs)
  have htail (xs : List Bool) :
      (lowBits f.vertices.size parent.val ++ bit :: xs).drop (f.vertices.size + 1) = xs := by
    rw [← List.tail_drop, hd]
    rfl
  by_cases hg : vertex < vertices ∧ origin.stage ≤ fs.length + 1
  · by_cases hb : origin.stage = fs.length + 1
    · by_cases hi : origin.index ≤ vertex
      · simpa [V, dispatch, hg, hb, hi, htail] using
          plays_rank f f.vertices (vertex - origin.index)
      · simp [V, dispatch, hg, hb, hi, plays_constant]
    · cases bit with
      | false =>
        by_cases hm : parent.val < f.vertices ∧ symbol f parent.val = f.group
        · simpa [V, dispatch, hg, hb, ht, hd, htail, ofBits_lowBits parent.isLt,
            hm, hm.1, hm.2] using plays_rank f parent.val vertex
        · simp [V, dispatch, hg, hb, ht, ofBits_lowBits parent.isLt,
            hm, plays_constant]
          tauto
      | true =>
        simpa [V, dispatch, hg, hb, ht, hd, ofBits_lowBits parent.isLt] using
          plays_constant (cont parent.val) [] (SeededVertexRank.flags f.vertices)
  · simp [V, dispatch, hg, plays_constant]

private theorem plays_dispatch (f : Frame) (fs : List Frame) (vertices vertex : ℕ)
    (origin : Origin) (cont : ℕ → Prop) :
    plays (fun xs => (dispatch ⟨f :: fs, vertices, vertex, origin⟩ xs).elim
      (fun b => b = true) cont) [] (frameFlags f) ↔
      vertex < vertices ∧
        ((origin.stage = fs.length + 1 ∧ vertex = retained f f.vertices + origin.index) ∨
          (origin.stage ≤ fs.length ∧ ∃ parent, parent < f.vertices ∧
            symbol f parent = f.group ∧ vertex = retained f parent ∧ cont parent)) := by
  rw [frameFlags, plays_exists_field]
  simp only [List.nil_append, plays, ↓reduceIte]
  simp_rw [plays_dispatch_bits]
  by_cases hg : vertex < vertices ∧ origin.stage ≤ fs.length + 1
  · simp only [hg, and_self, ↓reduceIte]
    by_cases hb : origin.stage = fs.length + 1
    · have : Nonempty (Fin (2 ^ f.vertices.size)) := ⟨⟨0, by positivity⟩⟩
      simp [hb]
      omega
    · have hs : origin.stage ≤ fs.length := by omega
      simp only [hb, hs, ↓reduceIte, false_and, false_or, true_and,
        Bool.forall_bool, Bool.false_eq_true]
      constructor
      · rintro ⟨parent, hlocal, hcont⟩
        exact ⟨parent.val, hlocal.1, hlocal.2.1, hlocal.2.2, hcont⟩
      · rintro ⟨parent, hp, hm, hr, hc⟩
        exact ⟨⟨parent, hp.trans (Nat.lt_size_self f.vertices)⟩, ⟨hp, hm, hr⟩, hc⟩
  · simp only [hg, ↓reduceIte]
    constructor
    · rintro ⟨parent, h⟩
      exact (h false).elim
    · rintro ⟨hv, h⟩
      exfalso
      rcases h with ⟨hs, _⟩ | ⟨hs, _⟩ <;> exact hg ⟨hv, by omega⟩

/-- The fixed concatenated word verifies exactly the numerical origin relation. This includes
zero frames, invalid current numbers, impossible stages, and zero-width parent proposals. -/
theorem plays_program (q : Query) :
    plays (fun xs => program (q, xs) = true) [] (flags q.frames) ↔
      HasOrigin q.vertices q.vertex q.origin q.frames := by
  rcases q with ⟨frames, vertices, vertex, origin⟩
  change plays (fun xs => run vertices vertex origin frames xs = true) [] (flags frames) ↔ _
  induction frames generalizing vertices vertex with
  | nil =>
    simp only [flags, List.flatMap_nil, plays, run, dispatch, List.length_nil, Nat.le_zero,
      HasOrigin]
    split_ifs <;> simp_all
  | cons f fs ih =>
    let V : List Bool → List Bool → Prop := fun xs ys =>
      (dispatch ⟨f :: fs, vertices, vertex, origin⟩ xs).elim (fun b => b = true)
        (fun parent => run f.vertices parent origin fs ys = true)
    let W : List Bool → Prop := fun xs =>
      (dispatch ⟨f :: fs, vertices, vertex, origin⟩ xs).elim (fun b => b = true)
        (fun parent => HasOrigin f.vertices parent origin fs)
    have hsplit := plays_split V W (frameFlags f) (flags fs) (by
      intro xs _
      dsimp only [V, W]
      cases dispatch ⟨f :: fs, vertices, vertex, origin⟩ xs with
      | inl b => exact plays_constant (b = true) [] (flags fs)
      | inr parent => exact ih f.vertices parent)
    have hsame : plays (fun xs => run vertices vertex origin (f :: fs) xs = true) []
        (flags (f :: fs)) ↔
        plays (fun xs => V (xs.take (frameFlags f).length)
          (xs.drop (frameFlags f).length)) [] (frameFlags f ++ flags fs) := by
      simp only [flags, List.flatMap_cons]
      apply plays_congr_length
      intro xs _
      simp only [List.nil_append, run, V]
      cases dispatch ⟨f :: fs, vertices, vertex, origin⟩
        (xs.take (frameFlags f).length) <;> rfl
    exact hsame.trans (hsplit.trans
      (plays_dispatch f fs vertices vertex origin
        (fun parent => HasOrigin f.vertices parent origin fs)))

end Turing.MultiTapeTM.DescendantVertex
