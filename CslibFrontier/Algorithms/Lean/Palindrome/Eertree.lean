/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.List.Palindrome
public import Mathlib.Data.List.AList
import Mathlib.Data.List.Induction

/-!
# Palindromic trees

The eertree of a word has an imaginary root of length `-1`, the empty palindrome, and one
vertex for each distinct nonempty palindromic factor. A letter-labelled edge extends a word
at both ends, or creates a singleton from the imaginary root. The suffix link of a nonempty
palindrome goes to its longest proper palindromic suffix. Both roots link to the imaginary root.

This executable representation implements the graph of [Rubinchik and Shur][RubinchikShur2015],
arXiv:1506.04862v2, §2, pp. 3–5, using full words as keys.
Appending a letter retains the previous tree. A longest-first suffix scan stops at the first
palindrome to identify the one possible new vertex and its link. The bound counts graph vertices.
The paper's time and space bounds use a different representation and search.
-/

public section

namespace Cslib.Algorithms.Lean.Palindrome

/-- Eertree vertex labels. The empty word is the root of length zero. -/
inductive PalVertex (α : Type*) where
  /-- The formal root of length minus one, whose children are the single letters. -/
  | imaginary
  /-- A word labelling a vertex, including the empty root. -/
  | word (letters : List α)
  deriving DecidableEq, Repr

/-- Word formed by a letter-labelled extension from a vertex. -/
@[expose] def PalVertex.extend {α : Type*} (v : PalVertex α) (a : α) : List α :=
  match v with
  | .imaginary => [a]
  | .word p => a :: (p ++ [a])

/-- The text read so far and the suffix-link table indexed by complete palindromic words.
The imaginary root is implicit. Each other vertex has exactly one entry. -/
structure Eertree (α : Type*) where
  /-- Current input prefix. -/
  text : List α
  /-- A word key represents a vertex, and the associated value is its suffix link. -/
  links : AList fun _ : List α => PalVertex α

namespace Eertree

variable {α : Type*} [DecidableEq α]

private def longestSuffix (w : List α) : List α :=
  (w.tails.find? (fun p => decide p.Palindrome)).getD []

private theorem longestSuffix_spec (w : List α) :
    longestSuffix w <:+ w ∧ (longestSuffix w).Palindrome ∧
      ∀ p : List α, p <:+ w → p.Palindrome → p.length ≤ (longestSuffix w).length := by
  induction w with
  | nil => simp [longestSuffix, List.tails, List.Palindrome.nil]
  | cons a w ih =>
    by_cases h : (a :: w).Palindrome
    · have eq : longestSuffix (a :: w) = a :: w := by simp [longestSuffix, h]
      rw [eq]
      exact ⟨List.suffix_rfl, h, fun _ hs _ => hs.length_le⟩
    · have eq : longestSuffix (a :: w) = longestSuffix w := by
        simp [longestSuffix, h]
      rw [eq]
      refine ⟨ih.1.trans (List.suffix_cons a w), ih.2.1, fun p hs hp => ih.2.2 p ?_ hp⟩
      exact (List.suffix_cons_iff.mp hs).resolve_left fun e => h (e ▸ hp)

private theorem factors_append (w : List α) (a : α) :
    (w ++ [a]).palindromicFactors = insert (longestSuffix (w ++ [a])) w.palindromicFactors := by
  have rev (s : List α) : s.reverse.palindromicFactors = s.palindromicFactors := by
    ext p
    simp only [List.mem_palindromicFactors]
    exact and_congr_left fun hp => by
      simpa only [hp.reverse_eq] using (List.reverse_infix (l₁ := p) (l₂ := s))
  have one := List.card_sdiff_palindromicFactors_cons_le_one a w.reverse
  rw [← rev (a :: w.reverse), List.reverse_cons, List.reverse_reverse, rev w] at one
  let q := longestSuffix (w ++ [a])
  obtain ⟨hs, hq, hmax⟩ := longestSuffix_spec (w ++ [a])
  have hmem : q ∈ (w ++ [a]).palindromicFactors := List.mem_palindromicFactors.mpr ⟨hs.isInfix, hq⟩
  ext p
  rw [Finset.mem_insert]
  constructor
  · intro hp
    by_cases old : p ∈ w.palindromicFactors
    · exact Or.inr old
    · obtain ⟨hi, hpal⟩ := List.mem_palindromicFactors.mp hp
      have hn : ¬ p <:+: w := fun h => old (List.mem_palindromicFactors.mpr ⟨h, hpal⟩)
      have ps := (List.infix_concat_iff.mp hi).resolve_right hn
      have sub : p <:+ q := List.suffix_of_suffix_length_le ps hs (hmax p ps hpal)
      apply Or.inl
      apply Finset.card_le_one.mp one p (Finset.mem_sdiff.mpr ⟨hp, old⟩) q
      exact Finset.mem_sdiff.mpr ⟨hmem, fun h => hn (sub.isInfix.trans
        (List.mem_palindromicFactors.mp h).1)⟩
  · rintro (rfl | h)
    · exact hmem
    · obtain ⟨hi, hp⟩ := List.mem_palindromicFactors.mp h
      exact List.mem_palindromicFactors.mpr ⟨List.infix_concat_iff.mpr (.inr hi), hp⟩

private def linkTarget : List α → PalVertex α
  | [] => .imaginary
  | _ :: t => .word (longestSuffix t)

/-- The empty word's eertree already contains its two roots. -/
@[expose] def empty : Eertree α := ⟨[], (∅ : AList _).insert [] .imaginary⟩

/-- Append one letter, adding a suffix-link entry only for a previously unseen longest
palindromic suffix. All earlier entries retain their links. -/
def append (tree : Eertree α) (a : α) : Eertree α :=
  let text := tree.text ++ [a]
  let q := longestSuffix text
  ⟨text, if q ∈ tree.links then tree.links else tree.links.insert q (linkTarget q)⟩

/-- Build a palindromic tree one letter at a time from left to right. -/
@[expose] def ofList (w : List α) : Eertree α := w.foldl append empty

/-- Follow the suffix link of a vertex. An absent word has no link. -/
@[expose] def suffixLink? (tree : Eertree α) : PalVertex α → Option (PalVertex α)
  | .imaginary => some .imaginary
  | .word p => tree.links.lookup p

/-- Look up the outgoing edge labelled `a`. Full word keys determine extension edges. -/
@[expose] def edge? (tree : Eertree α) (v : PalVertex α) (a : α) : Option (PalVertex α) :=
  let q := v.extend a
  if q ∈ tree.links then some (.word q) else none

/-- Building after a one-letter extension agrees with updating the previous tree. -/
theorem ofList_append_singleton (w : List α) (a : α) :
    ofList (w ++ [a]) = (ofList w).append a := by simp [ofList, List.foldl_append]

private theorem ofList_spec (w : List α) :
    (ofList w).text = w ∧ ∀ p, (ofList w).links.lookup p =
      if p ∈ w.palindromicFactors then some (linkTarget p) else none := by
  induction w using List.reverseRecOn with
  | nil =>
    refine ⟨rfl, fun p => ?_⟩
    cases p with
    | nil => rfl
    | cons a t =>
      simp only [List.mem_palindromicFactors, List.infix_nil, List.cons_ne_nil, false_and,
        ↓reduceIte]
      exact AList.lookup_insert_ne (by simp)
  | append_singleton w a ih =>
    rw [ofList_append_singleton]
    refine ⟨by simp [append, ih.1], fun p => ?_⟩
    simp only [append, ih.1, factors_append, Finset.mem_insert]
    let q := longestSuffix (w ++ [a])
    change AList.lookup p (if q ∈ (ofList w).links then (ofList w).links
      else (ofList w).links.insert q (linkTarget q)) = if p = q ∨ _ then _ else _
    by_cases hq : q ∈ (ofList w).links
    · have hm := AList.lookup_isSome.mpr hq
      rw [ih.2] at hm
      by_cases h : q ∈ w.palindromicFactors
      · simp only [hq, ↓reduceIte, ih.2]
        by_cases e : p = q <;> simp_all
      · simp [h] at hm
    · by_cases e : p = q
      · subst p; simp [hq]
      · simp [hq, e, AList.lookup_insert_ne e, ih.2]

/-- The word vertices are exactly the distinct palindromic factors, including the empty root. -/
theorem wordKeys_ofList (w : List α) :
    (ofList w).links.keys.toFinset = w.palindromicFactors := by
  ext p
  rw [List.mem_toFinset, ← AList.mem_keys, ← AList.lookup_isSome, (ofList_spec w).2]
  by_cases h : p ∈ w.palindromicFactors <;> simp [h]

/-- Counting the imaginary root as well, the eertree has at most `length + 2` vertices. -/
theorem vertexCount_le (w : List α) : (ofList w).links.keys.length + 1 ≤ w.length + 2 := by
  have hc := congrArg Finset.card (wordKeys_ofList w)
  rw [List.toFinset_card_of_nodup (ofList w).links.keys_nodup] at hc
  have := List.card_palindromicFactors_le w
  omega

/-- From either root or a word vertex, a letter-labelled edge exists precisely when the
extended word occurs as a palindromic factor. The extended word determines the target. -/
theorem edge?_ofList (w : List α) (v : PalVertex α) (a : α) :
    (ofList w).edge? v a =
      if v.extend a ∈ w.palindromicFactors then some (.word (v.extend a)) else none := by
  simp only [edge?, ← wordKeys_ofList w, List.mem_toFinset, ← AList.mem_keys]

/-- The empty word has a suffix link to the imaginary root at every prefix. -/
@[simp] theorem suffixLink?_emptyRoot (w : List α) :
    (ofList w).suffixLink? (.word []) = some .imaginary := by
  simp [suffixLink?, (ofList_spec w).2, List.Palindrome.nil, linkTarget]

/-- A nonempty vertex links to the longest palindromic suffix strictly shorter than itself. -/
theorem suffixLink?_longest {w : List α} {a : α} {t : List α}
    (h : a :: t ∈ w.palindromicFactors) :
    ∃ q, (ofList w).suffixLink? (.word (a :: t)) = some (.word q) ∧
      q <:+ a :: t ∧ q.Palindrome ∧ q.length < (a :: t).length ∧
      ∀ p : List α, p <:+ a :: t → p.Palindrome → p.length < (a :: t).length →
        p.length ≤ q.length := by
  obtain ⟨hs, hp, hmax⟩ := longestSuffix_spec t
  refine ⟨_, by simp [suffixLink?, (ofList_spec w).2, h, linkTarget],
    List.suffix_cons_iff.mpr (.inr hs), hp, Nat.lt_succ_of_le hs.length_le, ?_⟩
  intro p hsu hpal hlt
  exact hmax p ((List.suffix_cons_iff.mp hsu).resolve_left fun e => by simp [e] at hlt) hpal

end Eertree

end Cslib.Algorithms.Lean.Palindrome
