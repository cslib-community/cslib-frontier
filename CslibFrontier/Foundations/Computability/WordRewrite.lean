/-
Copyright (c) 2026 Samuel Schlesinger, Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Logic.Relation

/-!
# Finite-word rewriting

A pair of words gives a rewrite rule. The rewriting relation applies a rule inside an arbitrary
prefix and suffix. We retain the `PostCorrespondence` namespace and its top and bottom convention
so the existing correspondence constructions use the same rules.
-/

public section

namespace Cslib.PostCorrespondence

open Relation

variable {α : Type*}

-- Exposed so that `decide` can evaluate the derived `DecidableEq` instance in client modules.
@[expose] public section DominoDef

/-- A domino: a pair of words, its top and its bottom. -/
structure Domino (α : Type*) where
  /-- The top word. -/
  top : List α
  /-- The bottom word. -/
  bottom : List α
deriving DecidableEq

end DominoDef

/-- One rewriting step with a set `R` of dominoes, read as a semi-Thue system: an occurrence of the
top word of a domino of `R` is replaced by its bottom word. -/
@[expose] def Rewrites (R : Domino α → Prop) (u v : List α) : Prop :=
  ∃ p d s, R d ∧ u = p ++ d.top ++ s ∧ v = p ++ d.bottom ++ s

theorem Rewrites.append_left {R : Domino α → Prop} {u v : List α} (h : Rewrites R u v)
    (w : List α) : Rewrites R (w ++ u) (w ++ v) := by
  obtain ⟨p, d, s, hd, rfl, rfl⟩ := h
  exact ⟨w ++ p, d, s, hd, by simp only [List.append_assoc],
    by simp only [List.append_assoc]⟩

theorem Rewrites.append_right {R : Domino α → Prop} {u v : List α} (h : Rewrites R u v)
    (w : List α) : Rewrites R (u ++ w) (v ++ w) := by
  obtain ⟨p, d, s, hd, rfl, rfl⟩ := h
  exact ⟨p, d, s ++ w, hd, by simp only [List.append_assoc],
    by simp only [List.append_assoc]⟩

theorem reflTransGen_rewrites_append_left {R : Domino α → Prop} {u v : List α}
    (h : ReflTransGen (Rewrites R) u v) (w : List α) :
    ReflTransGen (Rewrites R) (w ++ u) (w ++ v) :=
  ReflTransGen.lift (w ++ ·) (fun _ _ (h : Rewrites R _ _) => h.append_left w) _ _ h

theorem reflTransGen_rewrites_append_right {R : Domino α → Prop} {u v : List α}
    (h : ReflTransGen (Rewrites R) u v) (w : List α) :
    ReflTransGen (Rewrites R) (u ++ w) (v ++ w) :=
  ReflTransGen.lift (· ++ w) (fun _ _ (h : Rewrites R _ _) => h.append_right w) _ _ h

end Cslib.PostCorrespondence
