/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.CSP.OneHot3.Order
public import CslibFrontier.Computability.PolyTime.Graph.RotationSystem
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.PolyTime.Graph.RotationSystem.Reindex
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Captured
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Native ternary scope alignment and certificate conjugation

The programs retain binary variables, successor entries and arithmetic indices. Only actual
list positions are generated in unary and converted to binary before lookup. In particular,
a malformed successor entry of arbitrary binary magnitude never funds an iteration.

These certificates cover every raw scope and table. Acceptance of the reordered output is
a separate geometric and positional correctness result for the exact ternary base source.
-/

public section

namespace Cslib.Complexity.CSP.OneHot3

open Cslib.Logic.PL Graph Turing.MultiTapeTM
open scoped RotationCertificate

/-- Framed binary CSP followed by its supplied binary successor table. -/
abbrev encOrderInput := encPair (encCSP encUnit encNat) encRotationCertificate

/-- A binary rotation table followed by a binary index, with no unary clock conversion. -/
abbrev encTableIndex := encPair encRotationCertificate encNat

private theorem swapTail3_polyTime :
    ComputableInPolyTime swapTail3 (encList encNat) (encList encNat) := by
  have he (xs : List ℕ) : swapTail3 xs =
      if 3 ≤ xs.length then xs.getD 0 0 :: xs.getD 2 0 :: xs.getD 1 0 :: xs.drop 3 else xs := by
    rcases xs with _ | ⟨a, _ | ⟨b, _ | ⟨c, tail⟩⟩⟩ <;> rfl
  have hid : ComputableInPolyTime (fun xs : List ℕ => xs) (encList encNat) (encList encNat) := .id'
  have hget (j : ℕ) := ComputableInPolyTime.listGetD_binary (encA := encNat) 0 hid (.const j)
  simpa only [← he] using ComputableInPolyTime.ite_decide
    (ComputableInPolyTime.unary_le' (.const 3) (.length_list encNat))
    (.cons' (hget 0) (.cons' (hget 2) (.cons' (hget 1) (.listDropWithInput hid (.const 3))))) hid

private theorem forward_polyTime :
    ComputableInPolyTime (fun p : RotationCertificate × ℕ => forward p.1 p.2)
      encTableIndex encBool := by
  unfold forward encTableIndex
  have h6 : ComputableInPolyTime (fun p : RotationCertificate × ℕ => 6 * p.2)
      (encPair encRotationCertificate encNat) encNat :=
    ComputableInPolyTime.binary_mul' (ComputableInPolyTime.const 6) (by fun_prop)
  exact ComputableInPolyTime.decide_eq'
    (RotationCertificate.listGetD_binary_encList 0 (by fun_prop)
      (ComputableInPolyTime.binary_add' h6 (ComputableInPolyTime.const 1)))
    (ComputableInPolyTime.binary_add' h6 (ComputableInPolyTime.const 3))

/-- The exact conditional scope exchange is native polynomial time on all raw input lists. -/
theorem computableInPolyTime_orderedConstraints :
    ComputableInPolyTime (fun p : CSP Unit ℕ × RotationCertificate =>
      orderedConstraints p.1 p.2) encOrderInput (encCSP encUnit encNat) := by
  simp only [orderedConstraints, List.mapIdx_eq_zipIdx_map]
  apply ComputableInPolyTime.mapWithInput
    ((ComputableInPolyTime.zipIdx _).comp (ComputableInPolyTime.fst _ _))
  let encRow := encPair (encConstraint encUnit encNat) encUnary
  have hdata := ComputableInPolyTime.snd encOrderInput encRow
  have hrow := (ComputableInPolyTime.fst (encConstraint encUnit encNat) encUnary).comp hdata
  have hi := ComputableInPolyTime.unary_to_binary.comp
    ((ComputableInPolyTime.snd (encConstraint encUnit encNat) encUnary).comp hdata)
  have hf := forward_polyTime.comp
    (((ComputableInPolyTime.snd (encCSP encUnit encNat) encRotationCertificate).comp
      (ComputableInPolyTime.fst encOrderInput encRow)).prod hi)
  have hscope := encConstraint_scope_polyTime hrow
  exact encConstraint_mk_polyTime (encConstraint_rel_polyTime hrow)
    (ComputableInPolyTime.ite hf hscope (swapTail3_polyTime.comp hscope))

private theorem dartReindex_polyTime :
    ComputableInPolyTime (fun p : RotationCertificate × ℕ => dartReindex p.1 p.2)
      encTableIndex encNat := by
  have hrow : ComputableInPolyTime (fun p : RotationCertificate × ℕ => p.2 / 6)
      encTableIndex encNat := by unfold encTableIndex; fun_prop
  have hf := forward_polyTime.comp
    ((ComputableInPolyTime.fst encRotationCertificate encNat).prod hrow)
  have hi := ComputableInPolyTime.snd encRotationCertificate encNat
  have hport := ComputableInPolyTime.binary_mod'
    (ComputableInPolyTime.binary_div' hi (.const 2)) (.const 3)
  have hside := ComputableInPolyTime.binary_mod' hi (.const 2)
  dsimp only [dartReindex]
  fun_prop

/-- Conjugating the supplied binary table executes a polynomial-time program on all raw
inputs, even when lookups or table entries have enormous binary indices. -/
theorem computableInPolyTime_orderedCertificate :
    ComputableInPolyTime (fun p : CSP Unit ℕ × RotationCertificate =>
      orderedCertificate p.1 p.2) encOrderInput encRotationCertificate := by
  change ComputableInPolyTime (fun p : CSP Unit ℕ × RotationCertificate =>
    RotationCertificate.reindex p.2 (2 * (incidenceGraph p.1).edges.length)
      (dartReindex p.2) (dartReindex p.2)) encOrderInput encRotationCertificate
  have hg := (computableInPolyTime_incidenceGraph encUnit encNat).comp
    (ComputableInPolyTime.fst (encCSP encUnit encNat) encRotationCertificate)
  have hn : ComputableInPolyTime (fun p : CSP Unit ℕ × RotationCertificate =>
      2 * (incidenceGraph p.1).edges.length) encOrderInput encUnary := by
    fun_prop
  have hc : ComputableInPolyTime (fun p : CSP Unit ℕ × RotationCertificate => p.2)
      encOrderInput encRotationCertificate := ComputableInPolyTime.snd _ _
  have hi : ComputableInPolyTime (fun p : (CSP Unit ℕ × RotationCertificate) × ℕ =>
      (p.1.2, p.2)) (encPair encOrderInput encNat) encTableIndex :=
    ((ComputableInPolyTime.snd (encCSP encUnit encNat) encRotationCertificate).comp
      (ComputableInPolyTime.fst encOrderInput encNat)).prod
      (ComputableInPolyTime.snd encOrderInput encNat)
  have hr : ComputableInPolyTime (fun p : (CSP Unit ℕ × RotationCertificate) × ℕ =>
      dartReindex p.1.2 p.2) (encPair encOrderInput encNat) encNat :=
    dartReindex_polyTime.comp hi
  exact RotationCertificate.computableInPolyTime_reindex
    (α := CSP Unit ℕ × RotationCertificate) (input := encOrderInput)
    (table := fun p => p.2)
    (count := fun p => 2 * (incidenceGraph p.1).edges.length)
    (forward := fun p i => dartReindex p.2 i) (back := fun p i => dartReindex p.2 i)
    hc hn hr hr

end Cslib.Complexity.CSP.OneHot3
