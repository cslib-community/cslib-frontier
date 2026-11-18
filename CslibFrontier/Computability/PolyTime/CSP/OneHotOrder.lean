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

/-- Framed binary CSP followed by its supplied binary successor table. -/
abbrev encOrderInput := encPair (encCSP encUnit encNat) encRotationCertificate

/-- A binary rotation table followed by a binary index, with no unary clock conversion. -/
abbrev encTableIndex := encPair encRotationCertificate encNat

private theorem swapTail3_tidy :
    ComputableTidilyInPolyTime swapTail3 (encList encNat) (encList encNat) := by
  have he (xs : List ℕ) : swapTail3 xs =
      if 3 ≤ xs.length then xs.getD 0 0 :: xs.getD 2 0 :: xs.getD 1 0 :: xs.drop 3 else xs := by
    cases xs with
    | nil => rfl
    | cons a xs =>
      cases xs with
      | nil => rfl
      | cons b xs =>
        cases xs with
        | nil => rfl
        | cons c tail => simp only [swapTail3, List.length_cons, List.getD_cons_zero,
            List.getD_cons_succ, List.drop_succ_cons, List.drop_zero,
            show 3 ≤ tail.length + 1 + 1 + 1 by omega, ↓reduceIte]
  have hid : ComputableTidilyInPolyTime (fun xs : List ℕ => xs)
      (encList encNat) (encList encNat) := .id'
  have hget (j : ℕ) := ComputableTidilyInPolyTime.listGetD_binary (encA := encNat) 0
    hid (ComputableTidilyInPolyTime.const j)
  have htail := ComputableTidilyInPolyTime.listDropWithInput hid
    (ComputableTidilyInPolyTime.const 3)
  have hbody := ComputableTidilyInPolyTime.cons' (hget 0)
    (ComputableTidilyInPolyTime.cons' (hget 2)
      (ComputableTidilyInPolyTime.cons' (hget 1) htail))
  have hguard := ComputableTidilyInPolyTime.unary_le'
    (ComputableTidilyInPolyTime.const 3) (ComputableTidilyInPolyTime.length_list encNat)
  have hp := ComputableTidilyInPolyTime.ite_decide hguard hbody hid
  simpa only [← he] using hp

private theorem forward_tidy :
    ComputableTidilyInPolyTime (fun p : RotationCertificate × ℕ => forward p.1 p.2)
      encTableIndex encBool := by
  have hs := RotationCertificate.computableInPolyTime_successor.tidy
  have hidx : ComputableTidilyInPolyTime (fun p : RotationCertificate × ℕ => 6 * p.2 + 1)
      encTableIndex encNat := by
    unfold encTableIndex
    fun_prop
  have hlookup := ComputableTidilyInPolyTime.listGetD_binary (encA := encNat) 0
    (hs.comp (ComputableTidilyInPolyTime.fst _ _)) hidx
  unfold forward encTableIndex at *
  fun_prop

/-- The exact conditional scope exchange is native polynomial time on all raw input lists. -/
theorem computableInPolyTime_orderedConstraints :
    ComputableInPolyTime (fun p : CSP Unit ℕ × RotationCertificate =>
      orderedConstraints p.1 p.2) encOrderInput (encCSP encUnit encNat) := by
  apply ComputableInPolyTime.of_tidy
  have hz : ComputableTidilyInPolyTime (fun p : CSP Unit ℕ × RotationCertificate => p.1.zipIdx)
      encOrderInput (encList (encPair (encConstraint encUnit encNat) encUnary)) :=
    (ComputableTidilyInPolyTime.zipIdx _).comp (ComputableTidilyInPolyTime.fst _ _)
  simp only [orderedConstraints, List.mapIdx_eq_zipIdx_map]
  apply ComputableTidilyInPolyTime.mapWithInput hz
  let encRow := encPair (encConstraint encUnit encNat) encUnary
  have hdata := ComputableTidilyInPolyTime.snd encOrderInput encRow
  have hinput := ComputableTidilyInPolyTime.fst encOrderInput encRow
  have hrow := (ComputableTidilyInPolyTime.fst (encConstraint encUnit encNat) encUnary).comp
    hdata
  have hi := ComputableTidilyInPolyTime.unary_to_binary.comp
    ((ComputableTidilyInPolyTime.snd (encConstraint encUnit encNat) encUnary).comp hdata)
  have htable := (ComputableTidilyInPolyTime.snd (encCSP encUnit encNat)
    encRotationCertificate).comp hinput
  have hf := forward_tidy.comp (htable.prod hi)
  have hscope := (encConstraint_scope_polyTime hrow.computableInPolyTime).tidy
  have hswap := swapTail3_tidy.comp hscope
  have hout := ComputableTidilyInPolyTime.cond hf hscope hswap
  exact (encConstraint_mk_polyTime (encConstraint_rel_polyTime hrow.computableInPolyTime)
    hout.computableInPolyTime).tidy

private theorem dartReindex_tidy :
    ComputableTidilyInPolyTime (fun p : RotationCertificate × ℕ => dartReindex p.1 p.2)
      encTableIndex encNat := by
  have hrow : ComputableTidilyInPolyTime (fun p : RotationCertificate × ℕ => p.2 / 6)
      encTableIndex encNat := by unfold encTableIndex; fun_prop
  have hf := forward_tidy.comp
    ((ComputableTidilyInPolyTime.fst encRotationCertificate encNat).prod hrow)
  have hi := ComputableTidilyInPolyTime.snd encRotationCertificate encNat
  have hport := ComputableTidilyInPolyTime.binary_mod'
    (ComputableTidilyInPolyTime.binary_div' hi (ComputableTidilyInPolyTime.const 2))
    (ComputableTidilyInPolyTime.const 3)
  have hside := ComputableTidilyInPolyTime.binary_mod' hi
    (ComputableTidilyInPolyTime.const 2)
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
    have he := encGraph_edges_polyTime hg
    have hl := ((ComputableTidilyInPolyTime.length_list (encPair encNat encNat)).comp
      he.tidy).computableInPolyTime
    exact ComputableInPolyTime.unary_mul.comp ((ComputableInPolyTime.const 2).prod hl)
  have hc : ComputableInPolyTime (fun p : CSP Unit ℕ × RotationCertificate => p.2)
      encOrderInput encRotationCertificate := ComputableInPolyTime.snd _ _
  have hi : ComputableInPolyTime (fun p : (CSP Unit ℕ × RotationCertificate) × ℕ =>
      (p.1.2, p.2)) (encPair encOrderInput encNat) encTableIndex :=
    ((ComputableInPolyTime.snd (encCSP encUnit encNat) encRotationCertificate).comp
      (ComputableInPolyTime.fst encOrderInput encNat)).prod
      (ComputableInPolyTime.snd encOrderInput encNat)
  have hr : ComputableInPolyTime (fun p : (CSP Unit ℕ × RotationCertificate) × ℕ =>
      dartReindex p.1.2 p.2) (encPair encOrderInput encNat) encNat :=
    dartReindex_tidy.computableInPolyTime.comp hi
  exact RotationCertificate.computableInPolyTime_reindex
    (α := CSP Unit ℕ × RotationCertificate) (input := encOrderInput)
    (table := fun p => p.2)
    (count := fun p => 2 * (incidenceGraph p.1).edges.length)
    (forward := fun p i => dartReindex p.2 i) (back := fun p i => dartReindex p.2 i)
    hc hn hr hr

end Cslib.Complexity.CSP.OneHot3
