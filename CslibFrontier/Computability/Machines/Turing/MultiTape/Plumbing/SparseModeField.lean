/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.GammaOffset

/-!
# Physical field lookup on padded sparse mode tables

Given the unary token ordinal of an occupied entry, the same read-only machine retrieves its
positive weight gap or multiplicity. The clock counts the entire physical prefix up to that
field, and is linear in the length of the compressed table.
-/

public section

namespace Turing.MultiTapeTM.SparseModeField

open Cslib.BitString Cslib.SparseModeTuple GammaStream

/-- The tokens before one of the fields of an occupied entry of a particular colour row. -/
@[expose] def prefixFields (right : Bool) (rows prior : List Row) (r : Row)
    (earlier : List Entry) (e : Entry) : List ℕ :=
  [rows.length + 1] ++ prior.flatMap rowFields ++ [r.skip + 1, r.rest.length + 1] ++
    earlier.flatMap entryFields ++ (if right then [e.skip + 1] else [])

/-- A true side selects the multiplicity and a false side selects the weight gap. -/
@[expose] def value (right : Bool) (e : Entry) : ℕ := (if right then e.extra else e.skip) + 1

private def following (right : Bool) (e : Entry) (later : List Entry) (rows : List Row) : List ℕ :=
  (if right then [] else [e.extra + 1]) ++ later.flatMap entryFields ++ rows.flatMap rowFields

private theorem fields_eq (right : Bool) (prior after : List Row) (r : Row)
    (earlier later : List Entry) (e : Entry) (h : r.first :: r.rest = earlier ++ e :: later) :
    let rows := prior ++ r :: after
    fields rows = prefixFields right rows prior r earlier e ++
      value right e :: following right e later after := by
  cases right <;> simp [fields, prefixFields, rowFields, entryFields, value, following,
    h, List.append_assoc]

/-- The physical selector with the specified tally reads the requested gap or multiplicity from
the canonical padded table. Previous success flags precede the selected positive number. -/
theorem runsBetween (right : Bool) {input : List Bool} (ip : Fin (input.length + 2))
    (out : List Bool)
    (width : ℕ) (prior after : List Row) (r : Row) (earlier later : List Entry) (e : Entry)
    (h : r.first :: r.rest = earlier ++ e :: later) :
    let rows := prior ++ r :: after
    let px := prefixFields right rows prior r earlier e
    let tally := List.replicate px.length true
    let cursor := (px.flatMap eliasGamma).length + (eliasGamma (value right e)).length
    let time := 4 * (encode rows).length + 2
    RunsBetween GammaOffset.machine (GammaOffset.storage ip out (padded width rows) 0 tally 0)
      (GammaOffset.storage ip ((out ++ tally) ++ tokenOutput true (value right e))
        (padded width rows) cursor tally px.length) time (3 * (time + 1)) := by
  let rows := prior ++ r :: after
  let px := prefixFields right rows prior r earlier e
  let v := value right e
  let post := following right e later after
  let pad := List.replicate (width - (encode rows).length) false
  have hraw : encode rows = px.flatMap eliasGamma ++ eliasGamma v ++ post.flatMap eliasGamma := by
    have hf := fields_eq right prior after r earlier later e h
    rw [← flatMap_fields, hf]
    simp [px, v, post, rows, List.append_assoc]
  have hword : px.flatMap eliasGamma ++ eliasGamma v ++ (post.flatMap eliasGamma ++ pad) =
      padded width rows := by
    change _ = encode rows ++ pad
    rw [hraw]
    simp only [List.append_assoc]
  have hr := GammaOffset.runsBetween ip out [] (post.flatMap eliasGamma ++ pad) px v
  dsimp only at hr
  simp only [List.nil_append, List.length_nil, zero_add, hword] at hr
  have hlen := congrArg List.length hraw
  simp only [List.length_append] at hlen
  have ht : 4 * (px.flatMap eliasGamma).length + (eliasGamma v).length + 2 ≤
      4 * (encode rows).length + 2 := by omega
  exact hr.mono ht (Nat.mul_le_mul_left 3 (Nat.add_le_add_right ht 1))

end Turing.MultiTapeTM.SparseModeField
