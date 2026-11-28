/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Dealing.AllRuns
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Interpreter.AccSize

/-!
# The size of the steps of the dealing program

The dealing program of [AnthropicVPVNP2026] has `O(X ^ 2)` steps up to its checks
(`length_dealSteps_le`), each of size `O(X ^ 2 * Lc)`, so that their list has size
`O(X ^ 4 * Lc)` (`size_listT_dealSteps_le`), and its guesses of the contents have size
`O(X * Lc)` in all (`size_listT_contentSteps_le`). Here `X` bounds the numbers of blocks, parties,
units, moves, digits, steps of the straight-line program, channels, tapes, states and row data and
the numbers of the states, and `Lc` the lengths of the codes of the names, digits, row data and
keys (`Codes.SizeBounds`).

## Main definitions

* `Codes.SizeBounds`: the bounds for the sizes of the dealing program.

## Main results

* `length_dealSteps_le`: the number of the steps up to the checks.
* `size_listT_dealSteps_le`, `size_listT_contentSteps_le`: the sizes of the lists of the steps.

## References

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], Appendix J.3: the program `G` in the proof
of Theorem J.3 (p. 53: some program of size at most `v^a₀` cuts). Ported from the source module
`Nc.Dl.SizeDeal` (the steps).
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Dealing

open Function Finset Interpreter Interpreter.Tree Cut GroupProgram

variable {F : Type} [CommSemiring F] {K A' E U0 U1 D pS : ℕ} {M : Moves F (K + K + A') E}
  {S Q : Type} [Fintype S] [Fintype Q]

/-- Bounds for the sizes of the dealing program: `Lc` bounds the lengths of the codes of the
names, digits, row data and keys, and `X` the numbers of the blocks plus one, the base parties,
the units of a string plus one, the units of a channel, the moves plus one, the digits, the steps
of the straight-line program, the channels, all units, the tapes, the states plus one, the row
data, the roles, the slots and channels of a role, and the numbers `qn` of the states and
`tg r + 4` of the roles. -/
structure Codes.SizeBounds (C : Codes S M U0 U1 D pS) (qn : Q → ℕ) (tg : M.Role → ℕ)
    (X Lc : ℕ) : Prop where
  /-- The codes are not empty. -/
  one_le_Lc : 1 ≤ Lc
  /-- The codes of the names. -/
  name : ∀ y, (C.name y).length ≤ Lc
  /-- The codes of the digits. -/
  digit : ∀ d, (C.digit d).length ≤ Lc
  /-- The codes of the row data. -/
  rowData : ∀ d, (C.rowData d).length ≤ Lc
  /-- The keys of the cells. -/
  key : ∀ c, (C.key c).length ≤ Lc
  /-- The keys of the second copies. -/
  dkey : ∀ c, (C.dkey c).length ≤ Lc
  /-- The blocks, plus one. -/
  blocks : K + 1 ≤ X
  /-- The base parties. -/
  parties : K + K ≤ X
  /-- The units of a string, plus one. -/
  initUnits : U0 + 1 ≤ X
  /-- The units of a channel. -/
  newUnits : U1 ≤ X
  /-- The moves, plus one. -/
  moves : E + 1 ≤ X
  /-- The digits. -/
  digits : D ≤ X
  /-- The steps of the straight-line program. -/
  gates : pS ≤ X
  /-- The channels. -/
  channels : Fintype.card M.Channel ≤ X
  /-- All units. -/
  units : Fintype.card (UnitId (K + K) U0 M.Channel U1) ≤ X
  /-- The tapes. -/
  tapes : Fintype.card (Option S) ≤ X
  /-- The states, plus one. -/
  states : Fintype.card Q + 1 ≤ X
  /-- The row data. -/
  rowDatas : Fintype.card (RowData (K + K)) ≤ X
  /-- The roles. -/
  roles : Fintype.card M.Role ≤ X
  /-- The slots of a role. -/
  slotsAt : ∀ r : M.Role, Fintype.card ((M.law r.1).SlotAt r.2) ≤ X
  /-- The channels of a role. -/
  channelsAt : ∀ r : M.Role, Fintype.card ((M.law r.1).ChannelAt r.2) ≤ X
  /-- The numbers of the states. -/
  stateNum : ∀ q, qn q ≤ X
  /-- The numbers of the roles of laws, plus four. -/
  roleNum : ∀ r, tg r + 4 ≤ X

variable {C : Codes S M U0 U1 D pS} {qn : Q → ℕ} {tg : M.Role → ℕ} {X Lc : ℕ}
  (H : C.SizeBounds qn tg X Lc)
include H

namespace Codes.SizeBounds

theorem one_le_X : 1 ≤ X := (Nat.le_add_left 1 K).trans H.blocks

/-- A code of length at most `Lc` has size at most `5 * Lc`. -/
theorem size_ofBits_le {w : List Bool} (hw : w.length ≤ Lc) : (ofBits w).size ≤ 5 * Lc := by
  have := size_ofBits w
  have := H.one_le_Lc
  omega

/-- The units of the bounds increase. -/
theorem le_mul_X (u : ℕ) : u ≤ X * u := Nat.le_mul_of_pos_left u H.one_le_X

end Codes.SizeBounds

/-- The trie of a function on at most `X` elements with codes of length at most `Lc` and values
of size at most `b * u`, for `Lc ≤ u`. -/
private theorem size_trieOf_le_mul {α : Type*} [Fintype α] {code : α → List Bool} {f : α → Tree}
    {b u : ℕ} (hc : ∀ a, (code a).length ≤ Lc) (hα : Fintype.card α ≤ X)
    (hf : ∀ a, (f a).size ≤ b * u) (hu : Lc ≤ u) : (trieOf code f).size ≤ (b + 9) * (X * u) := by
  have h1 := size_trieOf_le hc hf
  have h2 := Nat.mul_le_mul_right (b * u + 4 * Lc + 4) hα
  have := H.one_le_Lc
  have := H.le_mul_X u
  have : X * (b * u + 4 * Lc + 4) ≤ X * (b * u + 8 * u) := Nat.mul_le_mul_left X (by omega)
  nlinarith

/-- The keys of at most `X` units. -/
private theorem size_wordsEnc_le {ks : List (List Bool)} (hl : ks.length ≤ X)
    (h : ∀ k ∈ ks, k.length ≤ Lc) : (wordsEnc ks).size ≤ 7 * (X * Lc) :=
  size_listT_le_mul H.one_le_X H.one_le_Lc (by simpa [wordsEnc] using hl) fun t ht => by
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 ht
    exact H.size_ofBits_le (h k hk)

/-- A pick from at most `X` options of at most four assignments each, of values of size at most
`19 * (X * Lc)`. -/
private theorem size_pickStep_le {α : Type*} {opts : List α}
    {o : α → List (PlanName S M U0 U1 pS × Tree)} (hl : opts.length ≤ X)
    (ho : ∀ x ∈ opts, (o x).length ≤ 4 ∧ ∀ y ∈ o x, y.2.size ≤ 19 * (X * Lc)) :
    (C.pickStep opts o).tree.size ≤ 120 * (X * (X * Lc)) := by
  have hX := H.one_le_X
  have hLc := H.one_le_Lc
  have h1 := H.le_mul_X Lc
  have h2 := H.le_mul_X (X * Lc)
  have := size_listT_le_mul (a := 105) (l := opts.map fun x => optionTree C.name (o x)) hX
    (h1.trans' hLc) (by simpa using hl) fun t ht => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ht
      refine (size_listT_le (X := 4) (s := 25 * (X * Lc))
        (l := (o x).map fun y => .cons (ofBits (C.name y.1)) y.2) (by simpa using (ho x hx).1)
          fun t ht => ?_).trans (by omega)
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 ht
      have := H.size_ofBits_le (H.name y.1)
      have := (ho x hx).2 y hy
      simp only [Tree.size]
      omega
  have := H.size_ofBits_le (H.name .empty)
  simp only [Codes.pickStep, DStep.tree, Tree.size, num] at *
  omega

/-- An operation with a table of size at most `25 * (X * (X * Lc))`. -/
private theorem size_op_le (x y z : PlanName S M U0 U1 pS) {φ : Tree}
    (hφ : φ.size ≤ 25 * (X * (X * Lc))) :
    (DStep.op (C.name x) (C.name y) (C.name z) φ).tree.size ≤ 120 * (X * (X * Lc)) := by
  have := H.size_ofBits_le (H.name x)
  have := H.size_ofBits_le (H.name y)
  have := H.size_ofBits_le (H.name z)
  have := H.le_mul_X Lc
  have := H.le_mul_X (X * Lc)
  have := H.one_le_Lc
  simp only [DStep.tree, Tree.size, num]
  omega

private theorem size_unaryStep_le (x dst : PlanName S M U0 U1 pS) {f : Fin D → Tree}
    (hf : ∀ d, (f d).size ≤ 5 * (X * Lc)) :
    (C.unaryStep x dst f).tree.size ≤ 120 * (X * (X * Lc)) := by
  have := H.le_mul_X (X * Lc)
  refine size_op_le H x .empty dst ((size_trieOf_le_mul (b := 7) H H.digit
    (by simpa using H.digits) (fun d => ?_) (H.le_mul_X Lc)).trans (by omega))
  have := hf d
  have := (H.le_mul_X Lc).trans' H.one_le_Lc
  simp only [Tree.size]
  omega

variable {nI mm : ℕ} {P : Plan M U0 U1}
  {grp : PlanInput M U0 U1 → Fin (K + K + A') → Fin mm} (tab : SlpTab P grp D nI pS)

/-- The steps up to the checks have size at most `120 * (X * (X * Lc))` each. -/
private theorem size_dealSteps_le (i e : Q) (hU0 : U0 < D) (hU1 : U1 ≤ D) :
    ∀ s ∈ C.dealSteps tab qn i e hU0 hU1, s.tree.size ≤ 120 * (X * (X * Lc)) := by
  classical
  have hX := H.one_le_X
  have hLc := H.one_le_Lc
  have h1 := H.le_mul_X Lc
  have h2 := H.le_mul_X (X * Lc)
  have h0 : X ≤ X * Lc := Nat.le_mul_of_pos_right X hLc
  have hd (d : Fin D) : (C.digitTree d).size ≤ 5 * Lc := H.size_ofBits_le (H.digit d)
  have hb (c : Bool) : (bit c).size ≤ 3 * Lc := by
    cases c <;> simp only [bit, Bool.false_eq_true, ↓reduceIte, one, Tree.size] <;> omega
  intro s hs
  simp only [Codes.dealSteps, Codes.choiceSteps, Codes.stateSteps, Codes.rowDataSteps,
    Codes.countSteps, Codes.outcomeSteps, Codes.rowCheckSteps, Codes.gateSteps,
    Codes.readOutSteps, Codes.checkSteps, List.mem_append, List.mem_map, mem_toList, mem_univ,
    true_and, List.mem_finRange] at hs
  rcases hs with (⟨a, rfl⟩ | ⟨a, rfl⟩ | ⟨⟨a, b⟩, rfl⟩ | ⟨ν, rfl⟩) | ⟨⟨s', p⟩, rfl⟩ | ⟨k, rfl⟩ |
    ⟨a, rfl⟩ | ⟨_, (⟨a, rfl⟩ | ⟨c, rfl⟩), rfl⟩
  · refine size_pickStep_le H ?_ fun q _ => ⟨by simp, fun y hy => ?_⟩
    · have := H.states
      unfold stateOptions
      split_ifs <;> simp only [List.length_singleton, length_toList, card_univ] <;> omega
    · obtain rfl := List.mem_singleton.1 hy
      have := H.stateNum q
      simp only [size_num]
      omega
  · refine size_pickStep_le H (by simpa using H.rowDatas) fun d _ => ⟨by simp, fun y hy => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl
    · refine (size_listT_le (s := 5) (by simpa using H.parties) fun t ht => ?_).trans (by omega)
      simp only [List.mem_map, List.mem_reverse, List.mem_ofFn] at ht
      obtain ⟨_, ⟨b, rfl⟩, rfl⟩ := ht
      have : rowFlag d b ≤ 2 := by unfold rowFlag; split_ifs <;> omega
      rw [size_num]
      omega
    · have := H.size_ofBits_le (H.rowData d)
      simp only
      omega
  · have hm (m : Fin (U0 + 1)) : (indicesBelow m).length ≤ X := by
      simpa using m.is_le.trans (Nat.le_of_succ_le H.initUnits)
    have hk (f : Fin U0 → List Bool) (hf : ∀ k, (f k).length ≤ Lc) (m : Fin (U0 + 1)) :
        (wordsEnc ((indicesBelow m).map f)).size ≤ 7 * (X * Lc) :=
      size_wordsEnc_le H (by simpa using hm m) fun k hk => by
        obtain ⟨j, -, rfl⟩ := List.mem_map.1 hk; exact hf j
    refine size_pickStep_le H (by simpa using H.initUnits) fun m _ => ⟨?_, fun y hy => ?_⟩
    · simp only [Codes.countOption, List.length_cons]; split_ifs <;> simp
    simp only [Codes.countOption, List.mem_cons] at hy
    rcases hy with rfl | rfl | rfl | hy
    · exact (hk (fun k => C.key ⟨Fin.castAdd A' a, .init a b k⟩) (fun _ => H.key _) m).trans
        (by omega)
    · have := hk (fun k => if a = b then C.dkey (b, k) else C.key ⟨Fin.castAdd A' b, .init a b k⟩)
        (fun k => by split_ifs; exacts [H.dkey _, H.key _]) m
      exact this.trans (by omega)
    · have := hd (Fin.castLE hU0 m)
      exact this.trans (by omega)
    · split_ifs at hy with hab
      · obtain rfl := List.mem_singleton.1 hy
        refine (size_listT_le_mul (a := 17) hX hLc (by simpa using hm m) fun t ht => ?_).trans
          (by omega)
        obtain ⟨k, -, rfl⟩ := List.mem_map.1 ht
        have := H.size_ofBits_le (H.key ⟨Fin.castAdd A' a, .init a a k⟩)
        have := H.size_ofBits_le (H.dkey (a, k))
        simp only [Instruction.enc, Tree.size, size_num]
        omega
      · simp at hy
  · refine size_pickStep_le H (by simpa using H.newUnits) fun j _ => ⟨by simp, fun y hy => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    have hn (d : Bool) : (C.newKeysTree ν d j).size ≤ 7 * (X * Lc) :=
      size_wordsEnc_le H (by simpa using j.is_lt.trans_le H.newUnits) fun k hk => by
        obtain ⟨_, -, rfl⟩ := List.mem_map.1 hk; exact H.key _
    rcases hy with rfl | rfl | rfl
    · exact (hd _).trans (by omega)
    · exact (hn false).trans (by omega)
    · exact (hn true).trans (by omega)
  · simp only [uncurry_apply_pair, Codes.rowCheckStep]
    split_ifs
    · refine size_op_le H _ _ _ ?_
      have := size_trieOf_le_mul H (f := fun d => bit (decide (RowValidAfter 0 d))) H.rowData
        H.rowDatas (fun d => hb _) le_rfl
      simp only [Tree.size]
      omega
    · exact size_op_le H _ _ _ ((size_trieOf_le_mul (b := 12) H H.rowData H.rowDatas
        (fun d => size_trieOf_le_mul H H.rowData H.rowDatas (fun d => hb _) le_rfl) h1).trans
          (by omega))
  · have hc (dst : PlanName S M U0 U1 pS) {t : Tree} (ht : t.size ≤ 5 * Lc) :
        (C.constStep dst t).tree.size ≤ 120 * (X * (X * Lc)) :=
      size_op_le H _ _ _ (by simp only [Tree.size]; omega)
    unfold Codes.gateStep
    split_ifs
    · exact size_unaryStep_le H _ _ fun d => (hd d).trans (by omega)
    · exact hc _ (hd _)
    · exact size_op_le H _ _ _ ((size_trieOf_le_mul (b := 14) H H.digit (by simpa using H.digits)
        (fun d => size_trieOf_le_mul H H.digit (by simpa using H.digits) (fun d => hd _) le_rfl)
          h1).trans (by omega))
    · exact hc _ (by simp [Tree.size]; omega)
  · have hD : D ≤ X := H.digits
    rcases a with x | c | u <;> refine size_unaryStep_le H _ _ fun d => ?_
    · rw [size_num]; omega
    all_goals exact (hb _).trans (by omega)
  all_goals
    refine (show ∀ y, (DStep.check (C.name y)).tree.size ≤ 120 * (X * (X * Lc)) from fun y => ?_) _
    have := H.size_ofBits_le (H.name y)
    simp only [DStep.tree, Tree.size, num]
    omega

omit H in
/-- **The number of the steps up to the checks**, if `X` bounds the numbers of the blocks plus
one, the base parties, the tapes, the channels, the steps of the straight-line program, the moves
plus one and the units. -/
theorem length_dealSteps_le (hK1 : K + 1 ≤ X) (hK2 : K + K ≤ X)
    (hS : Fintype.card (Option S) ≤ X) (hN : Fintype.card M.Channel ≤ X) (hpS : pS ≤ X)
    (hE : E + 1 ≤ X) (hU : Fintype.card (UnitId (K + K) U0 M.Channel U1) ≤ X) (i e : Q)
    (hU0 : U0 < D) (hU1 : U1 ≤ D) :
    (C.dealSteps tab qn i e hU0 hU1).length ≤ 4 * (X * X) + 7 * X := by
  have h1 := Nat.mul_le_mul hS hK2
  have h2 := Nat.mul_le_mul hK2 hK2
  simp only [Codes.dealSteps, Codes.choiceSteps, Codes.stateSteps, Codes.rowDataSteps,
    Codes.countSteps, Codes.outcomeSteps, Codes.rowCheckSteps, Codes.gateSteps,
    Codes.readOutSteps, Codes.checkSteps, List.length_append, List.length_map, length_toList,
    card_univ, Fintype.card_prod, Fintype.card_sum, Fintype.card_option, Fintype.card_fin,
    List.length_finRange] at h1 ⊢
  omega

/-- **The size of the steps up to the checks**, as a list of trees. -/
theorem size_listT_dealSteps_le (i e : Q) (hU0 : U0 < D) (hU1 : U1 ≤ D) :
    (listT ((C.dealSteps tab qn i e hU0 hU1).map DStep.tree)).size ≤
      1332 * (X * (X * (X * (X * Lc)))) := by
  have hl := length_dealSteps_le (C := C) (qn := qn) tab H.blocks H.parties H.tapes H.channels
    H.gates H.moves H.units i e hU0 hU1
  have h := size_listT_le (s := 120 * (X * (X * Lc))) (X := 4 * (X * X) + 7 * X)
    (l := (C.dealSteps tab qn i e hU0 hU1).map DStep.tree) (by simpa using hl) fun t ht => by
      obtain ⟨s, hs, rfl⟩ := List.mem_map.1 ht
      exact size_dealSteps_le H tab i e hU0 hU1 s hs
  have a1 : 1 ≤ X * Lc := Nat.mul_le_mul H.one_le_X H.one_le_Lc
  have a2 := H.le_mul_X (X * Lc)
  have a3 := H.le_mul_X (X * (X * Lc))
  have a4 := H.le_mul_X (X * (X * (X * Lc)))
  have a5 : X * X ≤ X * (X * Lc) := Nat.mul_le_mul_left X (Nat.le_mul_of_pos_right X H.one_le_Lc)
  have a6 : X ≤ X * Lc := Nat.le_mul_of_pos_right X H.one_le_Lc
  nlinarith

/-- **The size of the guesses of the contents**, as a list of trees. -/
theorem size_listT_contentSteps_le :
    (listT (C.contentSteps.map DStep.tree)).size ≤ 19 * (X * Lc) :=
  size_listT_le_mul H.one_le_X H.one_le_Lc (by simpa [Codes.contentSteps] using H.units)
    fun t ht => by
      obtain ⟨_, hs, rfl⟩ := List.mem_map.1 ht
      obtain ⟨u, -, rfl⟩ := List.mem_map.1 hs
      have := H.size_ofBits_le (H.name (.isCut u))
      have := H.size_ofBits_le (H.name (.content u))
      have := H.one_le_Lc
      simp only [DStep.tree, Tree.size, num]
      omega

end Cslib.Circuits.Arithmetic.Separation.Dealing
