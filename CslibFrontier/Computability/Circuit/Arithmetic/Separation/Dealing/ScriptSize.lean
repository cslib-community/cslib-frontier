/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.GroupProgram.GroupScript
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Cuts.MoveIdentity
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Interpreter.AccSize
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Interpreter.Guess
import CslibFrontier.Foundations.Data.List.Blocks
import CslibFrontier.Foundations.Data.List.FilterMap
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The size of the script of a group

A unit that the dealing program of [AnthropicVPVNP2026] cuts between two groups lies in a group
`g` with exactly one of its holders (`OneIn`). The script of the group `g` (`groupScript`) is
small: its size is at most `200 * X ^ 3 * Lc`, where `X` bounds the numbers of parties, tapes,
units, roles, slots, channels, states and units of a move and `Lc` the lengths of the keys and of
the binary numbers, plus the codes of the letters of the input parts of the group and the bits of
the units cut with one holder in the group (`size_scriptEnc_le`).

## Main definitions

* `OneIn`: exactly one of the two holders of a unit is in a group.

## Main results

* `oneIn_iff`: `OneIn` without `Xor`.
* `size_scriptEnc_le`: the size of the script of a group.

## References

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], Appendix J.3: the scripts in the proof of
Theorem J.3 (p. 54: a script has `(s/k + M/k)Λ` input symbols, the bits of the cut packets, and
`v^O(1)` names and instructions). Ported from the source modules `Nc.Dl.SizeScript` and
`Nc.Plus.Interface` (`OneIn`).
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Dealing

open Finset Interpreter Interpreter.Tree Cut GroupProgram

/-- Exactly one of the two holders `h u false`, `h u true` of the unit `u` is in the group `g`. -/
@[expose] def OneIn {U A G : Type*} (h : U → Bool → A) (grp : A → G) (g : G) (u : U) : Prop :=
  Xor (grp (h u false) = g) (grp (h u true) = g)

instance {U A G : Type*} [DecidableEq G] (h : U → Bool → A) (grp : A → G) (g : G) (u : U) :
    Decidable (OneIn h grp g u) :=
  inferInstanceAs (Decidable (Xor _ _))

/-- Exactly one holder of `u` is in `g` if and only if not both or neither of them are. -/
theorem oneIn_iff {U A G : Type*} {h : U → Bool → A} {grp : A → G} {g : G} {u : U} :
    OneIn h grp g u ↔ ¬(grp (h u false) = g ↔ grp (h u true) = g) :=
  xor_iff_not_iff _ _

section Sizes

private theorem sum_map_le {α : Type*} {l : List α} {f : α → ℕ} {X s : ℕ} (hl : l.length ≤ X)
    (h : ∀ a ∈ l, f a ≤ s) : (l.map f).sum ≤ X * s :=
  (List.sum_le_length_nsmul _ s (by simpa using h)).trans (by simpa using Nat.mul_le_mul_right s hl)

private theorem size_wordsEnc_le {ks : List (List Bool)} {X Lc : ℕ} (hl : ks.length ≤ X)
    (h : ∀ k ∈ ks, k.length ≤ Lc) : (wordsEnc ks).size ≤ X * (4 * Lc + 2) + 1 :=
  size_listT_le (s := 4 * Lc + 1) (by simpa using hl) fun t ht => by
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 ht
    have := size_ofBits k
    have := h k hk
    omega

private theorem size_keysEnc_le {kss : List (List (List Bool))} {X Lc : ℕ} (hl : kss.length ≤ X)
    (h : ∀ ks ∈ kss, ks.length ≤ X ∧ ∀ k ∈ ks, k.length ≤ Lc) :
    (keysEnc kss).size ≤ X * (X * (4 * Lc + 2) + 2) + 1 :=
  size_listT_le (by simpa using hl) fun t ht => by
    obtain ⟨ks, hks, rfl⟩ := List.mem_map.1 ht
    exact size_wordsEnc_le (h ks hks).1 (h ks hks).2

end Sizes

variable {F : Type} [CommRing F] {Γ S Q : Type} [Fintype S] [DecidableEq S]
  {A' E K U0 U1 ub c X Lc : ℕ} {G : Type} [DecidableEq G] {M : Moves F (K + K + A') E}
  {qn : Q → ℕ} {cb : Option Γ → Fin c → Bool} {P : Plan M U0 U1} {q : Fin (K + 1) → Q}
  {x : Fin K → List Γ} {ρ : Option S → Fin (K + K) → RowData (K + K)}
  {n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1)} {o : M.Channel → Fin U1}
  {grp : Fin (K + K + A') → G} {g : G} {key : Cell M U0 U1 → List Bool}
  {dkey : Fin (K + K) × Fin U0 → List Bool} {tg : M.Role → ℕ}

omit [DecidableEq S] in
private theorem size_baseBody_le (hK : K + K ≤ X) (hU0 : U0 ≤ X) (hS : Fintype.card (Option S) ≤ X)
    (hk : ∀ c, (key c).length ≤ Lc) (hd : ∀ c, (dkey c).length ≤ Lc) (p : Fin (K + K)) :
    (baseBody ρ n key dkey p).enc.size ≤ X * X * (8 * Lc + 10) + 6 * X + 5 := by
  have hflags : (listT ((baseBody ρ n key dkey p).flags.map fun l => listT (l.map num))).size ≤
      X * (X * 6 + 1 + 1) + 1 := by
    refine size_listT_le (by simpa [baseBody, tapes] using hS) fun t ht => ?_
    simp only [baseBody, List.map_map, List.mem_map, Function.comp_apply] at ht
    obtain ⟨s, -, rfl⟩ := ht
    refine size_listT_le (s := 5) (by simpa using hK) fun t ht => ?_
    simp only [List.mem_map, List.mem_reverse, List.mem_ofFn] at ht
    obtain ⟨_, ⟨b, rfl⟩, rfl⟩ := ht
    rw [size_num]
    have : rowFlag (ρ s p) b ≤ 2 := by unfold rowFlag; split_ifs <;> omega
    omega
  have hkeys (m : Fin (K + K) → Fin (U0 + 1)) (f : Fin (K + K) → Fin U0 → List Bool)
      (hf : ∀ b k, (f b k).length ≤ Lc) :
      (keysEnc (List.ofFn fun b => (indicesBelow (m b)).map (f b))).size ≤
        X * (X * (4 * Lc + 2) + 2) + 1 :=
    size_keysEnc_le (by simpa using hK) fun ks hks => by
      obtain ⟨b, rfl⟩ := List.mem_ofFn.1 hks
      refine ⟨by simpa using (Nat.lt_succ_iff.1 (m b).isLt).trans hU0, fun k hk' => ?_⟩
      obtain ⟨_, -, rfl⟩ := List.mem_map.1 hk'
      exact hf _ _
  have h1 : (keysEnc (baseBody ρ n key dkey p).writeKeys).size ≤
      X * (X * (4 * Lc + 2) + 2) + 1 := hkeys (n p) _ fun _ _ => hk _
  have h2 : (keysEnc (baseBody ρ n key dkey p).readKeys).size ≤
      X * (X * (4 * Lc + 2) + 2) + 1 :=
    hkeys (fun b => n b p) _ fun b _ => by split_ifs; exacts [hd _, hk _]
  simp only [Body.enc, Tree.size]
  ring_nf at hflags h1 h2 ⊢
  omega

omit [DecidableEq S] in
/-- **The size of the script of a group.** If `X` bounds the numbers of the base parties, the
tapes, the units, the roles and the slots and channels of a role, the units at the beginning
and of a channel, the numbers of the states and of the roles of laws, and the units of a move, and
`Lc` bounds the lengths of the keys and of the binary numbers `bT`, `bub`, then the script of the
group `g` has size at most `200 * X ^ 3 * Lc`, plus `4 * c + 2` for every letter of an input part
of the group and `4 * ub` for every current unit with exactly one holder in the group. -/
theorem size_scriptEnc_le (hX : 1 ≤ X) (hLc : 1 ≤ Lc) (hK : K + K ≤ X) (hU0 : U0 ≤ X)
    (hU1 : U1 ≤ X) (hS : Fintype.card (Option S) ≤ X)
    (hU : Fintype.card (UnitId (K + K) U0 M.Channel U1) ≤ X) (hR : Fintype.card M.Role ≤ X)
    (hsl : ∀ r : M.Role, Fintype.card ((M.law r.1).SlotAt r.2) ≤ X)
    (hcn : ∀ r : M.Role, Fintype.card ((M.law r.1).ChannelAt r.2) ≤ X)
    (hk : ∀ c, (key c).length ≤ Lc) (hd : ∀ c, (dkey c).length ≤ Lc) (hqn : ∀ a, qn a ≤ X)
    (htg : ∀ r, tg r ≤ X) (hcount : ∀ y, P.count n o y ≤ X) {bT bub : List Bool}
    (hbT : bT.length ≤ Lc) (hbub : bub.length ≤ Lc)
    (b : UnitId (K + K) U0 M.Channel U1 → UnitContent ub) :
    (scriptEnc bT bub (groupScript qn cb P q x ρ n o grp g key dkey tg b)).size ≤
      200 * X ^ 3 * Lc +
        (∑ κ with grp (Fin.castAdd A' (Fin.natAdd K κ)) = g, (x κ).length) * (4 * c + 2) +
        ((P.cur n o E).filter (OneIn (UnitId.holder M.channelParty) grp g)).card * (4 * ub) := by
  classical
  -- the base parties
  let plen : Fin (K + K) → ℕ := Fin.addCases (fun _ => 0) fun κ => (x κ).length
  have hbase (p : Fin (K + K)) : ((baseInstructions qn cb q x ρ n key dkey p).map
      fun i => i.enc.size + 1).sum ≤
        X * X * (8 * Lc + 10) + 10 * X + 12 + X * (8 * Lc + 10) + plen p * (4 * c + 2) := by
    have hB := size_baseBody_le (ρ := ρ) (n := n) hK hU0 hS hk hd p
    have hagree : (((indicesBelow (n p p)).map fun k => Instruction.agree
        (key ⟨Fin.castAdd A' p, .init p p k⟩) (dkey (p, k))).map fun i => i.enc.size + 1).sum ≤
          X * (8 * Lc + 10) := by
      rw [List.map_map]
      refine sum_map_le (by simpa using (n p p).is_le.trans hU0) fun k _ => ?_
      have := size_ofBits (key ⟨Fin.castAdd A' p, .init p p k⟩)
      have := size_ofBits (dkey (p, k))
      have := hk ⟨Fin.castAdd A' p, .init p p k⟩
      have := hd (p, k)
      simp only [Function.comp_apply, Instruction.enc, Tree.size, size_num]
      omega
    rw [baseInstructions, List.map_cons, List.sum_cons]
    induction p using Fin.addCases with
    | left κ =>
      have := hqn (q κ.castSucc)
      have := hqn (q κ.succ)
      simp only [Fin.addCases_left, plen, Instruction.enc, Tree.size, size_num] at hB hagree ⊢
      omega
    | right κ =>
      have hw : (wordsEnc ((x κ).map (letterCode cb)).reverse).size ≤
          (x κ).length * (4 * c + 2) + 1 :=
        size_wordsEnc_le (by simp) fun k hk => by
          rcases List.mem_map.1 (List.mem_reverse.1 hk) with ⟨_, -, rfl⟩
          simp [letterCode]
      simp only [Fin.addCases_right, plen, Instruction.enc, Tree.size, size_num] at hB hagree ⊢
      omega
  have hplen : ((baseParties grp g).map plen).sum =
      ∑ κ with grp (Fin.castAdd A' (Fin.natAdd K κ)) = g, (x κ).length := by
    rw [baseParties_eq_filter, ← List.sum_toFinset _ ((List.nodup_finRange _).filter _),
      List.toFinset_filter, List.toFinset_finRange, sum_filter, sum_filter, Fin.sum_univ_add]
    simp [-Fin.natAdd_eq_addNat]
  have h1 : (((baseParties grp g).flatMap (baseInstructions qn cb q x ρ n key dkey)).map
      fun i => i.enc.size + 1).sum ≤ X * (X * X * (8 * Lc + 10) + 10 * X + 12 + X * (8 * Lc + 10)) +
        (∑ κ with grp (Fin.castAdd A' (Fin.natAdd K κ)) = g, (x κ).length) * (4 * c + 2) := by
    have hl : (baseParties grp g).length ≤ X := by
      rw [baseParties_eq_filter]
      exact (List.length_filter_le _ _).trans (by simpa using hK)
    rw [List.sum_map_flatMap, ← hplen]
    refine (List.sum_le_sum fun p _ => hbase p).trans ?_
    rw [List.sum_map_add, List.sum_map_mul_right, List.map_const', List.sum_replicate, smul_eq_mul]
    exact Nat.add_le_add_right (Nat.mul_le_mul_right _ hl) _
  -- the roles
  have h2 : ((groupRoles grp g M).map fun r => (roleInstruction P n o key tg r).enc.size + 1).sum ≤
      X * (X * X * (8 * Lc + 4) + 8 * X + 16) := by
    refine sum_map_le ((nodup_groupRoles grp g M).length_le_card.trans hR) fun r _ => ?_
    have hs := size_keysEnc_le (X := X) (Lc := Lc) (kss := (slotList (M.law r.1) r.2).map fun e =>
      ((P.ids n o ⟨r.1, e.val⟩).map fun u => key ⟨M.roleParty r, u⟩).reverse)
      (by simpa [slotList] using hsl r) fun ks hks => by
        obtain ⟨e, -, rfl⟩ := List.mem_map.1 hks
        refine ⟨?_, fun k hk' => ?_⟩
        · simpa [Plan.ids] using (List.length_filter_le _ _).trans (by simpa [UnitId.list] using hU)
        · rcases List.mem_map.1 (List.mem_reverse.1 hk') with ⟨_, -, rfl⟩
          exact hk _
    have hc := size_keysEnc_le (X := X) (Lc := Lc) (kss := (channelList (M.law r.1) r.2).map
      fun ν => (indicesBelow (o ⟨r.1, ν.val⟩).succ).map fun k =>
        key ⟨M.roleParty r, .new ⟨r.1, ν.val⟩ k⟩)
      (by simpa [channelList] using hcn r) fun ks hks => by
        obtain ⟨ν, -, rfl⟩ := List.mem_map.1 hks
        refine ⟨by simpa using Nat.succ_le_of_lt ((o ⟨r.1, ν.val⟩).isLt.trans_le hU1),
          fun k hk' => ?_⟩
        obtain ⟨_, -, rfl⟩ := List.mem_map.1 hk'
        exact hk _
    have := htg r
    have := hcount r.1
    simp only [roleInstruction, Instruction.enc, Tree.size, size_num]
    ring_nf at hs hc ⊢
    omega
  -- the end
  have h3 : ((endInstructions P n o grp g key b).map fun i => i.enc.size + 1).sum ≤
      X * (8 * Lc + 12) +
        ((P.cur n o E).filter (OneIn (UnitId.holder M.channelParty) grp g)).card * (4 * ub) := by
    rw [endInstructions]
    refine (List.sum_map_filterMap_le (D := fun u => 8 * Lc + 12 +
      if OneIn (UnitId.holder M.channelParty) grp g u then 4 * ub else 0) (fun u i hi => ?_)
      _).trans ?_
    · have := hk ⟨UnitId.holder M.channelParty u false, u⟩
      have := hk ⟨UnitId.holder M.channelParty u true, u⟩
      have := size_ofBits (key ⟨UnitId.holder M.channelParty u false, u⟩)
      have := size_ofBits (key ⟨UnitId.holder M.channelParty u true, u⟩)
      have := size_ofBits (b u).bits
      have := UnitContent.length_bits_le (b u)
      by_cases h0 : grp (UnitId.holder M.channelParty u false) = g <;>
        by_cases h1 : grp (UnitId.holder M.channelParty u true) = g <;>
        simp only [h0, h1, ↓reduceIte, reduceCtorEq, Option.some.injEq] at hi <;>
        subst hi <;> simp [OneIn, h0, h1, Instruction.enc, Tree.size, size_num] <;> omega
    · rw [List.sum_map_add, List.map_const', List.sum_replicate, smul_eq_mul]
      refine Nat.add_le_add (Nat.mul_le_mul_right _ ((List.length_filter_le _ _).trans
        (by simpa [UnitId.list] using hU))) (le_of_eq ?_)
      rw [UnitId.list, ← List.sum_toFinset _ ((nodup_toList _).filter _), List.toFinset_filter,
        toList_toFinset, sum_ite, sum_const_zero, add_zero, sum_const, smul_eq_mul, filter_filter]
      congr 2
      ext u
      simp
  have := size_ofBits bT
  have := size_ofBits bub
  simp only [scriptEnc, groupScript, Tree.size, size_listT, List.map_append, List.sum_append,
    List.map_map, Function.comp_def]
  have hX3 : X * (X * X * (8 * Lc + 10) + 10 * X + 12 + X * (8 * Lc + 10)) +
      X * (X * X * (8 * Lc + 4) + 8 * X + 16) + X * (8 * Lc + 12) + 8 * Lc + 6 ≤
        200 * X ^ 3 * Lc := by
    have a1 : X ≤ X ^ 2 := Nat.le_self_pow two_ne_zero X
    have a2 : X ^ 2 ≤ X ^ 3 := Nat.pow_le_pow_right hX (by decide)
    nlinarith [Nat.mul_le_mul_right Lc a1, Nat.mul_le_mul_right Lc a2]
  omega

end Cslib.Circuits.Arithmetic.Separation.Dealing
