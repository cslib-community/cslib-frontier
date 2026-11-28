/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.GroupProgram.GroupScript
public import CslibFrontier.Foundations.Data.BitString.List.Binary
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Cuts.MoveIdentity
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Cuts.PlayMoves
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.GroupProgram.Executions
import CslibFrontier.Foundations.Data.List.Blocks
import CslibFrontier.Foundations.Data.List.FilterMap
import Mathlib.Tactic.Linarith

/-!
# The time of GROUP at the script of a group

The cost of the program GROUP of [AnthropicVPVNP2026] at a script is linear in the costs of its
instructions and in the binary numbers `T` and `ub` times their lengths (`groupTime`, the time in
`exists_formula_scriptSem`). At the script of a group (`groupScript`), whose keys have at most
`Lc` bits, this time is bounded by the numbers of cells of the group (`cellCount`), of the units
that its roles read (`roleUnitCount`), and of the units of its base parties, times the size
`ub + Lc + 1` of a unit with its key, plus `T` for every base party and a cube in a bound `X` of
the numbers of tapes, parties, roles, slots and channels (`groupTime_le`).

## Main definitions

* `groupTime`: the time of GROUP at a script.
* `cellCount`, `roleUnitCount`: the number of cells of a group, and of the units that its roles
  read.

## Main results

* `putCost_le`: the cost of writing units at lists of keys.
* `groupTime_le`: the time of GROUP at the script of a group.

## References

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], Appendix J.3: the evaluator described in the
proof of Theorem J.3 (the theorem on p. 53, the evaluator on p. 54). Ported from the source module
`Nc.Grp.GrpTime`.
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.GroupProgram

open Cut Finset

/-- The time of GROUP at the script `l` with the binary numbers `bT` and `bub`: the cost of
reading the two numbers and the costs of the instructions, plus one for every instruction. -/
@[expose] def groupTime (bT bub : List Bool) (l : List Instruction) : ℕ :=
  (bT.length + 1) * (BitString.binaryValue bT + 1) +
    (bub.length + 1) * (BitString.binaryValue bub + 1) +
    (l.map (Instruction.cost (BitString.binaryValue bT) (BitString.binaryValue bub))).sum + l.length

/-- **The cost of writing units at lists of keys**, if the keys have at most `Lc` bits: at most
`ub + Lc + 1` for every key and `1` for every list. -/
theorem putCost_le {ub Lc : ℕ} {kss : List (List (List Bool))}
    (h : ∀ ks ∈ kss, ∀ k ∈ ks, k.length ≤ Lc) :
    putCost ub kss ≤ (kss.map List.length).sum * (ub + Lc + 1) + kss.length := by
  induction kss with
  | nil => simp [putCost]
  | cons ks kss ih =>
    have h1 := ih fun ks' h' => h ks' (List.mem_cons_of_mem _ h')
    have h2 := List.sum_le_length_nsmul (ks.map fun k => ub + k.length + 1) (ub + Lc + 1)
      fun y hy => by
        obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hy
        have := h ks List.mem_cons_self k hk
        omega
    simp only [putCost, List.map_cons, List.sum_cons, List.length_cons, List.length_map,
      smul_eq_mul] at h1 h2 ⊢
    nlinarith

section Counts

variable {F : Type*} [CommSemiring F] {A' E K U0 U1 : ℕ} {G : Type*} [DecidableEq G]
  {M : Moves F (K + K + A') E}

/-- The number of cells of the group `g`: for every party of the group, the number of units seen
in the end that it holds. -/
@[expose] def cellCount (n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1)) (o : M.Channel → Fin U1)
    (grp : Fin (K + K + A') → G) (g : G) : ℕ :=
  ∑ a with grp a = g, #{u ∈ Plan.seenAt n o E | Play.Holds (UnitId.holder M.channelParty) a u}

/-- The number of units that the roles of the group `g` read: for every role, the number of units
of its move once, and once more for every slot of the role. -/
@[expose] def roleUnitCount (P : Plan M U0 U1) (n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1))
    (o : M.Channel → Fin U1) (grp : Fin (K + K + A') → G) (g : G) : ℕ :=
  ∑ r with grp (M.roleParty r) = g, (1 + Fintype.card ((M.law r.1).SlotAt r.2)) * P.count n o r.1

variable {n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1)} {o : M.Channel → Fin U1}
  {grp : Fin (K + K + A') → G} {g : G}

private theorem card_groupCells : #(groupCells n o grp g) = cellCount n o grp g := by
  rw [card_eq_sum_card_fiberwise (f := Cell.party) (t := univ.filter fun a => grp a = g)
    fun c hc => mem_filter.2 ⟨mem_univ _, (mem_groupCells.1 hc).1⟩]
  refine sum_congr rfl fun a ha => card_nbij' Cell.unit (fun u => ⟨a, u⟩)
    (fun c hc => ?_) (fun u hu => ?_) (fun c hc => (Finset.mem_filter.1 hc).2 ▸ rfl)
    fun _ _ => rfl
  · simp only [coe_filter, Set.mem_ofPred_eq, mem_groupCells] at hc ⊢
    exact ⟨hc.1.2.1, hc.2 ▸ hc.1.2.2⟩
  · simp only [coe_filter, Set.mem_ofPred_eq, mem_groupCells] at hu ⊢
    exact ⟨⟨(mem_filter.1 ha).2, hu⟩, trivial⟩

end Counts

section Time

variable {F : Type} [CommRing F] {Γ S Q : Type} [Fintype S]
  {A' E K U0 U1 ub c T Lc X : ℕ} {G : Type} [DecidableEq G] {M : Moves F (K + K + A') E}
  {qn : Q → ℕ} {cb : Option Γ → Fin c → Bool} {P : Plan M U0 U1} {q : Fin (K + 1) → Q}
  {x : Fin K → List Γ} {ρ : Option S → Fin (K + K) → RowData (K + K)}
  {n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1)} {o : M.Channel → Fin U1}
  {grp : Fin (K + K + A') → G} {g : G} {key : Cell M U0 U1 → List Bool}
  {dkey : Fin (K + K) × Fin U0 → List Bool} {tg : M.Role → ℕ}

/-- The time of the instructions of a base party. -/
private theorem cost_baseInstructions (hx : ∀ κ, (x κ).length ≤ T)
    (hk : ∀ c, (key c).length ≤ Lc) (hd : ∀ c, (dkey c).length ≤ Lc)
    (hS : Fintype.card (Option S) ≤ X) (hA : K + K ≤ X) (p : Fin (K + K)) :
    ((baseInstructions qn cb q x ρ n key dkey p).map fun i => i.cost T ub + 1).sum ≤
      T + X * X + 3 * X + 2 + 3 * (∑ b, ((n p b : ℕ) + n b p)) * (ub + Lc + 1) := by
  have hW := putCost_le (ub := ub) (Lc := Lc) (kss := (baseBody ρ n key dkey p).writeKeys)
    (by simp [baseBody, hk])
  have hR := putCost_le (ub := ub) (Lc := Lc) (kss := (baseBody ρ n key dkey p).readKeys)
    fun ks hks k hk' => by
      obtain ⟨b, rfl⟩ := List.mem_ofFn.1 hks
      obtain ⟨k, -, rfl⟩ := List.mem_map.1 hk'
      split_ifs
      exacts [hd _, hk _]
  have hfl : ((baseBody ρ n key dkey p).flags.map List.length).sum ≤ X * X := by
    simpa [baseBody, tapes] using Nat.mul_le_mul hS hA
  have hhead : (Fin.addCases (motive := fun _ => Instruction)
      (fun κ => .block (qn (q κ.castSucc)) (qn (q κ.succ)) (baseBody ρ n key dkey p))
      (fun κ => .input ((x κ).map (letterCode cb)).reverse (baseBody ρ n key dkey p)) p).cost T ub
      ≤ T + (baseBody ρ n key dkey p).cost ub := by
    induction p using Fin.addCases <;> simp [Instruction.cost, hx, -Fin.natAdd_eq_addNat]
  have hdiag := List.sum_le_length_nsmul (((indicesBelow (n p p)).map fun k =>
    Instruction.agree (key ⟨Fin.castAdd A' p, .init p p k⟩) (dkey (p, k))).map
      fun i => i.cost T ub + 1) (2 * (ub + Lc + 1)) fun y hy => by
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hy
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hi
    have := hk ⟨Fin.castAdd A' p, .init p p k⟩
    have := hd (p, k)
    simp only [Instruction.cost]; omega
  have hpp : (n p p : ℕ) ≤ ∑ b, (n p b : ℕ) :=
    single_le_sum (f := fun b => (n p b : ℕ)) (fun _ _ => Nat.zero_le _) (mem_univ p)
  have e1 : ((baseBody ρ n key dkey p).writeKeys.map List.length).sum = ∑ b, (n p b : ℕ) := by
    simp [baseBody, List.sum_ofFn]
  have e2 : ((baseBody ρ n key dkey p).readKeys.map List.length).sum = ∑ b, (n b p : ℕ) := by
    simp [baseBody, List.sum_ofFn]
  have e3 : (baseBody ρ n key dkey p).writeKeys.length = K + K := List.length_ofFn
  have e4 : (baseBody ρ n key dkey p).readKeys.length = K + K := List.length_ofFn
  have hppW := Nat.mul_le_mul_right (ub + Lc + 1) hpp
  rw [e1, e3] at hW
  rw [e2, e4] at hR
  simp only [Body.cost, e3, List.length_map, length_indicesBelow, smul_eq_mul] at hhead hdiag
  rw [baseInstructions, List.map_cons, List.sum_cons, sum_add_distrib]
  ring_nf at hfl hW hR hdiag hppW ⊢; omega

/-- The time of the instruction of a role. -/
private theorem cost_roleInstruction {cap : ℕ} (hP : P.Ok cap) (hk : ∀ c, (key c).length ≤ Lc)
    (hsl : ∀ r : M.Role, Fintype.card ((M.law r.1).SlotAt r.2) ≤ X)
    (hcn : ∀ r : M.Role, Fintype.card ((M.law r.1).ChannelAt r.2) ≤ X) (r : M.Role) :
    (roleInstruction P n o key tg r).cost T ub + 1 ≤
      ((1 + Fintype.card ((M.law r.1).SlotAt r.2)) * P.count n o r.1 +
        ∑ ν : (M.law r.1).ChannelAt r.2, ((o ⟨r.1, ν.val⟩ : ℕ) + 1)) *
        (ub + Lc + 1) + 2 * X + 2 := by
  have h1 := putCost_le (ub := ub) (Lc := Lc) (kss := (slotList (M.law r.1) r.2).map fun e =>
    ((P.ids n o ⟨r.1, e.val⟩).map fun u => key ⟨M.roleParty r, u⟩).reverse) fun ks hks k hk' => by
      obtain ⟨e, -, rfl⟩ := List.mem_map.1 hks
      obtain ⟨u, -, rfl⟩ := List.mem_map.1 (List.mem_reverse.1 hk')
      exact hk _
  have h2 := putCost_le (ub := ub) (Lc := Lc) (kss := (channelList (M.law r.1) r.2).map fun ν =>
    (indicesBelow (o ⟨r.1, ν.val⟩).succ).map fun k => key ⟨M.roleParty r, .new ⟨r.1, ν.val⟩ k⟩)
    fun ks hks k hk' => by
      obtain ⟨ν, -, rfl⟩ := List.mem_map.1 hks
      obtain ⟨u, -, rfl⟩ := List.mem_map.1 hk'
      exact hk _
  have h3 : ∑ e : (M.law r.1).SlotAt r.2, (P.ids n o ⟨r.1, e.val⟩).length ≤
      Fintype.card ((M.law r.1).SlotAt r.2) * P.count n o r.1 :=
    (sum_le_sum fun (e : (M.law r.1).SlotAt r.2) _ => (Plan.length_ids (P := P) (n := n)
      (o := o) (z := ⟨r.1, e.val⟩)).trans_le (hP.card_given_le n o ⟨r.1, e.val⟩)).trans (by simp)
  simp only [List.map_map, Function.comp_def, List.length_reverse, List.length_map,
    length_indicesBelow, Fin.val_succ, slotList, channelList, Finset.sum_map_toList,
    Finset.length_toList, card_univ] at h1 h2
  have h4 := hsl r
  have h5 := hcn r
  have h7 := Nat.mul_le_mul_right (ub + Lc + 1) h3
  simp only [roleInstruction, Instruction.cost, slotList, channelList]
  ring_nf at h1 h2 h7 ⊢; omega

omit [Fintype S] in
/-- The new units of the channels of the roles of a group, at their parties, are cells of the
group. -/
private theorem sum_channels_le :
    ∑ r with grp (M.roleParty r) = g, ∑ ν : (M.law r.1).ChannelAt r.2, ((o ⟨r.1, ν.val⟩ : ℕ) + 1) ≤
      cellCount n o grp g := by
  rw [← card_groupCells]
  have e (r : M.Role) : ∑ ν : (M.law r.1).ChannelAt r.2, ((o ⟨r.1, ν.val⟩ : ℕ) + 1) =
      #(univ.sigma fun ν : (M.law r.1).ChannelAt r.2 => Iic (o ⟨r.1, ν.val⟩)) := by
    simp [card_sigma]
  simp only [e, ← card_sigma]
  refine card_le_card_of_injOn (fun z => ⟨M.roleParty z.1, .new ⟨z.1.1, z.2.1.val⟩ z.2.2⟩)
    (fun z hz => ?_) ?_
  · simp only [coe_sigma, Set.mem_sigma_iff, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq,
      coe_univ, Set.mem_univ, coe_Iic, Set.mem_Iic] at hz
    exact roleCells_subset_groupCells _ ((mem_roleCells hz.1).2 ⟨z.2.1, z.2.2, hz.2, rfl⟩)
  · rintro ⟨⟨x, p⟩, ν, k⟩ - ⟨⟨x', p'⟩, ν', k'⟩ - h
    simp only [Cell.mk.injEq, UnitId.new.injEq, Sigma.mk.injEq] at h
    obtain ⟨h1, ⟨rfl, h2⟩, rfl⟩ := h
    obtain rfl : p = p' := M.party_injective x h1
    obtain rfl : ν = ν' := Subtype.ext (eq_of_heq h2)
    rfl

omit [Fintype S] in
/-- The time of the instructions of the end: they compare at most the cells of the group. -/
private theorem cost_endInstructions (hk : ∀ c, (key c).length ≤ Lc)
    (b : UnitId (K + K) U0 M.Channel U1 → UnitContent ub) :
    ((endInstructions P n o grp g key b).map fun i => i.cost T ub + 1).sum ≤
      cellCount n o grp g * (2 * (ub + Lc + 1)) := by
  refine (List.sum_map_filterMap_le (D := fun u =>
    if grp (UnitId.holder M.channelParty u false) = g ∨
      grp (UnitId.holder M.channelParty u true) = g then 2 * (ub + Lc + 1) else 0)
    (fun u i h => ?_) _).trans ?_
  · have := hk ⟨UnitId.holder M.channelParty u false, u⟩
    have := hk ⟨UnitId.holder M.channelParty u true, u⟩
    have := (b u).length_bits_le
    have hD : grp (UnitId.holder M.channelParty u false) = g ∨
        grp (UnitId.holder M.channelParty u true) = g := by
      split_ifs at h <;> tauto
    rw [ite_eq_left hD]
    split_ifs at h <;> cases h <;> simp only [Instruction.cost] <;> omega
  rw [UnitId.list, ← List.sum_toFinset _ ((nodup_toList _).filter _), ← card_groupCells, sum_ite,
    sum_const_zero,
    add_zero, sum_const, smul_eq_mul]
  refine Nat.mul_le_mul_right _ (card_le_card_of_injOn (fun u =>
    ⟨if grp (UnitId.holder M.channelParty u false) = g then UnitId.holder M.channelParty u false
      else UnitId.holder M.channelParty u true, u⟩) (fun u hu => ?_) fun u _ u' _ h => ?_)
  · simp only [coe_filter, Set.mem_ofPred_eq, List.mem_toFinset, List.mem_filter, mem_toList,
      mem_univ, true_and, decide_eq_true_eq] at hu
    rw [Finset.mem_coe, mem_groupCells]
    dsimp only
    refine ⟨by split_ifs <;> tauto, (Plan.mem_cur.1 hu.1).1, ?_⟩
    split_ifs
    exacts [Play.holds_end _ u false, Play.holds_end _ u true]
  · exact congrArg Cell.unit h

/-- **The time of GROUP at the script of a group.** If `T` and `ub` have binary words `bT` and
`bub` of at most `Lc` bits, all keys have at most `Lc` bits, the group has at most `ι` base
parties, each with at most `lh` units at the beginning, at most `ev` cells and at most `pd` units
read by its roles, and `X` bounds the numbers of tapes, parties, roles and of the slots and the
channels of a role, then the time of GROUP at the script is at most
`(Lc + 1) * (T + ub + 2) + ι * T + 3 * (ev + pd + ι * lh) * (ub + Lc + 1) + 10 * X ^ 3`. -/
theorem groupTime_le {cap ι lh ev pd : ℕ} {bT bub : List Bool}
    (hT : BitString.binaryValue bT = T) (hub : BitString.binaryValue bub = ub)
    (hlT : bT.length ≤ Lc) (hlub : bub.length ≤ Lc) (hP : P.Ok cap) (hx : ∀ κ, (x κ).length ≤ T)
    (hk : ∀ c, (key c).length ≤ Lc) (hd : ∀ c, (dkey c).length ≤ Lc)
    (hS : Fintype.card (Option S) ≤ X) (hA : K + K ≤ X) (hR : Fintype.card M.Role ≤ X)
    (hsl : ∀ r : M.Role, Fintype.card ((M.law r.1).SlotAt r.2) ≤ X)
    (hcn : ∀ r : M.Role, Fintype.card ((M.law r.1).ChannelAt r.2) ≤ X)
    (hι : (baseParties grp g).length ≤ ι) (hιX : ι ≤ X)
    (hlh : ∀ p, grp (Fin.castAdd A' p) = g → ∑ b, ((n p b : ℕ) + n b p) ≤ lh)
    (hev : cellCount n o grp g ≤ ev) (hpd : roleUnitCount P n o grp g ≤ pd)
    (b : UnitId (K + K) U0 M.Channel U1 → UnitContent ub) :
    groupTime bT bub (groupScript qn cb P q x ρ n o grp g key dkey tg b) ≤
      (Lc + 1) * (T + ub + 2) + ι * T + 3 * (ev + pd + ι * lh) * (ub + Lc + 1) + 10 * X ^ 3 := by
  have hX : 1 ≤ X := le_trans Fintype.card_pos hS
  have hsum (l : List Instruction) : (l.map (Instruction.cost T ub)).sum + l.length =
      (l.map fun i => i.cost T ub + 1).sum := by
    simp [List.sum_map_add]
  rw [groupTime, hT, hub, add_assoc, hsum, groupScript, List.map_append, List.map_append,
    List.sum_append, List.sum_append, List.sum_map_flatMap, List.map_map]
  have c1 := List.sum_le_length_nsmul ((baseParties grp g).map fun p =>
    ((baseInstructions qn cb q x ρ n key dkey p).map fun i => i.cost T ub + 1).sum)
    (T + X * X + 3 * X + 2 + 3 * lh * (ub + Lc + 1)) fun y hy => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hy
      have := hlh p (mem_baseParties.1 hp)
      exact (cost_baseInstructions hx hk hd hS hA p).trans (by gcongr)
  have hGf : (groupRoles grp g M).toFinset = univ.filter fun r => grp (M.roleParty r) = g :=
    Finset.ext fun r => by simp [mem_groupRoles]
  rw [← List.sum_toFinset _ (nodup_groupRoles grp g M), hGf]
  have c2 := sum_le_sum (s := univ.filter fun r => grp (M.roleParty r) = g) fun r _ =>
    cost_roleInstruction (T := T) (ub := ub) (P := P) (n := n) (o := o) (key := key) (tg := tg)
      hP hk hsl hcn r
  have c3 := sum_channels_le (n := n) (o := o) (grp := grp) (g := g)
  have c4 : #(univ.filter fun r => grp (M.roleParty r) = g) ≤ X := (card_le_univ _).trans hR
  have c5 := cost_endInstructions (T := T) (P := P) (n := n) (o := o) (grp := grp) (g := g) hk b
  have h1 : (bT.length + 1) * (T + 1) ≤ (Lc + 1) * (T + 1) := Nat.mul_le_mul_right _ (by omega)
  have h2 : (bub.length + 1) * (ub + 1) ≤ (Lc + 1) * (ub + 1) := Nat.mul_le_mul_right _ (by omega)
  rw [List.length_map, smul_eq_mul] at c1
  have h3 := Nat.mul_le_mul_right (T + X * X + 3 * X + 2 + 3 * lh * (ub + Lc + 1)) hι
  have h4 := Nat.mul_le_mul_right (2 * X + 2) c4
  have h5 : ι * (X * X + 3 * X + 2) ≤ X * (X * X + 3 * X + 2) := Nat.mul_le_mul_right _ hιX
  have h6 : X * X ≤ X ^ 3 := by nlinarith
  have h7 : X ≤ X * X := Nat.le_mul_of_pos_left _ hX
  have h8 := Nat.mul_le_mul_right (ub + Lc + 1) hev
  have h9 := Nat.mul_le_mul_right (ub + Lc + 1) hpd
  have h10 := Nat.mul_le_mul_right (ub + Lc + 1) c3
  unfold roleUnitCount at h9
  simp only [Function.comp_def, sum_add_distrib, ← sum_mul, sum_const, smul_eq_mul] at c2 h9 h10 ⊢
  generalize ub + Lc + 1 = W at *
  nlinarith

end Time

end Cslib.Circuits.Arithmetic.Separation.GroupProgram
