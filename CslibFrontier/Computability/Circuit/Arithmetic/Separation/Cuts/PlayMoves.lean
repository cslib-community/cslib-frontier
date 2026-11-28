/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Cuts.Moves
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Cuts.MoveIdentity
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators

/-!
# The play of a plan

A plan (`Cut.Plan`) says which units every move is given. The moves of a plan that obeys the
rules (`Cut.Plan.Ok`) keep the value of the position ([AnthropicVPVNP2026], Section H.2, law
moves; module `Nc.G.PlayThm`): the value at the beginning, where the units are those of the
strings between the base parties and the weight is the product of the tables of the parties, is
the sum, over the allowed outcomes of all moves, of the values of the positions in the end, where
the table of a party is its table at the beginning times the tables of its roles
(`Cut.Plan.value_moves`). Outcomes that are not allowed may be left out if every possible outcome
is allowed, because impossible outcomes contribute nothing (`Cut.move_zero`).

The proof applies `Play.value_move` to one move after the other; its hypothesis is the identity
of one move (`Cut.Plan.value_move`, from `Cut.move_identity`).

## Main definitions

* `Cut.Plan.givenAt`: the units given in a move.

## Main results

* `Cut.Plan.new_mem_seenAt`, `Cut.Plan.init_mem_seenAt`, `Cut.Plan.mem_seenAt_end`,
  `Cut.Plan.mem_cur`, `Cut.Plan.mem_ids`, `Cut.Plan.length_ids`: the units seen, the current
  units and the units given at a slot.
* `Cut.Plan.seenAt_succ`, `Cut.Plan.cur_succ`: the units seen, and the current units, after one
  more move.
* `Cut.Plan.card_filter_holds_seenAt`: the number of units seen before a move that a party holds.
* `Cut.Plan.value_move`: the identity of one move of a plan.
* `Cut.Plan.value_moves`: the moves of a plan keep the value.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Section H.2 (law moves), which Appendix J applies; module `Nc.G.PlayThm`
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Cut

open Finset

variable {F : Type*} [CommSemiring F] {A A' E U0 U1 ub cap : ℕ} {M : Moves F (A + A') E}

namespace Plan

variable {P : Plan M U0 U1} {n : Fin A → Fin A → Fin (U0 + 1)} {o o' : M.Channel → Fin U1}

@[simp]
theorem new_mem_seenAt {x : ℕ} {ν : M.Channel} {k : Fin U1} :
    (.new ν k : UnitId A U0 M.Channel U1) ∈ seenAt n o x ↔ (ν.1 : ℕ) < x ∧ k ≤ o ν := by
  simp only [seenAt, mem_union, new_notMem_initialUnits, false_or, mem_biUnion, mem_filter,
    mem_univ, true_and, new_mem_newUnits]
  exact ⟨fun ⟨x', hx, h, hk⟩ => ⟨h ▸ hx, hk⟩, fun ⟨hx, hk⟩ => ⟨ν.1, hx, rfl, hk⟩⟩

@[simp]
theorem init_mem_seenAt {x : ℕ} {a b : Fin A} {k : Fin U0} :
    (.init a b k : UnitId A U0 M.Channel U1) ∈ seenAt n o x ↔ (k : ℕ) < n a b := by
  simp [seenAt]

/-- The units seen in the end are the units whose number is less than the number of units of
their string. -/
theorem mem_seenAt_end {id : UnitId A U0 M.Channel U1} :
    id ∈ seenAt n o E ↔ id.index < id.count n o := by
  obtain _ | ⟨ν, k⟩ := id
  · exact init_mem_seenAt
  · simp [UnitId.index, UnitId.count, Nat.lt_succ_iff]

/-- **The units seen that a party holds.** The units seen before the move `x` (for `x = E`: in
the end) that the party `p` holds are the initial units of the strings at `p` and, for every end
at `p` of a channel of an earlier move, the outcome of the channel and one more unit. -/
theorem card_filter_holds_seenAt (x : ℕ) (p : Fin (A + A')) :
    ((seenAt n o x).filter (Play.Holds (UnitId.holder M.channelParty) p)).card =
      (∑ a, ∑ b, if p = Fin.castAdd A' a ∨ p = Fin.castAdd A' b then (n a b : ℕ) else 0) +
        ∑ ν with (ν.1 : ℕ) < x, ∑ d, if M.channelParty ν d = p then (o ν : ℕ) + 1 else 0 := by
  have hs : ((seenAt n o x).filter (Play.Holds (UnitId.holder M.channelParty) p)).card =
      ∑ u, if u ∈ seenAt n o x ∧ Play.Holds (UnitId.holder M.channelParty) p u then 1 else 0 := by
    simp only [ite_and]
    rw [sum_ite_mem, univ_inter, card_filter]
  rw [hs, UnitId.sum_eq, sum_filter]
  congr 1
  · refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
    simp only [init_mem_seenAt, UnitId.holds_init]
    by_cases hp : p = Fin.castAdd A' a ∨ p = Fin.castAdd A' b <;>
      simp [hp, Fin.card_filter_val_lt, Nat.le_of_lt_succ (n a b).2]
  · refine sum_congr rfl fun ν _ => ?_
    have hne : M.channelParty ν false ≠ M.channelParty ν true := fun h =>
      (M.law ν.1).channelEnd_ne ν.2 (M.party_injective ν.1 h)
    simp only [new_mem_seenAt, Play.Holds, UnitId.holder, Fintype.sum_bool]
    by_cases hx : (ν.1 : ℕ) < x
    · by_cases H : ∃ d, M.channelParty ν d = p
      · obtain ⟨d, rfl⟩ := H
        cases d <;> simp [hx, hne, hne.symm, filter_ge_eq_Iic]
      · simp [hx, not_exists.1 H]
    · simp [hx]

theorem mem_cur {x : ℕ} {id : UnitId A U0 M.Channel U1} :
    id ∈ P.cur n o x ↔ id ∈ seenAt n o x ∧ ∀ z : M.Slot, (z.1 : ℕ) < x → id ∉ P.given n o z := by
  simp only [cur, used, mem_sdiff, mem_biUnion, mem_filter, mem_univ, true_and, not_exists,
    not_and]

theorem mem_ids {z : M.Slot} {id : UnitId A U0 M.Channel U1} :
    id ∈ P.ids n o z ↔ id ∈ P.given n o z := by
  simp [ids, UnitId.list]

theorem length_ids {z : M.Slot} : (P.ids n o z).length = (P.given n o z).card := by
  rw [ids, UnitId.list, ← List.toFinset_card_of_nodup ((nodup_toList _).filter _)]
  exact congrArg card (by ext id; simp)

/-- The units given in the move `x`. -/
@[expose] def givenAt (P : Plan M U0 U1) (n : Fin A → Fin A → Fin (U0 + 1))
    (o : M.Channel → Fin U1) (x : Fin E) : Finset (UnitId A U0 M.Channel U1) :=
  univ.biUnion fun e : (M.law x).Slot => P.given n o ⟨x, e⟩

@[simp]
theorem mem_givenAt {x : Fin E} {id : UnitId A U0 M.Channel U1} :
    id ∈ P.givenAt n o x ↔ ∃ e, id ∈ P.given n o ⟨x, e⟩ := by
  simp [givenAt]

private theorem filter_lt_succ (x : Fin E) : (univ.filter fun x' : Fin E => (x' : ℕ) < x + 1) =
    insert x (univ.filter fun x' : Fin E => (x' : ℕ) < x) := by
  ext x'
  simp only [mem_filter, mem_univ, true_and, mem_insert, Fin.ext_iff]
  omega

private theorem forall_sigma_lt_succ {β : Fin E → Type*} (x : Fin E) {Q : (Σ x, β x) → Prop} :
    (∀ z, (z.1 : ℕ) < x + 1 → Q z) ↔ (∀ z, (z.1 : ℕ) < x → Q z) ∧ ∀ e, Q ⟨x, e⟩ := by
  refine ⟨fun h => ⟨fun z hz => h z (Nat.lt_succ_of_lt hz), fun e => h ⟨x, e⟩ (Nat.lt_succ_self _)⟩,
    ?_⟩
  rintro ⟨h1, h2⟩ ⟨x', e⟩ hz
  rcases Nat.lt_succ_iff_lt_or_eq.1 hz with h | h
  · exact h1 _ h
  · obtain rfl : x' = x := Fin.ext h
    exact h2 e

/-- The units seen after the move `x` are those seen before it and its new units. -/
theorem seenAt_succ (x : Fin E) : seenAt n o (x + 1) = seenAt n o x ∪ newUnits M x o := by
  rw [seenAt, seenAt, filter_lt_succ, biUnion_insert, union_left_comm, union_comm]

/-- The units seen before the move `x` are not new units of this move or of a later one. -/
private theorem notMem_newUnits_of_mem_seenAt {x : ℕ} {x' : Fin E} (hx : x ≤ x')
    {id : UnitId A U0 M.Channel U1} (h : id ∈ seenAt n o x) : id ∉ newUnits M x' o' := by
  intro hn
  obtain ⟨ν, k, rfl, -⟩ := mem_newUnits.1 hn
  exact absurd (new_mem_seenAt.1 h).1 (not_lt.2 hx)

private theorem mem_seenAt_of_mem_given (hP : P.Ok cap) {x : Fin E} {e : (M.law x).Slot}
    {id : UnitId A U0 M.Channel U1} (h : id ∈ P.given n o ⟨x, e⟩) : id ∈ seenAt n o x :=
  (mem_cur.1 (hP.given_subset n o ⟨x, e⟩ h)).1

/-- The current units after the move `x`: the units given in the move are taken away, and its
new units are added. -/
theorem cur_succ (hP : P.Ok cap) (x : Fin E) :
    P.cur n o (x + 1) = P.cur n o x \ P.givenAt n o x ∪ newUnits M x o := by
  ext id
  have hnew : id ∈ newUnits M x o → (∀ z : M.Slot, (z.1 : ℕ) < x → id ∉ P.given n o z) ∧
      ∀ e, id ∉ P.given n o ⟨x, e⟩ := fun hn =>
    (forall_sigma_lt_succ x).1 fun z hz hg => notMem_newUnits_of_mem_seenAt
      (Nat.lt_succ_iff.1 hz) (mem_seenAt_of_mem_given hP (x := z.1) (e := z.2) hg) hn
  simp only [mem_cur, seenAt_succ, forall_sigma_lt_succ x, mem_union, mem_sdiff, mem_givenAt,
    not_exists]
  tauto

section Congr

variable {x : ℕ}

/-- The units seen before the move `x` depend on the outcomes of earlier moves only. -/
private theorem seenAt_congr (h : ∀ ν : M.Channel, (ν.1 : ℕ) < x → o ν = o' ν) :
    seenAt n o x = seenAt n o' x := by
  ext (_ | ⟨ν, k⟩)
  · simp
  · simp only [new_mem_seenAt]
    exact and_congr_right fun hx => by rw [h ν hx]

private theorem given_congr_of_le (hP : P.Ok cap) (h : ∀ ν : M.Channel, (ν.1 : ℕ) < x → o ν = o' ν)
    {z : M.Slot} (hz : (z.1 : ℕ) ≤ x) : P.given n o z = P.given n o' z :=
  hP.given_congr n o o' z fun ν hν => h ν (lt_of_lt_of_le hν hz)

/-- The current units before the move `x` depend on the outcomes of earlier moves only. -/
private theorem cur_congr (hP : P.Ok cap) (h : ∀ ν : M.Channel, (ν.1 : ℕ) < x → o ν = o' ν) :
    P.cur n o x = P.cur n o' x := by
  ext id
  simp only [mem_cur, seenAt_congr h]
  exact and_congr_right fun _ => forall₂_congr fun z hz => by
    rw [given_congr_of_le hP h hz.le]

end Congr

end Plan

open Plan

variable {P : Plan M U0 U1} {n : Fin A → Fin A → Fin (U0 + 1)} {o o' : M.Channel → Fin U1}

/-- The parties at the two ends of a slot hold the units given at the slot. -/
private theorem holds_given (hP : P.Ok cap) {z : M.Slot} {id : UnitId A U0 M.Channel U1}
    (h : id ∈ P.given n o z) (d : Bool) :
    Play.Holds (UnitId.holder M.channelParty) (M.slotParty z d) id := by
  obtain ⟨d₀, hd⟩ := hP.holder_given n o z id h
  exact ⟨d₀ ^^ d, by rw [hd, ← Bool.xor_assoc, Bool.xor_self, Bool.false_xor]⟩

/-- The table of a role in the play, with the number of units and the units given taken at an
outcome that agrees with `o'` before the move. -/
private theorem roleTableAt_eq (hP : P.Ok cap) {x : Fin E}
    (h : ∀ ν : M.Channel, (ν.1 : ℕ) < x → o ν = o' ν) (p : (M.law x).Role)
    (y : UnitId A U0 M.Channel U1 → UnitContent ub) :
    roleTableAt P n o' ⟨x, p⟩ y =
      roleTable M x p (P.count n o x) (fun e => P.ids n o ⟨x, e⟩) o' y := by
  have hg (e) : P.given n o' ⟨x, e⟩ = P.given n o ⟨x, e⟩ := (hP.given_congr n o o' _ h).symm
  simp only [roleTableAt, ids, hg, ← hP.count_congr n o o' x h]

section Joint

variable (P) [∀ n o x, Decidable (P.Good n o x)] (n) (o)
  (init : Fin (A + A') → (UnitId A U0 M.Channel U1 → UnitContent ub) → F)

/-- The table of a move in the play: the product of the tables of its roles, and zero if its
outcome is not allowed. -/
private noncomputable def moveTable (x : Fin E)
    (y : Fin (A + A') → UnitId A U0 M.Channel U1 → UnitContent ub) : F :=
  if P.Good n o x then ∏ p, roleTableAt P n o ⟨x, p⟩ (y (M.party x p)) else 0

/-- The joint weight before the move `x`: the tables of the parties at the beginning times the
tables of the earlier moves. -/
private noncomputable def jointTable (x : ℕ)
    (y : Fin (A + A') → UnitId A U0 M.Channel U1 → UnitContent ub) : F :=
  (∏ a, init a (y a)) * ∏ x' ∈ univ.filter fun x' : Fin E => (x' : ℕ) < x, moveTable P n o x' y

/-- The value of the position before the move `x`. -/
private noncomputable def valueAt (x : ℕ) (o : M.Channel → Fin U1) : F :=
  Play.value (UnitId.holder M.channelParty) none (seenAt n o x) (P.cur n o x)
    (jointTable P n o init x)

variable {P n o init}

private theorem jointTable_succ (x : Fin E)
    (y : Fin (A + A') → UnitId A U0 M.Channel U1 → UnitContent ub) :
    jointTable P n o init (x + 1) y = jointTable P n o init x y * moveTable P n o x y := by
  rw [jointTable, jointTable, filter_lt_succ, prod_insert (by simp), mul_left_comm, mul_comm]

/-- The joint weight after all moves is the product of the tables of the parties. -/
private theorem jointTable_end : jointTable P n o init E = fun y =>
    if ∀ x, P.Good n o x then ∏ a, partyTable P n o (init a) a (y a) else 0 := by
  funext y
  have h : ∏ a, partyTable P n o (init a) a (y a) =
      (∏ a, init a (y a)) * ∏ x, ∏ p, roleTableAt P n o ⟨x, p⟩ (y (M.party x p)) := by
    simp only [partyTable, prod_mul_distrib]
    rw [prod_comm, Fintype.prod_sigma]
    exact congrArg _ (prod_congr rfl fun x _ => prod_congr rfl fun p _ =>
      Fintype.prod_ite_eq (M.party x p) fun a => roleTableAt P n o ⟨x, p⟩ (y a))
  rw [jointTable, filter_true_of_mem fun x' _ => x'.2, h]
  simp only [moveTable, prod_ite_zero, mem_univ, forall_true_left, mul_ite, mul_zero]

/-- The joint weight before the move `x` depends on the outcomes of earlier moves only. -/
private theorem jointTable_congr (hP : P.Ok cap) {x : ℕ}
    (h : ∀ ν : M.Channel, (ν.1 : ℕ) < x → o ν = o' ν)
    (y : Fin (A + A') → UnitId A U0 M.Channel U1 → UnitContent ub) :
    jointTable P n o init x y = jointTable P n o' init x y := by
  rw [jointTable, jointTable]
  refine congrArg _ (prod_congr rfl fun x' hx' => ?_)
  have hx := (mem_filter.1 hx').2
  have hle : ∀ ν : M.Channel, ν.1 ≤ x' → o ν = o' ν := fun ν hν => h ν (lt_of_le_of_lt hν hx)
  rw [moveTable, moveTable]
  refine if_congr (hP.good_congr n o o' x' hle) (prod_congr rfl fun p _ => ?_) rfl
  rw [roleTableAt_eq hP (fun ν hν => hle ν hν.le)]
  exact roleTable_congr (fun ν => hle _ le_rfl) (fun _ _ _ => rfl) fun _ _ => rfl

/-- The joint weight before the move `x` does not read the new units of this move or of a later
one. -/
private theorem jointTable_extend (hP : P.Ok cap)
    (hloc : ∀ a y y', (∀ b c k, y (.init b c k) = y' (.init b c k)) → init a y = init a y')
    {x : ℕ} {x' : Fin E} (hx : x ≤ x') (o' : M.Channel → Fin U1)
    (y : Fin (A + A') → UnitId A U0 M.Channel U1 → UnitContent ub)
    (z : UnitId A U0 M.Channel U1 → UnitContent ub) :
    jointTable P n o init x
      (Play.extend (UnitId.holder M.channelParty) (newUnits M x' o') y z) =
      jointTable P n o init x y := by
  rw [jointTable, jointTable]
  congr 1
  · exact prod_congr rfl fun a _ => hloc a _ _ fun b c k =>
      Play.extend_of_notMem init_notMem_newUnits
  · refine prod_congr rfl fun x'' hx'' => ?_
    have hlt := (mem_filter.1 hx'').2
    rw [moveTable, moveTable]
    refine if_congr Iff.rfl (prod_congr rfl fun p _ => ?_) rfl
    rw [roleTableAt, roleTableAt]
    refine roleTable_congr (fun _ => rfl) (fun e id hid => ?_) fun ν k => ?_
    · exact Play.extend_of_notMem (notMem_newUnits_of_mem_seenAt (hlt.le.trans hx)
        (mem_seenAt_of_mem_given hP (mem_ids.1 hid)))
    · exact Play.extend_of_notMem fun hn =>
        (hlt.trans_le hx).ne (congrArg Fin.val (new_mem_newUnits.1 hn).1)

/-- If the joint weight before the move `x` is not zero, then the copies of the units seen before
this move are present at their holders. -/
private theorem jointTable_ne_none
    (hinit : ∀ a y, init a y ≠ 0 → ∀ id ∈ initialUnits n,
      Play.Holds (UnitId.holder M.channelParty) a id → y id ≠ none)
    {x : ℕ} {y : Fin (A + A') → UnitId A U0 M.Channel U1 → UnitContent ub}
    (h : jointTable P n o init x y ≠ 0) {a : Fin (A + A')} {id : UnitId A U0 M.Channel U1}
    (hid : id ∈ seenAt n o x) (ha : Play.Holds (UnitId.holder M.channelParty) a id) :
    y a id ≠ none := by
  rw [jointTable] at h
  obtain ⟨b, c, k⟩ | ⟨⟨x', ν⟩, k⟩ := id
  · exact hinit a _ (fun h0 => left_ne_zero_of_mul h (prod_eq_zero (mem_univ a) h0)) _
      (init_mem_initialUnits.2 (init_mem_seenAt.1 hid)) ha
  · obtain ⟨hx, hk⟩ := new_mem_seenAt.1 hid
    obtain ⟨d, rfl⟩ := ha
    have h1 : moveTable P n o x' y ≠ 0 := fun h0 =>
      right_ne_zero_of_mul h (prod_eq_zero (mem_filter.2 ⟨mem_univ _, hx⟩) h0)
    rw [moveTable] at h1
    exact roleTable_new_ne_none (fun h0 => (ite_ne_right_iff.1 h1).2
      (prod_eq_zero (mem_univ ((M.law x').channelEnd ν d)) h0)) (Play.holds_end _ ν d) hk

end Joint

namespace Plan

variable [∀ n o x, Decidable (P.Good n o x)]

/-- **The identity of one move of a plan.** For contents `y` of the units seen before the move
`x` whose copies at their holders are present, the condition that the two copies of every unit
given in the move agree is the sum, over the allowed outcomes of the move and over the common
contents of its new units, of the product of the tables of its roles. Every possible outcome is
allowed, the strings of the law of a move have at most `m x` bits, and the strings on its
channels have at most `U1` units. -/
theorem value_move (hP : P.Ok cap) (hub : 0 < ub)
    (hgood : ∀ n o x, P.Possible n o ub x → P.Good n o x) {m : Fin E → ℕ}
    (hm : ∀ x, (M.law x).LengthLE (m x))
    (hU1 : ∀ x, cap * (m x + (M.law x).labelLength) + 1 ≤ U1) (x : Fin E)
    {y : Fin (A + A') → UnitId A U0 M.Channel U1 → UnitContent ub}
    (hy : y ∈ Play.contents (UnitId.holder M.channelParty) none (seenAt n o x))
    (hne : ∀ a id, id ∈ seenAt n o x → Play.Holds (UnitId.holder M.channelParty) a id →
      y a id ≠ none) :
    (if Play.Agree (UnitId.holder M.channelParty) (P.givenAt n o x) y then (1 : F) else 0) =
      ∑ oo : (M.law x).Channel → Fin U1,
        ∑ z ∈ Play.common none (newUnits M x (M.setOutcome o x oo)),
          if P.Good n (M.setOutcome o x oo) x then
            ∏ p, roleTableAt P n (M.setOutcome o x oo) ⟨x, p⟩
              (Play.extend (UnitId.holder M.channelParty) (newUnits M x (M.setOutcome o x oo)) y z
                (M.party x p))
          else 0 := by
  have hlt (oo) : ∀ ν : M.Channel, (ν.1 : ℕ) < x → o ν = M.setOutcome o x oo ν := fun ν hν =>
    (Moves.setOutcome_of_ne M o oo (Fin.ne_of_lt hν)).symm
  have hB : P.count n o x * (m x + (M.law x).labelLength) + 1 ≤ U1 :=
    (Nat.add_le_add_right (Nat.mul_le_mul_right _ (hP.count_le n o x)) 1).trans (hU1 x)
  have hseen : ∀ e, ∀ id ∈ P.ids n o ⟨x, e⟩, id ∈ seenAt n o x := fun e id hid =>
    mem_seenAt_of_mem_given hP (mem_ids.1 hid)
  have hnew : ∀ ν k a, y a (.new ⟨x, ν⟩ k) = none := fun ν k a =>
    Play.mem_contents.1 hy a _ fun h => lt_irrefl _ (new_mem_seenAt.1 h.1).1
  have hids : ∀ e ν k, .new ⟨x, ν⟩ k ∉ P.ids n o ⟨x, e⟩ := fun e ν k hid =>
    lt_irrefl _ (new_mem_seenAt.1 (hseen e _ hid)).1
  have hne' : ∀ e, ∀ id ∈ P.ids n o ⟨x, e⟩, ∀ d,
      y (M.party x ((M.law x).slotEnd e d)) id ≠ none := fun e id hid d =>
    hne _ _ (hseen e id hid) (holds_given hP (mem_ids.1 hid) d)
  have hz (oo : (M.law x).Channel → Fin U1) :
      (∑ z ∈ Play.common none (newUnits M x (M.setOutcome o x oo)),
        if P.Good n (M.setOutcome o x oo) x then
          ∏ p, roleTableAt P n (M.setOutcome o x oo) ⟨x, p⟩
            (Play.extend (UnitId.holder M.channelParty) (newUnits M x (M.setOutcome o x oo)) y z
              (M.party x p))
        else 0) =
      ∑ z ∈ Play.common none (newUnits M x (M.setOutcome o x oo)), ∏ p,
        roleTable M x p (P.count n o x) (fun e => P.ids n o ⟨x, e⟩) (M.setOutcome o x oo)
          (Play.extend (UnitId.holder M.channelParty) (newUnits M x (M.setOutcome o x oo)) y z
            (M.party x p)) := by
    simp only [roleTableAt_eq hP (hlt oo)]
    by_cases hG : P.Good n (M.setOutcome o x oo) x
    · simp only [hG, ite_true]
    · simp only [hG, ite_false, sum_const_zero]
      refine (move_zero x _ _ hub (hm x) hB hnew hids hne' fun ⟨i, hi⟩ =>
        hG (hgood n _ x ?_)).symm
      rw [Possible, ← hP.count_congr n o _ x (hlt oo)]
      exact ⟨i, hi⟩
  simp only [hz]
  rw [move_identity x o _ hub (hm x) hB hnew hids hne' fun e =>
    length_ids.trans_le (hP.card_given_le n o ⟨x, e⟩)]
  refine if_congr ?_ rfl rfl
  simp only [Play.Agree, mem_givenAt, mem_ids, forall_exists_index]
  rw [forall_comm]
  refine forall₃_congr fun e id hid => ?_
  obtain ⟨d, hd⟩ := hP.holder_given n o ⟨x, e⟩ id hid
  rw [hd false, hd true]
  cases d
  · exact Iff.rfl
  · exact eq_comm

/-- One move of a plan keeps the value of the position. -/
private theorem valueAt_succ (hP : P.Ok cap) (hub : 0 < ub)
    (hgood : ∀ n o x, P.Possible n o ub x → P.Good n o x) {m : Fin E → ℕ}
    (hm : ∀ x, (M.law x).LengthLE (m x))
    (hU1 : ∀ x, cap * (m x + (M.law x).labelLength) + 1 ≤ U1)
    {init : Fin (A + A') → (UnitId A U0 M.Channel U1 → UnitContent ub) → F}
    (hloc : ∀ a y y', (∀ b c k, y (.init b c k) = y' (.init b c k)) → init a y = init a y')
    (hinit : ∀ a y, init a y ≠ 0 → ∀ id ∈ initialUnits n,
      Play.Holds (UnitId.holder M.channelParty) a id → y id ≠ none)
    (x : Fin E) (o : M.Channel → Fin U1) :
    valueAt P n init x o =
      ∑ oo : (M.law x).Channel → Fin U1, valueAt P n init (x + 1) (M.setOutcome o x oo) := by
  have hlt (oo) : ∀ ν : M.Channel, (ν.1 : ℕ) < x → o ν = M.setOutcome o x oo ν := fun ν hν =>
    (Moves.setOutcome_of_ne M o oo (Fin.ne_of_lt hν)).symm
  rw [valueAt, Play.value_move (UnitId.holder M.channelParty) none (Out := P.givenAt n o x)
    (biUnion_subset.2 fun e _ => hP.given_subset n o ⟨x, e⟩) (fun _ h => (mem_cur.1 h).1)
    (fun oo => newUnits M x (M.setOutcome o x oo))
    (fun oo => disjoint_left.2 fun id h => notMem_newUnits_of_mem_seenAt le_rfl h)
    (jointTable P n o init x) (fun oo y z => jointTable_extend hP hloc le_rfl _ y z)
    (fun oo => moveTable P n (M.setOutcome o x oo) x)
    fun y hy h0 => value_move hP hub hgood hm hU1 x hy fun a id => jointTable_ne_none hinit h0]
  refine sum_congr rfl fun oo _ => ?_
  rw [valueAt, seenAt_succ, cur_succ hP, ← seenAt_congr (hlt oo), ← cur_congr hP (hlt oo)]
  have hg : P.givenAt n (M.setOutcome o x oo) x = P.givenAt n o x :=
    biUnion_congr rfl fun e _ => (given_congr_of_le hP (hlt oo) le_rfl).symm
  rw [hg]
  refine congrArg _ (funext fun y => ?_)
  rw [jointTable_succ, ← jointTable_congr hP (hlt oo)]

/-- **The moves of a plan keep the value.** The value of the position at the beginning, with the
units of the strings between the base parties and the tables `init` of the parties, is the sum,
over the allowed outcomes of all moves, of the values of the positions in the end, where the
table of a party is its table at the beginning times the tables of its roles. The plan obeys the
rules, every possible outcome is allowed, the strings of the law of a move have at most `m x`
bits, and the strings on its channels have at most `U1` units. The tables at the beginning read
the initial units only, and vanish unless the initial units that the party holds are present. -/
theorem value_moves (hP : P.Ok cap) (hub : 0 < ub)
    (hgood : ∀ n o x, P.Possible n o ub x → P.Good n o x) {m : Fin E → ℕ}
    (hm : ∀ x, (M.law x).LengthLE (m x))
    (hU1 : ∀ x, cap * (m x + (M.law x).labelLength) + 1 ≤ U1)
    (n : Fin A → Fin A → Fin (U0 + 1))
    (init : Fin (A + A') → (UnitId A U0 M.Channel U1 → UnitContent ub) → F)
    (hloc : ∀ a y y', (∀ b c k, y (.init b c k) = y' (.init b c k)) → init a y = init a y')
    (hinit : ∀ a y, init a y ≠ 0 → ∀ id ∈ initialUnits n,
      Play.Holds (UnitId.holder M.channelParty) a id → y id ≠ none) :
    Play.value (UnitId.holder M.channelParty) (none : UnitContent ub) (initialUnits n)
        (initialUnits n) (fun y => ∏ a, init a (y a)) =
      ∑ o : M.Channel → Fin U1, if ∀ x, P.Good n o x then
        Play.value (UnitId.holder M.channelParty) none (seenAt n o E) (P.cur n o E) fun y =>
          ∏ a, partyTable P n o (init a) a (y a) else 0 := by
  have claim : ∀ x ≤ E, ∀ o, valueAt P n init x o =
      ∑ o' with ∀ ν : M.Channel, (ν.1 : ℕ) < x → o' ν = o ν, valueAt P n init E o' := by
    intro x hx
    induction hx using Nat.decreasingInduction with
    | self =>
      intro o
      have : (univ.filter fun o' : M.Channel → Fin U1 =>
          ∀ ν : M.Channel, (ν.1 : ℕ) < E → o' ν = o ν) = {o} := by
        ext o'
        simp [funext_iff]
      rw [this, sum_singleton]
    | of_succ x hx ih =>
      intro o
      rw [valueAt_succ hP hub hgood hm hU1 hloc hinit ⟨x, hx⟩ o,
        ← sum_fiberwise _ fun (o' : M.Channel → Fin U1) (ν : (M.law ⟨x, hx⟩).Channel) =>
          o' ⟨⟨x, hx⟩, ν⟩]
      refine sum_congr rfl fun oo _ => (ih _).trans (sum_congr ?_ fun _ _ => rfl)
      ext o'
      simp only [mem_filter, mem_univ, true_and]
      rw [forall_sigma_lt_succ ⟨x, hx⟩]
      exact and_congr (forall₂_congr fun ν hν => by
        rw [Moves.setOutcome_of_ne M o oo (Fin.ne_of_lt hν)]) (by simp [funext_iff])
  have h0 : valueAt P n init 0 (fun ν => ⟨0, (Nat.succ_pos _).trans_le (hU1 ν.1)⟩) =
      Play.value (UnitId.holder M.channelParty) (none : UnitContent ub) (initialUnits n)
        (initialUnits n) (fun y => ∏ a, init a (y a)) := by
    have hj : jointTable P n (fun ν => ⟨0, (Nat.succ_pos _).trans_le (hU1 ν.1)⟩) init 0 =
        fun y => ∏ a, init a (y a) := funext fun y => by simp [jointTable]
    simp [valueAt, hj, seenAt, cur, used]
  rw [← h0, claim 0 (Nat.zero_le _)]
  simp only [Nat.not_lt_zero, false_imp_iff, implies_true, filter_true_of_mem]
  refine sum_congr rfl fun o _ => ?_
  rw [valueAt, jointTable_end]
  split_ifs with hG
  · rfl
  · rw [Play.value_eq_sum_filter]
    exact sum_const_zero

end Plan

end Cslib.Circuits.Arithmetic.Separation.Cut
