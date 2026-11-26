/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Cuts.Moves
public import Mathlib.Data.Set.Operations
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Cuts.Contract
import CslibFrontier.Foundations.Data.List.Counting
import CslibFrontier.Foundations.Data.List.FixedWidth
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators

/-!
# The identity of one move

A move of the cutting argument of [AnthropicVPVNP2026] (Section H.2, law moves; module
`Nc.G.Move`) gives units at the slots of its law and makes new units on the channels of the law.
The two copies of every given unit are held by the parties at the ends of its slot. The identity
of the move (`Cut.move_identity`) says that the condition "the two copies of every given unit
agree" is the sum, over the outcomes of the move and over the common contents of its new units,
of the product of the tables of the roles (`Cut.roleTable`).

The proof applies the law to every bit of the given units (`Cut.Law.pow`). The strings on a
channel then determine the indices and the strings of all bits, also after they are cut into
units (`Cut.codeWord_injective`), so that the sum over the contents of the new units is the sum
over one index for every bit and over the strings on all channels (`Cut.sum_prod_codeTable`).
Every choice of indices and strings belongs to exactly one outcome, the one that gives the numbers
of units of the strings (`Cut.move_outcome`), and outcomes that no choice of indices gives
contribute nothing (`Cut.move_zero`).

## Main results

* `Cut.UnitContent.bits_injOn`, `Cut.slotBits_eq_iff`: a unit that is not absent is
  determined by its bits, and the bits given at a slot agree in two copies exactly when the units
  do.
* `Cut.roleTable_congr`, `Cut.roleTable_ne_zero`, `Cut.roleTable_new_ne_none`: the table of a role
  reads the units given at its slots and the new units of its channels only, and it vanishes
  unless the new units of its channels are present.
* `Cut.move_outcome`: one outcome of a move, as a sum over the indices that give this outcome.
* `Cut.move_identity`: the identity of one move.
* `Cut.move_zero`: outcomes that no indices give contribute nothing.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Section H.2 (law moves), which Appendix J applies; module `Nc.G.Move`
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Cut

open Finset

namespace UnitContent

variable {ub : ℕ}

theorem length_bits {w : UnitContent ub} (h : w ≠ none) : w.bits.length = ub := by
  obtain ⟨v, rfl⟩ := Option.ne_none_iff_exists'.1 h
  exact List.length_ofFn

/-- A unit has at most `ub` bits. -/
theorem length_bits_le (w : UnitContent ub) : w.bits.length ≤ ub := by
  cases w <;> simp [bits]

/-- A unit that is not absent is determined by its bits. -/
theorem bits_injOn : Set.InjOn (bits (ub := ub)) {w | w ≠ none} := by
  rintro (_ | v) h (_ | v') h' e
  · rfl
  · exact absurd rfl h
  · exact absurd rfl h'
  · exact congrArg some (List.ofFn_injective e)

end UnitContent

namespace Moves

variable {F : Type*} [CommSemiring F] {A E U1 : ℕ} (M : Moves F A E) (o : M.Channel → Fin U1)

@[simp]
theorem setOutcome_self (x : Fin E) (oo : (M.law x).Channel → Fin U1) (ν : (M.law x).Channel) :
    M.setOutcome o x oo ⟨x, ν⟩ = oo ν := by
  simp [setOutcome]

theorem setOutcome_of_ne {x : Fin E} (oo : (M.law x).Channel → Fin U1) {ν : M.Channel}
    (h : ν.1 ≠ x) : M.setOutcome o x oo ν = o ν :=
  dite_eq_right h

end Moves

section Slots

variable {A U0 U1 ub t : ℕ} {N : Type*} {ids : List (UnitId A U0 N U1)}
  {y y' : UnitId A U0 N U1 → UnitContent ub}

private theorem slotBits_congr (h : ∀ id ∈ ids, y id = y' id) :
    slotBits t ids y = slotBits t ids y' := by
  rw [slotBits, slotBits, List.flatMap_congr fun id hid => by rw [h id hid]]

private theorem length_slotBits (h : ∀ id ∈ ids, y id ≠ none) (ht : ids.length ≤ t) :
    (slotBits t ids y).length = t * ub := by
  rw [slotBits, List.length_append, List.length_replicate,
    List.length_flatMap_of_forall_length_eq fun id hid => UnitContent.length_bits (h id hid),
    ← add_mul, Nat.add_sub_cancel' ht]

/-- The bits given at a slot agree in two copies exactly when the units do. -/
theorem slotBits_eq_iff (h : ∀ id ∈ ids, y id ≠ none) (h' : ∀ id ∈ ids, y' id ≠ none)
    (ht : ids.length ≤ t) :
    (∀ k : Fin (t * ub), (slotBits t ids y).getD k false = (slotBits t ids y').getD k false) ↔
      ∀ id ∈ ids, y id = y' id := by
  refine ⟨fun hk id hid => UnitContent.bits_injOn (h id hid) (h' id hid) ?_,
    fun hk k => by rw [slotBits_congr hk]⟩
  have e : slotBits t ids y = slotBits t ids y' :=
    List.ext_getElem (by rw [length_slotBits h ht, length_slotBits h' ht]) fun k h1 h2 => by
      simpa [List.getD_eq_getElem?_getD, h1, h2] using hk ⟨k, by rwa [length_slotBits h ht] at h1⟩
  exact (List.flatMap_eq_flatMap_iff_of_forall_length_eq fun id hid => by
    rw [UnitContent.length_bits (h id hid), UnitContent.length_bits (h' id hid)]).1
    (List.append_cancel_right e) id hid

end Slots

variable {F : Type*} [CommSemiring F] {A A' E U0 U1 ub : ℕ} {M : Moves F (A + A') E}

/-- The new units of a move are units of its channels. -/
theorem mem_newUnits {x : Fin E} {o : M.Channel → Fin U1} {id : UnitId A U0 M.Channel U1} :
    id ∈ newUnits M x o ↔ ∃ ν k, id = .new ⟨x, ν⟩ k ∧ k ≤ o ⟨x, ν⟩ := by
  obtain _ | ⟨⟨x', ν⟩, k⟩ := id
  · simp
  · refine new_mem_newUnits.trans ⟨fun ⟨rfl, hk⟩ => ⟨ν, k, rfl, hk⟩, ?_⟩
    rintro ⟨_, _, ⟨⟩, hk⟩
    exact ⟨rfl, hk⟩

section Role

variable {x : Fin E} {p : (M.law x).Role} {t : ℕ}
  {ids : (M.law x).SlotAt p → List (UnitId A U0 M.Channel U1)} {o o' : M.Channel → Fin U1}
  {y y' : UnitId A U0 M.Channel U1 → UnitContent ub}

/-- The table of a role depends on the units given at its slots, and on the outcome and the new
units of its channels only. -/
theorem roleTable_congr (ho : ∀ ν : (M.law x).ChannelAt p, o ⟨x, ν⟩ = o' ⟨x, ν⟩)
    (h1 : ∀ e, ∀ id ∈ ids e, y id = y' id)
    (h2 : ∀ (ν : (M.law x).ChannelAt p) k, y (.new ⟨x, ν⟩ k) = y' (.new ⟨x, ν⟩ k)) :
    roleTable M x p t ids o y = roleTable M x p t ids o' y' := by
  have hs (e) : slotBits t (ids e) y = slotBits t (ids e) y' := slotBits_congr (h1 e)
  simp only [roleTable, ChannelOk, ho, h2, hs]
  exact if_congr (forall_congr' fun e => forall₂_congr fun id hid => by rw [h1 e id hid]) rfl rfl

/-- If the table of a role is not zero, the units given at its slots are present, and there are
indices and strings whose strings on the channels of the role are cut into its new units. -/
theorem roleTable_ne_zero (h : roleTable M x p t ids o y ≠ 0) :
    (∀ e, ∀ id ∈ ids e, y id ≠ none) ∧ ∃ (i : Fin (t * ub) → (M.law x).Index)
      (g : ∀ k, ∀ ν : (M.law x).ChannelAt p, BitString ((M.law x).length (i k) ν)),
      (∀ ν : (M.law x).ChannelAt p, ChannelOk ⟨x, ν.1⟩ (o ⟨x, ν.1⟩)
        (sideString (M.law x).label (fun j => (M.law x).length j ν) i fun k => g k ν) y) ∧
      ∏ k : Fin (t * ub),
        (M.law x).table p (i k) (fun e => (slotBits t (ids e) y).getD k false) (g k) ≠ 0 := by
  rw [roleTable] at h
  obtain ⟨hy, h⟩ := ite_ne_right_iff.1 h
  obtain ⟨i, -, h⟩ := exists_ne_zero_of_sum_ne_zero h
  obtain ⟨g, -, h⟩ := exists_ne_zero_of_sum_ne_zero h
  exact ⟨hy, i, g, ite_ne_right_iff.1 h⟩

private theorem ChannelOk.ne_none {N : Type*} {ν : N} {J : ℕ} {str : List Bool}
    {y : UnitId A U0 N U1 → UnitContent ub} (h : ChannelOk ν J str y) {k : Fin U1}
    (hk : (k : ℕ) ≤ J) : y (.new ν k) ≠ none := by
  rw [h.2 k, Ne, unitsOf_eq_none, h.1]
  omega

/-- The table of a role vanishes unless the new units of its channels are present. -/
theorem roleTable_new_ne_none (h : roleTable M x p t ids o y ≠ 0) {ν : (M.law x).Channel}
    (hν : Play.Holds (M.law x).channelEnd p ν) {k : Fin U1} (hk : k ≤ o ⟨x, ν⟩) :
    y (.new ⟨x, ν⟩ k) ≠ none := by
  obtain ⟨-, i, g, hg, -⟩ := roleTable_ne_zero h
  exact (hg ⟨ν, hν⟩).ne_none hk

end Role

section Law

variable (L : Law F) (ub : ℕ) {B : ℕ} (X : L.Role → Fin B → L.Slot → Bool)
  (o : L.Channel → Fin U1)

/-- The table of a role of a law for `B` bits on every slot and an outcome `o`, with units on
its channels: the sum, over the indices and the strings whose code words on the channels of the
role are `ζ`, of the product of the tables of the law; the indices must give the numbers of units
of the outcome. -/
private def unitTable (p : L.Role) (ζ : L.Channel → Fin U1 → UnitContent ub) : F :=
  codeTable (S := fun (i : Fin B → L.Index) ν => (k : Fin B) → BitString (L.length (i k) ν))
    L.channelEnd (fun ν i => codeWord L.label (fun j => L.length j ν) ub U1 i) p
    (fun i g => if ∀ ν : L.ChannelAt p,
        (o ν : ℕ) = (∑ k, (L.labelLength + L.length (i k) ν)) / ub then
      ∏ k, L.table p (i k) (fun e => X p k e) fun ν => g ν k else 0) ζ

variable {L ub X o}

private theorem eq_none_of_unitTable_ne_zero {p : L.Role}
    {ζ : L.Channel → Fin U1 → UnitContent ub} (h : unitTable L ub X o p ζ ≠ 0)
    (ν : L.ChannelAt p) {k : Fin U1} (hk : o ν < k) : ζ ν k = none := by
  rw [unitTable, codeTable_eq_sum_sigma] at h
  obtain ⟨⟨i, g⟩, -, h⟩ := exists_ne_zero_of_sum_ne_zero h
  obtain ⟨hc, ho, -⟩ := (ite_ne_right_iff.1 h).imp_right ite_ne_right_iff.1
  simpa only [← hc ν, codeWord, unitsOf_eq_none, unitCount, length_sideString, ← ho ν,
    Nat.add_one_le_iff] using Fin.lt_def.1 hk

variable (X o) in
/-- Tables with units, summed over the contents of the units on all channels: the sum over the
indices that give the outcome and over the strings on all channels. -/
private theorem sum_prod_unitTable (hub : 0 < ub) {m : ℕ} (hm : L.LengthLE m)
    (hB : B * (m + L.labelLength) / ub + 1 ≤ U1) :
    ∑ ζ : L.Channel → Fin U1 → UnitContent ub, ∏ p, unitTable L ub X o p ζ =
      ∑ i : Fin B → L.Index,
        if ∀ ν, (o ν : ℕ) = (∑ k, (L.labelLength + L.length (i k) ν)) / ub then
          ∑ g : (ν : L.Channel) → (k : Fin B) → BitString (L.length (i k) ν),
            ∏ p, ∏ k, L.table p (i k) (fun e => X p k e) fun ν => g ν k
        else 0 := by
  rcases isEmpty_or_nonempty L.Role with hR | hR
  · have : IsEmpty L.Channel := ⟨fun ν => hR.elim (L.channelEnd ν false)⟩
    have : IsEmpty L.Slot := ⟨fun e => hR.elim (L.slotEnd e false)⟩
    simpa using L.pow B X
  simp only [unitTable]
  rw [sum_prod_codeTable
    (fun ν => codeWord_injective L.label_injective hub (fun i => hm i ν) hB) L.connected_pow]
  refine sum_congr rfl fun i _ => ?_
  have hc : (∀ p ∈ (univ : Finset L.Role), ∀ ν : L.ChannelAt p,
      (o ν : ℕ) = (∑ k, (L.labelLength + L.length (i k) ν)) / ub) ↔
      ∀ ν, (o ν : ℕ) = (∑ k, (L.labelLength + L.length (i k) ν)) / ub :=
    ⟨fun h ν => h _ (mem_univ _) ⟨ν, false, rfl⟩, fun h _ _ ν => h ν⟩
  simp only [prod_ite_zero, hc, sum_ite_irrel, sum_const_zero]

end Law

/-- The table of a role, as a table with units. -/
private theorem roleTable_eq_unitTable {x : Fin E} {p : (M.law x).Role} {t : ℕ}
    {ids : (M.law x).SlotAt p → List (UnitId A U0 M.Channel U1)} (o : M.Channel → Fin U1)
    {y : UnitId A U0 M.Channel U1 → UnitContent ub} (hy : ∀ e, ∀ id ∈ ids e, y id ≠ none)
    {X : (M.law x).Role → Fin (t * ub) → (M.law x).Slot → Bool}
    (hX : ∀ k (e : (M.law x).SlotAt p), X p k e = (slotBits t (ids e) y).getD k false) :
    roleTable M x p t ids o y =
      unitTable (M.law x) ub X (fun ν => o ⟨x, ν⟩) p fun ν k => y (.new ⟨x, ν⟩ k) := by
  rw [roleTable, ite_eq_left hy, unitTable, codeTable_eq_sum_sigma, Fintype.sum_sigma]
  refine sum_congr rfl fun i _ => Fintype.sum_equiv (Equiv.piComm _) _ _ fun g => ?_
  rw [← ite_and]
  refine if_congr ?_ (prod_congr rfl fun k _ => by simp only [hX]; rfl) rfl
  simp only [ChannelOk, unitCount, length_sideString, codeWord, funext_iff, ← forall_and,
    Nat.add_right_cancel_iff]
  exact forall_congr' fun ν => and_comm.trans
    (and_congr ⟨fun h k => (h k).symm, fun h k => (h k).symm⟩ eq_comm)

section Identity

variable (x : Fin E) {t : ℕ} (o : M.Channel → Fin U1)
  {y : Fin (A + A') → UnitId A U0 M.Channel U1 → UnitContent ub}
  (ids : (M.law x).Slot → List (UnitId A U0 M.Channel U1)) (hub : 0 < ub) {m : ℕ}
  (hm : (M.law x).LengthLE m) (hB : t * (m + (M.law x).labelLength) + 1 ≤ U1)
  (hnew : ∀ ν k a, y a (.new ⟨x, ν⟩ k) = none) (hids : ∀ e ν k, .new ⟨x, ν⟩ k ∉ ids e)
  (hne : ∀ e, ∀ id ∈ ids e, ∀ d, y (M.party x ((M.law x).slotEnd e d)) id ≠ none)

include hub hm hB hnew hids hne

/-- **One outcome of a move.** The units `ids e` are given at the slot `e`, the move uses `t`
units, and `o` is the outcome. The copies `y` of the new units of the move are still absent, no
new unit of the move is given, and the copies of the given units at the two ends of their slots
are present. Then the sum, over the common contents of the new units, of the product of the
tables of the roles is the sum, over the indices that give the outcome `o` and over the strings
on all channels, of the product of the tables of the law. -/
theorem move_outcome :
    ∑ z ∈ Play.common none (newUnits M x o), ∏ p,
      roleTable M x p t (fun e => ids e) o
        (Play.extend (UnitId.holder M.channelParty) (newUnits M x o) y z (M.party x p)) =
      ∑ i : Fin (t * ub) → (M.law x).Index,
        if ∀ ν, (o ⟨x, ν⟩ : ℕ) =
            (∑ k, ((M.law x).labelLength + (M.law x).length (i k) ν)) / ub then
          ∑ g : (ν : (M.law x).Channel) → (k : Fin (t * ub)) →
              BitString ((M.law x).length (i k) ν),
            ∏ p, ∏ k, (M.law x).table p (i k)
              (fun e => (slotBits t (ids e) (y (M.party x p))).getD k false) fun ν => g ν k
        else 0 := by
  have hext (z) (p) (e) : ∀ id ∈ ids e, Play.extend (UnitId.holder M.channelParty)
      (newUnits M x o) y z (M.party x p) id = y (M.party x p) id := fun id hid =>
    Play.extend_of_notMem fun hn => by
      obtain ⟨ν, k, rfl, -⟩ := mem_newUnits.1 hn
      exact hids e ν k hid
  have e1 : ∀ z ∈ Play.common none (newUnits M x o), ∀ p,
      roleTable M x p t (fun e => ids e) o
        (Play.extend (UnitId.holder M.channelParty) (newUnits M x o) y z (M.party x p)) =
      unitTable (M.law x) ub (B := t * ub)
        (fun p k e => (slotBits t (ids e) (y (M.party x p))).getD k false) (fun ν => o ⟨x, ν⟩) p
        fun ν k => z (.new ⟨x, ν⟩ k) := by
    intro z hz p
    rw [roleTable_eq_unitTable (X := fun p k e =>
      (slotBits t (ids e) (y (M.party x p))).getD k false) o ?_ fun k e => by
        rw [slotBits_congr (hext z p e)]]
    · refine codeTable_congr _ _ fun ν hν => funext fun k => ?_
      by_cases hn : (.new ⟨x, ν⟩ k : UnitId A U0 M.Channel U1) ∈ newUnits M x o
      · exact Play.extend_of_holds hn (hν.imp fun d hd => congrArg (M.party x) hd)
      · rw [Play.extend_of_notMem hn, hnew, Play.mem_common.1 hz _ hn]
    · rintro ⟨e, d, rfl⟩ id hid
      rw [hext z _ e id hid]
      exact hne e id hid d
  rw [sum_congr rfl fun z hz => prod_congr rfl fun p _ => e1 z hz p,
    ← sum_prod_unitTable (fun p k e => (slotBits t (ids e) (y (M.party x p))).getD k false)
      (fun ν => o ⟨x, ν⟩) hub hm (by rwa [Nat.mul_right_comm, Nat.mul_div_cancel _ hub])]
  refine sum_bij_ne_zero (fun z _ _ ν k => z (.new ⟨x, ν⟩ k)) (fun _ _ _ => mem_univ _) ?_ ?_
    fun _ _ _ => rfl
  · intro z₁ h₁ _ z₂ h₂ _ heq
    funext id
    by_cases hn : id ∈ newUnits M x o
    · obtain ⟨ν, k, rfl, -⟩ := mem_newUnits.1 hn
      exact congrFun (congrFun heq ν) k
    · rw [Play.mem_common.1 h₁ _ hn, Play.mem_common.1 h₂ _ hn]
  · intro ζ _ hζ
    have hemb : Function.Injective fun q : (M.law x).Channel × Fin U1 =>
        (.new ⟨x, q.1⟩ q.2 : UnitId A U0 M.Channel U1) := by
      rintro ⟨_, _⟩ ⟨_, _⟩ ⟨⟩
      rfl
    have hz (ν k) : Function.extend (fun q : (M.law x).Channel × Fin U1 =>
        (.new ⟨x, q.1⟩ q.2 : UnitId A U0 M.Channel U1)) (fun q => ζ q.1 q.2) (fun _ => none)
        (.new ⟨x, ν⟩ k) = ζ ν k := hemb.extend_apply _ _ (ν, k)
    refine ⟨_, Play.mem_common.2 fun id hn => ?_, by simpa only [hz] using hζ,
      funext fun ν => funext fun k => hz ν k⟩
    by_cases hr : ∃ q : (M.law x).Channel × Fin U1, .new ⟨x, q.1⟩ q.2 = id
    · obtain ⟨⟨ν, k⟩, rfl⟩ := hr
      rw [hz]
      exact eq_none_of_unitTable_ne_zero (fun h0 => hζ (prod_eq_zero (mem_univ _) h0))
        ⟨ν, false, rfl⟩ (not_le.1 fun hk => hn (new_mem_newUnits.2 ⟨rfl, hk⟩))
    · exact Function.extend_apply' _ _ _ hr

/-- Outcomes of a move that no indices give contribute nothing. -/
theorem move_zero (ho : ¬∃ i : Fin (t * ub) → (M.law x).Index, ∀ ν,
      (o ⟨x, ν⟩ : ℕ) = (∑ k, ((M.law x).labelLength + (M.law x).length (i k) ν)) / ub) :
    ∑ z ∈ Play.common none (newUnits M x o), ∏ p,
      roleTable M x p t (fun e => ids e) o
        (Play.extend (UnitId.holder M.channelParty) (newUnits M x o) y z (M.party x p)) = 0 := by
  rw [move_outcome x o ids hub hm hB hnew hids hne]
  exact sum_eq_zero fun i _ => ite_eq_right fun h => ho ⟨i, h⟩

/-- **The identity of one move.** The units `ids e` are given at the slot `e`, at most `t` at a
slot, and the move uses `t` units. The copies `y` of the new units of the move are still absent,
no new unit of the move is given, and the copies of the given units at the two ends of their
slots are present. Then the condition that the two copies of every given unit agree is the sum,
over the outcomes of the move and over the common contents of its new units, of the product of
the tables of the roles. -/
theorem move_identity (ht : ∀ e, (ids e).length ≤ t) :
    (∑ oo : (M.law x).Channel → Fin U1,
      ∑ z ∈ Play.common none (newUnits M x (M.setOutcome o x oo)), ∏ p,
        roleTable M x p t (fun e => ids e) (M.setOutcome o x oo)
          (Play.extend (UnitId.holder M.channelParty) (newUnits M x (M.setOutcome o x oo)) y z
            (M.party x p))) =
      if ∀ e, ∀ id ∈ ids e, y (M.party x ((M.law x).slotEnd e false)) id =
        y (M.party x ((M.law x).slotEnd e true)) id then 1 else 0 := by
  have hlt (i : Fin (t * ub) → (M.law x).Index) (ν) :
      (∑ k, ((M.law x).labelLength + (M.law x).length (i k) ν)) / ub < U1 := by
    have := unitCount_sideString_le (lab := (M.law x).label) (ub := ub) (U := U1)
      (fun j => hm j ν) (by rwa [Nat.mul_right_comm, Nat.mul_div_cancel _ hub]) i
      fun _ _ => false
    rwa [unitCount, length_sideString] at this
  have hc (i : Fin (t * ub) → (M.law x).Index) (oo : (M.law x).Channel → Fin U1) :
      (∀ ν, (oo ν : ℕ) = (∑ k, ((M.law x).labelLength + (M.law x).length (i k) ν)) / ub) ↔
        oo = fun ν => ⟨_, hlt i ν⟩ := by
    simp [funext_iff, Fin.ext_iff]
  simp only [move_outcome x _ ids hub hm hB hnew hids hne, Moves.setOutcome_self]
  rw [sum_comm]
  simp only [hc, sum_ite_eq', mem_univ, ite_true]
  exact ((M.law x).pow (t * ub) fun p k e =>
    (slotBits t (ids e) (y (M.party x p))).getD k false).symm.trans (if_congr (forall_congr'
      fun e => slotBits_eq_iff (fun id hid => hne e id hid false) (fun id hid => hne e id hid true)
        (ht e)) rfl rfl)

end Identity

end Cslib.Circuits.Arithmetic.Separation.Cut
