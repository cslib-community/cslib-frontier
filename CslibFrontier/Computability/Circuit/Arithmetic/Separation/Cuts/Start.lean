/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Cuts.Initial
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# The start of the play on the blocks of a run

Lemma I.2 of [AnthropicVPVNP2026] (module `Nc.G.Start`) writes the value of a tape automaton on
a run of `K * T` steps as a sum of values of networks on the `K` blocks and the `K` parts of the
input, the *base* parties. Here the networks are the starting positions of the play
(`Play.value`): the units are the initial units (`Cut.initialUnits`), all of them current, and
the weight is the product of the tables of the base parties at the beginning
(`Cut.initialTable`). The packets of `ℓ` bits of the paper are the units of `ub` bits, and its
parts of `T'` letters are the parts of `ℓ` letters (`Cut.parts`).

For given states between the blocks, the terms of these positions are the segments with staircase
support (`Cut.sum_segments`): the row data are those of the segments
(`Cut.validRow_and_ok_iff`), the string from a party `a` to a party `b` is the bit string of the
segments that `a` writes and `b` reads, its units are the common contents of the two copies of
the initial units between `a` and `b`, and a string is determined by its units.

`Cut.runVal_eq_sum_value_initial` is the identity of Lemma I.2. The lemma also bounds the number
of units at a party whose table is not zero; that bound is not stated in this file
(`Cut.sum_unitCount_le` bounds the units of the strings that one party writes or reads).

## Main results

* `Cut.initialTable_congr`: the table of a base party at the beginning reads its copies of the
  initial units only.
* `Cut.initialTable_ne_none`: the initial units that a base party holds are present if its table
  at the beginning does not vanish.
* `Cut.sum_value_initial`: the sum, over the valid row data and the numbers of units, of the
  values of the starting positions is the sum over the segments with staircase support.
* `Cut.runVal_eq_sum_value_initial`: the value of an automaton in `K * T` steps is the sum, over
  the states between the blocks, the valid row data and the numbers of units, of the values of
  the starting positions.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Lemma I.2 (Section I.3), which Proposition J.2 of Appendix J applies; module `Nc.G.Start`
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Cut

open Finset List.StairRefinement Tape

variable {F Γ S Q N : Type*} {A A' K T U0 U1 c ub : ℕ}

section Units

variable [Fintype S] {cb : Option Γ → BitString c} {np : N → Bool → Fin (A + A')}

/-- The numbers of units of the strings between the parties, if `R a s b` is what the party `a`
writes for the party `b` on the tape `s`. -/
private noncomputable def countsOf (ub U0 : ℕ) (cb : Option Γ → BitString c)
    (R : Fin A → Option S → Fin A → List Γ) (a b : Fin A) : Fin (U0 + 1) :=
  Fin.ofNat (U0 + 1) (unitCount ub (segmentString cb fun s => R a s b))

/-- The copies of the initial units at their holders, if `R a s b` is what the party `a` writes
for the party `b` on the tape `s`: the units of the strings between the parties. -/
private noncomputable def copiesOf (cb : Option Γ → BitString c)
    (R : Fin A → Option S → Fin A → List Γ) (p : Fin (A + A')) :
    UnitId A U0 N U1 → UnitContent ub
  | .init a b k => if p = Fin.castAdd A' a ∨ p = Fin.castAdd A' b then
      unitsOf ub (segmentString cb fun s => R a s b) k else none
  | .new _ _ => none

variable [Fintype N] [DecidableEq N]

/-- The row data are valid, the two copies of every initial unit agree, and the conditions of the
tables of all parties at the beginning hold for what the parties write (`R`) and read (`C`), if
and only if what is written has staircase support, every party reads what the other parties write
for it, and the row data, the numbers of units and the contents of the units are those of what is
written. -/
private theorem validRows_and_initialOk_iff (hcb : Function.Injective cb) (hc : 0 < c)
    (hub : 0 < ub) {ρ : Option S → Fin A → RowData A} {n : Fin A → Fin A → Fin (U0 + 1)}
    {y : Fin (A + A') → UnitId A U0 N U1 → UnitContent ub}
    {R C : Fin A → Option S → Fin A → List Γ}
    (hR : ∀ a b, unitCount ub (segmentString cb fun s => R a s b) ≤ U0) :
    (ValidRows ρ ∧ y ∈ Play.contents (UnitId.holder np) none (initialUnits n) ∧
      Play.Agree (UnitId.holder np) (initialUnits n) y ∧
      ∀ p, InitialOk ub cb (fun s => ρ s p) (fun a b => n a b) p (y (Fin.castAdd A' p))
        (R p) (C p)) ↔
    y = copiesOf cb R ∧ n = countsOf ub U0 cb R ∧ (ρ = fun s => rowsOf fun a => R a s) ∧
      (∀ s, Stair fun a => R a s) ∧ ∀ p s b, C p s b = R b s p := by
  constructor
  · rintro ⟨hρ, hy, hag, hI⟩
    simp only [InitialOk, forall_and] at hI
    obtain ⟨hok, ⟨hn, h1⟩, hn', h2⟩ := hI
    have hr (s) := validRow_and_ok_iff.1 ⟨hρ s, fun p => hok p s⟩
    have hL (a b) : segmentString cb (fun s => C b s a) = segmentString cb fun s => R a s b := by
      refine unitsOf_injective hub (funext fun k => ?_)
      by_cases hk : k < n a b
      · have hk' : k < U0 := by omega
        rw [← h1 a b ⟨k, hk'⟩, ← h2 b a ⟨k, hk'⟩]
        exact (hag (.init a b ⟨k, hk'⟩) (init_mem_initialUnits.2 hk)).symm
      · rw [unitsOf_eq_none.2 (by rw [hn']; omega), unitsOf_eq_none.2 (by rw [hn]; omega)]
    refine ⟨?_, ?_, funext fun s => (hr s).2, fun s => (hr s).1,
      fun p s b => congrFun (segmentString_injective hcb hc (hL b p)) s⟩
    · simp only [hL] at h2
      funext p id
      rcases id with ⟨a, b, k⟩ | ⟨ν, k⟩ <;>
        grind [copiesOf, UnitId.holds_init, Play.mem_contents, new_notMem_initialUnits]
    · funext a b
      exact Fin.ext (by simp [countsOf, hn])
  · rintro ⟨rfl, rfl, rfl, hst, hC⟩
    have hr (s) := validRow_and_ok_iff.2 ⟨hst s, rfl⟩
    have hC' (p) : C p = fun s b => R b s p := funext₂ (hC p)
    have hn (a b) : (countsOf ub U0 cb R a b : ℕ) =
        unitCount ub (segmentString cb fun s => R a s b) :=
      Nat.mod_eq_of_lt (Nat.lt_succ_of_le (hR a b))
    refine ⟨fun s => (hr s).1, Play.mem_contents.2 fun p id hid => ?_, fun id hid => ?_,
      fun p => ⟨fun s => (hr s).2 p, fun b => ⟨(hn p b).symm, fun k => ?_⟩,
        fun b => ⟨?_, fun k => ?_⟩⟩⟩
    · rcases id with ⟨a, b, k⟩ | ⟨ν, k⟩ <;>
        grind [copiesOf, UnitId.holds_init, unitsOf_eq_none, init_mem_initialUnits]
    · rcases id with ⟨a, b, k⟩ | ⟨ν, k⟩ <;> simp_all [copiesOf, UnitId.holder]
    all_goals simp [copiesOf, hC', hn]

end Units

variable [CommSemiring F] [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S] [Fintype Q]
  [DecidableEq Q] {mu : Letter S Unit Γ → Matrix Q Q F} {cb : Option Γ → BitString c}
  {q : Fin (K + 1) → Q} {x : Fin K → List Γ}

/-- The string from a party to a party has at most `U0` units if the weight of the party is not
zero. -/
private theorem unitCount_le_of_partyWeight_ne_zero
    (hU : (T + (Fintype.card S + 1)) * c / ub + 1 ≤ U0) (hx : ∀ κ, (x κ).length ≤ T)
    {p : Fin (K + K)} {R C : Option S → Fin (K + K) → List Γ}
    (h : partyWeight mu T q x p R C ≠ 0) (b : Fin (K + K)) :
    unitCount ub (segmentString cb fun s => R s b) ≤ U0 := by
  refine le_trans ?_ hU
  rw [unitCount, length_segmentString, Fintype.card_option]
  gcongr
  exact (sum_le_sum fun s _ => length_le_cat (R s) b).trans
    (sum_length_le_of_partyWeight_ne_zero hx h)

variable [Fintype N]

variable [DecidableEq N]

/-- What every party writes and reads: at most `T` letters for every tape and every party. -/
private noncomputable abbrev sides (Γ S : Type*) [Fintype Γ] [Fintype S] [DecidableEq S]
    (K T : ℕ) : Finset (Fin (K + K) →
      (Option S → Fin (K + K) → List Γ) × (Option S → Fin (K + K) → List Γ)) :=
  Fintype.piFinset fun _ =>
    (Fintype.piFinset fun _ => Fintype.piFinset fun _ => List.wordsLe Γ T) ×ˢ
      Fintype.piFinset fun _ => Fintype.piFinset fun _ => List.wordsLe Γ T

/-- **Units.** For given states between the blocks, the sum, over the valid row data and the
numbers of units, of the values of the starting positions is the sum over the segments with
staircase support of the product of the weights of the parties. In a starting position the units
are the initial units, all of them current, and the weight is the product of the tables of the
base parties at the beginning. -/
theorem sum_value_initial (hcb : Function.Injective cb) (hc : 0 < c) (hub : 0 < ub)
    (hU : (T + (Fintype.card S + 1)) * c / ub + 1 ≤ U0) (np : N → Bool → Fin (K + K + A'))
    (q : Fin (K + 1) → Q) (hx : ∀ κ, (x κ).length ≤ T) :
    (∑ ρ : Option S → Fin (K + K) → RowData (K + K), if ValidRows ρ then
      ∑ n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1),
        Play.value (UnitId.holder np) (none : UnitContent ub)
          (initialUnits (N := N) (U1 := U1) n) (initialUnits n) fun y => ∏ p : Fin (K + K),
            initialTable mu T cb q x (fun s => ρ s p) (fun a b => n a b) p (y (Fin.castAdd A' p))
      else 0) =
    ∑ X ∈ segments Γ S K T, if ∀ s, Stair (X s) then segmentWeight mu T q x X else 0 := by
  -- a product of sums over what one party writes and reads is a sum over what all parties do
  simp only [initialTable, ← sum_product', prod_univ_sum, Fintype.prod_ite_zero]
  simp only [Play.value_eq_sum_filter, sum_filter, ← Fintype.sum_ite_mem (Play.contents _ _ _),
    ← ite_and, ite_sum_zero, sum_comm (t := sides Γ S K T)]
  -- the row data, the numbers of units and the contents of the units are determined
  trans ∑ z ∈ sides Γ S K T,
    if (∀ s, Stair fun a => (z a).1 s) ∧ ∀ p s b, (z p).2 s b = (z b).1 s p then
      ∏ p, partyWeight mu T q x p (z p).1 (z p).2 else 0
  · refine sum_congr rfl fun z _ => ?_
    by_cases hw : ∏ p, partyWeight mu T q x p (z p).1 (z p).2 = 0
    · simp [hw]
    simp only [validRows_and_initialOk_iff hcb hc hub fun a =>
      unitCount_le_of_partyWeight_ne_zero hU hx fun h0 => hw (prod_eq_zero (mem_univ a) h0),
      ite_and, sum_ite_eq', mem_univ, ite_true]
  -- every party reads what the other parties write for it
  rw [← sum_filter, ← sum_filter]
  refine sum_nbij' (fun z s a b => (z a).1 s b)
    (fun X p => (fun s b => X s p b, fun s b => X s b p)) ?_ ?_ ?_ (fun _ _ => rfl) ?_
  · simp +contextual [Fintype.mem_piFinset]
  · simp +contextual [Fintype.mem_piFinset]
  · exact fun z hz => funext fun p =>
      Prod.ext rfl (funext₂ fun s b => ((mem_filter.1 hz).2.2 p s b).symm)
  · exact fun z hz => prod_congr rfl fun p _ =>
      congrArg (partyWeight mu T q x p (z p).1) (funext₂ ((mem_filter.1 hz).2.2 p))

/-- **The start of the play.** The value of an automaton with one input in `K * T` steps, for an
input of at most `K * ℓ` letters with `ℓ ≤ T`, is the sum, over the states between the blocks,
the valid row data and the numbers of units, of the values of the starting positions, where the
input parties hold the parts of the input of `ℓ` letters each. -/
theorem runVal_eq_sum_value_initial {F : Type*} [CommRing F]
    {mu : Letter S Unit Γ → Matrix Q Q F} (hcb : Function.Injective cb) (hc : 0 < c)
    (hub : 0 < ub) (hU : (T + (Fintype.card S + 1)) * c / ub + 1 ≤ U0)
    (np : N → Bool → Fin (K + K + A')) (i e : Q) (u : Unit → List Γ) {ℓ : ℕ} (hℓ : ℓ ≤ T)
    (hu : (u ()).length ≤ K * ℓ) :
    runVal mu i e (K * T) u = ∑ q : Fin (K + 1) → Q, if q 0 = i ∧ q (Fin.last K) = e then
      ∑ ρ : Option S → Fin (K + K) → RowData (K + K), if ValidRows ρ then
        ∑ n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1),
          Play.value (UnitId.holder np) (none : UnitContent ub)
            (initialUnits (N := N) (U1 := U1) n) (initialUnits n) fun y => ∏ p : Fin (K + K),
              initialTable mu T cb q (parts ℓ (u ())) (fun s => ρ s p) (fun a b => n a b) p
                (y (Fin.castAdd A' p))
        else 0
      else 0 := by
  have hx (κ : Fin K) : (parts ℓ (u ()) κ).length ≤ T := (length_parts_le _ _ _).trans hℓ
  rw [runVal_blocks]
  refine sum_congr rfl fun q _ => ?_
  rw [sum_value_initial hcb hc hub hU np q hx,
    ← sum_segments q hx u (by rw [cat_parts, List.take_of_length_le hu])]

end Cslib.Circuits.Arithmetic.Separation.Cut
