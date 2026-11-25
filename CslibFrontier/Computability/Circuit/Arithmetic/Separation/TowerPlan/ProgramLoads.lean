/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.SlpCostPow
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.TowerPlan.Cardinalities

/-!
# The program of the tower plan: bounds, and the loads from the numbers of units

The numbers of the tower plan of [AnthropicVPVNP2026] (Theorem H.2(d); modules `Nc.Tow.Slp1`
and `Nc.Tow.Slp2`) are computed by a straight-line program over an alphabet `Fin K`. Its inputs
are the numbers `nx x` of initial units and the outcomes `ox x`, as functions of the input `x` of
the program, at most `U0` and `U1` (`InputBound`). The costs are counted in powers of a base `Y`
(`Cslib.Circuits.StepBase`) that bounds the sizes of the plan (`ProgramBound`), and the program
is built in stages of `Y ^ 12` gates (`Cslib.Circuits.StepBase.stage`). This file computes what
does not change in time (`StaticIn`, in three stages), and then, for given numbers of units of the
moves, the alive units of every channel and the load of every target (`loads_stage`, in two
stages). All loads are at most the number `numUnits` of units of the play.

## Main definitions

* `ProgramBound`: the bounds for the program.
* `InputBound`: the numbers of initial units and the outcomes are at most `U0` and `U1`.
* `InputsIn`, `StaticIn`: the inputs, and what does not change in time, are among the computed
  functions.

## Main results

* `loadGiven_le_numUnits`: the loads are at most `numUnits`.
* `static_stage`, `loads_stage`: the stages of the program.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Theorem H.2(d), p. 46, and its proof ("For (d)", p. 48); modules `Nc.Tow.Slp1`, `Nc.Tow.Slp2`
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.TowerPlan

open Finset Cslib.CoveringTower

variable {F : Type*} [CommSemiring F] {h b D J r m Uu A U0 U1 : ℕ} {T : Tower h b D J r}

section Bounds

variable (R : Routes T m Uu) (ch : Fin A ↪ T.X 0) (FL : VertexLaws F T)

/-- The bounds for the program of the tower plan: the square of the number of base parties, the
number of units, the numbers of channels, moves, targets, nodes, pairs of places and kinds of
laws, the number of types, the end of time, and a bound for the numbers of units at the vertices
are at most `Y`. -/
structure ProgramBound (U0 U1 Y : ℕ) : Prop where
  base_mul_base_le : A * A ≤ Y
  numUnits_le : numUnits R ch FL U0 U1 ≤ Y
  card_channel_le : Fintype.card (MoveChannel R ch FL) ≤ Y
  card_move_le : Fintype.card (Move R ch FL) ≤ Y
  card_target_le : Fintype.card (Target T m A) ≤ Y
  card_node_le : Fintype.card T.Node ≤ Y
  card_pair_le : Fintype.card (Sym2 T.Fl) ≤ Y
  card_kind_le : Fintype.card FL.Kind ≤ Y
  types_le : h ≤ Y
  endTime_le : endTime J m ≤ Y
  units_le : b * Fintype.card (Sym2 T.Fl) * numUnits R ch FL U0 U1 + 2 ≤ Y

namespace ProgramBound

variable {R ch FL} {Y : ℕ} (hB : ProgramBound R ch FL U0 U1 Y)
include hB

private theorem base_le : A ≤ Y :=
  (Nat.le_mul_self A).trans hB.base_mul_base_le

private theorem initial_le (a : Fin A) : U0 ≤ Y :=
  (Nat.le_mul_of_pos_left U0 (Nat.mul_pos a.pos a.pos)).trans
    ((Nat.le_add_right _ _).trans hB.numUnits_le)

private theorem outcome_le (ν : MoveChannel R ch FL) : U1 ≤ Y :=
  (Nat.le_mul_of_pos_left U1 (Fintype.card_pos_iff.2 ⟨ν⟩)).trans
    ((Nat.le_add_left _ _).trans hB.numUnits_le)

theorem card_vertexMove_le : Fintype.card (VertexMove FL) ≤ Y :=
  (Fintype.card_le_of_injective (Move.vertex (R := R) (ch := ch)) fun _ _ he => by
    cases he; rfl).trans hB.card_move_le

theorem card_law_channel_le (l : VertexMove FL) : Fintype.card (FL.law l.kind).Channel ≤ Y :=
  (Fintype.card_le_of_injective (Sigma.mk (β := fun mv : Move R ch FL => mv.law.Channel)
    (.vertex l)) sigma_mk_injective).trans hB.card_channel_le

end ProgramBound

end Bounds

variable {R : Routes T m Uu} {ch : Fin A ↪ T.X 0} {FL : VertexLaws F T}

private theorem sum_card_initialTarget_le {n : Fin A → Fin A → ℕ} (hn : ∀ a c, n a c ≤ U0)
    (τ : Target T m A) :
    ∑ a, ∑ c, ((range (n a c)).filter fun k => initialTarget R ch a c k = τ).card ≤
      A * A * U0 :=
  (sum_le_card_nsmul _ _ (A * U0) fun a _ => (sum_le_card_nsmul _ _ U0 fun c _ =>
    (card_filter_le _ _).trans ((card_range _).trans_le (hn a c))).trans_eq (by simp)).trans_eq
      (by simp [mul_assoc])

/-- The loads are at most `numUnits` when the numbers of initial units and the outcomes are at
most `U0` and `U1`, whatever numbers of units the moves use. -/
theorem loadGiven_le_numUnits {lhat : ℕ} {n : Fin A → Fin A → ℕ} {o : MoveChannel R ch FL → ℕ}
    (hn : ∀ a c, n a c ≤ U0) (ho : ∀ ν, o ν ≤ U1) (N : Move R ch FL → ℕ) (τ : Target T m A) :
    loadGiven lhat n o N τ ≤ numUnits R ch FL U0 U1 := by
  refine add_le_add ?_ ((sum_le_card_nsmul _ _ U1 fun ν _ => ?_).trans_eq (by simp))
  · unfold initialLoad
    split_ifs
    exacts [sum_card_initialTarget_le hn τ, Nat.zero_le _]
  · split_ifs
    exacts [(aliveGiven_le _ _).trans (ho ν), Nat.zero_le _]

section Program

variable {Inp : Type} {K Y N p c : ℕ} {inp : Fin N → Inp → Fin K} {H H' : Set (Inp → ℕ)}
  (nx : Inp → Fin A → Fin A → ℕ) (ox : Inp → MoveChannel R ch FL → ℕ) (lhat : ℕ)

/-- The numbers of initial units and the outcomes, at every input `x` of the program, are at most
`U0` and `U1`. -/
structure InputBound (U0 U1 : ℕ) : Prop where
  initial_le : ∀ x a c, nx x a c ≤ U0
  outcome_le : ∀ x ν, ox x ν ≤ U1

/-- The numbers of initial units and the outcomes are among the functions `H`. -/
structure InputsIn (H : Set (Inp → ℕ)) : Prop where
  initial : ∀ a c, (fun x => nx x a c) ∈ H
  outcome : ∀ ν, (fun x => ox x ν) ∈ H

/-- What does not change in time is among the functions `H`: the inputs, the indicator of the
bound for the initial units, the initial units with every target, and the sum of the squares of
the outcomes of every law move. -/
structure StaticIn (H : Set (Inp → ℕ)) : Prop extends InputsIn nx ox H where
  initialBound : {x | InitialBound lhat (nx x)}.indicator 1 ∈ H
  initialLoad : ∀ τ, (fun x => initialLoad R ch lhat (nx x) τ) ∈ H
  sqOutcome : ∀ l : VertexMove FL,
    (fun x => ∑ ν : (FL.law l.kind).Channel, ox x ⟨.vertex l, ν⟩ ^ 2) ∈ H

variable {nx ox lhat}

theorem InputsIn.mono (hi : InputsIn nx ox H) (hH : H ⊆ H') : InputsIn nx ox H' :=
  ⟨fun a c => hH (hi.initial a c), fun ν => hH (hi.outcome ν)⟩

theorem StaticIn.mono (hs : StaticIn nx ox lhat H) (hH : H ⊆ H') : StaticIn nx ox lhat H' :=
  ⟨hs.toInputsIn.mono hH, hH hs.initialBound, fun τ => hH (hs.initialLoad τ),
    fun l => hH (hs.sqOutcome l)⟩

variable (hY : StepBase K Y) (hB : ProgramBound R ch FL U0 U1 Y) (hR : InputBound nx ox U0 U1)
include hY hB hR

private theorem costP_initialBound (hi : InputsIn nx ox H) :
    CostP K H (Y ^ 6) fun x => InitialBound lhat (nx x) := by
  have hn x a c : nx x a c ≤ Y := (hR.initial_le x a c).trans (hB.initial_le a)
  have hA : (univ : Finset (Fin A)).card ≤ Y := by simpa using hB.base_le
  refine hY.forall_univ (by simpa using hB.base_le) fun a => hY.rel1 (· ≤ lhat) <|
    hY.sum univ hA (fun c _ => ?_) fun x => hY.lt_of_le_two_mul_pow_three ?_
  · by_cases hca : c = a
    · simpa only [hca, ↓reduceIte] using hY.const (H := H) (a := 1) 0 hY.zero_lt
    · simpa only [hca, ↓reduceIte] using hY.op (· + ·) (Cost.of_mem (hi.initial a c))
        (Cost.of_mem (hi.initial c a)) fun x => hY.lt_of_le_two_mul_pow_three (by
          nlinarith [hn x a c, hn x c a, Nat.le_self_pow (by norm_num : 3 ≠ 0) Y])
  · refine (sum_le_card_nsmul _ _ (2 * Y) fun c _ => ?_).trans ?_
    · split_ifs <;> linarith [hn x a c, hn x c a]
    · simp only [card_univ, Fintype.card_fin, smul_eq_mul]
      nlinarith [hB.base_le, Nat.pow_le_pow_right hY.pos (show 2 ≤ 3 by norm_num) (n := Y)]

private theorem cost_initialLoad (hi : InputsIn nx ox H)
    (hv : {x | InitialBound lhat (nx x)}.indicator 1 ∈ H) (τ : Target T m A) :
    Cost K H (Y ^ 7) fun x => initialLoad R ch lhat (nx x) τ := by
  have hle x := (sum_card_initialTarget_le (R := R) (ch := ch) (hR.initial_le x) τ).trans
    ((Nat.le_add_right _ _).trans hB.numUnits_le)
  have hA : (univ : Finset (Fin A)).card ≤ Y := by simpa using hB.base_le
  refine hY.ite (CostP.of_mem hv) (hY.sum univ hA (fun a _ => hY.sum univ hA (fun c _ => ?_)
    fun x => hY.lt_of_le ?_) fun x => hY.lt_of_le (hle x)) (hY.const 0 hY.zero_lt)
    (fun x => hY.lt_of_le (hle x)) fun _ => hY.zero_lt
  · exact hY.op1 (fun s => ((range s).filter fun k => initialTarget R ch a c k = τ).card)
      (Cost.of_mem (hi.initial a c)) fun x => hY.lt_of_le <| (card_filter_le _ _).trans <|
        (card_range _).trans_le ((hR.initial_le x a c).trans (hB.initial_le a))
  · exact (single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ a)).trans (hle x)

private theorem cost_sqOutcome (hi : InputsIn nx ox H) (l : VertexMove FL) :
    Cost K H (Y ^ 3) fun x => ∑ ν : (FL.law l.kind).Channel, ox x ⟨.vertex l, ν⟩ ^ 2 := by
  have hsq x (ν : (FL.law l.kind).Channel) : ox x ⟨.vertex l, ν⟩ ^ 2 ≤ Y ^ 2 :=
    Nat.pow_le_pow_left ((hR.outcome_le x _).trans (hB.outcome_le ⟨.vertex l, ν⟩)) 2
  have h23 : Y ^ 2 ≤ Y ^ 3 := Nat.pow_le_pow_right hY.pos (by norm_num)
  refine hY.sum univ (by simpa using hB.card_law_channel_le l) (fun ν _ => hY.op1 (· ^ 2)
    (Cost.of_mem (hi.outcome ⟨.vertex l, ν⟩)) fun x => hY.lt_of_le_two_mul_pow_three
      ((hsq x ν).trans (h23.trans (Nat.le_mul_of_pos_left _ two_pos))))
    fun x => hY.lt_of_le_two_mul_pow_three ?_
  refine (sum_le_card_nsmul _ _ _ fun ν _ => hsq x ν).trans ?_
  have := hB.card_law_channel_le l
  simp only [card_univ, smul_eq_mul]
  nlinarith [Nat.mul_le_mul_right (Y ^ 2) this, show Y * Y ^ 2 = Y ^ 3 by ring]

/-- **What does not change in time** takes three stages: the indicator of the bound for the
initial units, the initial units with every target, and the sums of the squares of the outcomes
of the law moves. -/
theorem static_stage (hS : SlpN inp (p + c * Y ^ 12) H) (hi : InputsIn nx ox H) :
    ∃ H', SlpN inp (p + (c + 3) * Y ^ 12) H' ∧ H ⊆ H' ∧ StaticIn nx ox lhat H' := by
  obtain ⟨H1, s1, u1, f1⟩ := hY.stage hS (κ := Unit)
    (fun _ => {x | InitialBound lhat (nx x)}.indicator 1) (e := 0) (by simp)
    (fun _ => costP_iff.1 (costP_initialBound hY hB hR hi)) (by norm_num)
  obtain ⟨H2, s2, u2, f2⟩ := hY.stage s1 (fun τ x => initialLoad R ch lhat (nx x) τ) (e := 1)
    (by simpa using hB.card_target_le)
    (fun τ => cost_initialLoad hY hB hR (hi.mono u1) (f1 ()) τ) (by norm_num)
  obtain ⟨H3, s3, u3, f3⟩ := hY.stage s2
    (fun (l : VertexMove FL) x => ∑ ν : (FL.law l.kind).Channel, ox x ⟨.vertex l, ν⟩ ^ 2) (e := 1)
    (by simpa using hB.card_vertexMove_le) (fun l => cost_sqOutcome hY hB hR (hi.mono
      (u1.trans u2)) l) (by norm_num)
  exact ⟨H3, s3, u1.trans (u2.trans u3), ⟨hi.mono (u1.trans (u2.trans u3)), u3 (u2 (f1 ())),
    fun τ => u3 (f2 τ), f3⟩⟩

variable {Nf : Inp → Move R ch FL → ℕ}

private theorem cost_aliveGiven (hs : StaticIn nx ox lhat H) (hN : ∀ mv, (fun x => Nf x mv) ∈ H)
    (ν : MoveChannel R ch FL) : Cost K H (Y ^ 3) fun x => aliveGiven (ox x) ν (Nf x ν.1) := by
  have ho x : ox x ν ≤ Y := (hR.outcome_le x ν).trans (hB.outcome_le ν)
  rcases ν with ⟨⟨y, hy⟩ | l, ν⟩
  · refine (hY.op (fun s t => if s = t then t else 0) (Cost.of_mem (hs.outcome _))
      (Cost.of_mem (hN _)) fun x => hY.lt_of_le ?_).mono
        (Nat.pow_le_pow_right hY.pos (show 1 ≤ 3 by norm_num))
    exact (aliveGiven_le (o := ox x) ⟨.relay y hy, ν⟩ _).trans (ho x)
  · exact hY.ite (hY.rel (fun q t => r * b * q ≤ FL.lengthBound * t ^ 2)
      (Cost.of_mem (hs.sqOutcome l)) (Cost.of_mem (hN _))) (Cost.of_mem (hs.outcome _))
      (hY.op min (Cost.of_mem (hs.outcome _)) (Cost.of_mem (hN _)) fun x =>
        hY.lt_of_le ((min_le_left _ _).trans (ho x)))
      (fun x => hY.lt_of_le (ho x)) fun x => hY.lt_of_le ((min_le_left _ _).trans (ho x))

private theorem cost_loadGiven (hs : StaticIn nx ox lhat H)
    (ha : ∀ ν, (fun x => aliveGiven (ox x) ν (Nf x ν.1)) ∈ H) (τ : Target T m A) :
    Cost K H (Y ^ 3) fun x => loadGiven lhat (nx x) (ox x) (Nf x) τ := by
  have hle x : loadGiven lhat (nx x) (ox x) (Nf x) τ ≤ Y :=
    (loadGiven_le_numUnits (hR.initial_le x) (hR.outcome_le x) _ τ).trans hB.numUnits_le
  have e x : loadGiven lhat (nx x) (ox x) (Nf x) τ = initialLoad R ch lhat (nx x) τ +
      ∑ ν ∈ univ.filter (fun ν : MoveChannel R ch FL => ν.1.target ν.2 = τ),
        aliveGiven (ox x) ν (Nf x ν.1) := by
    rw [sum_filter]
    rfl
  refine (hY.op (· + ·) (Cost.of_mem (hs.initialLoad τ)) (hY.sum _
    ((card_filter_le _ _).trans hB.card_channel_le) (fun ν _ => Cost.of_mem (ha ν))
    fun x => hY.lt_of_le ?_) fun x => (e x).symm ▸ hY.lt_of_le (hle x)).congr fun x => (e x).symm
  have h1 := hle x
  rw [e x] at h1
  omega

/-- **The loads from the numbers of units** take two stages: the alive units of every channel and
the load of every target, when the moves use the numbers `Nf x` of units. -/
theorem loads_stage (hS : SlpN inp (p + c * Y ^ 12) H) (hs : StaticIn nx ox lhat H)
    (hN : ∀ mv, (fun x => Nf x mv) ∈ H) :
    ∃ H', SlpN inp (p + (c + 2) * Y ^ 12) H' ∧ H ⊆ H' ∧
      (∀ ν, (fun x => aliveGiven (ox x) ν (Nf x ν.1)) ∈ H') ∧
      ∀ τ, (fun x => loadGiven lhat (nx x) (ox x) (Nf x) τ) ∈ H' := by
  obtain ⟨H1, s1, u1, f1⟩ := hY.stage hS (fun ν x => aliveGiven (ox x) ν (Nf x ν.1)) (e := 1)
    (by simpa using hB.card_channel_le) (cost_aliveGiven hY hB hR hs hN) (by norm_num)
  obtain ⟨H2, s2, u2, f2⟩ := hY.stage s1 (fun τ x => loadGiven lhat (nx x) (ox x) (Nf x) τ)
    (e := 1) (by simpa using hB.card_target_le) (cost_loadGiven hY hB hR (hs.mono u1) f1)
    (by norm_num)
  exact ⟨H2, s2, u1.trans u2, fun ν => u2 (f1 ν), f2⟩

end Program

end Cslib.Circuits.Arithmetic.Separation.TowerPlan
