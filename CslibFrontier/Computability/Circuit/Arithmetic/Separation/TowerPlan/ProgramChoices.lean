/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.TowerPlan.ProgramLoads
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.TowerPlan.Norms

/-!
# The program of the tower plan: choices from the loads, the loop over time, and the tree

The program of the tower plan of [AnthropicVPVNP2026] (Theorem H.2(d); modules `Nc.Tow.Slp3` and
`Nc.Tow.Slp5`) computes from loads `L x` of the targets, in five stages, the chosen types of the
stages, the numbers of units at the vertices, the kinds of laws that are used and the numbers of
units of the moves (`ChoicesIn`, `choices_stage`). A loop over time computes the numbers of units
of the moves of the earlier times by the loads of `ProgramLoads.lean` and these choices, eight
stages for every time, and so the numbers of units, the alive units and the loads of the plan
(`CountsIn`, `counts_stage`). From the loads, two more stages compute the parents in the tree of
the tower and the units between the nodes and their parents (`TreeIn`, `tree_stage`).

## Main definitions

* `ChoicesIn`: the choices from the loads are among the computed functions.
* `CountsIn`: the numbers of units of the moves, the alive units and the loads are among the
  computed functions.
* `TreeIn`: the parents in the tree and the units between the nodes and their parents are among
  the computed functions.

## Main results

* `choices_stage`, `counts_stage`, `tree_stage`: the stages of the program.
* `costP_active`: whether a relay is used is decided from the indicators of the chosen types.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Theorem H.2(d) and (e), p. 46, and the proof ("For (d)", p. 48); modules `Nc.Tow.Slp3`,
  `Nc.Tow.Slp5`
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.TowerPlan

open Finset Cslib.CoveringTower

variable {F : Type*} [CommSemiring F] {h b D J r m Uu A U0 U1 : ℕ} {T : Tower h b D J r}
  {R : Routes T m Uu} {ch : Fin A ↪ T.X 0} {FL : VertexLaws F T}
  {Inp : Type} {K Y N p c a : ℕ} {inp : Fin N → Inp → Fin K} {H H' : Set (Inp → ℕ)}

private theorem ProgramBound.card_edge_le {Y : ℕ} (hB : ProgramBound R ch FL U0 U1 Y)
    (j : Fin (J + 1)) : Fintype.card (T.Ed j) ≤ Y :=
  (Fintype.card_le_of_injective (Target.edge (m := m) (A := A) j) fun _ _ he => by
    cases he; rfl).trans hB.card_target_le

/-! ### The number of units at a vertex -/

private theorem minUnits_lt (hb : 0 < b) {L : Target T m A → ℕ} {w : ℕ} (hL : ∀ τ, L τ ≤ w)
    (l : VertexMove FL) : l.minUnits L < b * Fintype.card (Sym2 T.Fl) * w + 2 := by
  set s := Fintype.card (Sym2 T.Fl)
  have h1 := VertexMove.scale_mul_minUnits_le L l (n' := fun _ => w) fun q => hL _
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hs : (s : ℝ) ≤ (s : ℝ) ^ 2 := by exact_mod_cast Nat.le_self_pow two_ne_zero s
  have hN : T.NN2 (fun _ => w) ≤ ((b * s * w : ℕ) : ℝ) ^ 2 := by
    have e1 : (∑ q : Sym2 T.Fl, if q.IsDiag then (0 : ℝ) else (w : ℝ) ^ 2) ≤ s * (w : ℝ) ^ 2 :=
      (sum_le_card_nsmul _ _ ((w : ℝ) ^ 2) fun q _ => by
        split_ifs <;> [positivity; exact le_rfl]).trans_eq (by simp [s, nsmul_eq_mul])
    rw [Tower.NN2_def]
    calc _ ≤ (b : ℝ) * (b - 1) / 2 * (s * (w : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left e1 (by nlinarith)
      _ ≤ (b : ℝ) ^ 2 * ((s : ℝ) ^ 2 * (w : ℝ) ^ 2) := by gcongr; nlinarith
      _ = _ := by push_cast; ring
  have h2 : √(T.NN2 fun _ => w) ≤ (b * s * w : ℕ) :=
    (Real.sqrt_le_sqrt hN).trans_eq (Real.sqrt_sq (Nat.cast_nonneg _))
  have ha : (1 : ℝ) ≤ FL.scale := by exact_mod_cast FL.scale_pos
  have h3 : (l.minUnits L : ℝ) ≤ (b * s * w : ℕ) + 1 := le_of_mul_le_mul_left
    (by nlinarith [Nat.cast_nonneg (α := ℝ) (b * s * w)] : (FL.scale : ℝ) * l.minUnits L ≤
      FL.scale * ((b * s * w : ℕ) + 1)) (by positivity)
  have : l.minUnits L ≤ b * s * w + 1 := by exact_mod_cast h3
  omega

private theorem minUnits_eq_card {L : Target T m A → ℕ} {l : VertexMove FL} {B : ℕ}
    (hB : l.minUnits L < B) :
    l.minUnits L = ((range B).filter fun s => ¬ ∃ d, (l.withKind d).Fits L s).card := by
  have e : (range B).filter (fun s => ¬ ∃ d, (l.withKind d).Fits L s) = range (l.minUnits L) := by
    ext s
    simp only [mem_filter, mem_range]
    refine ⟨fun ⟨_, hs⟩ => not_le.1 fun hle => hs ?_, fun hs => ⟨hs.trans hB, fun ⟨d, hd⟩ =>
      (Nat.sInf_le (⟨d, hd⟩ : s ∈ {t | ∃ d, (l.withKind d).Fits L t})).not_gt hs⟩⟩
    obtain ⟨d, hd⟩ := VertexMove.exists_fits_minUnits L l
    exact ⟨d, fun q hq => (hd q hq).trans (Nat.mul_le_mul_left _ hle)⟩
  rw [e, card_range]

/-! ### Choices from the loads -/

variable (R ch FL) in
/-- The choices from the loads `L x` are among the functions `H`: the indicators of the chosen
types of the stages, the numbers of units at the vertices, the indicators of the kinds of laws
that are used, and the numbers of units of the moves. -/
structure ChoicesIn (L : Inp → Target T m A → ℕ) (H : Set (Inp → ℕ)) : Prop where
  chosenType : ∀ (j : Fin J) i, {x | T.IsChosenType (edgeLoads (L x) j) i}.indicator 1 ∈ H
  minUnits : ∀ l : VertexMove FL, (fun x => l.minUnits (L x)) ∈ H
  isPicked : ∀ l : VertexMove FL, {x | l.IsPicked (L x)}.indicator 1 ∈ H
  countOfLoad : ∀ mv : Move R ch FL, (fun x => countOfLoad (L x) mv) ∈ H

private theorem ChoicesIn.mono {L : Inp → Target T m A → ℕ} (hc : ChoicesIn R ch FL L H)
    (hH : H ⊆ H') : ChoicesIn R ch FL L H' :=
  ⟨fun j i => hH (hc.chosenType j i), fun l => hH (hc.minUnits l), fun l => hH (hc.isPicked l),
    fun mv => hH (hc.countOfLoad mv)⟩

section Choices

variable {L : Inp → Target T m A → ℕ} (hY : StepBase K Y) (hB : ProgramBound R ch FL U0 U1 Y)
include hY hB

private theorem costP_fits (hm : ∀ τ, (fun x => L x τ) ∈ H) (l : VertexMove FL) {s : Inp → ℕ}
    (hs : Cost K H (Y ^ a) s) : CostP K H (Y ^ (a + 3)) fun x => l.Fits (L x) (s x) :=
  (hY.forall_mem (univ.filter fun q : Sym2 T.Fl => ¬ q.IsDiag)
    ((card_filter_le _ _).trans hB.card_pair_le) fun q _ =>
      hY.rel (fun u t => u ≤ FL.slotCount l.kind q * t)
        (Cost.of_mem (hm (.segment l.stage l.type l.vertex q))) hs).congr
    fun x => by simp only [VertexMove.Fits, mem_filter, mem_univ, true_and]

private theorem costP_isChosenType {j : ℕ} (hq : ∀ i, (fun x => T.sqLoad (edgeLoads (L x) j) i) ∈ H)
    (i : Fin h) : CostP K H (Y ^ 7) fun x => T.IsChosenType (edgeLoads (L x) j) i := by
  have h1 i : CostP K H (Y ^ 3) fun x => ∀ i', T.sqLoad (edgeLoads (L x) j) i ≤
      T.sqLoad (edgeLoads (L x) j) i' :=
    hY.forall_univ (by simpa using hB.types_le) fun i' =>
      hY.rel (· ≤ ·) (Cost.of_mem (hq i)) (Cost.of_mem (hq i'))
  refine (hY.and ((h1 i).mono (Nat.pow_le_pow_right hY.pos (by norm_num)))
    (hY.forall_mem (univ.filter (· < i)) ((card_filter_le _ _).trans (by simpa using hB.types_le))
      fun i' _ => hY.not (h1 i'))).congr fun x => ?_
  simp only [Tower.IsChosenType, IsLeast, lowerBounds, Set.mem_ofPred_eq, mem_filter, mem_univ,
    true_and]
  exact and_congr_right' ⟨fun h i' h' => not_lt.1 fun hi' => h i' hi' h',
    fun h i' hi' h' => (not_le.2 hi') (h h')⟩

private theorem cost_sqLoad (hL : ∀ x τ, L x τ ≤ numUnits R ch FL U0 U1)
    (hm : ∀ τ, (fun x => L x τ) ∈ H) (j : Fin J) (i : Fin h) :
    Cost K H (Y ^ 3) fun x => T.sqLoad (edgeLoads (L x) j) i := by
  have hle x (e : T.Ed j) : L x (.edge j.castSucc e) ^ 2 ≤ Y ^ 2 :=
    Nat.pow_le_pow_left ((hL x _).trans hB.numUnits_le) 2
  have h23 : Y ^ 2 ≤ Y ^ 3 := Nat.pow_le_pow_right hY.pos (by norm_num)
  have e x : T.sqLoad (edgeLoads (L x) j) i =
      ∑ e ∈ univ.filter (T.ty · = i), L x (.edge j.castSucc e) ^ 2 := by
    rw [sum_filter]
    exact sum_congr rfl fun e _ => by rw [edgeLoads_of_lt _ (by omega)]; rfl
  refine (hY.sum _ ((card_filter_le _ _).trans (hB.card_edge_le j.castSucc)) (fun e _ =>
    hY.op1 (· ^ 2) (Cost.of_mem (hm (.edge j.castSucc e))) fun x => hY.lt_of_le_two_mul_pow_three
      ((hle x e).trans (h23.trans (Nat.le_mul_of_pos_left _ two_pos)))) fun x =>
        hY.lt_of_le_two_mul_pow_three ?_).congr fun x => (e x).symm
  refine (sum_le_card_nsmul _ _ _ fun e _ => hle x e).trans ?_
  have := (card_filter_le univ (T.ty · = i)).trans (hB.card_edge_le j.castSucc)
  rw [smul_eq_mul]
  nlinarith [Nat.mul_le_mul_right (Y ^ 2) this, show Y * Y ^ 2 = Y ^ 3 by ring]

private theorem cost_minUnits (hb : 0 < b) (hL : ∀ x τ, L x τ ≤ numUnits R ch FL U0 U1)
    (hm : ∀ τ, (fun x => L x τ) ∈ H) (l : VertexMove FL) :
    Cost K H (Y ^ 8) fun x => l.minUnits (L x) :=
  (hY.card_filter (range Y) (by simp) fun s hs => hY.not (hY.exists_univ hB.card_kind_le
    fun d => costP_fits hY hB hm (l.withKind d) (hY.const (a := 0) s
      (hY.lt_of_le (mem_range.1 hs).le)))).congr fun x =>
        (minUnits_eq_card ((minUnits_lt hb (hL x) l).trans_le hB.units_le)).symm

private theorem costP_isPicked (hm : ∀ τ, (fun x => L x τ) ∈ H)
    (hu : ∀ l : VertexMove FL, (fun x => l.minUnits (L x)) ∈ H) (l : VertexMove FL) :
    CostP K H (Y ^ 7) fun x => l.IsPicked (L x) := by
  have h d : CostP K H (Y ^ 3) fun x => (l.withKind d).Fits (L x) (l.minUnits (L x)) :=
    costP_fits hY hB hm _ (Cost.of_mem (hu l))
  refine (hY.and ((h l.kind).mono (Nat.pow_le_pow_right hY.pos (by norm_num)))
    (hY.forall_mem (univ.filter fun d => Fintype.equivFin FL.Kind d <
      Fintype.equivFin FL.Kind l.kind) ((card_filter_le _ _).trans hB.card_kind_le)
        fun d _ => hY.not (h d))).congr fun x => ?_
  simp only [VertexMove.IsPicked, mem_filter, mem_univ, true_and]
  rfl

omit hB in
/-- Whether a relay is used is decided from the indicators of the chosen types in any number of
steps. -/
theorem costP_active
    (hi : ∀ (j : Fin J) i, {x | T.IsChosenType (edgeLoads (L x) j) i}.indicator 1 ∈ H)
    (y : Relay T m A) : CostP K H (Y ^ a) fun x => y.Active (L x) := by
  rcases y with ⟨-, -, -, -⟩ | ⟨j, i, e⟩ | ⟨j, e, s⟩ | e
  · exact hY.constP True
  · exact CostP.of_mem (hi j i)
  · by_cases hs : s = 0
    · exact (CostP.of_mem (hi j (T.ty e))).congr fun x => ⟨fun h _ => h, fun h => h hs⟩
    · exact (hY.constP True).congr fun x => ⟨fun _ h => absurd h hs, fun _ => trivial⟩
  · exact hY.constP True

private theorem cost_countOfLoad (hb : 0 < b) (hL : ∀ x τ, L x τ ≤ numUnits R ch FL U0 U1)
    (hm : ∀ τ, (fun x => L x τ) ∈ H)
    (hi : ∀ (j : Fin J) i, {x | T.IsChosenType (edgeLoads (L x) j) i}.indicator 1 ∈ H)
    (hu : ∀ l : VertexMove FL, (fun x => l.minUnits (L x)) ∈ H)
    (hp : ∀ l : VertexMove FL, {x | l.IsPicked (L x)}.indicator 1 ∈ H) (mv : Move R ch FL) :
    Cost K H (Y ^ 2) fun x => countOfLoad (L x) mv := by
  rcases mv with ⟨y, hy⟩ | l
  · exact hY.ite (costP_active hY hi y) (Cost.of_mem (hm y.input)) (hY.const 0 hY.zero_lt)
      (fun x => hY.lt_of_le ((hL x _).trans hB.numUnits_le)) fun _ => hY.zero_lt
  · exact hY.ite (CostP.of_mem (hp l)) (Cost.of_mem (hu l)) (hY.const 0 hY.zero_lt)
      (fun x => hY.lt_of_le ((minUnits_lt hb (hL x) l).trans_le hB.units_le).le)
      fun _ => hY.zero_lt

/-- **The choices from the loads** take five stages: the sums of the squares of the loads of the
types, the indicators of the chosen types, the numbers of units at the vertices, the indicators
of the kinds of laws that are used, and the numbers of units of the moves. -/
theorem choices_stage (hb : 0 < b) (hL : ∀ x τ, L x τ ≤ numUnits R ch FL U0 U1)
    (hS : SlpN inp (p + c * Y ^ 12) H) (hm : ∀ τ, (fun x => L x τ) ∈ H) :
    ∃ H', SlpN inp (p + (c + 5) * Y ^ 12) H' ∧ H ⊆ H' ∧ ChoicesIn R ch FL L H' := by
  have hJh : Fintype.card (Fin J × Fin h) ≤ Y ^ 2 := by
    have := hB.endTime_le
    simp only [endTime] at this
    simpa [pow_two] using Nat.mul_le_mul (show J ≤ Y by omega) hB.types_le
  have hl : Fintype.card (VertexMove FL) ≤ Y ^ 1 := by simpa using hB.card_vertexMove_le
  obtain ⟨H1, s1, u1, f1⟩ := hY.stage hS
    (fun (q : Fin J × Fin h) x => T.sqLoad (edgeLoads (L x) q.1) q.2) hJh
    (fun q => cost_sqLoad hY hB hL hm q.1 q.2) (by norm_num)
  obtain ⟨H2, s2, u2, f2⟩ := hY.stage s1
    (fun q : Fin J × Fin h => {x | T.IsChosenType (edgeLoads (L x) q.1) q.2}.indicator 1) hJh
    (fun q => costP_iff.1 (costP_isChosenType hY hB (fun i => f1 (q.1, i)) q.2)) (by norm_num)
  have m2 τ : (fun x => L x τ) ∈ H2 := u2 (u1 (hm τ))
  obtain ⟨H3, s3, u3, f3⟩ := hY.stage s2 (fun l x => l.minUnits (L x)) hl
    (cost_minUnits hY hB hb hL m2) (by norm_num)
  obtain ⟨H4, s4, u4, f4⟩ := hY.stage s3
    (fun l : VertexMove FL => {x | l.IsPicked (L x)}.indicator 1) hl
    (fun l => costP_iff.1 (costP_isPicked hY hB (fun τ => u3 (m2 τ)) f3 l)) (by norm_num)
  obtain ⟨H5, s5, u5, f5⟩ := hY.stage s4 (fun mv x => countOfLoad (L x) mv) (e := 1)
    (by simpa using hB.card_move_le) (cost_countOfLoad hY hB hb hL (fun τ => u4 (u3 (m2 τ)))
      (fun j i => u4 (u3 (f2 (j, i)))) (fun l => u4 (f3 l)) f4) (by norm_num)
  exact ⟨H5, s5, u1.trans (u2.trans (u3.trans (u4.trans u5))), fun j i => u5 (u4 (u3 (f2 (j, i)))),
    fun l => u5 (u4 (f3 l)), fun l => u5 (f4 l), f5⟩

/-! ### The tree -/

variable (hh : 0 < h)

omit hB in
private theorem costP_parent
    (hi : ∀ (j : Fin J) i, {x | T.IsChosenType (edgeLoads (L x) j) i}.indicator 1 ∈ H)
    (hhY : h ≤ Y) (P P' : T.Node) :
    CostP K H (Y ^ 2) fun x => P.parent hh (edgeLoads (L x)) = P' := by
  rcases P with _ | ⟨j, c⟩
  · exact (hY.constP (.root = P')).congr fun _ => Iff.rfl
  by_cases hj : (j : ℕ) + 1 ≤ J
  · refine (hY.exists_mem (univ.filter fun i => Tower.Node.ofChamber hj (T.hostOf i c) = P')
      ((card_filter_le _ _).trans (by simpa using hhY)) fun i _ =>
        CostP.of_mem (hi ⟨j, hj⟩ i)).congr fun x => ?_
    simp only [Tower.Node.parent, hj, dite_true, mem_filter, mem_univ, true_and,
      Tower.parentChamber, Tower.isChosenType_iff hh]
    exact ⟨fun ⟨i, h1, h2⟩ => h2 ▸ h1, fun h => ⟨_, h, rfl⟩⟩
  · exact (hY.constP (.root = P')).congr fun _ => by simp [Tower.Node.parent, hj]

private theorem cost_parentUnits (hL : ∀ x τ, L x τ ≤ numUnits R ch FL U0 U1)
    (hm : ∀ τ, (fun x => L x τ) ∈ H) (P : T.Node) :
    Cost K H (Y ^ 2) fun x => P.lift (T.parentUnits (edgeLoads (L x))) 0 := by
  rcases P with _ | ⟨j, c⟩
  · exact hY.const 0 hY.zero_lt
  have hcard := (card_filter_le univ fun e : T.Ed j => T.e0 e = c ∨ T.e1 e = c).trans
    (hB.card_edge_le j)
  refine (hY.sum _ hcard (fun e _ => Cost.of_mem (hm (.edge j e))) fun x =>
    hY.lt_of_le_two_mul_pow_three ?_).congr fun x =>
      sum_congr rfl fun e _ => (edgeLoads_of_lt _ j.2 e).symm
  refine (sum_le_card_nsmul _ _ Y fun e _ => (hL x _).trans hB.numUnits_le).trans ?_
  rw [smul_eq_mul]
  nlinarith [Nat.mul_le_mul_right Y hcard, Nat.pow_le_pow_right hY.pos (show 2 ≤ 3 by norm_num)]

omit hY hB in
/-- The tree for the loads `L x` is among the functions `H`: the indicators of the parents of
the nodes, and the units between the nodes and their parents (`0` at the root). -/
structure TreeIn (hh : 0 < h) (L : Inp → Target T m A → ℕ) (H : Set (Inp → ℕ)) : Prop where
  parent : ∀ P P' : T.Node, {x | P.parent hh (edgeLoads (L x)) = P'}.indicator 1 ∈ H
  parentUnits : ∀ P : T.Node, (fun x => P.lift (T.parentUnits (edgeLoads (L x))) 0) ∈ H

/-- **The tree** takes two stages: the indicators of the parents of the nodes, and the units
between the nodes and their parents. -/
theorem tree_stage (hL : ∀ x τ, L x τ ≤ numUnits R ch FL U0 U1)
    (hS : SlpN inp (p + c * Y ^ 12) H) (hm : ∀ τ, (fun x => L x τ) ∈ H)
    (hc : ChoicesIn R ch FL L H) :
    ∃ H', SlpN inp (p + (c + 2) * Y ^ 12) H' ∧ H ⊆ H' ∧ TreeIn hh L H' := by
  obtain ⟨H1, s1, u1, f1⟩ := hY.stage hS
    (fun q : T.Node × T.Node => {x | q.1.parent hh (edgeLoads (L x)) = q.2}.indicator 1) (e := 2)
    (by simpa [pow_two] using Nat.mul_le_mul hB.card_node_le hB.card_node_le)
    (fun q => costP_iff.1 (costP_parent hY hh hc.chosenType hB.types_le q.1 q.2)) (by norm_num)
  obtain ⟨H2, s2, u2, f2⟩ := hY.stage s1
    (fun (P : T.Node) x => P.lift (T.parentUnits (edgeLoads (L x))) 0) (e := 1)
    (by simpa using hB.card_node_le) (cost_parentUnits hY hB hL fun τ => u1 (hm τ)) (by norm_num)
  exact ⟨H2, s2, u1.trans u2, fun P P' => u2 (f1 (P, P')), f2⟩

end Choices

/-! ### The loop over time -/

variable {nx : Inp → Fin A → Fin A → ℕ} {ox : Inp → MoveChannel R ch FL → ℕ} {lhat : ℕ}

variable (nx ox lhat) in
/-- The numbers of the plan are among the functions `H`: what does not change in time, the
choices from the loads of the plan, the numbers of units of the moves, the alive units of the
channels and the loads of the targets. -/
structure CountsIn (H : Set (Inp → ℕ)) : Prop extends StaticIn nx ox lhat H,
    ChoicesIn R ch FL (fun x => load lhat (nx x) (ox x)) H where
  count : ∀ mv, (fun x => moveCount lhat (nx x) (ox x) mv) ∈ H
  alive : ∀ ν, (fun x => alive lhat (nx x) (ox x) ν) ∈ H
  load : ∀ τ, (fun x => load lhat (nx x) (ox x) τ) ∈ H

theorem CountsIn.mono (hc : CountsIn nx ox lhat H) (hH : H ⊆ H') : CountsIn nx ox lhat H' where
  toStaticIn := hc.toStaticIn.mono hH
  toChoicesIn := hc.toChoicesIn.mono hH
  count mv := hH (hc.count mv)
  alive ν := hH (hc.alive ν)
  load τ := hH (hc.load τ)

variable (hY : StepBase K Y) (hB : ProgramBound R ch FL U0 U1 Y) (hR : InputBound nx ox U0 U1)
  (hb : 0 < b)
include hY hB hR hb

private theorem countBefore_stage (hS : SlpN inp (p + c * Y ^ 12) H) (hs : StaticIn nx ox lhat H)
    (t : ℕ) : ∃ H', SlpN inp (p + (c + 1 + 8 * t) * Y ^ 12) H' ∧ H ⊆ H' ∧
      ∀ mv, (fun x => countBefore lhat (nx x) (ox x) t mv) ∈ H' := by
  induction t with
  | zero =>
    exact hY.stage hS (fun mv x => countBefore lhat (nx x) (ox x) 0 mv) (a := 0) (e := 1)
      (by simpa using hB.card_move_le)
      (fun mv => (hY.const 0 hY.zero_lt).congr fun x => (countBefore_zero mv).symm) (by norm_num)
  | succ t ih =>
    obtain ⟨H0, s0, u0, f0⟩ := ih
    obtain ⟨H1, s1, u1, f1, g1⟩ := loads_stage hY hB hR s0 (hs.mono u0) f0
    obtain ⟨H2, s2, u2, f2⟩ := choices_stage hY hB hb
      (fun x τ => loadGiven_le_numUnits (hR.initial_le x) (hR.outcome_le x) _ τ) s1 g1
    have hc mv : Cost K H2 (Y ^ 0) fun x => countBefore lhat (nx x) (ox x) (t + 1) mv := by
      by_cases ht : mv.time = t
      · exact Cost.of_mem (f2.countOfLoad mv) |>.congr fun x => by
          simp only [countBefore_succ, ht, ↓reduceIte]
      · exact Cost.of_mem (u2 (u1 (f0 mv))) |>.congr fun x => by
          simp only [countBefore_succ, ht, ↓reduceIte]
    obtain ⟨H3, s3, u3, f3⟩ := hY.stage s2
      (fun mv x => countBefore lhat (nx x) (ox x) (t + 1) mv) (e := 1)
      (by simpa using hB.card_move_le) hc (by norm_num)
    exact ⟨H3, (show c + 1 + 8 * t + 2 + 5 + 1 = c + 1 + 8 * (t + 1) by ring) ▸ s3,
      u0.trans (u1.trans (u2.trans u3)), f3⟩

/-- **The numbers of the plan** take `11 + 8 Y` stages: what does not change in time, the loop
over time, eight stages for every time, the alive units and the loads, and the choices from the
loads. -/
theorem counts_stage (hS : SlpN inp (p + c * Y ^ 12) H) (hi : InputsIn nx ox H) :
    ∃ H', SlpN inp (p + (c + 11 + 8 * Y) * Y ^ 12) H' ∧ H ⊆ H' ∧ CountsIn nx ox lhat H' := by
  obtain ⟨H1, s1, u1, f1⟩ := static_stage (lhat := lhat) hY hB hR hS hi
  obtain ⟨H2, s2, u2, f2⟩ := countBefore_stage hY hB hR hb s1 f1 (endTime J m)
  obtain ⟨H3, s3, u3, f3, g3⟩ := loads_stage hY hB hR s2 (f1.mono u2)
    (Nf := fun x => moveCount lhat (nx x) (ox x)) f2
  obtain ⟨H4, s4, u4, f4⟩ := choices_stage (L := fun x => load lhat (nx x) (ox x)) hY hB hb
    (fun x τ => loadGiven_le_numUnits (hR.initial_le x) (hR.outcome_le x) _ τ) s3 g3
  refine ⟨H4, s4.le hY.zero_lt (Nat.add_le_add_left (Nat.mul_le_mul_right _ ?_) _),
    u1.trans (u2.trans (u3.trans u4)), f1.mono (u2.trans (u3.trans u4)), f4,
    fun mv => u4 (u3 (f2 mv)), fun ν => u4 (f3 ν), fun τ => u4 (g3 τ)⟩
  have := hB.endTime_le
  omega

end Cslib.Circuits.Arithmetic.Separation.TowerPlan
