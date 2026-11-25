/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.TowerPlan.Counts
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.TowerPlan.StartLoads
import Mathlib.Tactic.FinCases

/-!
# The tower plan: the norms of the loads, stage by stage

One stage of the tower plan of [AnthropicVPVNP2026] (proof of Theorem H.2; modules `Nc.Tow.Load3`
and `Nc.Tow.Load2`) multiplies the norm of the loads of the edges by at most `ρ`, up to an error
for every chamber of the next level (`norm_load_le`). For the chosen type `i` of the stage, the
edges of type `i` in the next level carry at most the loads of the edges over them, the end
segments at a vertex carry at most the end segments of the loads, and the edges of the other
types at a vertex carry at most the alive units of the channels of the law move that is used
there, whose outcome is short. These are the hypotheses of `Tower.kap_le_of_stage`.

## Main results

* `VertexMove.exists_fits`, `VertexMove.exists_fits_minUnits`, `VertexMove.exists_isPicked`: the
  end segments at a vertex fit into some number of units, the least one is attained, and a kind of
  law is used.
* `VertexMove.scale_mul_minUnits_le`, `moveCount_vertex_le`: the number of units at a vertex.
* `Relay.of_target_eq_segment`, `load_segment_le`: the end segments.
* `moveCount_vertex_eq_zero`: law moves of a type that is not chosen, or of a kind that is not
  used, use no units.
* `norm_load_le`: the norms of the loads, one stage.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Theorem H.2 (proof: "One stage", p. 47); modules `Nc.Tow.Load3`, `Nc.Tow.Load2`
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.TowerPlan

open Finset Cslib.CoveringTower Cut

variable {F : Type*} [CommSemiring F] {h b D J r m Uu A : ℕ} {T : Tower h b D J r}
  {R : Routes T m Uu} {ch : Fin A ↪ T.X 0} {FL : VertexLaws F T} {lhat : ℕ}
  {n : Fin A → Fin A → ℕ} {o : MoveChannel R ch FL → ℕ}

/-! ### The number of units at a vertex -/

namespace VertexMove

variable (L : Target T m A → ℕ)

/-- The end segments at a vertex fit into some number of units, for some kind of law. -/
theorem exists_fits (j : Fin J) (i : Fin h) (ω : T.V (j + 1) i) :
    ∃ t d, Fits L (⟨j, i, ω, d⟩ : VertexMove FL) t := by
  obtain ⟨t, ht⟩ := exists_nat_ge (√(T.NN2 fun q => L (.segment j i ω q)) / (FL.scale : ℝ))
  obtain ⟨d, hd⟩ := FL.exists_le_card_slot _ t <| by
    rwa [div_le_iff₀' (by exact_mod_cast FL.scale_pos)] at ht
  exact ⟨t, d, hd⟩

/-- The least number of units at a vertex is attained by some kind of law. -/
theorem exists_fits_minUnits (l : VertexMove FL) :
    ∃ d, (l.withKind d).Fits L (l.minUnits L) := by
  obtain ⟨t, d, hd⟩ := exists_fits (FL := FL) L l.stage l.type l.vertex
  exact Nat.sInf_mem (s := {t | ∃ d, (l.withKind d).Fits L t}) ⟨t, d, hd⟩

/-- A kind of law is used at every vertex. -/
theorem exists_isPicked (l : VertexMove FL) : ∃ d, (l.withKind d).IsPicked L := by
  obtain ⟨d₀, hd₀⟩ := exists_fits_minUnits L l
  obtain ⟨d, hd, hmin⟩ := exists_min_image
    (univ.filter fun d => (l.withKind d).Fits L (l.minUnits L)) (Fintype.equivFin FL.Kind)
    ⟨d₀, mem_filter.2 ⟨mem_univ _, hd₀⟩⟩
  exact ⟨d, (mem_filter.1 hd).2, fun d' hd' hf =>
    (hmin d' (mem_filter.2 ⟨mem_univ _, hf⟩)).not_gt hd'⟩

/-- The number of units at a vertex is at most the norm of the end segments over the scale, plus
one, for every bound `n'` of the end segments. -/
theorem scale_mul_minUnits_le (l : VertexMove FL) {n' : Sym2 T.Fl → ℕ}
    (hn' : ∀ q, L (.segment l.stage l.type l.vertex q) ≤ n' q) :
    (FL.scale : ℝ) * l.minUnits L ≤ √(T.NN2 n') + FL.scale := by
  have ha : (0 : ℝ) < FL.scale := by exact_mod_cast FL.scale_pos
  set x := √(T.NN2 fun q => L (.segment l.stage l.type l.vertex q))
  have h1 : l.minUnits L ≤ ⌈x / FL.scale⌉₊ := by
    obtain ⟨d, hd⟩ := FL.exists_le_card_slot _ ⌈x / FL.scale⌉₊ <| by
      rw [← div_le_iff₀' ha]
      exact Nat.le_ceil _
    exact Nat.sInf_le ⟨d, hd⟩
  have h2 : x ≤ √(T.NN2 n') := Real.sqrt_le_sqrt (Tower.NN2_mono hn')
  have h3 := Nat.ceil_lt_add_one (div_nonneg (Real.sqrt_nonneg _) ha.le : 0 ≤ x / FL.scale)
  calc (FL.scale : ℝ) * l.minUnits L ≤ FL.scale * (x / FL.scale + 1) := by
        gcongr
        exact (Nat.cast_le.2 h1).trans h3.le
    _ = x + FL.scale := by field_simp
    _ ≤ _ := by linarith

private theorem minUnits_eq_zero {l : VertexMove FL}
    (hL : ∀ q, L (.segment l.stage l.type l.vertex q) = 0) : l.minUnits L = 0 :=
  Nat.eq_zero_of_le_zero (Nat.sInf_le ⟨l.kind, fun q _ => (hL q).trans_le (Nat.zero_le _)⟩)

end VertexMove

/-- A law move uses at most the number of units at its vertex. -/
theorem moveCount_vertex_le (l : VertexMove FL) :
    moveCount lhat n o (.vertex l) ≤ l.minUnits (load lhat n o) := by
  rw [moveCount_eq, countOfLoad]
  split_ifs <;> omega

/-! ### End segments -/

private theorem relayAlive_middle_le_load (j : Fin J) (e : T.Ed j) (s : Fin 4) (d : Bool) :
    relayAlive lhat n o (.middle j e s) d ≤ load lhat n o (.edge j.castSucc e) :=
  (relayAlive_middle_le j e s d).trans
    (by split_ifs; exacts [(edgeLoads_of_lt _ (by omega) e).le, Nat.zero_le _])

/-- The relays whose channels give units to end segments: the second and the fourth step of the
way of an edge of the type of the vertex, on their channels `false`. -/
theorem Relay.of_target_eq_segment {x : Relay T m A} {d : Bool} {j : Fin J} {i : Fin h}
    {ω : T.V (j + 1) i} {q : Sym2 T.Fl} (hx : x.target R ch d = .segment j i ω q) :
    d = false ∧ ∃ e : T.Ed j, T.ty e = i ∧
      ((x = .middle j e 1 ∧ T.πV (T.vx i (T.e0 e)) = ω ∧
        s(T.co i (T.hostOf i (T.e0 e)), T.co i (T.e0 e)) = q) ∨
      (x = .middle j e 3 ∧ T.πV (T.vx i (T.e1 e)) = ω ∧
        s(T.co i (T.hostOf i (T.e1 e)), T.co i (T.e1 e)) = q)) := by
  rcases x with ⟨a', c', γ', s'⟩ | ⟨j', i', e'⟩ | ⟨j', e', s'⟩ | e' <;> cases d <;>
    (try fin_cases s') <;> simp only [Relay.target] at hx <;> (try split_ifs at hx) <;>
    first
    | (cases hx; exact ⟨rfl, _, rfl, .inl ⟨rfl, rfl, rfl⟩⟩)
    | (cases hx; exact ⟨rfl, _, rfl, .inr ⟨rfl, rfl, rfl⟩⟩)
    | simp_all

/-- The end segments of a type that is not chosen carry no units. -/
private theorem load_segment_eq_zero {j : Fin J} {i : Fin h}
    (hi : ¬ T.IsChosenType (edgeLoads (load lhat n o) j) i) (ω : T.V (j + 1) i) (q : Sym2 T.Fl) :
    load lhat n o (.segment j i ω q) = 0 := by
  rw [load_eq_relay fun _ _ => by simp [Move.target],
    initialLoad_eq_zero (by simp) (by simp only [Target.time]; omega), zero_add]
  refine sum_eq_zero fun x _ => sum_eq_zero fun d _ => ite_eq_right_iff.2 fun hx => ?_
  obtain ⟨rfl, e, rfl, ⟨rfl, -⟩ | ⟨rfl, -⟩⟩ := Relay.of_target_eq_segment hx <;>
    exact Nat.eq_zero_of_le_zero ((relayAlive_middle_le j e _ false).trans_eq (ite_eq_right hi))

/-- A law move at a vertex of a type that is not chosen, or of a kind that is not used, uses no
units. -/
theorem moveCount_vertex_eq_zero {l : VertexMove FL}
    (hl : ¬ T.IsChosenType (edgeLoads (load lhat n o) l.stage) l.type ∨
      ¬ l.IsPicked (load lhat n o)) :
    moveCount lhat n o (.vertex l) = 0 := by
  rcases hl with hl | hl
  · exact Nat.eq_zero_of_le_zero ((moveCount_vertex_le l).trans_eq
      (VertexMove.minUnits_eq_zero _ fun q => load_segment_eq_zero hl _ q))
  · rw [moveCount_eq, countOfLoad, ite_eq_right hl]

/-- The end segments on a pair of places of a vertex carry at most the end segments of the loads
of the edges. -/
theorem load_segment_le (j : Fin J) (i : Fin h) (ω : T.V (j + 1) i) (q : Sym2 T.Fl) :
    load lhat n o (.segment j i ω q) ≤
      T.nEnd i (fun e => load lhat n o (.edge j.castSucc e)) ω q := by
  rw [load_eq_relay fun _ _ => by simp [Move.target],
    initialLoad_eq_zero (by simp) (by simp only [Target.time]; omega), zero_add, Tower.nEnd_eq,
    ← Fintype.sum_prod_type']
  refine (sum_le_sum_of_ne_zero (t := (univ : Finset (Bool × T.Ed j)).image
    fun (⟨b, e⟩ : Bool × T.Ed j) => (.middle j e (bif b then 1 else 3), false))
      fun ⟨x, d⟩ _ hxd => ?_).trans ((sum_image_le_of_nonneg fun _ _ => Nat.zero_le _).trans ?_)
  · rw [Fintype.sum_prod_type, Fintype.sum_bool]
    refine add_le_add (sum_le_sum fun e _ => ?_) (sum_le_sum fun e _ => ?_) <;>
      dsimp only <;> split_ifs with h1 h2 <;>
      first
      | exact Nat.zero_le _
      | (cases h1; exact absurd ⟨rfl, rfl, rfl⟩ h2)
      | exact relayAlive_middle_le_load j e _ false
  · obtain ⟨rfl, e, -, ⟨rfl, -⟩ | ⟨rfl, -⟩⟩ := Relay.of_target_eq_segment (ite_ne_right_iff.1 hxd).1
    exacts [mem_image.2 ⟨(true, e), mem_univ _, rfl⟩, mem_image.2 ⟨(false, e), mem_univ _, rfl⟩]

/-! ### The edges of the next level -/

/-- Only the third step of the way of an edge gives units to an edge of the next level, on its
channel `false`. -/
private theorem Relay.of_target_eq_edge_succ {x : Relay T m A} {d : Bool} {j : Fin J}
    {e' : T.Ed (j + 1)} (hx : x.target R ch d = .edge j.succ e') :
    ∃ e, x = .middle j e 2 ∧ d = false ∧ T.πE e = e' := by
  rcases x with ⟨a', c', γ', s'⟩ | ⟨j', i', e'⟩ | ⟨j', e', s'⟩ | e' <;> cases d <;>
    (try fin_cases s') <;> simp only [Relay.target] at hx <;> (try split_ifs at hx) <;>
    first
    | (obtain ⟨h1, h2⟩ := Target.edge.inj hx
       obtain rfl := Fin.succ_injective _ h1
       exact ⟨_, rfl, rfl, eq_of_heq h2⟩)
    | simp_all

/-- The edges of the chosen type in the next level carry at most the loads of the edges over
them: their units are the middle segments. -/
private theorem load_edge_succ_le (hr : 0 < r) (hb : 0 < b) {j : Fin J} {i : Fin h}
    (hi : T.IsChosenType (edgeLoads (load lhat n o) j) i) {e' : T.Ed (j + 1)}
    (he' : T.ty e' = i) :
    load lhat n o (.edge j.succ e') ≤
      ∑ e ∈ univ.filter (T.πE · = e'), load lhat n o (.edge j.castSucc e) := by
  have hv : (∑ l, ∑ c, if (Move.vertex l : Move R ch FL).target c = .edge j.succ e' then
      alive lhat n o ⟨.vertex l, c⟩ else 0) = 0 :=
    sum_eq_zero fun l _ => sum_eq_zero fun c _ => ite_eq_right_iff.2 fun hc => by
      obtain ⟨j', i', ω, d⟩ := l
      obtain ⟨h1, h2⟩ := Target.edge.inj hc
      obtain rfl : j = j' := (Fin.succ_injective _ h1).symm
      have hne := ((T.nr j.2 i').symm (ω, FL.nearPair d c)).2
      rw [eq_of_heq h2] at hne
      have h0 : moveCount lhat n o (.vertex ⟨j, i', ω, d⟩) = 0 :=
        moveCount_vertex_eq_zero (.inl fun h => hne (he'.trans (hi.unique h)))
      exact (congrArg (aliveGiven o _) h0).trans (aliveGiven_zero hr hb _)
  rw [load_eq_sum, initialLoad_eq_zero (by simp) (by simp only [Target.time, Fin.val_succ]; omega),
    zero_add, hv, add_zero, ← Fintype.sum_prod_type']
  refine (sum_le_sum_of_ne_zero (t := (univ.filter (T.πE · = e')).image
    fun e => (.middle j e 2, false)) fun ⟨x, d⟩ _ hxd => ?_).trans
      ((sum_image_le_of_nonneg fun _ _ => Nat.zero_le _).trans (sum_le_sum fun e _ => ?_))
  · split_ifs
    exacts [relayAlive_middle_le_load j e 2 false, Nat.zero_le _]
  · obtain ⟨e, rfl, rfl, he⟩ := Relay.of_target_eq_edge_succ (ite_ne_right_iff.1 hxd).1
    exact mem_image.2 ⟨e, mem_filter.2 ⟨mem_univ _, he⟩, rfl⟩

/-- The alive units of the channels of a law move are short. -/
private theorem sum_alive_sq_le (l : VertexMove FL) :
    r * b * ∑ c, alive lhat n o ⟨.vertex l, c⟩ ^ 2 ≤
      FL.lengthBound * moveCount lhat n o (.vertex l) ^ 2 := by
  by_cases hs : l.OutcomeShort o (moveCount lhat n o (.vertex l))
  · simp only [alive, aliveGiven, ite_eq_left hs]
    exact hs
  · obtain ⟨i₀⟩ := FL.nonempty_index l.kind
    calc r * b * ∑ c, alive lhat n o ⟨.vertex l, c⟩ ^ 2 ≤
        r * b * ∑ c, ((FL.law l.kind).labelLength + (FL.law l.kind).length i₀ c) ^ 2 *
          moveCount lhat n o (.vertex l) ^ 2 := by
          refine Nat.mul_le_mul_left _ (sum_le_sum fun c _ => ?_)
          have h1 : alive lhat n o ⟨.vertex l, c⟩ ≤ moveCount lhat n o (.vertex l) := by
            simp only [alive, aliveGiven, ite_eq_right hs]
            exact min_le_right _ _
          have h2 := Nat.one_le_pow 2 _ (Nat.lt_of_lt_of_le Nat.one_pos
            ((FL.labelLength_pos l.kind).trans (Nat.le_add_right _
              ((FL.law l.kind).length i₀ c))))
          calc _ ≤ moveCount lhat n o (.vertex l) ^ 2 := by gcongr
            _ ≤ _ := Nat.le_mul_of_pos_left _ h2
      _ = (r * b * ∑ c, ((FL.law l.kind).labelLength + (FL.law l.kind).length i₀ c) ^ 2) *
          moveCount lhat n o (.vertex l) ^ 2 := by
          rw [← sum_mul]
          ring
      _ ≤ _ := Nat.mul_le_mul_right _ (FL.sum_length_sq_le l.kind i₀)

/-- An edge of the next level at a vertex of the chosen type carries at most the alive units of
its channel of the law move that is used at the vertex. -/
private theorem load_edge_vertex_le (hr : 0 < r) (hb : 0 < b) {j : Fin J} {i : Fin h}
    (hi : T.IsChosenType (edgeLoads (load lhat n o) j) i) {ω : T.V (j + 1) i} {d : FL.Kind}
    (hd : (⟨j, i, ω, d⟩ : VertexMove FL).IsPicked (load lhat n o)) (c : (FL.law d).Channel) :
    load lhat n o (.edge j.succ ((T.nr j.2 i).symm (ω, FL.nearPair d c)).1) ≤
      alive lhat n o ⟨.vertex ⟨j, i, ω, d⟩, c⟩ := by
  have hrel : (∑ x, ∑ d', if x.target R ch d' = .edge j.succ ((T.nr j.2 i).symm
      (ω, FL.nearPair d c)).1 then relayAlive lhat n o x d' else 0) = 0 :=
    sum_eq_zero fun x _ => sum_eq_zero fun d' _ => ite_eq_right_iff.2 fun hx => by
      obtain ⟨e, rfl, rfl, he⟩ := Relay.of_target_eq_edge_succ hx
      have hne := ((T.nr j.2 i).symm (ω, FL.nearPair d c)).2
      rw [← he, T.π_ty j.2] at hne
      exact Nat.eq_zero_of_le_zero ((relayAlive_middle_le j e 2 false).trans_eq
        (ite_eq_right fun h => hne (hi.unique h).symm))
  rw [load_eq_sum, initialLoad_eq_zero (by simp) (by simp only [Target.time, Fin.val_succ]; omega),
    zero_add, hrel, zero_add]
  refine (Fintype.sum_sigma (α := fun l : VertexMove FL => (FL.law l.kind).Channel)
    fun lc => if (Move.vertex lc.fst : Move R ch FL).target lc.snd = .edge j.succ
      ((T.nr j.2 i).symm (ω, FL.nearPair d c)).1 then alive lhat n o ⟨.vertex lc.fst, lc.snd⟩
      else 0).symm.trans_le
    ((sum_le_sum_of_ne_zero (t := {⟨⟨j, i, ω, d⟩, c⟩}) ?_).trans ?_)
  · rintro ⟨⟨j', i', ω', d'⟩, c'⟩ _ hne
    obtain ⟨htg, hal⟩ := ite_ne_right_iff.1 hne
    obtain ⟨h1, h2⟩ := Target.edge.inj htg
    obtain rfl : j = j' := (Fin.succ_injective _ h1).symm
    have hm : moveCount lhat n o (.vertex ⟨j, i', ω', d'⟩) ≠ 0 := fun h0 =>
      hal ((congrArg (aliveGiven o _) h0).trans (aliveGiven_zero hr hb _))
    obtain rfl : i = i' := hi.unique (by_contra fun h => hm (moveCount_vertex_eq_zero (.inl h)))
    have hpk : (⟨j, i, ω', d'⟩ : VertexMove FL).IsPicked (load lhat n o) :=
      by_contra fun h => hm (moveCount_vertex_eq_zero (.inr h))
    obtain ⟨rfl, h4⟩ := Prod.mk.inj ((T.nr j.2 i).symm.injective (Subtype.ext (eq_of_heq h2)))
    obtain rfl : d' = d := VertexMove.kind_eq_of_isPicked hpk hd
    obtain rfl := (FL.nearPair d').injective h4
    exact mem_singleton_self _
  · rw [sum_singleton]
    split_ifs <;> simp

/-! ### One stage -/

/-- **The norms of the loads, one stage** ([AnthropicVPVNP2026], Theorem H.2, proof, "One stage",
p. 47): for every `ρ ≥ 0` with `1 + 8 C₁ ≤ ρ² h`, the norm of the loads of the edges of the level
`j + 1` is at most `ρ` times that of the level `j`, plus `√C₁ a₁ / b` for every chamber of the
level `j + 1`, where `C₁` and `a₁` are the contraction and the scale of the laws. -/
theorem norm_load_le (hr : 0 < r) (hb : 0 < b) (hh : 0 < h) (hbD : b ≤ 2 * D) {ρ : ℝ}
    (hρ : 0 ≤ ρ) (hρ1 : 1 + 8 * FL.contraction ≤ ρ ^ 2 * h) (j : Fin J) :
    T.kap (edgeLoads (load lhat n o) (j + 1)) ≤ ρ * T.kap (edgeLoads (load lhat n o) j) +
      √FL.contraction * FL.scale / b * Fintype.card (T.X (j + 1)) := by
  set L := load lhat n o
  have hi := Tower.isChosenType_chosenType hh (edgeLoads L) j
  have hn : edgeLoads L j = fun e => L (.edge j.castSucc e) :=
    funext fun e => edgeLoads_of_lt L (by omega) e
  have hn' : edgeLoads L (j + 1) = fun e => L (.edge j.succ e) :=
    funext fun e => edgeLoads_of_lt L (by omega) e
  have hsel := hi.mul_sum_sq_le
  rw [hn] at hsel
  rw [hn, hn']
  choose _ d₀ _ using fun ω =>
    VertexMove.exists_fits (FL := FL) L j (T.chosenType hh (edgeLoads L) j) ω
  refine Tower.kap_le_of_stage j.2 hr hb hbD FL.contraction_nonneg (Nat.cast_nonneg _) hρ hρ1
    hsel (fun e' he' => load_edge_succ_le hr hb hi he')
    (fun ω => (⟨j, _, ω, d₀ ω⟩ : VertexMove FL).minUnits L) (fun ω => ?_)
    fun ω => VertexMove.scale_mul_minUnits_le L _ fun q => load_segment_le j _ ω q
  obtain ⟨d, hd⟩ := VertexMove.exists_isPicked L (⟨j, _, ω, d₀ ω⟩ : VertexMove FL)
  have h1 : r * b * ∑ c, L (.edge j.succ ((T.nr j.2 _).symm (ω, FL.nearPair d c)).1) ^ 2 ≤
      FL.lengthBound * (⟨j, _, ω, d₀ ω⟩ : VertexMove FL).minUnits L ^ 2 := calc
    _ ≤ r * b * ∑ c, alive lhat n o ⟨.vertex ⟨j, _, ω, d⟩, c⟩ ^ 2 :=
        Nat.mul_le_mul_left _ (sum_le_sum fun c _ =>
          Nat.pow_le_pow_left (load_edge_vertex_le hr hb hi hd c) 2)
    _ ≤ FL.lengthBound * moveCount lhat n o (.vertex ⟨j, _, ω, d⟩) ^ 2 := sum_alive_sq_le _
    _ ≤ _ := by
        gcongr
        exact moveCount_vertex_le _
  rw [(FL.nearPair d).sum_comp (fun ν => L (.edge j.succ ((T.nr j.2 _).symm (ω, ν)).1) ^ 2)] at h1
  have h2 := mul_le_mul_of_nonneg_right FL.lengthBound_le
    (sq_nonneg ((⟨j, _, ω, d₀ ω⟩ : VertexMove FL).minUnits L : ℝ))
  have h3 : (r * b * ∑ ν, (L (.edge j.succ ((T.nr j.2 _).symm (ω, ν)).1) : ℝ) ^ 2) ≤
      FL.lengthBound * ((⟨j, _, ω, d₀ ω⟩ : VertexMove FL).minUnits L : ℝ) ^ 2 := by
    exact_mod_cast h1
  linarith

end Cslib.Circuits.Arithmetic.Separation.TowerPlan
