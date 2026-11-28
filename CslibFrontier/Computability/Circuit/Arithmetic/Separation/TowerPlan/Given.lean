/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.TowerPlan.Counts
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.TowerPlan.Holders
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.TowerPlan.Norms
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.TowerPlan.StartLoads

/-!
# The tower plan: the units given at a node

A move of the tower plan of [AnthropicVPVNP2026] (proof of Theorem H.2; modules `Nc.Tow.Ever1`,
`Nc.Tow.Ever2`, `Nc.Tow.Ever3`) is given its number of units at each of its roles
(`unitsAt`). When the outcomes are good, the relays at a node are given at most `2 m lhat` units
of the start if the node is the chamber of a base party, plus `8` times the units between the
chamber and its parent and `3` times those between its children and the chamber
(`Cslib.CoveringTower.Tower.childUnits`); at the root they are given at most the loads of the last
level. The law moves at a node are given at most the number of kinds of laws times the units
between the chamber and its parent.

The relays of a stage are bounded by the loads of the edges of their way: an inner relay that is
used takes the units of its edge, the four relays of the way of an edge of the chosen type take
at most those units, and the third of them puts them on the edge of the next level over the edge.
The relays of the start are bounded by the batches of the initial units and, on their first
channel, by the loads of the edges of the level `0`. A law move uses at most the units on each of
its channels, which lie on edges at its chambers.

## Main definitions

* `unitsAt`: the units given in a move at a node, once for each of its roles there.

## Main results

* `sum_unitsAt_relay_le`: the units given in the relays at a node.
* `sum_unitsAt_vertex_le`: the units given in the law moves at a node.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Theorem H.2(e), p. 46, and its proof ("For (e)", p. 48); modules `Nc.Tow.Ever1`,
  `Nc.Tow.Ever2`, `Nc.Tow.Ever3`
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.TowerPlan

open Finset Cslib.CoveringTower Cut

variable {F : Type*} [CommSemiring F] {h b D J r m Uu A : ℕ} {T : Tower h b D J r}
  {R : Routes T m Uu} {ch : Fin A ↪ T.X 0} {FL : VertexLaws F T} {lhat : ℕ}
  {n : Fin A → Fin A → ℕ} {o : MoveChannel R ch FL → ℕ} (hh : 0 < h)

variable (lhat n o) in
/-- The units given in the move `mv` at the node `P`: the number of units of the move, once for
each of its roles at `P`. -/
@[expose] noncomputable def unitsAt (P : T.Node) (mv : Move R ch FL) : ℕ :=
  ∑ p, if mv.party p = P then moveCount lhat n o mv else 0

/-! ### Relays -/

/-- The relays carry at most the load of a target on its channels with that target. -/
private theorem sum_relayAlive_le (τ : Target T m A) :
    ∑ x, ∑ d, (if x.target R ch d = τ then relayAlive lhat n o x d else 0) ≤
      load lhat n o τ := by
  rw [load_eq_sum]; omega

/-- The channels of relays whose units lie on edges of the level `j`, with the weights `w` of the
edges. -/
private theorem sum_edge_target_le (j : Fin (J + 1)) (w : T.Ed j → ℕ) :
    ∑ x : Relay T m A, ∑ d, ∑ e, (if x.target R ch d = .edge j e then
      w e * relayAlive lhat n o x d else 0) ≤ ∑ e, w e * edgeLoads (load lhat n o) j e := by
  simp only [← mul_ite_zero]
  rw [sum_congr rfl fun x _ => sum_comm, sum_comm]
  refine sum_le_sum fun e _ => ?_
  simpa only [edgeLoads_of_lt _ j.isLt, ← mul_sum] using Nat.mul_le_mul_left _ (sum_relayAlive_le _)

/-- One channel of a relay whose units lie on an edge of the level `j`. -/
private theorem le_sum_edge_target {x : Relay T m A} {d : Bool} {j : Fin (J + 1)} {e : T.Ed j}
    (h : x.target R ch d = .edge j e) (w : T.Ed j → ℕ) :
    w e * relayAlive lhat n o x d ≤ ∑ d', ∑ e', (if x.target R ch d' = .edge j e' then
      w e' * relayAlive lhat n o x d' else 0) := by
  refine le_trans ?_ (single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ d))
  refine le_trans ?_ (single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ e))
  rw [ite_eq_left h]

/-- The number of ends of an edge of the level `j` at the node `P`. -/
private abbrev endsAt {j : ℕ} (hj : j ≤ J) (P : T.Node) (e : T.Ed j) : ℕ :=
  (if Tower.Node.ofChamber hj (T.e0 e) = P then 1 else 0) +
    if Tower.Node.ofChamber hj (T.e1 e) = P then 1 else 0

private theorem sum_endsAt_mul {j : ℕ} (hj : j ≤ J) (P : T.Node) (L : T.Ed j → ℕ) :
    ∑ e, endsAt hj P e * L e =
      ∑ c, if Tower.Node.ofChamber hj c = P then T.incidentSum L c else 0 := by
  rw [Tower.sum_ite_incidentSum]
  simp only [add_mul, ite_mul, one_mul, zero_mul]

/-- A channel carries at most the load of its target. -/
private theorem alive_le_load (ν : MoveChannel R ch FL) :
    alive lhat n o ν ≤ load lhat n o (ν.1.target ν.2) :=
  le_add_left ((ite_eq_left rfl).symm.trans_le (single_le_sum (f := fun ν' =>
    if ν'.1.target ν'.2 = ν.1.target ν.2 then aliveGiven o ν' (moveCount lhat n o ν'.1)
    else 0) (fun _ _ => Nat.zero_le _) (mem_univ ν)))

/-- With good outcomes, a channel of a relay carries all units of the relay. -/
private theorem relayAlive_eq_moveCount (hg : ∀ mv, GoodOutcome lhat n o mv) {x : Relay T m A}
    (hx : x.Occurs R ch) (d : Bool) :
    relayAlive lhat n o x d = moveCount lhat n o (.relay x hx) := by
  rw [relayAlive_of_occurs hx]
  exact ite_eq_left (hg (.relay x hx) d)

/-- With good outcomes, the second and the fourth step of the way of an edge use at most the
units of the third one. -/
private theorem relayAlive_middle_le_two (hg : ∀ mv, GoodOutcome lhat n o mv) (j : Fin J)
    (e : T.Ed j) {s : Fin 4} (hs : s = 1 ∨ s = 3) :
    relayAlive lhat n o (.middle j e s) false ≤ relayAlive lhat n o (.middle j e 2) false := by
  have h2 : (Relay.middle j e 2 : Relay T m A).Occurs R ch := ⟨nofun, nofun⟩
  by_cases hx : (Relay.middle j e s).Occurs R ch
  · rw [relayAlive_eq_moveCount hg hx, relayAlive_eq_moveCount hg h2]
    rcases hs with rfl | rfl
    · rw [← relayAlive_eq_moveCount hg hx true, relayAlive_of_occurs hx, moveCount_eq,
        countOfLoad, ite_eq_left (by simp [Relay.Active])]
      exact alive_le_load _
    · refine (moveCount_relay_le _ hx).trans ?_
      rw [← relayAlive_eq_moveCount hg h2 true]
      simp only [Relay.input, Fin.reduceEq, ↓reduceIte]
      refine (load_le_relayAlive (fun _ _ => by simp [Move.target]) (.middle j e 2) true
        fun x d h _ => ?_).trans_eq ?_
      · obtain ⟨rfl, h' | h' | h'⟩ := Relay.of_target_eq_relay_middle h
        exacts [absurd h'.1 (by decide), absurd h'.1 (by decide), ⟨h'.2, rfl⟩]
      · rw [initialLoad_eq_zero (by simp) (by simp only [Target.time, Relay.time]; omega),
          zero_add]
  · exact (relayAlive_of_not_occurs hx _).trans_le (Nat.zero_le _)

variable (lhat n o) in
/-- The units of the channel `false` of a relay, once for each of its roles at the node `P`. -/
private noncomputable def relayAt (P : T.Node) (x : Relay T m A) : ℕ :=
  ∑ q, if x.party R ch q = P then relayAlive lhat n o x false else 0

/-- The relays of the start: at most `2 m lhat` units at the chamber of a base party as the last
node of the routes, and on their first channels the loads of the edges of the level `0`. -/
private theorem start_le (P : T.Node) :
    ∑ a, ∑ c, ∑ γ, ∑ s, relayAt lhat n o P (.start a c γ s) ≤
      (if ∃ a, Tower.Node.ofChamber (Nat.zero_le J) (ch a) = P then 2 * m * lhat else 0) +
        ∑ c : T.X 0, if Tower.Node.ofChamber (Nat.zero_le J) c = P then
          T.parentUnits (edgeLoads (load lhat n o)) 0 c else 0 := by
  -- the units of a batch at the last node of its route
  have hsink (c : Fin A) :
      ∑ a, ∑ γ, ∑ s, relayAlive lhat n o (.start a c γ s : Relay T m A) false ≤
        2 * m * lhat := calc
    _ ≤ ∑ a, ∑ γ, ∑ _s : Fin (2 * m), if a = c then 0 else batchSize ch lhat n a c γ := by
        gcongr with a _ γ _ s _
        by_cases hx : (Relay.start a c γ s).Occurs R ch
        · rw [ite_eq_right hx.1]
          exact (relayAlive_of_occurs hx _).trans_le
            ((alive_le_moveCount _ hx _).trans (moveCount_start_le hx))
        · exact (relayAlive_of_not_occurs hx _).trans_le (Nat.zero_le _)
    _ = ∑ a, 2 * m * (if a = c then 0 else ∑ γ, batchSize ch lhat n a c γ) := by
        refine sum_congr rfl fun a _ => ?_
        split_ifs <;> simp [mul_sum]
    _ ≤ 2 * m * lhat := by
        rw [← mul_sum]
        gcongr
        by_cases hv : InitialBound lhat n
        · refine (sum_le_sum fun a _ => ?_).trans (hv c)
          simp only [batchSize, hv, ↓reduceIte]
          rw [← card_eq_sum_card_fiberwise fun k _ => mem_univ (batchChamber ch a k), card_range]
          split_ifs <;> omega
        · simp [batchSize, hv]
  -- the first two roles are the ends of the first channel, on an edge of the level `0`
  have hsplit (a c γ s) : relayAt lhat n o P (.start a c γ s) ≤
      (if Tower.Node.ofChamber (Nat.zero_le J) (ch c) = P then
        relayAlive lhat n o (.start a c γ s) false else 0) +
      ∑ d, ∑ e : T.Ed 0, (if (Relay.start a c γ s).target R ch d = .edge 0 e then
        endsAt (Nat.zero_le J) P e * relayAlive lhat n o (.start a c γ s) d else 0) := by
    by_cases hx : (Relay.start a c γ s).Occurs R ch
    · obtain ⟨e, h1, h2, -⟩ := R.exists_edge (ch a) (ch c) γ (s := s) (by have := hx.2; omega)
      refine le_trans ?_ (Nat.add_le_add_left (le_sum_edge_target (lhat := lhat) (n := n)
        (o := o) (x := .start a c γ s) (d := false) (j := 0) (e := e)
        (by simp [Relay.target, stepTarget, h1, Option.elim]) _) _)
      simp only [relayAt, RelayRole.sum_univ, endsAt, add_mul, ite_mul, one_mul, zero_mul,
        Relay.party, RelayRole.elim]
      rcases Sym2.eq_iff.1 h2 with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> rw [h3, h4] <;> grind
    · simp [relayAt, relayAlive_of_not_occurs hx]
  refine (sum_le_sum fun a _ => sum_le_sum fun c _ => sum_le_sum fun γ _ => sum_le_sum fun s _ =>
    hsplit a c γ s).trans ?_
  simp only [sum_add_distrib]
  gcongr ?_ + ?_
  · rw [sum_comm]
    simp only [← ite_sum_zero]
    split_ifs with hP
    · obtain ⟨a₀, rfl⟩ := hP
      rw [Fintype.sum_eq_single a₀ fun c hc => ite_eq_right fun h =>
        hc (ch.injective (Tower.Node.ofChamber_inj.1 h)), ite_eq_left rfl]
      exact hsink a₀
    · exact (sum_eq_zero fun c _ => ite_eq_right fun h => hP ⟨c, h⟩).le
  · refine le_trans ?_ ((sum_edge_target_le 0 (endsAt (Nat.zero_le J) P)).trans_eq
      (sum_endsAt_mul _ P _))
    rw [Relay.sum_eq]
    exact le_self_add

/-- The inner relays of an edge: at its ends, and at the parent of its first end. -/
private theorem inner_le (P : T.Node) (j : Fin J) (e : T.Ed j) :
    ∑ i, relayAt lhat n o P (.inner j i e) ≤
      ((if Tower.Node.ofChamber j.isLt.le (T.e0 e) = P then edgeLoads (load lhat n o) j e else 0) +
        if Tower.Node.ofChamber j.isLt.le (T.e1 e) = P then edgeLoads (load lhat n o) j e else 0) +
      ((if Tower.Node.ofChamber j.isLt (T.parentChamber hh (edgeLoads (load lhat n o)) (T.e0 e)) = P
          then edgeLoads (load lhat n o) j e else 0) +
        if Tower.Node.ofChamber j.isLt (T.parentChamber hh (edgeLoads (load lhat n o)) (T.e1 e)) = P
          then edgeLoads (load lhat n o) j e else 0) := by
  rw [sum_eq_single (T.chosenType hh (edgeLoads (load lhat n o)) j) (fun i _ hi => ?_) (by simp)]
  · have h1 := (relayAlive_inner_le (lhat := lhat) (n := n) (o := o) (R := R) (ch := ch) j _ e
      false).trans_eq (ite_eq_left (Tower.isChosenType_chosenType hh _ j))
    simp only [relayAt, RelayRole.sum_univ, Relay.party, RelayRole.elim, Tower.parentChamber]
    grind
  · have h1 := (relayAlive_inner_le (lhat := lhat) (n := n) (o := o) (R := R) (ch := ch) j i e
      false).trans_eq (ite_eq_right fun h => hi ((Tower.isChosenType_iff hh).1 h))
    simp [relayAt, Nat.eq_zero_of_le_zero h1]

/-- The relays of the way of an edge of the chosen type: at its ends, at the parents of its ends,
and at the images of its ends with the units of the third step. -/
private theorem middle_le (hg : ∀ mv, GoodOutcome lhat n o mv) (P : T.Node) (j : Fin J)
    (e : T.Ed j) : ∑ s, relayAt lhat n o P (.middle j e s) ≤
      4 * ((if Tower.Node.ofChamber j.isLt.le (T.e0 e) = P then edgeLoads (load lhat n o) j e
          else 0) +
        if Tower.Node.ofChamber j.isLt.le (T.e1 e) = P then edgeLoads (load lhat n o) j e else 0) +
      2 * ((if Tower.Node.ofChamber j.isLt
            (T.parentChamber hh (edgeLoads (load lhat n o)) (T.e0 e)) = P then
          edgeLoads (load lhat n o) j e else 0) +
        if Tower.Node.ofChamber j.isLt
            (T.parentChamber hh (edgeLoads (load lhat n o)) (T.e1 e)) = P then
          edgeLoads (load lhat n o) j e else 0) +
      2 * ((if Tower.Node.ofChamber j.isLt (T.π (T.e0 e)) = P then
          relayAlive lhat n o (.middle j e 2) false else 0) +
        if Tower.Node.ofChamber j.isLt (T.π (T.e1 e)) = P then
          relayAlive lhat n o (.middle j e 2) false else 0) := by
  have hM (s) := relayAlive_middle_le (lhat := lhat) (n := n) (o := o) (R := R) (ch := ch) j e s
    false
  have h1 := relayAlive_middle_le_two hg j e (s := 1) (by decide)
  have h3 := relayAlive_middle_le_two hg j e (s := 3) (by decide)
  simp only [Fin.sum_univ_four, relayAt, RelayRole.sum_univ, Relay.party, RelayRole.elim,
    Tower.parentChamber, Matrix.cons_val]
  by_cases ht : T.IsChosenType (edgeLoads (load lhat n o) j) (T.ty e)
  · simp only [ht, ↓reduceIte] at hM
    simp only [(Tower.isChosenType_iff hh).1 ht]; grind
  · simp only [ht, ↓reduceIte, Nat.le_zero] at hM
    simp [hM]

/-- The relays of the third step put the units of the edges of the chosen type on the edges of
the next level: at the images of the ends of the edges, at most the units between the chambers of
the next level and their parents. -/
private theorem images_le (P : T.Node) (j : Fin J) :
    ∑ e : T.Ed j, ((if Tower.Node.ofChamber j.isLt (T.π (T.e0 e)) = P then
        relayAlive lhat n o (.middle j e 2) false else 0) +
      if Tower.Node.ofChamber j.isLt (T.π (T.e1 e)) = P then
        relayAlive lhat n o (.middle j e 2) false else 0) ≤
      ∑ c : T.X (j + 1), if Tower.Node.ofChamber j.isLt c = P then
        T.parentUnits (edgeLoads (load lhat n o)) (j + 1) c else 0 := by
  refine le_trans ?_ ((sum_edge_target_le (lhat := lhat) (n := n) (o := o) (R := R) (ch := ch)
    j.succ (endsAt j.isLt P)).trans_eq (sum_endsAt_mul _ P _))
  refine sum_le_sum_of_injOn (fun e => Relay.middle j e 2) (fun e _ e' _ he => by cases he; rfl)
    (subset_univ _) (fun e _ => le_trans (le_of_eq ?_) (le_sum_edge_target (d := false)
      (j := j.succ) (e := T.πE e) rfl _)) fun _ _ _ => Nat.zero_le _
  simp only [endsAt, add_mul, ite_mul, one_mul, zero_mul]
  exact (Sym2.eq_iff.1 (T.π_ends j.isLt e)).elim (fun ⟨h3, h4⟩ => by rw [h3, h4])
    fun ⟨h3, h4⟩ => by rw [h3, h4, add_comm]

/-- The relays after the last stage: at the ends of an edge of the last level, and at the root. -/
private theorem final_le (P : T.Node) (e : T.Ed J) :
    relayAt lhat n o P (.final e) ≤
      ((if Tower.Node.ofChamber le_rfl (T.e0 e) = P then edgeLoads (load lhat n o) J e else 0) +
        if Tower.Node.ofChamber le_rfl (T.e1 e) = P then edgeLoads (load lhat n o) J e else 0) +
      if Tower.Node.root = P then edgeLoads (load lhat n o) J e else 0 := by
  have h1 := relayAlive_final_le (lhat := lhat) (n := n) (o := o) (R := R) (ch := ch) e false
  simp only [relayAt, RelayRole.sum_univ, Relay.party, RelayRole.elim]
  grind

/-- **The units given in the relays at a node**, for good outcomes: at most `2 m lhat` at the
chamber of a base party, and at most `8` times the units between a chamber and its parent and `3`
times those between its children and the chamber; at the root, at most the loads of the last
level. -/
theorem sum_unitsAt_relay_le (hg : ∀ mv, GoodOutcome lhat n o mv) (P : T.Node) :
    ∑ x, (if hx : x.Occurs R ch then unitsAt lhat n o P (.relay x hx) else 0) ≤
      (if ∃ a, Tower.Node.ofChamber (Nat.zero_le J) (ch a) = P then 2 * m * lhat else 0) +
        P.lift (fun j c => 8 * T.parentUnits (edgeLoads (load lhat n o)) j c +
          3 * T.childUnits hh (edgeLoads (load lhat n o)) j c)
          (∑ e, edgeLoads (load lhat n o) J e) := by
  have h0 : (∑ x, if hx : x.Occurs R ch then unitsAt lhat n o P (.relay x hx) else 0) =
      ∑ x, relayAt lhat n o P x := sum_congr rfl fun x _ => by
    by_cases hx : x.Occurs R ch
    · simp only [hx, ↓reduceDIte, unitsAt, relayAt, relayAlive_eq_moveCount hg hx]; rfl
    · simp [hx, relayAt, relayAlive_of_not_occurs hx]
  have hI : ∑ j, ∑ i, ∑ e, relayAt lhat n o P (.inner j i e) ≤ ∑ j : Fin J,
      ((∑ c : T.X j, if Tower.Node.ofChamber j.isLt.le c = P then
        T.parentUnits (edgeLoads (load lhat n o)) j c else 0) +
      ∑ c : T.X (j + 1), if Tower.Node.ofChamber j.isLt c = P then
        T.childUnits hh (edgeLoads (load lhat n o)) (j + 1) c else 0) :=
    sum_le_sum fun j _ => sum_comm.trans_le ((sum_le_sum fun e _ => inner_le hh P j e).trans_eq
      (by rw [Tower.sum_ite_childUnits, Tower.sum_ite_incidentSum, Tower.sum_ite_incidentSum,
        sum_add_distrib]))
  have hM : ∑ j, ∑ e, ∑ s, relayAt lhat n o P (.middle j e s) ≤ ∑ j : Fin J,
      (4 * (∑ c : T.X j, if Tower.Node.ofChamber j.isLt.le c = P then
        T.parentUnits (edgeLoads (load lhat n o)) j c else 0) +
      2 * (∑ c : T.X (j + 1), if Tower.Node.ofChamber j.isLt c = P then
        T.childUnits hh (edgeLoads (load lhat n o)) (j + 1) c else 0) +
      2 * ∑ c : T.X (j + 1), if Tower.Node.ofChamber j.isLt c = P then
        T.parentUnits (edgeLoads (load lhat n o)) (j + 1) c else 0) :=
    sum_le_sum fun j _ => (sum_le_sum fun e _ => middle_le hh hg P j e).trans (by
      rw [Tower.sum_ite_childUnits, Tower.sum_ite_incidentSum, Tower.sum_ite_incidentSum]
      simp only [sum_add_distrib, ← mul_sum]
      have := sum_add_distrib.symm.trans_le
        (images_le (lhat := lhat) (n := n) (o := o) (R := R) (ch := ch) P j)
      omega)
  have hF : ∑ e, relayAt lhat n o P (.final e) ≤
      (∑ c : T.X J, if Tower.Node.ofChamber le_rfl c = P then
        T.parentUnits (edgeLoads (load lhat n o)) J c else 0) +
      if Tower.Node.root = P then ∑ e, edgeLoads (load lhat n o) J e else 0 :=
    (sum_le_sum fun e _ => final_le P e).trans_eq (by
      rw [Tower.sum_ite_incidentSum, sum_add_distrib, ite_sum_zero])
  have hA := Tower.Node.sum_ofChamber_castSucc (T.parentUnits (edgeLoads (load lhat n o))) P
  have hB := Tower.Node.sum_ofChamber_succ (T.parentUnits (edgeLoads (load lhat n o))) P
  have hC := Tower.Node.sum_ofChamber_succ (T.childUnits hh (edgeLoads (load lhat n o))) P
  have hS := start_le (lhat := lhat) (n := n) (o := o) (R := R) (ch := ch) P
  have hL : P.lift (fun j c => 8 * T.parentUnits (edgeLoads (load lhat n o)) j c +
      3 * T.childUnits hh (edgeLoads (load lhat n o)) j c) (∑ e, edgeLoads (load lhat n o) J e) =
      8 * P.lift (T.parentUnits (edgeLoads (load lhat n o))) 0 +
      3 * P.lift (T.childUnits hh (edgeLoads (load lhat n o))) 0 +
      if Tower.Node.root = P then ∑ e, edgeLoads (load lhat n o) J e else 0 := by
    cases P <;> simp [Tower.Node.lift]
  simp only [sum_add_distrib, ← mul_sum] at hI hM
  rw [sum_eq_zero fun _ _ => by simp [Tower.childUnits], zero_add] at hC
  rw [h0, Relay.sum_eq, hL]; omega

/-! ### Law moves -/

/-- The units on the edge of a channel are at most the units between each end of the channel and
its parent. -/
private theorem load_edge_le_lift {ν : MoveChannel R ch FL} {j : Fin (J + 1)} {e : T.Ed j}
    (hν : ν.1.target ν.2 = .edge j e) (b : Bool) :
    load lhat n o (.edge j e) ≤ Tower.Node.lift (T.parentUnits (edgeLoads (load lhat n o))) 0
      (ν.1.party (ν.1.law.channelEnd ν.2 b)) := by
  have h1 := holders_target ν (by simp [hν])
  have h2 : ν.1.party (ν.1.law.channelEnd ν.2 b) ∈ channelHolders ν := by
    cases b <;> simp [channelHolders]
  rw [← h1, hν, Target.holders, Sym2.mem_iff] at h2
  refine (edgeLoads_of_lt _ j.isLt e).symm.trans_le ?_
  rcases h2 with h2 | h2 <;> rw [h2, Tower.Node.lift_ofChamber] <;>
    exact single_le_sum (fun _ _ => Nat.zero_le _) (mem_filter.2 ⟨mem_univ _, by simp⟩)

/-- With good outcomes, a law move uses at most the units between each of its chambers and the
parent. -/
private theorem moveCount_vertex_le_lift (hg : ∀ mv, GoodOutcome lhat n o mv)
    (hnr : ∀ f : T.Fl, ∃ ν, T.cN ν = f ∨ T.dN ν = f) (l : VertexMove FL)
    (p : (FL.law l.kind).Role) : moveCount lhat n o (.vertex l) ≤
      Tower.Node.lift (T.parentUnits (edgeLoads (load lhat n o))) 0
        ((Move.vertex l : Move R ch FL).party p) := by
  obtain ⟨ν, b, rfl⟩ := FL.exists_channelEnd hnr l.kind p
  obtain ⟨hs, hc⟩ := hg (.vertex l)
  exact (hc ν).trans ((ite_eq_left hs).symm.trans_le ((alive_le_load ⟨.vertex l, ν⟩).trans
    (load_edge_le_lift (ν := ⟨.vertex l, ν⟩) rfl b)))

/-- **The units given in the law moves at a node**, for good outcomes and if every place is an
end of a near pair: at most the number of kinds of laws times the units between the chamber and
its parent. -/
theorem sum_unitsAt_vertex_le (hg : ∀ mv, GoodOutcome lhat n o mv)
    (hnr : ∀ f : T.Fl, ∃ ν, T.cN ν = f ∨ T.dN ν = f) (P : T.Node) :
    ∑ l : VertexMove FL, unitsAt lhat n o P (.vertex l) ≤
      Fintype.card FL.Kind * P.lift (T.parentUnits (edgeLoads (load lhat n o))) 0 := by
  set V := P.lift (T.parentUnits (edgeLoads (load lhat n o))) 0
  have h1 (l : VertexMove FL) : unitsAt lhat n o P (.vertex l) ≤
      if T.IsChosenType (edgeLoads (load lhat n o) l.stage) l.type then
        ∑ p, if (Move.vertex l : Move R ch FL).party p = P then V else 0 else 0 := by
    split_ifs with hi
    · refine sum_le_sum fun p _ => ?_
      split_ifs with hp
      · simpa only [hp, V] using moveCount_vertex_le_lift hg hnr l p
      · exact le_rfl
    · simp [unitsAt, moveCount_vertex_eq_zero (.inl hi)]
  have h2 (j : Fin J) (i : Fin h) (d : FL.Kind) :
      ∑ ω, ∑ p : (FL.law d).Role, (if Tower.Node.ofChamber j.isLt ((T.chamberEquiv j.isLt i).symm
        (ω, FL.place d p)) = P then V else 0) =
        ∑ c : T.X (j + 1), if Tower.Node.ofChamber j.isLt c = P then V else 0 := by
    rw [← Fintype.sum_prod_type']
    exact (((Equiv.refl _).prodCongr (FL.place d)).sum_comp fun y =>
      if Tower.Node.ofChamber j.isLt ((T.chamberEquiv j.isLt i).symm y) = P then V else 0).trans
      ((T.chamberEquiv j.isLt i).symm.sum_comp fun c =>
        if Tower.Node.ofChamber j.isLt c = P then V else 0)
  have h3 (j : Fin J) : ∑ i, ∑ ω, ∑ d, (if T.IsChosenType (edgeLoads (load lhat n o) j) i then
      ∑ p : (FL.law d).Role, (if Tower.Node.ofChamber j.isLt ((T.chamberEquiv j.isLt i).symm
        (ω, FL.place d p)) = P then V else 0) else 0) ≤
      Fintype.card FL.Kind *
        ∑ c : T.X (j + 1), if Tower.Node.ofChamber j.isLt c = P then V else 0 := calc
    _ = ∑ i, if T.IsChosenType (edgeLoads (load lhat n o) j) i then Fintype.card FL.Kind *
        ∑ c : T.X (j + 1), (if Tower.Node.ofChamber j.isLt c = P then V else 0) else 0 :=
      sum_congr rfl fun i _ => by
        split_ifs with hi
        · rw [sum_comm]
          simp [h2]
        · simp
    _ ≤ _ := by
      rw [← sum_filter, sum_const, smul_eq_mul]
      exact (Nat.mul_le_mul_right _ (card_le_one.2 fun a ha b hb =>
        (mem_filter.1 ha).2.unique (mem_filter.1 hb).2)).trans_eq (one_mul _)
  have h4 := Tower.Node.sum_ofChamber_succ (fun _ _ => V) P
  have h5 : P.lift (fun _ _ => V) 0 ≤ V := by cases P <;> simp [Tower.Node.lift, V]
  refine (VertexMove.sum_eq _).trans_le ((sum_le_sum fun j _ => (sum_le_sum fun i _ =>
    sum_le_sum fun ω _ => sum_le_sum fun d _ => h1 ⟨j, i, ω, d⟩).trans (h3 j)).trans ?_)
  rw [← mul_sum]
  exact Nat.mul_le_mul_left _ (by omega)

end Cslib.Circuits.Arithmetic.Separation.TowerPlan
