/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.SemiUnbounded
public import CslibFrontier.Computability.Circuit.Boolean.SemiUnbounded.MinIsolation
public import Mathlib.Logic.Equiv.Fin.Basic

import CslibFrontier.Foundations.Data.Nat.Log
import Mathlib.Tactic.Ring

/-!
# Balanced-depth normal-form semi-unbounded circuits for realizability trees

Given a finite vertex type `V` equipped with height-preserving transitions `stay : V → V → Prop`
and matched push-pop transitions `pushPop : V → V → V → V → Prop`, a *realizability tree*
(`RealTree stay pushPop u v`) is a derivation tree whose nodes are leaves (`refl` / `stay`),
unary `pushPop` wrappers, or binary sequential compositions (`trans`).

Naive dynamic programming on realizable pairs `(u, v)` has linear depth in the tree size on deeply
nested `pushPop` chains. Following the balanced tree-contraction / suspended-pair construction of
Ruzzo (1980) and Venkateswaran (1991) (informal attribution; locator not verified against primary
PDF), this module maintains alternating OR/AND layers computing both:

* **realizable pairs** `orP r u v`, and
* **one-hole realizability contexts** `orQ r u v x y` (derivations of `(u, v)` missing one
  descendant subtree `(x, y)`),

combined in `R` rounds (`2 * R + 4` layers). Every three rounds increase the covered tree and
context size by a factor of at least `3 / 2` (`growthBound k`, satisfying
`2 ^ j ≤ growthBound (2 * j)`), so `roundsForSize sz = 6 * (Nat.log2 sz + 1)` rounds suffice for
every realizability tree of size at most `sz` (`balancedCircuit_eval_output_complete`).

Crucially, the circuit is in strict alternating AND-first-layer normal form
(`LayeredSemiUnboundedCircuit.InNormalForm`): layer `0` has a single true leaf, layer `1` has a
single unary AND buffer above it, even layers `2 * r + 2` are OR gates, odd layers `2 * r + 3` are
binary AND gates, layer `2 * R + 3` holds unary AND buffers for accepting endpoints, and layer
`2 * R + 4` is the single output OR gate. Reindexing along a computable mixed-radix bijection
`balancedGateEquivFin` transports the circuit onto `Fin (balancedGateCount S R)` while preserving
`InNormalForm`, `Eval`, `andLevel`, and `isAndGate`.

This is original library formalization for Work Package 4 of cslib-frontier #7920.

## Main definitions

* `Cslib.Circuits.Boolean.LayeredSemiUnboundedCircuit.reindex`: transport a circuit along a gate
  bijection `G ≃ G'`.
* `Cslib.Circuits.Boolean.RealTree`: derivation trees for matched push-pop and sequential
  realizability, with node count `RealTree.size`.
* `Cslib.Circuits.Boolean.BalancedGate`, `Cslib.Circuits.Boolean.balancedCircuit`: alternating
  normal-form semi-unbounded circuit over `BalancedGate V R`.
* `Cslib.Circuits.Boolean.roundsForSize`, `Cslib.Circuits.Boolean.balancedGateCount`,
  `Cslib.Circuits.Boolean.balancedGateEquivFin`, `Cslib.Circuits.Boolean.balancedCircuitFin`,
  `Cslib.Circuits.Boolean.balancedOutputGate`: computable `Fin N`-indexed circuit.

## Main results

* `Cslib.Circuits.Boolean.LayeredSemiUnboundedCircuit.reindex_inNormalForm`,
  `Cslib.Circuits.Boolean.LayeredSemiUnboundedCircuit.reindex_eval_iff`: reindexing preserves
  normal form and gate evaluation.
* `Cslib.Circuits.Boolean.balancedCircuit_inNormalForm`,
  `Cslib.Circuits.Boolean.balancedCircuit_andLevel_le`: normal-form and `R + 2` AND-level bounds.
* `Cslib.Circuits.Boolean.balancedCircuit_eval_output_sound`,
  `Cslib.Circuits.Boolean.balancedCircuit_eval_output_complete`: soundness at every `R` and
  completeness at `R ≥ roundsForSize sz`.
* `Cslib.Circuits.Boolean.balancedCircuitFin_inNormalForm`,
  `Cslib.Circuits.Boolean.balancedCircuitFin_eval_output_sound`,
  `Cslib.Circuits.Boolean.balancedCircuitFin_eval_output_complete`: `Fin N`-indexed counterparts.
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

/-! ### Circuit reindexing along a gate bijection -/

/-- Map the child gate references of an `AndInputs` along a function. -/
def AndInputs.map {G G' : Type*} (f : G → G') : AndInputs G → AndInputs G'
  | .unary c => .unary (f c)
  | .binary l r => .binary (f l) (f r)

/-- Map the child gate references of a `GateKind` along a function. -/
def GateKind.map {G G' : Type*} (f : G → G') : GateKind G → GateKind G'
  | .leaf b => .leaf b
  | .and inp => .and (inp.map f)
  | .or => .or

namespace LayeredSemiUnboundedCircuit

variable {G G' : Type*}

/-- Transport a layered semi-unbounded circuit along a bijection `e : G ≃ G'` of gate sets. -/
def reindex (C : LayeredSemiUnboundedCircuit G) (e : G ≃ G') :
    LayeredSemiUnboundedCircuit G' where
  layer g' := C.layer (e.symm g')
  kind g' := (C.kind (e.symm g')).map e
  orChild g' c' := C.orChild (e.symm g') (e.symm c')
  layer_andUnary {g' c'} h := by
    cases hk : C.kind (e.symm g') with
    | leaf _ | or => simp [GateKind.map, hk] at h
    | and inp =>
      cases inp with
      | unary c =>
        simp only [GateKind.map, AndInputs.map, hk, GateKind.and.injEq,
          AndInputs.unary.injEq] at h
        subst h
        simpa only [Equiv.symm_apply_apply] using C.layer_andUnary hk
      | binary _ _ => simp [GateKind.map, AndInputs.map, hk] at h
  layer_andBinary {g' l' r'} h := by
    cases hk : C.kind (e.symm g') with
    | leaf _ | or => simp [GateKind.map, hk] at h
    | and inp =>
      cases inp with
      | unary _ => simp [GateKind.map, AndInputs.map, hk] at h
      | binary l r =>
        simp only [GateKind.map, AndInputs.map, hk, GateKind.and.injEq,
          AndInputs.binary.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simpa only [Equiv.symm_apply_apply] using C.layer_andBinary hk
  layer_orChild {g' c'} h hch := by
    cases hk : C.kind (e.symm g') with
    | leaf _ | and _ => simp [GateKind.map, hk] at h
    | or => exact C.layer_orChild hk hch

instance instDecidableOrChildReindex (C : LayeredSemiUnboundedCircuit G) (e : G ≃ G')
    [DecidableRel C.orChild] : DecidableRel (C.reindex e).orChild := fun g' c' =>
  show Decidable (C.orChild (e.symm g') (e.symm c')) from inferInstance

@[simp]
theorem reindex_layer (C : LayeredSemiUnboundedCircuit G) (e : G ≃ G') (g : G) :
    (C.reindex e).layer (e g) = C.layer g := by
  simp [reindex]

@[simp]
theorem reindex_andLevel (C : LayeredSemiUnboundedCircuit G) (e : G ≃ G') (g : G) :
    (C.reindex e).andLevel (e g) = C.andLevel g := by
  simp [andLevel, reindex]

theorem reindex_inNormalForm {C : LayeredSemiUnboundedCircuit G} (h : C.InNormalForm)
    (e : G ≃ G') : (C.reindex e).InNormalForm where
  leaf_of_layer_zero h0 :=
    let ⟨b, hb⟩ := h.leaf_of_layer_zero h0; ⟨b, by simp [reindex, hb, GateKind.map]⟩
  and_of_odd hodd :=
    let ⟨inp, hinp⟩ := h.and_of_odd hodd; ⟨inp.map e, by simp [reindex, hinp, GateKind.map]⟩
  or_of_pos_even hpos heven := by simp [reindex, h.or_of_pos_even hpos heven, GateKind.map]

/-- Reindexing along a bijection preserves Boolean gate evaluation at every gate. -/
theorem reindex_eval_iff (C : LayeredSemiUnboundedCircuit G) (e : G ≃ G') (g : G) :
    (C.reindex e).Eval (e g) ↔ C.Eval g := by
  suffices h : ∀ n g, C.layer g = n → ((C.reindex e).Eval (e g) ↔ C.Eval g) from h _ g rfl
  intro n; induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro g hn; subst hn
    match hk : C.kind g with
    | .leaf b =>
      rw [(C.reindex e).eval_leaf (show (C.reindex e).kind (e g) = .leaf b by
        simp [reindex, hk, GateKind.map]), C.eval_leaf hk]
    | .and (.unary c) =>
      rw [(C.reindex e).eval_andUnary (show (C.reindex e).kind (e g) = .and (.unary (e c)) by
        simp [reindex, hk, GateKind.map, AndInputs.map]), C.eval_andUnary hk]
      have := C.layer_andUnary hk; exact ih _ (by omega) c rfl
    | .and (.binary l r) =>
      rw [(C.reindex e).eval_andBinary (show (C.reindex e).kind (e g) = .and (.binary (e l) (e r))
        by simp [reindex, hk, GateKind.map, AndInputs.map]), C.eval_andBinary hk]
      have := C.layer_andBinary hk; exact and_congr (ih _ (by omega) l rfl) (ih _ (by omega) r rfl)
    | .or =>
      rw [(C.reindex e).eval_or (by simp [reindex, hk, GateKind.map]), C.eval_or hk]
      refine ⟨fun ⟨c', hch', hev'⟩ => ?_, fun ⟨c, hch, hev⟩ => ?_⟩
      · have hch : C.orChild g (e.symm c') := by simpa [reindex] using hch'
        have := C.layer_orChild hk hch
        exact ⟨e.symm c', hch, (ih _ (by omega) _ rfl).mp (by simpa using hev')⟩
      · have := C.layer_orChild hk hch
        exact ⟨e c, by simpa [reindex] using hch, (ih _ (by omega) c rfl).mpr hev⟩

end LayeredSemiUnboundedCircuit

/-! ### Realizability trees, one-hole contexts, and balanced splitting -/

/-- A derivation tree for same-height realizability between vertices `u` and `v`: leaves (`refl`
or `stay`), unary matched `pushPop` steps, and binary sequential compositions (`trans`). -/
inductive RealTree {V : Type*} (stay : V → V → Prop) (pushPop : V → V → V → V → Prop) :
    V → V → Type _ where
  /-- Zero-step reflexivity leaf. -/
  | refl (u : V) : RealTree stay pushPop u u
  /-- Single height-preserving step leaf. -/
  | stay {u v : V} (h : stay u v) : RealTree stay pushPop u v
  /-- Matched push-pop wrapper around a sub-derivation. -/
  | pushPop {u u' v' v : V} (h : pushPop u u' v' v) (sub : RealTree stay pushPop u' v') :
      RealTree stay pushPop u v
  /-- Sequential composition of two sub-derivations at an intermediate vertex `w`. -/
  | trans {u w v : V} (left : RealTree stay pushPop u w) (right : RealTree stay pushPop w v) :
      RealTree stay pushPop u v

namespace RealTree

variable {V : Type*} {stay : V → V → Prop} {pushPop : V → V → V → V → Prop}

/-- Number of nodes in a realizability derivation tree (always at least `1`). -/
def size : {u v : V} → RealTree stay pushPop u v → ℕ
  | _, _, .refl _ => 1
  | _, _, .stay _ => 1
  | _, _, .pushPop _ sub => 1 + sub.size
  | _, _, .trans l r => 1 + l.size + r.size

lemma size_pos {u v : V} (T : RealTree stay pushPop u v) : 0 < T.size := by
  cases T <;> simp [size]

end RealTree

/-- A one-hole spine context from root `(u, v)` down to a single descendant hole `(x, y)`. -/
private inductive RealCtx {V : Type*} (stay : V → V → Prop) (pushPop : V → V → V → V → Prop) :
    V → V → V → V → Type _ where
  | hole (x y : V) : RealCtx stay pushPop x y x y
  | pushPop {u u' v' v x y : V} (h : pushPop u u' v' v)
      (rest : RealCtx stay pushPop u' v' x y) : RealCtx stay pushPop u v x y
  | transLeft {u w v x y : V} (left : RealTree stay pushPop u w)
      (rest : RealCtx stay pushPop w v x y) : RealCtx stay pushPop u v x y
  | transRight {u w v x y : V} (rest : RealCtx stay pushPop u w x y)
      (right : RealTree stay pushPop w v) : RealCtx stay pushPop u v x y

private def RealCtx.size {V : Type*} {stay : V → V → Prop} {pushPop : V → V → V → V → Prop} :
    {u v x y : V} → RealCtx stay pushPop u v x y → ℕ
  | _, _, _, _, .hole _ _ => 0
  | _, _, _, _, .pushPop _ rest => 1 + rest.size
  | _, _, _, _, .transLeft l rest => 1 + l.size + rest.size
  | _, _, _, _, .transRight rest r => 1 + rest.size + r.size

/-- Centroid splitting for a realizability tree: any tree strictly larger than `M ≥ 1` decomposes
into a subtree of size in `[(M + 1) / 2, M]` plugged into a one-hole context of the remaining
size. -/
private lemma realTree_split_le {V : Type*} {stay : V → V → Prop}
    {pushPop : V → V → V → V → Prop} {u v : V} (T : RealTree stay pushPop u v)
    {M : ℕ} (hM : 1 ≤ M) (hgt : M < T.size) :
    ∃ (x y : V), Nonempty (RealCtx stay pushPop u v x y) ∧
      ∃ (C : RealCtx stay pushPop u v x y) (sub : RealTree stay pushPop x y),
        sub.size ≤ M ∧ (M + 1) / 2 ≤ sub.size ∧ C.size + sub.size = T.size := by
  induction T with
  | refl _ | stay _ => simp [RealTree.size] at hgt; omega
  | @pushPop u u' v' v h sub ih =>
    simp only [RealTree.size] at hgt
    by_cases hsub : M < sub.size
    · obtain ⟨x, y, -, C, sub', hle, hge, hsum⟩ := ih hsub
      exact ⟨x, y, ⟨.pushPop h C⟩, .pushPop h C, sub', hle, hge,
        by simp only [RealCtx.size, RealTree.size]; omega⟩
    · exact ⟨u', v', ⟨.pushPop h (.hole u' v')⟩, .pushPop h (.hole u' v'), sub, by omega,
        by omega, by simp [RealCtx.size, RealTree.size]⟩
  | @trans u w v l r ihl ihr =>
    simp only [RealTree.size] at hgt
    by_cases hl : M < l.size
    · obtain ⟨x, y, -, C, sub', hle, hge, hsum⟩ := ihl hl
      exact ⟨x, y, ⟨.transRight C r⟩, .transRight C r, sub', hle, hge,
        by simp only [RealCtx.size, RealTree.size]; omega⟩
    · by_cases hr : M < r.size
      · obtain ⟨x, y, -, C, sub', hle, hge, hsum⟩ := ihr hr
        exact ⟨x, y, ⟨.transLeft l C⟩, .transLeft l C, sub', hle, hge,
          by simp only [RealCtx.size, RealTree.size]; omega⟩
      · by_cases hgeL : (M + 1) / 2 ≤ l.size
        · exact ⟨u, w, ⟨.transRight (.hole u w) r⟩, .transRight (.hole u w) r, l, by omega,
            hgeL, by simp only [RealCtx.size, RealTree.size]; omega⟩
        · exact ⟨w, v, ⟨.transLeft l (.hole w v)⟩, .transLeft l (.hole w v), r, by omega,
            by omega, by simp only [RealCtx.size, RealTree.size]; omega⟩

private lemma realCtx_split_lift {V : Type*} {stay : V → V → Prop}
    {pushPop : V → V → V → V → Prop} {u v u' v' x y : V}
    {rest : RealCtx stay pushPop u' v' x y} {stepSz K : ℕ}
    (wrap : ∀ {a b}, RealCtx stay pushPop u' v' a b → RealCtx stay pushPop u v a b)
    (hwrap : ∀ {a b} (Ctop : RealCtx stay pushPop u' v' a b),
      (wrap Ctop).size = stepSz + Ctop.size)
    (hpos : 0 < stepSz) (hgt : stepSz < K)
    (ihSplit :
      ∃ (a b a' b' : V) (Ctop : RealCtx stay pushPop u' v' a b)
        (Cbot : RealCtx stay pushPop a' b' x y),
        Ctop.size < K - stepSz ∧ Cbot.size ≤ rest.size - (K - stepSz) ∧
        (pushPop a a' b' b ∨
          (b' = b ∧ ∃ L : RealTree stay pushPop a a', L.size < rest.size) ∨
          (a' = a ∧ ∃ R : RealTree stay pushPop b' b, R.size < rest.size))) :
    ∃ (a b a' b' : V) (Ctop : RealCtx stay pushPop u v a b)
      (Cbot : RealCtx stay pushPop a' b' x y),
      Ctop.size < K ∧ Cbot.size ≤ (stepSz + rest.size) - K ∧
      (pushPop a a' b' b ∨
        (b' = b ∧ ∃ L : RealTree stay pushPop a a', L.size < stepSz + rest.size) ∨
        (a' = a ∧ ∃ R : RealTree stay pushPop b' b, R.size < stepSz + rest.size)) := by
  obtain ⟨a, b, a', b', Ctop, Cbot, htop, hbot, hmid⟩ := ihSplit
  refine ⟨a, b, a', b', wrap Ctop, Cbot, by rw [hwrap]; omega, by omega, ?_⟩
  rcases hmid with hp | ⟨rfl, L, hL⟩ | ⟨rfl, R, hR⟩
  · exact .inl hp
  · exact .inr (.inl ⟨rfl, L, by omega⟩)
  · exact .inr (.inr ⟨rfl, R, by omega⟩)

/-- Spine splitting for a one-hole context: for any `1 ≤ K ≤ C.size`, `C` splits at a single
spine step into an upper context of size `< K`, a lower context of size `≤ C.size - K`, and one
middle step (either `pushPop`, left sibling tree, or right sibling tree). -/
private lemma realCtx_split_at {V : Type*} {stay : V → V → Prop}
    {pushPop : V → V → V → V → Prop} {u v x y : V} (C : RealCtx stay pushPop u v x y) :
    ∀ {K : ℕ}, 1 ≤ K → K ≤ C.size →
      ∃ (a b a' b' : V) (Ctop : RealCtx stay pushPop u v a b)
        (Cbot : RealCtx stay pushPop a' b' x y),
        Ctop.size < K ∧ Cbot.size ≤ C.size - K ∧
        (pushPop a a' b' b ∨
          (b' = b ∧ ∃ L : RealTree stay pushPop a a', L.size < C.size) ∨
          (a' = a ∧ ∃ R : RealTree stay pushPop b' b, R.size < C.size)) := by
  induction C with
  | hole _ _ => intro K h1 hle; simp [RealCtx.size] at hle; omega
  | @pushPop u u' v' v x y h rest ih =>
    intro K h1 hle; simp only [RealCtx.size] at hle ⊢
    by_cases hK : K = 1
    · exact ⟨u, v, u', v', .hole u v, rest, by simp [RealCtx.size]; omega, by omega, .inl h⟩
    · exact realCtx_split_lift (.pushPop h) (fun _ => rfl) Nat.one_pos (by omega)
        (ih (by omega) (by omega))
  | @transLeft u w v x y l rest ih =>
    intro K h1 hle; simp only [RealCtx.size] at hle ⊢
    by_cases hK : K ≤ 1 + l.size
    · exact ⟨u, v, w, v, .hole u v, rest, by simp [RealCtx.size]; omega, by omega,
        .inr (.inl ⟨rfl, l, by omega⟩)⟩
    · exact realCtx_split_lift (.transLeft l) (fun _ => rfl) (by omega) (by omega)
        (ih (by omega) (by omega))
  | @transRight u w v x y rest r ih =>
    intro K h1 hle; simp only [RealCtx.size] at hle ⊢
    by_cases hK : K ≤ 1 + r.size
    · exact ⟨u, v, u, w, .hole u v, rest, by simp [RealCtx.size]; omega, by omega,
        .inr (.inr ⟨rfl, r, by omega⟩)⟩
    · rw [show 1 + rest.size + r.size = (1 + r.size) + rest.size by omega]
      exact realCtx_split_lift (stepSz := 1 + r.size) (fun Ctop => .transRight Ctop r)
        (fun _ => by simp only [RealCtx.size]; omega) (by omega) (by omega)
        (ih (by omega) (by omega))

/-! ### Exponential tree-size growth per 3 rounds -/

/-- Tree/context size covered after `3 * k` rounds: `growthBound 0 = 1` and
`growthBound (k + 1) = growthBound k + (growthBound k + 1) / 2`. -/
def growthBound : ℕ → ℕ
  | 0 => 1
  | k + 1 => growthBound k + (growthBound k + 1) / 2

lemma growthBound_pos (k : ℕ) : 1 ≤ growthBound k := by
  induction k with | zero => exact le_rfl | succ k ih => simp only [growthBound]; omega

lemma two_mul_growthBound_le (k : ℕ) : 2 * growthBound k ≤ growthBound (k + 2) := by
  have := growthBound_pos k; simp only [growthBound]; omega

/-- Every two phases (6 rounds) at least double the covered tree size:
`2 ^ j ≤ growthBound (2 * j)`. -/
theorem two_pow_le_growthBound_two_mul (j : ℕ) : 2 ^ j ≤ growthBound (2 * j) := by
  induction j with
  | zero => simp [growthBound]
  | succ j ih =>
    simpa only [pow_succ', Nat.mul_add] using
      (Nat.mul_le_mul_left 2 ih).trans (two_mul_growthBound_le (2 * j))

/-- Round count `6 * (Nat.log2 sz + 1)` sufficient to realize every tree of size at most `sz`. -/
def roundsForSize (sz : ℕ) : ℕ :=
  6 * (Nat.log2 sz + 1)

theorem le_growthBound_roundsForSize (sz : ℕ) :
    sz ≤ growthBound (2 * (Nat.log2 sz + 1)) :=
  (Nat.log2_eq_log_two ▸ Nat.lt_pow_succ_log_self (by decide) sz).le.trans
    (two_pow_le_growthBound_two_mul _)

/-! ### Alternating normal-form balanced-depth circuit -/

/-- Gates of the `R`-round alternating normal-form balanced-depth semi-unbounded circuit over a
vertex type `V`. -/
inductive BalancedGate (V : Type*) (R : ℕ) where
  /-- Layer `0`: sole true leaf. -/
  | leafTrue
  /-- Layer `1` (AND-level `0`): unary AND buffer above `leafTrue`. -/
  | andTrue
  /-- Layer `2 * r + 2` (OR): realizable pair `(u, v)` at round `r`. -/
  | orP (r : Fin (R + 1)) (u v : V)
  /-- Layer `2 * r + 2` (OR): realizable one-hole context `(u, v; x, y)` at round `r`. -/
  | orQ (r : Fin (R + 1)) (u v x y : V)
  /-- Layer `2 * r + 3` (AND): plug pair `(x, y)` into context `(u, v; x, y)` for `orP (r + 1)`. -/
  | andPPlug (r : Fin R) (u v x y : V)
  /-- Layer `2 * r + 3` (AND): compose contexts `(u, v; a, b)` and `(a, b; x, y)`. -/
  | andQComp (r : Fin R) (u v a b x y : V)
  /-- Layer `2 * r + 3` (AND): attach left pair `(u, w)` to context `(w, v; x, y)`. -/
  | andQLeft (r : Fin R) (u w v x y : V)
  /-- Layer `2 * r + 3` (AND): attach right pair `(w, v)` to context `(u, w; x, y)`. -/
  | andQRight (r : Fin R) (u w v x y : V)
  /-- Layer `2 * R + 3` (AND): unary buffer for accepting endpoint `v` feeding `output`. -/
  | andAccept (v : V)
  /-- Layer `2 * R + 4` (OR): single circuit output gate. -/
  | output
  deriving DecidableEq

namespace BalancedGate

variable {V : Type*} {R : ℕ}

/-- Layer index of a gate in `balancedCircuit`. -/
def layer : BalancedGate V R → ℕ
  | .leafTrue => 0
  | .andTrue => 1
  | .orP r _ _ => 2 * r.val + 2
  | .orQ r _ _ _ _ => 2 * r.val + 2
  | .andPPlug r _ _ _ _ => 2 * r.val + 3
  | .andQComp r _ _ _ _ _ _ => 2 * r.val + 3
  | .andQLeft r _ _ _ _ _ => 2 * r.val + 3
  | .andQRight r _ _ _ _ _ => 2 * r.val + 3
  | .andAccept _ => 2 * R + 3
  | .output => 2 * R + 4

/-- Gate kind (and AND-gate children) relative to initial vertex `start`. -/
def kind (start : V) : BalancedGate V R → GateKind (BalancedGate V R)
  | .leafTrue => .leaf true
  | .andTrue => .and (.unary .leafTrue)
  | .orP _ _ _ => .or
  | .orQ _ _ _ _ _ => .or
  | .andPPlug r u v x y => .and (.binary (.orQ r.castSucc u v x y) (.orP r.castSucc x y))
  | .andQComp r u v a b x y => .and (.binary (.orQ r.castSucc u v a b) (.orQ r.castSucc a b x y))
  | .andQLeft r u w v x y => .and (.binary (.orP r.castSucc u w) (.orQ r.castSucc w v x y))
  | .andQRight r u w v x y => .and (.binary (.orQ r.castSucc u w x y) (.orP r.castSucc w v))
  | .andAccept v => .and (.unary (.orP (Fin.last R) start v))
  | .output => .or

/-- OR-gate child relation (quantifier-free by pattern matching on parent and child). -/
def orChild (accept : V → Prop) (stay : V → V → Prop) (pushPop : V → V → V → V → Prop) :
    BalancedGate V R → BalancedGate V R → Prop
  | .orP ⟨0, _⟩ u v, .andTrue => u = v ∨ stay u v
  | .orP ⟨r + 1, _⟩ u v, .andPPlug r' u' v' _ _ => r'.val = r ∧ u' = u ∧ v' = v
  | .orQ ⟨0, _⟩ u v x y, .andTrue => (u = x ∧ v = y) ∨ pushPop u x y v
  | .orQ ⟨r + 1, _⟩ u v x y, .andQComp r' u' v' _ _ x' y' =>
      r'.val = r ∧ u' = u ∧ v' = v ∧ x' = x ∧ y' = y
  | .orQ ⟨r + 1, _⟩ u v x y, .andQLeft r' u' _ v' x' y' =>
      r'.val = r ∧ u' = u ∧ v' = v ∧ x' = x ∧ y' = y
  | .orQ ⟨r + 1, _⟩ u v x y, .andQRight r' u' _ v' x' y' =>
      r'.val = r ∧ u' = u ∧ v' = v ∧ x' = x ∧ y' = y
  | .output, .andAccept v => accept v
  | _, _ => False

instance instDecidableOrChild [DecidableEq V]
    {accept : V → Prop} {stay : V → V → Prop} {pushPop : V → V → V → V → Prop}
    [∀ v, Decidable (accept v)] [∀ u v, Decidable (stay u v)]
    [∀ u x y v, Decidable (pushPop u x y v)]
    (g c : BalancedGate V R) :
    Decidable (orChild accept stay pushPop g c) := by
  cases g with
  | orP r u v =>
    rcases r with ⟨r, hr⟩
    cases r with
    | zero => cases c <;> dsimp only [orChild] <;> infer_instance
    | succ r => cases c <;> dsimp only [orChild] <;> infer_instance
  | orQ r u v x y =>
    rcases r with ⟨r, hr⟩
    cases r with
    | zero => cases c <;> dsimp only [orChild] <;> infer_instance
    | succ r => cases c <;> dsimp only [orChild] <;> infer_instance
  | output => cases c <;> dsimp only [orChild] <;> infer_instance
  | leafTrue | andTrue | andPPlug _ _ _ _ _ | andQComp _ _ _ _ _ _ _
  | andQLeft _ _ _ _ _ _ | andQRight _ _ _ _ _ _ | andAccept _ =>
    dsimp only [orChild]; infer_instance

end BalancedGate

/-- The `R`-round alternating normal-form semi-unbounded circuit deciding existence of a
realizability tree from `start` to some vertex satisfying `accept`. -/
def balancedCircuit {V : Type*} (start : V) (accept : V → Prop)
    (stay : V → V → Prop) (pushPop : V → V → V → V → Prop) (R : ℕ) :
    LayeredSemiUnboundedCircuit (BalancedGate V R) where
  layer := BalancedGate.layer
  kind := BalancedGate.kind start
  orChild := BalancedGate.orChild accept stay pushPop
  layer_andUnary {g c} h := by
    cases g <;> simp only [BalancedGate.kind] at h <;> cases h <;> simp [BalancedGate.layer]
  layer_andBinary {g l r} h := by
    cases g <;> simp only [BalancedGate.kind] at h <;> cases h <;> simp [BalancedGate.layer]
  layer_orChild {g c} h hch := by
    cases g with
    | orP r u v =>
      rcases r with ⟨r, hr⟩
      cases r with
      | zero =>
        cases c <;> simp only [BalancedGate.orChild] at hch
        simp [BalancedGate.layer]
      | succ r =>
        cases c <;> simp only [BalancedGate.orChild] at hch
        obtain ⟨hr', -, -⟩ := hch
        simp only [BalancedGate.layer, hr']
        omega
    | orQ r u v x y =>
      rcases r with ⟨r, hr⟩
      cases r with
      | zero =>
        cases c <;> simp only [BalancedGate.orChild] at hch
        simp [BalancedGate.layer]
      | succ r =>
        cases c <;> simp only [BalancedGate.orChild] at hch <;>
          obtain ⟨hr', -⟩ := hch <;> simp only [BalancedGate.layer, hr'] <;> omega
    | output =>
      cases c <;> simp only [BalancedGate.orChild] at hch
      simp [BalancedGate.layer]
    | leafTrue | andTrue | andPPlug _ _ _ _ _ | andQComp _ _ _ _ _ _ _
    | andQLeft _ _ _ _ _ _ | andQRight _ _ _ _ _ _ | andAccept _ =>
      simp [BalancedGate.kind] at h

instance instDecidableOrChildBalancedCircuit {V : Type*} [DecidableEq V] (start : V)
    (accept : V → Prop) [∀ v, Decidable (accept v)]
    (stay : V → V → Prop) [∀ u v, Decidable (stay u v)]
    (pushPop : V → V → V → V → Prop) [∀ u u' v' v, Decidable (pushPop u u' v' v)] (R : ℕ) :
    DecidableRel (balancedCircuit start accept stay pushPop R).orChild :=
  BalancedGate.instDecidableOrChild

/-- `balancedCircuit` is strictly in alternating AND-first-layer normal form (`InNormalForm`). -/
theorem balancedCircuit_inNormalForm {V : Type*} (start : V) (accept : V → Prop)
    (stay : V → V → Prop) (pushPop : V → V → V → V → Prop) (R : ℕ) :
    (balancedCircuit start accept stay pushPop R).InNormalForm where
  leaf_of_layer_zero {g} h0 := by
    cases g <;> simp only [balancedCircuit, BalancedGate.layer] at h0; · exact ⟨true, rfl⟩
    all_goals omega
  and_of_odd {g} := fun ⟨m, hm⟩ => by
    cases g <;>
      first | exact ⟨_, rfl⟩ | (simp only [balancedCircuit, BalancedGate.layer] at hm; omega)
  or_of_pos_even {g} hpos := fun ⟨m, hm⟩ => by
    cases g <;>
      first | rfl | (simp only [balancedCircuit, BalancedGate.layer] at hpos hm; omega)

/-- Every gate in `balancedCircuit … R` has `andLevel` at most `R + 2`. -/
theorem balancedCircuit_andLevel_le {V : Type*} (start : V) (accept : V → Prop)
    (stay : V → V → Prop) (pushPop : V → V → V → V → Prop) (R : ℕ)
    (g : BalancedGate V R) :
    (balancedCircuit start accept stay pushPop R).andLevel g ≤ R + 2 := by
  cases g with
  | leafTrue | andTrue | andAccept _ | output =>
    simp only [LayeredSemiUnboundedCircuit.andLevel, balancedCircuit, BalancedGate.layer]; omega
  | orP r _ _ | orQ r _ _ _ _ | andPPlug r _ _ _ _ | andQComp r _ _ _ _ _ _
  | andQLeft r _ _ _ _ _ | andQRight r _ _ _ _ _ =>
    have := r.isLt
    simp only [LayeredSemiUnboundedCircuit.andLevel, balancedCircuit, BalancedGate.layer]; omega

/-! ### Exact evaluation equations, soundness, and `O(log sz)` completeness -/

section Eval

variable {V : Type*} {start : V} {accept : V → Prop}
variable {stay : V → V → Prop} {pushPop : V → V → V → V → Prop} {R : ℕ}

private abbrev C (start : V) (accept : V → Prop) (stay : V → V → Prop)
    (pushPop : V → V → V → V → Prop) (R : ℕ) :=
  balancedCircuit start accept stay pushPop R

private lemma eval_andTrue :
    (C start accept stay pushPop R).Eval .andTrue := by
  rw [(C start accept stay pushPop R).eval_andUnary rfl,
    (C start accept stay pushPop R).eval_leaf rfl]

private lemma eval_or_andTrue_iff {g : BalancedGate V R} {P : Prop}
    (hkind : (C start accept stay pushPop R).kind g = .or)
    (hfwd : ∀ c, (C start accept stay pushPop R).orChild g c → P)
    (hbwd : P → (C start accept stay pushPop R).orChild g .andTrue) :
    (C start accept stay pushPop R).Eval g ↔ P := by
  rw [(C start accept stay pushPop R).eval_or hkind]
  exact ⟨fun ⟨c, hc, _⟩ => hfwd c hc, fun hp => ⟨.andTrue, hbwd hp, eval_andTrue⟩⟩

private lemma eval_orP_zero_iff (u v : V) :
    (C start accept stay pushPop R).Eval (.orP ⟨0, Nat.succ_pos R⟩ u v) ↔ u = v ∨ stay u v :=
  eval_or_andTrue_iff rfl
    (fun c hch => by
      cases c <;> simp only [C, balancedCircuit, BalancedGate.orChild] at hch; exact hch)
    id

private lemma eval_orQ_zero_iff (u v x y : V) :
    (C start accept stay pushPop R).Eval (.orQ ⟨0, Nat.succ_pos R⟩ u v x y) ↔
      (u = x ∧ v = y) ∨ pushPop u x y v :=
  eval_or_andTrue_iff rfl
    (fun c hch => by
      cases c <;> simp only [C, balancedCircuit, BalancedGate.orChild] at hch; exact hch)
    id

private lemma eval_andBinary_castSucc {r : ℕ} (hr : r + 1 < R + 1) {r' : Fin R}
    (hr' : r'.val = r) {c : BalancedGate V R}
    {g₁ g₂ : Fin (R + 1) → BalancedGate V R}
    (hkind : (C start accept stay pushPop R).kind c =
      .and (.binary (g₁ r'.castSucc) (g₂ r'.castSucc)))
    (hev : (C start accept stay pushPop R).Eval c) :
    (C start accept stay pushPop R).Eval (g₁ ⟨r, by omega⟩) ∧
      (C start accept stay pushPop R).Eval (g₂ ⟨r, by omega⟩) := by
  rw [(C start accept stay pushPop R).eval_andBinary hkind,
    show r'.castSucc = ⟨r, by omega⟩ from Fin.ext hr'] at hev
  exact hev

private lemma eval_or_of_andBinary {g c g₁ g₂ : BalancedGate V R}
    (hor : (C start accept stay pushPop R).kind g = .or)
    (hch : (C start accept stay pushPop R).orChild g c)
    (hand : (C start accept stay pushPop R).kind c = .and (.binary g₁ g₂))
    (h₁ : (C start accept stay pushPop R).Eval g₁)
    (h₂ : (C start accept stay pushPop R).Eval g₂) :
    (C start accept stay pushPop R).Eval g := by
  rw [(C start accept stay pushPop R).eval_or hor]
  exact ⟨c, hch, ((C start accept stay pushPop R).eval_andBinary hand).mpr ⟨h₁, h₂⟩⟩

private lemma eval_orP_succ_iff {r : ℕ} (hr : r + 1 < R + 1) (u v : V) :
    (C start accept stay pushPop R).Eval (.orP ⟨r + 1, hr⟩ u v) ↔
      ∃ x y,
        (C start accept stay pushPop R).Eval (.orQ ⟨r, by omega⟩ u v x y) ∧
        (C start accept stay pushPop R).Eval (.orP ⟨r, by omega⟩ x y) := by
  refine ⟨fun hev => ?_, fun ⟨x, y, hq, hp⟩ =>
    eval_or_of_andBinary rfl (c := .andPPlug ⟨r, by omega⟩ u v x y) ⟨rfl, rfl, rfl⟩ rfl hq hp⟩
  obtain ⟨c, hch, hevc⟩ := ((C start accept stay pushPop R).eval_or rfl).mp hev
  cases c <;> simp only [C, balancedCircuit, BalancedGate.orChild] at hch
  rename_i r' u' v' x y
  rcases hch with ⟨hr', rfl, rfl⟩
  exact ⟨x, y, eval_andBinary_castSucc hr hr'
    (g₁ := fun t => .orQ t u' v' x y) (g₂ := fun t => .orP t x y) rfl hevc⟩

private lemma eval_orQ_succ_iff {r : ℕ} (hr : r + 1 < R + 1) (u v x y : V) :
    (C start accept stay pushPop R).Eval (.orQ ⟨r + 1, hr⟩ u v x y) ↔
      (∃ a b,
        (C start accept stay pushPop R).Eval (.orQ ⟨r, by omega⟩ u v a b) ∧
        (C start accept stay pushPop R).Eval (.orQ ⟨r, by omega⟩ a b x y)) ∨
      (∃ w,
        (C start accept stay pushPop R).Eval (.orP ⟨r, by omega⟩ u w) ∧
        (C start accept stay pushPop R).Eval (.orQ ⟨r, by omega⟩ w v x y)) ∨
      (∃ w,
        (C start accept stay pushPop R).Eval (.orQ ⟨r, by omega⟩ u w x y) ∧
        (C start accept stay pushPop R).Eval (.orP ⟨r, by omega⟩ w v)) := by
  constructor
  · intro hev
    obtain ⟨c, hch, hevc⟩ := ((C start accept stay pushPop R).eval_or rfl).mp hev
    cases c <;> simp only [C, balancedCircuit, BalancedGate.orChild] at hch
    · rename_i r' u' v' a b x' y'
      rcases hch with ⟨hr', rfl, rfl, rfl, rfl⟩
      exact .inl ⟨a, b, eval_andBinary_castSucc hr hr'
        (g₁ := fun t => .orQ t u' v' a b) (g₂ := fun t => .orQ t a b x' y') rfl hevc⟩
    · rename_i r' u' w v' x' y'
      rcases hch with ⟨hr', rfl, rfl, rfl, rfl⟩
      exact .inr (.inl ⟨w, eval_andBinary_castSucc hr hr'
        (g₁ := fun t => .orP t u' w) (g₂ := fun t => .orQ t w v' x' y') rfl hevc⟩)
    · rename_i r' u' w v' x' y'
      rcases hch with ⟨hr', rfl, rfl, rfl, rfl⟩
      exact .inr (.inr ⟨w, eval_andBinary_castSucc hr hr'
        (g₁ := fun t => .orQ t u' w x' y') (g₂ := fun t => .orP t w v') rfl hevc⟩)
  · rintro (⟨a, b, h1, h2⟩ | ⟨w, h1, h2⟩ | ⟨w, h1, h2⟩)
    · exact eval_or_of_andBinary rfl (c := .andQComp ⟨r, by omega⟩ u v a b x y)
        ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl h1 h2
    · exact eval_or_of_andBinary rfl (c := .andQLeft ⟨r, by omega⟩ u w v x y)
        ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl h1 h2
    · exact eval_or_of_andBinary rfl (c := .andQRight ⟨r, by omega⟩ u w v x y)
        ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl h1 h2

private lemma eval_orQ_refl :
    ∀ (r : ℕ) (hr : r < R + 1) (u v : V),
      (C start accept stay pushPop R).Eval (.orQ ⟨r, hr⟩ u v u v)
  | 0, _, u, v => (eval_orQ_zero_iff u v u v).mpr (.inl ⟨rfl, rfl⟩)
  | r + 1, hr, u, v =>
    (eval_orQ_succ_iff hr u v u v).mpr
      (.inl ⟨u, v, eval_orQ_refl r (by omega) u v, eval_orQ_refl r (by omega) u v⟩)

private lemma eval_orQ_mono {r₁ r₂ : ℕ} (hle : r₁ ≤ r₂) (hr₂ : r₂ < R + 1) {u v x y : V}
    (h : (C start accept stay pushPop R).Eval (.orQ ⟨r₁, by omega⟩ u v x y)) :
    (C start accept stay pushPop R).Eval (.orQ ⟨r₂, hr₂⟩ u v x y) := by
  induction r₂ with
  | zero =>
    have hr1 : r₁ = 0 := by omega
    subst hr1
    exact h
  | succ r₂ ih =>
    rcases lt_or_eq_of_le hle with hlt | rfl
    · exact (eval_orQ_succ_iff hr₂ u v x y).mpr
        (.inl ⟨x, y, ih (by omega) (by omega) h, eval_orQ_refl r₂ (by omega) x y⟩)
    · exact h

private lemma eval_orP_mono {r₁ r₂ : ℕ} (hle : r₁ ≤ r₂) (hr₂ : r₂ < R + 1) {u v : V}
    (h : (C start accept stay pushPop R).Eval (.orP ⟨r₁, by omega⟩ u v)) :
    (C start accept stay pushPop R).Eval (.orP ⟨r₂, hr₂⟩ u v) := by
  induction r₂ with
  | zero =>
    have hr1 : r₁ = 0 := by omega
    subst hr1
    exact h
  | succ r₂ ih =>
    rcases lt_or_eq_of_le hle with hlt | rfl
    · exact (eval_orP_succ_iff hr₂ u v).mpr
        ⟨u, v, eval_orQ_refl r₂ (by omega) u v, ih (by omega) (by omega) h⟩
    · exact h

private lemma eval_orP_orQ_sound :
    ∀ (r : ℕ) (hr : r < R + 1),
      (∀ u v, (C start accept stay pushPop R).Eval (.orP ⟨r, hr⟩ u v) →
        Nonempty (RealTree stay pushPop u v)) ∧
      (∀ u v x y, (C start accept stay pushPop R).Eval (.orQ ⟨r, hr⟩ u v x y) →
        Nonempty (RealTree stay pushPop x y) → Nonempty (RealTree stay pushPop u v))
  | 0, _ =>
    ⟨fun u v h => ((eval_orP_zero_iff u v).mp h).elim (fun e => e ▸ ⟨.refl u⟩) (⟨.stay ·⟩),
     fun u v x y h ⟨T⟩ => ((eval_orQ_zero_iff u v x y).mp h).elim
       (fun ⟨hu, hv⟩ => hu ▸ hv ▸ ⟨T⟩) (⟨.pushPop · T⟩)⟩
  | r + 1, hr => by
    obtain ⟨ihP, ihQ⟩ := eval_orP_orQ_sound r (by omega)
    refine ⟨fun u v h => let ⟨x, y, hq, hp⟩ := (eval_orP_succ_iff hr u v).mp h
      ihQ u v x y hq (ihP x y hp), fun u v x y h hT => ?_⟩
    rcases (eval_orQ_succ_iff hr u v x y).mp h with ⟨a, b, h1, h2⟩ | ⟨w, h1, h2⟩ | ⟨w, h1, h2⟩
    · exact ihQ u v a b h1 (ihQ a b x y h2 hT)
    · exact let ⟨Tl⟩ := ihP u w h1; let ⟨Tr⟩ := ihQ w v x y h2 hT; ⟨.trans Tl Tr⟩
    · exact let ⟨Tl⟩ := ihQ u w x y h1 hT; let ⟨Tr⟩ := ihP w v h2; ⟨.trans Tl Tr⟩

/-- **Soundness of `balancedCircuit`**: if the output gate evaluates to `true` (at any round
count `R`), there exists an accepting vertex `v` and a `RealTree` from `start` to `v`. -/
theorem balancedCircuit_eval_output_sound
    (h : (balancedCircuit start accept stay pushPop R).Eval .output) :
    ∃ v, accept v ∧ Nonempty (RealTree stay pushPop start v) := by
  obtain ⟨c, hch, hev⟩ := ((balancedCircuit start accept stay pushPop R).eval_or rfl).mp h
  cases c <;> simp only [balancedCircuit, BalancedGate.orChild] at hch
  rw [(balancedCircuit start accept stay pushPop R).eval_andUnary rfl] at hev
  exact ⟨_, hch, (eval_orP_orQ_sound (start := start) (accept := accept) (stay := stay)
    (pushPop := pushPop) (R := R) R (Nat.lt_succ_self R)).1 start _ hev⟩

private lemma eval_orP_orQ_complete :
    ∀ (k : ℕ) (hk : 3 * k < R + 1),
      (∀ {u v} (T : RealTree stay pushPop u v), T.size ≤ growthBound k →
        (C start accept stay pushPop R).Eval (.orP ⟨3 * k, hk⟩ u v)) ∧
      (∀ {u v x y} (Ctx : RealCtx stay pushPop u v x y), Ctx.size ≤ growthBound k →
        (C start accept stay pushPop R).Eval (.orQ ⟨3 * k, hk⟩ u v x y))
  | 0, hk =>
    ⟨fun T hsz => by
        cases T with
        | refl _ => exact (eval_orP_zero_iff _ _).mpr (.inl rfl)
        | stay h => exact (eval_orP_zero_iff _ _).mpr (.inr h)
        | pushPop _ sub =>
          have := sub.size_pos; simp only [RealTree.size, growthBound] at hsz; omega
        | trans l r =>
          have := l.size_pos; have := r.size_pos
          simp only [RealTree.size, growthBound] at hsz; omega,
     fun Ctx hsz => by
        cases Ctx with
        | hole _ _ => exact (eval_orQ_zero_iff _ _ _ _).mpr (.inl ⟨rfl, rfl⟩)
        | pushPop h rest =>
          cases rest with
          | hole _ _ => exact (eval_orQ_zero_iff _ _ _ _).mpr (.inr h)
          | pushPop _ _ => simp [RealCtx.size, growthBound] at hsz
          | transLeft l _ =>
            have := l.size_pos; simp only [RealCtx.size, growthBound] at hsz; omega
          | transRight _ r =>
            have := r.size_pos; simp only [RealCtx.size, growthBound] at hsz; omega
        | transLeft l _ =>
          have := l.size_pos; simp only [RealCtx.size, growthBound] at hsz; omega
        | transRight _ r =>
          have := r.size_pos; simp only [RealCtx.size, growthBound] at hsz; omega⟩
  | k + 1, hk => by
    obtain ⟨ihP, ihQ⟩ := eval_orP_orQ_complete k (by omega)
    have hP1 {u v} (T : RealTree stay pushPop u v) (hsz : T.size ≤ growthBound (k + 1)) :
        (C start accept stay pushPop R).Eval (.orP ⟨3 * k + 1, by omega⟩ u v) := by
      by_cases hle : T.size ≤ growthBound k
      · exact eval_orP_mono (by omega) (by omega) (ihP T hle)
      · obtain ⟨x, y, -, Ctx, sub, hsubLe, hsubGe, hsum⟩ :=
          realTree_split_le T (growthBound_pos k) (by omega)
        exact (eval_orP_succ_iff (by omega) u v).mpr
          ⟨x, y, ihQ Ctx (by simp only [growthBound] at hsz; omega), ihP sub hsubLe⟩
    refine ⟨fun T hsz => eval_orP_mono (by omega) hk (hP1 T hsz), fun {u v x y} Ctx hsz => ?_⟩
    by_cases hle : Ctx.size ≤ growthBound k
    · exact eval_orQ_mono (by omega) hk (ihQ Ctx hle)
    · obtain ⟨a, b, a', b', Ctop, Cbot, htopLt, hbotLe, hmid⟩ :=
        realCtx_split_at (K := Ctx.size - growthBound k) Ctx (by omega) (Nat.sub_le _ _)
      have hkpos := growthBound_pos k
      have hEvalTop : (C start accept stay pushPop R).Eval (.orQ ⟨3 * k + 2, by omega⟩ u v a b) :=
        eval_orQ_mono (by omega) (by omega) (ihQ Ctop (by simp only [growthBound] at hsz; omega))
      have hEvalBot : (C start accept stay pushPop R).Eval (.orQ ⟨3 * k + 1, by omega⟩ a' b' x y) :=
        eval_orQ_mono (by omega) (by omega) (ihQ Cbot (by omega))
      refine (eval_orQ_succ_iff hk u v x y).mpr (.inl ⟨a, b, hEvalTop, ?_⟩)
      rcases hmid with hp | ⟨rfl, L, hL⟩ | ⟨rfl, Rtree, hR⟩
      · exact (eval_orQ_succ_iff (r := 3 * k + 1) (by omega) a b x y).mpr (.inl ⟨a', b',
          eval_orQ_mono (r₁ := 0) (Nat.zero_le _) (by omega)
            ((eval_orQ_zero_iff a b a' b').mpr (.inr hp)), hEvalBot⟩)
      · exact (eval_orQ_succ_iff (r := 3 * k + 1) (by omega) a b' x y).mpr
          (.inr (.inl ⟨a', hP1 L (hL.le.trans hsz), hEvalBot⟩))
      · exact (eval_orQ_succ_iff (r := 3 * k + 1) (by omega) a' b x y).mpr
          (.inr (.inr ⟨b', hEvalBot, hP1 Rtree (hR.le.trans hsz)⟩))

/-- **Balanced-depth completeness of `balancedCircuit`**: whenever `R ≥ roundsForSize sz`, any
accepting realizability tree of size at most `sz` makes the output gate evaluate to `true`. -/
theorem balancedCircuit_eval_output_complete {sz : ℕ} (hR : roundsForSize sz ≤ R)
    {v : V} (hacc : accept v) (T : RealTree stay pushPop start v) (hsz : T.size ≤ sz) :
    (balancedCircuit start accept stay pushPop R).Eval .output := by
  have h3k : 3 * (2 * (Nat.log2 sz + 1)) ≤ R := by unfold roundsForSize at hR; omega
  have hev3k := (eval_orP_orQ_complete (start := start) (accept := accept) (stay := stay)
    (pushPop := pushPop) (R := R) (2 * (Nat.log2 sz + 1)) (by omega)).1 T
    (hsz.trans (le_growthBound_roundsForSize sz))
  rw [(balancedCircuit start accept stay pushPop R).eval_or rfl]
  exact ⟨.andAccept v, hacc, ((balancedCircuit start accept stay pushPop R).eval_andUnary rfl).mpr
    (eval_orP_mono h3k (Nat.lt_succ_self R) hev3k)⟩

end Eval

/-! ### Computable `Fin N` indexing of `BalancedGate (Fin S) R` -/

/-- Exact number of gates in `balancedCircuit` over `Fin S` with `R` rounds. -/
def balancedGateCount (S R : ℕ) : ℕ :=
  ((((((((1 + 1) + (R + 1) * (S * S)) + (R + 1) * ((S * S) * (S * S))) +
    R * ((S * S) * (S * S))) + R * (((S * S) * (S * S)) * (S * S))) +
    R * (((S * S) * (S * S)) * S)) + R * (((S * S) * (S * S)) * S)) + S) + 1

/-- Computable bijection indexing every gate of `BalancedGate (Fin S) R` into
`Fin (balancedGateCount S R)`. -/
def balancedGateEquivFin (S R : ℕ) : BalancedGate (Fin S) R ≃ Fin (balancedGateCount S R) :=
  let fin2 : Fin S × Fin S ≃ Fin (S * S) := finProdFinEquiv
  let fin4 : (Fin S × Fin S) × (Fin S × Fin S) ≃ Fin ((S * S) * (S * S)) :=
    (Equiv.prodCongr fin2 fin2).trans finProdFinEquiv
  let fin5 : ((Fin S × Fin S) × (Fin S × Fin S)) × Fin S ≃ Fin (((S * S) * (S * S)) * S) :=
    (Equiv.prodCongr fin4 (Equiv.refl _)).trans finProdFinEquiv
  let fin6 :
      ((Fin S × Fin S) × (Fin S × Fin S)) × (Fin S × Fin S) ≃
        Fin (((S * S) * (S * S)) * (S * S)) :=
    (Equiv.prodCongr fin4 fin2).trans finProdFinEquiv
  let eSplit : BalancedGate (Fin S) R ≃
      ((((((((Fin 1 ⊕ Fin 1) ⊕ (Fin (R + 1) × (Fin S × Fin S))) ⊕
        (Fin (R + 1) × ((Fin S × Fin S) × (Fin S × Fin S)))) ⊕
        (Fin R × ((Fin S × Fin S) × (Fin S × Fin S)))) ⊕
        (Fin R × (((Fin S × Fin S) × (Fin S × Fin S)) × (Fin S × Fin S)))) ⊕
        (Fin R × (((Fin S × Fin S) × (Fin S × Fin S)) × Fin S))) ⊕
        (Fin R × (((Fin S × Fin S) × (Fin S × Fin S)) × Fin S))) ⊕ Fin S) ⊕ Fin 1 :=
    { toFun := fun
        | .leafTrue => .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl 0))))))))
        | .andTrue => .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inr 0))))))))
        | .orP r u v => .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inr (r, (u, v)))))))))
        | .orQ r u v x y => .inl (.inl (.inl (.inl (.inl (.inl (.inr (r, ((u, v), (x, y)))))))))
        | .andPPlug r u v x y =>
            .inl (.inl (.inl (.inl (.inl (.inr (r, ((u, v), (x, y))))))))
        | .andQComp r u v a b x y =>
            .inl (.inl (.inl (.inl (.inr (r, (((u, v), (a, b)), (x, y)))))))
        | .andQLeft r u w v x y =>
            .inl (.inl (.inl (.inr (r, (((u, w), (v, x)), y)))))
        | .andQRight r u w v x y =>
            .inl (.inl (.inr (r, (((u, w), (v, x)), y))))
        | .andAccept v => .inl (.inr v)
        | .output => .inr 0
      invFun := fun
        | .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl _)))))))) => .leafTrue
        | .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inr _)))))))) => .andTrue
        | .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inr (r, (u, v))))))))) => .orP r u v
        | .inl (.inl (.inl (.inl (.inl (.inl (.inr (r, ((u, v), (x, y))))))))) => .orQ r u v x y
        | .inl (.inl (.inl (.inl (.inl (.inr (r, ((u, v), (x, y)))))))) => .andPPlug r u v x y
        | .inl (.inl (.inl (.inl (.inr (r, (((u, v), (a, b)), (x, y))))))) =>
            .andQComp r u v a b x y
        | .inl (.inl (.inl (.inr (r, (((u, w), (v, x)), y))))) => .andQLeft r u w v x y
        | .inl (.inl (.inr (r, (((u, w), (v, x)), y)))) => .andQRight r u w v x y
        | .inl (.inr v) => .andAccept v
        | .inr _ => .output
      left_inv := fun g => by cases g <;> rfl
      right_inv := fun
        | .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl i)))))))) => by
            fin_cases i; rfl
        | .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inr i)))))))) => by
            fin_cases i; rfl
        | .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inr (_, (_, _))))))))) => rfl
        | .inl (.inl (.inl (.inl (.inl (.inl (.inr (_, ((_, _), (_, _))))))))) => rfl
        | .inl (.inl (.inl (.inl (.inl (.inr (_, ((_, _), (_, _)))))))) => rfl
        | .inl (.inl (.inl (.inl (.inr (_, (((_, _), (_, _)), (_, _))))))) => rfl
        | .inl (.inl (.inl (.inr (_, (((_, _), (_, _)), _))))) => rfl
        | .inl (.inl (.inr (_, (((_, _), (_, _)), _)))) => rfl
        | .inl (.inr _) => rfl
        | .inr i => by fin_cases i; rfl }
  let c0 := finSumFinEquiv (m := 1) (n := 1)
  let c1 := (Equiv.sumCongr c0 ((Equiv.prodCongr (Equiv.refl _) fin2).trans finProdFinEquiv)).trans
    finSumFinEquiv
  let c2 := (Equiv.sumCongr c1 ((Equiv.prodCongr (Equiv.refl _) fin4).trans finProdFinEquiv)).trans
    finSumFinEquiv
  let c3 := (Equiv.sumCongr c2 ((Equiv.prodCongr (Equiv.refl _) fin4).trans finProdFinEquiv)).trans
    finSumFinEquiv
  let c4 := (Equiv.sumCongr c3 ((Equiv.prodCongr (Equiv.refl _) fin6).trans finProdFinEquiv)).trans
    finSumFinEquiv
  let c5 := (Equiv.sumCongr c4 ((Equiv.prodCongr (Equiv.refl _) fin5).trans finProdFinEquiv)).trans
    finSumFinEquiv
  let c6 := (Equiv.sumCongr c5 ((Equiv.prodCongr (Equiv.refl _) fin5).trans finProdFinEquiv)).trans
    finSumFinEquiv
  let c7 := (Equiv.sumCongr c6 (Equiv.refl _)).trans finSumFinEquiv
  let c8 := (Equiv.sumCongr c7 (Equiv.refl _)).trans finSumFinEquiv
  eSplit.trans c8

theorem le_balancedGateCount (S R : ℕ) : S + 3 ≤ balancedGateCount S R := by
  unfold balancedGateCount
  omega

theorem balancedGateCount_le (S R : ℕ) :
    balancedGateCount S R ≤ 6 * (R + 1) * (S + 1) ^ 6 := by
  unfold balancedGateCount
  have hd (d : ℕ) (hd6 : d ≤ 6) : S ^ d ≤ (S + 1) ^ 6 :=
    (Nat.pow_le_pow_left (Nat.le_succ S) d).trans (Nat.pow_le_pow_right (Nat.succ_pos S) hd6)
  nlinarith [Nat.one_le_pow 6 (S + 1) (Nat.succ_pos S),
    (Nat.le_succ S).trans (Nat.le_self_pow (by decide : 6 ≠ 0) (S + 1)),
    show S * S ≤ (S + 1) ^ 6 by simpa only [sq] using hd 2 (by decide),
    show (S * S) * (S * S) ≤ (S + 1) ^ 6 by
      rw [show (S * S) * (S * S) = S ^ 4 by ring]
      exact hd 4 (by decide),
    show ((S * S) * (S * S)) * S ≤ (S + 1) ^ 6 by
      rw [show ((S * S) * (S * S)) * S = S ^ 5 by ring]
      exact hd 5 (by decide),
    show ((S * S) * (S * S)) * (S * S) ≤ (S + 1) ^ 6 by
      rw [show ((S * S) * (S * S)) * (S * S) = S ^ 6 by ring]
      exact hd 6 le_rfl]

/-- The `Fin N`-indexed balanced-depth normal-form semi-unbounded circuit over `Fin S`. -/
def balancedCircuitFin {S : ℕ} (start : Fin S) (accept : Fin S → Prop)
    (stay : Fin S → Fin S → Prop) (pushPop : Fin S → Fin S → Fin S → Fin S → Prop) (R : ℕ) :
    LayeredSemiUnboundedCircuit (Fin (balancedGateCount S R)) :=
  (balancedCircuit start accept stay pushPop R).reindex (balancedGateEquivFin S R)

instance instDecidableOrChildBalancedCircuitFin {S : ℕ} (start : Fin S)
    (accept : Fin S → Prop) [∀ v, Decidable (accept v)]
    (stay : Fin S → Fin S → Prop) [∀ u v, Decidable (stay u v)]
    (pushPop : Fin S → Fin S → Fin S → Fin S → Prop)
    [∀ u u' v' v, Decidable (pushPop u u' v' v)] (R : ℕ) :
    DecidableRel (balancedCircuitFin start accept stay pushPop R).orChild :=
  inferInstanceAs (DecidableRel ((balancedCircuit start accept stay pushPop R).reindex _).orChild)

/-- The output gate index of `balancedCircuitFin`. -/
def balancedOutputGate (S R : ℕ) : Fin (balancedGateCount S R) :=
  balancedGateEquivFin S R .output

theorem balancedCircuitFin_inNormalForm {S : ℕ} (start : Fin S) (accept : Fin S → Prop)
    (stay : Fin S → Fin S → Prop) (pushPop : Fin S → Fin S → Fin S → Fin S → Prop) (R : ℕ) :
    (balancedCircuitFin start accept stay pushPop R).InNormalForm :=
  LayeredSemiUnboundedCircuit.reindex_inNormalForm
    (balancedCircuit_inNormalForm start accept stay pushPop R) _

theorem balancedCircuitFin_andLevel_le {S : ℕ} (start : Fin S) (accept : Fin S → Prop)
    (stay : Fin S → Fin S → Prop) (pushPop : Fin S → Fin S → Fin S → Fin S → Prop) (R : ℕ)
    (g : Fin (balancedGateCount S R)) :
    (balancedCircuitFin start accept stay pushPop R).andLevel g ≤ R + 2 := by
  have h := balancedCircuit_andLevel_le start accept stay pushPop R
    ((balancedGateEquivFin S R).symm g)
  simpa only [balancedCircuitFin, LayeredSemiUnboundedCircuit.andLevel,
    LayeredSemiUnboundedCircuit.reindex] using h

theorem balancedCircuitFin_eval_output_sound {S : ℕ} {start : Fin S} {accept : Fin S → Prop}
    {stay : Fin S → Fin S → Prop} {pushPop : Fin S → Fin S → Fin S → Fin S → Prop} {R : ℕ}
    (h : (balancedCircuitFin start accept stay pushPop R).Eval (balancedOutputGate S R)) :
    ∃ v, accept v ∧ Nonempty (RealTree stay pushPop start v) :=
  balancedCircuit_eval_output_sound
    ((LayeredSemiUnboundedCircuit.reindex_eval_iff _ (balancedGateEquivFin S R) .output).mp h)

theorem balancedCircuitFin_eval_output_complete {S : ℕ} {start : Fin S} {accept : Fin S → Prop}
    {stay : Fin S → Fin S → Prop} {pushPop : Fin S → Fin S → Fin S → Fin S → Prop} {R sz : ℕ}
    (hR : roundsForSize sz ≤ R) {v : Fin S} (hacc : accept v)
    (T : RealTree stay pushPop start v) (hsz : T.size ≤ sz) :
    (balancedCircuitFin start accept stay pushPop R).Eval (balancedOutputGate S R) :=
  (LayeredSemiUnboundedCircuit.reindex_eval_iff _ (balancedGateEquivFin S R) .output).mpr
    (balancedCircuit_eval_output_complete hR hacc T hsz)

end Cslib.Circuits.Boolean
