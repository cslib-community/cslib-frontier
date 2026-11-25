/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Cuts.Law
public import CslibFrontier.Foundations.Combinatorics.CoveringTower.Load
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators

/-!
# The relay law and the laws at the vertices of a tower

The moves of the tower plan of [AnthropicVPVNP2026] (Theorem H.2; module `Nc.Tow.Relay`) are of
two kinds, and this file has their laws. A *relay* leads a bit shared by two roles through a
third role: it is the law `relayLaw`. A *law move* applies, at a vertex of a covering tower, one
of finitely many laws whose roles are the places at the vertex and whose channels are the near
pairs: these are the `VertexLaws` of a tower, with the constants that the bounds for the loads
need.

## Main definitions

* `RelayRole`, `RelayRole.elim`: the three roles of a relay, and functions on them.
* `relaySlotEnd`, `relayChannelEnd`, `relayTable`, `relayLaw`: the relay.
* `VertexLaws`, with `VertexLaws.slotPair` and `VertexLaws.slotCount`: the laws at the vertices
  of a tower, the pair of places at the ends of a slot, and the number of slots on a pair.

## Main results

* `RelayRole.elim_injective`, `RelayRole.prod_univ`, `RelayRole.sum_univ`: three different values
  give an injective function on the roles, and a product and a sum over the roles.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Appendix H.2 (the two moves) and Theorem H.2; module `Nc.Tow.Relay`
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.TowerPlan

open Finset Cslib.CoveringTower Cut

section Relay

/-- The roles of a relay: a bit shared by `source` and `sink` is led through `via`. -/
inductive RelayRole where
  /-- the first end of the shared bit -/
  | source
  /-- the role in between -/
  | via
  /-- the second end of the shared bit -/
  | sink
  deriving DecidableEq

instance : Fintype RelayRole := ⟨{.source, .via, .sink}, fun x => by cases x <;> simp⟩

namespace RelayRole

/-- The function on the roles of a relay with the values `x`, `y`, `z`. -/
@[expose] def elim {α : Type*} (x y z : α) : RelayRole → α
  | source => x
  | via => y
  | sink => z

theorem elim_injective {α : Type*} {x y z : α} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    Function.Injective (elim x y z) := by
  intro i j h
  cases i <;> cases j <;> simp_all [elim, eq_comm]

@[to_additive]
theorem prod_univ {M : Type*} [CommMonoid M] (f : RelayRole → M) :
    ∏ p, f p = f source * f via * f sink := by
  rw [show (Finset.univ : Finset RelayRole) = {source, via, sink} from rfl]
  simp [mul_assoc]

end RelayRole

/-- The roles at the ends of the slot of a relay: the bit is shared by `source` and `sink`. -/
@[expose] def relaySlotEnd (_ : Unit) (d : Bool) : RelayRole := bif d then .sink else .source

/-- The roles at the ends of the two channels of a relay: the channel `false` joins `source` and
`via`, and the channel `true` joins `via` and `sink`. -/
@[expose] def relayChannelEnd (ν d : Bool) : RelayRole :=
  bif ν then (bif d then .sink else .via) else (bif d then .via else .source)

variable (F : Type*) [CommSemiring F]

/-- The tables of a relay: `source` and `sink` compare their copy of the bit with the bit on
their channel, and `via` compares the bits on its two channels. -/
@[expose] def relayTable : (p : RelayRole) → ({e : Unit // Play.Holds relaySlotEnd p e} → Bool) →
    ((ν : {ν : Bool // Play.Holds relayChannelEnd p ν}) → BitString 1) → F
  | .source, X, g => if X ⟨(), false, rfl⟩ = g ⟨false, false, rfl⟩ 0 then 1 else 0
  | .via, _, g => if g ⟨false, true, rfl⟩ 0 = g ⟨true, false, rfl⟩ 0 then 1 else 0
  | .sink, X, g => if g ⟨true, true, rfl⟩ 0 = X ⟨(), true, rfl⟩ then 1 else 0

/-- The relay: a bit shared by `source` and `sink` is led through `via`. There is one index, and
each of the two channels carries one bit. -/
@[expose] def relayLaw : Law F where
  Role := RelayRole
  Slot := Unit
  Channel := Bool
  Index := Unit
  slotEnd := relaySlotEnd
  slotEnd_ne := by decide
  channelEnd := relayChannelEnd
  channelEnd_ne := by decide
  labelLength := 0
  label _ := Fin.elim0
  label_injective _ _ _ := rfl
  length _ _ := 1
  table p _ := relayTable F p
  identity X := by
    rw [Fintype.sum_unique, ← ((Equiv.piCongrRight fun _ : Bool =>
      Equiv.funUnique (Fin 1) Bool).trans (Equiv.boolArrowEquivProd Bool)).symm.sum_comp,
      Fintype.sum_prod_type]
    rcases Bool.eq_false_or_eq_true (X .source ()) with h0 | h0 <;>
      rcases Bool.eq_false_or_eq_true (X .sink ()) with h2 | h2 <;>
      simp [RelayRole.prod_univ, relayTable, relaySlotEnd, Equiv.boolArrowEquivProd, h0, h2]
  connected _ _ _ _ := rfl

end Relay

variable {h b D J r : ℕ}

/-- The laws at the vertices of a tower: finitely many kinds of laws whose roles are the places
at a vertex and whose channels are the near pairs, with the constants of their bounds. -/
structure VertexLaws (F : Type*) [CommSemiring F] (T : Tower h b D J r) where
  /-- The kinds of laws. -/
  Kind : Type
  [fintypeKind : Fintype Kind]
  [decEqKind : DecidableEq Kind]
  /-- The law of a kind. -/
  law : Kind → Law F
  /-- The roles of a law are the places at a vertex. -/
  place : ∀ d, (law d).Role ≃ T.Fl
  /-- The channels of a law are the near pairs. -/
  nearPair : ∀ d, (law d).Channel ≃ T.Nr
  place_channelEnd : ∀ d ν, s(place d ((law d).channelEnd ν false),
    place d ((law d).channelEnd ν true)) = s(T.cN (nearPair d ν), T.dN (nearPair d ν))
  labelLength_pos : ∀ d, 1 ≤ (law d).labelLength
  nonempty_index : ∀ d, Nonempty (law d).Index
  /-- The scale: a load of norm at most `scale * t` fits into `t` units at every slot of some
  law. -/
  scale : ℕ
  scale_pos : 0 < scale
  /-- The constant of the contraction. -/
  contraction : ℝ
  contraction_nonneg : 0 ≤ contraction
  /-- The bound for the squares of the lengths of the strings: the integer form of the
  constant. -/
  lengthBound : ℕ
  lengthBound_le : (lengthBound : ℝ) ≤ 2 * contraction * (scale : ℝ) ^ 2
  /-- Every load on the pairs of places is below the slots of one of the laws. -/
  exists_le_card_slot : ∀ (n : Sym2 T.Fl → ℕ) (t : ℕ), √(T.NN2 n) ≤ (scale : ℝ) * t →
    ∃ d, ∀ q : Sym2 T.Fl, ¬ q.IsDiag → n q ≤ (univ.filter fun e : (law d).Slot =>
      s(place d ((law d).slotEnd e false), place d ((law d).slotEnd e true)) = q).card * t
  /-- The strings of the laws are short. -/
  sum_length_sq_le : ∀ d i,
    r * b * ∑ ν, ((law d).labelLength + (law d).length i ν) ^ 2 ≤ lengthBound

attribute [instance] VertexLaws.fintypeKind VertexLaws.decEqKind

namespace VertexLaws

variable {F : Type*} [CommSemiring F] {T : Tower h b D J r} (FL : VertexLaws F T)

/-- The pair of places at the two ends of a slot. -/
@[expose] def slotPair (d : FL.Kind) (e : (FL.law d).Slot) : Sym2 T.Fl :=
  s(FL.place d ((FL.law d).slotEnd e false), FL.place d ((FL.law d).slotEnd e true))

/-- The number of slots on a pair of places. -/
@[expose] def slotCount (d : FL.Kind) (q : Sym2 T.Fl) : ℕ :=
  (univ.filter fun e : (FL.law d).Slot => FL.slotPair d e = q).card

end VertexLaws

end Cslib.Circuits.Arithmetic.Separation.TowerPlan
