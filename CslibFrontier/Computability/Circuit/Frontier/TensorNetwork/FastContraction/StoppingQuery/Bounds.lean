/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import
  CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.FastContraction.StoppingQuery.Rank
public import
  CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.FastContraction.SignedValueGame.Bounds

/-!
# Bounded navigation through a stopping product

A product query retains its assignment and descends through consecutive subblocks of a fixed
vertex interval. The level, coefficient, precision bit and multiplier address stay bounded.
No source can return to the outer assignment sum. These are address invariants for the native
short-metadata traversal; the assignment may be retained separately from that metadata.
-/

public section

namespace Cslib.Circuits.Frontier.FastContraction.StoppingQuery

open Boolean LocalValueGame

/-- A stopping-product macro within a fixed vertex interval and height. The terminal includes
the network bound as well as the interval bound; padded vertices never issue entry requests. -/
@[expose] def ProductWellFormed (m p vertices assignment limit levels : ℕ) : Node → Prop
  | .sum _ _ | .sumTree _ _ => False
  | .product a base level coefficient node =>
      a = assignment ∧ base + 2 ^ (level + 1) ≤ limit ∧ level + 1 ≤ levels ∧
        coefficient < (modulus m).length ∧
          SignedValueGame.WellFormed (3 ^ modulusExp m) p node
  | .value a base level coefficient bit =>
      a = assignment ∧ base + 2 ^ level ≤ limit ∧ level ≤ levels ∧
        coefficient < (modulus m).length ∧ bit < p
  | .entry e =>
      e.assignment = assignment ∧ e.vertex < vertices ∧ e.vertex < limit ∧
        e.coefficient < (modulus m).length ∧ e.bit < p

/-- Every source of a bounded product preserves its assignment, interval and short arithmetic
fields. In particular it never enters either outer-sum node constructor. -/
theorem ProductWellFormed.source {m p edges vertices assignment limit levels : ℕ} {a : Node}
    (ha : ProductWellFormed m p vertices assignment limit levels a) (port : Fin 7) (b : Node)
    (h : source m p edges vertices a port = some b) :
    ProductWellFormed m p vertices assignment limit levels b := by
  cases a with
  | sum coefficient a | sumTree coefficient a => exact ha.elim
  | product a base level coefficient node =>
    obtain ⟨hassign, hbase, hlevel, hcoefficient, hnode⟩ := ha
    have hpow : 2 ^ (level + 1) = 2 ^ level + 2 ^ level := by omega
    cases node with
    | port path carry bit index =>
      simp only [StoppingQuery.source] at h
      split at h
      · split at h
        · obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.mp h
          have hb := ConvolutionOperand.Signed.source_bounds hj
          simp only [operandQuery, ← length_modulus] at hb
          exact ⟨hassign, (Nat.add_le_add_left (Nat.pow_le_pow_right (by decide : 0 < 2)
            (Nat.le_succ level)) base).trans hbase, by omega, hb⟩
        · split at h
          · obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.mp h
            have hb := ConvolutionOperand.Signed.source_bounds hj
            simp only [operandQuery, ← length_modulus] at hb
            exact ⟨hassign, by simpa only [hpow, Nat.add_assoc] using hbase, by omega, hb⟩
          · simp at h
      · simp at h
    | finish a | tree a =>
      simp only [StoppingQuery.source] at h
      obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp h
      exact ⟨hassign, hbase, hlevel, hcoefficient, hnode.source port c hc⟩
  | value a base level coefficient bit =>
    obtain ⟨hassign, hbase, hlevel, hcoefficient, hbit⟩ := ha
    cases level with
    | zero =>
      simp only [StoppingQuery.source] at h
      split at h
      · rename_i hg
        cases h
        exact ⟨hassign, hg.2.2.2, by simpa using hbase, hcoefficient, hbit⟩
      · simp at h
    | succ level =>
      simp only [StoppingQuery.source] at h
      split at h
      · cases h
        exact ⟨hassign, hbase, hlevel, hcoefficient, hbit⟩
      · simp at h
  | entry e => simp [StoppingQuery.source] at h

/-- A Boolean child changes only the local formula or follows a source. Both preserve the
product invariant, independently of the values supplied at entry terminals. -/
theorem ProductWellFormed.child {m p edges vertices assignment limit levels : ℕ}
    {a : Address} (ha : ProductWellFormed m p vertices assignment limit levels a.node)
    (input : Entry → Bool) (b : Bool) :
    ProductWellFormed m p vertices assignment limit levels
      ((decoder m p edges vertices input).child a b).node := by
  rcases a with ⟨node, formula⟩
  cases formula with
  | input i =>
    cases hs : StoppingQuery.source m p edges vertices node i with
    | none => simpa [decoder, FormulaExpansion.decoder, hs] using ha
    | some n =>
      simpa only [decoder, FormulaExpansion.decoder, hs, Option.elim_some,
        FormulaExpansion.root] using ha.source i n hs
  | gate op args => cases op <;> exact ha

end Cslib.Circuits.Frontier.FastContraction.StoppingQuery
