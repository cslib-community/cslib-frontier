/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import
  CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.FastContraction.StoppingQuery

/-!
# Depth of the stopping contraction circuit

The assignment sum contributes one carry-save level per edge. Each balanced vertex-product
level contributes the depth of one signed extension-ring multiplier. An explicit rank proves
termination for every address, including malformed addresses, and bounds the root by a quantity
linear in the number of edges and logarithmic in the vertex count times the multiplication
depth. This counts Boolean moves; native navigation and entry-access clocks are separate.
-/

public section

namespace Cslib.Circuits.Frontier.FastContraction.StoppingQuery

open Boolean LocalValueGame

private def productSpan (m p : ℕ) : ℕ :=
  SignedValueGame.height (3 ^ modulusExp m) p + 2 * SignedValueGame.rounds p + 11

private def nodeRank (m p edges vertices : ℕ) : Node → ℕ
  | .sum _ a => Nat.clog 2 vertices * productSpan m p + edges + 3 +
      CarryLookahead.Query.rank (SignedValueGame.rounds p) a
  | .sumTree _ a => Nat.clog 2 vertices * productSpan m p + a.remaining + 2
  | .product _ _ level _ a => level * productSpan m p + 2 +
      SignedValueGame.nodeRank (3 ^ modulusExp m) p a
  | .value _ _ level _ _ => level * productSpan m p + 1
  | .entry _ => 0

/-- The expanded circuit rank pays for one bounded formula between successive macro nodes. -/
def rank (m p edges vertices : ℕ) : Address → ℕ :=
  FormulaExpansion.rank 12 (nodeRank m p edges vertices)

/-- Every local template has depth at most twelve, independently of all circuit parameters. -/
theorem template_depth (m p edges vertices : ℕ) (a : Node) :
    (template m p edges vertices a).depth ≤ 12 := by
  cases a with
  | sum coefficient a => exact SignedValueGame.template_depth p (.finish a)
  | sumTree coefficient a =>
    simp only [template]
    split
    · split
      · split <;> decide
      · exact CarrySaveLocal.depth_formula_le _
    · decide
  | product assignment base level coefficient a =>
    cases a with
    | finish a => exact SignedValueGame.template_depth p (.finish a)
    | tree a => exact SignedValueGame.template_depth p (.tree a)
    | port path carry bit index =>
      simp only [template]
      split
      · split <;> simp
      · decide
  | value assignment base level coefficient bit =>
    cases level <;> simp only [template]
    · split
      · split <;> simp
      · decide
    · split <;> decide
  | entry e => simp [template]

private theorem sumSource_rank (m p edges vertices coefficient : ℕ)
    (a : CarryLookahead.Query.Address) (port : Fin 7) (b : Node)
    (h : sumSource p coefficient a port = some b) :
    nodeRank m p edges vertices b < nodeRank m p edges vertices (.sum coefficient a) := by
  simp only [sumSource, Option.bind_eq_some_iff] at h
  obtain ⟨c, hc, hb⟩ := h
  cases c with
  | finish c =>
    cases hb
    have hs := SignedValueGame.finishSource_rank (3 ^ modulusExp m) p a port (.finish c) hc
    simp only [nodeRank, SignedValueGame.nodeRank] at *
    omega
  | tree c => simp at hb
  | port path carry bit index => simp at hb

private theorem source_rank (m p edges vertices : ℕ) (a : Node) (port : Fin 7) (b : Node)
    (h : source m p edges vertices a port = some b) :
    nodeRank m p edges vertices b < nodeRank m p edges vertices a := by
  cases a with
  | sum coefficient a =>
    cases a
    case input j =>
      simp only [source] at h
      split at h
      · cases h
        simp [nodeRank, CarryLookahead.Query.rank]
      · simp at h
    all_goals exact sumSource_rank m p edges vertices coefficient _ port b h
  | sumTree coefficient a =>
    simp only [source] at h
    split at h
    · split at h
      · rename_i hz
        split at h
        · cases h
          simp [nodeRank, hz]
        · simp at h
      · cases hd : CarrySaveQuery.descend a port with
        | none => simp [hd] at h
        | some c =>
          simp only [hd, Option.map_some, Option.some.injEq] at h
          subst b
          have hh := CarrySaveQuery.descend_remaining hd
          simp only [nodeRank]
          omega
    · simp at h
  | product assignment base level coefficient a =>
    cases a with
    | port path carry bit index =>
      simp only [source] at h
      split at h
      · split at h
        · cases hs : ConvolutionOperand.Signed.source
              (operandQuery m p coefficient path carry bit false) with
          | none => simp [hs] at h
          | some j =>
            simp only [hs, Option.map_some, Option.some.injEq] at h
            subst b
            simp [nodeRank, SignedValueGame.nodeRank]
        · split at h
          · cases hs : ConvolutionOperand.Signed.source
                (operandQuery m p coefficient path carry bit true) with
            | none => simp [hs] at h
            | some j =>
              simp only [hs, Option.map_some, Option.some.injEq] at h
              subst b
              simp [nodeRank, SignedValueGame.nodeRank]
          · simp at h
      · simp at h
    | finish a | tree a =>
      simp only [source] at h
      obtain ⟨c, hc, hb⟩ := Option.map_eq_some_iff.mp h
      subst b
      have hh := SignedValueGame.source_rank (3 ^ modulusExp m) p _ port c hc
      simp only [nodeRank]
      omega
  | value assignment base level coefficient bit =>
    cases level with
    | zero =>
      simp only [source] at h
      split at h
      · cases h
        simp [nodeRank]
      · simp at h
    | succ level =>
      simp only [source] at h
      split at h
      · cases h
        simp only [nodeRank, SignedValueGame.nodeRank, CarryLookahead.Query.rank,
          Nat.add_mul, productSpan]
        omega
      · simp at h
  | entry e => simp [source] at h

/-- Every Boolean edge used by the stopping circuit strictly lowers its rank. The bound holds
for arbitrary terminal interpretations and arbitrary addresses. -/
theorem descends (m p edges vertices : ℕ) (input : Entry → Bool) :
    (decoder m p edges vertices input).Descends (rank m p edges vertices) := by
  have h := FormulaExpansion.descends (template m p edges vertices)
    (source m p edges vertices) (template_depth m p edges vertices)
    (source_rank m p edges vertices)
  intro a b
  cases he : inputLabel a with
  | none => simpa only [decoder, operation, he, Sum.elim_inr, id_eq, rank] using h a b
  | some e => simp only [decoder, operation, he, Sum.elim_inl]

/-- Starting at a balanced block has a rank linear in its height and the signed multiplier
depth, independently of the assignment and the number of summed assignments. -/
theorem rank_block_root_le (m p edges vertices assignment base level coefficient bit : ℕ) :
    rank m p edges vertices (FormulaExpansion.root (template m p edges vertices)
      (.value assignment base level coefficient bit)) ≤
        13 * (level * (SignedValueGame.height (3 ^ modulusExp m) p +
          2 * SignedValueGame.rounds p + 11) + 1) + 12 := by
  have h := template_depth m p edges vertices (.value assignment base level coefficient bit)
  simpa only [rank, FormulaExpansion.rank, FormulaExpansion.root, nodeRank, productSpan,
    Nat.reduceAdd] using Nat.add_le_add_left h _

/-- Every play from the output ends within the stated gate budget. This includes arithmetic
navigation but does not charge native tape instructions or evaluation of a terminal input. -/
theorem ends_root (m p edges vertices : ℕ) (input : Entry → Bool)
    (coefficient : Fin (modulus m).length) (bit : Fin p) (claim : Bool)
    (enc : Claim Address ↪ List Bool) :
    Turing.MultiTapeATM.WordGame.Ends
      (LocalValueGame.update (decoder m p edges vertices input) enc)
      (13 * (Nat.clog 2 vertices * (SignedValueGame.height (3 ^ modulusExp m) p +
        2 * SignedValueGame.rounds p + 11) + edges + 2 * SignedValueGame.rounds p + 9) + 12)
      (position (decoder m p edges vertices input) enc
        ⟨root m p edges vertices coefficient bit, claim⟩) := by
  refine Turing.MultiTapeATM.WordGame.Ends.mono ?_
    (ends_position (encC := enc) (descends m p edges vertices input)
      (⟨root m p edges vertices coefficient bit, claim⟩ : Claim Address))
  have hd := template_depth m p edges vertices (.sum coefficient.val (.sum bit.val))
  simp only [rank, FormulaExpansion.rank, root, FormulaExpansion.root, nodeRank,
    CarryLookahead.Query.rank, productSpan]
  omega

/-- The alternating Boolean game for the compiled stopping circuit checks the requested bit
of the actual described-network contraction. The entry labels have their exact ring meanings;
native implementation and cost of those input accesses are not assumed by this game theorem. -/
theorem wins_contraction_iff {T : Type} (m p : ℕ) (d : DescribedNetwork T)
    (eval : T → List Bool → GaloisRingArith.Ring p (modulus m))
    (coefficient : Fin (modulus m).length) (bit : Fin p) (claim : Bool)
    (enc : Claim Address ↪ List Bool) :
    let D := decoder m p d.numEdges d.vertices.length (entryBit m p (networkEntry d eval))
    Turing.MultiTapeATM.WordGame.Wins (LocalValueGame.update D enc)
      (position D enc ⟨root m p d.numEdges d.vertices.length coefficient bit, claim⟩) ↔
        ((representative m p (d.contraction eval)).coeff coefficient.val).val.testBit bit.val =
          claim := by
  intro D
  rw [wins_position_iff (descends m p d.numEdges d.vertices.length
    (entryBit m p (networkEntry d eval)))
      (value m p d.numEdges d.vertices.length (networkEntry d eval))
      (value_eq_eval m p d.numEdges d.vertices.length (networkEntry d eval)),
    value_root_contraction]

end Cslib.Circuits.Frontier.FastContraction.StoppingQuery
