/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Boolean.LocalValueGame.Formula
public import CslibFrontier.Computability.Circuit.Boolean.CarryLookahead.Query.Counting
public import
  CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.FastContraction.SignedRouting

/-!
# One Boolean value game for a reduced polynomial product

The finishing carry-lookahead adder, the complete signed carry-save tree, and its operand-bit
ports form one local Boolean decoder. Addresses store structural queries and local formulas.
The constructed root and source references use bounded templates; the raw address type also
admits other formulas. Neither a polynomial nor an exponentially large row is stored in an address.

For a coefficient index below the modulus degree, the root game computes a specified bit of
the product reduced modulo the sparse trinomial.
Its gate rank is logarithmic in the modulus degree and coefficient precision. This is the
semantic circuit fragment of the counting simulation in #4728. Native encodings, persistent
navigation, and their cumulative machine-time bounds remain separate obligations; polynomial
coefficient bits at terminal gates are not supplied as free machine operations.
-/

public section

namespace Cslib.Circuits.Frontier.FastContraction.SignedValueGame

open Polynomial BitString Boolean LocalValueGame SparseTrinomial

/-- The finishing adder, a carry-save subtree, or one signed operand/correction port. -/
inductive Node where
  /-- A wire of the finishing carry-lookahead adder. -/
  | finish (address : CarryLookahead.Query.Address)
  /-- One component bit of a carry-save subtree. -/
  | tree (query : CarrySaveQuery.Query)
  /-- One of the seven signed leaf ports, addressed without either operand word. -/
  | port (path : List Bool) (carry : Bool) (bit : ℕ) (index : Fin 7)
  deriving DecidableEq

/-- A structural macro query and a local formula; constructed roots use the fragment template. -/
abbrev Address := FormulaExpansion.Address Node 7

/-- The height of the signed diagonal and partial-product tree. -/
@[expose] def height (q p : ℕ) : ℕ := Nat.clog 2 (2 * q) + Nat.clog 2 p + 2

/-- The number of parallel-prefix rounds in the finishing adder. -/
@[expose] def rounds (p : ℕ) : ℕ := Nat.clog 2 (p + 1)

/-- The two carry-save components of the signed coefficient sum. -/
private noncomputable def pair {p : ℕ} (q i : ℕ) (u v : (ZMod (2 ^ p))[X]) :
    BitString (p + p) :=
  CarrySaveQuery.tree (reducedLeaves q i u v) (height q p) []

/-- The carry-save components followed by the zero incoming carry. -/
private noncomputable def adderInput {p : ℕ} (q i : ℕ) (u v : (ZMod (2 ^ p))[X]) :
    BitString (p + p + 1) :=
  Fin.append (Fin.append (CarrySaveQuery.component (pair q i u v) false)
    (CarrySaveQuery.component (pair q i u v) true)) ![false]

/-- The finishing adder with placeholder input bits. Its internal gates are input-independent. -/
@[expose] def finishDecoder (p : ℕ) : Decoder CarryLookahead.Query.Address :=
  CarryLookahead.Query.decoder p (rounds p) (fun _ => false)

/-- The fixed local formula of one Boolean operation, using its first two ports. -/
@[expose] def operationFormula : Op → Formula signature 7
  | .const b => Formula.const b
  | .not => (Formula.input 0).not
  | .and => (Formula.input 0).and (.input 1)
  | .or => (Formula.input 0).or (.input 1)

/-- The two operand bits, with the local two's-complement sign correction. -/
private def signedFormula : Formula signature 7 :=
  ((Formula.input 0).and (.input 1)).xor (.input 2)

/-- The operand-independent local formula. Ports are placeholders; a containing circuit
replaces them by the routed operand query or its local sign correction. -/
@[expose] def template (p : ℕ) : Node → Formula signature 7
  | .finish (.input j) => if j < p + p then .input 0 else Formula.const false
  | .finish a => operationFormula ((finishDecoder p).op a)
  | .tree a => if a.bit < p then
      if a.remaining = 0 then ((Formula.input 0).and (.input 1)).xor (.input 2)
      else CarrySaveLocal.formula a.carry
      else Formula.const false
  | .port _ _ _ _ => Formula.const false

private noncomputable def formula {p : ℕ} (q i : ℕ) (u v : (ZMod (2 ^ p))[X]) :
    Node → Formula signature 7
  | .port path carry bit j => Formula.const
      (if bit < p then signedBit u v q i path bit carry j else false)
  | a => template p a

/-- The internal adder references of a finishing-adder node. -/
@[expose] def finishSource (p : ℕ) (a : CarryLookahead.Query.Address) (j : Fin 7) : Option Node :=
  match (finishDecoder p).op a with
  | .const _ => none
  | .not => if j = 0 then some (.finish ((finishDecoder p).child a false)) else none
  | .and | .or => if j = 0 then some (.finish ((finishDecoder p).child a false))
      else if j = 1 then some (.finish ((finishDecoder p).child a true)) else none

/-- Internal references of the signed fragment, independent of the operand values. -/
@[expose] def source (q p : ℕ) : Node → Fin 7 → Option Node
  | .finish (.input j), port =>
      if j < p + p ∧ port = 0 then
        some (.tree ⟨[], height q p, decide (p ≤ j), if p ≤ j then j - p else j⟩)
      else none
  | .finish a, port => finishSource p a port
  | .tree a, port => if a.bit < p then
      if a.remaining = 0 then some (.port a.path a.carry a.bit port)
      else (CarrySaveQuery.descend a port).map Node.tree
      else none
  | .port _ _ _ _, _ => none

/-- The Boolean value of each signed-product macro node. -/
@[expose] noncomputable def nodeValue {p : ℕ} (q i : ℕ)
    (u v : (ZMod (2 ^ p))[X]) : Node → Bool
  | .finish a =>
      let components := CarrySaveQuery.tree (reducedLeaves q i u v) (height q p) []
      CarryLookahead.Query.value p (rounds p)
        (Fin.append (Fin.append (CarrySaveQuery.component components false)
          (CarrySaveQuery.component components true)) ![false]) a
  | .tree a => CarrySaveQuery.value (reducedLeaves q i u v) a
  | .port path carry bit j => if bit < p then signedBit u v q i path bit carry j else false

/-- Internal macro rank; every port is at rank zero. -/
@[expose] def nodeRank (q p : ℕ) : Node → ℕ
  | .finish a => height q p + 2 + CarryLookahead.Query.rank (rounds p) a
  | .tree a => a.remaining + 1
  | .port _ _ _ _ => 0

/-- Local gate access to the entire signed product, from the finishing adder to operand bits. -/
noncomputable def decoder {p : ℕ} (q i : ℕ) (u v : (ZMod (2 ^ p))[X]) :
    Decoder Address :=
  FormulaExpansion.decoder (formula q i u v) (source q p)

/-- The root address for a valid coefficient bit. Precision zero has no such bit. -/
noncomputable def root {p : ℕ} (q i : ℕ) (u v : (ZMod (2 ^ p))[X])
    (bit : Fin p) : Address :=
  FormulaExpansion.root (formula q i u v) (.finish (.sum bit.val))

/-- Boolean meaning of every local formula address in the unified product circuit. -/
noncomputable def value {p : ℕ} (q i : ℕ) (u v : (ZMod (2 ^ p))[X]) : Address → Bool :=
  FormulaExpansion.value (source q p) (nodeValue q i u v)

/-- A proof-only gate rank, with thirteen steps allowed per macro-node rank. -/
def rank (q p : ℕ) : Address → ℕ :=
  FormulaExpansion.rank 12 (nodeRank q p)

/-- Every operand-independent local template has bounded Boolean depth. -/
theorem template_depth (p : ℕ) (a : Node) : (template p a).depth ≤ 12 := by
  have hop (op : Op) : (operationFormula op).depth ≤ 12 := by
    cases op <;> simp [operationFormula]
  cases a with
  | finish a =>
    cases a <;> simp only [template]
    · split <;> decide
    all_goals exact hop _
  | tree a =>
    simp only [template]
    split
    · split
      · change signedFormula.depth ≤ 12
        decide
      · exact CarrySaveLocal.depth_formula_le _
    · decide
  | port path carry bit j => simp [template, Formula.depth_const]

private theorem formula_depth {p : ℕ} (q i : ℕ) (u v : (ZMod (2 ^ p))[X]) (a : Node) :
    (formula q i u v a).depth ≤ 12 := by
  cases a with
  | finish a => simpa only [formula] using template_depth p (.finish a)
  | tree a => simpa only [formula] using template_depth p (.tree a)
  | port path carry bit j => simp [formula, Formula.depth_const]

/-- Every finishing-adder reference lowers its rank before entering a carry-save tree. -/
theorem finishSource_rank (q p : ℕ) (a : CarryLookahead.Query.Address) (j : Fin 7)
    (b : Node) (h : finishSource p a j = some b) : nodeRank q p b < nodeRank q p (.finish a) := by
  have hd := CarryLookahead.Query.descends p (rounds p) (fun _ => false)
  cases ho : (finishDecoder p).op a with
  | const bit => simp [finishSource, ho] at h
  | not =>
    simp only [finishSource, ho] at h
    split at h
    · cases h
      change (finishDecoder p).Descends (CarryLookahead.Query.rank (rounds p)) at hd
      have hlt := hd a false
      simp only [ho] at hlt
      simp only [nodeRank]
      omega
    · simp at h
  | and | or =>
    simp only [finishSource, ho] at h
    split at h
    · cases h
      change (finishDecoder p).Descends (CarryLookahead.Query.rank (rounds p)) at hd
      have hlt := hd a false
      simp only [ho] at hlt
      simp only [nodeRank]
      omega
    · split at h
      · cases h
        change (finishDecoder p).Descends (CarryLookahead.Query.rank (rounds p)) at hd
        have hlt := hd a true
        simp only [ho] at hlt
        simp only [nodeRank]
        omega
      · simp at h

/-- Every internal fragment reference lowers its macro rank. -/
theorem source_rank (q p : ℕ) (a : Node) (j : Fin 7) (b : Node)
    (h : source q p a j = some b) : nodeRank q p b < nodeRank q p a := by
  cases a with
  | finish a =>
    cases a
    case input k =>
      simp only [source] at h
      split at h
      · cases h
        simp [nodeRank, CarryLookahead.Query.rank]
      · simp at h
    all_goals exact finishSource_rank q p _ j b h
  | tree a =>
    simp only [source] at h
    split at h
    · split at h
      · cases h
        simp [nodeRank]
      · cases hd : CarrySaveQuery.descend a j with
        | none => simp [hd] at h
        | some a' =>
          simp only [hd, Option.map_some, Option.some.injEq] at h
          subst b
          have hh := CarrySaveQuery.descend_remaining hd
          simp only [nodeRank]
          omega
    · simp at h
  | port path carry bit k => simp [source] at h

/-- Every used Boolean gate edge decreases rank, on all addresses and all input widths. -/
theorem descends {p : ℕ} (q i : ℕ) (u v : (ZMod (2 ^ p))[X]) :
    (decoder q i u v).Descends (rank q p) :=
  FormulaExpansion.descends (formula q i u v) (source q p)
    (formula_depth q i u v) (source_rank q p)

/-- Reading the finishing input pair selects the corresponding root carry-save component;
the extra incoming carry and every out-of-range input are false. -/
theorem read_tree_input {p : ℕ} (leaves : List Bool → BitString (p + p)) (depth j : ℕ) :
    CarryLookahead.Query.readInput p
      (Fin.append (Fin.append (CarrySaveQuery.component (CarrySaveQuery.tree leaves depth []) false)
        (CarrySaveQuery.component (CarrySaveQuery.tree leaves depth []) true)) ![false]) j =
      if j < p + p then CarrySaveQuery.value leaves
        ⟨[], depth, decide (p ≤ j), if p ≤ j then j - p else j⟩ else false := by
  by_cases h₀ : j < p
  · simp [CarryLookahead.Query.readInput, Fin.append, Fin.addCases, h₀,
      show j < p + p by omega, show j < p + p + 1 by omega, Nat.not_le.mpr h₀,
      CarrySaveQuery.value]
  · by_cases h₁ : j < p + p
    · have hp : p ≤ j := by omega
      have hj : j - p < p := by omega
      simp [CarryLookahead.Query.readInput, Fin.append, Fin.addCases, h₀, h₁,
        show j < p + p + 1 by omega, hp, hj, CarrySaveQuery.value]
    · by_cases h₂ : j < p + p + 1
      · have he : j = p + p := by omega
        subst j
        simp [CarryLookahead.Query.readInput, Fin.append, Fin.addCases]
      · simp [CarryLookahead.Query.readInput, h₁, h₂]

private theorem finish_formula_value {p : ℕ} (q i : ℕ) (u v : (ZMod (2 ^ p))[X])
    (a : CarryLookahead.Query.Address) :
    (operationFormula ((finishDecoder p).op a)).eval interpretation
      (fun j => (finishSource p a j).elim false (nodeValue q i u v)) =
        (finishDecoder p).eval
          (CarryLookahead.Query.value p (rounds p) (adderInput q i u v)) a := by
  cases ho : (finishDecoder p).op a <;>
    simp [operationFormula, finishSource, ho, nodeValue, adderInput, pair, Decoder.eval]

/-- Away from input nodes the finishing decoder is independent of all input values. -/
theorem finish_eval_eq (p : ℕ) (input : BitString (p + p + 1))
    (values : CarryLookahead.Query.Address → Bool) (a : CarryLookahead.Query.Address)
    (ha : ∀ j, a ≠ .input j) :
    (finishDecoder p).eval values a =
      (CarryLookahead.Query.decoder p (rounds p) input).eval values a := by
  have ho : (finishDecoder p).op a =
      (CarryLookahead.Query.decoder p (rounds p) input).op a := by
    cases a <;> first | rfl | exact False.elim (ha _ rfl)
  simp only [Decoder.eval, ho]
  rfl

private theorem formula_value {p : ℕ} (q i : ℕ) (u v : (ZMod (2 ^ p))[X])
    (hv : v.natDegree < 2 * q) (a : Node) :
    nodeValue q i u v a = (formula q i u v a).eval interpretation
      (fun j => (source q p a j).elim false (nodeValue q i u v)) := by
  cases a with
  | finish a =>
    cases a
    case input j =>
      simp only [nodeValue, CarryLookahead.Query.value]
      rw [read_tree_input]
      by_cases hj : j < p + p <;> simp [formula, template, source, hj, nodeValue]
    all_goals
      simp only [formula, template, source]
      rw [finish_formula_value]
      rw [finish_eval_eq p (adderInput q i u v) _ _ (by intro j h; cases h)]
      simp only [nodeValue]
      exact CarryLookahead.Query.value_eq_eval p (rounds p) (adderInput q i u v) _
  | tree a =>
    rcases a with ⟨path, remaining, carry, bit⟩
    by_cases hb : bit < p
    · cases remaining with
      | zero =>
        have h := value_reduced_eq_gate u v q i hv path carry ⟨bit, hb⟩
        have hp (j : Fin 7) := value_port u v q i j path ⟨bit, hb⟩ carry
        simp only [signedGate, hp] at h
        simpa [nodeValue, formula, template, source, hb] using h
      | succ remaining =>
        have h := CarrySaveQuery.value_layer (reducedLeaves q i u v)
          path remaining carry ⟨bit, hb⟩
        rw [nodeValue, h]
        simp only [formula, template, source, hb, ↓reduceIte, Nat.add_eq_zero_iff, Nat.one_ne_zero,
          and_false]
        congr 1
        funext j
        cases he : CarrySaveQuery.descend ⟨path, remaining + 1, carry, bit⟩ j <;>
          simp [nodeValue]
    · simp [nodeValue, CarrySaveQuery.value, formula, template, source, hb]
  | port path carry bit j => simp [nodeValue, formula]

/-- Nonterminal fragment nodes satisfy their operand-independent local templates. Operand
ports are deliberately excluded: a containing circuit routes them to its own input queries. -/
theorem nodeValue_eq_template {p : ℕ} (q i : ℕ) (u v : (ZMod (2 ^ p))[X])
    (hv : v.natDegree < 2 * q) (a : Node)
    (ha : ∀ path carry bit j, a ≠ .port path carry bit j) :
    nodeValue q i u v a = (template p a).eval interpretation
      (fun j => (source q p a j).elim false (nodeValue q i u v)) := by
  cases a with
  | finish a => exact formula_value q i u v hv _
  | tree a => exact formula_value q i u v hv _
  | port path carry bit j => exact False.elim (ha path carry bit j rfl)

/-- The integrated semantic value satisfies every decoded local Boolean equation. -/
theorem value_eq_eval {p : ℕ} (q i : ℕ) (u v : (ZMod (2 ^ p))[X])
    (hv : v.natDegree < 2 * q) (a : Address) :
    value q i u v a = (decoder q i u v).eval (value q i u v) a :=
  FormulaExpansion.value_eq_eval (formula q i u v) (source q p) (nodeValue q i u v)
    (formula_value q i u v hv) a

private theorem value_root_eq_word {p : ℕ} (q i : ℕ) (u v : (ZMod (2 ^ p))[X])
    (hv : v.natDegree < 2 * q) (bit : Fin p) :
    value q i u v (root q i u v bit) =
      (carryLookaheadAdd p).eval interpretation (pair q i u v) bit := by
  rw [value, root, FormulaExpansion.value_root _ _ _ (formula_value q i u v hv)]
  exact CarryLookahead.Query.value_pair_sum_eq _ bit

/-- The root computes a bit of the sparse reduction expression, including negative diagonals
and modular underflow. At indices below `2*q`, this expression is the actual remainder
coefficient. Both polynomial operands have degree below the trinomial degree `2*q`. -/
theorem value_root_eq_reducedCoeff {p : ℕ} (q i : ℕ) (u v : (ZMod (2 ^ p))[X])
    (hu : u.natDegree < 2 * q) (hv : v.natDegree < 2 * q) (bit : Fin p) :
    value q i u v (root q i u v bit) = (reducedCoeff q (u * v).coeff i).val.testBit bit.val := by
  rw [value_root_eq_word q i u v hv bit]
  let word := (carryLookaheadAdd p).eval interpretation (pair q i u v)
  have h := congrArg ZMod.val (residue_reducedTree q i u v hu)
  change (CarrySaveQuery.SignedSum.residue word).val = _ at h
  simp only [CarrySaveQuery.SignedSum.residue, ZMod.val_natCast,
    Nat.mod_eq_of_lt (equivFin p word).isLt] at h
  exact (testBit_equivFin word bit).symm.trans (congrArg (fun n : ℕ => n.testBit bit.val) h)

/-- The complete Boolean game answers the sparse reduction expression for either claim. -/
theorem wins_root_iff {p : ℕ} (q i : ℕ) (u v : (ZMod (2 ^ p))[X])
    (hu : u.natDegree < 2 * q) (hv : v.natDegree < 2 * q)
    (enc : Claim Address ↪ List Bool) (bit : Fin p) (claim : Bool) :
    Turing.MultiTapeATM.WordGame.Wins (LocalValueGame.update (decoder q i u v) enc)
      (position (decoder q i u v) enc ⟨root q i u v bit, claim⟩) ↔
        (reducedCoeff q (u * v).coeff i).val.testBit bit.val = claim := by
  rw [wins_position_iff (descends q i u v) (value q i u v) (value_eq_eval q i u v hv),
    value_root_eq_reducedCoeff q i u v hu hv]

/-- Every play ends within an explicit logarithmic gate budget. This counts Boolean moves,
not native tape instructions or the time required to obtain terminal coefficient bits. -/
theorem ends_root {p : ℕ} (q i : ℕ) (u v : (ZMod (2 ^ p))[X])
    (enc : Claim Address ↪ List Bool) (bit : Fin p) (claim : Bool) :
    Turing.MultiTapeATM.WordGame.Ends (LocalValueGame.update (decoder q i u v) enc)
      (13 * (Nat.clog 2 (2 * q) + Nat.clog 2 p + 2 * Nat.clog 2 (p + 1) + 10) + 12)
      (position (decoder q i u v) enc ⟨root q i u v bit, claim⟩) := by
  refine Turing.MultiTapeATM.WordGame.Ends.mono ?_
    (ends_position (encC := enc) (descends q i u v)
      (⟨root q i u v bit, claim⟩ : Claim Address))
  have hd := formula_depth q i u v (.finish (.sum bit.val))
  simp only [rank, FormulaExpansion.rank, root, FormulaExpansion.root, nodeRank,
    CarryLookahead.Query.rank, height, rounds]
  omega

/-- The reusable fragment's finishing node reads the selected bit of the extension-ring
product; its operands may therefore be supplied recursively by a larger circuit. -/
theorem nodeValue_product (m p : ℕ) (x y : GaloisRingArith.Ring p (modulus m))
    (i : Fin (modulus m).length) (bit : Fin p) :
    nodeValue (3 ^ modulusExp m) i.val (representative m p x) (representative m p y)
      (.finish (.sum bit.val)) =
        ((representative m p (x * y)).coeff i.val).val.testBit bit.val := by
  simp only [nodeValue, rounds]
  rw [CarryLookahead.Query.value_pair_sum_eq]
  exact bit_reducedTree m p x y i bit

/-- Specializing the unified game to representatives gives the corresponding extension-ring
product bit. The same decoder handles the two's-complement corrections internally. -/
theorem wins_product_iff (m p : ℕ) (x y : GaloisRingArith.Ring p (modulus m))
    (i : Fin (modulus m).length) (bit : Fin p) (claim : Bool)
    (enc : Claim Address ↪ List Bool) :
    let q := 3 ^ modulusExp m
    let u := representative m p x
    let v := representative m p y
    Turing.MultiTapeATM.WordGame.Wins (LocalValueGame.update (decoder q i.val u v) enc)
      (position (decoder q i.val u v) enc ⟨root q i.val u v bit, claim⟩) ↔
        ((representative m p (x * y)).coeff i.val).val.testBit bit.val = claim := by
  intro q u v
  have hv : v.natDegree < 2 * q := by
    simpa only [v, q, length_modulus] using natDegree_representative_lt m p y
  rw [wins_position_iff (descends q i.val u v) (value q i.val u v)
    (value_eq_eval q i.val u v hv), value_root_eq_word q i.val u v hv]
  have h := bit_reducedTree m p x y i bit
  change (carryLookaheadAdd p).eval interpretation (pair q i.val u v) bit = _ at h
  rw [h]

end Cslib.Circuits.Frontier.FastContraction.SignedValueGame
