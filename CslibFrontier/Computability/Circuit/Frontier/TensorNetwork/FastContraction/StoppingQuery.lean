/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import
  CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.FastContraction.SignedValueGame
public import
  CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.FastContraction.InterpolationSum
public import
  CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.FastContraction.StoppingQuery.Entry

/-!
# A succinct Boolean circuit for the stopping contraction

The assignment sum is a complete carry-save tree. Its leaves enter balanced products of the
vertex entries, and each product uses the existing signed sparse-trinomial multiplier. Addresses
store structural indices, paths and local formulas. Constructed roots and source references use
bounded templates; the raw address type also admits other formulas. Terminal input labels
name a bit of one vertex entry; no table, polynomial, assignment list or product value occurs in
an address. Identity padding handles every vertex count, including zero.

`operation` and `decoder.child` give local gate access without evaluating an entry. `decoder`
interprets the explicit terminal labels, and `value_root` identifies its output with the selected
representative coefficient bit of the actual sum of products. The specialization to a described
network is `value_root_contraction`. These semantic results do not assert the native cumulative
navigation bound required by the full circuit compiler.
-/

@[expose] public section

namespace Cslib.Circuits.Frontier.FastContraction.StoppingQuery

open Polynomial BitString Boolean LocalValueGame GaloisRingArith

/-- The assignment sum, a product fragment, a balanced value query, or an explicit input label. -/
inductive Node where
  /-- A finishing-adder gate for one coordinate of the assignment sum. -/
  | sum (coefficient : ℕ) (address : CarryLookahead.Query.Address)
  /-- A carry-save subtree of the assignment sum. -/
  | sumTree (coefficient : ℕ) (query : CarrySaveQuery.Query)
  /-- A signed multiplication fragment for two adjacent blocks of height `level`. -/
  | product (assignment base level coefficient : ℕ) (node : SignedValueGame.Node)
  /-- One representative bit of a balanced block of vertex entries. -/
  | value (assignment base level coefficient bit : ℕ)
  /-- A single bit of one original vertex entry. -/
  | entry (label : Entry)
  deriving DecidableEq

/-- A structural macro address and a local formula; constructed roots use the bounded template. -/
abbrev Address := FormulaExpansion.Address Node 7

/-- The router request for a signed product port. -/
def operandQuery (m p coefficient : ℕ) (path : List Bool) (carry : Bool) (bit : ℕ)
    (right : Bool) : ConvolutionOperand.Signed.Query :=
  ⟨3 ^ modulusExp m, p, coefficient, path, bit, carry, right⟩

/-- Local Boolean templates, independent of every vertex entry value. Entry templates are
placeholders: `operation` exposes their input label instead of interpreting this formula. -/
def template (m p edges vertices : ℕ) : Node → Formula signature 7
  | .sum _ a => SignedValueGame.template p (.finish a)
  | .sumTree _ a => if a.bit < p then
      if a.remaining = 0 then
        if !a.carry && decide (binaryValue a.path < 2 ^ edges) then .input 0
        else Formula.const false
      else CarrySaveLocal.formula a.carry
      else Formula.const false
  | .product _ _ _ coefficient (.port path carry bit index) =>
      if bit < p then
        if index = 0 ∨ index = 1 then .input 0 else Formula.const
          (ConvolutionOperand.Signed.correction (operandQuery m p coefficient path carry bit false))
      else Formula.const false
  | .product _ _ _ _ a => SignedValueGame.template p a
  | .value _ base 0 coefficient bit =>
      if coefficient < (modulus m).length ∧ bit < p then
        if base < vertices then .input 0
        else Formula.const (InterpolationGrid.factorBit 0 0 0 coefficient bit)
      else Formula.const false
  | .value _ _ (_ + 1) coefficient bit =>
      if coefficient < (modulus m).length ∧ bit < p then .input 0 else Formula.const false
  | .entry _ => Formula.const false

/-- Follow an internal finishing-adder reference, retaining its sum coordinate. -/
def sumSource (p coefficient : ℕ) (a : CarryLookahead.Query.Address) (port : Fin 7) :
    Option Node :=
  (SignedValueGame.finishSource p a port).bind fun
    | .finish a' => some (.sum coefficient a')
    | _ => none

/-- Every macro reference is computed from its address and the fixed circuit parameters. -/
def source (m p edges vertices : ℕ) : Node → Fin 7 → Option Node
  | .sum coefficient (.input j), port =>
      if j < p + p ∧ port = 0 then
        some (.sumTree coefficient
          ⟨[], edges, decide (p ≤ j), if p ≤ j then j - p else j⟩)
      else none
  | .sum coefficient a, port => sumSource p coefficient a port
  | .sumTree coefficient a, port => if a.bit < p then
      if a.remaining = 0 then
        if (!a.carry && decide (binaryValue a.path < 2 ^ edges)) = true ∧ port = 0 then
          some (.value (binaryValue a.path) 0 (Nat.clog 2 vertices) coefficient a.bit)
        else none
      else (CarrySaveQuery.descend a port).map (Node.sumTree coefficient)
      else none
  | .product assignment base level coefficient (.port path carry bit index), port =>
      if bit < p ∧ port = 0 then
        if index = 0 then
          (ConvolutionOperand.Signed.source (operandQuery m p coefficient path carry bit false)).map
            fun j => .value assignment base level j.1 j.2
        else if index = 1 then
          (ConvolutionOperand.Signed.source (operandQuery m p coefficient path carry bit true)).map
            fun j => .value assignment (base + 2 ^ level) level j.1 j.2
        else none
      else none
  | .product assignment base level coefficient a, port =>
      (SignedValueGame.source (3 ^ modulusExp m) p a port).map
        (Node.product assignment base level coefficient)
  | .value assignment base 0 coefficient bit, port =>
      if coefficient < (modulus m).length ∧ bit < p ∧ port = 0 ∧ base < vertices then
        some (.entry ⟨assignment, base, coefficient, bit⟩)
      else none
  | .value assignment base (level + 1) coefficient bit, port =>
      if coefficient < (modulus m).length ∧ bit < p ∧ port = 0 then
        some (.product assignment base level coefficient (.finish (.sum bit)))
      else none
  | .entry _, _ => none

/-- The public input label at a terminal; the local formula carries no input value. -/
def inputLabel (a : Address) : Option Entry :=
  match a.node with
  | .entry e => some e
  | _ => none

/-- A genuine circuit instruction: either one explicit entry-bit input or a Boolean operation. -/
def operation (m p edges vertices : ℕ) (a : Address) : Entry ⊕ Op :=
  match inputLabel a with
  | some e => .inl e
  | none => .inr ((FormulaExpansion.decoder (template m p edges vertices)
      (source m p edges vertices)).op a)

/-- Interpret only the explicitly labelled circuit inputs; all child navigation is value-free. -/
def decoder (m p edges vertices : ℕ) (input : Entry → Bool) : Decoder Address where
  op a := (operation m p edges vertices a).elim (fun e => .const (input e)) id
  child := (FormulaExpansion.decoder (template m p edges vertices)
    (source m p edges vertices)).child

/-- The output gate for a valid representative coefficient and precision bit. -/
def root (m p edges vertices : ℕ) (coefficient : Fin (modulus m).length) (bit : Fin p) : Address :=
  FormulaExpansion.root (template m p edges vertices) (.sum coefficient.val (.sum bit.val))

/-- A balanced vertex block, padded with the multiplicative identity. This is proof data only. -/
private noncomputable def block (m p vertices : ℕ) (entry : ℕ → ℕ → Ring p (modulus m))
    (assignment base level : ℕ) : Ring p (modulus m) :=
  InterpolationGrid.blockProduct (fun vertex => if vertex < vertices then entry assignment vertex
    else 1) base level

/-- The semantic bit of a labelled entry. -/
noncomputable def entryBit (m p : ℕ) (entry : ℕ → ℕ → Ring p (modulus m)) (e : Entry) : Bool :=
  ((representative m p (entry e.assignment e.vertex)).coeff e.coefficient).val.testBit e.bit

/-- Carry-save leaves of one coordinate of the assignment sum. -/
private noncomputable def sumLeaves (m p edges vertices : ℕ)
    (entry : ℕ → ℕ → Ring p (modulus m)) (coefficient : ℕ) : List Bool → BitString (p + p) :=
  InterpolationGrid.terms (2 ^ edges) (fun assignment =>
    (representative m p (block m p vertices entry assignment 0
      (Nat.clog 2 vertices))).coeff coefficient)

/-- The two root sum components, followed by zero incoming carry. -/
private noncomputable def sumInput (m p edges vertices : ℕ)
    (entry : ℕ → ℕ → Ring p (modulus m)) (coefficient : ℕ) : BitString (p + p + 1) :=
  let pair := CarrySaveQuery.tree (sumLeaves m p edges vertices entry coefficient) edges []
  Fin.append (Fin.append (CarrySaveQuery.component pair false) (CarrySaveQuery.component pair true))
    ![false]

/-- Mathematical meanings of the macros. None of these values is stored by the compiler. -/
private noncomputable def nodeValue (m p edges vertices : ℕ)
    (entry : ℕ → ℕ → Ring p (modulus m)) : Node → Bool
  | .sum coefficient a => CarryLookahead.Query.value p (SignedValueGame.rounds p)
      (sumInput m p edges vertices entry coefficient) a
  | .sumTree coefficient a => CarrySaveQuery.value
      (sumLeaves m p edges vertices entry coefficient) a
  | .product assignment base level coefficient a =>
      SignedValueGame.nodeValue (3 ^ modulusExp m) coefficient
        (representative m p (block m p vertices entry assignment base level))
        (representative m p (block m p vertices entry assignment (base + 2 ^ level) level)) a
  | .value assignment base level coefficient bit =>
      ((representative m p (block m p vertices entry assignment base level)).coeff
        coefficient).val.testBit bit
  | .entry e => entryBit m p entry e

/-- Formula semantics, with the explicitly labelled input interpreted at a terminal. -/
@[no_expose] noncomputable def value (m p edges vertices : ℕ)
    (entry : ℕ → ℕ → Ring p (modulus m)) (a : Address) : Bool :=
  match inputLabel a with
  | some e => entryBit m p entry e
  | none => FormulaExpansion.value (source m p edges vertices)
      (nodeValue m p edges vertices entry) a

private theorem coefficient_bit_false (m p : ℕ) (x : Ring p (modulus m))
    (coefficient bit : ℕ) (h : ¬(coefficient < (modulus m).length ∧ bit < p)) :
    ((representative m p x).coeff coefficient).val.testBit bit = false := by
  by_cases hc : coefficient < (modulus m).length
  · have hb : p ≤ bit := by omega
    exact Nat.testBit_lt_two_pow ((ZMod.val_lt _).trans_le
      (Nat.pow_le_pow_right (by decide : 0 < 2) hb))
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt
      ((natDegree_representative_lt m p x).trans_le (by omega))]
    simp

private theorem sum_formula_value (m p edges vertices : ℕ)
    (entry : ℕ → ℕ → Ring p (modulus m)) (coefficient : ℕ) (a : CarryLookahead.Query.Address) :
    (SignedValueGame.operationFormula ((SignedValueGame.finishDecoder p).op a)).eval interpretation
      (fun j => (sumSource p coefficient a j).elim false (nodeValue m p edges vertices entry)) =
        (SignedValueGame.finishDecoder p).eval
          (CarryLookahead.Query.value p (SignedValueGame.rounds p)
            (sumInput m p edges vertices entry coefficient)) a := by
  cases ho : (SignedValueGame.finishDecoder p).op a <;>
    simp [SignedValueGame.operationFormula, sumSource, SignedValueGame.finishSource, ho,
      nodeValue, Decoder.eval]

/-- Every nonterminal macro satisfies its local Boolean template. The statement includes
arbitrary malformed indices and paths; they use the decoder's stated zero padding. -/
private theorem nodeValue_eq_template (m p edges vertices : ℕ)
    (entry : ℕ → ℕ → Ring p (modulus m)) (a : Node) (ha : ∀ e, a ≠ .entry e) :
    nodeValue m p edges vertices entry a = (template m p edges vertices a).eval interpretation
      (fun j => (source m p edges vertices a j).elim false
        (nodeValue m p edges vertices entry)) := by
  cases a with
  | sum coefficient a =>
    cases a
    case input j =>
      simp only [nodeValue, CarryLookahead.Query.value, sumInput]
      rw [SignedValueGame.read_tree_input]
      by_cases hj : j < p + p <;>
        simp [template, SignedValueGame.template, source, hj, nodeValue]
    all_goals
      simp only [template, SignedValueGame.template, source]
      rw [sum_formula_value]
      rw [SignedValueGame.finish_eval_eq p (sumInput m p edges vertices entry coefficient)
        _ _ (by intro j h; cases h)]
      simp only [nodeValue]
      exact CarryLookahead.Query.value_eq_eval p (SignedValueGame.rounds p)
        (sumInput m p edges vertices entry coefficient) _
  | sumTree coefficient a =>
    rcases a with ⟨path, remaining, carry, bit⟩
    by_cases hb : bit < p
    · cases remaining with
      | zero =>
        simp only [nodeValue, CarrySaveQuery.value, hb, ↓reduceDIte, CarrySaveQuery.tree,
          sumLeaves, InterpolationGrid.terms, InterpolationGrid.component_residuePair]
        cases carry <;> by_cases hpath : binaryValue path < 2 ^ edges <;>
          simp [template, source, hb, hpath, nodeValue]
      | succ remaining =>
        have h := CarrySaveQuery.value_layer (sumLeaves m p edges vertices entry coefficient)
          path remaining carry ⟨bit, hb⟩
        rw [nodeValue, h]
        simp only [template, source, hb, ↓reduceIte, Nat.add_eq_zero_iff, Nat.one_ne_zero,
          and_false]
        congr 1
        funext j
        cases he : CarrySaveQuery.descend ⟨path, remaining + 1, carry, bit⟩ j <;>
          simp [nodeValue]
    · simp [nodeValue, CarrySaveQuery.value, template, source, hb]
  | product assignment base level coefficient a =>
    have hv : (representative m p (block m p vertices entry assignment
        (base + 2 ^ level) level)).natDegree < 2 * 3 ^ modulusExp m := by
      simpa only [length_modulus] using natDegree_representative_lt m p
        (block m p vertices entry assignment (base + 2 ^ level) level)
    cases a with
    | finish a | tree a =>
      rw [nodeValue, SignedValueGame.nodeValue_eq_template _ _ _ _ hv _
        (by intro path carry bit j h; cases h)]
      simp only [template, source]
      congr 1
      funext j
      cases hs : SignedValueGame.source (3 ^ modulusExp m) p _ j <;> simp [nodeValue]
    | port path carry bit index =>
      by_cases hb : bit < p
      · by_cases h₀ : index = 0
        · subst index
          simp [nodeValue, SignedValueGame.nodeValue, signedBit, signedRead, template,
            source, hb, operandQuery, Function.comp_def]
        · by_cases h₁ : index = 1
          · subst index
            simp [nodeValue, SignedValueGame.nodeValue, signedBit, signedRead, template,
              source, hb, operandQuery, Function.comp_def]
          · simp [nodeValue, SignedValueGame.nodeValue, signedBit, template, source,
              hb, h₀, h₁, operandQuery]
      · simp [nodeValue, SignedValueGame.nodeValue, template, hb]
  | value assignment base level coefficient bit =>
    by_cases hvalid : coefficient < (modulus m).length ∧ bit < p
    · cases level with
      | zero =>
        by_cases hbase : base < vertices
        · simp [nodeValue, template, source, hvalid.1, hvalid.2, hbase, block,
            InterpolationGrid.blockProduct_zero, entryBit]
        · simp only [nodeValue, block, InterpolationGrid.blockProduct_zero, hbase, ↓reduceIte,
            template, hvalid]
          exact (InterpolationGrid.factorBit_eq m p 0 0 0
            ⟨coefficient, hvalid.1⟩ ⟨bit, hvalid.2⟩).symm
      | succ level =>
        simp only [template, hvalid, ↓reduceIte, Formula.eval_input, source,
          and_self, Option.elim_some, nodeValue]
        rw [show block m p vertices entry assignment base (level + 1) =
            block m p vertices entry assignment base level *
              block m p vertices entry assignment (base + 2 ^ level) level from
          InterpolationGrid.blockProduct_succ _ _ _]
        exact (SignedValueGame.nodeValue_product m p _ _
          ⟨coefficient, hvalid.1⟩ ⟨bit, hvalid.2⟩).symm
    · cases level <;> simp [template, hvalid, nodeValue,
        coefficient_bit_false m p _ coefficient bit hvalid]
  | entry e => exact False.elim (ha e rfl)

private theorem inputLabel_none (a : Node) (ha : ∀ e, a ≠ .entry e)
    (f : Formula signature 7) : inputLabel ⟨a, f⟩ = none := by
  cases a <;> first | rfl | exact False.elim (ha _ rfl)

/-- Entering a macro at its full local formula gives that macro's specified value, including
an explicitly labelled entry terminal. -/
private theorem value_node_root (m p edges vertices : ℕ)
    (entry : ℕ → ℕ → Ring p (modulus m)) (a : Node) :
    value m p edges vertices entry (FormulaExpansion.root (template m p edges vertices) a) =
      nodeValue m p edges vertices entry a := by
  by_cases ht : ∃ e, a = .entry e
  · obtain ⟨e, rfl⟩ := ht
    rfl
  · have ha : ∀ e, a ≠ .entry e := by simpa using ht
    rw [value, FormulaExpansion.root, inputLabel_none a ha]
    exact (nodeValue_eq_template m p edges vertices entry a ha).symm

/-- The interpreted circuit satisfies every local Boolean equation, with input values used
only when an explicit entry label is reached. -/
theorem value_eq_eval (m p edges vertices : ℕ)
    (entry : ℕ → ℕ → Ring p (modulus m)) (a : Address) :
    value m p edges vertices entry a =
      (decoder m p edges vertices (entryBit m p entry)).eval
        (value m p edges vertices entry) a := by
  rcases a with ⟨a, f⟩
  by_cases ht : ∃ e, a = .entry e
  · obtain ⟨e, rfl⟩ := ht
    rfl
  · have ha : ∀ e, a ≠ .entry e := by simpa using ht
    have hl := inputLabel_none a ha
    cases f with
    | input i =>
      cases hs : source m p edges vertices a i with
      | none => simp [value, decoder, operation, hl, FormulaExpansion.value,
          FormulaExpansion.decoder, Decoder.eval, hs]
      | some a' =>
        simp only [value, hl, FormulaExpansion.value, Formula.eval_input, hs, Option.elim_some,
          decoder, operation, Sum.elim_inr, id_eq, Decoder.eval, FormulaExpansion.decoder]
        change nodeValue m p edges vertices entry a' =
          (value m p edges vertices entry
              (FormulaExpansion.root (template m p edges vertices) a') ||
            value m p edges vertices entry (FormulaExpansion.root (template m p edges vertices) a'))
        rw [value_node_root]
        simp
    | gate op args =>
      cases op <;> simp [value, decoder, operation, hl, FormulaExpansion.value,
        FormulaExpansion.decoder, Decoder.eval, interpretation]

private theorem block_root (m p vertices : ℕ) (entry : ℕ → ℕ → Ring p (modulus m))
    (assignment : ℕ) :
    block m p vertices entry assignment 0 (Nat.clog 2 vertices) =
      ∏ vertex ∈ Finset.range vertices, entry assignment vertex := by
  simp only [block, InterpolationGrid.blockProduct, Nat.zero_add]
  have hs : Finset.range vertices ⊆ Finset.range (2 ^ Nat.clog 2 vertices) :=
    Finset.range_mono (Nat.le_pow_clog (by decide : 1 < 2) vertices)
  calc
    _ = ∏ vertex ∈ Finset.range vertices,
        (if vertex < vertices then entry assignment vertex else 1) :=
      (Finset.prod_subset hs fun vertex _ hv => by
        simp [Finset.mem_range.not.mp hv]).symm
    _ = _ := Finset.prod_congr rfl fun vertex hv => ite_eq_left (Finset.mem_range.mp hv)

/-- A balanced product request computes the selected bit of its consecutive vertex block.
The assignment is a parameter of the entry interpretation; no assignment sum is traversed.
Vertices outside the network contribute the multiplicative identity. -/
theorem value_block_root (m p edges vertices : ℕ)
    (entry : ℕ → ℕ → Ring p (modulus m)) (assignment base level coefficient bit : ℕ) :
    value m p edges vertices entry
      (FormulaExpansion.root (template m p edges vertices)
        (.value assignment base level coefficient bit)) =
      ((representative m p (InterpolationGrid.blockProduct
        (fun vertex => if vertex < vertices then entry assignment vertex else 1)
          base level)).coeff coefficient).val.testBit bit := by
  exact value_node_root m p edges vertices entry (.value assignment base level coefficient bit)

/-- The full balanced block computes the product of all actual vertices for one assignment.
Identity padding disappears, including when the vertex set is empty. -/
theorem value_product_root (m p edges vertices : ℕ)
    (entry : ℕ → ℕ → Ring p (modulus m)) (assignment coefficient bit : ℕ) :
    value m p edges vertices entry
      (FormulaExpansion.root (template m p edges vertices)
        (.value assignment 0 (Nat.clog 2 vertices) coefficient bit)) =
      ((representative m p (∏ vertex ∈ Finset.range vertices,
        entry assignment vertex)).coeff coefficient).val.testBit bit := by
  rw [value_node_root]
  change ((representative m p
    (block m p vertices entry assignment 0 (Nat.clog 2 vertices))).coeff coefficient).val.testBit
      bit = _
  rw [block_root]

/-- The output is the requested representative coefficient bit of the full assignment sum
of vertex products, uniformly for all edge counts, vertex counts and entry values. -/
theorem value_root (m p edges vertices : ℕ)
    (entry : ℕ → ℕ → Ring p (modulus m)) (coefficient : Fin (modulus m).length) (bit : Fin p) :
    value m p edges vertices entry (root m p edges vertices coefficient bit) =
      ((representative m p (∑ assignment ∈ Finset.range (2 ^ edges),
        ∏ vertex ∈ Finset.range vertices, entry assignment vertex)).coeff
          coefficient.val).val.testBit
          bit.val := by
  rw [root, value_node_root]
  simp only [nodeValue, sumInput, SignedValueGame.rounds]
  rw [CarryLookahead.Query.value_pair_sum_eq]
  have h := InterpolationGrid.bit_ringSum m p (2 ^ edges)
    (fun assignment => block m p vertices entry assignment 0 (Nat.clog 2 vertices)) coefficient bit
  rw [Nat.clog_pow 2 edges (by decide)] at h
  simpa only [sumLeaves, block_root] using h

/-- Specializing the terminal entry function gives the original described-network contraction;
the constructor requires no precomputed tensor table or list of assignment products. -/
theorem value_root_contraction {T : Type} (m p : ℕ) (d : DescribedNetwork T)
    (eval : T → List Bool → Ring p (modulus m))
    (coefficient : Fin (modulus m).length) (bit : Fin p) :
    value m p d.numEdges d.vertices.length (networkEntry d eval)
      (root m p d.numEdges d.vertices.length coefficient bit) =
        ((representative m p (d.contraction eval)).coeff coefficient.val).val.testBit bit.val := by
  rw [value_root, sum_prod_networkEntry]

end Cslib.Circuits.Frontier.FastContraction.StoppingQuery
