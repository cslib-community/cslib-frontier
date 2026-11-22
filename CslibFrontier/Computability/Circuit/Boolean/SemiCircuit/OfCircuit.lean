/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.SemiCircuit
public import CslibFrontier.Computability.Circuit.Simulation
public import Cslib.Computability.Circuit.Full
public import Mathlib.Data.Fin.VecNotation
import CslibFrontier.Computability.Circuit.Program
import CslibFrontier.Computability.Circuit.Topology

/-!
# The semi-circuit of a circuit

A circuit over the full binary basis with `n` inputs and one output is a fair semi-circuit without
equations (`SemiCircuit.ofCircuit`): input `i` is the parameter `i`, gate `j` is the gate `n + j`,
and a constant line becomes a gate with a constant operation. It is well formed
(`SemiCircuit.wellFormed_ofCircuit`), and the output of a consistent assignment is the output of
the circuit on the values of the parameters (`SemiCircuit.out_eval_ofCircuit`).

Under `SemiCircuit.binaryB2Cost`, which charges `1` only for the ten genuinely two-variable
operations of `B₂` and `0` for constants and unary projections / negations,
`SemiCircuit.ofCircuitBinary` folds all cost-`0` lines directly into `Lit`s without creating gates,
yielding a well-formed semi-circuit (`SemiCircuit.wellFormed_ofCircuitBinary`) of size equal to
`C.program.cost binaryB2Cost` (`SemiCircuit.size_ofCircuitBinary`) that computes the same output on
every consistent assignment (`SemiCircuit.out_eval_ofCircuitBinary`).

## Main definitions

* `Cslib.Circuits.Boolean.SemiCircuit.wireName`,
  `Cslib.Circuits.Boolean.SemiCircuit.lineGate`,
  `Cslib.Circuits.Boolean.SemiCircuit.ofCircuit`: the gate-per-line semi-circuit of a circuit.
* `Cslib.Circuits.Boolean.SemiCircuit.binaryB2Cost`: cost charging `1` on genuinely binary `B₂`
  gates and `0` on constants and unary operations.
* `Cslib.Circuits.Boolean.SemiCircuit.ofCircuitBinary`: the binary-gate semi-circuit folding
  constants and unary lines into literals.

## Main results

* `Cslib.Circuits.Boolean.SemiCircuit.wellFormed_ofCircuit`,
  `Cslib.Circuits.Boolean.SemiCircuit.out_eval_ofCircuit`.
* `Cslib.Circuits.Boolean.SemiCircuit.cost_binaryB2Cost_le_size`,
  `Cslib.Circuits.Boolean.SemiCircuit.size_ofCircuitBinary`,
  `Cslib.Circuits.Boolean.SemiCircuit.size_ofCircuitBinary_le`,
  `Cslib.Circuits.Boolean.SemiCircuit.wellFormed_ofCircuitBinary`,
  `Cslib.Circuits.Boolean.SemiCircuit.out_eval_ofCircuitBinary`.

## References

* [O. S. Mishra and R. Santhanam, *An Explicit 3.5n − o(n) Size Lower Bound against General
  Boolean Circuits*][MishraSanthanam2026]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.SemiCircuit

open Cslib.Circuits

variable {n : ℕ}

/-- The name of a wire of a circuit with `n` inputs: input `i` is `i` and gate `j` is `n + j`. -/
def wireName {g : ℕ} : Wire n g → ℕ
  | .input i => i
  | .gate j => n + j

/-- The gate of a line of a circuit over the full binary basis; a constant becomes a gate with
a constant operation. -/
def lineGate {g : ℕ} : Line (fullSignature 2 Bool) n g → Gate
  | ⟨.fn op, w⟩ => ⟨fun a b => op ![a, b], .node (wireName (w ⟨0, by simp [fullSignature]⟩)),
      .node (wireName (w ⟨1, by simp [fullSignature]⟩))⟩
  | ⟨.con c, _⟩ => ⟨fun _ _ => c, .const false, .const false⟩

/-- Evaluating `lineGate line` under `val` equals applying `fullInterpretation line.op` to the
values of `line`'s input wires. -/
theorem eval_lineGate {g : ℕ} (line : Line (fullSignature 2 Bool) n g) (val : ℕ → Bool) :
    (lineGate line).eval val =
      fullInterpretation line.op fun a => val (wireName (line.wires a)) := by
  obtain ⟨op | c, w⟩ := line
  · simp only [lineGate, Gate.eval, Arg.eval_node, fullInterpretation]
    congr 1 with a : 1
    obtain ⟨_ | _ | k, ha⟩ := a
    · rfl
    · rfl
    · simp at ha
  · rfl

private theorem reads_lineGate {g : ℕ} {line : Line (fullSignature 2 Bool) n g} {i : ℕ}
    (h : (lineGate line).Reads i) : ∃ a, wireName (line.wires a) = i := by
  obtain ⟨op | c, w⟩ := line
  · rcases h with h | h
    · exact ⟨_, Arg.node.inj h⟩
    · exact ⟨_, Arg.node.inj h⟩
  · rcases h with h | h <;> cases h

/-- The semi-circuit of a circuit over the full binary basis with one output: its inputs are the
parameters, its lines the gates, and it has no auxiliary variables and no equations. -/
def ofCircuit (C : Circuit (fullSignature 2 Bool) n 1) : SemiCircuit where
  params := Finset.range n
  aux := ∅
  gates := Finset.Ico n (n + C.size)
  gate i := if h : n ≤ i ∧ i < n + C.size then lineGate (C.program.lines ⟨i - n, by omega⟩)
    else ⟨fun _ _ => false, .const false, .const false⟩
  eqns := ∅
  eqn _ := ⟨∅, false⟩
  out := ⟨.node (wireName (C.outputs 0)), false⟩

/-- The parameters of `ofCircuit C` are `Finset.range n`. -/
@[simp] theorem ofCircuit_params (C : Circuit (fullSignature 2 Bool) n 1) :
    (ofCircuit C).params = Finset.range n := rfl

/-- The semi-circuit `ofCircuit C` has no auxiliary variables. -/
@[simp] theorem ofCircuit_aux (C : Circuit (fullSignature 2 Bool) n 1) :
    (ofCircuit C).aux = ∅ := rfl

/-- The gate indices of `ofCircuit C` are `Finset.Ico n (n + C.size)`. -/
@[simp] theorem ofCircuit_gates (C : Circuit (fullSignature 2 Bool) n 1) :
    (ofCircuit C).gates = Finset.Ico n (n + C.size) := rfl

/-- The semi-circuit `ofCircuit C` has no affine equations. -/
@[simp] theorem ofCircuit_eqns (C : Circuit (fullSignature 2 Bool) n 1) :
    (ofCircuit C).eqns = ∅ := rfl

private theorem ofCircuit_gate (C : Circuit (fullSignature 2 Bool) n 1) (k : Fin C.size) :
    (ofCircuit C).gate (n + k) = lineGate (C.program.lines k) := by
  have h : n ≤ n + (k : ℕ) ∧ n + (k : ℕ) < n + C.size := ⟨Nat.le_add_right _ _, by omega⟩
  simp only [ofCircuit, dite_eq_left h]
  congr 2
  exact Fin.ext (by simp)

/-- The node index `wireName w` of any wire `w` of `C` is live in `ofCircuit C`. -/
theorem wireName_mem_live (C : Circuit (fullSignature 2 Bool) n 1) (w : Wire n C.size) :
    wireName w ∈ (ofCircuit C).live := by
  cases w with
  | input i => simp [live, ofCircuit, wireName]
  | gate j => simp [live, ofCircuit, wireName]

/-- Every gate index of `ofCircuit C` has the form `n + k` for some `k : Fin C.size`. -/
theorem exists_eq_add_of_mem_gates {C : Circuit (fullSignature 2 Bool) n 1} {J : ℕ}
    (hJ : J ∈ (ofCircuit C).gates) : ∃ k : Fin C.size, J = n + k := by
  simp only [ofCircuit, Finset.mem_Ico] at hJ
  exact ⟨⟨J - n, by omega⟩, by dsimp only; omega⟩

/-- The semi-circuit of a circuit is well formed. -/
theorem wellFormed_ofCircuit (C : Circuit (fullSignature 2 Bool) n 1) :
    (ofCircuit C).WellFormed where
  disjoint_params_aux := Finset.disjoint_empty_right _
  disjoint_params_gates := by
    rw [Finset.disjoint_left]
    intro i hi hg
    simp only [ofCircuit, Finset.mem_range, Finset.mem_Ico] at hi hg
    omega
  disjoint_aux_gates := Finset.disjoint_empty_left _
  reads_lt J hJ i _ hr := by
    obtain ⟨k, rfl⟩ := exists_eq_add_of_mem_gates hJ
    rw [ofCircuit_gate] at hr
    obtain ⟨a, rfl⟩ := reads_lineGate hr
    -- `wireName` is the wire numbering `Wire.toNat`, so this is `Circuit.isOrdered_topology`.
    have hname (w : Wire n C.size) : wireName w = w.toNat := by cases w <;> rfl
    rw [hname]
    exact C.isOrdered_topology k a
  reads_live J hJ i hr := by
    obtain ⟨k, rfl⟩ := exists_eq_add_of_mem_gates hJ
    rw [ofCircuit_gate] at hr
    obtain ⟨a, rfl⟩ := reads_lineGate hr
    exact wireName_mem_live C _
  terms_subset e he := by simp [ofCircuit] at he
  card_terms_le e he := by simp [ofCircuit] at he
  out_live i hi := by
    cases hi
    exact wireName_mem_live C _
  solvable u := ⟨u, fun _ _ => rfl, fun e he => by simp [ofCircuit] at he⟩
  unique _ _ _ _ _ v hv := by simp [ofCircuit] at hv

/-- On a consistent assignment, the output of the semi-circuit of a circuit is the output of the
circuit on the values of the parameters. -/
theorem out_eval_ofCircuit (C : Circuit (fullSignature 2 Bool) n 1) {val : ℕ → Bool}
    (hval : (ofCircuit C).Consistent val) :
    (ofCircuit C).out.eval val = C.eval fullInterpretation (fun i => val i) 0 := by
  have htrace : (fun w => val (wireName w)) =
      C.program.trace fullInterpretation (fun i => val i) := by
    refine Program.eq_trace_of_forall_gate (fun i => rfl) fun k => ?_
    have hk : n + (k : ℕ) ∈ (ofCircuit C).gates := by
      simp only [ofCircuit, Finset.mem_Ico]; omega
    have := hval.2 _ hk
    rw [ofCircuit_gate, eval_lineGate] at this
    exact this
  change (val (wireName (C.outputs 0)) ^^ false) = _
  rw [Bool.xor_false, Circuit.eval, Function.comp_apply, ← htrace]

/-! ### Binary `B₂` cost and folding unary/constant lines -/

/-- Cost charging `1` for each genuinely two-variable operation of `fullSignature 2 Bool` (the
eight AND-type operations, XOR, and XNOR) and `0` for constants (`.con c` and constant `.fn`) and
unary projections / negated projections. -/
def binaryB2Cost : (fullSignature 2 Bool).Op → ℕ
  | .con _ => 0
  | .fn op =>
    if (op ![false, false] = op ![false, true] ∧ op ![true, false] = op ![true, true]) ∨
        (op ![false, false] = op ![true, false] ∧ op ![false, true] = op ![true, true]) then
      0
    else 1

/-- A constant operation `.con c` has binary `B₂` cost `0`. -/
@[simp] theorem binaryB2Cost_con (c : Bool) : binaryB2Cost (.con c) = 0 := rfl

/-- Every operation of `fullSignature 2 Bool` has binary `B₂` cost at most `1`. -/
theorem binaryB2Cost_le_one (op : (fullSignature 2 Bool).Op) : binaryB2Cost op ≤ 1 := by
  cases op with
  | con _ => exact Nat.zero_le 1
  | fn op =>
    dsimp only [binaryB2Cost]
    split_ifs <;> omega

/-- The binary `B₂` cost of a circuit's program is at most its total gate count `C.size`. -/
theorem cost_binaryB2Cost_le_size {m : ℕ} (C : Circuit (fullSignature 2 Bool) n m) :
    C.program.cost binaryB2Cost ≤ C.size :=
  (C.program.cost_le_mul binaryB2Cost_le_one).trans_eq (one_mul _)

/-- Binary gate for a `fullSignature 2 Bool` line given the literals carried by earlier wires:
negations on input literals are absorbed into the gate's operation. -/
def lineBinaryGate {g : ℕ} (wLit : Wire n g → Lit) :
    Line (fullSignature 2 Bool) n g → Gate
  | ⟨.fn op, w⟩ =>
    let ℓ₀ := wLit (w ⟨0, by simp [fullSignature]⟩)
    let ℓ₁ := wLit (w ⟨1, by simp [fullSignature]⟩)
    ⟨fun a b => op ![a ^^ ℓ₀.neg, b ^^ ℓ₁.neg], ℓ₀.arg, ℓ₁.arg⟩
  | ⟨.con c, _⟩ => ⟨fun _ _ => c, .const false, .const false⟩

/-- The literal computed by `line` when constant and unary lines fold into `wLit` and genuinely
binary lines introduce gate `n + g`. -/
def lineBinaryLit {g : ℕ} (wLit : Wire n g → Lit) :
    Line (fullSignature 2 Bool) n g → Lit
  | ⟨.con c, _⟩ => Lit.const c
  | ⟨.fn op, w⟩ =>
    let ℓ₀ := wLit (w ⟨0, by simp [fullSignature]⟩)
    let ℓ₁ := wLit (w ⟨1, by simp [fullSignature]⟩)
    if op ![false, false] = op ![false, true] ∧ op ![true, false] = op ![true, true] then
      unaryLit (fun a => op ![a ^^ ℓ₀.neg, false]) ℓ₀.arg
    else if op ![false, false] = op ![true, false] ∧ op ![false, true] = op ![true, true] then
      unaryLit (fun b => op ![false, b ^^ ℓ₁.neg]) ℓ₁.arg
    else
      Lit.node (n + g) false

/-- Propagate literals along a `fullSignature 2 Bool` program: constant and unary lines fold into
a `Lit` of an input or an earlier binary gate, while genuinely binary lines introduce `n + g`. -/
def programGateLit {g : ℕ} (p : Program (fullSignature 2 Bool) n g) : Fin g → Lit :=
  match p with
  | .empty => Fin.elim0
  | @Program.gate _ _ _ p line =>
    let prior := programGateLit p
    Fin.lastCases (lineBinaryLit (Wire.elim (fun i => Lit.node i false) prior) line) prior

/-- The literal carried by any wire of `p` when constant and unary lines are folded. -/
def programWireLit {g : ℕ} (p : Program (fullSignature 2 Bool) n g) : Wire n g → Lit :=
  Wire.elim (fun i => Lit.node i false) (programGateLit p)

private theorem programWireLit_gate_last {g : ℕ} (p : Program (fullSignature 2 Bool) n g)
    (line : Line (fullSignature 2 Bool) n g) :
    programWireLit (p.gate line) (.gate (Fin.last g)) = lineBinaryLit (programWireLit p) line := by
  simp [programWireLit, programGateLit]

private theorem programWireLit_gate_castSucc {g : ℕ} (p : Program (fullSignature 2 Bool) n g)
    (line : Line (fullSignature 2 Bool) n g) (j : Fin g) :
    programWireLit (p.gate line) (.gate j.castSucc) = programWireLit p (.gate j) := by
  simp [programWireLit, programGateLit]

/-- The indices `n + k` of genuinely binary gates in `p`. -/
def programBinaryGates {g : ℕ} (p : Program (fullSignature 2 Bool) n g) : Finset ℕ :=
  match p with
  | .empty => ∅
  | @Program.gate _ _ g p line =>
    if binaryB2Cost line.op = 1 then insert (n + g) (programBinaryGates p)
    else programBinaryGates p

/-- The gate map of `p` on `programBinaryGates p`. -/
def programBinaryGate {g : ℕ} (p : Program (fullSignature 2 Bool) n g) (i : ℕ) : Gate :=
  match p with
  | .empty => ⟨fun _ _ => false, .const false, .const false⟩
  | @Program.gate _ _ g p line =>
    if i = n + g then lineBinaryGate (programWireLit p) line else programBinaryGate p i

private theorem mem_programBinaryGates_bounds {g : ℕ} {p : Program (fullSignature 2 Bool) n g}
    {J : ℕ} (hJ : J ∈ programBinaryGates p) : n ≤ J ∧ J < n + g := by
  induction p with
  | empty => simp [programBinaryGates] at hJ
  | @gate g p line ih =>
    dsimp only [programBinaryGates] at hJ
    split_ifs at hJ with hc
    · rcases Finset.mem_insert.1 hJ with rfl | hJ
      · omega
      · have := ih hJ; omega
    · have := ih hJ; omega

private theorem card_programBinaryGates {g : ℕ} (p : Program (fullSignature 2 Bool) n g) :
    (programBinaryGates p).card = p.cost binaryB2Cost := by
  induction p with
  | empty => rfl
  | @gate g p line ih =>
    rw [Program.cost_gate, ← ih]
    dsimp only [programBinaryGates]
    have hnot : n + g ∉ programBinaryGates p := fun h => by
      have := mem_programBinaryGates_bounds h; omega
    have hle := binaryB2Cost_le_one line.op
    split_ifs with hc
    · rw [Finset.card_insert_of_notMem hnot, hc]
    · omega

private theorem subset_programBinaryGates_gate {g : ℕ} (p : Program (fullSignature 2 Bool) n g)
    (line : Line (fullSignature 2 Bool) n g) :
    programBinaryGates p ⊆ programBinaryGates (p.gate line) := by
  intro J hJ
  dsimp only [programBinaryGates]
  split_ifs
  · exact Finset.mem_insert_of_mem hJ
  · exact hJ

private theorem reads_programWireLit {g : ℕ} (p : Program (fullSignature 2 Bool) n g) :
    ∀ (w : Wire n g) {t : ℕ}, (programWireLit p w).Reads t →
      (t < n ∨ t ∈ programBinaryGates p) ∧ t < n + g := by
  induction p with
  | empty =>
    rintro (i | k) t ht
    · simp only [programWireLit, Wire.elim_input, Lit.Reads, Lit.node, Arg.node.injEq] at ht
      subst ht; exact ⟨Or.inl i.isLt, by omega⟩
    · exact k.elim0
  | @gate g p line ih =>
    rintro (i | k) t ht
    · simp only [programWireLit, Wire.elim_input, Lit.Reads, Lit.node, Arg.node.injEq] at ht
      subst ht; exact ⟨Or.inl i.isLt, by omega⟩
    · revert ht
      refine Fin.lastCases ?_ (fun j => ?_) k
      · rw [programWireLit_gate_last]
        intro ht'
        have hsub : ∀ x ∈ programBinaryGates p, x ∈ programBinaryGates (p.gate line) :=
          fun x hx => subset_programBinaryGates_gate p line hx
        obtain ⟨op | c, w⟩ := line
        · dsimp only [lineBinaryLit] at ht'
          split_ifs at ht' with h1 h2
          · obtain ⟨hb, hlt⟩ := ih _ (reads_of_unaryLit_reads ht')
            exact ⟨hb.imp_right (hsub t), by omega⟩
          · obtain ⟨hb, hlt⟩ := ih _ (reads_of_unaryLit_reads ht')
            exact ⟨hb.imp_right (hsub t), by omega⟩
          · simp only [Lit.Reads, Lit.node, Arg.node.injEq] at ht'
            subst ht'
            have hc : binaryB2Cost (.fn op) = 1 := by simp [binaryB2Cost, h1, h2]
            exact ⟨Or.inr (by simp [programBinaryGates, hc]), by omega⟩
        · simp [lineBinaryLit, Lit.Reads, Lit.const] at ht'
      · rw [programWireLit_gate_castSucc]
        intro ht'
        obtain ⟨hb, hlt⟩ := ih (.gate j) ht'
        exact ⟨hb.imp_right (fun hx => subset_programBinaryGates_gate p line hx), by omega⟩

private theorem reads_programBinaryGate {g : ℕ} (p : Program (fullSignature 2 Bool) n g) :
    ∀ {J : ℕ}, J ∈ programBinaryGates p → ∀ {t : ℕ}, (programBinaryGate p J).Reads t →
      (t < n ∨ t ∈ programBinaryGates p) ∧ t < J := by
  induction p with
  | empty => simp [programBinaryGates]
  | @gate g p line ih =>
    intro J hJ t ht
    have hsub : ∀ x ∈ programBinaryGates p, x ∈ programBinaryGates (p.gate line) :=
      fun x hx => subset_programBinaryGates_gate p line hx
    by_cases hJg : J = n + g
    · subst hJg
      simp only [programBinaryGate, ↓reduceIte] at ht
      obtain ⟨op | c, w⟩ := line
      · rcases ht with ht | ht
        · obtain ⟨hb, hlt⟩ := reads_programWireLit p (w ⟨0, by simp [fullSignature]⟩) ht
          exact ⟨hb.imp_right (hsub t), hlt⟩
        · obtain ⟨hb, hlt⟩ := reads_programWireLit p (w ⟨1, by simp [fullSignature]⟩) ht
          exact ⟨hb.imp_right (hsub t), hlt⟩
      · rcases ht with ht | ht <;> cases ht
    · simp only [programBinaryGate, hJg, ↓reduceIte] at ht
      have hJp : J ∈ programBinaryGates p := by
        dsimp only [programBinaryGates] at hJ
        split_ifs at hJ with hc
        · exact (Finset.mem_insert.1 hJ).resolve_left hJg
        · exact hJ
      obtain ⟨hb, hlt⟩ := ih hJp ht
      exact ⟨hb.imp_right (hsub t), hlt⟩

private theorem fn_indep_snd {op : (Fin 2 → Bool) → Bool}
    (h0 : op ![false, false] = op ![false, true]) (h1 : op ![true, false] = op ![true, true])
    (a b : Bool) : op ![a, b] = op ![a, false] := by
  cases a <;> cases b <;> simp [h0, h1]

private theorem fn_indep_fst {op : (Fin 2 → Bool) → Bool}
    (h0 : op ![false, false] = op ![true, false]) (h1 : op ![false, true] = op ![true, true])
    (a b : Bool) : op ![a, b] = op ![false, b] := by
  cases a <;> cases b <;> simp [h0, h1]

private theorem eval_lineBinaryLit {g : ℕ} (wLit : Wire n g → Lit)
    (line : Line (fullSignature 2 Bool) n g) {val : ℕ → Bool}
    (hg : binaryB2Cost line.op = 1 → val (n + g) = (lineBinaryGate wLit line).eval val) :
    (lineBinaryLit wLit line).eval val =
      fullInterpretation line.op fun a => (wLit (line.wires a)).eval val := by
  revert hg
  obtain ⟨op | c, w⟩ := line
  · intro hg
    have hv_eq : (fullInterpretation (k := 2) (.fn op) fun a => (wLit (w a)).eval val) =
        op ![(wLit (w ⟨0, by simp [fullSignature]⟩)).eval val,
          (wLit (w ⟨1, by simp [fullSignature]⟩)).eval val] := by
      change op _ = _
      congr 1 with a : 1
      obtain ⟨_ | _ | m, hm⟩ := a
      · rfl
      · rfl
      · simp [fullSignature] at hm
    change (lineBinaryLit wLit ⟨.fn op, w⟩).eval val =
      fullInterpretation (k := 2) (.fn op) fun a => (wLit (w a)).eval val
    rw [hv_eq]
    dsimp only [lineBinaryLit]
    set ℓ₀ := wLit (w ⟨0, by simp [fullSignature]⟩)
    set ℓ₁ := wLit (w ⟨1, by simp [fullSignature]⟩)
    split_ifs with h1 h2
    · rw [← eval_unaryLit]
      exact (fn_indep_snd h1.1 h1.2 (ℓ₀.eval val) (ℓ₁.eval val)).symm
    · rw [← eval_unaryLit]
      exact (fn_indep_fst h2.1 h2.2 (ℓ₀.eval val) (ℓ₁.eval val)).symm
    · have hc : binaryB2Cost (.fn op) = 1 := by
        dsimp only [binaryB2Cost]
        rw [ite_eq_right (not_or.2 ⟨h1, h2⟩)]
      have hgv := hg hc
      dsimp only [lineBinaryGate, Gate.eval] at hgv
      rw [Lit.eval_node, Bool.xor_false, hgv]
      rfl
  · intro _; exact Lit.eval_const c val

private theorem eval_programWireLit {g : ℕ} (p : Program (fullSignature 2 Bool) n g)
    {val : ℕ → Bool}
    (hval : ∀ J ∈ programBinaryGates p, val J = (programBinaryGate p J).eval val) :
    ∀ w : Wire n g,
      (programWireLit p w).eval val = p.trace fullInterpretation (fun i => val i) w := by
  induction p with
  | empty =>
    rintro (i | k)
    · simp [programWireLit]
    · exact k.elim0
  | @gate g p line ih =>
    have hval_p : ∀ J ∈ programBinaryGates p, val J = (programBinaryGate p J).eval val := by
      intro J hJ
      have hne : J ≠ n + g := by have := mem_programBinaryGates_bounds hJ; omega
      have hJ' := hval J (subset_programBinaryGates_gate p line hJ)
      simpa [programBinaryGate, hne] using hJ'
    rintro (i | k)
    · simp [programWireLit]
    · refine Fin.lastCases ?_ (fun j => ?_) k
      · rw [programWireLit_gate_last, Program.trace_gate_last, eval_lineBinaryLit]
        · congr 1 with a : 1
          exact ih hval_p (line.wires a)
        · intro hc
          have hmem : n + g ∈ programBinaryGates (p.gate line) := by
            simp [programBinaryGates, hc]
          simpa [programBinaryGate] using hval (n + g) hmem
      · rw [programWireLit_gate_castSucc,
          show (Wire.gate j.castSucc : Wire n (g + 1)) = (Wire.gate j).castSucc from rfl,
          Program.trace_gate_castSucc]
        exact ih hval_p (.gate j)

/-- The semi-circuit of a `fullSignature 2 Bool` circuit with constant and unary lines folded into
literals: its gate count equals `C.program.cost binaryB2Cost`. -/
def ofCircuitBinary (C : Circuit (fullSignature 2 Bool) n 1) : SemiCircuit where
  params := Finset.range n
  aux := ∅
  gates := programBinaryGates C.program
  gate := programBinaryGate C.program
  eqns := ∅
  eqn _ := ⟨∅, false⟩
  out := programWireLit C.program (C.outputs 0)

/-- The parameters of `ofCircuitBinary C` are `Finset.range n`. -/
@[simp] theorem ofCircuitBinary_params (C : Circuit (fullSignature 2 Bool) n 1) :
    (ofCircuitBinary C).params = Finset.range n := rfl

/-- The semi-circuit `ofCircuitBinary C` has no auxiliary variables. -/
@[simp] theorem ofCircuitBinary_aux (C : Circuit (fullSignature 2 Bool) n 1) :
    (ofCircuitBinary C).aux = ∅ := rfl

/-- The semi-circuit `ofCircuitBinary C` has no affine equations. -/
@[simp] theorem ofCircuitBinary_eqns (C : Circuit (fullSignature 2 Bool) n 1) :
    (ofCircuitBinary C).eqns = ∅ := rfl

/-- The size of `ofCircuitBinary C` equals the binary `B₂` gate cost of `C`. -/
@[simp] theorem size_ofCircuitBinary (C : Circuit (fullSignature 2 Bool) n 1) :
    (ofCircuitBinary C).size = C.program.cost binaryB2Cost := by
  change (programBinaryGates C.program).card + (∅ : Finset ℕ).card = C.program.cost binaryB2Cost
  rw [Finset.card_empty, add_zero, card_programBinaryGates]

/-- The size of `ofCircuitBinary C` is at most `C.program.cost binaryB2Cost`. -/
theorem size_ofCircuitBinary_le (C : Circuit (fullSignature 2 Bool) n 1) :
    (ofCircuitBinary C).size ≤ C.program.cost binaryB2Cost :=
  (size_ofCircuitBinary C).le

/-- The binary-gate semi-circuit `ofCircuitBinary C` is well formed. -/
theorem wellFormed_ofCircuitBinary (C : Circuit (fullSignature 2 Bool) n 1) :
    (ofCircuitBinary C).WellFormed where
  disjoint_params_aux := Finset.disjoint_empty_right _
  disjoint_params_gates := by
    rw [Finset.disjoint_left]
    intro i hi hg
    have := mem_programBinaryGates_bounds hg
    have := Finset.mem_range.1 hi
    omega
  disjoint_aux_gates := Finset.disjoint_empty_left _
  reads_lt J hJ i _ hr := (reads_programBinaryGate C.program hJ hr).2
  reads_live J hJ i hr := by
    rcases (reads_programBinaryGate C.program hJ hr).1 with hi | hi
    · simp [live, ofCircuitBinary, hi]
    · simp [live, ofCircuitBinary, hi]
  terms_subset e he := by simp [ofCircuitBinary] at he
  card_terms_le e he := by simp [ofCircuitBinary] at he
  out_live i hi := by
    rcases (reads_programWireLit C.program (C.outputs 0) hi).1 with hi' | hi'
    · simp [live, ofCircuitBinary, hi']
    · simp [live, ofCircuitBinary, hi']
  solvable u := ⟨u, fun _ _ => rfl, fun e he => by simp [ofCircuitBinary] at he⟩
  unique _ _ _ _ _ v hv := by simp [ofCircuitBinary] at hv

/-- On a consistent assignment, the output of `ofCircuitBinary C` equals the output of `C` on the
values of the parameters. -/
theorem out_eval_ofCircuitBinary (C : Circuit (fullSignature 2 Bool) n 1) {val : ℕ → Bool}
    (hval : (ofCircuitBinary C).Consistent val) :
    (ofCircuitBinary C).out.eval val = C.eval fullInterpretation (fun i => val i) 0 := by
  change (programWireLit C.program (C.outputs 0)).eval val = _
  rw [eval_programWireLit C.program hval.2, Circuit.eval, Function.comp_apply]

end Cslib.Circuits.Boolean.SemiCircuit
