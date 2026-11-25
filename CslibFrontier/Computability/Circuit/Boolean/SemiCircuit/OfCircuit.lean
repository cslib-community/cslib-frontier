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

/-!
# The binary-gate semi-circuit of a circuit

Under `SemiCircuit.binaryB2Cost`, which charges `1` only for the ten genuinely two-variable
operations of `B₂` (`fullSignature 2 Bool`) and `0` for constants and unary projections /
negations, `SemiCircuit.ofCircuitBinary` folds all cost-`0` lines directly into `Lit`s without
creating gates. Input `i` becomes parameter `i`, each genuinely binary line `g` becomes gate
`n + g` with input literal negations absorbed into its operation, and the affine system is empty.

The resulting semi-circuit is well formed (`SemiCircuit.wellFormed_ofCircuitBinary`), has size
equal to `C.program.cost binaryB2Cost` (`SemiCircuit.size_ofCircuitBinary`), and evaluates to the
circuit's output on every consistent assignment (`SemiCircuit.out_eval_ofCircuitBinary`).

## Main definitions

* `Cslib.Circuits.Boolean.SemiCircuit.binaryB2Cost`: cost charging `1` on genuinely binary `B₂`
  gates and `0` on constants and unary operations.
* `Cslib.Circuits.Boolean.SemiCircuit.ofCircuitBinary`: the binary-gate semi-circuit folding
  constants and unary lines into literals.

## Main results

* `Cslib.Circuits.Boolean.SemiCircuit.cost_binaryB2Cost_le_size`,
  `Cslib.Circuits.Boolean.SemiCircuit.size_ofCircuitBinary`,
  `Cslib.Circuits.Boolean.SemiCircuit.wellFormed_ofCircuitBinary`,
  `Cslib.Circuits.Boolean.SemiCircuit.out_eval_ofCircuitBinary`.

## References

* [O. S. Mishra and R. Santhanam, *An Explicit 3.5n − o(n) Size Lower Bound against General
  Boolean Circuits*][MishraSanthanam2026]
-/

public section

namespace Cslib.Circuits.Boolean.SemiCircuit

open Cslib.Circuits

variable {n : ℕ}

/-- Cost charging `1` for each genuinely two-variable operation of `fullSignature 2 Bool` (the
eight AND-type operations, XOR, and XNOR) and `0` for constants (`.con c` and constant `.fn`) and
unary projections / negated projections. -/
@[expose] def binaryB2Cost : (fullSignature 2 Bool).Op → ℕ
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
private def lineBinaryGate {g : ℕ} (wLit : Wire n g → Lit) :
    Line (fullSignature 2 Bool) n g → Gate
  | ⟨.fn op, w⟩ =>
    let ℓ₀ := wLit (w ⟨0, by simp [fullSignature]⟩)
    let ℓ₁ := wLit (w ⟨1, by simp [fullSignature]⟩)
    ⟨fun a b => op ![a ^^ ℓ₀.neg, b ^^ ℓ₁.neg], ℓ₀.arg, ℓ₁.arg⟩
  | ⟨.con c, _⟩ => ⟨fun _ _ => c, .const false, .const false⟩

/-- The literal computed by `line` when constant and unary lines fold into `wLit` and genuinely
binary lines introduce gate `n + g`. -/
private def lineBinaryLit {g : ℕ} (wLit : Wire n g → Lit) :
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
private def programGateLit {g : ℕ} (p : Program (fullSignature 2 Bool) n g) : Fin g → Lit :=
  match p with
  | .empty => Fin.elim0
  | @Program.gate _ _ _ p line =>
    let prior := programGateLit p
    Fin.lastCases (lineBinaryLit (Wire.elim (fun i => Lit.node i false) prior) line) prior

/-- The literal carried by any wire of `p` when constant and unary lines are folded. -/
private def programWireLit {g : ℕ} (p : Program (fullSignature 2 Bool) n g) : Wire n g → Lit :=
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
private def programBinaryGates {g : ℕ} (p : Program (fullSignature 2 Bool) n g) : Finset ℕ :=
  match p with
  | .empty => ∅
  | @Program.gate _ _ g p line =>
    if binaryB2Cost line.op = 1 then insert (n + g) (programBinaryGates p)
    else programBinaryGates p

/-- The gate map of `p` on `programBinaryGates p`. -/
private def programBinaryGate {g : ℕ} (p : Program (fullSignature 2 Bool) n g) (i : ℕ) : Gate :=
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
    split_ifs at hJ
    · rcases Finset.mem_insert.1 hJ with rfl | hJ
      exacts [by omega, by have := ih hJ; omega]
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
  dsimp only [programBinaryGates]
  split_ifs
  exacts [Finset.subset_insert _ _, subset_rfl]

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
    have lift {t : ℕ} : (t < n ∨ t ∈ programBinaryGates p) ∧ t < n + g →
        (t < n ∨ t ∈ programBinaryGates (p.gate line)) ∧ t < n + (g + 1) :=
      fun ⟨hb, _⟩ => ⟨hb.imp_right (subset_programBinaryGates_gate p line ·), by omega⟩
    rintro (i | k) t ht
    · exact lift (ih (.input i) ht)
    · revert ht
      refine Fin.lastCases ?_ (fun j => ?_) k
      · rw [programWireLit_gate_last]
        intro ht'
        obtain ⟨op | c, w⟩ := line
        · dsimp only [lineBinaryLit] at ht'
          split_ifs at ht' with h1 h2
          iterate 2 exact lift (ih _ (reads_of_unaryLit_reads ht'))
          simp only [Lit.Reads, Lit.node, Arg.node.injEq] at ht'
          subst ht'
          have hc : binaryB2Cost (.fn op) = 1 := by simp [binaryB2Cost, h1, h2]
          exact ⟨Or.inr (by simp [programBinaryGates, hc]), by omega⟩
        · simp [lineBinaryLit, Lit.Reads, Lit.const] at ht'
      · rw [programWireLit_gate_castSucc]
        exact fun ht' => lift (ih (.gate j) ht')

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
      · rcases ht with ht | ht <;>
          exact (reads_programWireLit p _ ht).imp_left (Or.imp_right (hsub t))
      · rcases ht with ht | ht <;> cases ht
    · simp only [programBinaryGate, hJg, ↓reduceIte] at ht
      have hJp : J ∈ programBinaryGates p := by
        dsimp only [programBinaryGates] at hJ
        split_ifs at hJ
        exacts [(Finset.mem_insert.1 hJ).resolve_left hJg, hJ]
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
      obtain ⟨_ | _ | m, hm⟩ := a <;> first | rfl | simp [fullSignature] at hm
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
    (ofCircuitBinary C).params = Finset.range n := by rfl

/-- The semi-circuit `ofCircuitBinary C` has no auxiliary variables. -/
@[simp] theorem ofCircuitBinary_aux (C : Circuit (fullSignature 2 Bool) n 1) :
    (ofCircuitBinary C).aux = ∅ := by rfl

/-- The semi-circuit `ofCircuitBinary C` has no affine equations. -/
@[simp] theorem ofCircuitBinary_eqns (C : Circuit (fullSignature 2 Bool) n 1) :
    (ofCircuitBinary C).eqns = ∅ := by rfl

/-- The size of `ofCircuitBinary C` equals the binary `B₂` gate cost of `C`. -/
@[simp] theorem size_ofCircuitBinary (C : Circuit (fullSignature 2 Bool) n 1) :
    (ofCircuitBinary C).size = C.program.cost binaryB2Cost := by
  change (programBinaryGates C.program).card + (∅ : Finset ℕ).card = C.program.cost binaryB2Cost
  rw [Finset.card_empty, add_zero, card_programBinaryGates]

/-- The binary-gate semi-circuit `ofCircuitBinary C` is well formed. -/
theorem wellFormed_ofCircuitBinary (C : Circuit (fullSignature 2 Bool) n 1) :
    (ofCircuitBinary C).WellFormed where
  disjoint_params_aux := Finset.disjoint_empty_right _
  disjoint_params_gates := Finset.disjoint_left.2 fun i hi hg => by
    have := mem_programBinaryGates_bounds hg; have := Finset.mem_range.1 hi; omega
  disjoint_aux_gates := Finset.disjoint_empty_left _
  reads_lt J hJ i _ hr := (reads_programBinaryGate C.program hJ hr).2
  reads_live J hJ i hr := by
    rcases (reads_programBinaryGate C.program hJ hr).1 with hi | hi <;>
      simp [live, ofCircuitBinary, hi]
  terms_subset e he := by simp [ofCircuitBinary] at he
  card_terms_le e he := by simp [ofCircuitBinary] at he
  out_live i hi := by
    rcases (reads_programWireLit C.program (C.outputs 0) hi).1 with hi' | hi' <;>
      simp [live, ofCircuitBinary, hi']
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
