/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (addition to `Cslib/Computability/Circuit/Basic.lean`)

public import Cslib.Computability.Circuit.Basic
public import Mathlib.SetTheory.Cardinal.NatCard
import CslibFrontier.Computability.Circuit.Program
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum

/-!
# Inner gates and multiary gates

A gate of arity zero is a constant: like an input, it is a leaf of the circuit. The *inner*
gates of a program are its gates of positive arity, and the *inner size* of a circuit counts
them. A lower bound that holds over every basis can only count inner gates, since every value of
the alphabet may be a constant gate of the basis.

Over a finite alphabet `U`, gates of arity one can also be made free without changing the basis:
every wire of arity at most one computes either a constant in `U` or a unary function `U → U` of
an input or a gate of arity at least two. The *multiary* gates of a program are its gates of arity
at least two, and the *multiary size* of a circuit counts them (`Circuit.multiarySize`). By
deduplicating gates of arity at most one that compute the same constant or the same unary function
of the same input or multiary gate (`Circuit.exists_eval_eq_multiarySize_size_le`), every circuit
over any signature `σ` and interpretation on `U` is equivalent to one over `σ` with at most
`c.multiarySize` multiary gates and total gate count `O_{|U|}(c.multiarySize + n)`.

## Main definitions

* `Cslib.Circuits.Program.innerGates`: the gates of positive arity.
* `Cslib.Circuits.Circuit.innerSize`: the number of gates of positive arity.
* `Cslib.Circuits.Program.multiaryGates`: the gates of arity at least two.
* `Cslib.Circuits.Circuit.multiarySize`: the number of gates of arity at least two.

## Main results

* `Cslib.Circuits.Circuit.innerSize_le_size`: constant gates are free.
* `Cslib.Circuits.Circuit.multiarySize_le_innerSize`: unary gates are free in `multiarySize`.
* `Cslib.Circuits.Circuit.innerSize_eq_size_of_forall_arity_ne_zero`: without constant symbols,
  the inner size equals the size.
* `Cslib.Circuits.Circuit.multiarySize_eq_innerSize_of_forall_arity_ne_one`: without unary
  symbols, the multiary size equals the inner size.
* `Cslib.Circuits.Program.fanInAtMost_of_forall_arity_le`,
  `Cslib.Circuits.Circuit.fanInAtMost_of_forall_arity_le`,
  `Cslib.Circuits.Circuit.fanInAtMost_fullSignature`: fan-in bounds from signature arities.
* `Cslib.Circuits.Circuit.innerSize_eq_zero_of_fanInAtMost_zero`: without arguments every gate is
  a constant.
* `Cslib.Circuits.Circuit.multiarySize_eq_zero_of_fanInAtMost_one`: with fan-in at most one, no
  gate is multiary.
* `Cslib.Circuits.Circuit.exists_eval_eq_multiarySize_size_le`: over a finite alphabet `U`,
  deduplicating constant and unary gates bounds total circuit size linearly in
  `c.multiarySize + n` over the same signature `σ`.
-/

@[expose] public section

namespace Cslib.Circuits

variable {σ : Signature} {n g m : ℕ}

/-- The *inner* gates of a program: those of positive arity. A gate of arity zero is a constant,
a leaf of the circuit like an input. -/
def Program.innerGates (p : Program σ n g) : Finset (Fin g) :=
  {k | σ.Arity (p.lines k).op ≠ 0}

/-- A gate `k` belongs to `p.innerGates` if and only if its operation has nonzero arity. -/
@[simp] theorem Program.mem_innerGates {p : Program σ n g} {k : Fin g} :
    k ∈ p.innerGates ↔ σ.Arity (p.lines k).op ≠ 0 := by
  simp [Program.innerGates]

/-- The *inner size* of a circuit: the number of its gates of positive arity. Constant gates are
free. For arithmetic circuits this counts the additions and multiplications. -/
def Circuit.innerSize (c : Circuit σ n m) : ℕ :=
  c.program.innerGates.card

/-- Constant gates are free: the inner size is at most the size. -/
theorem Circuit.innerSize_le_size (c : Circuit σ n m) : c.innerSize ≤ c.size :=
  (Finset.card_le_univ _).trans_eq (Fintype.card_fin _)

/-- Without arguments every gate is a constant, so a circuit of fan-in zero has inner size
zero. -/
theorem Circuit.innerSize_eq_zero_of_fanInAtMost_zero {c : Circuit σ n m}
    (h : c.FanInAtMost 0) : c.innerSize = 0 := by
  rw [Circuit.innerSize, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro k hk
  exact Program.mem_innerGates.mp hk (Nat.le_zero.mp (Program.fanInAtMost_iff.mp h k))

/-- A pure input-wiring circuit has `0` inner gates. -/
@[simp] theorem Circuit.innerSize_wiring (select : Fin m → Fin n) :
    (Circuit.wiring σ select).innerSize = 0 :=
  Nat.le_zero.mp ((Circuit.wiring σ select).innerSize_le_size)

/-- In a signature without nullary operations, every gate has positive arity, so the inner size is
the full gate count. -/
theorem Circuit.innerSize_eq_size_of_forall_arity_ne_zero (c : Circuit σ n m)
    (h : ∀ op, σ.Arity op ≠ 0) : c.innerSize = c.size := by
  have huniv : c.program.innerGates = Finset.univ :=
    Finset.eq_univ_iff_forall.mpr fun k => Program.mem_innerGates.mpr (h _)
  rw [Circuit.innerSize, huniv, Finset.card_univ, Fintype.card_fin]

/-- If every operation symbol has arity at most `r`, every program over the signature has fan-in at
most `r`. -/
theorem Program.fanInAtMost_of_forall_arity_le (p : Program σ n g) {r : ℕ}
    (h : ∀ op, σ.Arity op ≤ r) : p.FanInAtMost r :=
  Program.fanInAtMost_iff.mpr fun _ => h _

/-- If every operation symbol has arity at most `r`, every circuit over the signature has fan-in at
most `r`. -/
theorem Circuit.fanInAtMost_of_forall_arity_le (c : Circuit σ n m) {r : ℕ}
    (h : ∀ op, σ.Arity op ≤ r) : c.FanInAtMost r :=
  c.program.fanInAtMost_of_forall_arity_le h

/-- Every circuit over the full basis of arity `r` has fan-in at most `r`. -/
theorem Circuit.fanInAtMost_fullSignature {U : Type*} {r : ℕ}
    (c : Circuit (fullSignature r U) n m) : c.FanInAtMost r :=
  c.fanInAtMost_of_forall_arity_le fun op => by rcases op with _ | _ <;> simp [fullSignature]

/-! ### Multiary gates and finite-alphabet unary deduplication -/

/-- The *multiary* gates of a program: those of arity at least two. Gates of arity zero
(constants) and arity one (unary operations such as negations) are excluded. -/
def Program.multiaryGates (p : Program σ n g) : Finset (Fin g) :=
  {k | 2 ≤ σ.Arity (p.lines k).op}

/-- A gate `k` belongs to `p.multiaryGates` if and only if its operation has arity at least two. -/
@[simp] theorem Program.mem_multiaryGates {p : Program σ n g} {k : Fin g} :
    k ∈ p.multiaryGates ↔ 2 ≤ σ.Arity (p.lines k).op := by
  simp [Program.multiaryGates]

/-- The *multiary size* of a circuit: the number of its gates of arity at least two. Both constant
gates and unary gates are free. -/
def Circuit.multiarySize (c : Circuit σ n m) : ℕ :=
  c.program.multiaryGates.card

/-- Multiary gates are inner gates, so `multiarySize ≤ innerSize`. -/
theorem Circuit.multiarySize_le_innerSize (c : Circuit σ n m) : c.multiarySize ≤ c.innerSize :=
  Finset.card_le_card fun _ hk =>
    Program.mem_innerGates.mpr (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_two
      (Program.mem_multiaryGates.mp hk)))

/-- With fan-in at most one every gate is nullary or unary, so the multiary size is zero. -/
theorem Circuit.multiarySize_eq_zero_of_fanInAtMost_one {c : Circuit σ n m}
    (h : c.FanInAtMost 1) : c.multiarySize = 0 := by
  rw [Circuit.multiarySize, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro k hk
  exact not_le_of_gt (lt_of_le_of_lt (Program.fanInAtMost_iff.mp h k) Nat.one_lt_two)
    (Program.mem_multiaryGates.mp hk)

/-- A pure input-wiring circuit has `0` multiary gates. -/
@[simp] theorem Circuit.multiarySize_wiring (select : Fin m → Fin n) :
    (Circuit.wiring σ select).multiarySize = 0 :=
  Nat.le_zero.mp (((Circuit.wiring σ select).multiarySize_le_innerSize).trans_eq
    (Circuit.innerSize_wiring select))

/-- In a signature without unary operations, every inner gate has arity at least two, so the
multiary size equals the inner size. -/
theorem Circuit.multiarySize_eq_innerSize_of_forall_arity_ne_one (c : Circuit σ n m)
    (h : ∀ op, σ.Arity op ≠ 1) : c.multiarySize = c.innerSize := by
  have heq : c.program.multiaryGates = c.program.innerGates := by
    ext k
    simp only [Program.mem_multiaryGates, Program.mem_innerGates]
    have hk := h (c.program.lines k).op
    omega
  rw [Circuit.multiarySize, Circuit.innerSize, heq]

section DeduplicateUnary

private theorem Program.mem_multiaryGates_gate_castSucc (p : Program σ n g) (line : Line σ n g)
    (k : Fin g) : k.castSucc ∈ (p.gate line).multiaryGates ↔ k ∈ p.multiaryGates := by
  simp [Program.multiaryGates]

private theorem Program.mem_multiaryGates_gate_last (p : Program σ n g) (line : Line σ n g) :
    Fin.last g ∈ (p.gate line).multiaryGates ↔ 2 ≤ σ.Arity line.op := by
  simp [Program.multiaryGates]

private theorem Program.card_multiaryGates_gate_of_lt (p : Program σ n g) (line : Line σ n g)
    (h : ¬ 2 ≤ σ.Arity line.op) :
    (p.gate line).multiaryGates.card = p.multiaryGates.card := by
  have heq : (p.gate line).multiaryGates = p.multiaryGates.map Fin.castSuccEmb := by
    ext k
    refine Fin.lastCases ?_ (fun j => ?_) k
    · simp [Program.multiaryGates, h]
    · simp [Program.multiaryGates]
  rw [heq, Finset.card_map]

private theorem Program.card_multiaryGates_gate_of_le (p : Program σ n g) (line : Line σ n g)
    (h : 2 ≤ σ.Arity line.op) :
    (p.gate line).multiaryGates.card = p.multiaryGates.card + 1 := by
  have heq : (p.gate line).multiaryGates =
      insert (Fin.last g) (p.multiaryGates.map Fin.castSuccEmb) := by
    ext k
    refine Fin.lastCases ?_ (fun j => ?_) k
    · simp [Program.multiaryGates, h]
    · simp [Program.multiaryGates, Fin.castSucc_ne_last]
  rw [heq, Finset.card_insert_of_notMem (by simp), Finset.card_map]

/-- Semantic descriptor of a wire up to unary functions of inputs and multiary gates: either a
constant value in `U` or a unary transfer function applied to a multiary gate or an input. -/
private abbrev DedupTag (U : Type*) {g' : ℕ} (p' : Program σ n g') :=
  U ⊕ ((p'.multiaryGates ⊕ Fin n) × (U → U))

private def evalDedupTag {U : Type*} (I : Interpretation σ U) {g' : ℕ}
    (p' : Program σ n g') (x : Fin n → U) : DedupTag U p' → U
  | .inl u => u
  | .inr (.inl k, f) => f (p'.trace I x (.gate k.val))
  | .inr (.inr i, f) => f (x i)

private def liftDedupTag {U : Type*} {g' : ℕ} (p' : Program σ n g')
    (line' : Line σ n g') : DedupTag U p' → DedupTag U (p'.gate line')
  | .inl u => .inl u
  | .inr (.inl k, f) =>
    .inr (.inl ⟨k.val.castSucc,
      (Program.mem_multiaryGates_gate_castSucc p' line' k.val).mpr k.property⟩, f)
  | .inr (.inr i, f) => .inr (.inr i, f)

private theorem evalDedupTag_lift {U : Type*} (I : Interpretation σ U) {g' : ℕ}
    (p' : Program σ n g') (line' : Line σ n g') (x : Fin n → U) (t : DedupTag U p') :
    evalDedupTag I (p'.gate line') x (liftDedupTag p' line' t) = evalDedupTag I p' x t := by
  rcases t with u | ⟨k | i, f⟩
  · rfl
  · exact congrArg f (Program.trace_gate_castSucc p' line' I x (.gate k.val))
  · rfl

private theorem liftDedupTag_injective {U : Type*} {g' : ℕ} (p' : Program σ n g')
    (line' : Line σ n g') : Function.Injective (liftDedupTag (U := U) p' line') := by
  rintro (u₁ | ⟨k₁ | i₁, f₁⟩) (u₂ | ⟨k₂ | i₂, f₂⟩) h <;> simp only [liftDedupTag] at h
  · exact congrArg Sum.inl (Sum.inl.inj h)
  · nomatch h
  · nomatch h
  · nomatch h
  · obtain ⟨hk, rfl⟩ := Prod.mk.inj (Sum.inr.inj h)
    obtain rfl : k₁ = k₂ :=
      Subtype.ext (Fin.castSucc_inj.mp (congrArg Subtype.val (Sum.inl.inj hk)))
    rfl
  · obtain ⟨hk, _⟩ := Prod.mk.inj (Sum.inr.inj h)
    nomatch hk
  · nomatch h
  · obtain ⟨hk, _⟩ := Prod.mk.inj (Sum.inr.inj h)
    nomatch hk
  · obtain ⟨hk, rfl⟩ := Prod.mk.inj (Sum.inr.inj h)
    obtain rfl : i₁ = i₂ := Sum.inr.inj hk
    rfl

private def composeDedupTag {U : Type*} {g' : ℕ} {p' : Program σ n g'}
    (φ : U → U) : DedupTag U p' → DedupTag U p'
  | .inl u => .inl (φ u)
  | .inr (root, f) => .inr (root, φ ∘ f)

private theorem evalDedupTag_compose {U : Type*} (I : Interpretation σ U) {g' : ℕ}
    {p' : Program σ n g'} (φ : U → U) (x : Fin n → U) (t : DedupTag U p') :
    evalDedupTag I p' x (composeDedupTag φ t) = φ (evalDedupTag I p' x t) := by
  rcases t with u | ⟨k | i, f⟩ <;> rfl

private theorem Program.exists_dedup {U : Type*} (I : Interpretation σ U)
    (p : Program σ n g) :
    ∃ (g' : ℕ) (p' : Program σ n g') (remap : Wire n g → Wire n g')
      (tag : Wire n g' → DedupTag U p'),
      (∀ x w, p'.trace I x (remap w) = p.trace I x w) ∧
      (∀ r, p.FanInAtMost r → p'.FanInAtMost r) ∧
      p'.multiaryGates.card ≤ p.multiaryGates.card ∧
      (∀ x w', p'.trace I x w' = evalDedupTag I p' x (tag w')) ∧
      Set.InjOn (fun k' : Fin g' => tag (.gate k')) {k' : Fin g' | k' ∉ p'.multiaryGates} := by
  classical
  induction p with
  | empty =>
    refine ⟨0, .empty, id, fun | .input i => .inr (.inr i, id) | .gate k => k.elim0,
      fun _ _ => rfl, fun _ _ => trivial, le_rfl, fun _ w' => ?_, fun k' _ => k'.elim0⟩
    cases w' with
    | input i => rfl
    | gate k => exact k.elim0
  | @gate g p line ih =>
    obtain ⟨g', p', remap, tag, htrace, hfan, hmult, htag, hinj⟩ := ih
    let line' : Line σ n g' := line.mapWires remap
    have heval_line (x : Fin n → U) :
        line'.eval I x (p'.eval I x) = line.eval I x (p.eval I x) :=
      Line.eval_mapWires line remap I x x (p.eval I x) (p'.eval I x) (htrace x)
    have appendGate (t_last : DedupTag U (p'.gate line'))
        (ht_last : ∀ x, (p'.gate line').trace I x (.gate (Fin.last g')) =
          evalDedupTag I (p'.gate line') x t_last)
        (hinj_last : ∀ j : Fin g', j ∉ p'.multiaryGates →
          Fin.last g' ∉ (p'.gate line').multiaryGates →
            t_last ≠ liftDedupTag p' line' (tag (.gate j)))
        (hmult' : (p'.gate line').multiaryGates.card ≤ (p.gate line).multiaryGates.card) :
        ∃ (g'' : ℕ) (p'' : Program σ n g'') (remap'' : Wire n (g + 1) → Wire n g'')
          (tag'' : Wire n g'' → DedupTag U p''),
          (∀ x w, p''.trace I x (remap'' w) = (p.gate line).trace I x w) ∧
          (∀ r, (p.gate line).FanInAtMost r → p''.FanInAtMost r) ∧
          p''.multiaryGates.card ≤ (p.gate line).multiaryGates.card ∧
          (∀ x w', p''.trace I x w' = evalDedupTag I p'' x (tag'' w')) ∧
          Set.InjOn (fun k' : Fin g'' => tag'' (.gate k'))
            {k' : Fin g'' | k' ∉ p''.multiaryGates} := by
      let p'' := p'.gate line'
      let remap'' : Wire n (g + 1) → Wire n (g' + 1)
        | .input i => .input i
        | .gate k => Fin.lastCases (.gate (Fin.last g')) (fun j => (remap (.gate j)).castSucc) k
      let tag'' : Wire n (g' + 1) → DedupTag U p''
        | .input i => .inr (.inr i, id)
        | .gate k' => Fin.lastCases t_last (fun j' => liftDedupTag p' line' (tag (.gate j'))) k'
      refine ⟨g' + 1, p'', remap'', tag'', ?_, ?_, hmult', ?_, ?_⟩
      · intro x w
        cases w with
        | input i => rfl
        | gate k =>
          refine Fin.lastCases ?_ (fun j => ?_) k
          · simp only [remap'', Fin.lastCases_last, p'', Program.trace_gateWire,
              Program.gateFunction_apply, Program.eval_gate_last]
            exact heval_line x
          · simp only [remap'', Fin.lastCases_castSucc, p'', Program.trace_gate_castSucc]
            exact (htrace x (.gate j)).trans
              (Program.trace_gate_castSucc p line I x (.gate j)).symm
      · exact fun r h => ⟨hfan r h.1, h.2⟩
      · intro x w'
        cases w' with
        | input i => rfl
        | gate k' =>
          refine Fin.lastCases ?_ (fun j' => ?_) k'
          · simpa only [tag'', Fin.lastCases_last, p''] using ht_last x
          · simp only [tag'', Fin.lastCases_castSucc, evalDedupTag_lift, p'']
            exact (Program.trace_gate_castSucc p' line' I x (.gate j')).trans (htag x (.gate j'))
      · have hnm {j : Fin g'} (h : j.castSucc ∉ p''.multiaryGates) : j ∉ p'.multiaryGates :=
          mt (Program.mem_multiaryGates_gate_castSucc p' line' j).mpr h
        intro k₁ hk₁ k₂ hk₂ heq
        induction k₁ using Fin.lastCases <;> induction k₂ using Fin.lastCases <;>
          simp only [tag'', Fin.lastCases_last, Fin.lastCases_castSucc] at heq
        · rfl
        · exact (hinj_last _ (hnm hk₂) hk₁ heq).elim
        · exact (hinj_last _ (hnm hk₁) hk₂ heq.symm).elim
        · exact congrArg Fin.castSucc
            (hinj (hnm hk₁) (hnm hk₂) (liftDedupTag_injective p' line' heq))
    by_cases h2 : 2 ≤ σ.Arity line.op
    · -- Multiary gate: always emit `line'`.
      have hlast_mem : Fin.last g' ∈ (p'.gate line').multiaryGates :=
        (Program.mem_multiaryGates_gate_last p' line').mpr h2
      refine appendGate (.inr (.inl ⟨Fin.last g', hlast_mem⟩, id)) (fun _ => rfl)
        (fun _ _ hnot => (hnot hlast_mem).elim) ?_
      rw [Program.card_multiaryGates_gate_of_le p' line' h2,
        Program.card_multiaryGates_gate_of_le p line h2]
      exact Nat.add_le_add_right hmult 1
    · -- Nullary or unary gate: compute its semantic tag `t_new`.
      have ht_new : ∃ t_new : DedupTag U p',
          ∀ x, line'.eval I x (p'.eval I x) = evalDedupTag I p' x t_new := by
        rcases (by omega : σ.Arity line.op = 0 ∨ σ.Arity line.op = 1) with h0 | h1
        · have h0' : σ.Arity line'.op = 0 := h0
          exact ⟨.inl (I line'.op fun a => absurd a.isLt (by omega)), fun x =>
            congrArg (I line'.op) (funext fun a => absurd a.isLt (by omega))⟩
        · have h1' : σ.Arity line'.op = 1 := h1
          let a₀ : Fin (σ.Arity line'.op) := ⟨0, by omega⟩
          let w₀ : Wire n g' := line'.wires a₀
          let φ : U → U := fun u => I line'.op fun _ => u
          refine ⟨composeDedupTag φ (tag w₀), fun x => ?_⟩
          rw [evalDedupTag_compose, ← htag x w₀]
          change I line'.op _ = I line'.op _
          congr 1
          funext a
          have ha : a = a₀ := Fin.ext (by have := a.isLt; omega)
          subst ha
          rfl
      obtain ⟨t_new, ht_new⟩ := ht_new
      by_cases hex : ∃ k₀ : Fin g', k₀ ∉ p'.multiaryGates ∧ tag (.gate k₀) = t_new
      · -- Existing non-multiary gate already carries `t_new`: reuse it without adding a gate.
        obtain ⟨k₀, _, htk₀⟩ := hex
        let remap'' : Wire n (g + 1) → Wire n g'
          | .input i => .input i
          | .gate k => Fin.lastCases (.gate k₀) (fun j => remap (.gate j)) k
        refine ⟨g', p', remap'', tag, ?_, ?_, ?_, htag, hinj⟩
        · intro x w
          cases w with
          | input i => rfl
          | gate k =>
            refine Fin.lastCases ?_ (fun j => ?_) k
            · simp only [remap'', Fin.lastCases_last, Program.trace_gateWire,
                Program.gateFunction_apply, Program.eval_gate_last]
              exact (htag x (.gate k₀)).trans ((congrArg (evalDedupTag I p' x) htk₀).trans
                ((ht_new x).symm.trans (heval_line x)))
            · simp only [remap'', Fin.lastCases_castSucc]
              exact (htrace x (.gate j)).trans
                (Program.trace_gate_castSucc p line I x (.gate j)).symm
        · exact fun r h => hfan r h.1
        · exact hmult.trans_eq (Program.card_multiaryGates_gate_of_lt p line h2).symm
      · -- Fresh tag: emit `line'` and record `t_new`.
        refine appendGate (liftDedupTag p' line' t_new)
          (fun x => by simp only [evalDedupTag_lift, ← ht_new x, Program.trace_gateWire,
            Program.gateFunction_apply, Program.eval_gate_last])
          (fun j hj _ heq => hex ⟨j, hj, (liftDedupTag_injective p' line' heq).symm⟩) ?_
        rw [Program.card_multiaryGates_gate_of_lt p' line' h2,
          Program.card_multiaryGates_gate_of_lt p line h2]
        exact hmult

/-- **Deduplicating unary and constant gates over a finite alphabet.** Over a finite alphabet `U`,
every circuit `c` over any signature `σ` can be replaced by a circuit `c'` over the same
signature `σ` that computes the same function under `I`, preserves every fan-in bound of `c`,
uses at most `c.multiarySize` multiary gates, and has total gate count at most
`c.multiarySize + |U| + (c.multiarySize + n) * |U| ^ |U|`. -/
theorem Circuit.exists_eval_eq_multiarySize_size_le {U : Type*} [Finite U]
    (I : Interpretation σ U) (c : Circuit σ n m) :
    ∃ c' : Circuit σ n m, c'.eval I = c.eval I ∧
      (∀ r, c.FanInAtMost r → c'.FanInAtMost r) ∧
      c'.multiarySize ≤ c.multiarySize ∧
      c'.size ≤ c.multiarySize + Nat.card U +
        (c.multiarySize + n) * Nat.card U ^ Nat.card U := by
  classical
  let _ := Fintype.ofFinite U
  obtain ⟨g', p', remap, tag, htrace, hfan, hmult, _, hinj⟩ := c.program.exists_dedup I
  let c' : Circuit σ n m := ⟨p', remap ∘ c.outputs⟩
  refine ⟨c', ?_, hfan, hmult, ?_⟩
  · funext x j
    exact htrace x (c.outputs j)
  · have hpart : g' = p'.multiaryGates.card + (Finset.univ \ p'.multiaryGates).card := by
      have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ p'.multiaryGates)
      rw [Finset.card_univ, Fintype.card_fin] at h
      omega
    have hnonmult : (Finset.univ \ p'.multiaryGates).card ≤ Fintype.card (DedupTag U p') := by
      rw [← Finset.card_univ (α := DedupTag U p')]
      exact Finset.card_le_card_of_injOn (fun k' => tag (.gate k'))
        (fun _ _ => Finset.mem_univ _) fun k₁ hk₁ k₂ hk₂ heq =>
          hinj (Finset.mem_sdiff.mp hk₁).2 (Finset.mem_sdiff.mp hk₂).2 heq
    have hcard_tag : Fintype.card (DedupTag U p') =
        Nat.card U + (p'.multiaryGates.card + n) * Nat.card U ^ Nat.card U := by
      simp only [DedupTag, Fintype.card_sum, Fintype.card_prod, Fintype.card_coe,
        Fintype.card_fin, Fintype.card_pi, Finset.prod_const, Finset.card_univ,
        Nat.card_eq_fintype_card]
    have h2 : (p'.multiaryGates.card + n) * Nat.card U ^ Nat.card U ≤
        (c.multiarySize + n) * Nat.card U ^ Nat.card U :=
      Nat.mul_le_mul_right _ (Nat.add_le_add_right hmult n)
    change g' ≤ _
    change p'.multiaryGates.card ≤ c.multiarySize at hmult
    omega

end DeduplicateUnary

end Cslib.Circuits
