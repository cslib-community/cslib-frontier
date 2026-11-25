/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Order.Lattice.Nat

/-!
# Binary linear circuits and their gate complexity

A gate forms a weighted sum of two inputs or earlier registers. Inputs and registers can be
reused arbitrarily. An output is zero or a freely scaled wire. A circuit evaluates to
multiplication by its matrix of basis responses, and every finite matrix has a least gate count.

The model and proofs are adapted from the modules `Circuit`, `CircuitLinearity` and
`CircuitComposition` of the Lean release accompanying [OpenAI2026FiniteFourier].
-/

public section

namespace Cslib.Circuit.Linear

/-- A binary linear gate over two previously available wires. -/
structure BinaryGate (K W : Type*) where
  /-- First source wire. -/
  left : W
  /-- Second source wire. -/
  right : W
  /-- Coefficient of the first wire. -/
  leftCoeff : K
  /-- Coefficient of the second wire. -/
  rightCoeff : K

/-- Evaluate the weighted sum at a binary gate. -/
@[expose] def BinaryGate.eval {K W : Type*} [Semiring K] (g : BinaryGate K W) (v : W → K) : K :=
  g.leftCoeff * v g.left + g.rightCoeff * v g.right

/-- Outputs may select and scale a wire, or output zero. -/
inductive Readout (K W : Type*) where
  | zero
  | scaled (coeff : K) (wire : W)

/-- Read zero or a scalar multiple of a wire. -/
@[expose] def Readout.eval {K W : Type*} [Semiring K] (z : Readout K W) (v : W → K) : K :=
  match z with
  | .zero => 0
  | .scaled c w => c * v w

/-- A straight-line program of precisely the displayed number of binary gates. -/
inductive Program (K I : Type*) : ℕ → Type _ where
  | nil : Program K I 0
  | step {r : ℕ} (p : Program K I r) (g : BinaryGate K (I ⊕ Fin r)) : Program K I (r + 1)

namespace Program

variable {K I : Type*} [Semiring K]

/-- Evaluation of the stored registers, with the newest value in register zero. -/
@[expose] def value : {r : ℕ} → Program K I r → (I → K) → Fin r → K
  | _, .nil, _ => Fin.elim0
  | _, .step p g, x => Fin.cases (g.eval (Sum.elim x (p.value x))) (p.value x)

end Program

/-- A program together with its readouts. -/
structure LinearCircuit (K I O : Type*) (s : ℕ) where
  /-- The ordered gate list. -/
  program : Program K I s
  /-- A free readout for each output. -/
  output : O → Readout K (I ⊕ Fin s)

namespace LinearCircuit

variable {K I O : Type*} [Semiring K] {s : ℕ}

/-- Evaluate the program and read the indicated output. -/
@[expose] def eval (p : LinearCircuit K I O s) (x : I → K) (o : O) : K :=
  (p.output o).eval (Sum.elim x (p.program.value x))

/-- The matrix of responses to the standard basis vectors. -/
@[expose] noncomputable def matrix (p : LinearCircuit K I O s) : Matrix O I K := by
  classical
  exact fun o i => p.eval (Pi.single i 1) o

/-- A matrix entry is the corresponding output for a unit input. -/
theorem matrix_apply [DecidableEq I] (p : LinearCircuit K I O s) (o : O) (i : I) :
    p.matrix o i = p.eval (Pi.single i 1) o := by
  simp only [matrix]
  exact congrArg (fun x => p.eval x o) (by ext j; by_cases h : j = i <;> simp [h])

end LinearCircuit

/-- Exact realization with at most the given number of gates. -/
@[expose] def RealizableAtMost {K I O : Type*} [Semiring K] (M : Matrix O I K) (S : ℕ) : Prop :=
  ∃ s ≤ S, ∃ p : LinearCircuit K I O s, p.matrix = M

section Linearity

variable {K I O : Type*} [Semiring K] [Fintype I]

private theorem wire_eq_sum [DecidableEq I] {s : ℕ} (p : Program K I s) (x : I → K)
    (w : I ⊕ Fin s) :
    Sum.elim x (p.value x) w =
      ∑ i, Sum.elim (Pi.single i 1) (p.value (Pi.single i 1)) w * x i := by
  classical
  induction p with
  | nil =>
    cases w with
    | inl j => simp [Pi.single_apply, ite_mul]
    | inr j => exact j.elim0
  | step p g ih =>
    cases w with
    | inl j => simp [Pi.single_apply, ite_mul]
    | inr j =>
      refine Fin.cases ?_ (fun k => ih (.inr k)) j
      change g.eval _ = ∑ i, g.eval _ * x i
      simp only [BinaryGate.eval, add_mul, mul_assoc, Finset.sum_add_distrib,
        ← Finset.mul_sum]
      rw [← ih g.left, ← ih g.right]

/-- Evaluating a circuit on any input gives the matrix-vector product of its basis
evaluations with that input. -/
theorem LinearCircuit.eval_eq_mulVec {s : ℕ} (p : LinearCircuit K I O s) (x : I → K) :
    p.eval x = p.matrix.mulVec x := by
  classical
  funext o
  change (p.output o).eval _ = ∑ i, (p.output o).eval _ * x i
  cases p.output o with
  | zero => simp [Readout.eval]
  | scaled a w =>
    simp only [Readout.eval, mul_assoc, ← Finset.mul_sum]
    rw [← wire_eq_sum p.program x w]

end Linearity

variable {K I O : Type*} [Semiring K]

namespace Program

/-- A freely readable scalar-valued function of the inputs. -/
@[expose] def Available {r : ℕ} (p : Program K I r) (f : (I → K) → K) : Prop :=
  ∃ z : Readout K (I ⊕ Fin r), ∀ x, z.eval (Sum.elim x (p.value x)) = f x

private theorem available_step {r : ℕ} {p : Program K I r} (g : BinaryGate K (I ⊕ Fin r))
    {f : (I → K) → K} (hf : Available p f) : Available (p.step g) f := by
  obtain ⟨z, hz⟩ := hf
  cases z with
  | zero => exact ⟨.zero, hz⟩
  | scaled c w =>
    cases w with
    | inl i => exact ⟨.scaled c (.inl i), hz⟩
    | inr j => exact ⟨.scaled c (.inr j.succ), hz⟩

/-- A scalar multiple of a readable value remains readable. -/
theorem Available.scale {r : ℕ} {p : Program K I r} {f : (I → K) → K}
    (c : K) (hf : Available p f) : Available p (fun x => c * f x) := by
  obtain ⟨z, hz⟩ := hf
  cases z with
  | zero => exact ⟨.zero, fun x => by simp [← hz x, Readout.eval]⟩
  | scaled d w => exact ⟨.scaled (c * d) w, fun x => by simp [← hz x, Readout.eval, mul_assoc]⟩

/-- A weighted sum of two readable values costs at most one additional gate. -/
theorem Available.combine {r : ℕ} (p : Program K I r)
    {f g : (I → K) → K} (a b : K) (hf : Available p f) (hg : Available p g) :
    ∃ n ≤ r + 1, ∃ q : Program K I n, (∀ u, Available p u → Available q u) ∧
      Available q (fun x => a * f x + b * g x) := by
  obtain ⟨z, hz⟩ := hf
  obtain ⟨w, hw⟩ := hg
  cases z with
  | zero =>
    refine ⟨r, Nat.le_succ _, p, fun _ h => h, ?_⟩
    simpa only [← hz, Readout.eval, mul_zero, zero_add] using Available.scale b ⟨w, hw⟩
  | scaled c i =>
    cases w with
    | zero =>
      refine ⟨r, Nat.le_succ _, p, fun _ h => h, ?_⟩
      simpa only [← hw, Readout.eval, mul_zero, add_zero] using Available.scale a ⟨.scaled c i, hz⟩
    | scaled d j =>
      let gate : BinaryGate K (I ⊕ Fin r) := ⟨i, j, a * c, b * d⟩
      exact ⟨r + 1, le_rfl, p.step gate, fun _ h => available_step gate h,
        .scaled 1 (.inr 0), fun x => by simp [← hz x, ← hw x, Readout.eval,
          Program.value, BinaryGate.eval, gate, mul_assoc]⟩

end Program

private theorem addRow {r : ℕ} (p : Program K I r) (s : Finset I)
    (f : I → K) : ∃ n ≤ r + s.card, ∃ q : Program K I n,
      (∀ u, Program.Available p u → Program.Available q u) ∧
        Program.Available q (fun x => ∑ i ∈ s, f i * x i) := by
  classical
  induction s using Finset.induction with
  | empty => exact ⟨r, by simp, p, fun _ h => h, .zero, by simp [Readout.eval]⟩
  | @insert i s hi ih =>
    obtain ⟨n, hn, q, hpq, hrow⟩ := ih
    have hin : q.Available (fun x => x i) := ⟨.scaled 1 (.inl i), fun x => one_mul _⟩
    obtain ⟨m, hm, q', hkeep, hg⟩ := Program.Available.combine q (f i) 1 hin hrow
    refine ⟨m, ?_, q', fun u h => hkeep u (hpq u h), ?_⟩
    · rw [Finset.card_insert_of_notMem hi]
      lia
    · simpa only [Finset.sum_insert hi, one_mul] using hg

private theorem addRows [Fintype I] (t : Finset O) (M : Matrix O I K) :
    ∃ n ≤ t.card * Fintype.card I, ∃ q : Program K I n,
      ∀ o ∈ t, Program.Available q (fun x => ∑ i, M o i * x i) := by
  classical
  induction t using Finset.induction with
  | empty => exact ⟨0, by simp, .nil, by simp⟩
  | @insert o t ho ih =>
    obtain ⟨r, hr, p, hrows⟩ := ih
    obtain ⟨n, hn, q, hpq, hrow⟩ := addRow p Finset.univ (M o)
    refine ⟨n, ?_, q, fun j hj => ?_⟩
    · rw [Finset.card_insert_of_notMem ho, Nat.succ_mul]
      exact hn.trans (Nat.add_le_add_right hr _)
    · rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hrow
      · exact hpq _ (hrows j hj)

/-- The row-by-row construction realizes every finite matrix, including empty formats. -/
theorem realizableAtMost_card_mul_card [Fintype I] [Fintype O] (M : Matrix O I K) :
    RealizableAtMost M (Fintype.card O * Fintype.card I) := by
  classical
  obtain ⟨n, hn, q, hrows⟩ := addRows Finset.univ M
  choose z hz using fun o => hrows o (Finset.mem_univ o)
  refine ⟨n, hn, ⟨q, z⟩, ?_⟩
  ext o i
  change (z o).eval (Sum.elim _ _) = _
  rw [hz]
  simp [Pi.single_apply, mul_ite]

/-- Least number of binary linear gates needed to apply a matrix. -/
@[expose] noncomputable def complexity [Fintype I] [Fintype O] (M : Matrix O I K) : ℕ :=
  sInf {n | RealizableAtMost M n}

/-- A circuit attains the least gate count. -/
theorem realizableAtMost_complexity [Fintype I] [Fintype O] (M : Matrix O I K) :
    RealizableAtMost M (complexity M) := by
  classical
  exact Nat.sInf_mem (s := {n | RealizableAtMost M n}) ⟨_, realizableAtMost_card_mul_card M⟩

/-- A gate budget bounds the minimum exactly when it admits a circuit. -/
theorem complexity_le_iff [Fintype I] [Fintype O] (M : Matrix O I K) (s : ℕ) :
    complexity M ≤ s ↔ RealizableAtMost M s := by
  constructor
  · intro h
    obtain ⟨r, hr, p, hp⟩ := realizableAtMost_complexity M
    exact ⟨r, hr.trans h, p, hp⟩
  · intro h
    classical
    exact Nat.sInf_le h

end Cslib.Circuit.Linear
