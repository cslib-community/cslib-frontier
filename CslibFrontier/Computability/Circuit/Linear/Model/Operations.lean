/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Linear.Model.Rewire
public import Mathlib.Data.Matrix.Block

/-!
# Serial and parallel linear circuits and change of coefficients

Serial composition adds gate budgets. On independent blocks the budgets may be summed, and
applying a semiring homomorphism to all coefficients preserves any circuit budget.

Adapted from `CircuitComposition`, `CircuitParallel`, `IntegralGridInputs` and
`PrimeKernelSpecialization` of the Lean release accompanying [OpenAI2026FiniteFourier].
-/

public section

namespace Cslib.Circuit.Linear

section Composition

variable {K I J O P T : Type*} [Semiring K]

/-- Append the second program, given a free readout for each of its input values. -/
private theorem simulate {s t : ℕ} (p : Program K I s) (q : Program K J t)
    (y : (I → K) → J → K) (hin : ∀ j, Program.Available p (fun x => y x j)) :
    ∃ n ≤ s + t, ∃ r : Program K I n, (∀ u, Program.Available p u → Program.Available r u) ∧
      (∀ w : J ⊕ Fin t, Program.Available r (fun x => Sum.elim (y x) (q.value (y x)) w)) := by
  induction q with
  | nil =>
    refine ⟨s, le_rfl, p, fun _ h => h, ?_⟩
    rintro (j | j)
    · exact hin j
    · exact j.elim0
  | @step t q g ih =>
    obtain ⟨m, hm, r, hkeep, hav⟩ := ih
    obtain ⟨n, hn, r', hkeep', hnew⟩ := Program.Available.combine r g.leftCoeff g.rightCoeff
      (hav g.left) (hav g.right)
    refine ⟨n, by lia, r', fun u h => hkeep' u (hkeep u h), ?_⟩
    rintro (j | j)
    · exact hkeep' _ (hkeep _ (hin j))
    · refine Fin.cases ?_ (fun k => ?_) j
      · exact hnew
      · exact hkeep' _ (hav (.inr k))

private theorem available_output {t n : ℕ} {r : Program K I n} {q : Program K J t}
    {y : (I → K) → J → K}
    (h : ∀ w : J ⊕ Fin t, Program.Available r (fun x => Sum.elim (y x) (q.value (y x)) w))
    (z : Readout K (J ⊕ Fin t)) :
    Program.Available r (fun x => z.eval (Sum.elim (y x) (q.value (y x)))) := by
  cases z with
  | zero => exact ⟨.zero, fun _ => rfl⟩
  | scaled c w => exact Program.Available.scale c (h w)

/-- Serial execution of two arbitrary circuits costs at most their combined sizes. -/
theorem LinearCircuit.exists_comp {s t : ℕ} (p : LinearCircuit K I J s)
    (q : LinearCircuit K J O t) :
    ∃ n ≤ s + t, ∃ r : LinearCircuit K I O n, ∀ x, r.eval x = q.eval (p.eval x) := by
  obtain ⟨n, hn, r, _, hv⟩ := simulate p.program q.program p.eval
    (fun j => ⟨p.output j, fun _ => rfl⟩)
  choose z hz using fun o => available_output hv (q.output o)
  exact ⟨n, hn, ⟨r, z⟩, fun x => funext fun o => hz o x⟩

/-- Execute two circuits on shared inputs while retaining all outputs. -/
theorem LinearCircuit.exists_fanout {s t : ℕ} (p : LinearCircuit K I O s)
    (q : LinearCircuit K I P t) :
    ∃ n ≤ s + t, ∃ r : LinearCircuit K I (O ⊕ P) n,
      ∀ x, r.eval x = Sum.elim (p.eval x) (q.eval x) := by
  obtain ⟨n, hn, r, hk, hv⟩ := simulate p.program q.program id
    (fun j => ⟨.scaled 1 (.inl j), fun x => by simp [Readout.eval]⟩)
  choose z₁ hz₁ using fun o => hk (fun x => p.eval x o) ⟨p.output o, fun _ => rfl⟩
  choose z₂ hz₂ using fun o => available_output hv (q.output o)
  refine ⟨n, hn, ⟨r, Sum.elim z₁ z₂⟩, fun x => funext fun o => ?_⟩
  cases o with
  | inl j => exact hz₁ j x
  | inr j => exact hz₂ j x

/-- Matrix multiplication is realized by serial circuit composition. -/
theorem RealizableAtMost.mul [Fintype J] {M : Matrix O J K} {N : Matrix J I K}
    {s t : ℕ} (hM : RealizableAtMost M s) (hN : RealizableAtMost N t) :
    RealizableAtMost (M * N) (s + t) := by
  classical
  obtain ⟨t', ht, p, rfl⟩ := hN
  obtain ⟨s', hs, q, rfl⟩ := hM
  obtain ⟨n, hn, r, he⟩ := p.exists_comp q
  refine ⟨n, by lia, r, ?_⟩
  ext o i
  change r.eval (Pi.single i 1) o = _
  rw [he, q.eval_eq_mulVec]
  rfl

private theorem circuitOnBlocks {s : T → ℕ} (p : ∀ k, LinearCircuit K I O (s k)) (t : Finset T) :
    ∃ n ≤ ∑ k ∈ t, s k, ∃ q : LinearCircuit K (I × T) (O × T) n,
      ∀ k ∈ t, ∀ x o, q.eval x (o, k) = (p k).eval (fun i => x (i, k)) o := by
  classical
  induction t using Finset.induction with
  | empty => exact ⟨0, by simp, ⟨.nil, fun _ => .zero⟩, by simp⟩
  | @insert k t hk ih =>
    obtain ⟨m, hm, q, hq⟩ := ih
    let first := (p k).rewire (fun i => (1, (i, k))) (fun o => (1, o))
    obtain ⟨n, hn, r, hr⟩ := first.exists_fanout q
    let out (ot : O × T) : O ⊕ (O × T) := if ot.2 = k then .inl ot.1 else .inr ot
    refine ⟨n, ?_, ⟨r.program, fun ot => r.output (out ot)⟩, fun j hj x o => ?_⟩
    · rw [Finset.sum_insert hk]
      lia
    · change r.eval x (out (o, j)) = _
      rw [hr]
      by_cases he : j = k
      · subst j
        simp [out, first, LinearCircuit.eval_rewire]
      · simpa [out, he] using hq j ((Finset.mem_insert.mp hj).resolve_left he) x o

/-- The sum of the block budgets realizes a block diagonal matrix. -/
theorem RealizableAtMost.blockDiagonal_family [Fintype T] [DecidableEq T] [Finite I]
    {M : T → Matrix O I K} {s : T → ℕ} (h : ∀ k, RealizableAtMost (M k) (s k)) :
    RealizableAtMost (Matrix.blockDiagonal M) (∑ k, s k) := by
  classical
  let := Fintype.ofFinite I
  choose m hm p hp using h
  obtain ⟨n, hn, r, hr⟩ := circuitOnBlocks p Finset.univ
  refine ⟨n, hn.trans (Finset.sum_le_sum (fun k _ => hm k)), r, ?_⟩
  ext ⟨o, k⟩ ⟨i, j⟩
  rw [LinearCircuit.matrix_apply, hr k (Finset.mem_univ _), Matrix.blockDiagonal_apply]
  by_cases hkj : k = j
  · subst j
    rw [ite_eq_left rfl, ← hp k, LinearCircuit.matrix_apply]
    congr 1
    ext u
    simp [Pi.single_apply]
  · have he : (fun l : I => (Pi.single (i, j) (1 : K) : I × T → K) (l, k)) = 0 := by
      ext l
      simp [hkj]
    rw [ite_eq_right hkj, he, LinearCircuit.eval_eq_mulVec, Matrix.mulVec_zero]
    rfl

/-- Running one copy of the same circuit on each block multiplies its budget by the block count. -/
theorem RealizableAtMost.blockDiagonal (T : Type*) [Fintype T] [DecidableEq T] [Finite I]
    {M : Matrix O I K} {s : ℕ} (hM : RealizableAtMost M s) :
    RealizableAtMost (Matrix.blockDiagonal (fun _ : T => M)) (Fintype.card T * s) := by
  simpa using RealizableAtMost.blockDiagonal_family (fun _ : T => hM)

end Composition

section BaseChange

variable {R K I O W : Type*} [Semiring R] [Semiring K]

private def BinaryGate.mapCoeff (g : BinaryGate R W) (φ : R →+* K) : BinaryGate K W :=
  ⟨g.left, g.right, φ g.leftCoeff, φ g.rightCoeff⟩

private def Readout.mapCoeff (z : Readout R W) (φ : R →+* K) : Readout K W :=
  match z with
  | .zero => .zero
  | .scaled c w => .scaled (φ c) w

/-- Change the coefficient semiring of a straight-line program. -/
private def Program.mapCoeff (φ : R →+* K) : {s : ℕ} → Program R I s → Program K I s
  | _, .nil => .nil
  | _, .step p g => .step (p.mapCoeff φ) (g.mapCoeff φ)

private theorem Program.value_mapCoeff (φ : R →+* K) {s : ℕ} (p : Program R I s) (x : I → R) :
    (p.mapCoeff φ).value (fun i => φ (x i)) = fun j => φ (p.value x j) := by
  induction p with
  | nil => funext j; exact j.elim0
  | step p g ih =>
    have hw (w : I ⊕ _) :
        Sum.elim (fun i => φ (x i)) ((p.mapCoeff φ).value (fun i => φ (x i))) w =
          φ (Sum.elim x (p.value x) w) := by cases w <;> simp [ih]
    funext j
    refine Fin.cases ?_ (fun k => congrFun ih k) j
    change (g.mapCoeff φ).eval _ = φ (g.eval _)
    simp only [BinaryGate.mapCoeff, BinaryGate.eval, map_add, map_mul, hw]

/-- Change the gate and readout coefficients, preserving the exact number of gates. -/
def LinearCircuit.mapCoeff {s : ℕ} (p : LinearCircuit R I O s) (φ : R →+* K) :
    LinearCircuit K I O s :=
  ⟨p.program.mapCoeff φ, fun o => (p.output o).mapCoeff φ⟩

/-- A coefficient homomorphism commutes with evaluating the circuit. -/
theorem LinearCircuit.eval_mapCoeff {s : ℕ} (p : LinearCircuit R I O s) (φ : R →+* K)
    (x : I → R) (o : O) :
    (p.mapCoeff φ).eval (fun i => φ (x i)) o = φ (p.eval x o) := by
  simp only [eval, mapCoeff, Program.value_mapCoeff]
  cases p.output o with
  | zero => simp [Readout.mapCoeff, Readout.eval]
  | scaled c w => cases w <;> simp [Readout.mapCoeff, Readout.eval]

/-- Changing the gate coefficients acts entrywise on the circuit matrix. -/
theorem LinearCircuit.matrix_mapCoeff {s : ℕ} (p : LinearCircuit R I O s) (φ : R →+* K) :
    (p.mapCoeff φ).matrix = p.matrix.map φ := by
  classical
  ext o i
  have he : (Pi.single i (1 : K) : I → K) = fun j => φ ((Pi.single i (1 : R) : I → R) j) := by
    funext j
    by_cases h : j = i <;> simp [h]
  change (p.mapCoeff φ).eval (Pi.single i 1) o = φ (p.eval (Pi.single i 1) o)
  rw [he, eval_mapCoeff]

end BaseChange

variable {R S I O : Type*} [Semiring R] [Semiring S]

/-- Applying a coefficient homomorphism to every gate and readout preserves the gate budget. -/
theorem RealizableAtMost.mapCoeff {M : Matrix O I R} {s : ℕ}
    (h : RealizableAtMost M s) (φ : R →+* S) : RealizableAtMost (M.map φ) s := by
  obtain ⟨r, hr, p, rfl⟩ := h
  exact ⟨r, hr, p.mapCoeff φ, p.matrix_mapCoeff φ⟩

end Cslib.Circuit.Linear
