/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.MatrixMultiplication.Exponent
public import Cslib.Computability.Circuit.Simulation
import CslibFrontier.Computability.Circuit.Program
import CslibFrontier.Computability.Circuit.Simulation
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Fintype.Prod

/-!
# Strassen bi-homogeneous rank extraction from matrix-multiplication circuits

Converse to Strassen's block recursion (`admissibleExponent_of_rank`): over any infinite integral
domain `K` (in particular any characteristic-zero field), an arithmetic circuit
`C : Circuit (arithSignature K) (n * n + n * n) (n * n)` computing `n × n` matrix multiplication
yields a bilinear algorithm of rank at most `2 * C.program.cost ArithOp.mulCost` — and hence at
most `2 * C.size` — for `Tensor.mm n n n` (`rank_mm_two_mul_mulCost`, `rank_mm_two_mul_size`,
[Strassen][Strassen1973b];
[Bürgisser, Clausen and Shokrollahi][BurgisserClausenShokrollahi1997], Chapter 14). Here
`ArithOp.mulCost` counts all `.mul` gates in division-free `arithSignature K` circuits (including
multiplications by constants, which Strassen's nonscalar count omits).

Feeding `(s • A, t • B)` in the bivariate polynomial ring `K[t][s]` isolates the `(1, 1)`
bi-homogeneous component of every wire, where each `.mul` gate contributes at most two rank-one
bilinear products `(L_A(x) · R_B(y)) + (L_A(y) · R_B(x))`. Consequently (`exists_rank_mm_le_rpow`),
over any characteristic-zero field `K` and every `τ > omega K`, there exists `c > 0` such that
`Tensor.mm D D D` has rank at most `c * D ^ τ` for every `D ≥ 1`.

## Main results

* `Cslib.Circuits.Arithmetic.MatrixMultiplication.two_le_omega`: over a nontrivial commutative
  semiring `K`, `2 ≤ omega K`.
* `Cslib.Circuits.Arithmetic.MatrixMultiplication.rank_mm_two_mul_mulCost`: `ComputesMatMul K C`
  implies `Tensor.Rank (2 * C.program.cost ArithOp.mulCost) (Tensor.mm n n n)` over an infinite
  integral domain `K`.
* `Cslib.Circuits.Arithmetic.MatrixMultiplication.rank_mm_two_mul_size`: `ComputesMatMul K C`
  implies `Tensor.Rank (2 * C.size) (Tensor.mm n n n)` over an infinite integral domain `K`.
* `Cslib.Circuits.Arithmetic.MatrixMultiplication.exists_rank_mm_le_rpow`: for every `τ > omega K`
  in characteristic zero, `Tensor.mm D D D` has rank `O(D ^ τ)`.

## References

* [V. Strassen, *Vermeidung von Divisionen*][Strassen1973b]
* [P. Bürgisser, M. Clausen, M. A. Shokrollahi, *Algebraic Complexity
  Theory*][BurgisserClausenShokrollahi1997], Chapter 14
-/

public section

namespace Cslib.Circuits.Arithmetic.MatrixMultiplication

open Cslib.Circuits Cslib.Tensor

/-- Over any nontrivial commutative semiring `K`, the matrix-multiplication exponent is at least
`2`. -/
theorem two_le_omega (K : Type*) [CommSemiring K] [Nontrivial K] : 2 ≤ omega K :=
  le_csInf ⟨3, admissibleExponent_three (K := K)⟩ fun _ h => two_le_of_admissibleExponent h

/-! ### Strassen `(1, 1)` bi-homogeneous rank extraction -/

/-- Bivariate polynomials `K[t][s]`, with outer variable `s` and inner variable `t`. -/
private abbrev Biv (K : Type*) [CommSemiring K] := Polynomial (Polynomial K)

/-- The `(i, j)` coefficient of `P(s, t) ∈ K[t][s]` (degree `i` in `s`, degree `j` in `t`). -/
private def bivCoeff {K : Type*} [CommSemiring K] (i j : ℕ) (P : Biv K) : K :=
  (P.coeff i).coeff j

private theorem bivCoeff_zero {K : Type*} [CommSemiring K] (i j : ℕ) :
    bivCoeff i j (0 : Biv K) = 0 := by
  simp [bivCoeff]

private theorem bivCoeff_add {K : Type*} [CommSemiring K] (i j : ℕ) (P Q : Biv K) :
    bivCoeff i j (P + Q) = bivCoeff i j P + bivCoeff i j Q := by
  simp [bivCoeff]

private theorem bivCoeff_const {K : Type*} [CommSemiring K] (c : K) :
    bivCoeff 0 0 (Polynomial.C (Polynomial.C c) : Biv K) = c ∧
      bivCoeff 1 0 (Polynomial.C (Polynomial.C c) : Biv K) = 0 ∧
      bivCoeff 0 1 (Polynomial.C (Polynomial.C c) : Biv K) = 0 ∧
      bivCoeff 1 1 (Polynomial.C (Polynomial.C c) : Biv K) = 0 := by
  simp [bivCoeff]

private theorem bivCoeff_mul_00 {K : Type*} [CommSemiring K] (P Q : Biv K) :
    bivCoeff 0 0 (P * Q) = bivCoeff 0 0 P * bivCoeff 0 0 Q := by
  simp [bivCoeff]

private theorem bivCoeff_mul_10 {K : Type*} [CommSemiring K] (P Q : Biv K) :
    bivCoeff 1 0 (P * Q) = bivCoeff 0 0 P * bivCoeff 1 0 Q + bivCoeff 1 0 P * bivCoeff 0 0 Q := by
  simp [bivCoeff, Polynomial.mul_coeff_one]

private theorem bivCoeff_mul_01 {K : Type*} [CommSemiring K] (P Q : Biv K) :
    bivCoeff 0 1 (P * Q) = bivCoeff 0 0 P * bivCoeff 0 1 Q + bivCoeff 0 1 P * bivCoeff 0 0 Q := by
  simp [bivCoeff, Polynomial.mul_coeff_one]

private theorem bivCoeff_mul_11 {K : Type*} [CommSemiring K] (P Q : Biv K) :
    bivCoeff 1 1 (P * Q) =
      bivCoeff 0 0 P * bivCoeff 1 1 Q + bivCoeff 1 1 P * bivCoeff 0 0 Q +
        bivCoeff 1 0 P * bivCoeff 0 1 Q + bivCoeff 0 1 P * bivCoeff 1 0 Q := by
  simp only [bivCoeff, Polynomial.mul_coeff_one, Polynomial.coeff_add]
  ring

/-- Bivariate inputs `(s • A, t • B)` to an `n × n` matrix multiplication circuit. -/
private noncomputable def bivMatInputs {K : Type*} [CommSemiring K] {n : ℕ}
    (A B : Fin n × Fin n → K) : Fin (n * n + n * n) → Biv K :=
  Fin.append
    (fun i => Polynomial.C (Polynomial.C (A (finProdFinEquiv.symm i))) * Polynomial.X)
    (fun j => Polynomial.C (Polynomial.C (B (finProdFinEquiv.symm j)) * Polynomial.X))

/-- Evaluate `P(s, t) ∈ K[t][s]` at `(s₀, t₀) ∈ K × K`. -/
private noncomputable def evalBiv {K : Type*} [CommSemiring K] (s₀ t₀ : K) : Biv K →+* K :=
  Polynomial.eval₂RingHom (Polynomial.evalRingHom t₀) s₀

private theorem evalBiv_bivMatInputs {K : Type*} [CommSemiring K] {n : ℕ}
    (A B : Fin n × Fin n → K) (s₀ t₀ : K) :
    evalBiv s₀ t₀ ∘ bivMatInputs A B =
      matrixInputs K (Matrix.of fun i j => s₀ * A (i, j))
        (Matrix.of fun i j => t₀ * B (i, j)) := by
  funext idx
  refine Fin.addCases (fun i => ?_) (fun j => ?_) idx
  · simp only [Function.comp_apply, bivMatInputs, matrixInputs, Fin.append_left, evalBiv, entry,
      Matrix.of_apply, Prod.mk.eta, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_mul,
      Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.coe_evalRingHom, Polynomial.eval_C,
      mul_comm]
  · simp only [Function.comp_apply, bivMatInputs, matrixInputs, Fin.append_right, evalBiv, entry,
      Matrix.of_apply, Prod.mk.eta, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
      Polynomial.coe_evalRingHom, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
      mul_comm]

/-- Evaluating an arithmetic circuit in `Biv K` and specializing `(s, t) := (s₀, t₀)` agrees with
evaluating the circuit in `K` at the specialized inputs. -/
private theorem evalBiv_circuit_eval {K : Type*} [CommSemiring K] {m p : ℕ}
    (C : Circuit (arithSignature K) m p) (inp : Fin m → Biv K) (s₀ t₀ : K) (o : Fin p) :
    evalBiv s₀ t₀
        (C.eval (arithInterpretationWith K (Polynomial.C ∘ Polynomial.C)) inp o) =
      C.eval (arithInterpretation K) (evalBiv s₀ t₀ ∘ inp) o := by
  let h : Homomorphism (arithInterpretationWith K (Polynomial.C ∘ Polynomial.C))
      (arithInterpretation K) :=
    ⟨evalBiv s₀ t₀, fun op args => by
      cases op <;> simp [arithInterpretation, arithInterpretationWith, evalBiv]⟩
  simpa [h, Function.comp_def] using congrFun (C.map_eval h inp) o

private theorem trace_gate_add {K : Type*} [CommSemiring K] {m p : ℕ}
    (C : Circuit (arithSignature K) m p) (I : Interpretation (arithSignature K) (Biv K))
    (hadd : ∀ args, I .add args = args 0 + args 1) (inp : Fin m → Biv K) (k : Fin C.size)
    (hop : (C.program.lines k).op = .add) :
    C.program.trace I inp (.gate k) =
      C.program.trace I inp
          ((C.program.lines k).wires (Fin.cast (congrArg (ArithOp.arity K) hop.symm) 0)) +
        C.program.trace I inp
          ((C.program.lines k).wires (Fin.cast (congrArg (ArithOp.arity K) hop.symm) 1)) := by
  rw [C.program.trace_gate]
  revert hop
  generalize C.program.lines k = ln
  rcases ln with ⟨op, wires⟩
  intro hop
  dsimp only at hop ⊢
  subst hop
  exact hadd _

private theorem trace_gate_mul {K : Type*} [CommSemiring K] {m p : ℕ}
    (C : Circuit (arithSignature K) m p) (I : Interpretation (arithSignature K) (Biv K))
    (hmul : ∀ args, I .mul args = args 0 * args 1) (inp : Fin m → Biv K) (k : Fin C.size)
    (hop : (C.program.lines k).op = .mul) :
    C.program.trace I inp (.gate k) =
      C.program.trace I inp
          ((C.program.lines k).wires (Fin.cast (congrArg (ArithOp.arity K) hop.symm) 0)) *
        C.program.trace I inp
          ((C.program.lines k).wires (Fin.cast (congrArg (ArithOp.arity K) hop.symm) 1)) := by
  rw [C.program.trace_gate]
  revert hop
  generalize C.program.lines k = ln
  rcases ln with ⟨op, wires⟩
  intro hop
  dsimp only at hop ⊢
  subst hop
  exact hmul _

private theorem trace_gate_const {K : Type*} [CommSemiring K] {m p : ℕ}
    (C : Circuit (arithSignature K) m p) (I : Interpretation (arithSignature K) (Biv K))
    (c : K) (hconst : ∀ args, I (.const c) args = Polynomial.C (Polynomial.C c))
    (inp : Fin m → Biv K) (k : Fin C.size) (hop : (C.program.lines k).op = .const c) :
    C.program.trace I inp (.gate k) = Polynomial.C (Polynomial.C c) := by
  rw [C.program.trace_gate]
  revert hop
  generalize C.program.lines k = ln
  rcases ln with ⟨op, wires⟩
  intro hop
  dsimp only at hop ⊢
  subst hop
  exact hconst _

/-- Wire-by-wire structural invariants of `C.program.trace` on `bivMatInputs A B`:
`(0, 0)` is constant, `(1, 0)` is linear in `A`, `(0, 1)` is linear in `B`, and `(1, 1)` is a
`K`-linear combination of `2 * C.program.cost ArithOp.mulCost` fixed bilinear products. -/
private theorem exists_biv_wire_decomp {K : Type*} [CommRing K] {n : ℕ}
    (C : Circuit (arithSignature K) (n * n + n * n) (n * n)) :
    ∃ (α β : Fin (2 * C.program.cost ArithOp.mulCost) → Fin n × Fin n → K),
      ∀ w : Wire (n * n + n * n) C.size,
        (∃ c₀ : K, ∀ A B : Fin n × Fin n → K,
          bivCoeff 0 0 (C.program.trace
            (arithInterpretationWith K (Polynomial.C ∘ Polynomial.C))
            (bivMatInputs A B) w) = c₀) ∧
        (∃ fA : Fin n × Fin n → K, ∀ A B : Fin n × Fin n → K,
          bivCoeff 1 0 (C.program.trace
            (arithInterpretationWith K (Polynomial.C ∘ Polynomial.C))
            (bivMatInputs A B) w) = ∑ x, fA x * A x) ∧
        (∃ fB : Fin n × Fin n → K, ∀ A B : Fin n × Fin n → K,
          bivCoeff 0 1 (C.program.trace
            (arithInterpretationWith K (Polynomial.C ∘ Polynomial.C))
            (bivMatInputs A B) w) = ∑ y, fB y * B y) ∧
        (∃ γ : Fin (2 * C.program.cost ArithOp.mulCost) → K, ∀ A B : Fin n × Fin n → K,
          bivCoeff 1 1 (C.program.trace
            (arithInterpretationWith K (Polynomial.C ∘ Polynomial.C))
            (bivMatInputs A B) w) =
              ∑ ν, γ ν * ((∑ x, α ν x * A x) * (∑ y, β ν y * B y))) := by
  classical
  set I := arithInterpretationWith K (Polynomial.C ∘ Polynomial.C : K → Biv K)
  have hlin : ∀ w : Wire (n * n + n * n) C.size,
      (∃ c₀ : K, ∀ A B, bivCoeff 0 0 (C.program.trace I (bivMatInputs A B) w) = c₀) ∧
      (∃ fA : Fin n × Fin n → K, ∀ A B,
        bivCoeff 1 0 (C.program.trace I (bivMatInputs A B) w) = ∑ x, fA x * A x) ∧
      (∃ fB : Fin n × Fin n → K, ∀ A B,
        bivCoeff 0 1 (C.program.trace I (bivMatInputs A B) w) = ∑ y, fB y * B y) := by
    refine C.program.wire_induction ?_ ?_
    · intro idx
      refine Fin.addCases (fun i => ?_) (fun j => ?_) idx
      · refine ⟨⟨0, fun A B => ?_⟩, ⟨Pi.single (finProdFinEquiv.symm i) 1, fun A B => ?_⟩,
          ⟨0, fun A B => ?_⟩⟩ <;> simp [Program.trace, bivMatInputs, bivCoeff, Pi.single_apply]
      · refine ⟨⟨0, fun A B => ?_⟩, ⟨0, fun A B => ?_⟩,
          ⟨Pi.single (finProdFinEquiv.symm j) 1, fun A B => ?_⟩⟩ <;>
          simp [Program.trace, bivMatInputs, bivCoeff, Pi.single_apply, -Fin.natAdd_eq_addNat]
    · intro k ih
      rcases hop : (C.program.lines k).op with _ | _ | c
      · let s0 := Fin.cast (congrArg (ArithOp.arity K) hop.symm) 0
        let s1 := Fin.cast (congrArg (ArithOp.arity K) hop.symm) 1
        obtain ⟨⟨c0, hc0⟩, ⟨fA0, hfA0⟩, ⟨fB0, hfB0⟩⟩ := ih s0
        obtain ⟨⟨c1, hc1⟩, ⟨fA1, hfA1⟩, ⟨fB1, hfB1⟩⟩ := ih s1
        have htr (A B) : C.program.trace I (bivMatInputs A B) (.gate k) =
            C.program.trace I (bivMatInputs A B) ((C.program.lines k).wires s0) +
              C.program.trace I (bivMatInputs A B) ((C.program.lines k).wires s1) :=
          trace_gate_add C I (fun _ => rfl) (bivMatInputs A B) k hop
        refine ⟨⟨c0 + c1, fun A B => by rw [htr, bivCoeff_add, hc0, hc1]⟩,
          ⟨fA0 + fA1, fun A B => by
            rw [htr, bivCoeff_add, hfA0, hfA1, ← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl fun x _ => by simp [Pi.add_apply, add_mul]⟩,
          ⟨fB0 + fB1, fun A B => by
            rw [htr, bivCoeff_add, hfB0, hfB1, ← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl fun y _ => by simp [Pi.add_apply, add_mul]⟩⟩
      · let s0 := Fin.cast (congrArg (ArithOp.arity K) hop.symm) 0
        let s1 := Fin.cast (congrArg (ArithOp.arity K) hop.symm) 1
        obtain ⟨⟨c0, hc0⟩, ⟨fA0, hfA0⟩, ⟨fB0, hfB0⟩⟩ := ih s0
        obtain ⟨⟨c1, hc1⟩, ⟨fA1, hfA1⟩, ⟨fB1, hfB1⟩⟩ := ih s1
        have htr (A B) : C.program.trace I (bivMatInputs A B) (.gate k) =
            C.program.trace I (bivMatInputs A B) ((C.program.lines k).wires s0) *
              C.program.trace I (bivMatInputs A B) ((C.program.lines k).wires s1) :=
          trace_gate_mul C I (fun _ => rfl) (bivMatInputs A B) k hop
        refine ⟨⟨c0 * c1, fun A B => by rw [htr, bivCoeff_mul_00, hc0, hc1]⟩,
          ⟨c0 • fA1 + c1 • fA0, fun A B => by
            rw [htr, bivCoeff_mul_10, hc0, hc1, hfA0, hfA1, Finset.mul_sum, Finset.sum_mul,
              ← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl fun x _ => by simp [Pi.add_apply, Pi.smul_apply]; ring⟩,
          ⟨c0 • fB1 + c1 • fB0, fun A B => by
            rw [htr, bivCoeff_mul_01, hc0, hc1, hfB0, hfB1, Finset.mul_sum, Finset.sum_mul,
              ← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl fun y _ => by simp [Pi.add_apply, Pi.smul_apply]; ring⟩⟩
      · have htr (A B) : C.program.trace I (bivMatInputs A B) (.gate k) =
            Polynomial.C (Polynomial.C c) :=
          trace_gate_const C I c (fun _ => rfl) (bivMatInputs A B) k hop
        obtain ⟨h00, h10, h01, -⟩ := bivCoeff_const c
        exact ⟨⟨c, fun A B => by rw [htr, h00]⟩,
          ⟨0, fun A B => by rw [htr, h10]; simp⟩,
          ⟨0, fun A B => by rw [htr, h01]; simp⟩⟩
  choose c₀ hc₀ using fun w => (hlin w).1
  choose fA hfA using fun w => (hlin w).2.1
  choose fB hfB using fun w => (hlin w).2.2
  let MulGate := {k : Fin C.size // (C.program.lines k).op = .mul}
  set m := C.program.cost ArithOp.mulCost
  have hcard_mul : Fintype.card MulGate = m := by
    rw [Fintype.card_subtype]
    dsimp only [m]
    rw [Program.cost_eq_sum]
    have hop_cost (k : Fin C.size) :
        ArithOp.mulCost (C.program.lines k).op =
          if (C.program.lines k).op = .mul then 1 else 0 := by
      cases (C.program.lines k).op <;> simp [ArithOp.mulCost]
    simp_rw [hop_cost]
    rw [Finset.sum_boole, Nat.cast_id]
  have hcard : Fintype.card (Fin 2 × MulGate) = 2 * m := by
    rw [Fintype.card_prod, Fintype.card_fin, hcard_mul]
  let e : (Fin 2 × MulGate) ≃ Fin (2 * m) := Fintype.equivFinOfCardEq hcard
  let mulArg (g : MulGate) (i : Fin 2) : Fin (ArithOp.arity K (C.program.lines g.val).op) :=
    Fin.cast (congrArg (ArithOp.arity K) g.property.symm) i
  let α : Fin (2 * m) → Fin n × Fin n → K := fun ν =>
    let p := e.symm ν
    if p.1 = 0 then fA ((C.program.lines p.2.val).wires (mulArg p.2 0))
    else fA ((C.program.lines p.2.val).wires (mulArg p.2 1))
  let β : Fin (2 * m) → Fin n × Fin n → K := fun ν =>
    let p := e.symm ν
    if p.1 = 0 then fB ((C.program.lines p.2.val).wires (mulArg p.2 1))
    else fB ((C.program.lines p.2.val).wires (mulArg p.2 0))
  refine ⟨α, β, fun w => ⟨⟨c₀ w, hc₀ w⟩, ⟨fA w, hfA w⟩, ⟨fB w, hfB w⟩, ?_⟩⟩
  refine C.program.wire_induction
    (P := fun w => ∃ γ : Fin (2 * m) → K, ∀ A B : Fin n × Fin n → K,
      bivCoeff 1 1 (C.program.trace I (bivMatInputs A B) w) =
        ∑ ν, γ ν * ((∑ x, α ν x * A x) * (∑ y, β ν y * B y))) ?_ ?_ w
  · intro idx
    refine ⟨0, fun A B => ?_⟩
    simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero]
    refine Fin.addCases (fun i => ?_) (fun j => ?_) idx <;>
      simp [Program.trace, bivMatInputs, bivCoeff, -Fin.natAdd_eq_addNat]
  · intro k ih
    rcases hop : (C.program.lines k).op with _ | _ | c
    · let s0 := Fin.cast (congrArg (ArithOp.arity K) hop.symm) 0
      let s1 := Fin.cast (congrArg (ArithOp.arity K) hop.symm) 1
      obtain ⟨γ0, hγ0⟩ := ih s0
      obtain ⟨γ1, hγ1⟩ := ih s1
      have htr (A B) : C.program.trace I (bivMatInputs A B) (.gate k) =
          C.program.trace I (bivMatInputs A B) ((C.program.lines k).wires s0) +
            C.program.trace I (bivMatInputs A B) ((C.program.lines k).wires s1) :=
        trace_gate_add C I (fun _ => rfl) (bivMatInputs A B) k hop
      refine ⟨γ0 + γ1, fun A B => ?_⟩
      rw [htr, bivCoeff_add, hγ0, hγ1, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun ν _ => by simp [Pi.add_apply, add_mul]
    · let s0 := mulArg ⟨k, hop⟩ 0
      let s1 := mulArg ⟨k, hop⟩ 1
      let w0 := (C.program.lines k).wires s0
      let w1 := (C.program.lines k).wires s1
      have htr (A B) : C.program.trace I (bivMatInputs A B) (.gate k) =
          C.program.trace I (bivMatInputs A B) w0 *
            C.program.trace I (bivMatInputs A B) w1 :=
        trace_gate_mul C I (fun _ => rfl) (bivMatInputs A B) k hop
      obtain ⟨γ0, hγ0⟩ := ih s0
      obtain ⟨γ1, hγ1⟩ := ih s1
      let slot0 : Fin (2 * m) := e (0, ⟨k, hop⟩)
      let slot1 : Fin (2 * m) := e (1, ⟨k, hop⟩)
      have hαβ : α slot0 = fA w0 ∧ β slot0 = fB w1 ∧ α slot1 = fA w1 ∧ β slot1 = fB w0 := by
        refine ⟨?_, ?_, ?_, ?_⟩ <;> dsimp only [α, β, slot0, slot1, w0, w1, s0, s1] <;>
          rw [e.symm_apply_apply] <;> simp
      refine ⟨c₀ w0 • γ1 + c₀ w1 • γ0 + Pi.single slot0 1 + Pi.single slot1 1,
        fun A B => ?_⟩
      rw [htr, bivCoeff_mul_11, hc₀ w0, hc₀ w1, hfA w0, hfB w1, hfA w1, hfB w0, hγ0, hγ1]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib,
        mul_assoc, ← Finset.mul_sum, Pi.single_apply, ite_mul, one_mul, zero_mul,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true, hαβ]
      ring
    · have htr (A B) : C.program.trace I (bivMatInputs A B) (.gate k) =
          Polynomial.C (Polynomial.C c) :=
        trace_gate_const C I c (fun _ => rfl) (bivMatInputs A B) k hop
      refine ⟨0, fun A B => ?_⟩
      rw [htr, (bivCoeff_const c).2.2.2]
      simp

/-- **Strassen `(1, 1)` bi-homogeneous rank extraction (multiplication count).** Over any infinite
integral domain `K` (in particular any characteristic-zero field), an arithmetic circuit computing
`n × n` matrix multiplication with `m = C.program.cost ArithOp.mulCost` multiplication gates
yields a bilinear algorithm of rank at most `2 * m` for `Tensor.mm n n n`. Here `ArithOp.mulCost`
counts all `.mul` gates in division-free `arithSignature K` circuits. -/
theorem rank_mm_two_mul_mulCost {K : Type*} [CommRing K] [IsDomain K] [Infinite K] {n : ℕ}
    {C : Circuit (arithSignature K) (n * n + n * n) (n * n)} (hC : ComputesMatMul K C) :
    Rank (2 * C.program.cost ArithOp.mulCost) (mm n n n : Tensor K _ _ _) := by
  set m := C.program.cost ArithOp.mulCost
  obtain ⟨α, β, hwire⟩ := exists_biv_wire_decomp C
  choose γ hγ using fun c : Fin n × Fin n => (hwire (C.outputs (finProdFinEquiv c))).2.2.2
  let Mα : Matrix (Fin (2 * m)) (Fin n × Fin n) K := Matrix.of α
  let Mβ : Matrix (Fin (2 * m)) (Fin n × Fin n) K := Matrix.of β
  let Mγ : Matrix (Fin n × Fin n) (Fin (2 * m)) K := Matrix.of γ
  refine ⟨Mα, Mβ, Mγ, Tensor.ext_of_bil fun A B => ?_⟩
  funext c
  rw [bil_restrict, bil_mm]
  have hunit (u w : Fin (2 * m) → K) :
      (unit (2 * m) : Tensor K _ _ _).bil u w = fun ν => u ν * w ν := by
    funext ν
    simp [Tensor.bil, unit_apply, ite_and, ite_mul]
  rw [hunit]
  simp only [Matrix.mulVec, dotProduct, Mα, Mβ, Mγ, Matrix.of_apply]
  rw [← hγ c A B]
  set P : Biv K := C.eval (arithInterpretationWith K (Polynomial.C ∘ Polynomial.C))
    (bivMatInputs A B) (finProdFinEquiv c)
  change bivCoeff 1 1 P = ∑ j, A (c.1, j) * B (j, c.2)
  set val : K := ∑ j, A (c.1, j) * B (j, c.2)
  have heval (s₀ t₀ : K) : evalBiv s₀ t₀ P = s₀ * (t₀ * val) := by
    dsimp only [P]
    rw [evalBiv_circuit_eval, evalBiv_bivMatInputs, hC]
    simp only [entry, Equiv.symm_apply_apply, Matrix.mul_apply, Matrix.of_apply]
    dsimp only [val]
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hcoeff1_eval (t₀ : K) : (P.coeff 1).eval t₀ = t₀ * val := by
    have hpoly : P.map (Polynomial.evalRingHom t₀) = Polynomial.C (t₀ * val) * Polynomial.X := by
      refine Polynomial.funext fun s₀ => ?_
      rw [Polynomial.eval_map]
      change evalBiv s₀ t₀ P = _
      rw [heval s₀ t₀, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, mul_comm]
    have hc1 := congrArg (fun q : Polynomial K => q.coeff 1) hpoly
    simpa [Polynomial.coeff_map] using hc1
  have hp1 : P.coeff 1 = Polynomial.C val * Polynomial.X := by
    refine Polynomial.funext fun t₀ => ?_
    rw [hcoeff1_eval, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, mul_comm]
  dsimp only [bivCoeff]
  rw [hp1]
  simp

/-- **Strassen `(1, 1)` bi-homogeneous rank extraction (circuit size).** Over any infinite integral
domain `K` (in particular any characteristic-zero field), an arithmetic circuit of size `s`
computing `n × n` matrix multiplication yields a bilinear algorithm of rank at most `2 * s` for
`Tensor.mm n n n`. -/
theorem rank_mm_two_mul_size {K : Type*} [CommRing K] [IsDomain K] [Infinite K] {n : ℕ}
    {C : Circuit (arithSignature K) (n * n + n * n) (n * n)} (hC : ComputesMatMul K C) :
    Rank (2 * C.size) (mm n n n : Tensor K _ _ _) := by
  have hcost : C.program.cost ArithOp.mulCost ≤ C.size := by
    simpa using C.program.cost_le_mul (b := 1) fun op => by cases op <;> simp [ArithOp.mulCost]
  exact (rank_mm_two_mul_mulCost hC).mono (Nat.mul_le_mul_left 2 hcost)

/-- **From `omega K` to bilinear rank of square matrix multiplication.** Over a characteristic-zero
field `K`, for every `τ > omega K` there exists `c > 0` such that for all `D ≥ 1`, `Tensor.mm D D D`
has rank `r ≤ c * D ^ τ`. -/
theorem exists_rank_mm_le_rpow (K : Type*) [Field K] [CharZero K] {τ : ℝ} (hτ : omega K < τ) :
    ∃ c : ℝ, 0 < c ∧ ∀ D : ℕ, 1 ≤ D →
      ∃ r : ℕ, (r : ℝ) ≤ c * (D : ℝ) ^ τ ∧ Rank r (mm D D D : Tensor K _ _ _) := by
  have : Infinite K := Infinite.of_injective (Nat.cast : ℕ → K) Nat.cast_injective
  set ε : ℝ := (τ - omega K) / 2
  have hε : 0 < ε := by dsimp only [ε]; linarith
  have hne : {τ' : ℝ | AdmissibleExponent K τ'}.Nonempty := ⟨3, admissibleExponent_three (K := K)⟩
  obtain ⟨τ₀, hτ₀_adm, hτ₀_lt⟩ := exists_lt_of_csInf_lt hne (by dsimp only [ε]; linarith :
    omega K < omega K + ε)
  have hadm : AdmissibleExponent K (omega K + ε) := hτ₀_adm.mono hτ₀_lt.le
  obtain ⟨c₀, hc₀, hC⟩ := hadm ε hε
  have hτ_eq : omega K + ε + ε = τ := by dsimp only [ε]; ring
  refine ⟨2 * c₀, by positivity, fun D hD => ?_⟩
  obtain ⟨C, hcomp, hsize⟩ := hC D hD
  rw [hτ_eq] at hsize
  refine ⟨2 * C.size, ?_, rank_mm_two_mul_size hcomp⟩
  push_cast
  linarith

end Cslib.Circuits.Arithmetic.MatrixMultiplication
