/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic
public import CslibFrontier.Computability.Circuit.DecomposableGates
public import Mathlib.Algebra.MvPolynomial.Variables
public import Mathlib.RingTheory.MvPolynomial.Basic
public import CslibFrontier.Foundations.BooleanAnalysis.MultilinearExtension
import CslibFrontier.Foundations.BooleanAnalysis.BooleanQuotient
import CslibFrontier.Foundations.Data.MvPolynomial.DisjointVars

/-!
# Syntactically multilinear arithmetic circuits

An arithmetic program is *syntactically multilinear* when the two arguments of every
multiplication are reached by disjoint sets of inputs (`Cslib.Circuits.Program.IsDecomposableAt`
for `ArithOp.mul`). The polynomial computed at each wire then involves only the inputs that reach
it and has degree at most one in each of them.

The statement allows the inputs to be specialized: evaluate the program on polynomials `ρ i`, where
each `ρ i` is multilinear in its own set `V i` of variables and the sets are pairwise disjoint.
Taking `ρ i = X i` gives the polynomial computed by the program, and taking some `ρ i` to be
constants restricts it to the remaining inputs. The polynomial at a wire `w` then involves only the
variables `V i` of the inputs `i` reaching `w` and is multilinear
(`Cslib.Circuits.Program.vars_trace_subset_and_mem_restrictDegree`). So a syntactically multilinear
program computes the multilinear extension of the function it computes on the Boolean cube
(`Cslib.Circuits.Program.trace_eq_multilinearExtension`).

A circuit over a commutative ring `K` *computes the multilinear representative* of a Boolean
function `f` when the polynomial at its output is the multilinear extension of `f`, with values `0`
and `1` in `K` (`Cslib.Circuits.Circuit.ComputesMultilinear`). Lower bounds for syntactically
multilinear circuits are stated in this model; deterministic decomposable circuits and read-once
parity branching programs simulate it with linear overhead
(`Cslib.Circuits.Circuit.IsDeterministicDecomposable.exists_syntacticallyMultilinear`,
`Cslib.BranchingPrograms.NBP.exists_syntacticallyMultilinear`).

## Main results

* `Cslib.Circuits.Program.vars_trace_subset_and_mem_restrictDegree`: a syntactically multilinear
  program on specialized inputs computes multilinear polynomials in the variables of the inputs
  reaching each wire.
* `Cslib.Circuits.Program.trace_mem_restrictDegree`: it computes multilinear polynomials.
* `Cslib.Circuits.Program.trace_eq_multilinearExtension`: the polynomial at a wire is the
  multilinear extension of the values of the wire on the Boolean cube.
* `Cslib.Circuits.Circuit.computesMultilinear_iff`: a syntactically multilinear circuit computes
  the multilinear representative of a Boolean function exactly when it computes the function on
  the Boolean cube.

## Main definitions

* `Cslib.Circuits.Circuit.IsSyntacticallyMultilinear`: a syntactically multilinear circuit.
* `Cslib.Circuits.Circuit.ComputesMultilinear`: a circuit computing the multilinear representative
  of a Boolean function, the model of lower bounds for syntactically multilinear circuits.
-/

public section

namespace Cslib.Circuits

open MvPolynomial

universe u

variable {F : Type u} {n g : ℕ} {τ K : Type*} [CommSemiring K]

/-- **Syntactic multilinearity gives multilinear polynomials.** Evaluate a syntactically
multilinear program on polynomials `ρ i`, each multilinear in its own set `V i` of variables, the
sets being pairwise disjoint, and interpret each constant `c` as `C (φ c)`. The polynomial at a
wire `w` involves only the variables `V i` of the inputs `i` that reach `w`, and it has degree at
most one in each variable. -/
theorem Program.vars_trace_subset_and_mem_restrictDegree [DecidableEq τ]
    (p : Program (arithSignature F) n g) (hp : p.IsDecomposableAt (· = .mul)) (φ : F → K)
    (ρ : Fin n → MvPolynomial τ K) (V : Fin n → Finset τ)
    (hV : Pairwise fun i j => Disjoint (V i) (V j)) (hvars : ∀ i, (ρ i).vars ⊆ V i)
    (hdeg : ∀ i, ρ i ∈ restrictDegree τ K 1) (w : Wire n g) :
    (p.trace (arithInterpretationWith F (C ∘ φ)) ρ w).vars ⊆ (p.wireSupport w).biUnion V ∧
      p.trace (arithInterpretationWith F (C ∘ φ)) ρ w ∈ restrictDegree τ K 1 := by
  induction p with
  | empty =>
    cases w with
    | input i => exact ⟨by simpa using hvars i, hdeg i⟩
    | gate k => exact k.elim0
  | gate p line ih =>
    rw [isDecomposableAt_gate_iff] at hp
    refine Wire.lastCases ?_ (fun w => ?_) w
    · change ((p.gate line).eval _ ρ (Fin.last _)).vars ⊆ _ ∧
        (p.gate line).eval _ ρ (Fin.last _) ∈ _
      rw [eval_gate_last, wireSupport_gate_last]
      obtain ⟨op, args⟩ := line
      have harg (a) := ih hp.1 (args a)
      have hsub (a) : (p.wireSupport (args a)).biUnion V ⊆
          (Line.inputSupport ⟨op, args⟩ p.wireSupport).biUnion V :=
        Finset.biUnion_subset_biUnion_of_subset_left _
          (Finset.subset_biUnion_of_mem (fun a => p.wireSupport (args a)) (Finset.mem_univ a))
      cases op with
      | add =>
        refine ⟨(vars_add_subset _ _).trans (Finset.union_subset ((harg 0).1.trans (hsub 0))
          ((harg 1).1.trans (hsub 1))), add_mem (harg 0).2 (harg 1).2⟩
      | mul =>
        refine ⟨(vars_mul _ _).trans (Finset.union_subset ((harg 0).1.trans (hsub 0))
          ((harg 1).1.trans (hsub 1))),
          mul_mem_restrictDegree_of_disjoint_vars (harg 0).2 (harg 1).2 ?_⟩
        have hdisj := hp.2 rfl (show (0 : Fin 2) ≠ 1 by decide)
        refine Finset.disjoint_of_subset_left (harg 0).1 (Finset.disjoint_of_subset_right (harg 1).1
          ?_)
        rw [Finset.disjoint_biUnion_left]
        intro i hi
        rw [Finset.disjoint_biUnion_right]
        intro j hj
        exact hV fun hij => Finset.disjoint_left.mp hdisj hi (hij ▸ hj)
      | const c =>
        refine ⟨by simp [Line.eval, arithInterpretationWith], ?_⟩
        rw [mem_restrictDegree]
        intro s hs i
        classical
        have hs' : s ∈ (C (φ c) : MvPolynomial τ K).support := by
          simpa [Line.eval, arithInterpretationWith] using hs
        rw [support_C] at hs'
        split_ifs at hs' with h
        · simp at hs'
        · rw [Finset.mem_singleton.mp hs']
          exact Nat.zero_le _
    · rw [trace_gate_castSucc, wireSupport_gate_castSucc]
      exact ih hp.1 w

/-- A syntactically multilinear program, evaluated on multilinear polynomials in pairwise disjoint
sets of variables, computes multilinear polynomials. -/
theorem Program.trace_mem_restrictDegree
    (p : Program (arithSignature F) n g) (hp : p.IsDecomposableAt (· = .mul)) (φ : F → K)
    (ρ : Fin n → MvPolynomial τ K) (V : Fin n → Finset τ)
    (hV : Pairwise fun i j => Disjoint (V i) (V j)) (hvars : ∀ i, (ρ i).vars ⊆ V i)
    (hdeg : ∀ i, ρ i ∈ restrictDegree τ K 1) (w : Wire n g) :
    p.trace (arithInterpretationWith F (C ∘ φ)) ρ w ∈ restrictDegree τ K 1 := by
  classical
  exact (p.vars_trace_subset_and_mem_restrictDegree hp φ ρ V hV hvars hdeg w).2

/-- **A syntactically multilinear program computes multilinear extensions.** The polynomial at a
wire is the multilinear extension of the values of the wire at the points of the Boolean cube. -/
theorem Program.trace_eq_multilinearExtension {K : Type*} [CommRing K]
    (p : Program (arithSignature F) n g) (hp : p.IsDecomposableAt (· = .mul)) (φ : F → K)
    (w : Wire n g) :
    p.trace (arithInterpretationWith F (C ∘ φ)) X w = BitString.multilinearExtension
      fun x => p.trace (arithInterpretationWith F φ) (BitString.bitPoint x) w := by
  classical
  have hmem := p.trace_mem_restrictDegree hp φ X (fun i => {i})
    (fun i j hij => Finset.disjoint_singleton.mpr hij)
    (fun i => vars_X_subset i) (fun i => X_mem_restrictDegree le_rfl i) w
  rw [BitString.eq_multilinearExtension_of_mem_restrictDegree hmem]
  congr 1
  funext x
  let h : Homomorphism (arithInterpretationWith F (C ∘ φ)) (arithInterpretationWith F φ) :=
    ⟨MvPolynomial.eval (BitString.bitPoint x), fun op args => by
      cases op <;> simp [arithInterpretationWith]⟩
  have := congrFun (p.map_trace h X) w
  simpa [h, Function.comp_def] using this

/-! ### Circuits computing multilinear representatives -/

variable {m : ℕ}

/-- An arithmetic circuit is *syntactically multilinear* when the two arguments of every
multiplication are reached by disjoint sets of inputs. -/
abbrev Circuit.IsSyntacticallyMultilinear (c : Circuit (arithSignature F) n m) : Prop :=
  c.program.IsDecomposableAt (· = .mul)

/-- Evaluating the polynomial computed by an arithmetic circuit on specialized inputs evaluates the
circuit on the evaluated inputs. -/
theorem Circuit.eval_eval {τ K : Type*} [CommSemiring K] (c : Circuit (arithSignature F) n m)
    (φ : F → K) (ρ : Fin n → MvPolynomial τ K) (z : τ → K) (j : Fin m) :
    MvPolynomial.eval z (c.eval (arithInterpretationWith F (C ∘ φ)) ρ j) =
      c.eval (arithInterpretationWith F φ) (fun i => MvPolynomial.eval z (ρ i)) j := by
  let h : Homomorphism (arithInterpretationWith F (C ∘ φ)) (arithInterpretationWith F φ) :=
    ⟨MvPolynomial.eval z, fun op args => by cases op <;> simp [arithInterpretationWith]⟩
  simpa [h, Function.comp_def] using congrFun (c.map_eval h ρ) j

variable {K : Type*} [CommRing K]

/-- An arithmetic circuit over `K` *computes the multilinear representative* of the Boolean
function `f` when the polynomial at its output is the multilinear extension of `f`, with values
`0` and `1` in `K`. -/
@[expose]
def Circuit.ComputesMultilinear (c : Circuit (arithSignature K) n 1)
    (f : (Fin n → Bool) → Bool) : Prop :=
  c.eval (arithInterpretationWith K C) X 0 =
    BitString.multilinearExtension fun z => BitString.bitVal K (f z)

/-- A circuit computing the multilinear representative of `f` computes `f` on the Boolean cube. -/
theorem Circuit.ComputesMultilinear.eval_bitPoint {c : Circuit (arithSignature K) n 1}
    {f : (Fin n → Bool) → Bool} (h : c.ComputesMultilinear f) (z : Fin n → Bool) :
    c.eval (arithInterpretation K) (BitString.bitPoint z) 0 = BitString.bitVal K (f z) := by
  classical
  have := congrArg (MvPolynomial.eval (BitString.bitPoint z)) h
  rw [show (arithInterpretationWith K C : Interpretation (arithSignature K) _) =
    arithInterpretationWith K (C ∘ id) from rfl, c.eval_eval] at this
  simp only [eval_X, BitString.eval_multilinearExtension] at this
  exact this

/-- **Syntactically multilinear circuits compute multilinear representatives.** A syntactically
multilinear circuit computes the multilinear representative of `f` exactly when it computes `f` on
the Boolean cube. -/
theorem Circuit.computesMultilinear_iff {c : Circuit (arithSignature K) n 1}
    (hc : c.IsSyntacticallyMultilinear) {f : (Fin n → Bool) → Bool} :
    c.ComputesMultilinear f ↔
      ∀ z, c.eval (arithInterpretation K) (BitString.bitPoint z) 0 = BitString.bitVal K (f z) := by
  refine ⟨fun h => h.eval_bitPoint, fun h => ?_⟩
  have := c.program.trace_eq_multilinearExtension hc (id : K → K) (c.outputs 0)
  rw [Circuit.ComputesMultilinear]
  refine this.trans ?_
  congr 1
  funext z
  exact h z

end Cslib.Circuits
