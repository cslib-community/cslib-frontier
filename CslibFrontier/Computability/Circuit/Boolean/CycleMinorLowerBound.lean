/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.BranchingProgram.ReadOnceParityArithmetic
public import CslibFrontier.Computability.Circuit.Arithmetic.BalancedCuts
public import CslibFrontier.Computability.Circuit.Arithmetic.HamiltonianCycle
public import CslibFrontier.Computability.Circuit.Boolean.CycleMinor
public import CslibFrontier.Computability.Circuit.Boolean.DeterministicDecomposableArithmetic
public import Mathlib.Logic.Function.DependsOn
import CslibFrontier.Foundations.BooleanAnalysis.BooleanQuotient
import CslibFrontier.Foundations.Data.MvPolynomial.DisjointVars

/-!
# Syntactically multilinear circuits for the cycle-and-minor function

The size lower bounds of #8623 for the cycle-and-minor function `Cslib.Circuits.cycleMinorFn` are
lower bounds for syntactically multilinear arithmetic circuits computing its multilinear
representative (`Cslib.Circuits.Circuit.ComputesMultilinear`). Syntactically multilinear circuits
simulate deterministic decomposable circuits and read-once parity branching programs with linear
overhead, so the bounds for these models are corollaries. All of them reduce to two algebraic
measures:

* `Cslib.Circuits.cutCover K d a b`: the least number of products across sets of between `a` and
  `b` of the `d` coordinates that, from one list of sets for all `C`, write every table
  `T_C x = det C_x` as a sum (`Cslib.Circuits.minorTable`). Here `C` ranges over the
  `d / 2 × d` matrices over `K`, and `C_x` is the minor of `C` on the columns where `x` is one, with
  `T_C x = 0` unless there are `d / 2` of them.
* `Cslib.Circuits.hcComponentSize K d`: the least size of an arithmetic circuit whose homogeneous
  component of degree `d` is the Hamiltonian cycle polynomial `HC_d`.

**The main theorem** (`Cslib.Circuits.measures_le_of_syntacticallyMultilinear`): a syntactically
multilinear circuit with `s` gates computing the multilinear representative of the function over a
field of characteristic two gives `cutCover K d a b ≤ 2 s + 1` and `hcComponentSize K d ≤ s + 1`.
On the minor branch, the circuit with the first `d / 2` rows of `Y` set to `C` and the others to
zero computes `T_C` on the coordinates of `x`, and the cut lemma
(`Cslib.Circuits.Circuit.exists_balanced_cuts`) writes it as such a sum. On the cycle branch, the
circuit with `b` and `x` set to zero computes the multilinear representative of the cycle test,
whose component of degree `d` is `HC_d`; this part holds over every field.

**Corollaries.** A d-D with `s` gates
(`Cslib.Circuits.Circuit.IsDeterministicDecomposable.cutCover_le`,
`Cslib.Circuits.Circuit.IsDeterministicDecomposable.hcComponentSize_le`) and a read-once parity
branching program with `w` wires (`Cslib.BranchingPrograms.NBP.cutCover_le`,
`Cslib.BranchingPrograms.NBP.hcComponentSize_le`) computing the function bound both measures
linearly, through the simulations
`Cslib.Circuits.Circuit.IsDeterministicDecomposable.exists_syntacticallyMultilinear` and
`Cslib.BranchingPrograms.NBP.exists_syntacticallyMultilinear`.

The manuscript of #8623 [Anonymous, Theorem 1][Anonymous2026MultilinearCircuits] derives
`2 ^ (N ^ δ)` lower bounds from lower bounds on these measures, proved with the spectral geometry of
tensors; those lower bounds are not formalized here.

## Main definitions

* `Cslib.Circuits.cycleMinorFn`: the cycle-and-minor function on `d * d + d + 1` bits.
* `Cslib.Circuits.minorTable`, `Cslib.Circuits.cutCover`, `Cslib.Circuits.hcComponentSize`: the two
  measures; `Cslib.Circuits.minorTable_eq` computes the minor tables.

## Main results

* `Cslib.Circuits.measures_le_of_syntacticallyMultilinear`: the main theorem, with its two halves
  `Cslib.Circuits.cutCover_le_of_syntacticallyMultilinear` and
  `Cslib.Circuits.hcComponentSize_le_of_syntacticallyMultilinear`.
* `Cslib.Circuits.Circuit.IsDeterministicDecomposable.cutCover_le`,
  `Cslib.Circuits.Circuit.IsDeterministicDecomposable.hcComponentSize_le`: d-Ds.
* `Cslib.BranchingPrograms.NBP.cutCover_le`, `Cslib.BranchingPrograms.NBP.hcComponentSize_le`:
  read-once parity branching programs.

## References

* [Anonymous, *A Stretched-Exponential Lower Bound for Syntactically Multilinear Circuits*,
  Section 4][Anonymous2026MultilinearCircuits]
* [M. Monet and D. Olteanu, *Towards Deterministic Decomposable Circuits for Safe
  Queries*][MonetOlteanu2018]
* [B. L. Volk, *A Lower Bound for Read-Once Parity Branching Programs*][Volk2026]
-/

public section

namespace Cslib.Circuits

open MvPolynomial BitString

universe u

variable {d : ℕ}

/-! ### The inputs -/

/-- The number of inputs of the cycle-and-minor function on `d × d` matrices: the entries of the
matrix, then the `d` coordinates of the vector, then the bit `b`. -/
abbrev cmInputs (d : ℕ) : ℕ := d * d + d + 1

/-- The input carrying the entry `(i, j)` of the matrix. -/
def yIdx (v : Fin d × Fin d) : Fin (cmInputs d) :=
  Fin.castSucc (Fin.castAdd d (finProdFinEquiv v))

/-- The input carrying the coordinate `i` of the vector. -/
def xIdx (i : Fin d) : Fin (cmInputs d) :=
  Fin.castSucc (Fin.natAdd (d * d) i)

/-- The input carrying the bit `b`. -/
def bIdx : Fin (cmInputs d) :=
  Fin.last _

/-- The point with bit `b`, vector `x` and matrix `Y`. -/
@[expose]
def cmPoint {α : Type*} (b : α) (x : Fin d → α) (Y : Fin d × Fin d → α) : Fin (cmInputs d) → α :=
  Fin.lastCases b (Fin.addCases (fun v => Y (finProdFinEquiv.symm v)) x)

@[simp] theorem cmPoint_bIdx {α : Type*} (b : α) (x : Fin d → α) (Y : Fin d × Fin d → α) :
    cmPoint b x Y bIdx = b := by
  rw [cmPoint, bIdx, Fin.lastCases_last]

@[simp] theorem cmPoint_xIdx {α : Type*} (b : α) (x : Fin d → α) (Y : Fin d × Fin d → α)
    (i : Fin d) : cmPoint b x Y (xIdx i) = x i := by
  rw [cmPoint, xIdx, Fin.lastCases_castSucc, Fin.addCases_right]

@[simp] theorem cmPoint_yIdx {α : Type*} (b : α) (x : Fin d → α) (Y : Fin d × Fin d → α)
    (v : Fin d × Fin d) : cmPoint b x Y (yIdx v) = Y v := by
  rw [cmPoint, yIdx, Fin.lastCases_castSucc, Fin.addCases_left, Equiv.symm_apply_apply]

/-- Applying a function to a point applies it to each part. -/
private theorem comp_cmPoint {α β : Type*} (f : α → β) (b : α) (x : Fin d → α)
    (Y : Fin d × Fin d → α) :
    f ∘ cmPoint b x Y = cmPoint (f b) (f ∘ x) (f ∘ Y) := by
  funext i
  induction i using Fin.lastCases with
  | last => rw [Function.comp_apply, cmPoint, cmPoint, Fin.lastCases_last, Fin.lastCases_last]
  | cast i =>
    induction i using Fin.addCases with
    | left v =>
      rw [Function.comp_apply, cmPoint, cmPoint, Fin.lastCases_castSucc, Fin.lastCases_castSucc,
        Fin.addCases_left, Fin.addCases_left, Function.comp_apply]
    | right i =>
      rw [Function.comp_apply, cmPoint, cmPoint, Fin.lastCases_castSucc, Fin.lastCases_castSucc,
        Fin.addCases_right, Fin.addCases_right, Function.comp_apply]

/-- The *cycle-and-minor function* on `d * d + d + 1` bits. -/
noncomputable def cycleMinorFn (d : ℕ) (z : Fin (cmInputs d) → Bool) : Bool :=
  cycleMinor (z bIdx) (fun i => z (xIdx i)) (fun v => z (yIdx v))

@[simp] theorem cycleMinorFn_cmPoint (b : Bool) (x : Fin d → Bool) (Y : Fin d × Fin d → Bool) :
    cycleMinorFn d (cmPoint b x Y) = cycleMinor b x Y := by
  simp only [cycleMinorFn, cmPoint_bIdx, cmPoint_xIdx, cmPoint_yIdx]

/-! ### The measures -/

variable (K : Type*) [Field K]

/-- The table of the minor branch at the `d / 2 × d` matrix `C`: the generic minor at the matrix
whose first `d / 2` rows are `C` and whose other rows are zero. It is the minor of `C` on the
columns where `x` is one, or `0` unless there are `d / 2` of them
(`Cslib.Circuits.minorTable_eq`). -/
noncomputable def minorTable (C : Matrix (Fin (d / 2)) (Fin d) K) (x : Fin d → Bool) : K :=
  eval (padRows C) (minorPoly K x)

/-- The minor table is the minor of `C` on the columns where `x` is one, or `0` unless there are
`d / 2` of them. -/
theorem minorTable_eq (C : Matrix (Fin (d / 2)) (Fin d) K) (x : Fin d → Bool) :
    minorTable K C x = if h : (selected x).card = d / 2 then
      (C.submatrix id ((selected x).orderEmbOfFin h)).det else 0 :=
  eval_padRows_minorPoly C x

/-- One list of `L` sets of between `a` and `b` of the `d` coordinates writes every minor table as a
sum of `L` products of a table of the coordinates in a set and a table of the others. -/
def CutRepresentable (d a b L : ℕ) : Prop :=
  ∃ cut : Fin L → Finset (Fin d), (∀ j, a ≤ (cut j).card ∧ (cut j).card ≤ b) ∧
    ∀ C : Matrix (Fin (d / 2)) (Fin d) K, ∃ A B : Fin L → (Fin d → Bool) → K,
      (∀ j, DependsOn (A j) (cut j)) ∧ (∀ j, DependsOn (B j) (↑(cut j))ᶜ) ∧
      ∀ x, minorTable K C x = ∑ j, A j x * B j x

/-- The *cut cover number*: the least number of products across sets of between `a` and `b` of the
coordinates writing every minor table as a sum (`0` if there is none). -/
noncomputable def cutCover (d a b : ℕ) : ℕ :=
  sInf {L | CutRepresentable K d a b L}

/-- The *component size of `HC_d`*: the least size of an arithmetic circuit whose homogeneous
component of degree `d` is the Hamiltonian cycle polynomial (`0` if there is none). -/
noncomputable def hcComponentSize (d : ℕ) : ℕ :=
  sInf {s | ∃ c : Circuit (arithSignature K) (d * d) 1, c.size = s ∧
    homogeneousComponent d (c.eval (arithInterpretationWith K C) X 0) =
      (Arithmetic.hcFamily K).poly d}

/-! ### Evaluation helpers -/

variable {K}

/-- At the Boolean points, a polynomial depends only on its variables. -/
private theorem dependsOn_eval_bitPoint {τ : Type*} {p : MvPolynomial τ K} {U : Set τ}
    (h : ↑p.vars ⊆ U) : DependsOn (fun x : τ → Bool => eval (bitPoint x) p) U := by
  intro x y hxy
  exact eval₂Hom_congr' rfl (fun i hi _ => by simp [bitPoint, hxy i (h hi)]) rfl

/-! ### The variables of the inputs -/

/-- Every input is the bit, a coordinate of the vector, or an entry of the matrix. -/
private theorem cm_cases (i : Fin (cmInputs d)) :
    i = bIdx ∨ (∃ t, i = xIdx t) ∨ ∃ v, i = yIdx v := by
  induction i using Fin.lastCases with
  | last => exact Or.inl rfl
  | cast i =>
    induction i using Fin.addCases with
    | left w =>
      exact Or.inr (Or.inr ⟨finProdFinEquiv.symm w, by rw [yIdx, Equiv.apply_symm_apply]⟩)
    | right t => exact Or.inr (Or.inl ⟨t, rfl⟩)

/-- An input is the coordinate `t` of the vector when it carries the variable `t`. -/
private theorem eq_xIdx_of_mem {i : Fin (cmInputs d)} {t : Fin d}
    (h : t ∈ cmPoint (∅ : Finset (Fin d)) (fun i => {i}) (fun _ => ∅) i) : i = xIdx t := by
  rcases cm_cases i with rfl | ⟨s, rfl⟩ | ⟨v, rfl⟩ <;>
    simp only [cmPoint_bIdx, cmPoint_xIdx, cmPoint_yIdx, Finset.notMem_empty,
      Finset.mem_singleton] at h
  rw [h]

/-- An input is the entry `t` of the matrix when it carries the variable `t`. -/
private theorem eq_yIdx_of_mem {i : Fin (cmInputs d)} {t : Fin d × Fin d}
    (h : t ∈ cmPoint (∅ : Finset (Fin d × Fin d)) (fun _ => ∅) (fun v => {v}) i) :
    i = yIdx t := by
  rcases cm_cases i with rfl | ⟨s, rfl⟩ | ⟨v, rfl⟩ <;>
    simp only [cmPoint_bIdx, cmPoint_xIdx, cmPoint_yIdx, Finset.notMem_empty,
      Finset.mem_singleton] at h
  rw [h]

/-! ### The minor branch -/

variable [CharP K 2]

/-- A syntactically multilinear circuit over a field of characteristic two computing the multilinear
representative of the cycle-and-minor function computes the minor table at the point with bit `1`,
Boolean vector `x`, and matrix the padding of `M`. -/
private theorem eval_cmPoint_padRows (A : Circuit (arithSignature K) (cmInputs d) 1)
    (hA : A.IsSyntacticallyMultilinear) (hf : A.ComputesMultilinear (cycleMinorFn d))
    (M : Matrix (Fin (d / 2)) (Fin d) K) (x : Fin d → Bool) :
    A.eval (arithInterpretationWith K (algebraMap K K)) (cmPoint 1 (bitPoint x) (padRows M)) 0 =
      minorTable K M x := by
  classical
  have hval : ∀ z, A.eval (arithInterpretationWith K (algebraMap K K)) (bitPoint z) 0 =
      bitVal K (cycleMinorFn d z) := hf.eval_bitPoint
  set ρ : Fin (cmInputs d) → MvPolynomial (Fin d × Fin d) K :=
    cmPoint 1 (fun i => C (bitVal K (x i))) X with hρ
  set Q := A.eval (arithInterpretationWith K (C ∘ algebraMap K K)) ρ 0
  have hQ : Q ∈ restrictDegree (Fin d × Fin d) K 1 := by
    refine A.program.trace_mem_restrictDegree hA (algebraMap K K) ρ
      (cmPoint ∅ (fun _ => ∅) fun v => {v}) (fun i j hij => ?_) (fun i => ?_) (fun i => ?_) _
    · change Disjoint _ _
      rw [Finset.disjoint_left]
      intro t hi hj
      exact hij ((eq_yIdx_of_mem hi).trans (eq_yIdx_of_mem hj).symm)
    · rcases cm_cases i with rfl | ⟨t, rfl⟩ | ⟨v, rfl⟩
      · simp [hρ]
      · simp [hρ]
      · simp [hρ]
    · rcases cm_cases i with rfl | ⟨t, rfl⟩ | ⟨v, rfl⟩
      · rw [hρ, cmPoint_bIdx, ← C_1]
        exact C_mem_restrictDegree 1 1
      · rw [hρ, cmPoint_xIdx]
        exact C_mem_restrictDegree 1 _
      · rw [hρ, cmPoint_yIdx]
        exact X_mem_restrictDegree le_rfl _
  have hpt (z : Fin d × Fin d → K) : (fun i => eval z (ρ i)) = cmPoint 1 (bitPoint x) z := by
    funext i
    rcases cm_cases i with rfl | ⟨t, rfl⟩ | ⟨v, rfl⟩ <;> simp [hρ, bitPoint]
  have hQeq : Q = minorPoly K x := by
    refine eq_of_mem_restrictDegree_of_forall_eval_bitPoint hQ (minorPoly_mem_restrictDegree x)
      fun Y => ?_
    rw [Circuit.eval_eval, hpt, eval_bitPoint_minorPoly, ← cycleMinor_true x Y,
      ← cycleMinorFn_cmPoint, ← hval]
    congr 1
    funext i
    rcases cm_cases i with rfl | ⟨t, rfl⟩ | ⟨v, rfl⟩ <;> simp [bitPoint, bitVal]
  rw [← hpt, ← Circuit.eval_eval]
  change eval (padRows M) Q = _
  rw [hQeq]
  rfl

/-- **Transfer to the cut cover number.** A syntactically multilinear arithmetic circuit with `s`
gates over a field of characteristic two computing the multilinear representative of the
cycle-and-minor function writes every minor table as a sum of at most `2 s + 1` products across one
list of sets of between `a` and `b` coordinates, for `a ≤ b`, `2 a ≤ b + 2`, `a ≤ d` and `1 ≤ b`. -/
theorem exists_cutRepresentable_of_syntacticallyMultilinear
    (A : Circuit (arithSignature K) (cmInputs d) 1) (hA : A.IsSyntacticallyMultilinear)
    (hf : A.ComputesMultilinear (cycleMinorFn d)) {a b : ℕ} (hab : a ≤ b) (ha : a ≤ (b + 2) / 2)
    (had : a ≤ d) (hb : 1 ≤ b) : ∃ L ≤ 2 * A.size + 1, CutRepresentable K d a b L := by
  classical
  have hval : ∀ z, A.eval (arithInterpretationWith K (algebraMap K K)) (bitPoint z) 0 =
      bitVal K (cycleMinorFn d z) := hf.eval_bitPoint
  set V : Fin (cmInputs d) → Finset (Fin d) := cmPoint ∅ (fun i => {i}) fun _ => ∅ with hV
  obtain ⟨L, cut, hL, hcut, hrep⟩ := A.exists_balanced_cuts (K := K) hA V
    (fun i j hij => by
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro t hi hj
      exact hij ((eq_xIdx_of_mem hi).trans (eq_xIdx_of_mem hj).symm))
    (fun i => by rcases cm_cases i with rfl | ⟨t, rfl⟩ | ⟨v, rfl⟩ <;> simp [hV, hb])
    hab ha (by simpa using had)
  refine ⟨L, hL, cut, hcut, fun M => ?_⟩
  set ρ : Fin (cmInputs d) → MvPolynomial (Fin d) K :=
    cmPoint 1 X fun v => C (padRows M v) with hρ
  obtain ⟨P, Q, hP, hQ, hsum⟩ := hrep (algebraMap K K) ρ
    (fun i => by rcases cm_cases i with rfl | ⟨t, rfl⟩ | ⟨v, rfl⟩ <;> simp [hρ, hV])
    (fun i => by
      rcases cm_cases i with rfl | ⟨t, rfl⟩ | ⟨v, rfl⟩
      · rw [hρ, cmPoint_bIdx, ← C_1]
        exact C_mem_restrictDegree 1 1
      · rw [hρ, cmPoint_xIdx]
        exact X_mem_restrictDegree le_rfl _
      · rw [hρ, cmPoint_yIdx]
        exact C_mem_restrictDegree 1 _)
  refine ⟨fun j x => eval (bitPoint x) (P j), fun j x => eval (bitPoint x) (Q j),
    fun j => dependsOn_eval_bitPoint (by exact_mod_cast hP j),
    fun j => dependsOn_eval_bitPoint fun t ht => Finset.disjoint_left.mp (hQ j) ht, fun x => ?_⟩
  rw [← eval_cmPoint_padRows A hA hf M x]
  have hpt : (fun i => eval (bitPoint x) (ρ i)) = cmPoint 1 (bitPoint x) (padRows M) := by
    funext i
    rcases cm_cases i with rfl | ⟨t, rfl⟩ | ⟨v, rfl⟩ <;> simp [hρ, bitPoint]
  rw [← hpt, ← Circuit.eval_eval, hsum, map_sum]
  simp only [map_mul]

/-- The cut cover number is at most `2 s + 1` for a syntactically multilinear arithmetic circuit
with `s` gates computing the multilinear representative of the cycle-and-minor function. -/
theorem cutCover_le_of_syntacticallyMultilinear (A : Circuit (arithSignature K) (cmInputs d) 1)
    (hA : A.IsSyntacticallyMultilinear) (hf : A.ComputesMultilinear (cycleMinorFn d)) {a b : ℕ}
    (hab : a ≤ b) (ha : a ≤ (b + 2) / 2) (had : a ≤ d) (hb : 1 ≤ b) :
    cutCover K d a b ≤ 2 * A.size + 1 := by
  obtain ⟨L, hL, hrep⟩ :=
    exists_cutRepresentable_of_syntacticallyMultilinear A hA hf hab ha had hb
  exact (Nat.sInf_le hrep).trans hL

/-! ### The cycle branch -/

omit [CharP K 2] in
/-- **Transfer to the component size of `HC_d`.** Setting the bit and the vector of a syntactically
multilinear arithmetic circuit computing the multilinear representative of the cycle-and-minor
function to zero gives, with one more gate, a circuit whose homogeneous component of degree `d` is
the Hamiltonian cycle polynomial. -/
theorem hcComponentSize_le_of_syntacticallyMultilinear
    (A : Circuit (arithSignature K) (cmInputs d) 1) (hA : A.IsSyntacticallyMultilinear)
    (hf : A.ComputesMultilinear (cycleMinorFn d)) : hcComponentSize K d ≤ A.size + 1 := by
  classical
  have hval : ∀ z, A.eval (arithInterpretationWith K (algebraMap K K)) (bitPoint z) 0 =
      bitVal K (cycleMinorFn d z) := hf.eval_bitPoint
  set e := (finProdFinEquiv : Fin d × Fin d ≃ Fin (d * d))
  let p0 : Program (arithSignature K) (d * d) 1 :=
    (Program.empty : Program (arithSignature K) (d * d) 0).gate ⟨ArithOp.const 0, Fin.elim0⟩
  let feed : Fin (cmInputs d) → Wire (d * d) 1 :=
    cmPoint (Wire.gate 0) (fun _ => Wire.gate 0) fun v => Wire.input (e v)
  let B : Circuit (arithSignature K) (d * d) 1 :=
    ⟨p0.append feed A.program, fun _ => Program.appendedWire feed (A.outputs 0)⟩
  set ρ : Fin (cmInputs d) → MvPolynomial (Fin (d * d)) K :=
    cmPoint 0 (fun _ => 0) fun v => X (e v) with hρ
  have hB : B.eval (arithInterpretationWith K C) X 0 =
      A.eval (arithInterpretationWith K (C ∘ algebraMap K K)) ρ 0 := by
    change (p0.append feed A.program).trace _ X _ = A.program.trace _ ρ (A.outputs 0)
    rw [Program.trace_append_appendedWire]
    congr 1
    funext i
    have h0 : p0.trace (arithInterpretationWith K C) X (Wire.gate 0) = 0 := by
      change C 0 = 0
      exact C_0
    rcases cm_cases i with rfl | ⟨t, rfl⟩ | ⟨v, rfl⟩ <;> simp [feed, hρ, h0]
  set Q := A.eval (arithInterpretationWith K (C ∘ algebraMap K K)) ρ 0
  have hQ : Q ∈ restrictDegree (Fin (d * d)) K 1 := by
    refine A.program.trace_mem_restrictDegree hA (algebraMap K K) ρ
      (cmPoint ∅ (fun _ => ∅) fun v => {e v}) (fun i j hij => ?_) (fun i => ?_) (fun i => ?_) _
    · change Disjoint _ _
      rw [Finset.disjoint_left]
      intro t hi hj
      rcases cm_cases i with rfl | ⟨s, rfl⟩ | ⟨v, rfl⟩ <;>
        rcases cm_cases j with rfl | ⟨s', rfl⟩ | ⟨w, rfl⟩ <;> simp_all
    · rcases cm_cases i with rfl | ⟨t, rfl⟩ | ⟨v, rfl⟩ <;> simp [hρ]
    · rcases cm_cases i with rfl | ⟨t, rfl⟩ | ⟨v, rfl⟩
      · rw [hρ, cmPoint_bIdx]
        exact Submodule.zero_mem _
      · rw [hρ, cmPoint_xIdx]
        exact Submodule.zero_mem _
      · rw [hρ, cmPoint_yIdx]
        exact X_mem_restrictDegree le_rfl _
  have hren : rename e (cyclePoly (d := d) K) ∈ restrictDegree (Fin (d * d)) K 1 := by
    rw [cyclePoly_eq_multilinearExtension, rename_multilinearExtension]
    exact multilinearExtension_mem_restrictDegree _
  have hQeq : Q = rename e (cyclePoly K) := by
    refine eq_of_mem_restrictDegree_of_forall_eval_bitPoint hQ hren fun w => ?_
    rw [Circuit.eval_eval, eval_rename]
    have hpt : (fun i => eval (bitPoint w) (ρ i)) = bitPoint (cmPoint false (fun _ => false)
        (w ∘ e)) := by
      funext i
      rcases cm_cases i with rfl | ⟨t, rfl⟩ | ⟨v, rfl⟩ <;> simp [hρ, bitPoint, bitVal]
    rw [hpt, hval, cycleMinorFn_cmPoint, cycleMinor_false]
    have := eval_bitPoint_cyclePoly (K := K) (w ∘ e)
    rw [show (bitPoint w ∘ e : Fin d × Fin d → K) = bitPoint (w ∘ e) from rfl, this]
  refine Nat.sInf_le ⟨B, by change 1 + A.size = A.size + 1; omega, ?_⟩
  rw [hB]
  change homogeneousComponent d Q = _
  rw [hQeq, ← rename_homogeneousComponent, homogeneousComponent_cyclePoly,
    AlgHom.map_hamiltonianCycleSum]
  change _ = (Arithmetic.genericMatrix K d).hamiltonianCycleSum
  rw [Arithmetic.genericMatrix_eq_map_rename]
  rfl

/-! ### The main theorem -/

/-- **Syntactically multilinear circuits for the cycle-and-minor function.** A syntactically
multilinear arithmetic circuit with `s` gates computing the multilinear representative of the
cycle-and-minor function over a field of characteristic two writes every minor table as a sum of at
most `2 s + 1` products across one list of sets of between `a` and `b` coordinates, and gives a
circuit with at most `s + 1` gates whose homogeneous component of degree `d` is the Hamiltonian
cycle polynomial. Here `a ≤ b`, `2 a ≤ b + 2`, `a ≤ d` and `1 ≤ b`. -/
theorem measures_le_of_syntacticallyMultilinear (A : Circuit (arithSignature K) (cmInputs d) 1)
    (hA : A.IsSyntacticallyMultilinear) (hf : A.ComputesMultilinear (cycleMinorFn d)) {a b : ℕ}
    (hab : a ≤ b) (ha : a ≤ (b + 2) / 2) (had : a ≤ d) (hb : 1 ≤ b) :
    cutCover K d a b ≤ 2 * A.size + 1 ∧ hcComponentSize K d ≤ A.size + 1 :=
  ⟨cutCover_le_of_syntacticallyMultilinear A hA hf hab ha had hb,
    hcComponentSize_le_of_syntacticallyMultilinear A hA hf⟩

/-! ### Deterministic decomposable circuits -/

namespace Circuit.IsDeterministicDecomposable

variable {c : Circuit Boolean.signature (cmInputs d) 1}

omit [CharP K 2] in
/-- A d-D computing the cycle-and-minor function gives a syntactically multilinear circuit with
four gates for each of its gates computing its multilinear representative, over every field. -/
theorem exists_syntacticallyMultilinear_cycleMinor (hc : c.IsDeterministicDecomposable)
    (hf : c.Computes Boolean.interpretation (single (cycleMinorFn d))) :
    ∃ A : Circuit (arithSignature K) (cmInputs d) 1, A.IsSyntacticallyMultilinear ∧
      A.ComputesMultilinear (cycleMinorFn d) ∧ A.size ≤ 4 * c.size := by
  obtain ⟨A, hA, hAf, hs⟩ := hc.exists_syntacticallyMultilinear (R := K)
  have : (fun z => c.eval Boolean.interpretation z 0) = cycleMinorFn d :=
    funext fun z => congrFun (hf z) 0
  exact ⟨A, hA, this ▸ hAf, hs⟩

/-- **d-Ds bound the cut cover number.** A d-D with `s` gates computing the cycle-and-minor function
writes every minor table over a field of characteristic two as a sum of at most `8 s + 1` products
across sets of between `a` and `b` coordinates. -/
theorem cutCover_le (hc : c.IsDeterministicDecomposable)
    (hf : c.Computes Boolean.interpretation (single (cycleMinorFn d))) {a b : ℕ} (hab : a ≤ b)
    (ha : a ≤ (b + 2) / 2) (had : a ≤ d) (hb : 1 ≤ b) : cutCover K d a b ≤ 8 * c.size + 1 := by
  obtain ⟨A, hA, hAf, hs⟩ := hc.exists_syntacticallyMultilinear_cycleMinor (K := K) hf
  exact (cutCover_le_of_syntacticallyMultilinear A hA hAf hab ha had hb).trans (by omega)

omit [CharP K 2] in
/-- **d-Ds bound the component size of `HC_d`.** A d-D with `s` gates computing the
cycle-and-minor function gives, over every field, a circuit with at most `4 s + 1` gates whose
homogeneous component of degree `d` is the Hamiltonian cycle polynomial. -/
theorem hcComponentSize_le (hc : c.IsDeterministicDecomposable)
    (hf : c.Computes Boolean.interpretation (single (cycleMinorFn d))) :
    hcComponentSize K d ≤ 4 * c.size + 1 := by
  obtain ⟨A, hA, hAf, hs⟩ := hc.exists_syntacticallyMultilinear_cycleMinor (K := K) hf
  exact (hcComponentSize_le_of_syntacticallyMultilinear A hA hAf).trans (by omega)

end Circuit.IsDeterministicDecomposable

end Cslib.Circuits

/-! ### Read-once parity branching programs -/

namespace Cslib.BranchingPrograms.NBP

open Cslib.Circuits MvPolynomial BitString

variable {d n : ℕ} {K : Type*} [Field K] [CharP K 2] {P : NBP (Fin (cmInputs d)) Bool n}

/-- A read-once parity program with `w` wires computing the cycle-and-minor function gives, in
characteristic two, a syntactically multilinear circuit with at most `2 + 5 w` gates computing its
multilinear representative. -/
theorem exists_syntacticallyMultilinear_cycleMinor (hP : P.IsReadOnce)
    (hf : ∀ z, P.AcceptsParity z ↔ cycleMinorFn d z = true) :
    ∃ A : Circuit (arithSignature K) (cmInputs d) 1, A.IsSyntacticallyMultilinear ∧
      A.ComputesMultilinear (cycleMinorFn d) ∧ A.size ≤ 2 + 5 * P.wireCount := by
  obtain ⟨A, hA, hAf, hs⟩ := P.exists_syntacticallyMultilinear (R := K) hP
  have : (fun z => decide (P.AcceptsParity z)) = cycleMinorFn d :=
    funext fun z => by
      have := hf z
      cases h : cycleMinorFn d z <;> simp_all
  exact ⟨A, hA, this ▸ hAf, hs⟩

/-- **Read-once parity programs bound the cut cover number.** A syntactic read-once parity branching
program with `w` wires computing the cycle-and-minor function writes every minor table over a field
of characteristic two as a sum of at most `2 (2 + 5 w) + 1` products across sets of between `a` and
`b` coordinates. -/
theorem cutCover_le (hP : P.IsReadOnce) (hf : ∀ z, P.AcceptsParity z ↔ cycleMinorFn d z = true)
    {a b : ℕ} (hab : a ≤ b) (ha : a ≤ (b + 2) / 2) (had : a ≤ d) (hb : 1 ≤ b) :
    cutCover K d a b ≤ 2 * (2 + 5 * P.wireCount) + 1 := by
  obtain ⟨A, hA, hAf, hs⟩ := exists_syntacticallyMultilinear_cycleMinor (K := K) hP hf
  exact (cutCover_le_of_syntacticallyMultilinear A hA hAf hab ha had hb).trans (by omega)

/-- **Read-once parity programs bound the component size of `HC_d`.** A syntactic read-once parity
branching program with `w` wires computing the cycle-and-minor function gives, over a field of
characteristic two, a circuit with at most `2 + 5 w + 1` gates whose homogeneous component of degree
`d` is the Hamiltonian cycle polynomial. -/
theorem hcComponentSize_le (hP : P.IsReadOnce)
    (hf : ∀ z, P.AcceptsParity z ↔ cycleMinorFn d z = true) :
    hcComponentSize K d ≤ 2 + 5 * P.wireCount + 1 := by
  obtain ⟨A, hA, hAf, hs⟩ := exists_syntacticallyMultilinear_cycleMinor (K := K) hP hf
  exact (hcComponentSize_le_of_syntacticallyMultilinear A hA hAf).trans (by omega)

end Cslib.BranchingPrograms.NBP
