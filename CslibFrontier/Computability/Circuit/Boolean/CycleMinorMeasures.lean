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
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Logic.Function.DependsOn
import CslibFrontier.Foundations.BooleanAnalysis.BooleanQuotient
import CslibFrontier.Foundations.Data.MvPolynomial.DisjointVars

/-!
# Two measures for the cycle-and-minor function

This module defines two algebraic measures and bounds both of them above by the size of a
syntactically multilinear arithmetic circuit computing the multilinear representative
(`Cslib.Circuits.Circuit.ComputesMultilinear`) of the cycle-and-minor function
`Cslib.Circuits.cycleMinorFn`. Syntactically multilinear circuits simulate deterministic
decomposable circuits and read-once parity branching programs with linear overhead, so the same
bounds hold for these models. A lower bound on either measure is therefore a size lower bound for
all three models.

* `Cslib.Circuits.cutCover K d a b`: the least number of products across sets of between `a` and
  `b` of the `d` coordinates that, from one list of sets for all `C`, write every table
  `T_C x = det C_x` as a sum (`Cslib.Circuits.minorTable`). Here `C` ranges over the
  `d / 2 × d` matrices over `K`, and `C_x` is the minor of `C` on the columns where `x` is one, with
  `T_C x = 0` unless there are `d / 2` of them.
* `Cslib.Circuits.hcComponentSize K d`: the least size of an arithmetic circuit over `K` whose
  homogeneous component of degree `d` is the Hamiltonian cycle polynomial `HC_d`.

Both take values in `ℕ∞`, with `⊤` when no list of cuts or no circuit exists, and
`Cslib.Circuits.le_cutCover_iff` and `Cslib.Circuits.le_hcComponentSize_iff` turn lower bounds on
the measures into statements about every list of cuts or every circuit.

**The main theorem** (`Cslib.Circuits.measures_le_of_syntacticallyMultilinear`): a syntactically
multilinear circuit over a commutative ring `F` with `s` gates computing the multilinear
representative of the function gives `cutCover K d a b ≤ 2 s + 1` for every `F`-algebra `K` of
characteristic two, and `hcComponentSize F d ≤ s + 1`.
On the minor branch, the circuit with the first `d / 2` rows of `Y` set to `C` and the others to
zero computes `T_C` on the coordinates of `x`, and the cut lemma
(`Cslib.Circuits.Circuit.exists_balanced_cuts`) writes it as such a sum, with the cuts chosen before
`C`. Since `C` ranges over matrices over `K`, the circuit may have constants in a smaller ring such
as `F₂`. On the cycle branch, the circuit with `b` and `x` set to zero computes the multilinear
representative of the cycle test, whose component of degree `d` is `HC_d`; this part holds in every
characteristic.

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

* `Cslib.Circuits.CycleMinor.inputs`, `Cslib.Circuits.CycleMinor.yIdx`,
  `Cslib.Circuits.CycleMinor.xIdx`, `Cslib.Circuits.CycleMinor.bIdx`,
  `Cslib.Circuits.CycleMinor.point`: the `d * d + d + 1` inputs, which carry the matrix, the vector
  and the bit, and the point with given parts.
* `Cslib.Circuits.cycleMinorFn`: the cycle-and-minor function on `d * d + d + 1` bits.
* `Cslib.Circuits.minorTable`, `Cslib.Circuits.CutRepresentable`, `Cslib.Circuits.cutCover`: the
  minor tables and the cut cover number.
* `Cslib.Circuits.hcComponentSize`: the component size of `HC_d`.

## Main results

* `Cslib.Circuits.minorTable_eq`, `Cslib.Circuits.minorTable_of_card_ne`,
  `Cslib.Circuits.minorTable_eq_det`: the values of the minor tables.
* `Cslib.Circuits.le_cutCover_iff`, `Cslib.Circuits.cutCover_le_iff`,
  `Cslib.Circuits.le_hcComponentSize_iff`, `Cslib.Circuits.hcComponentSize_le_iff`: the two
  measures as least values.
* `Cslib.Circuits.measures_le_of_syntacticallyMultilinear`: the main theorem, with its two halves
  `Cslib.Circuits.cutCover_le_of_syntacticallyMultilinear` (through
  `Cslib.Circuits.exists_cutRepresentable_of_syntacticallyMultilinear`) and
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

open MvPolynomial BitString CycleMinor

variable {d : ℕ}

/-! ### The inputs -/

namespace CycleMinor

/-- The number of inputs of the cycle-and-minor function on `d × d` matrices: the entries of the
matrix, then the `d` coordinates of the vector, then the bit `b`. -/
abbrev inputs (d : ℕ) : ℕ := d * d + d + 1

/-- The input carrying the entry `(i, j)` of the matrix. -/
@[expose]
def yIdx (v : Fin d × Fin d) : Fin (inputs d) :=
  Fin.castSucc (Fin.castAdd d (finProdFinEquiv v))

/-- The input carrying the coordinate `i` of the vector. -/
@[expose]
def xIdx (i : Fin d) : Fin (inputs d) :=
  Fin.castSucc (Fin.natAdd (d * d) i)

/-- The input carrying the bit `b`. -/
@[expose]
def bIdx : Fin (inputs d) :=
  Fin.last _

/-- The point with bit `b`, vector `x` and matrix `Y`. -/
@[expose]
def point {α : Type*} (b : α) (x : Fin d → α) (Y : Fin d × Fin d → α) : Fin (inputs d) → α :=
  Fin.lastCases b (Fin.addCases (fun v => Y (finProdFinEquiv.symm v)) x)

@[simp] theorem point_bIdx {α : Type*} (b : α) (x : Fin d → α) (Y : Fin d × Fin d → α) :
    point b x Y bIdx = b := by
  rw [point, bIdx, Fin.lastCases_last]

@[simp] theorem point_xIdx {α : Type*} (b : α) (x : Fin d → α) (Y : Fin d × Fin d → α)
    (i : Fin d) : point b x Y (xIdx i) = x i := by
  rw [point, xIdx, Fin.lastCases_castSucc, Fin.addCases_right]

@[simp] theorem point_yIdx {α : Type*} (b : α) (x : Fin d → α) (Y : Fin d × Fin d → α)
    (v : Fin d × Fin d) : point b x Y (yIdx v) = Y v := by
  rw [point, yIdx, Fin.lastCases_castSucc, Fin.addCases_left, Equiv.symm_apply_apply]

/-- Every input is the bit, a coordinate of the vector, or an entry of the matrix. -/
private theorem cases_input (i : Fin (inputs d)) :
    i = bIdx ∨ (∃ t, i = xIdx t) ∨ ∃ v, i = yIdx v := by
  induction i using Fin.lastCases with
  | last => exact Or.inl rfl
  | cast i =>
    induction i using Fin.addCases with
    | left w =>
      exact Or.inr (Or.inr ⟨finProdFinEquiv.symm w, by rw [yIdx, Equiv.apply_symm_apply]⟩)
    | right t => exact Or.inr (Or.inl ⟨t, rfl⟩)

/-- Every function on the inputs is the point with its values at the bit, the vector and the
matrix. -/
theorem point_eta {α : Type*} (z : Fin (inputs d) → α) :
    point (z bIdx) (fun i => z (xIdx i)) (fun v => z (yIdx v)) = z := by
  funext i
  rcases cases_input i with rfl | ⟨t, rfl⟩ | ⟨v, rfl⟩ <;> simp

end CycleMinor

/-- The *cycle-and-minor function* on `d * d + d + 1` bits. -/
@[expose]
noncomputable def cycleMinorFn (d : ℕ) (z : Fin (CycleMinor.inputs d) → Bool) : Bool :=
  cycleMinor (z bIdx) (fun i => z (xIdx i)) (fun v => z (yIdx v))

@[simp] theorem cycleMinorFn_point (b : Bool) (x : Fin d → Bool) (Y : Fin d × Fin d → Bool) :
    cycleMinorFn d (point b x Y) = cycleMinor b x Y := by
  simp only [cycleMinorFn, point_bIdx, point_xIdx, point_yIdx]

/-! ### The minor tables and the cut cover number -/

variable (K : Type*) [CommRing K]

/-- The table of the minor branch at the `d / 2 × d` matrix `C`: the generic minor at the matrix
whose first `d / 2` rows are `C` and whose other rows are zero. It is the minor of `C` on the
columns where `x` is one, or `0` unless there are `d / 2` of them
(`Cslib.Circuits.minorTable_eq`). -/
noncomputable def minorTable (C : Matrix (Fin (d / 2)) (Fin d) K) (x : Fin d → Bool) : K :=
  eval (padRows C) (minorPoly K x)

variable {K}

/-- The minor table is the minor of `C` on the columns where `x` is one, or `0` unless there are
`d / 2` of them. -/
theorem minorTable_eq (C : Matrix (Fin (d / 2)) (Fin d) K) (x : Fin d → Bool) :
    minorTable K C x = if h : (selected x).card = d / 2 then
      (C.submatrix id ((selected x).orderEmbOfFin h)).det else 0 :=
  eval_padRows_minorPoly C x

/-- The minor table is zero unless `x` selects `d / 2` columns. -/
@[simp] theorem minorTable_of_card_ne (C : Matrix (Fin (d / 2)) (Fin d) K) {x : Fin d → Bool}
    (h : (selected x).card ≠ d / 2) : minorTable K C x = 0 := by
  simp [minorTable_eq, h]

/-- The minor table through any increasing enumeration `f` of the `d / 2` columns that `x`
selects. -/
theorem minorTable_eq_det (C : Matrix (Fin (d / 2)) (Fin d) K) {x : Fin d → Bool}
    (f : Fin (d / 2) ↪o Fin d) (hf : ∀ c, x (f c) = true) (h : (selected x).card = d / 2) :
    minorTable K C x = (C.submatrix id f).det := by
  simp only [minorTable_eq, h, ↓reduceDIte]
  rw [← Finset.orderEmbOfFin_unique' h fun c => mem_selected.mpr (hf c)]

variable (K)

/-- One list of `L` sets of between `a` and `b` of the `d` coordinates writes every minor table as a
sum of `L` products of a table of the coordinates in a set and a table of the others. -/
@[expose]
def CutRepresentable (d a b L : ℕ) : Prop :=
  ∃ cut : Fin L → Finset (Fin d), (∀ j, a ≤ (cut j).card ∧ (cut j).card ≤ b) ∧
    ∀ C : Matrix (Fin (d / 2)) (Fin d) K, ∃ A B : Fin L → (Fin d → Bool) → K,
      (∀ j, DependsOn (A j) (cut j)) ∧ (∀ j, DependsOn (B j) (↑(cut j))ᶜ) ∧
      ∀ x, minorTable K C x = ∑ j, A j x * B j x

/-- The *cut cover number*: the least number of products across sets of between `a` and `b` of the
coordinates writing every minor table as a sum, or `⊤` if there is none. -/
noncomputable def cutCover (d a b : ℕ) : ℕ∞ :=
  ⨅ (L : ℕ) (_ : CutRepresentable K d a b L), (L : ℕ∞)

variable {K}

/-- Every list of `L` cuts writing every minor table as a sum bounds the cut cover number by
`L`. -/
theorem cutCover_le {a b L : ℕ} (h : CutRepresentable K d a b L) : cutCover K d a b ≤ L :=
  iInf₂_le L h

/-- `k ≤ cutCover K d a b` holds exactly when every list of cuts writing every minor table as a sum
has at least `k` cuts. -/
theorem le_cutCover_iff {a b : ℕ} {k : ℕ∞} :
    k ≤ cutCover K d a b ↔ ∀ L, CutRepresentable K d a b L → k ≤ L :=
  le_iInf₂_iff

/-- The cut cover number is at most `L` exactly when some list of at most `L` cuts writes every
minor table as a sum. -/
theorem cutCover_le_iff {a b L : ℕ} :
    cutCover K d a b ≤ L ↔ ∃ L' ≤ L, CutRepresentable K d a b L' := by
  refine ⟨fun h => ?_, fun ⟨L', hL', h⟩ => (cutCover_le h).trans (by exact_mod_cast hL')⟩
  by_contra hne
  simp only [not_exists, not_and] at hne
  refine absurd h (not_le.mpr (lt_of_lt_of_le (ENat.natCast_lt_natCast.mpr (Nat.lt_succ_self L))
    (le_cutCover_iff.mpr fun L' hL' => ?_)))
  have : L + 1 ≤ L' := by
    by_contra h'
    exact hne L' (by omega) hL'
  exact_mod_cast this

/-! ### The component size of `HC_d` -/

variable (K)

/-- The *component size of `HC_d`*: the least size of an arithmetic circuit whose homogeneous
component of degree `d` is the Hamiltonian cycle polynomial, or `⊤` if there is none. -/
noncomputable def hcComponentSize (d : ℕ) : ℕ∞ :=
  ⨅ (c : Circuit (arithSignature K) (d * d) 1)
    (_ : homogeneousComponent d (c.eval (arithInterpretationWith K C) X 0) =
      (Arithmetic.hcFamily K).poly d), (c.size : ℕ∞)

variable {K}

/-- Every circuit whose homogeneous component of degree `d` is the Hamiltonian cycle polynomial
bounds the component size of `HC_d` by its size. -/
theorem hcComponentSize_le (c : Circuit (arithSignature K) (d * d) 1)
    (h : homogeneousComponent d (c.eval (arithInterpretationWith K C) X 0) =
      (Arithmetic.hcFamily K).poly d) : hcComponentSize K d ≤ c.size :=
  iInf₂_le c h

/-- `k ≤ hcComponentSize K d` holds exactly when every circuit whose homogeneous component of degree
`d` is the Hamiltonian cycle polynomial has at least `k` gates. -/
theorem le_hcComponentSize_iff {k : ℕ∞} :
    k ≤ hcComponentSize K d ↔ ∀ c : Circuit (arithSignature K) (d * d) 1,
      homogeneousComponent d (c.eval (arithInterpretationWith K C) X 0) =
        (Arithmetic.hcFamily K).poly d → k ≤ c.size :=
  le_iInf₂_iff

/-- The component size of `HC_d` is at most `s` exactly when some circuit with at most `s` gates
has the Hamiltonian cycle polynomial as its homogeneous component of degree `d`. -/
theorem hcComponentSize_le_iff {s : ℕ} :
    hcComponentSize K d ≤ s ↔ ∃ c : Circuit (arithSignature K) (d * d) 1, c.size ≤ s ∧
      homogeneousComponent d (c.eval (arithInterpretationWith K C) X 0) =
        (Arithmetic.hcFamily K).poly d := by
  refine ⟨fun h => ?_, fun ⟨c, hc, h⟩ => (hcComponentSize_le c h).trans (by exact_mod_cast hc)⟩
  by_contra hne
  simp only [not_exists, not_and] at hne
  refine absurd h (not_le.mpr (lt_of_lt_of_le (ENat.natCast_lt_natCast.mpr (Nat.lt_succ_self s))
    (le_hcComponentSize_iff.mpr fun c hc => ?_)))
  have : s + 1 ≤ c.size := by
    by_contra h'
    exact hne c (by omega) hc
  exact_mod_cast this

/-! ### Evaluation helpers -/

/-- At the Boolean points, a polynomial depends only on its variables. -/
private theorem dependsOn_eval_bitPoint {τ : Type*} {p : MvPolynomial τ K} {U : Set τ}
    (h : ↑p.vars ⊆ U) : DependsOn (fun x : τ → Bool => eval (bitPoint x) p) U := by
  intro x y hxy
  exact eval₂Hom_congr' rfl (fun i hi _ => by simp [bitPoint, hxy i (h hi)]) rfl

/-- An input is the coordinate `t` of the vector when it carries the variable `t`. -/
private theorem eq_xIdx_of_mem {i : Fin (CycleMinor.inputs d)} {t : Fin d}
    (h : t ∈ point (∅ : Finset (Fin d)) (fun i => {i}) (fun _ => ∅) i) : i = xIdx t := by
  rcases cases_input i with rfl | ⟨s, rfl⟩ | ⟨v, rfl⟩ <;>
    simp only [point_bIdx, point_xIdx, point_yIdx, Finset.notMem_empty,
      Finset.mem_singleton] at h
  rw [h]

/-- An input is the entry `t` of the matrix when it carries the variable `t`. -/
private theorem eq_yIdx_of_mem {i : Fin (CycleMinor.inputs d)} {t : Fin d × Fin d}
    (h : t ∈ point (∅ : Finset (Fin d × Fin d)) (fun _ => ∅) (fun v => {v}) i) :
    i = yIdx t := by
  rcases cases_input i with rfl | ⟨s, rfl⟩ | ⟨v, rfl⟩ <;>
    simp only [point_bIdx, point_xIdx, point_yIdx, Finset.notMem_empty,
      Finset.mem_singleton] at h
  rw [h]

variable {F : Type*} [CommRing F]

/-- A circuit over `F` computing the multilinear representative of the cycle-and-minor function
computes the function on the Boolean points of every `F`-algebra. -/
private theorem eval_algebraMap_bitPoint [Algebra F K]
    {A : Circuit (arithSignature F) (CycleMinor.inputs d) 1}
    (hf : A.ComputesMultilinear (cycleMinorFn d)) (z : Fin (CycleMinor.inputs d) → Bool) :
    A.eval (arithInterpretationWith F (algebraMap F K)) (bitPoint z) 0 =
      bitVal K (cycleMinorFn d z) := by
  let h : Homomorphism (arithInterpretation F) (arithInterpretationWith F (algebraMap F K)) :=
    ⟨algebraMap F K, fun op args => by
      cases op <;> simp [arithInterpretation, arithInterpretationWith]⟩
  have hmap := congrFun (A.map_eval h (bitPoint z)) 0
  have hpt : (h.map ∘ bitPoint z : Fin (CycleMinor.inputs d) → K) = bitPoint z := by
    funext i
    cases z i <;> simp [h, bitPoint, bitVal]
  rw [hpt] at hmap
  rw [← hmap, Function.comp_apply]
  change algebraMap F K (A.eval (arithInterpretation F) (bitPoint z) 0) = _
  rw [hf.eval_bitPoint]
  cases cycleMinorFn d z <;> simp [bitVal]

/-! ### The minor branch -/

variable [Algebra F K] [CharP K 2]

/-- A syntactically multilinear circuit over `F` computing the multilinear representative of the
cycle-and-minor function computes, over an `F`-algebra of characteristic two, the minor table at
the point with bit `1`, Boolean vector `x`, and matrix the padding of `M`. -/
private theorem eval_point_padRows (A : Circuit (arithSignature F) (CycleMinor.inputs d) 1)
    (hA : A.IsSyntacticallyMultilinear) (hf : A.ComputesMultilinear (cycleMinorFn d))
    (M : Matrix (Fin (d / 2)) (Fin d) K) (x : Fin d → Bool) :
    A.eval (arithInterpretationWith F (algebraMap F K)) (point 1 (bitPoint x) (padRows M)) 0 =
      minorTable K M x := by
  classical
  set ρ : Fin (CycleMinor.inputs d) → MvPolynomial (Fin d × Fin d) K :=
    point 1 (fun i => C (bitVal K (x i))) X with hρ
  set Q := A.eval (arithInterpretationWith F (C ∘ algebraMap F K)) ρ 0
  have hQ : Q ∈ restrictDegree (Fin d × Fin d) K 1 := by
    refine A.program.trace_mem_restrictDegree hA (algebraMap F K) ρ
      (point ∅ (fun _ => ∅) fun v => {v}) (fun i j hij => ?_) (fun i => ?_) (fun i => ?_) _
    · change Disjoint _ _
      rw [Finset.disjoint_left]
      intro t hi hj
      exact hij ((eq_yIdx_of_mem hi).trans (eq_yIdx_of_mem hj).symm)
    · rcases cases_input i with rfl | ⟨t, rfl⟩ | ⟨v, rfl⟩
      · simp [hρ]
      · simp [hρ]
      · rw [hρ, point_yIdx, point_yIdx]
        exact vars_X_subset v
    · rcases cases_input i with rfl | ⟨t, rfl⟩ | ⟨v, rfl⟩
      · rw [hρ, point_bIdx, ← C_1]
        exact C_mem_restrictDegree 1 1
      · rw [hρ, point_xIdx]
        exact C_mem_restrictDegree 1 _
      · rw [hρ, point_yIdx]
        exact X_mem_restrictDegree le_rfl _
  have hpt (z : Fin d × Fin d → K) : (fun i => eval z (ρ i)) = point 1 (bitPoint x) z := by
    funext i
    rcases cases_input i with rfl | ⟨t, rfl⟩ | ⟨v, rfl⟩ <;> simp [hρ, bitPoint]
  have hQeq : Q = minorPoly K x := by
    refine eq_of_mem_restrictDegree_of_forall_eval_bitPoint hQ (minorPoly_mem_restrictDegree x)
      fun Y => ?_
    rw [Circuit.eval_eval, hpt, eval_bitPoint_minorPoly, ← cycleMinor_true x Y,
      ← cycleMinorFn_point, ← eval_algebraMap_bitPoint hf]
    congr 1
    funext i
    rcases cases_input i with rfl | ⟨t, rfl⟩ | ⟨v, rfl⟩ <;> simp [bitPoint, bitVal]
  rw [← hpt, ← Circuit.eval_eval]
  change eval (padRows M) Q = _
  rw [hQeq]
  rfl

/-- **Transfer to the cut cover number.** A syntactically multilinear arithmetic circuit over `F`
with `s` gates computing the multilinear representative of the cycle-and-minor function writes
every minor table over an `F`-algebra `K` of characteristic two as a sum of at most `2 s + 1`
products across one list of sets of between `a` and `b` coordinates, for `a ≤ b`, `2 a ≤ b + 2`,
`a ≤ d` and `1 ≤ b`. -/
theorem exists_cutRepresentable_of_syntacticallyMultilinear
    (A : Circuit (arithSignature F) (CycleMinor.inputs d) 1) (hA : A.IsSyntacticallyMultilinear)
    (hf : A.ComputesMultilinear (cycleMinorFn d)) {a b : ℕ} (hab : a ≤ b) (ha : a ≤ (b + 2) / 2)
    (had : a ≤ d) (hb : 1 ≤ b) : ∃ L ≤ 2 * A.size + 1, CutRepresentable K d a b L := by
  classical
  set V : Fin (CycleMinor.inputs d) → Finset (Fin d) := point ∅ (fun i => {i}) fun _ => ∅ with hV
  obtain ⟨L, cut, hL, hcut, hrep⟩ := A.exists_balanced_cuts (K := K) hA V
    (fun i j hij => by
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro t hi hj
      exact hij ((eq_xIdx_of_mem hi).trans (eq_xIdx_of_mem hj).symm))
    (fun i => by rcases cases_input i with rfl | ⟨t, rfl⟩ | ⟨v, rfl⟩ <;> simp [hV, hb])
    hab ha (by simpa using had)
  refine ⟨L, hL, cut, hcut, fun M => ?_⟩
  set ρ : Fin (CycleMinor.inputs d) → MvPolynomial (Fin d) K :=
    point 1 X fun v => C (padRows M v) with hρ
  obtain ⟨P, Q, hP, hQ, hsum⟩ := hrep (algebraMap F K) ρ
    (fun i => by
      rcases cases_input i with rfl | ⟨t, rfl⟩ | ⟨v, rfl⟩
      · simp [hρ, hV]
      · rw [hρ, hV, point_xIdx, point_xIdx]
        exact vars_X_subset t
      · simp [hρ, hV])
    (fun i => by
      rcases cases_input i with rfl | ⟨t, rfl⟩ | ⟨v, rfl⟩
      · rw [hρ, point_bIdx, ← C_1]
        exact C_mem_restrictDegree 1 1
      · rw [hρ, point_xIdx]
        exact X_mem_restrictDegree le_rfl _
      · rw [hρ, point_yIdx]
        exact C_mem_restrictDegree 1 _)
  refine ⟨fun j x => eval (bitPoint x) (P j), fun j x => eval (bitPoint x) (Q j),
    fun j => dependsOn_eval_bitPoint (by exact_mod_cast hP j),
    fun j => dependsOn_eval_bitPoint fun t ht => Finset.disjoint_left.mp (hQ j) ht, fun x => ?_⟩
  rw [← eval_point_padRows A hA hf M x]
  have hpt : (fun i => eval (bitPoint x) (ρ i)) = point 1 (bitPoint x) (padRows M) := by
    funext i
    rcases cases_input i with rfl | ⟨t, rfl⟩ | ⟨v, rfl⟩ <;> simp [hρ, bitPoint]
  rw [← hpt, ← Circuit.eval_eval, hsum, map_sum]
  simp only [map_mul]

/-- The cut cover number over an `F`-algebra of characteristic two is at most `2 s + 1` for a
syntactically multilinear arithmetic circuit over `F` with `s` gates computing the multilinear
representative of the cycle-and-minor function. -/
theorem cutCover_le_of_syntacticallyMultilinear
    (A : Circuit (arithSignature F) (CycleMinor.inputs d) 1) (hA : A.IsSyntacticallyMultilinear)
    (hf : A.ComputesMultilinear (cycleMinorFn d)) {a b : ℕ}
    (hab : a ≤ b) (ha : a ≤ (b + 2) / 2) (had : a ≤ d) (hb : 1 ≤ b) :
    cutCover K d a b ≤ (2 * A.size + 1 : ℕ) := by
  obtain ⟨L, hL, hrep⟩ :=
    exists_cutRepresentable_of_syntacticallyMultilinear (K := K) A hA hf hab ha had hb
  exact cutCover_le_iff.mpr ⟨L, hL, hrep⟩

/-! ### The cycle branch -/

omit [CommRing K] [Algebra F K] [CharP K 2] in
/-- **Transfer to the component size of `HC_d`.** Setting the bit and the vector of a syntactically
multilinear arithmetic circuit computing the multilinear representative of the cycle-and-minor
function to zero gives, with one more gate, a circuit whose homogeneous component of degree `d` is
the Hamiltonian cycle polynomial. -/
theorem hcComponentSize_le_of_syntacticallyMultilinear
    (A : Circuit (arithSignature F) (CycleMinor.inputs d) 1) (hA : A.IsSyntacticallyMultilinear)
    (hf : A.ComputesMultilinear (cycleMinorFn d)) : hcComponentSize F d ≤ (A.size + 1 : ℕ) := by
  classical
  have hval : ∀ z, A.eval (arithInterpretationWith F (algebraMap F F)) (bitPoint z) 0 =
      bitVal F (cycleMinorFn d z) := hf.eval_bitPoint
  set e := (finProdFinEquiv : Fin d × Fin d ≃ Fin (d * d))
  let p0 : Program (arithSignature F) (d * d) 1 :=
    (Program.empty : Program (arithSignature F) (d * d) 0).gate ⟨ArithOp.const 0, Fin.elim0⟩
  let feed : Fin (CycleMinor.inputs d) → Wire (d * d) 1 :=
    point (Wire.gate 0) (fun _ => Wire.gate 0) fun v => Wire.input (e v)
  let B : Circuit (arithSignature F) (d * d) 1 :=
    ⟨p0.append feed A.program, fun _ => Program.appendedWire feed (A.outputs 0)⟩
  set ρ : Fin (CycleMinor.inputs d) → MvPolynomial (Fin (d * d)) F :=
    point 0 (fun _ => 0) fun v => X (e v) with hρ
  have hB : B.eval (arithInterpretationWith F C) X 0 =
      A.eval (arithInterpretationWith F (C ∘ algebraMap F F)) ρ 0 := by
    change (p0.append feed A.program).trace _ X _ = A.program.trace _ ρ (A.outputs 0)
    rw [Program.trace_append_appendedWire]
    congr 1
    funext i
    have h0 : p0.trace (arithInterpretationWith F C) X (Wire.gate 0) = 0 := by
      change C 0 = 0
      exact C_0
    rcases cases_input i with rfl | ⟨t, rfl⟩ | ⟨v, rfl⟩ <;> simp [feed, hρ, h0]
  set Q := A.eval (arithInterpretationWith F (C ∘ algebraMap F F)) ρ 0
  have hQ : Q ∈ restrictDegree (Fin (d * d)) F 1 := by
    refine A.program.trace_mem_restrictDegree hA (algebraMap F F) ρ
      (point ∅ (fun _ => ∅) fun v => {e v}) (fun i j hij => ?_) (fun i => ?_) (fun i => ?_) _
    · change Disjoint _ _
      rw [Finset.disjoint_left]
      intro t hi hj
      rcases cases_input i with rfl | ⟨s, rfl⟩ | ⟨v, rfl⟩ <;>
        rcases cases_input j with rfl | ⟨s', rfl⟩ | ⟨w, rfl⟩ <;> simp_all
    · rcases cases_input i with rfl | ⟨t, rfl⟩ | ⟨v, rfl⟩
      · simp [hρ]
      · simp [hρ]
      · rw [hρ, point_yIdx, point_yIdx]
        exact vars_X_subset (e v)
    · rcases cases_input i with rfl | ⟨t, rfl⟩ | ⟨v, rfl⟩
      · rw [hρ, point_bIdx]
        exact Submodule.zero_mem _
      · rw [hρ, point_xIdx]
        exact Submodule.zero_mem _
      · rw [hρ, point_yIdx]
        exact X_mem_restrictDegree le_rfl _
  have hren : rename e (cyclePoly (d := d) F) ∈ restrictDegree (Fin (d * d)) F 1 := by
    rw [cyclePoly_eq_multilinearExtension, rename_multilinearExtension]
    exact multilinearExtension_mem_restrictDegree _
  have hQeq : Q = rename e (cyclePoly F) := by
    refine eq_of_mem_restrictDegree_of_forall_eval_bitPoint hQ hren fun w => ?_
    rw [Circuit.eval_eval, eval_rename]
    have hpt : (fun i => eval (bitPoint w) (ρ i)) = bitPoint (point false (fun _ => false)
        (w ∘ e)) := by
      funext i
      rcases cases_input i with rfl | ⟨t, rfl⟩ | ⟨v, rfl⟩ <;> simp [hρ, bitPoint, bitVal]
    rw [hpt, hval, cycleMinorFn_point, cycleMinor_false]
    have := eval_bitPoint_cyclePoly (K := F) (w ∘ e)
    rw [show (bitPoint w ∘ e : Fin d × Fin d → F) = bitPoint (w ∘ e) from rfl, this]
  refine (hcComponentSize_le B ?_).trans (by exact_mod_cast (show 1 + A.size ≤ A.size + 1 by omega))
  rw [hB]
  change homogeneousComponent d Q = _
  rw [hQeq, ← rename_homogeneousComponent, homogeneousComponent_cyclePoly,
    AlgHom.map_hamiltonianCycleSum]
  change _ = (Arithmetic.genericMatrix F d).hamiltonianCycleSum
  rw [Arithmetic.genericMatrix_eq_map_rename]
  rfl

/-! ### The main theorem -/

/-- **Syntactically multilinear circuits for the cycle-and-minor function.** A syntactically
multilinear arithmetic circuit over `F` with `s` gates computing the multilinear representative of
the cycle-and-minor function writes every minor table over an `F`-algebra `K` of characteristic two
as a sum of at most `2 s + 1` products across one list of sets of between `a` and `b` coordinates,
and gives a circuit over `F` with at most `s + 1` gates whose homogeneous component of degree `d` is
the Hamiltonian cycle polynomial. Here `a ≤ b`, `2 a ≤ b + 2`, `a ≤ d` and `1 ≤ b`. -/
theorem measures_le_of_syntacticallyMultilinear
    (A : Circuit (arithSignature F) (CycleMinor.inputs d) 1) (hA : A.IsSyntacticallyMultilinear)
    (hf : A.ComputesMultilinear (cycleMinorFn d)) {a b : ℕ}
    (hab : a ≤ b) (ha : a ≤ (b + 2) / 2) (had : a ≤ d) (hb : 1 ≤ b) :
    cutCover K d a b ≤ (2 * A.size + 1 : ℕ) ∧ hcComponentSize F d ≤ (A.size + 1 : ℕ) :=
  ⟨cutCover_le_of_syntacticallyMultilinear A hA hf hab ha had hb,
    hcComponentSize_le_of_syntacticallyMultilinear A hA hf⟩

/-! ### Deterministic decomposable circuits -/

namespace Circuit.IsDeterministicDecomposable

variable {c : Circuit Boolean.signature (CycleMinor.inputs d) 1}

omit [CharP K 2] in
/-- A d-D computing the cycle-and-minor function gives a syntactically multilinear circuit with
four gates for each of its gates computing its multilinear representative, over every commutative
ring. -/
private theorem exists_syntacticallyMultilinear_cycleMinor (hc : c.IsDeterministicDecomposable)
    (hf : c.Computes Boolean.interpretation (single (cycleMinorFn d))) :
    ∃ A : Circuit (arithSignature K) (CycleMinor.inputs d) 1, A.IsSyntacticallyMultilinear ∧
      A.ComputesMultilinear (cycleMinorFn d) ∧ A.size ≤ 4 * c.size := by
  obtain ⟨A, hA, hAf, hs⟩ := hc.exists_syntacticallyMultilinear (R := K)
  have : (fun z => c.eval Boolean.interpretation z 0) = cycleMinorFn d :=
    funext fun z => congrFun (hf z) 0
  exact ⟨A, hA, this ▸ hAf, hs⟩

/-- **d-Ds bound the cut cover number.** A d-D with `s` gates computing the cycle-and-minor function
writes every minor table over a commutative ring of characteristic two as a sum of at most `8 s + 1`
products across sets of between `a` and `b` coordinates. -/
theorem cutCover_le (hc : c.IsDeterministicDecomposable)
    (hf : c.Computes Boolean.interpretation (single (cycleMinorFn d))) {a b : ℕ} (hab : a ≤ b)
    (ha : a ≤ (b + 2) / 2) (had : a ≤ d) (hb : 1 ≤ b) :
    cutCover K d a b ≤ (8 * c.size + 1 : ℕ) := by
  obtain ⟨A, hA, hAf, hs⟩ := hc.exists_syntacticallyMultilinear_cycleMinor (K := K) hf
  exact (cutCover_le_of_syntacticallyMultilinear A hA hAf hab ha had hb).trans
    (by exact_mod_cast (show 2 * A.size + 1 ≤ 8 * c.size + 1 by omega))

omit [CharP K 2] in
/-- **d-Ds bound the component size of `HC_d`.** A d-D with `s` gates computing the
cycle-and-minor function gives, over every commutative ring, a circuit with at most `4 s + 1` gates
whose homogeneous component of degree `d` is the Hamiltonian cycle polynomial. -/
theorem hcComponentSize_le (hc : c.IsDeterministicDecomposable)
    (hf : c.Computes Boolean.interpretation (single (cycleMinorFn d))) :
    hcComponentSize K d ≤ (4 * c.size + 1 : ℕ) := by
  obtain ⟨A, hA, hAf, hs⟩ := hc.exists_syntacticallyMultilinear_cycleMinor (K := K) hf
  exact (hcComponentSize_le_of_syntacticallyMultilinear A hA hAf).trans
    (by exact_mod_cast (show A.size + 1 ≤ 4 * c.size + 1 by omega))

end Circuit.IsDeterministicDecomposable

end Cslib.Circuits

/-! ### Read-once parity branching programs -/

namespace Cslib.BranchingPrograms.NBP

open Cslib.Circuits Cslib.Circuits.CycleMinor MvPolynomial BitString

variable {d n : ℕ} {K : Type*} [CommRing K] [CharP K 2] {P : NBP (Fin (CycleMinor.inputs d)) Bool n}

/-- A read-once parity program with `w` wires computing the cycle-and-minor function gives, in
characteristic two, a syntactically multilinear circuit with at most `2 + 5 w` gates computing its
multilinear representative. -/
private theorem exists_syntacticallyMultilinear_cycleMinor (hP : P.IsReadOnce)
    (hf : ∀ z, P.AcceptsParity z ↔ cycleMinorFn d z = true) :
    ∃ A : Circuit (arithSignature K) (CycleMinor.inputs d) 1, A.IsSyntacticallyMultilinear ∧
      A.ComputesMultilinear (cycleMinorFn d) ∧ A.size ≤ 2 + 5 * P.wireCount := by
  obtain ⟨A, hA, hAf, hs⟩ := P.exists_syntacticallyMultilinear (R := K) hP
  have : (fun z => decide (P.AcceptsParity z)) = cycleMinorFn d :=
    funext fun z => by
      have := hf z
      cases h : cycleMinorFn d z <;> simp_all
  exact ⟨A, hA, this ▸ hAf, hs⟩

/-- **Read-once parity programs bound the cut cover number.** A syntactic read-once parity branching
program with `w` wires computing the cycle-and-minor function writes every minor table over a
commutative ring of characteristic two as a sum of at most `2 (2 + 5 w) + 1` products across sets of
between `a` and `b` coordinates. -/
theorem cutCover_le (hP : P.IsReadOnce) (hf : ∀ z, P.AcceptsParity z ↔ cycleMinorFn d z = true)
    {a b : ℕ} (hab : a ≤ b) (ha : a ≤ (b + 2) / 2) (had : a ≤ d) (hb : 1 ≤ b) :
    cutCover K d a b ≤ (2 * (2 + 5 * P.wireCount) + 1 : ℕ) := by
  obtain ⟨A, hA, hAf, hs⟩ := exists_syntacticallyMultilinear_cycleMinor (K := K) hP hf
  exact (cutCover_le_of_syntacticallyMultilinear A hA hAf hab ha had hb).trans
    (by exact_mod_cast (show 2 * A.size + 1 ≤ 2 * (2 + 5 * P.wireCount) + 1 by omega))

/-- **Read-once parity programs bound the component size of `HC_d`.** A syntactic read-once parity
branching program with `w` wires computing the cycle-and-minor function gives, over a commutative
ring of characteristic two, a circuit with at most `2 + 5 w + 1` gates whose homogeneous component
of degree `d` is the Hamiltonian cycle polynomial. -/
theorem hcComponentSize_le (hP : P.IsReadOnce)
    (hf : ∀ z, P.AcceptsParity z ↔ cycleMinorFn d z = true) :
    hcComponentSize K d ≤ (2 + 5 * P.wireCount + 1 : ℕ) := by
  obtain ⟨A, hA, hAf, hs⟩ := exists_syntacticallyMultilinear_cycleMinor (K := K) hP hf
  exact (hcComponentSize_le_of_syntacticallyMultilinear A hA hAf).trans
    (by exact_mod_cast (show A.size + 1 ≤ 2 + 5 * P.wireCount + 1 by omega))

end Cslib.BranchingPrograms.NBP
