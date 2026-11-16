/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.KernelVector
public import CslibFrontier.Foundations.LinearAlgebra.LinearSolve
import CslibFrontier.Tactic.Synthesis
import Mathlib.Tactic.Linarith

/-!
# Circuits for prescribed-entry kernel vectors and linear system solving

Over the full binary basis `fullInterpretation (k := 2)` of a field `F`, where every operation on
at most two field elements costs one gate, this module bounds the circuit size of the elimination
routines in `CslibFrontier.Foundations.LinearAlgebra.LinearSolve`:

* `Cslib.Circuits.Synthesis.full_kernelVecAt`: for an `r × n` matrix whose entries are available,
  the entries of `kernelVecAt A j` cost at most `kernelVecCost r n` gates.
* `Cslib.Circuits.Synthesis.full_vecMulSolve`: for an `r × n` matrix `M` and `n`-vector `b` whose
  entries are available, the entries of `vecMulSolve M b` cost at most
  `kernelVecCost n (r + 1) + r` gates.

As in `CslibFrontier.Computability.Circuit.KernelVector`, these bounds count field operations in
the full binary basis, not bit operations over an encoded field (`ComputableInPolyTime` for
elimination over an encoded field remains open, with rational elimination over `ℚ` handled in
`CslibFrontier.Computability.PolyTime.LinearAlgebra.RationalElimination`).

## Main results

* `Cslib.Circuits.Synthesis.full_kernelVecAt`: circuit size of `kernelVecAt`.
* `Cslib.Circuits.Synthesis.full_vecMulSolve`: circuit size of `vecMulSolve`.
-/

public section

namespace Cslib.Circuits.Synthesis

open Finset Cslib.LinearAlgebra

variable {F : Type*} [Field F] [DecidableEq F] {N n r : ℕ} {s : Set ((Fin N → F) → F)}

/-- **A kernel vector with a prescribed entry equal to one, by a circuit.** If the entries of a
matrix with `r` rows and `n` columns are available, the entries of `kernelVecAt A j` cost at most
`kernelVecCost r n = 8 * (r + 1) * (n + 1) ^ 2` gates of the full binary basis. -/
theorem full_kernelVecAt (A : Fin r → Fin n → (Fin N → F) → F) (hA : ∀ k l, A k l ∈ s)
    (j : Fin n) :
    Synthesis (fullInterpretation (k := 2)) s
      (Set.range fun l x => kernelVecAt (fun k l => A k l x) j l) (kernelVecCost r n) := by
  let K : Fin n → Fin n → (Fin N → F) → F := fun i l x => kernelBasis (fun k l => A k l x) i l
  let build := Builder.start (fullInterpretation (k := 2)) s
  let build := build.add (full_kernelBasis A hA)
  have hK : ∀ i l, K i l ∈ build.wires := fun i l => Set.mem_union_right _ ⟨(i, l), rfl⟩
  -- the flags of the first member whose entry `j` is nonzero
  let sel : Fin n → (Fin N → F) → F := fun i x => firstFlags (fun i' => K i' j x) i
  let build := build.add (full_firstFlags (s := build.wires) (fun i => K i j) fun i => hK i j)
  -- the selected member
  let u : Fin n → (Fin N → F) → F := fun l x => ∑ i, sel i x * K i l x
  let build := build.add (family (I := fullInterpretation (k := 2)) (s := build.wires)
    u (fun _ => 2 * n + 1) fun l => by
      simpa only [card_univ, Fintype.card_fin] using
        full_dot (s := build.wires) univ sel (fun i => K i l)
          (fun i _ => by synthesis_available) (fun i _ => by synthesis_available))
  -- the normalization
  let out : Fin n → (Fin N → F) → F := fun l x => (u j x)⁻¹ * u l x
  let build := build.add (family (I := fullInterpretation (k := 2)) (s := build.wires)
    out (fun _ => 1) fun l =>
      full_binary_mem (fun a b => a⁻¹ * b) (by synthesis_available) (by synthesis_available))
  refine build.finish ?_ ?_
  · rintro _ ⟨l, rfl⟩
    have hmem : out l ∈ build.wires := by synthesis_available
    convert hmem using 1
    funext x
    simp only [out, u, sel, K, kernelVecAt, kernelPivotAt, Pi.smul_apply, smul_eq_mul,
      Finset.sum_apply]
  · dsimp +zetaDelta [Builder.add, Builder.start]
    simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul, mul_one, kernelVecCost]
    nlinarith

/-- **Solving `w ᵥ* M = b` by a circuit.** If the entries of a matrix `M` with `r` rows and `n`
columns and of a vector `b` are available, the entries of `vecMulSolve M b` cost at most
`kernelVecCost n (r + 1) + r` gates of the full binary basis. -/
theorem full_vecMulSolve (M : Fin r → Fin n → (Fin N → F) → F) (b : Fin n → (Fin N → F) → F)
    (hM : ∀ k l, M k l ∈ s) (hb : ∀ l, b l ∈ s) :
    Synthesis (fullInterpretation (k := 2)) s
      (Set.range fun k x => vecMulSolve (fun k l => M k l x) (fun l => b l x) k)
      (kernelVecCost n (r + 1) + r) := by
  let B : Fin n → Fin (r + 1) → (Fin N → F) → F := fun l => Fin.cons (b l) fun k => M k l
  have hB : ∀ l c, B l c ∈ s := fun l c => by
    refine Fin.cases ?_ (fun k => ?_) c
    · exact hb l
    · exact hM k l
  have hBx (x : Fin N → F) :
      (fun l c => B l c x) = vecMulSolveMatrix (fun k l => M k l x) (fun l => b l x) := by
    funext l c
    refine Fin.cases ?_ (fun k => ?_) c <;> simp [B, vecMulSolveMatrix]
  let build := Builder.start (fullInterpretation (k := 2)) s
  let build := build.add (full_kernelVecAt B hB 0)
  let out : Fin r → (Fin N → F) → F := fun k x => -kernelVecAt (fun l c => B l c x) 0 k.succ
  let build := build.add (family (I := fullInterpretation (k := 2)) (s := build.wires)
    out (fun _ => 1) fun k => full_unary (fun a => -a) (by synthesis_available))
  refine build.finish ?_ ?_
  · rintro _ ⟨k, rfl⟩
    have hmem : out k ∈ build.wires := by synthesis_available
    convert hmem using 1
    funext x
    simp only [out, vecMulSolve, hBx]
  · dsimp +zetaDelta [Builder.add, Builder.start]
    simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
    omega

end Cslib.Circuits.Synthesis
