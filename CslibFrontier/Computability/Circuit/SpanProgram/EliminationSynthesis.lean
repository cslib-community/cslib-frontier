/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.KernelVector
public import CslibFrontier.Computability.Circuit.SpanProgram.Elimination
import CslibFrontier.Computability.Circuit.LinearSolve
import CslibFrontier.Tactic.Synthesis

/-!
# Circuits for `Lin` and `P_L`

[Boneh and Shoup, Theorem 22.14, p. 981][BonehShoup2023] calls the algorithm `Lin` efficient and
the program `P_L` efficiently computable. For the deterministic algorithms `Lin` and `P_L`, the
book's efficiency requirement (Definition 2.8, p. 30) is one algorithm on bit-string inputs whose
running time is polynomially bounded uniformly across inputs; Definition 2.8 additionally permits a
negligible running-time tail for probabilistic algorithms. This file
bounds the circuits that compute `MonotoneSpanProgram.recombination`,
`MonotoneSpanProgram.nullVector` and `MonotoneSpanProgram.normalForm` themselves, with the program
and the coalition as inputs. The bounds are a step toward the efficiency claims of Theorem 22.14,
not those claims.

For each shape of program (number of parties `N`, `tailDim + 1` columns, row dimensions
`rowDim`), there is one circuit. Its available wires are the matrix entries `M i row c` and, for
each party, a membership value `χ i`, nonzero for the members; at an input `x` the program is
`⟨tailDim, rowDim, fun i row c => M i row c x⟩` and the coalition is `{i | χ i x ≠ 0}`. The gates
are those of `fullInterpretation (k := 2)` over the field: one gate computes any function of at
most two field elements, so a zero test with selection, a product and a quotient `a⁻¹ * b` each
count as one gate. The bounds therefore count field operations and zero tests, not bit
operations. With `r = ∑ i, rowDim i` rows, `d = tailDim + 1` columns and
`kernelVecCost r n = 8 * (r + 1) * (n + 1) ^ 2`, the bounds are of order
`(r + 1) * d ^ 2 + d * (r + 1) ^ 2`.

Open: a bound in bit operations over an encoded field, and uniformity of the circuits in the
shape `(N, tailDim, rowDim)` (#5293).

## Main results

* `Cslib.Circuits.Synthesis.full_recombination`: the entries of `Lin`.
* `Cslib.Circuits.Synthesis.full_nullVector`: the kernel vector.
* `Cslib.Circuits.Synthesis.full_normalForm`: the entries of `P_L`.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023],
  Theorem 22.14, p. 981.
-/

public section

namespace Cslib.Circuits.Synthesis

open Finset Cslib.LinearAlgebra

variable {F : Type*} [Field F] [DecidableEq F] {N N' : ℕ} {src : Set ((Fin N' → F) → F)}

/-- The stacked rows of the members of the coalition cost one selection gate for each entry. -/
private theorem full_stack (tailDim : ℕ) (rowDim : Fin N → ℕ)
    (M : (i : Fin N) → Fin (rowDim i) → Fin (tailDim + 1) → (Fin N' → F) → F)
    (χ : Fin N → (Fin N' → F) → F)
    (hM : ∀ i row c, M i row c ∈ src) (hχ : ∀ i, χ i ∈ src) :
    Synthesis (fullInterpretation (k := 2)) src
      (Set.range fun (kc : Fin (∑ i, rowDim i) × Fin (tailDim + 1)) x =>
        (MonotoneSpanProgram.mk tailDim rowDim fun i row c => M i row c x).stack
          (univ.filter fun i => χ i x ≠ 0) kc.1 kc.2)
      ((∑ i, rowDim i) * (tailDim + 1)) := by
  let e := finSigmaFinEquiv (m := N) (n := rowDim)
  have h := family (I := fullInterpretation (k := 2)) (s := src)
    (fun (kc : Fin (∑ i, rowDim i) × Fin (tailDim + 1)) x =>
      if χ (e.symm kc.1).1 x ≠ 0 then M (e.symm kc.1).1 (e.symm kc.1).2 kc.2 x else 0)
    (fun _ => 1)
    fun kc => full_binary_mem (fun a b : F => if a ≠ 0 then b else 0) (hχ _) (hM _ _ _)
  refine h.mono Set.Subset.rfl ?_ (by simp)
  rintro _ ⟨kc, rfl⟩
  refine ⟨kc, funext fun x => ?_⟩
  simp only [MonotoneSpanProgram.stack, mem_filter, mem_univ, true_and, e]
  split_ifs <;> rfl

/-- A field-gate circuit for `Lin` for each shape of program, a step toward the efficiency claim
of [BonehShoup2023], Theorem 22.14(a) (p. 981), not that claim. For a program with
`r = ∑ i, rowDim i` rows and `tailDim + 1` columns whose entries, together with the membership
values of a coalition, are available wires, the entries of the recombination vectors of that
coalition cost at most `kernelVecCost (tailDim + 1) (r + 1) + r * (tailDim + 2) + 2` gates, one
gate being any function of at most two field elements. A bound in bit operations and uniformity
in the shape are open (#5293). -/
theorem full_recombination (tailDim : ℕ) (rowDim : Fin N → ℕ)
    (M : (i : Fin N) → Fin (rowDim i) → Fin (tailDim + 1) → (Fin N' → F) → F)
    (χ : Fin N → (Fin N' → F) → F)
    (hM : ∀ i row c, M i row c ∈ src) (hχ : ∀ i, χ i ∈ src) :
    Synthesis (fullInterpretation (k := 2)) src
      (Set.range fun (p : (i : Fin N) × Fin (rowDim i)) x =>
        (MonotoneSpanProgram.mk tailDim rowDim fun i row c => M i row c x).recombination
          (univ.filter fun i => χ i x ≠ 0) p.1 p.2)
      (kernelVecCost (tailDim + 1) (∑ i, rowDim i + 1) + (∑ i, rowDim i) * (tailDim + 2) + 2) := by
  let e := finSigmaFinEquiv (m := N) (n := rowDim)
  let A : Fin (∑ i, rowDim i) → Fin (tailDim + 1) → (Fin N' → F) → F := fun k c x =>
    (MonotoneSpanProgram.mk tailDim rowDim fun i row c => M i row c x).stack
      (univ.filter fun i => χ i x ≠ 0) k c
  let b : Fin (tailDim + 1) → (Fin N' → F) → F := fun c => if c = 0 then fun _ => 1 else fun _ => 0
  let build := Builder.start (fullInterpretation (k := 2)) src
  let build := build.add (full_const (k := 2) (s := build.wires) (0 : F))
  let build := build.add (full_const (k := 2) (s := build.wires) (1 : F))
  let build := build.add (full_stack (src := build.wires) tailDim rowDim M χ
    (fun i row c => Set.mem_union_left _ (Set.mem_union_left _ (hM i row c)))
    (fun i => Set.mem_union_left _ (Set.mem_union_left _ (hχ i))))
  have hA : ∀ k c, A k c ∈ build.wires := fun k c => Set.mem_union_right _ ⟨(k, c), rfl⟩
  have hb : ∀ c, b c ∈ build.wires := by
    intro c
    by_cases hc : c = 0
    · simp only [b, ite_eq_left hc]
      exact Set.mem_union_left _ (Set.mem_union_right _ rfl)
    · simp only [b, ite_eq_right hc]
      exact Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_right _ rfl))
  let build := build.add (full_vecMulSolve A b hA hb)
  refine build.finish ?_ ?_
  · rintro _ ⟨⟨i, row⟩, rfl⟩
    refine Set.mem_union_right _ ⟨e ⟨i, row⟩, funext fun x => ?_⟩
    have hbx : (fun l => b l x) =
        (MonotoneSpanProgram.mk tailDim rowDim fun i row c => M i row c x).target := by
      funext l
      by_cases hl : l = 0
      · simp [b, MonotoneSpanProgram.target, hl]
      · simp [b, MonotoneSpanProgram.target, hl]
    simp only [MonotoneSpanProgram.recombination, hbx, e, A]
  · have hmul : (∑ i, rowDim i) * (tailDim + 2) = (∑ i, rowDim i) * (tailDim + 1) + ∑ i, rowDim i :=
      Nat.mul_succ _ _
    dsimp +zetaDelta [Builder.add, Builder.start]
    omega

/-- **A circuit for the kernel vector.** For a program with `r = ∑ i, rowDim i` rows and
`tailDim + 1` columns whose entries, together with the membership values of a coalition, are
available wires, the entries of `nullVector` of that coalition cost at most
`kernelVecCost r (tailDim + 1) + r * (tailDim + 1)` gates, one gate being any function of at most
two field elements. -/
theorem full_nullVector (tailDim : ℕ) (rowDim : Fin N → ℕ)
    (M : (i : Fin N) → Fin (rowDim i) → Fin (tailDim + 1) → (Fin N' → F) → F)
    (χ : Fin N → (Fin N' → F) → F)
    (hM : ∀ i row c, M i row c ∈ src) (hχ : ∀ i, χ i ∈ src) :
    Synthesis (fullInterpretation (k := 2)) src
      (Set.range fun (c : Fin (tailDim + 1)) x =>
        (MonotoneSpanProgram.mk tailDim rowDim fun i row c => M i row c x).nullVector
          (univ.filter fun i => χ i x ≠ 0) c)
      (kernelVecCost (∑ i, rowDim i) (tailDim + 1) + (∑ i, rowDim i) * (tailDim + 1)) := by
  let A : Fin (∑ i, rowDim i) → Fin (tailDim + 1) → (Fin N' → F) → F := fun k c x =>
    (MonotoneSpanProgram.mk tailDim rowDim fun i row c => M i row c x).stack
      (univ.filter fun i => χ i x ≠ 0) k c
  let build := Builder.start (fullInterpretation (k := 2)) src
  let build := build.add (full_stack tailDim rowDim M χ hM hχ)
  have hA : ∀ k c, A k c ∈ build.wires := fun k c => Set.mem_union_right _ ⟨(k, c), rfl⟩
  let build := build.add (full_kernelVecAt A hA 0)
  refine build.finish ?_ ?_
  · rintro _ ⟨c, rfl⟩
    exact Set.mem_union_right _ ⟨c, rfl⟩
  · dsimp +zetaDelta [Builder.add, Builder.start]
    omega

/-- A field-gate circuit for `P_L` for each shape of program, a step toward the efficiency claim
of [BonehShoup2023], Theorem 22.14(b) (p. 981), not that claim. For a program with
`r = ∑ i, rowDim i` rows and `tailDim + 1` columns whose entries, together with the membership
values of a coalition, are available wires, all entries of `normalForm` of that coalition cost
at most `kernelVecCost r (tailDim + 1) + r * (3 * tailDim + 4)` gates, one gate being any
function of at most two field elements. A bound in bit operations and uniformity in the shape
are open (#5293). -/
theorem full_normalForm (tailDim : ℕ) (rowDim : Fin N → ℕ)
    (M : (i : Fin N) → Fin (rowDim i) → Fin (tailDim + 1) → (Fin N' → F) → F)
    (χ : Fin N → (Fin N' → F) → F)
    (hM : ∀ i row c, M i row c ∈ src) (hχ : ∀ i, χ i ∈ src) :
    Synthesis (fullInterpretation (k := 2)) src
      (Set.range <| Function.uncurry fun (p : (i : Fin N) × Fin (rowDim i))
        (c : Fin (tailDim + 1)) x =>
          ((MonotoneSpanProgram.mk tailDim rowDim fun i row c => M i row c x).normalForm
            (univ.filter fun i => χ i x ≠ 0)).matrix p.1 p.2 c)
      (kernelVecCost (∑ i, rowDim i) (tailDim + 1) + (∑ i, rowDim i) * (3 * tailDim + 4)) := by
  let v : Fin (tailDim + 1) → (Fin N' → F) → F := fun c x =>
    (MonotoneSpanProgram.mk tailDim rowDim fun i row c => M i row c x).nullVector
      (univ.filter fun i => χ i x ≠ 0) c
  let build := Builder.start (fullInterpretation (k := 2)) src
  let build := build.add (full_nullVector tailDim rowDim M χ hM hχ)
  have hv : ∀ c, v c ∈ build.wires := fun c => Set.mem_union_right _ ⟨c, rfl⟩
  have hM' : ∀ i row c, M i row c ∈ build.wires := fun i row c => Set.mem_union_left _ (hM i row c)
  -- the new first columns
  let col : ((i : Fin N) × Fin (rowDim i)) → (Fin N' → F) → F := fun p x =>
    ∑ c, M p.1 p.2 c x * v c x
  let build := build.add (family (I := fullInterpretation (k := 2)) (s := build.wires)
    col (fun _ => 2 * (tailDim + 1) + 1) fun p => by
      simpa only [card_univ, Fintype.card_fin] using
        full_dot (s := build.wires) univ (fun c => M p.1 p.2 c) v
          (fun c _ => hM' _ _ c) (fun c _ => hv c))
  refine build.finish ?_ ?_
  · rintro _ ⟨⟨⟨i, row⟩, c⟩, rfl⟩
    refine Fin.cases ?_ (fun c => ?_) c
    · refine Set.mem_union_right _ ⟨⟨i, row⟩, funext fun x => ?_⟩
      exact (MonotoneSpanProgram.mulRight_shearMatrix_matrix_zero
        (MonotoneSpanProgram.mk tailDim rowDim fun i row c => M i row c x) _ i row).symm
    · have hfun : (fun x => ((MonotoneSpanProgram.mk tailDim rowDim fun i row c =>
          M i row c x).normalForm (univ.filter fun i => χ i x ≠ 0)).matrix i row c.succ) =
            M i row c.succ :=
        funext fun x => MonotoneSpanProgram.normalForm_matrix_succ
          (MonotoneSpanProgram.mk tailDim rowDim fun i row c => M i row c x) _ i row c
      have hmem : (fun x => ((MonotoneSpanProgram.mk tailDim rowDim fun i row c =>
          M i row c x).normalForm (univ.filter fun i => χ i x ≠ 0)).matrix i row c.succ) ∈
            src := by
        rw [hfun]
        exact hM i row c.succ
      exact Set.mem_union_left _ (Set.mem_union_left _ hmem)
  · have hmul : (∑ i, rowDim i) * (3 * tailDim + 4) =
        (∑ i, rowDim i) * (tailDim + 1) + (∑ i, rowDim i) * (2 * (tailDim + 1) + 1) := by
      rw [← Nat.mul_add]
      congr 1
      omega
    dsimp +zetaDelta [Builder.add, Builder.start]
    simp only [sum_const, card_univ, Fintype.card_sigma, Fintype.card_fin, smul_eq_mul]
    omega

end Cslib.Circuits.Synthesis
