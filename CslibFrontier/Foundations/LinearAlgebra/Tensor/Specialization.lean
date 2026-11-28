/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.LinearAlgebra.Tensor.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import CslibFrontier.Foundations.LinearAlgebra.Tensor.Degeneration
import CslibFrontier.Foundations.RingTheory.Specialization

/-!
# Tensor rank under specialization

A ring homomorphism maps a rank decomposition to one with the same number of terms
(`Cslib.Tensor.Rank.map`). For a tensor with integer entries, this transfers rank between fields of
the same characteristic: rank at most `r` over a field `F` of characteristic `p` gives rank at most
`r` over every algebraically closed field `KK` of characteristic `p` (`Cslib.Tensor.Rank.transfer`).
The proof is that of the circuit transfer lemma `Separation.lem_transfer`: map the decomposition
into a common ring of `F` and `KK` (`Cslib.exists_common_ring`), lift its finitely many
coefficients to a subring with a homomorphism to `KK` (`Cslib.exists_specialisation`), and map it
there.

## Main results

* `Cslib.Tensor.map_unit`, `Cslib.Tensor.map_mm`: ring homomorphisms fix `⟨n⟩` and `⟨p, q, r⟩`.
* `Cslib.Tensor.Rank.map`: rank is kept by ring homomorphisms.
* `Cslib.Tensor.Rank.transfer`: rank transfer to an algebraically closed field of the same
  characteristic.
-/

public section

namespace Cslib.Tensor

variable {X Y Z : Type*} {R S : Type*} [CommSemiring R] [CommSemiring S]

/-- A ring homomorphism maps the unit tensor to the unit tensor. -/
@[simp] theorem map_unit (f : R →+* S) (n : ℕ) : (unit n : Tensor R _ _ _).map f = unit n := by
  funext i j k
  simp only [Tensor.map_apply, unit_apply]
  split_ifs <;> simp

/-- A ring homomorphism maps the matrix multiplication tensor to itself. -/
@[simp] theorem map_mm (f : R →+* S) (p q r : ℕ) :
    (mm p q r : Tensor R _ _ _).map f = mm p q r := by
  funext a b c
  simp only [Tensor.map_apply, mm_apply]
  split_ifs <;> simp

/-- A ring homomorphism maps a rank decomposition of `T` to one of the image of `T`. -/
theorem Rank.map (f : R →+* S) {r : ℕ} {T : Tensor R X Y Z} (h : Rank r T) : Rank r (T.map f) := by
  obtain ⟨α, β, γ, rfl⟩ := h
  exact ⟨α.map f, β.map f, γ.map f, by rw [map_restrict, map_unit]⟩

variable [Finite X] [Finite Y] [Finite Z]

/-- **Rank transfer.** An integer tensor of rank at most `r` over a field of characteristic `p`
has rank at most `r` over every algebraically closed field of characteristic `p`. -/
theorem Rank.transfer {F KK : Type} [Field F] [Field KK] [IsAlgClosed KK] (p : ℕ) [CharP F p]
    [CharP KK p] (T : Tensor ℤ X Y Z) {r : ℕ} (h : Rank r (T.map (Int.castRingHom F))) :
    Rank r (T.map (Int.castRingHom KK)) := by
  classical
  have := Fintype.ofFinite X
  have := Fintype.ofFinite Y
  have := Fintype.ofFinite Z
  obtain ⟨R, _, _, ⟨φF⟩, ⟨φK⟩⟩ := exists_common_ring F KK p
  -- the decomposition in the common ring `R`
  obtain ⟨α, β, γ, hR⟩ := h.map φF
  -- its coefficients lie in a subring `A` of `R` with a homomorphism to `KK`
  let S : Finset R := Finset.univ.image (fun kx : Fin r × X => α kx.1 kx.2) ∪
    Finset.univ.image (fun ky : Fin r × Y => β ky.1 ky.2) ∪
    Finset.univ.image (fun zk : Z × Fin r => γ zk.1 zk.2)
  obtain ⟨A, hSA, ⟨ψ⟩⟩ := exists_specialisation φK S
  have mem {a : R} (ha : a ∈ S) : a ∈ A := hSA ha
  have hS {a : R} : a ∈ S ↔ ((∃ kx : Fin r × X, α kx.1 kx.2 = a) ∨
      ∃ ky : Fin r × Y, β ky.1 ky.2 = a) ∨ ∃ zk : Z × Fin r, γ zk.1 zk.2 = a := by
    simp only [S, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
  let α' : Matrix (Fin r) X A := fun k x => ⟨α k x, mem (hS.2 (.inl (.inl ⟨(k, x), rfl⟩)))⟩
  let β' : Matrix (Fin r) Y A := fun k y => ⟨β k y, mem (hS.2 (.inl (.inr ⟨(k, y), rfl⟩)))⟩
  let γ' : Matrix Z (Fin r) A := fun z k => ⟨γ z k, mem (hS.2 (.inr ⟨(z, k), rfl⟩))⟩
  have hA : restrict α' β' γ' (unit r) = T.map (Int.castRingHom A) := by
    funext x y z
    apply Subtype.val_injective
    have := congrFun (congrFun (congrFun hR x) y) z
    simp only [Tensor.map_apply, eq_intCast, map_intCast, restrict_unit] at this
    rw [restrict_unit]
    simp only [Tensor.map_apply, eq_intCast, α', β', γ']
    push_cast
    exact this
  have := (show Rank r (T.map (Int.castRingHom A)) from ⟨α', β', γ', hA⟩).map ψ
  convert this using 1
  funext x y z
  simp only [Tensor.map_apply, eq_intCast, map_intCast]

end Cslib.Tensor
