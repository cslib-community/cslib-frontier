/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.RingTheory.SparseTrinomial
public import CslibFrontier.Computability.PolyTime.GaloisRingSeries
public import CslibFrontier.Computability.Circuit.Boolean.Modular.InnerProduct
public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.FastContractionMachine

/-!
# Sparse multiplication in the chosen contraction ring

The monic modulus used by the root and child contractions is the trinomial with exponents
`2q` and `q`. Each coordinate of a product consequently uses at most three convolutions.
-/

public section
namespace Cslib.Circuits.Frontier.FastContraction

open Polynomial GaloisRingArith SparseTrinomial

/-- Each reduced coefficient of the product in the selected modulus uses at most three
ordinary product coefficients. The precision and contraction scale stay uniform. -/
theorem coeff_mul_modulus (m p : ℕ) (u v : (ZMod (2 ^ p))[X])
    (hu : u.natDegree < (modulus m).length) (hv : v.natDegree < (modulus m).length)
    (i : Fin (modulus m).length) :
    ((u * v) %ₘ (monicOf (modulus m)).map (Int.castRingHom (ZMod (2 ^ p)))).coeff i.val =
      reducedCoeff (3 ^ modulusExp m) (u * v).coeff i.val := by
  nontriviality ZMod (2 ^ p)
  rw [monicOf_modulus]
  simp only [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one]
  apply coeff_mod_sparse _ (by positivity)
  · have := natDegree_mul_le (p := u) (q := v)
    rw [length_modulus] at hu hv
    omega
  · simpa only [length_modulus] using i.isLt

/-- The polynomial of degree below the selected modulus representing a contraction-ring element. -/
@[expose] noncomputable def representative (m p : ℕ) (x : Ring p (modulus m)) :
    (ZMod (2 ^ p))[X] :=
  AdjoinRoot.modByMonicHom ((monic_monicOf (modulus m)).map _) x

theorem natDegree_representative_lt (m p : ℕ) (x : Ring p (modulus m)) :
    (representative m p x).natDegree < (modulus m).length := by
  have hpos : 0 < (modulus m).length := by rw [length_modulus]; positivity
  rcases subsingleton_or_nontrivial (ZMod (2 ^ p)) with h | h
  · rw [Subsingleton.elim (representative m p x) 0, natDegree_zero]
    exact hpos
  obtain ⟨P, rfl⟩ := AdjoinRoot.mk_surjective x
  let f := (monicOf (modulus m)).map (Int.castRingHom (ZMod (2 ^ p)))
  have hm : f.Monic := (monic_monicOf _).map _
  have hdeg : f.natDegree = (modulus m).length :=
    ((monic_monicOf _).natDegree_map _).trans (natDegree_monicOf _)
  change (P %ₘ f).natDegree < _
  rw [← hdeg]
  exact natDegree_modByMonic_lt _ hm fun he => by simp [he] at hdeg; omega

/-- Pack the coefficient words used on one side of a convolution inner product. -/
@[expose] noncomputable def coefficientWords {d p : ℕ} (u : Fin d → ZMod (2 ^ p)) :
    BitString (d * p) :=
  BitString.blocksEquiv.symm fun j => (BitString.equivFin p).symm ⟨(u j).val, ZMod.val_lt _⟩

/-- Evaluate the Boolean inner-product circuit on one ordinary convolution diagonal. -/
@[expose] noncomputable def convolutionCircuit (d p k : ℕ) (u v : (ZMod (2 ^ p))[X]) :
    ZMod (2 ^ p) :=
  ((BitString.equivFin p ((Boolean.Modular.innerProduct d p).eval Boolean.interpretation
    (Fin.append (coefficientWords fun j => u.coeff j.val)
      (coefficientWords fun j => if j.val ≤ k then v.coeff (k - j.val) else 0)))) : ℕ)

theorem convolutionCircuit_eq_coeff (d p k : ℕ) (u v : (ZMod (2 ^ p))[X])
    (hu : u.natDegree < d) : convolutionCircuit d p k u v = (u * v).coeff k := by
  rw [convolutionCircuit, Boolean.Modular.val_eval_innerProduct, coeff_mul_eq_inner _ _ hu]
  simp only [coefficientWords, BitString.block_blocksEquiv_symm, Equiv.apply_symm_apply,
    ZMod.natCast_mod, Nat.cast_sum, Nat.cast_mul, ZMod.natCast_zmod_val]

/-- An arbitrary product coordinate of the actual contraction ring, as two or three Boolean
inner-product evaluations at the original precision. -/
theorem representative_mul_coeff (m p : ℕ) (x y : Ring p (modulus m))
    (i : Fin (modulus m).length) :
    (representative m p (x * y)).coeff i.val = reducedCoeff (3 ^ modulusExp m)
      (fun k => convolutionCircuit (modulus m).length p k
        (representative m p x) (representative m p y)) i.val := by
  let f := (monicOf (modulus m)).map (Int.castRingHom (ZMod (2 ^ p)))
  have hmk (z : Ring p (modulus m)) : AdjoinRoot.mk f (representative m p z) = z :=
    AdjoinRoot.mk_leftInverse ((monic_monicOf _).map _) _
  have he : x * y = AdjoinRoot.mk f (representative m p x * representative m p y) := by
    rw [map_mul, hmk, hmk]
  rw [he, representative, AdjoinRoot.modByMonicHom_mk, coeff_mul_modulus m p _ _
    (natDegree_representative_lt _ _ _) (natDegree_representative_lt _ _ _) i]
  simp only [convolutionCircuit_eq_coeff _ _ _ _ _ (natDegree_representative_lt _ _ _)]

/-- The native ring multiplication on lists agrees coordinate by coordinate with the sparse
inner-product formula, including short, long and noncanonical input lists. -/
theorem mul_getD_eq_reduced (m p : ℕ) (c d : List ℕ) (i : Fin (modulus m).length) :
    ((mul p (modulus m) c d).getD i.val 0 : ZMod (2 ^ p)) = reducedCoeff (3 ^ modulusExp m)
      (fun k => convolutionCircuit (modulus m).length p k
        (representative m p (val p (modulus m) c)) (representative m p (val p (modulus m) d)))
      i.val := by
  have he := representative_mul_coeff m p (val p (modulus m) c) (val p (modulus m) d) i
  rwa [← val_mul, representative, coeff_modByMonicHom_val, ite_eq_left i.isLt] at he

end Cslib.Circuits.Frontier.FastContraction
