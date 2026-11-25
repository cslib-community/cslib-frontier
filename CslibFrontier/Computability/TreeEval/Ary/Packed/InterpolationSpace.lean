/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.TreeEval.Ary.Packed.Interpolation
public import CslibFrontier.Computability.TreeEval.Reader.Cert.Residue
import CslibFrontier.Tactic.EncLen
import CslibFrontier.Tactic.Space

/-!
# Modular Lagrange basis evaluation within binary argument space

The counter in `basisWeight p s a x` is stored in binary. Every modular accumulator is bounded
by `p+1`, including malformed zero-modulus inputs. Thus the alphabet cardinality `s` contributes
its binary encoding length, rather than `s` cells of work space. The native arithmetic
certificates and bounded-counter iteration implement every multiplication, inverse and factor.

## Main definitions

* `Cslib.TreeEval.Ary.Packed.encBasisArgs`: encode `(p,s,a,x)` in binary.

## Main results

* `Cslib.TreeEval.Ary.Packed.basisWeight_inSpace`: the full scalar basis weight is computable
  in native work space linear in the encoded arguments.

This certifies one interpolation weight, not the full grid sum or a Tree Evaluation machine.
-/

public section

namespace Cslib.TreeEval.Ary.Packed

open Reader Turing MultiTapeTM ComputableInSpace

/-- Binary encoding of four natural parameters, in the order `(p,s,a,x)` for `basisWeight`. -/
abbrev encBasisArgs : ℕ × ℕ × ℕ × ℕ ↪ List Bool :=
  encPair encNat (encPair encNat (encPair encNat encNat))

attribute [local fun_prop] addMod_inSpace mulMod_inSpace negMod_inSpace unitInv_inSpace

/-- A single factor uses only linear space in its four binary arguments `(p,a,j,x)`. -/
theorem basisFactor_inSpace :
    ComputableInSpace (fun q : ℕ × ℕ × ℕ × ℕ => basisFactor q.1 q.2.1 q.2.2.1 q.2.2.2)
      encBasisArgs encNat fun q => (encBasisArgs q).length := by
  space [basisFactor]

attribute [local fun_prop] basisFactor_inSpace

private abbrev encBasisState : (ℕ × ℕ × ℕ) × ℕ × ℕ ↪ List Bool :=
  encPair encNat3 (encPair encNat encNat)

private theorem basisStep_inSpace :
    ComputableInSpace basisStep encBasisState encBasisState fun q => (encBasisState q).length := by
  space [basisStep]

/-- The complete basis weight, including its binary counter, is computed in native work space
linear in the binary encodings of `(p,s,a,x)`. The statement is total: no prime or positivity
hypothesis is needed for the resource certificate. -/
theorem basisWeight_inSpace :
    ComputableInSpace (fun q : ℕ × ℕ × ℕ × ℕ => basisWeight q.1 q.2.1 q.2.2.1 q.2.2.2)
      encBasisArgs encNat fun q => (encBasisArgs q).length := by
  have hstates (q : ℕ × ℕ × ℕ × ℕ) (j : ℕ) (hj : j ≤ q.2.1) :
      (encBasisState (basisStep^[j] ((q.1, q.2.2.1, q.2.2.2), 0, 1 % q.1))).length ≤
        16 * ((encBasisArgs q).length + 1) := by
    have hpar := (iterate_basisStep_counter q.1 q.2.2.1 q.2.2.2 j).1
    have hcounter := (iterate_basisStep_counter q.1 q.2.2.1 q.2.2.2 j).2
    have hacc := length_encNat_mono (basisWeight_le q.1 j q.2.2.1 q.2.2.2)
    have hs := length_encNat_mono hj
    have hsucc := length_encNat_add_le_add q.1 1
    have h1 : (encNat 1).length = 1 := rfl
    change (encBasisState
      ((basisStep^[j] ((q.1, q.2.2.1, q.2.2.2), 0, 1 % q.1)).1,
        (basisStep^[j] ((q.1, q.2.2.1, q.2.2.2), 0, 1 % q.1)).2.1,
        (basisStep^[j] ((q.1, q.2.2.1, q.2.2.2), 0, 1 % q.1)).2.2)).length ≤ _
    rw [hpar, hcounter]
    change (encBasisState ((q.1, q.2.2.1, q.2.2.2), j,
      basisWeight q.1 j q.2.2.1 q.2.2.2)).length ≤ _
    enc_len [encBasisState, encBasisArgs, encNat3] at hacc hs hsucc ⊢
  have hrun : ComputableInSpace
      (fun q : ℕ × ℕ × ℕ × ℕ =>
        basisStep^[q.2.1] ((q.1, q.2.2.1, q.2.2.2), 0, 1 % q.1))
      encBasisArgs encBasisState (fun q => (encBasisArgs q).length) :=
    budget_iterate (by space) (by space) basisStep_inSpace hstates
      (.of_le_linear 16 16 fun _ => le_rfl)
  exact (snd' (snd' hrun)).of_enc_eq fun _ => rfl

end Cslib.TreeEval.Ary.Packed
