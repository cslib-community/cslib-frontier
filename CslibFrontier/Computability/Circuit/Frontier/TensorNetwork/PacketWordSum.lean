/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.CoeffWordSum
public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.PacketTerms
public import
  CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.FastContraction.StoppingQuery.WordSum
import Mathlib.Data.Finset.Fin
import Mathlib.Data.List.GetD

/-!
# Packet entries in the existing binary sum-of-products circuit

A packet with `R` row ports uses `R * (tiles * nb).size` choice bits. Each row field selects
its local term or one dense mode. A validity factor enforces the target-mode multiplicities,
and a final factor supplies the source-mode product. Thus the whole packet entry is one sum
of products with `R + 2` factors; the existing stopping circuit can evaluate its coefficient
bits without a separate outer multiplication circuit.

`sum_factor` identifies this expression with the existing coefficient-list packet evaluator.
`value_root` and `bit_sum` instantiate the succinct stopping circuit and its carry-save sum.
The row terms and source product remain arithmetic input factors. Their native bit terminals
are part of the remaining circuit-compiler work tracked in #4741; these are semantic circuit
theorems, not a running-time bound for the complete packet evaluator.
-/

public section

namespace Cslib.Circuits.Frontier.NativePacket.PacketWordSum

open Finset GaloisRingArith TensorNetwork FastContraction

/-- The dense target modes, retaining their original indices in `Fin (tiles * nb)`. -/
@[expose] def targets (c : PacketCtx) : Finset (Fin (c.tiles * c.nb)) :=
  univ.filter fun k => modeTargets c.i c.e₁ c.e₂ (k.val / c.nb)

private theorem map_targets (c : PacketCtx) :
    (targets c).map Fin.valEmbedding = (targetModes c).toFinset := by
  ext k
  simp only [targets, targetModes, mem_map, mem_filter, mem_univ, true_and,
    List.mem_toFinset, List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j.isLt, hj⟩
  · rintro ⟨hk, ht⟩
    exact ⟨⟨k, hk⟩, ht, rfl⟩

/-- Row factors, the validity factor, then the source-mode product. Row and mode indices use
the existing port order and dense layout. Binary fields are read most significant first. -/
@[expose] noncomputable def factor (c : PacketCtx) (rows : List (ℕ × Bool)) (β : List ℕ)
    (assignment vertex : ℕ) : Ring c.p c.fl :=
  if vertex < rows.length + 1 then
    CoeffWordSum.factor (c.tiles * c.nb) rows.length (c.tiles * c.nb).size (targets c)
      (fun j o => val c.p c.fl (packetTerms.term c (rows.get j) (o.map Fin.val)))
      (fun k => β.getD k 0) assignment vertex
  else val c.p c.fl (sourceProduct c β)

/-- The complete binary sum of row terms, validity, and source-mode values is the actual native
packet entry, for all packet contexts and exponents, without grid or nondegeneracy assumptions. -/
theorem sum_factor (c : PacketCtx) (rows : List (ℕ × Bool)) (β : List ℕ) :
    (∑ assignment ∈ range (2 ^ (rows.length * (c.tiles * c.nb).size)),
      ∏ vertex ∈ range (rows.length + 2), factor c rows β assignment vertex) =
      val c.p c.fl (packetEntryNative c rows β) := by
  classical
  have hprod (assignment : ℕ) :
      (∏ vertex ∈ range (rows.length + 2), factor c rows β assignment vertex) =
      (∏ vertex ∈ range (rows.length + 1),
        CoeffWordSum.factor (c.tiles * c.nb) rows.length (c.tiles * c.nb).size (targets c)
          (fun j o => val c.p c.fl (packetTerms.term c (rows.get j) (o.map Fin.val)))
          (fun k => β.getD k 0) assignment vertex) * val c.p c.fl (sourceProduct c β) := by
    rw [show rows.length + 2 = (rows.length + 1) + 1 from by omega, prod_range_succ]
    simp only [factor, lt_self_iff_false, ↓reduceIte]
    congr 1
    apply prod_congr rfl
    intro vertex hvertex
    simp only [mem_range.mp hvertex, ↓reduceIte]
  simp_rw [hprod]
  rw [← sum_mul, CoeffWordSum.sum_factor _ _ _ (Nat.lt_size_self _)]
  have hvalue := packetTerms.val_value c (List.nodup_range.filter _) rows β
  change val c.p c.fl (packetTerms.value c rows β) =
    listCoeff (targetModes c).toFinset
      (rows.map fun r o => val c.p c.fl (packetTerms.term c r o)) (fun k => β.getD k 0) at hvalue
  rw [packetEntryNative, val_mul, hvalue]
  congr 1
  rw [← map_targets, listCoeff_map]
  congr 1
  conv_rhs => rw [← List.ofFn_get rows, List.map_ofFn, List.map_ofFn]
  rfl

private theorem representative_packetEntryNative (m : ℕ) (c : PacketCtx)
    (hfl : c.fl = modulus m) (rows : List (ℕ × Bool)) (β : List ℕ) (coefficient : ℕ) :
    ((representative m c.p (hfl ▸ val c.p c.fl (packetEntryNative c rows β))).coeff
      coefficient).val = (packetEntryNative c rows β).getD coefficient 0 := by
  rcases c with ⟨p, fl, a, L, i, tiles, t, nb, e₁, e₂, differ, cols, ζ⟩
  change fl = modulus m at hfl
  subst fl
  dsimp only
  rw [representative, coeff_modByMonicHom_val]
  split_ifs with h
  · rw [ZMod.val_natCast, Nat.mod_eq_of_lt]
    exact lt_of_mem_mul (by
      rw [List.getD_eq_getElem _ _ (by simpa only [packetEntryNative, length_mul] using h)]
      exact List.getElem_mem _)
  · rw [List.getD_eq_default _ _ (by
      simp only [packetEntryNative, length_mul]
      omega)]
    simp

/-- The packet's carry-save sum and finishing adder return the requested bit of the actual
coefficient-list output, at the packet's creation precision. Coefficients beyond the modulus
length have the same default-zero behavior as the native packet evaluator. -/
theorem bit_sum (m : ℕ) (c : PacketCtx) (hfl : c.fl = modulus m)
    (rows : List (ℕ × Bool)) (β : List ℕ) (coefficient : ℕ) (bit : Fin c.p) :
    let entry := fun assignment vertex =>
      (hfl ▸ factor c rows β assignment vertex : Ring c.p (modulus m))
    (Boolean.carryLookaheadAdd c.p).eval Boolean.interpretation
      (Boolean.CarrySaveQuery.tree
        (StoppingQuery.WordSum.leaves m c.p (rows.length + 2) entry coefficient)
        (rows.length * (c.tiles * c.nb).size) []) bit =
      ((packetEntryNative c rows β).getD coefficient 0).testBit bit.val := by
  rw [← representative_packetEntryNative m c hfl rows β coefficient]
  have hs := sum_factor c rows β
  rcases c with ⟨p, fl, a, L, i, tiles, t, nb, e₁, e₂, differ, cols, ζ⟩
  change fl = modulus m at hfl
  subst fl
  dsimp only at hs ⊢
  rw [StoppingQuery.WordSum.bit_sum, hs]

/-- The existing succinct circuit, instantiated with the packet factors, computes the actual
packet entry's selected representative bit. Arithmetic terminal labels still name factor bits. -/
theorem value_root (m : ℕ) (c : PacketCtx) (hfl : c.fl = modulus m)
    (rows : List (ℕ × Bool)) (β : List ℕ) (coefficient : Fin (modulus m).length) (bit : Fin c.p) :
    let entry := fun assignment vertex =>
      (hfl ▸ factor c rows β assignment vertex : Ring c.p (modulus m))
    StoppingQuery.value m c.p (rows.length * (c.tiles * c.nb).size) (rows.length + 2) entry
      (StoppingQuery.root m c.p (rows.length * (c.tiles * c.nb).size) (rows.length + 2)
        coefficient bit) =
      ((packetEntryNative c rows β).getD coefficient.val 0).testBit bit.val := by
  rw [← representative_packetEntryNative m c hfl rows β coefficient.val]
  have hs := sum_factor c rows β
  rcases c with ⟨p, fl, a, L, i, tiles, t, nb, e₁, e₂, differ, cols, ζ⟩
  change fl = modulus m at hfl
  subst fl
  dsimp only at hs ⊢
  rw [StoppingQuery.value_root, hs]

end Cslib.Circuits.Frontier.NativePacket.PacketWordSum
