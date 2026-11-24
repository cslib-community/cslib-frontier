/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.MLDSA.RejNTTProgramming
public import CslibFrontier.Crypto.Computational.MLDSA.FIPS204NTT
import CslibFrontier.Foundations.Data.Option
import Batteries.Data.Vector.Lemmas
import CslibFrontier.Probability.PMF.Uniform

/-!
# Programming the SHAKE128 addresses used by ExpandA

Algorithm 32 of [FIPS 204][NISTFIPS204] reads a different raw SHAKE128 input for each matrix
entry. At a fixed public seed the experiment samples the prefixes at those inputs, holding
the rest of the XOF fixed. Longer reads return the original stream after byte 894.
-/

public section

namespace Cslib.Crypto.MLDSA.FIPS204

open Cslib.Probability

private abbrev Cell (s : Level) := Fin s.params.k × Fin s.params.ℓ

private def address {s : Level} (rho : List Byte) (p : Cell s) : List Bool :=
  Keccak.bytesToBitsLE (rho ++ [Fin.ofNat 256 p.2.val, Fin.ofNat 256 p.1.val])

private def cellAt (s : Level) (rho : List Byte) (x : List Bool) : Option (Cell s) := do
  let tail := x.drop (Keccak.bytesToBitsLE rho).length
  let j := Keccak.bitsToByteLE (tail.take 8)
  let i := Keccak.bitsToByteLE (tail.drop 8)
  if hi : i.val < s.params.k then
    if hj : j.val < s.params.ℓ then
      let p : Cell s := (⟨i.val, hi⟩, ⟨j.val, hj⟩)
      if address rho p = x then some p else none
    else none
  else none

private theorem cellAt_address (s : Level) (rho : List Byte) (p : Cell s) :
    cellAt s rho (address rho p) = some p := by
  have hk : s.params.k ≤ 256 := by cases s <;> decide
  have hl : s.params.ℓ ≤ 256 := by cases s <;> decide
  let i := Fin.ofNat 256 p.1.val
  let j := Fin.ofNat 256 p.2.val
  have hi : i.val = p.1.val := Nat.mod_eq_of_lt (p.1.isLt.trans_le hk)
  have hj : j.val = p.2.val := Nat.mod_eq_of_lt (p.2.isLt.trans_le hl)
  have haddr : address rho p =
      Keccak.bytesToBitsLE rho ++ (Keccak.byteBitsLE j ++ Keccak.byteBitsLE i) := by
    simp [address, Keccak.bytesToBitsLE, i, j]
  have h8 : (Keccak.byteBitsLE j).length = 8 := by simp [Keccak.byteBitsLE]
  have take8 : (Keccak.byteBitsLE j ++ Keccak.byteBitsLE i).take 8 = Keccak.byteBitsLE j := by
    rw [← h8, List.take_append_length]
  have drop8 : (Keccak.byteBitsLE j ++ Keccak.byteBitsLE i).drop 8 = Keccak.byteBitsLE i := by
    rw [← h8, List.drop_left]
  simp only [cellAt, List.drop_left, take8, drop8, Keccak.bitsToByteLE_byteBitsLE,
    hi, hj, p.1.isLt, p.2.isLt, dite_true, Fin.eta, Prod.eta, haddr, ite_true]

private theorem address_of_cellAt {s : Level} {rho : List Byte} {x : List Bool} {p : Cell s}
    (h : cellAt s rho x = some p) : address rho p = x := by
  dsimp only [cellAt] at h
  split_ifs at h; simp_all

/-- The SHAKE128 prefixes used by Algorithm 32, indexed by matrix row and column. -/
abbrev MatrixPrefixes (s : Level) := Fin s.params.k → Fin s.params.ℓ → FixedBytes 894

/-- Install 894 bytes at each literal SHAKE128 matrix address for one public seed.
The suffix at each such address and all reads at other inputs are supplied by the original XOF. -/
def Xofs.withMatrixPrefixes (H : Xofs) (s : Level) (rho : List Byte) (t : MatrixPrefixes s) :
    Xofs :=
  { H with h128 := H.h128.withPrefixes fun x =>
      (cellAt s rho x).map fun (i, j) => List.ofFn (t i j) }

/-- Programming SHAKE128 matrix prefixes leaves the SHAKE256 oracle unchanged. -/
@[simp] theorem Xofs.withMatrixPrefixes_h256 (H : Xofs) (s : Level) (rho : List Byte)
    (t : MatrixPrefixes s) : (H.withMatrixPrefixes s rho t).h256 = H.h256 := by rfl

/-- Reading a programmed matrix address through the production SHAKE128 interface returns its
full replacement followed by the original suffix, truncated at the requested byte count. -/
theorem read_withMatrixPrefixes (H : Xofs) (s : Level) (rho : List Byte) (t : MatrixPrefixes s)
    (i : Fin s.params.k) (j : Fin s.params.ℓ) (n : ℕ) :
    (H.withMatrixPrefixes s rho t).h128.readBytes
        (rho ++ [Fin.ofNat 256 j.val, Fin.ofNat 256 i.val]) n =
      (List.ofFn (t i j)).take n ++
        (H.h128.readBytes (rho ++ [Fin.ofNat 256 j.val, Fin.ofNat 256 i.val]) n).drop 894 := by
  simp only [Xofs.withMatrixPrefixes, ExtendableOutput.readBytes, ExtendableOutput.withPrefixes]
  change (match (cellAt s rho (address rho (i, j))).map _ with
    | none => _
    | some p => H.h128.readWithPrefix _ n p) = _
  rw [cellAt_address]
  simp only [Option.map_some, ExtendableOutput.readWithPrefix, List.length_ofFn]

/-- Every raw input outside the `ρ || column || row` grid retains all its SHAKE128 bytes. -/
theorem read_withMatrixPrefixes_of_ne (H : Xofs) (s : Level) (rho : List Byte)
    (t : MatrixPrefixes s) (x : List Bool)
    (h : ∀ (i : Fin s.params.k) (j : Fin s.params.ℓ),
      Keccak.bytesToBitsLE (rho ++ [Fin.ofNat 256 j.val, Fin.ofNat 256 i.val]) ≠ x) (n : ℕ) :
    (H.withMatrixPrefixes s rho t).h128.read x n = H.h128.read x n := by
  have hnone : cellAt s rho x = none := by
    cases ha : cellAt s rho x with
    | none => rfl
    | some p => exact False.elim (h p.1 p.2 (address_of_cellAt ha))
  simp only [Xofs.withMatrixPrefixes, ExtendableOutput.withPrefixes, hnone, Option.map_none]

/-- Algorithm 32 receives the installed 894 bytes at this public row and column. -/
theorem read_matrixEntry (H : Xofs) (s : Level) (rho : List Byte) (t : MatrixPrefixes s)
    (i : Fin s.params.k) (j : Fin s.params.ℓ) :
    (H.withMatrixPrefixes s rho t).h128.readBytes
        (rho ++ [Fin.ofNat 256 j.val, Fin.ofNat 256 i.val]) 894 = List.ofFn (t i j) := by
  rw [read_withMatrixPrefixes, List.take_of_length_le List.length_ofFn.le,
    List.drop_of_length_le, List.append_nil]
  exact (H.h128.length_read _ _).le

/-- Program all matrix prefixes using an external matrix in coefficient representation.
At each address, exchange the accepted proposals with the forward NTT of that matrix entry. -/
def programMatrixPrefixes (s : Level) (t : MatrixPrefixes s) (A : PublicMatrix s) :
    MatrixPrefixes s := fun i j =>
  (exchangeRejNTT 894 (t i j, fromNTTEquiv.symm (A i j))).1

private theorem sample_programMatrixPrefixes (s : Level) (t : MatrixPrefixes s)
    (A : PublicMatrix s) (i : Fin s.params.k) (j : Fin s.params.ℓ) :
    (rejNTTPoly (List.ofFn (programMatrixPrefixes s t A i j))).map fromNTT =
      ((rejNTTPoly (List.ofFn (t i j))).map fromNTT).map fun _ => Vector.ofFn (A i j) := by
  cases h : rejNTTPoly (List.ofFn (t i j)) with
  | none =>
    rw [programMatrixPrefixes, exchangeRejNTT_of_none h]
    rfl
  | some y =>
    rw [programMatrixPrefixes, (exchangeRejNTT_of_some h _).1]
    apply congrArg some
    apply Vector.ext
    intro k hk
    have hv := congrFun (fromNTTEquiv.apply_symm_apply (A i j)) ⟨k, hk⟩
    rw [fromNTTEquiv_apply] at hv
    simpa only [Vector.get_eq_getElem, Vector.getElem_ofFn] using hv

/-- The programmed XOF makes Algorithm 32 return the supplied coefficient matrix on each successful
execution. It exhausts exactly when Algorithm 32 exhausts on the original prefixes. -/
theorem expandA_programMatrixPrefixes (H : Xofs) (s : Level) (rho : List Byte)
    (t : MatrixPrefixes s) (A : PublicMatrix s) :
    (H.withMatrixPrefixes s rho (programMatrixPrefixes s t A)).expandA s rho =
      ((H.withMatrixPrefixes s rho t).expandA s rho).map fun _ => A := by
  let entries (u : MatrixPrefixes s) (i : Fin s.params.k) (j : Fin s.params.ℓ) :=
    (rejNTTPoly (List.ofFn (u i j))).map fromNTT
  let rows (u : MatrixPrefixes s) (i : Fin s.params.k) := Vector.ofFnM (entries u i)
  let target (i : Fin s.params.k) := Vector.ofFn fun j : Fin s.params.ℓ => Vector.ofFn (A i j)
  have hr (i : Fin s.params.k) :
      rows (programMatrixPrefixes s t A) i = (rows t i).map fun _ => target i := by
    have he := funext (sample_programMatrixPrefixes s t A i)
    change Vector.ofFnM (entries (programMatrixPrefixes s t A) i) = _
    rw [show entries (programMatrixPrefixes s t A) i = _ from he]
    exact Vector.ofFnM_option_replace (entries t i) (fun j => Vector.ofFn (A i j))
  have hm : Vector.ofFnM (rows (programMatrixPrefixes s t A)) =
      (Vector.ofFnM (rows t)).map fun _ => Vector.ofFn target := by
    rw [funext hr, Vector.ofFnM_option_replace]
  let unpack (v : Vector (Vector (Vector (ZMod 8380417) 256) s.params.ℓ) s.params.k) :
      PublicMatrix s := fun i j => ((v.get i).get j).get
  have eval (u : MatrixPrefixes s) : (H.withMatrixPrefixes s rho u).expandA s rho =
      (Vector.ofFnM (rows u)).map unpack := by
    unfold Xofs.expandA
    simp only [read_matrixEntry, bind_pure_comp]
    rfl
  rw [eval, eval, hm]
  cases Vector.ofFnM (rows t) with
  | none => rfl
  | some _ =>
    apply congrArg some
    funext i j k
    simp only [unpack, target, Vector.get_ofFn]

/-- Joint law of the full shared XOF and the optional matrix output of FIPS 204 Algorithm 32,
for each public seed and each FIPS parameter set. Both experiments draw independent uniform
894-byte prefixes at the matrix addresses. The programmed experiment takes an independent
uniform lattice challenge in coefficient form and reports it when the original prefixes suffice. -/
theorem uniform_expandA_programMatrixPrefixes (H : Xofs) (s : Level) (rho : List Byte) :
    (PMF.uniformOfFintype (MatrixPrefixes s × PublicMatrix s)).map (fun (t, A) =>
      (H.withMatrixPrefixes s rho (programMatrixPrefixes s t A),
        ((H.withMatrixPrefixes s rho t).expandA s rho).map fun _ => A)) =
    (PMF.uniformOfFintype (MatrixPrefixes s)).map (fun t =>
      let G := H.withMatrixPrefixes s rho t
      (G, G.expandA s rho)) := by
  let c := (Equiv.refl (FixedBytes 894)).prodCongr fromNTTEquiv.symm
  let entry := (c.trans (exchangeRejNTT 894)).trans c.symm
  let split := Matrix.prodEquiv (Fin s.params.k) (Fin s.params.ℓ) (FixedBytes 894) Poly
  let e : Equiv.Perm (MatrixPrefixes s × PublicMatrix s) :=
    (split.symm.trans entry.mapMatrix).trans split
  conv_rhs => rw [← Probability.PMF.uniformOfFintype_prod_map_fst (β := PublicMatrix s),
    PMF.map_comp, ← Probability.PMF.uniformOfFintype_map_equiv e, PMF.map_comp]
  apply congrArg (fun f => (PMF.uniformOfFintype (MatrixPrefixes s × PublicMatrix s)).map f)
  funext ⟨t, A⟩
  have he : (e (t, A)).1 = programMatrixPrefixes s t A := by
    funext i j
    change (entry (t i j, A i j)).1 = _
    simp only [entry, c, programMatrixPrefixes, Equiv.trans_apply, Equiv.prodCongr_apply,
      Equiv.prodCongr_symm, Equiv.refl_symm, Equiv.refl_apply, Prod.map]
  simp only [Function.comp_apply, he, expandA_programMatrixPrefixes]

end Cslib.Crypto.MLDSA.FIPS204
