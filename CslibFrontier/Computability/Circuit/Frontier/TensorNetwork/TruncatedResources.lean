/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.TruncatedPolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Automation
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Envelope
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LinearSpaceArith
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListPrimitives
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeNatFrontends
import CslibFrontier.Tactic.EncLen

/-!
# Resources of the truncation-order reduction

The native machine `Cslib.Circuits.Frontier.engineCertificate` of
`CslibFrontier/Computability/Circuit/Frontier/TensorNetwork/TruncatedPolyTime.lean` runs the
reduction
of truncation order `ℓ` to contractions over `A_P = (ℤ / 2 ^ P)[U] / (f)`: it streams over the
`N = (ℓ - 1) k + 1` digit points, calling a given certificate of the contraction over `A_P` once per
point, and then interpolates. This file bounds its time and space by those of the calls.

**The loop** (`Cslib.Circuits.Frontier.engineCertificate_le`). If at every point the call takes
time at most `R`, space at most `Q`, and outputs at most `Yb` bits, then the machine takes time at
most `(N + 1) (K (n + Yb + 1) ^ K + R)` and space at most `K (n + Yb + 1) ^ K + Q`, for a constant
`K` and the encoded length `n` of the input. The live state is the binary index, the input and the
values so far (`Cslib.Circuits.Frontier.length_run_engineStep_le`), and `N ≤ n ^ 2 + 1`
(`Cslib.Circuits.Frontier.pointCount_le`).

**The calls.** The input of a call has length at most `9 (n + 1) ^ 2`
(`Cslib.Circuits.Frontier.length_encCore_coreInput_le`): the specialized network copies the
precision, the truncation order, the modulus and the point into every vertex.

**Specialized entries** (`Cslib.Circuits.Frontier.specEntryCertificate_le`). Evaluating a
specialized entry costs the original entry plus a polynomial in the lengths of the input and of the
original entry.

**Direct summation** (`Cslib.Circuits.Frontier.directCoreCertificate_le`,
`Cslib.Circuits.Frontier.truncDirectCertificate_le`). If the entry certificate takes time at most
`E` and space at most `ES` on the vertices of a network with `m` edges, direct summation over a
specialized network, and the truncated contraction by direct summation, take time
`K (n + ES + 1) ^ K 2 ^ m (E + 1)` and space `K (n + ES + 1) ^ K`.

## Main results

* `Cslib.Circuits.Frontier.engineCertificate_le`: time and space of the reduction.
* `Cslib.Circuits.Frontier.length_encCore_coreInput_le`: the size of a call.
* `Cslib.Circuits.Frontier.specEntryCertificate_le`: time and space of specialized entries.
* `Cslib.Circuits.Frontier.directCoreCertificate_le`,
  `Cslib.Circuits.Frontier.truncDirectCertificate_le`: time and space of direct summation.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Theorem D.1 (p. 53).
-/

public section

namespace Cslib.Circuits.Frontier

open Turing.MultiTapeTM Cslib.GenericRAM GaloisRingArith

variable {T : Type} {encT : T ↪ List Bool}

/-! ### Sizes -/

/-- The length of an input `(fl, P, ℓ, r, G)` of the reduction, by components. -/
theorem length_encEngine (fl : List ℕ) (P ℓ r : ℕ) (G : DescribedNetwork T) :
    (encEngine encT (fl, P, ℓ, r, G)).length = 2 * (encList encNat fl).length + 1 +
      (2 * P + 1 + (2 * ℓ + 1 +
        (2 * (encNat r).length + 1 + (DescribedNetwork.encDescribed encT G).length))) := by
  simp [encEngine, encTrunc]

/-- **The number of points is at most `n ^ 2 + 1`** for an input of length `n`: the truncation
order is in unary, and there are at most `n` vertices. -/
theorem pointCount_le (fl : List ℕ) (P ℓ r : ℕ) (G : DescribedNetwork T) :
    DescribedNetwork.pointCount ℓ G ≤
      (encEngine encT (fl, P, ℓ, r, G)).length * (encEngine encT (fl, P, ℓ, r, G)).length + 1 := by
  have hk := DescribedNetwork.length_numEdges_vertices_le (encT := encT) G
  have hlen := length_encEngine (encT := encT) fl P ℓ r G
  exact Nat.add_le_add_right (Nat.mul_le_mul (by omega) (by omega)) 1

/-- The length of an encoded described network, by components. -/
private theorem length_encDescribed {T' : Type} (encT' : T' ↪ List Bool)
    (G : DescribedNetwork T') :
    (DescribedNetwork.encDescribed encT' G).length =
      2 * G.numEdges + 1 + (encList (encPair (encList encNat) encT') G.vertices).length := by
  simp [DescribedNetwork.encDescribed, DescribedNetwork.equivProd]

/-- A binary-digit point has at most three bits per coordinate. -/
private theorem length_encList_digits_le (e k : ℕ) :
    (encList encNat (FastContraction.digits e k)).length ≤ 3 * e := by
  rw [length_encList]
  have h := List.sum_le_length_nsmul
    ((FastContraction.digits e k).map fun a => 2 * (encNat a).length + 1) 3 fun x hx => by
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hb
      have := length_encNat_le_self (if k.testBit i then 1 else 0)
      split_ifs at this ⊢ <;> omega
  simpa [FastContraction.digits, mul_comm] using h

/-- Copying the data `d` of a specialization into every vertex adds `2 |d|` bits per vertex, and
at most doubles the rest. -/
private theorem length_encList_spec_le (vs : List (List ℕ × T)) (d : ℕ × ℕ × List ℕ × List ℕ) :
    (encList (encPair (encList encNat) (encSpecDesc encT))
        (vs.map fun v => (v.1, (v.2, d)))).length ≤
      2 * (encList (encPair (encList encNat) encT) vs).length +
        vs.length * (2 * (encSpecData d).length) := by
  induction vs with
  | nil => simp
  | cons v vs ih =>
    enc_len [length_encList, List.map_cons, List.map_map, List.sum_cons, Function.comp_def,
      add_one_mul] at ih ⊢

/-- **The size of a call.** The input of the contraction at a digit point is at most
`9 (n + 1) ^ 2` bits for an input of the reduction of length `n`: the specialized network copies
the precision, the truncation order, the modulus and the point, at most `3 n` bits, into each of
at most `n` vertices. -/
theorem length_encCore_coreInput_le (y : List ℕ × ℕ × ℕ × ℕ × DescribedNetwork T) (k : ℕ) :
    (encCore encT (coreInput y k)).length ≤ 9 * ((encEngine encT y).length + 1) ^ 2 := by
  obtain ⟨fl, P, ℓ, r, G⟩ := y
  have hlen := length_encEngine (encT := encT) fl P ℓ r G
  have hG := length_encDescribed encT G
  have hk := DescribedNetwork.length_numEdges_vertices_le (encT := encT) G
  have hζ := length_encList_digits_le fl.length k
  have hfl := length_le_length_encList encNat fl
  have hspec := length_encList_spec_le (encT := encT) G.vertices
    (P, ℓ, fl, FastContraction.digits fl.length k)
  set L := (encEngine encT (fl, P, ℓ, r, G)).length
  have hd : (encSpecData (P, ℓ, fl, FastContraction.digits fl.length k)).length ≤ 3 * L := by
    enc_len at hlen ⊢
  have hkL : G.vertices.length ≤ L := by omega
  have hmul : G.vertices.length *
      (2 * (encSpecData (P, ℓ, fl, FastContraction.digits fl.length k)).length) ≤ L * (6 * L) :=
    Nat.mul_le_mul hkL (by omega)
  simp only [coreInput, encCore, length_encPair, encUnary_apply, List.length_replicate,
    length_encDescribed, DescribedNetwork.numEdges_specNet, DescribedNetwork.vertices_specNet]
    at hspec hmul ⊢
  linarith [Nat.zero_le (L * L)]

variable (core : ℕ × List ℕ × ℕ × DescribedNetwork (SpecDesc T) → List ℕ)

/-- **The live state of the loop.** After `j` rounds, if each of the first `j` values is at most
`Yb` bits, the state is at most `2 |j| + 2 n + 2 + j (2 Yb + 1)` bits, for the binary length `|j|`
of `j` and the length `n` of the input. -/
theorem length_run_engineStep_le (y : List ℕ × ℕ × ℕ × ℕ × DescribedNetwork T) {j Yb : ℕ}
    (hY : ∀ k < j, (encList encNat (core (coreInput y k))).length ≤ Yb) :
    (encEngineState encT (IndexFold.run (engineStep core) j (y, []))).length ≤
      2 * (encNat j).length + 2 * (encEngine encT y).length + 2 + j * (2 * Yb + 1) := by
  rw [run_engineStep]
  have h := Turing.MultiTapeTM.length_encList_le (encList encNat)
    ((List.range j).map fun k => core (coreInput y k)) (b := Yb) fun v hv => by
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hv
      exact hY k (List.mem_range.mp hk)
  simp only [List.length_map, List.length_range] at h
  enc_len

/-! ### The loop -/

/-- **Time and space of the reduction.** There is `K` such that, on an input `(fl, P, ℓ, r, G)` of
length `n` with `N = (ℓ - 1) k + 1` points, if at each of the indices `0, …, N` the call takes time
at most `R` and space at most `Q` and outputs at most `Yb` bits, the reduction takes time at most
`(N + 1) (K (n + Yb + 1) ^ K + R)` and space at most `K (n + Yb + 1) ^ K + Q`. (The loop charges
one more round than it runs, at the index `N`.) -/
theorem engineCertificate_le (cc : NativeCertificate core (encCore encT) (encList encNat)) :
    ∃ K : ℕ, ∀ (fl : List ℕ) (P ℓ r : ℕ) (G : DescribedNetwork T) (R Q Yb : ℕ),
      (∀ k ≤ DescribedNetwork.pointCount ℓ G,
        cc.time (coreInput (fl, P, ℓ, r, G) k) ≤ R ∧ cc.space (coreInput (fl, P, ℓ, r, G) k) ≤ Q ∧
          (encList encNat (core (coreInput (fl, P, ℓ, r, G) k))).length ≤ Yb) →
      (engineCertificate core cc).time (fl, P, ℓ, r, G) ≤
          (DescribedNetwork.pointCount ℓ G + 1) *
            (K * ((encEngine encT (fl, P, ℓ, r, G)).length + Yb + 1) ^ K + R) ∧
        (engineCertificate core cc).space (fl, P, ℓ, r, G) ≤
          K * ((encEngine encT (fl, P, ℓ, r, G)).length + Yb + 1) ^ K + Q := by
  -- The polynomial-time pieces.
  have hcN : ComputableInPolyTime
      (fun ((_, _, ℓ, _, G) : List ℕ × ℕ × ℕ × ℕ × DescribedNetwork T) =>
        DescribedNetwork.pointCount ℓ G) (encEngine encT) encNat :=
    ComputableInPolyTime.unary_to_binary.comp pointCount_polyTime
  have hcI : ComputableInPolyTime
      (fun y : List ℕ × ℕ × ℕ × ℕ × DescribedNetwork T => (y, ([] : List (List ℕ))))
      (encEngine encT) (encPair (encEngine encT) (encList (encList encNat))) :=
    ComputableInPolyTime.id'.prod (ComputableInPolyTime.const [])
  have hcA : ComputableInPolyTime
      (fun p : ℕ × ((List ℕ × ℕ × ℕ × ℕ × DescribedNetwork T) × List (List ℕ)) => p.2.1)
      (encEngineState encT) (encEngine encT) :=
    (ComputableInPolyTime.fst _ _).comp (ComputableInPolyTime.snd _ _)
  have hcC : ComputableInPolyTime
      (fun p : ℕ × ((List ℕ × ℕ × ℕ × ℕ × DescribedNetwork T) × List (List ℕ)) => p.2.2)
      (encEngineState encT) (encList (encList encNat)) :=
    (ComputableInPolyTime.snd _ _).comp (ComputableInPolyTime.snd _ _)
  have hcB := ComputableInPolyTime.snoc (encList encNat)
  obtain ⟨pN, hpN, mN, bN⟩ := exists_mono_poly_cert hcN
  obtain ⟨pI, hpI, mI, bI⟩ := exists_mono_poly_cert hcI
  obtain ⟨pA, hpA, mA, bA⟩ := exists_mono_poly_cert hcA
  obtain ⟨pC, hpC, mC, bC⟩ := exists_mono_poly_cert hcC
  obtain ⟨pB, hpB, mB, bB⟩ := exists_mono_poly_cert hcB
  obtain ⟨pD, hpD, mD, bD⟩ := exists_mono_poly_cert (coreInput_polyTime (encT := encT))
  obtain ⟨pR, hpR, mR, bR⟩ := exists_mono_poly_cert (engineRecover_polyTime (encT := encT))
  -- The overhead, as a polynomial in `X = n + Yb`.
  let Sh : ℕ → ℕ := fun X => 2 * (X + 1) ^ 2 + 2 * X + 2 + (X + 1) ^ 2 * (2 * X + 1)
  let U : ℕ → ℕ := fun X => pN X + X + pI X + 3 * Sh X + 3 * ((X + 1) ^ 2 + 1) ^ 2 +
    pA (Sh X) + pC (Sh X) + pD (Sh X) + pB (2 * Sh X + 1 + X) + pR (Sh X)
  have hU : PolyBounded id U := by growth_poly
  obtain ⟨K, hK⟩ := hU.exists_le_succ_pow
  refine ⟨K, fun fl P ℓ r G R Q Yb hcore => ?_⟩
  set y : List ℕ × ℕ × ℕ × ℕ × DescribedNetwork T := (fl, P, ℓ, r, G) with hy
  set L := (encEngine encT y).length with hL
  set N := DescribedNetwork.pointCount ℓ G with hN
  set X := L + Yb with hX
  have hUX : U X ≤ K * (X + 1) ^ K := hK _ le_rfl X
  -- Sizes of the states.
  have hNL : N ≤ L * L + 1 := pointCount_le fl P ℓ r G
  have hNX : N ≤ (X + 1) ^ 2 := by
    have : L * L ≤ X * X := Nat.mul_le_mul (by omega) (by omega)
    linarith
  let S := 2 * N + 2 * L + 2 + N * (2 * Yb + 1)
  have hSSh : S ≤ Sh X := by simp only [S, Sh]; gcongr <;> omega
  have hstate (j : ℕ) (hj : j ≤ N) :
      (encEngineState encT (IndexFold.run (engineStep core) j (y, []))).length ≤ S := by
    have h := length_run_engineStep_le (encT := encT) core y (j := j) (Yb := Yb)
      fun k hk => (hcore k (by omega)).2.2
    have hj' : (encNat j).length ≤ N := (length_encNat_mono hj).trans (length_encNat_le_self N)
    have hjN : j * (2 * Yb + 1) ≤ N * (2 * Yb + 1) := Nat.mul_le_mul_right _ hj
    omega
  -- The values so far, then the snoc input, are bounded by the state.
  have hsnoc (j : ℕ) (hj : j ≤ N) :
      (encPair (encList (encList encNat)) (encList encNat)
        ((IndexFold.run (engineStep core) j (y, [])).2.2,
          core (coreInput (IndexFold.run (engineStep core) j (y, [])).2.1
            (IndexFold.run (engineStep core) j (y, [])).1))).length ≤ 2 * S + 1 + Yb := by
    have hs := hstate j hj
    have hY := (hcore j hj).2.2
    rw [run_engineStep] at hs ⊢
    enc_len at hs ⊢
  set P4 := pA (Sh X) + pC (Sh X) + pD (Sh X) + pB (2 * Sh X + 1 + X)
  have hround (j : ℕ) (hj : j ≤ N) :
      (IndexFold.roundCertificate (engineStepCertificate core cc)).time
          (IndexFold.run (engineStep core) j (y, [])) ≤ S + (N + 1) ^ 2 + P4 + R ∧
        (IndexFold.roundCertificate (engineStepCertificate core cc)).space
          (IndexFold.run (engineStep core) j (y, [])) ≤ S + (N + 1) + P4 + Q := by
    have hs := hstate j hj
    have hB := mB ((hsnoc j hj).trans (by omega : 2 * S + 1 + Yb ≤ 2 * Sh X + 1 + X))
    have hA := mA (hs.trans hSSh)
    have hC := mC (hs.trans hSSh)
    have hD := mD (hs.trans hSSh)
    simp only [IndexFold.roundCertificate, engineStepCertificate, NativeCertificate.comp_time,
      NativeCertificate.prod_time, NativeCertificate.comp_space, NativeCertificate.prod_space]
    have h1 := (bA (IndexFold.run (engineStep core) j (y, []))).imp (·.trans hA) (·.trans hA)
    have h2 := (bC (IndexFold.run (engineStep core) j (y, []))).imp (·.trans hC) (·.trans hC)
    have h3 := (bD (IndexFold.run (engineStep core) j (y, []))).imp (·.trans hD) (·.trans hD)
    have h4 := (bB _).imp (·.trans hB) (·.trans hB)
    have hidx : (encNat (IndexFold.run (engineStep core) j (y, [])).1).length ≤ N := by
      rw [IndexFold.run_index]
      exact (length_encNat_mono hj).trans (length_encNat_le_self N)
    have hsq := Nat.pow_le_pow_left (Nat.add_le_add_right hidx 1) 2
    obtain ⟨hR, hQ, -⟩ := hcore j hj
    rw [run_engineStep] at h1 h2 h3 h4 hs hidx hsq ⊢
    simp only [Function.comp_apply, encEngineState] at h1 h2 h3 h4 hs hidx hsq ⊢
    constructor <;> omega
  -- The trajectory maxima.
  have hmaxT : NativeCertificate.maxRoundTime
      (IndexFold.roundCertificate (engineStepCertificate core cc)) N (0, y, []) ≤
        S + (N + 1) ^ 2 + P4 + R :=
    NativeCertificate.maxRoundTime_le _ _ _ fun j hj => (hround j hj).1
  have hmaxS : NativeCertificate.maxRoundSpace
      (IndexFold.roundCertificate (engineStepCertificate core cc)) N (0, y, []) ≤
        S + (N + 1) + P4 + Q :=
    NativeCertificate.maxRoundSpace_le _ _ _ fun j hj => (hround j hj).2
  have hmaxL : NativeCertificate.maxStateLength (encEngineState encT)
      (IndexFold.step (engineStep core)) N (0, y, []) ≤ S :=
    NativeCertificate.maxStateLength_le _ _ _ _ fun j hj => hstate j hj
  dsimp only [encEngineState] at hmaxL
  -- The pieces outside the loop.
  have hLX : L ≤ X := by omega
  have hN' := (bN y).imp (·.trans (mN hLX)) (·.trans (mN hLX))
  have hI' := (bI y).imp (·.trans (mI hLX)) (·.trans (mI hLX))
  have hRm := mR ((hstate N le_rfl).trans hSSh)
  have hR' := (bR (IndexFold.run (engineStep core) N (y, []))).imp (·.trans hRm) (·.trans hRm)
  have hNlen : (encNat N).length ≤ N := length_encNat_le_self N
  have hsq : ((encNat N).length + 1) ^ 2 ≤ (N + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hNsq : (N + 1) ^ 2 ≤ ((X + 1) ^ 2 + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hN1 : N ≤ (N + 1) ^ 2 := (Nat.le_add_right N 1).trans (Nat.le_self_pow (by norm_num) _)
  refine ⟨?_, ?_⟩
  · rw [engineCertificate, NativeCertificate.congr_time, NativeCertificate.comp_time,
      IndexFold.certificate, NativeCertificate.iterate_time]
    simp only [NativeCertificate.prod_time, NativeCertificate.const_time, Function.comp_apply]
    rw [← hN, ← hL]
    set A := pN X + X + pI X + pR (Sh X)
    have hA : A ≤ (N + 1) * A := Nat.le_mul_of_pos_left _ (by omega)
    have hB := Nat.mul_le_mul_left (N + 1) (Nat.add_le_add (Nat.add_le_add hmaxT hmaxL) hsq)
    have hC := Nat.mul_le_mul_left (N + 1)
      (show A + (S + (N + 1) ^ 2 + P4 + R + S + (N + 1) ^ 2) ≤ K * (X + 1) ^ K + R by
        simp only [U] at hUX
        omega)
    rw [Nat.mul_add] at hC
    omega
  · rw [engineCertificate, NativeCertificate.congr_space, NativeCertificate.comp_space,
      IndexFold.certificate, NativeCertificate.iterate_space]
    simp only [NativeCertificate.prod_space, NativeCertificate.const_space, Function.comp_apply]
    rw [← hN, ← hL]
    simp only [U] at hUX
    omega

/-! ### Specialized entries -/

/-- **Time and space of specialized entries.** There is `K` such that, for every entry
certificate `ce`, evaluating the specialized entry at `((t, P, ℓ, fl, ζ), bs)` costs the original
entry at `(t, bs)` plus `K (n + e + 1) ^ K`, in time and in space, for the length `n` of the input
and the length `e` of the original entry. -/
theorem specEntryCertificate_le :
    ∃ K : ℕ, ∀ (entry : T → List Bool → List ℕ)
      (ce : NativeCertificate (fun q : T × List Bool => entry q.1 q.2) (encPair encT encBits)
        (encList encNat)) (t : T) (P ℓ : ℕ) (fl ζ : List ℕ) (bs : List Bool),
      (specEntryCertificate entry ce).time ((t, P, ℓ, fl, ζ), bs) ≤ ce.time (t, bs) +
          K * ((encPair (encSpecDesc encT) encBits ((t, P, ℓ, fl, ζ), bs)).length +
            (encList encNat (entry t bs)).length + 1) ^ K ∧
        (specEntryCertificate entry ce).space ((t, P, ℓ, fl, ζ), bs) ≤ ce.space (t, bs) +
          K * ((encPair (encSpecDesc encT) encBits ((t, P, ℓ, fl, ζ), bs)).length +
            (encList encNat (entry t bs)).length + 1) ^ K := by
  have hcD : ComputableInPolyTime (fun q : SpecDesc T × List Bool => q.1.2)
      (encPair (encSpecDesc encT) encBits) encSpecData :=
    (ComputableInPolyTime.snd _ _).comp (ComputableInPolyTime.fst _ _)
  have hcE : ComputableInPolyTime (fun q : SpecDesc T × List Bool => (q.1.1, q.2))
      (encPair (encSpecDesc encT) encBits) (encPair encT encBits) :=
    ((ComputableInPolyTime.fst _ _).comp (ComputableInPolyTime.fst _ _)).prod
      (ComputableInPolyTime.snd _ _)
  obtain ⟨pD, hpD, mD, bD⟩ := exists_mono_poly_cert hcD
  obtain ⟨pE, hpE, mE, bE⟩ := exists_mono_poly_cert hcE
  obtain ⟨pH, hpH, mH, bH⟩ := exists_mono_poly_cert horner_polyTime
  let U : ℕ → ℕ := fun Z => pD Z + pE Z + pH (2 * Z + 1)
  have hU : PolyBounded id U := by growth_poly
  obtain ⟨K, hK⟩ := hU.exists_le_succ_pow
  refine ⟨K, fun entry ce t P ℓ fl ζ bs => ?_⟩
  set n := (encPair (encSpecDesc encT) encBits ((t, P, ℓ, fl, ζ), bs)).length with hn
  set Z := n + (encList encNat (entry t bs)).length with hZ
  have hUZ : U Z ≤ K * (Z + 1) ^ K := hK _ le_rfl Z
  have hnZ : n ≤ Z := by omega
  have hH : (encPair encSpecData (encList encNat) ((P, ℓ, fl, ζ), entry t bs)).length ≤
      2 * Z + 1 := by
    have : (encSpecData (P, ℓ, fl, ζ)).length ≤ n := by enc_len [hn]
    enc_len at this ⊢
  simp only [U] at hUZ
  have hD := (bD ((t, P, ℓ, fl, ζ), bs)).imp (·.trans (mD hnZ)) (·.trans (mD hnZ))
  have hE := (bE ((t, P, ℓ, fl, ζ), bs)).imp (·.trans (mE hnZ)) (·.trans (mE hnZ))
  have hH' := (bH ((P, ℓ, fl, ζ), entry t bs)).imp (·.trans (mH hH)) (·.trans (mH hH))
  refine ⟨?_, ?_⟩
  · simp only [specEntryCertificate, NativeCertificate.congr, NativeCertificate.comp_time,
      NativeCertificate.prod_time, Function.comp_apply]
    omega
  · simp only [specEntryCertificate, NativeCertificate.congr, NativeCertificate.comp_space,
      NativeCertificate.prod_space, Function.comp_apply]
    omega

/-! ### Direct summation -/

/-- A vertex is no longer than its network. -/
private theorem length_vertex_le {T' : Type} (encT' : T' ↪ List Bool) (G : DescribedNetwork T')
    {v : List ℕ × T'} (hv : v ∈ G.vertices) :
    (encPair (encList encNat) encT' v).length ≤ (DescribedNetwork.encDescribed encT' G).length := by
  have h1 := List.le_sum_of_mem
    (List.mem_map_of_mem (f := fun a => (encPair (encList encNat) encT' a).length) hv)
  have h2 := sum_length_le_length_encList (encPair (encList encNat) encT') G.vertices
  rw [length_encDescribed]
  omega

/-- `a + X (b + c E) ≤ T X (E + 1)` when `a + b ≤ T`, `c ≤ T` and `1 ≤ X`: the time of a set-up
step `a` followed by `X` rounds of cost `b + c E`. -/
private theorem add_mul_le_mul_mul {X E a b c T : ℕ} (hX : 1 ≤ X) (hab : a + b ≤ T)
    (hc : c ≤ T) : a + X * (b + c * E) ≤ T * X * (E + 1) := by
  have h1 : a ≤ X * a := Nat.le_mul_of_pos_left a hX
  have h2 : X * (a + b) ≤ X * T := Nat.mul_le_mul_left _ hab
  have h3 : X * (c * E) ≤ X * (T * E) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hc)
  have e : T * X * (E + 1) = X * (T * E) + X * T := by ring
  rw [e, Nat.mul_add]
  rw [Nat.mul_add] at h2
  omega

/-- **Time and space of direct summation over a specialized network.** There is `K` such that,
at the input `x = (P, fl, r, G')` for the network `G'` specialized at a point, of length `n`, if
the entry certificate takes time at most `E` and space at most `ES` at every vertex of the original
network `G` with `m` edges and every list of bits on its ports, then direct summation takes time
at most `K (n + ES + 1) ^ K 2 ^ m (E + 1)` and space at most `K (n + ES + 1) ^ K`. -/
theorem directCoreCertificate_le (entry : T → List Bool → List ℕ)
    (ce : NativeCertificate (fun q : T × List Bool => entry q.1 q.2) (encPair encT encBits)
      (encList encNat)) :
    ∃ K : ℕ, ∀ (P ℓ r : ℕ) (fl ζ : List ℕ) (G : DescribedNetwork T) (E ES : ℕ),
      (∀ v ∈ G.vertices, ∀ bs : List Bool, bs.length = v.1.length →
        ce.time (v.2, bs) ≤ E ∧ ce.space (v.2, bs) ≤ ES) →
      (directCoreCertificate entry ce).time (P, fl, r, DescribedNetwork.specNet P ℓ fl ζ G) ≤
          K * ((encCore encT (P, fl, r, DescribedNetwork.specNet P ℓ fl ζ G)).length + ES + 1) ^ K *
            2 ^ G.numEdges * (E + 1) ∧
        (directCoreCertificate entry ce).space (P, fl, r, DescribedNetwork.specNet P ℓ fl ζ G) ≤
          K * ((encCore encT (P, fl, r, DescribedNetwork.specNet P ℓ fl ζ G)).length + ES + 1) ^
            K := by
  obtain ⟨cE, -, hcE⟩ := ce.computes
  obtain ⟨K₃, hK₃⟩ := specEntryCertificate_le (encT := encT)
  obtain ⟨cS, -, hcS⟩ := (specEntryCertificate entry ce).computes
  obtain ⟨K₂, hK₂⟩ := DescribedNetwork.contractionCertificate_le (eval := specEntry entry)
    SumOps.galois_polyTime (specEntryCertificate entry ce)
  have hcR : ComputableInPolyTime
      (fun ((P, fl, _, G') : ℕ × List ℕ × ℕ × DescribedNetwork (SpecDesc T)) => ((P, fl), G'))
      (encCore encT)
      (DescribedNetwork.encInput (encPair encUnary (encList encNat)) (encSpecDesc encT)) :=
    ((ComputableInPolyTime.fst _ _).prod
      ((ComputableInPolyTime.fst _ _).comp (ComputableInPolyTime.snd _ _))).prod
      ((ComputableInPolyTime.snd _ _).comp ((ComputableInPolyTime.snd _ _).comp
        (ComputableInPolyTime.snd _ _)))
  obtain ⟨pS, hpS, mS, bS⟩ := exists_mono_poly_cert hcR
  -- The overheads, as polynomials in `Z = n + ES`.
  let Af : ℕ → ℕ := fun Z => 3 * Z + 1 + cE * (Z + 1) + 1
  let Uf : ℕ → ℕ := fun Z => K₃ * Af Z ^ K₃
  let Bf : ℕ → ℕ := fun Z =>
    K₂ * (2 * Z + 1 + cS * (Z + Uf Z + 1) + Z * (2 * Z + 3) + 1) ^ K₂
  let Tf : ℕ → ℕ := fun Z => pS Z + (Z + 2) * (Bf Z + 2 * Uf Z) + (Z + 2) * 2
  let Sf : ℕ → ℕ := fun Z => pS Z + Bf Z + (Z + Uf Z)
  have hTSp : PolyBounded id fun Z => Tf Z + Sf Z := by growth_poly
  obtain ⟨K, hK⟩ := hTSp.exists_le_succ_pow
  refine ⟨K, fun P ℓ r fl ζ G E ES hE => ?_⟩
  set G' := DescribedNetwork.specNet P ℓ fl ζ G with hG'
  set n := (encCore encT (P, fl, r, G')).length with hn
  set Z := n + ES with hZ
  set X := 2 ^ G.numEdges with hX
  have hX1 : 1 ≤ X := Nat.one_le_two_pow
  have hG'n : (DescribedNetwork.encDescribed (encSpecDesc encT) G').length ≤ n := by
    enc_len [hn, encCore]
  -- The specialized entries.
  have hv (v') (hv' : v' ∈ G'.vertices) (bs : List Bool) (hbs : bs.length = v'.1.length) :
      (specEntryCertificate entry ce).time (v'.2, bs) ≤ E + Uf Z ∧
        (specEntryCertificate entry ce).space (v'.2, bs) ≤ ES + Uf Z ∧
          (encList encNat (specEntry entry v'.2 bs)).length ≤ cS * (Z + Uf Z + 1) := by
    have hvl := length_vertex_le (encSpecDesc encT) G' hv'
    rw [hG', DescribedNetwork.vertices_specNet, List.mem_map] at hv'
    obtain ⟨v, hvG, rfl⟩ := hv'
    simp only at hbs ⊢
    obtain ⟨hEt, hEs⟩ := hE v hvG bs hbs
    have hent : (encList encNat (entry v.2 bs)).length ≤ cE * (ES + 1) :=
      (hcE (v.2, bs)).trans (Nat.mul_le_mul_left _ (by omega))
    obtain ⟨h1, h2⟩ := hK₃ entry ce v.2 P ℓ fl ζ bs
    have hq : (encPair (encSpecDesc encT) encBits ((v.2, P, ℓ, fl, ζ), bs)).length +
        (encList encNat (entry v.2 bs)).length + 1 ≤ Af Z := by
      have hports := length_le_length_encList encNat v.1
      have hcE' : cE * (ES + 1) ≤ cE * (Z + 1) := Nat.mul_le_mul_left _ (by omega)
      simp only [length_encPair, encBits_apply, Af] at hvl ⊢
      omega
    have hpow : K₃ * ((encPair (encSpecDesc encT) encBits ((v.2, P, ℓ, fl, ζ), bs)).length +
        (encList encNat (entry v.2 bs)).length + 1) ^ K₃ ≤ Uf Z :=
      Nat.mul_le_mul_left K₃ (Nat.pow_le_pow_left hq K₃)
    exact ⟨h1.trans (Nat.add_le_add hEt hpow), h2.trans (Nat.add_le_add hEs hpow),
      (hcS ((v.2, P, ℓ, fl, ζ), bs)).trans (Nat.mul_le_mul_left _ (by omega))⟩
  have hr : ∀ z, SumOps.galois.Reduced (P, fl) z → (encList encNat z).length ≤ Z * (2 * Z + 3) :=
    fun z hz => (SumOps.length_encList_le_of_galois_reduced hz).trans (by
      have hfl := length_le_length_encList encNat fl
      have hlen : (encList encNat fl).length + P ≤ n := by enc_len [hn, encCore]
      dsimp only
      exact Nat.mul_le_mul (by omega) (by omega))
  obtain ⟨hT, hS⟩ := hK₂ ((P, fl), G') (E + Uf Z) (ES + Uf Z) (cS * (Z + Uf Z + 1))
    (Z * (2 * Z + 3)) hv hr
  have hin : (DescribedNetwork.encInput (encPair encUnary (encList encNat)) (encSpecDesc encT)
      ((P, fl), G')).length ≤ 2 * Z + 1 := by
    have : (DescribedNetwork.encInput (encPair encUnary (encList encNat)) (encSpecDesc encT)
        ((P, fl), G')).length ≤ 2 * n + 1 := by enc_len [hn, DescribedNetwork.encInput, encCore]
    omega
  have hB : K₂ * ((DescribedNetwork.encInput (encPair encUnary (encList encNat))
      (encSpecDesc encT) ((P, fl), G')).length + cS * (Z + Uf Z + 1) + Z * (2 * Z + 3) + 1) ^ K₂ ≤
      Bf Z := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  have hk : G'.vertices.length ≤ Z := by
    have := DescribedNetwork.length_numEdges_vertices_le (encT := encSpecDesc encT) G'
    omega
  rw [DescribedNetwork.numEdges_specNet] at hT
  have hfac : X * (G'.vertices.length + 1) + 1 ≤ X * (Z + 2) := by
    have := Nat.mul_le_mul_left X (show G'.vertices.length + 1 ≤ Z + 1 by omega)
    have e : X * (Z + 2) = X * (Z + 1) + X := by ring
    omega
  have hT' := hT.trans (Nat.mul_le_mul hfac (Nat.add_le_add_right hB _))
  have hnZ : n ≤ Z := by omega
  have hR := (bS (P, fl, r, G')).imp (·.trans (mS hnZ)) (·.trans (mS hnZ))
  have h1 : Tf Z + Sf Z ≤ K * (Z + 1) ^ K := hK _ le_rfl Z
  refine ⟨?_, ?_⟩
  · simp only [directCoreCertificate, NativeCertificate.congr, NativeCertificate.comp_time,
      Function.comp_apply]
    -- `pS Z + X (Z + 2) (B + 2 (E + U)) ≤ T X (E + 1)`.
    have e : X * (Z + 2) * (Bf Z + 2 * (E + Uf Z)) =
        X * ((Z + 2) * (Bf Z + 2 * Uf Z) + (Z + 2) * 2 * E) := by ring
    have hTf : Tf Z ≤ K * (Z + 1) ^ K := by omega
    have := add_mul_le_mul_mul (b := (Z + 2) * (Bf Z + 2 * Uf Z)) (c := (Z + 2) * 2) (E := E) hX1
      ((Nat.le_add_right _ _).trans hTf) ((Nat.le_add_left _ _).trans hTf)
    have hpS : (NativeCertificate.ofPolyTime hcR).time (P, fl, r, G') ≤ pS Z := hR.1
    omega
  · simp only [directCoreCertificate, NativeCertificate.congr, NativeCertificate.comp_space,
      Function.comp_apply]
    simp only [Sf] at h1
    omega

/-- **Time and space of the truncated contraction by direct summation.** There is `K` such that,
on an input `(P, ℓ, r, G)` of length `n` with `m` edges, if the entry certificate takes time at
most `E` and space at most `ES` at every vertex and every list of bits on its ports, then
`truncDirectCertificate` takes time at most `K (n + ES + 1) ^ K 2 ^ m (E + 1)` and space at most
`K (n + ES + 1) ^ K`. -/
theorem truncDirectCertificate_le (entry : T → List Bool → List ℕ)
    (ce : NativeCertificate (fun q : T × List Bool => entry q.1 q.2) (encPair encT encBits)
      (encList encNat)) :
    ∃ K : ℕ, ∀ (P ℓ r : ℕ) (G : DescribedNetwork T) (E ES : ℕ),
      (∀ v ∈ G.vertices, ∀ bs : List Bool, bs.length = v.1.length →
        ce.time (v.2, bs) ≤ E ∧ ce.space (v.2, bs) ≤ ES) →
      (truncDirectCertificate entry ce).time (P, ℓ, r, G) ≤
          K * ((encTrunc encT (P, ℓ, r, G)).length + ES + 1) ^ K * 2 ^ G.numEdges * (E + 1) ∧
        (truncDirectCertificate entry ce).space (P, ℓ, r, G) ≤
          K * ((encTrunc encT (P, ℓ, r, G)).length + ES + 1) ^ K := by
  obtain ⟨KA, hKA⟩ := directCoreCertificate_le entry ce
  obtain ⟨cD, -, hcD⟩ := (directCoreCertificate entry ce).computes
  obtain ⟨K₁, hK₁⟩ := engineCertificate_le (encT := encT) _ (directCoreCertificate entry ce)
  obtain ⟨pM, hpM, mM, bM⟩ := exists_mono_poly_cert (modulusChoice_polyTime (encT := encT))
  obtain ⟨cY, dY, hY⟩ := (modulusChoice_polyTime (encT := encT)).polyBounded_length.exists_le
  -- The overheads, as polynomials in `W = n + ES`.
  let Yf : ℕ → ℕ := fun W => cY * (W + 1) ^ dY
  let Rf : ℕ → ℕ := fun W => KA * (9 * (Yf W + 1) ^ 2 + W + 1) ^ KA
  let Engf : ℕ → ℕ := fun W => K₁ * (Yf W + cD * (Rf W + 1) + 1) ^ K₁
  let Tf : ℕ → ℕ := fun W =>
    pM W + (Yf W * Yf W + 2) * Engf W + (Yf W * Yf W + 2) * Rf W
  let Sf : ℕ → ℕ := fun W => pM W + (Engf W + Rf W)
  have hTSp : PolyBounded id fun W => Tf W + Sf W := by growth_poly
  obtain ⟨K, hK⟩ := hTSp.exists_le_succ_pow
  refine ⟨K, fun P ℓ r G E ES hE => ?_⟩
  set n := (encTrunc encT (P, ℓ, r, G)).length with hn
  set W := n + ES with hW
  set X := 2 ^ G.numEdges with hX
  have hX1 : 1 ≤ X := Nat.one_le_two_pow
  set fl := FastContraction.modulus (DescribedNetwork.pointCount ℓ G) with hfl
  have hLy : (encEngine encT (fl, P, ℓ, r, G)).length ≤ Yf W := (hY (P, ℓ, r, G)).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
  have hNy : DescribedNetwork.pointCount ℓ G + 1 ≤ Yf W * Yf W + 2 := by
    have h1 := pointCount_le (encT := encT) fl P ℓ r G
    have h2 := Nat.mul_le_mul hLy hLy
    omega
  -- The calls of the loop, stated in the shape `engineCertificate_le` expects.
  obtain ⟨hTe, hSe⟩ := hK₁ fl P ℓ r G (Rf W * X * (E + 1)) (Rf W) (cD * (Rf W + 1)) <| by
    intro k _
    have hc := length_encCore_coreInput_le (encT := encT) (fl, P, ℓ, r, G) k
    have hci : coreInput (fl, P, ℓ, r, G) k =
        (P, fl, r, DescribedNetwork.specNet P ℓ fl (FastContraction.digits fl.length k) G) := rfl
    rw [hci] at hc ⊢
    obtain ⟨hT, hS⟩ := hKA P ℓ r fl (FastContraction.digits fl.length k) G E ES hE
    have hR : KA * ((encCore encT (P, fl, r, DescribedNetwork.specNet P ℓ fl
        (FastContraction.digits fl.length k) G)).length + ES + 1) ^ KA ≤ Rf W := by
      refine Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ _)
      linarith [Nat.mul_le_mul_left 9 (Nat.pow_le_pow_left (Nat.add_le_add_right hLy 1) 2)]
    have hS' := hS.trans hR
    exact ⟨hT.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hR)), hS',
      (hcD (P, fl, r, DescribedNetwork.specNet P ℓ fl
        (FastContraction.digits fl.length k) G)).trans
        (Nat.mul_le_mul_left _ (Nat.add_le_add_right hS' 1))⟩
  have hEng : K₁ * ((encEngine encT (fl, P, ℓ, r, G)).length + cD * (Rf W + 1) + 1) ^ K₁ ≤
      Engf W := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  have hnW : n ≤ W := by omega
  have hM := (bM (P, ℓ, r, G)).imp (·.trans (mM hnW)) (·.trans (mM hnW))
  have h1 : Tf W + Sf W ≤ K * (W + 1) ^ K := hK _ le_rfl W
  refine ⟨?_, ?_⟩
  · simp only [truncDirectCertificate, NativeCertificate.congr, NativeCertificate.comp_time]
    have hTe' := hTe.trans (Nat.mul_le_mul hNy (Nat.add_le_add_right hEng _))
    have e : (Yf W * Yf W + 2) * (Engf W + Rf W * X * (E + 1)) = (Yf W * Yf W + 2) * Engf W +
        X * ((Yf W * Yf W + 2) * Rf W + (Yf W * Yf W + 2) * Rf W * E) := by ring
    have hTf : Tf W ≤ K * (W + 1) ^ K := by omega
    have := add_mul_le_mul_mul (b := (Yf W * Yf W + 2) * Rf W) (E := E) hX1 hTf
      ((Nat.le_add_left _ _).trans hTf)
    change (NativeCertificate.ofPolyTime modulusChoice_polyTime).time (P, ℓ, r, G) +
      (engineCertificate _ (directCoreCertificate entry ce)).time (fl, P, ℓ, r, G) ≤ _
    omega
  · simp only [truncDirectCertificate, NativeCertificate.congr, NativeCertificate.comp_space]
    change (NativeCertificate.ofPolyTime modulusChoice_polyTime).space (P, ℓ, r, G) +
      (engineCertificate _ (directCoreCertificate entry ce)).space (fl, P, ℓ, r, G) ≤ _
    simp only [Sf] at h1
    omega

end Cslib.Circuits.Frontier
