/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.MLDSA.PublicKeyHash
public import CslibFrontier.Crypto.Computational.MLDSA.QuantumSigning
import CslibFrontier.Probability.PMF.Bind

/-!
# Representative and commitment address overlap in the signed ML-DSA game

[FIPS 204][NISTFIPS204], Algorithms 7 and 8, use the public-key hash as the first 512 bits
of a representative input and the message representative as the first 512 bits of a
commitment input. Both roles use SHAKE256. In a fixed-oracle run, searching the successful
signing log for a prefix match covers every overlap with a commitment for a logged message,
for any choice of commitment high bits. The bound
for the adaptive signing experiment is an original deduction from these encodings.
-/

public section

namespace Cslib.Crypto.MLDSA.FIPS204

open Cslib.Probability
open scoped ENNReal NNReal

/-- Raw SHAKE256 input of the first logged message whose 64-byte representative equals the
public-key hash. Comparing this input with the encoded public key tests for a collision. -/
def Xofs.matchingRepresentativeInput (H : Xofs) (pk : List Byte) (log : List Forgery) :
    Option (List Bool) :=
  let tr := H.h256.readBytes pk 64
  let addr (g : Forgery) := representativeInput tr (formattedMessage g)
  (log.find? fun g => H.h256.read (addr g) 64 == tr).map addr

/-- Equality of entire representative and commitment addresses implies that the search finds a
match in the log. This includes new signatures on a previously signed context and message. -/
theorem matchingRepresentativeInput_of_overlap (H : Xofs) (s : Level) (pk : List Byte)
    {log : List Forgery} {g : Forgery} (hg : g ∈ log) (formatted : List Bool)
    (w : Fin s.params.k → Fin 256 → ℤ)
    (overlap : representativeInput (H.h256.readBytes pk 64) formatted =
      commitmentInput s w (H.messageRepresentative pk (formattedMessage g))) :
    (H.matchingRepresentativeInput pk log).isSome := by
  let tr := H.h256.readBytes pk 64
  have ht : (Keccak.bytesToBitsLE tr).length = 512 := by
    rw [Keccak.length_bytesToBitsLE, show tr.length = 64 from H.h256.length_read ..]
  have same : Keccak.bytesToBitsLE tr = H.messageRepresentative pk (formattedMessage g) := by
    have h := congrArg (List.take 512) overlap
    have lg : (H.messageRepresentative pk (formattedMessage g)).length = 512 :=
      length_messageRepresentative ..
    rw [representativeInput, ← ht, List.take_left, ht, ← lg, take_commitmentInput] at h
    exact h
  have hash : H.h256.read (representativeInput tr (formattedMessage g)) 64 = tr :=
    (Keccak.bytesToBitsLE_injective same).symm
  simp only [Xofs.matchingRepresentativeInput, Option.isSome_map, List.isSome_find?]
  exact List.any_eq_true.mpr ⟨g, hg, beq_iff_eq.mpr hash⟩

private theorem match_valid {H : Xofs} {pk : List Byte} {log : List Forgery} {y : List Bool}
    (hit : H.matchingRepresentativeInput pk log = some y) :
    H.h256.read y 64 = H.h256.readBytes pk 64 ∧
      (Keccak.bytesToBitsLE pk ≠ y ∨ H.h256.readBytes pk 64 = pk.take 64) := by
  let tr := H.h256.readBytes pk 64
  let addr (g : Forgery) := representativeInput tr (formattedMessage g)
  let sameHash (g : Forgery) := H.h256.read (addr g) 64 == tr
  change (log.find? sameHash).map addr = some y at hit
  obtain ⟨g, found, rfl⟩ := Option.map_eq_some_iff.mp hit
  refine ⟨beq_iff_eq.mp (List.find?_some (p := sameHash) found), ?_⟩
  by_cases eq : Keccak.bytesToBitsLE pk = addr g
  · right
    have ht : (Keccak.bytesToBitsLE tr).length = 512 := by
      rw [Keccak.length_bytesToBitsLE, show tr.length = 64 from H.h256.length_read ..]
    have head := congrArg (List.take 512) eq
    change _ = (Keccak.bytesToBitsLE tr ++ formattedMessage g).take 512 at head
    rw [← ht, List.take_left, ht, show (512 : ℕ) = 8 * 64 by decide,
      ← Keccak.bytesToBitsLE_take] at head
    exact (Keccak.bytesToBitsLE_injective head).symm
  · exact Or.inl eq

/-- In the actual retained-controller experiment, a match in any successful signing reply
costs at most the probability of the computed SHAKE256 collision plus `2⁻⁵¹²` for the entire
setup. The controller may choose its messages after coherent queries and earlier signing
replies. Both probabilities use the same raw oracles throughout the original capped game. -/
theorem QuantumSigningForger.matchingRepresentative_le (C : QuantumSigningForger) (base : Xofs)
    (s : Level) {a b : ℕ} (ha : 8 * (32 + 320 * s.params.k) ≤ a) (hb : 64 ≤ b) :
    let run (test : Xofs → List Byte → List Forgery → Bool) : Game :=
      (base.uniformPrefixes a b).bind fun H => H.keyExperiment s fun keys =>
        (C.transcript H s keys).map fun z => test H keys.publicKey z.2
    Game.succProbability (run fun H pk log => (H.matchingRepresentativeInput pk log).isSome) ≤
      Game.succProbability (run fun H pk log => (H.matchingRepresentativeInput pk log).any fun y =>
        decide (Keccak.bytesToBitsLE pk ≠ y ∧ H.h256.readBytes pk 64 = H.h256.read y 64)) +
        (2 ^ 512 : ℝ≥0)⁻¹ := by
  intro run
  apply ENNReal.coe_le_coe.mp
  simp only [Game.succProbability, ENNReal.coe_add, ENNReal.coe_toNNReal (PMF.apply_ne_top _ _),
    ENNReal.coe_inv (pow_ne_zero 512 (two_ne_zero : (2 : ℝ≥0) ≠ 0)), ENNReal.coe_pow,
    ENNReal.coe_ofNat]
  dsimp only [run]
  refine le_trans ?_ (add_le_add le_rfl (uniformPrefixes_publicKeyPrefix_le base s ha hb))
  apply PMF.bind_apply_le_add_on_support
  intro H _
  unfold Xofs.keyExperiment
  apply PMF.bind_apply_le_add_on_support
  intro seed _
  cases H.keyGen s seed with
  | none => simp
  | some keys =>
    by_cases eq : H.h256.readBytes keys.publicKey 64 = keys.publicKey.take 64
    · simp only [eq, decide_true, PMF.pure_apply_self]
      exact (PMF.coe_le_one _ _).trans (le_add_self)
    · simp only [eq, decide_false, PMF.pure_apply_of_ne false true (by decide), add_zero]
      apply le_of_eq
      apply congrArg (fun game : Game => game true)
      congr 1
      funext z
      cases h : H.matchingRepresentativeInput keys.publicKey z.2 with
      | none => rfl
      | some y =>
        obtain ⟨hash, distinct⟩ := match_valid h
        simp [distinct.resolve_right eq, hash]

end Cslib.Crypto.MLDSA.FIPS204
