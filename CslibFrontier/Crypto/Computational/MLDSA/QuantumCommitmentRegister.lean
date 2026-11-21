/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.MLDSA.RandomXof
public import CslibFrontier.Crypto.Computational.MLDSA.QuantumSigning
public import CslibFrontier.Computability.Circuit.Quantum.Oracle.ValueQuery
import all CslibFrontier.Crypto.Computational.MLDSA.FIPS204
import all CslibFrontier.Crypto.Computational.MLDSA.RandomXof
import all CslibFrontier.Crypto.Computational.MLDSA.QuantumSigning
import CslibFrontier.Probability.PMF.UniformExtend

/-!
# Coherent access to the ML-DSA commitment digest register

Draw the SHAKE256 digest prefixes on all raw words of the FIPS commitment length as independent
bit strings before key generation. The joint distribution of the register and the full raw XOFs is
preserved. A placed coherent gate on the resulting SHAKE pair uses two XOR queries to this
register, with one fixed reversible response computation between them.

The digest widths and little-endian packing follow [NISTFIPS204], Algorithms 7 and 8, and
[NISTFIPS202], Appendix B.1. The finite oracle decomposition and gate comparison are original.
-/

public section

namespace Cslib.Crypto.MLDSA.FIPS204

open Cslib.Probability Cslib.Quantum ExtendableOutput

/-- Install a literal digest prefix on every SHAKE256 word of the FIPS commitment length,
including words that are also queried in another role. Long-read suffixes and SHAKE128
remain in the supplied XOF pair. -/
@[expose] def Xofs.withDigestRegister (H : Xofs) (s : Level)
    (D : BitString s.commitmentInputBits → BitString (8 * digestBytes s)) : Xofs :=
  { H with h256 := H.h256.withPrefixes fun x =>
      if x.length = s.commitmentInputBits then
        some (((Keccak.fixedBytesEquivBitsLE _).symm (D (BitString.ofList _ x))).toList) else none }

/-- The key seed, short-vector nonces and encoded public keys read by Algorithm 6 lie
outside the commitment register at each parameter set. The whole key pair and setup failure
are consequently independent of the values installed there. -/
theorem Xofs.keyGen_withDigestRegister (H : Xofs) (s : Level)
    (D : BitString s.commitmentInputBits → BitString (8 * digestBytes s)) (seed : FixedBytes 32) :
    (H.withDigestRegister s D).keyGen s seed = H.keyGen s seed := by
  have off (x : List Byte) (n : ℕ) (hne : 8 * x.length ≠ s.commitmentInputBits) :
      (H.withDigestRegister s D).h256.readBytes x n = H.h256.readBytes x n := by
    simp only [ExtendableOutput.readBytes, Xofs.withDigestRegister, ExtendableOutput.withPrefixes,
      Keccak.length_bytesToBitsLE, hne, ↓reduceIte]
  apply Xofs.keyGen_congr_of_reads (G := H.withDigestRegister s D) (H := H) s seed rfl
  · unfold Xofs.expandKeySeed
    apply off
    simp only [List.length_append, FixedBytes.length_toList, List.length_cons, List.length_nil]
    cases s <;> decide
  · intro nonce
    apply off
    simp only [nonceInput, List.length_append, List.length_take, List.length_drop,
      Xofs.expandKeySeed, H.h256.length_read, List.length_cons, List.length_nil]
    cases s <;> decide
  · intro x hx
    apply off
    rw [hx]
    cases s <;> decide

/-- Digest bits at a raw commitment-length input, in SHAKE's little-endian order. -/
def Xofs.readDigestRegister (H : Xofs) (s : Level) (x : BitString s.commitmentInputBits) :
    BitString (8 * digestBytes s) :=
  Keccak.fixedBytesEquivBitsLE _ (fun j => H.h256.byteAt (List.ofFn x) j)

/-- Reading all commitment prefixes from the current streams and reinstalling them preserves every
raw query, including SHAKE256 output beyond the digest. -/
theorem Xofs.withDigestRegister_readDigestRegister (H : Xofs) (s : Level) :
    H.withDigestRegister s (H.readDigestRegister s) = H := by
  cases H with
  | mk h128 h256 =>
    unfold Xofs.withDigestRegister
    congr 1
    apply ExtendableOutput.ext_byteAt
    intro x i
    by_cases len : x.length = s.commitmentInputBits
    · by_cases small : i < digestBytes s <;>
        simp [Xofs.readDigestRegister, ExtendableOutput.byteAt_withPrefixes, len, FixedBytes.toList,
          small, BitString.ofFn_ofList len]
    · simp [ExtendableOutput.byteAt_withPrefixes, len]

private def digestCells {a b : ℕ} (s : Level) (ha : s.commitmentInputBits ≤ a)
    (hb : digestBytes s ≤ b) : BitString s.commitmentInputBits × Fin (digestBytes s) ↪
      RawWord a × Fin b :=
  (show BitString s.commitmentInputBits ↪ RawWord a from
    ⟨fun x => word (List.ofFn x) (List.length_ofFn.le.trans ha), fun _ _ h =>
      List.ofFn_inj.mp (word_inj h)⟩).prodMap (Fin.castLEEmb hb)

private abbrev flatten (s : Level) :=
  ((Equiv.refl (BitString s.commitmentInputBits)).arrowCongr
    (Keccak.fixedBytesEquivBitsLE (digestBytes s)).symm).trans (Equiv.curry _ _ Byte).symm

private theorem overwrite {a b : ℕ} (s : Level) (ha : s.commitmentInputBits ≤ a)
    (hb : digestBytes s ≤ b) (H : ExtendableOutput) (t : Table a b)
    (D : BitString s.commitmentInputBits → BitString (8 * digestBytes s)) :
    (install H t).withPrefixes (fun x =>
      if x.length = s.commitmentInputBits then
        some (((Keccak.fixedBytesEquivBitsLE _).symm (D (BitString.ofList _ x))).toList)
      else none) =
      install H (Function.extend (digestCells s ha hb) (flatten s D) t) := by
  apply ext_byteAt
  intro x j
  rw [byteAt_withPrefixes, byteAt_install, byteAt_install]
  by_cases hx : x.length = s.commitmentInputBits ∧ j < digestBytes s
  · obtain ⟨len, small⟩ := hx
    let v := BitString.ofList s.commitmentInputBits x
    let p := (v, (⟨j, small⟩ : Fin (digestBytes s)))
    have atCell : digestCells s ha hb p =
        (word x (len.le.trans ha), ⟨j, small.trans_le hb⟩) := by
      refine Prod.ext ?_ rfl
      change word (List.ofFn (BitString.ofList s.commitmentInputBits x))
        (List.length_ofFn.le.trans ha) = word x (len.le.trans ha)
      simp only [BitString.ofFn_ofList len]
    simp only [len, small, ↓reduceIte, Option.bind_some, FixedBytes.toList, List.getElem?_ofFn,
      ↓reduceDIte, Option.getD_some, ha, small.trans_le hb, and_self]
    rw [← atCell, (digestCells s ha hb).injective.extend_apply]
    rfl
  · have miss {fit : x.length ≤ a} {idx : j < b} :
        ¬ ∃ p, digestCells s ha hb p = (word x fit, ⟨j, idx⟩) := by
      rintro ⟨⟨r, k⟩, h⟩
      have eq : List.ofFn r = x := word_inj (hx := List.length_ofFn.le.trans ha) (hy := fit)
        (congrArg Prod.fst h)
      have off : k.val = j := congrArg (fun z => z.2.val) h
      exact hx ⟨eq ▸ List.length_ofFn, off ▸ k.isLt⟩
    have off : ((if x.length = s.commitmentInputBits then
        some (((Keccak.fixedBytesEquivBitsLE _).symm (D (BitString.ofList _ x))).toList)
      else none).bind
        (fun r => r[j]?)) = none := by
      by_cases len : x.length = s.commitmentInputBits
      · have far : ¬ j < digestBytes s := fun small => hx ⟨len, small⟩
        simp [len, FixedBytes.toList, far]
      · simp [len]
    rw [off, Option.getD_none]
    split
    · exact (Function.extend_apply' _ _ _ miss).symm
    · rfl

/-- Draw all SHAKE256 commitment-length digest prefixes independently before key generation.
The register and the resulting full raw oracle pair have exactly their joint law in the
finite random-XOF experiment, including all cross-role and longer coherent reads. -/
theorem Xofs.uniformPrefixes_digestRegister (base : Xofs) (s : Level) {a b : ℕ}
    (ha : s.commitmentInputBits ≤ a) (hb : digestBytes s ≤ b) :
    ((base.uniformPrefixes a b).bind fun H =>
      (PMF.uniformOfFintype (BitString s.commitmentInputBits → BitString (8 * digestBytes s))).map
        fun D => (D, H.withDigestRegister s D)) =
      (base.uniformPrefixes a b).map fun H => (H.readDigestRegister s, H) := by
  let e := digestCells s ha hb
  let close (u t : Table a b) :=
    ((fun x => Keccak.fixedBytesEquivBitsLE (digestBytes s) (fun i => t (e (x, i)))),
      (⟨install base.h128 u, install base.h256 t⟩ : Xofs))
  have read (u t : Table a b) :
      close u t = ((⟨install base.h128 u, install base.h256 t⟩ : Xofs).readDigestRegister s,
        ⟨install base.h128 u, install base.h256 t⟩) := by
    refine Prod.ext ?_ rfl
    funext x
    apply congrArg (Keccak.fixedBytesEquivBitsLE _)
    funext i
    simp only [byteAt_install, List.length_ofFn, ha, i.isLt.trans_le hb, and_self, ↓reduceDIte]
    rfl
  have restore (u t : Table a b) (D : BitString s.commitmentInputBits → _) :
      close u (Function.extend e (flatten s D) t) =
        (D, (⟨install base.h128 u, install base.h256 t⟩ : Xofs).withDigestRegister s D) := by
    apply Prod.ext
    · funext x
      dsimp only [close]
      simp only [e.injective.extend_apply]
      exact (Keccak.fixedBytesEquivBitsLE _).apply_symm_apply (D x)
    · exact congrArg (Xofs.mk (install base.h128 u) ·) (overwrite s ha hb _ _ D).symm
  rw [independent_tables]
  simp only [PMF.bind_bind, PMF.bind_map, PMF.map_bind, PMF.map_comp, Function.comp_def]
  conv_lhs => rw [PMF.bind_comm]
  conv_rhs => simp only [← PMF.bind_pure_comp]; rw [PMF.bind_comm]
  apply congrArg (PMF.bind (PMF.uniformOfFintype (Table a b)) ·)
  funext u
  have law := PMF.uniformOfFintype_bind_bind_extend (κ := Byte) e (fun t => PMF.pure (close u t))
  rw [← PMF.uniformOfFintype_map_equiv (flatten s)] at law
  simp only [PMF.bind_map, Function.comp_def, restore] at law
  simpa only [← PMF.bind_pure_comp, Function.comp_def, read] using law

/-- Generate the actual key pair before sampling the independent commitment digest register.
The forger, signer and final verification all use the same installed pair of raw XOFs. -/
theorem QuantumSigningForger.randomPrefixGame_eq_digestRegister (C : QuantumSigningForger)
    (base : Xofs) (s : Level) {a b : ℕ} (ha : s.commitmentInputBits ≤ a)
    (hb : digestBytes s ≤ b) :
    C.randomPrefixGame s base a b =
      (base.uniformPrefixes a b).bind fun H => H.keyExperiment s fun keys =>
        (PMF.uniformOfFintype
          (BitString s.commitmentInputBits → BitString (8 * digestBytes s))).bind fun D =>
          let G := H.withDigestRegister s D
          (C.transcript G s keys).map fun (f, log) => G.winsForgery s keys.publicKey f log := by
  have eq := congrArg (fun p : PMF ((BitString s.commitmentInputBits →
    BitString (8 * digestBytes s)) × Xofs) => p.bind fun v => C.forgeryGame v.2 s)
    (base.uniformPrefixes_digestRegister s ha hb)
  simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def] at eq
  rw [randomPrefixGame, ← eq]
  apply congrArg (PMF.bind (base.uniformPrefixes a b) ·)
  funext H
  simp only [forgeryGame, Xofs.keyExperiment, Xofs.keyGen_withDigestRegister]
  rw [PMF.bind_comm]
  apply congrArg (PMF.bind (PMF.uniformOfFintype (FixedBytes 32)) ·)
  funext seed
  cases H.keyGen s seed <;> simp

/-- FIPS 204 signing and verification read precisely the installed digest at their packed
commitment. The representative may contain any 512 bits. -/
theorem Xofs.commitmentDigest_withDigestRegister (H : Xofs) (s : Level)
    (D : BitString s.commitmentInputBits → BitString (8 * digestBytes s))
    (w : Fin s.params.k → Fin 256 → ℤ) {μ : List Bool} (hμ : μ.length = 512) :
    Keccak.bytesToBitsLE ((H.withDigestRegister s D).commitmentDigest s w μ) =
      List.ofFn (D (BitString.ofList _ (commitmentInput s w μ))) := by
  let v := D (BitString.ofList _ (commitmentInput s w μ))
  have bits := Keccak.ofFn_fixedBytesEquivBitsLE (((Keccak.fixedBytesEquivBitsLE _).symm v))
  rw [Equiv.apply_symm_apply] at bits
  simpa only [Xofs.commitmentDigest, Xofs.withDigestRegister, ExtendableOutput.withPrefixes,
    commitmentInput_length s w hμ, ↓reduceIte, ExtendableOutput.readWithPrefix,
    List.take_of_length_le (FixedBytes.length_toList _).le, FixedBytes.length_toList,
    List.drop_eq_nil_of_le (H.h256.length_read ..).le, List.append_nil, v] using bits.symm

/-- The digest address decoded from a coherent device input. Queries at other lengths,
at malformed addresses and to SHAKE128 ignore the loaded digest. -/
def Xofs.digestLookup (s : Level) {a : ℕ} (x : BitString (a + 2)) :
    BitString s.commitmentInputBits :=
  match Xofs.unpad (List.ofFn fun i : Fin (a + 1) => x i.succ) with
  | none => 0
  | some word => BitString.ofList _ word

/-- Compute the native SHAKE response using one loaded digest. The same raw query decoder
handles both variants, shorter requests, suffixes and missing delimiters. -/
def Xofs.digestResponse (H : Xofs) (s : Level) (a b : ℕ) (x : BitString (a + 2))
    (v : BitString (8 * digestBytes s)) : BitString (8 * b) :=
  (H.withDigestRegister s fun _ => v).queryTable a b x

private theorem queryTable_register (H : Xofs) (s : Level)
    (D : BitString s.commitmentInputBits → BitString (8 * digestBytes s)) (a b : ℕ) :
    (H.withDigestRegister s D).queryTable a b =
      fun x => H.digestResponse s a b x (D (Xofs.digestLookup s x)) := by
  funext x
  unfold Xofs.digestResponse Xofs.queryTable Xofs.digestLookup
  split
  · rfl
  · rename_i word hw
    cases tag : x 0 <;> by_cases h : word.length = s.commitmentInputBits <;>
      simp only [hw, h, Bool.false_eq_true, ↓reduceIte, Xofs.withDigestRegister,
        ExtendableOutput.withPrefixes]

/-- Realize the actual placed SHAKE XOR gate by two queries to the independent digest register.
The same two scratch registers return to zero for every placement, including when the native
state is entangled across the addressed and unused wires. -/
theorem Xofs.xorQuery_withDigestRegister (H : Xofs) (s : Level)
    (D : BitString s.commitmentInputBits → BitString (8 * digestBytes s)) (a b m : ℕ)
    (wires : Fin (a + 2 + 8 * b) ↪ Fin m) (ψ : Qubits m) :
    runValue addStep (lookupXorSteps wires (Xofs.digestLookup s) (H.digestResponse s a b))
      (cleanLookupState ψ) D 2 =
      cleanLookupState ((xorQuery ((H.withDigestRegister s D).queryTable a b) wires).eval ψ) := by
  rw [runValue_lookupXorSteps, queryTable_register H s]

end Cslib.Crypto.MLDSA.FIPS204
