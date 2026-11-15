/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.SigmaProtocol.LanguageReduction.Sound
public import CslibFrontier.Crypto.Protocols.SigmaProtocol.LanguageReduction.Efficient
public import CslibFrontier.Crypto.Protocols.SigmaProtocol.Lyubashevsky.Efficient
public import CslibFrontier.Crypto.Protocols.SigmaProtocol.Composition
public import CslibFrontier.Crypto.Protocols.SigmaProtocol.Linear
public import CslibFrontier.Crypto.Computational.SchnorrProtocol
import CslibFrontier.Computability.Complexity.Reduction.Levin
import CslibFrontier.Computability.Interactive.StatementMap
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair.Projections

/-!
# Tests for language reductions and derived Sigma protocols

Exercises `StatementMap`, `LanguageReduction`, `LanguageReduction.Sound`, and
`LanguageReduction.Efficient`:

* **A.** Encrypted-bit Sigma protocol ([BonehShoup2023], Example 20.3, p. 826) via OR-proof of
  Chaum–Pedersen protocols and `SigmaProtocol.comap`.
* **B.** Necessity probes for conditions (i), (ii), and the explicit witness map back in
  `SpecialSoundness.mapWitness`.
* **B′.** Straight-line knowledge-soundness transfer (`Verifier.KnowledgeSound.comap`).
* **C.** Efficient simulator and extractor transfers on Schnorr's protocol over `u₀ + u₁`.
* **D.** Encoded `LevinReduction` yields a `LanguageReduction`.
-/

public section

namespace Cslib.Crypto.Protocols.SigmaProtocol

open Probability Interactive Turing.MultiTapeTM
open scoped ENNReal

/-! ### A. Client: encrypted bits ([BonehShoup2023], Example 20.3), additive notation -/

section EncryptedBit

section Relation

variable (q : ℕ) {G : Type} [AddCommGroup G] [Module (ZMod q) G] (g : G)

/-- `(u, v, w)` is a Diffie–Hellman triple with exponent `β`. -/
def dhRel : ZMod q → G × G × G → Prop := fun β (u, v, w) => β • g = v ∧ β • u = w

/-- `(v, e)` encrypts the bit `b` under the key `u` with randomness `β`: `v = β • g` and
`e = β • u + b • g`. The witness `Sum.inl β` is `b = 0`, and `Sum.inr β` is `b = 1`. -/
def bitRel : ZMod q ⊕ ZMod q → G × G × G → Prop
  | .inl β, (u, v, e) => β • g = v ∧ β • u = e
  | .inr β, (u, v, e) => β • g = v ∧ β • u + g = e

/-- The statement map of Example 20.3: `(u, v, e) ↦ ((u, v, e), (u, v, e - g))`. -/
def bitStmt : G × G × G → (G × G × G) × (G × G × G) := fun (u, v, e) => ((u, v, e), (u, v, e - g))

theorem bitRel_iff (x : ZMod q ⊕ ZMod q) (y : G × G × G) :
    orRelation (dhRel q g) (dhRel q g) x (bitStmt g y) ↔ bitRel q g x y := by
  obtain ⟨u, v, e⟩ := y
  cases x <;> simp [orRelation, dhRel, bitRel, bitStmt, eq_sub_iff_add_eq]

/-- Example 20.3 is a language reduction to the OR of two Diffie–Hellman relations, with the
identity as witness map and as witness map back. No hypothesis on `g`. -/
theorem languageReduction_bit :
    LanguageReduction (bitRel q g) (orRelation (dhRel q g) (dhRel q g)) (fun x _ => x)
      (bitStmt g) :=
  .of_witnessMap (fun x y h => (bitRel_iff q g x y).mpr h) (fun x' _ => x')
    fun x' y h => (bitRel_iff q g x' y).mp h

end Relation

variable (q : ℕ) [NeZero q] {G : Type} [AddCommGroup G] [Module (ZMod q) G] [DecidableEq G]
  (g : G)

/-- The Chaum–Pedersen simulator used on both sides. -/
noncomputable abbrev cpSimulate : G × G × G → ZMod q → PMF ((G × G) × ZMod q) :=
  linearSimulate (fun s : G × G × G => (LinearMap.toSpanSingleton (ZMod q) G g).prod
    (LinearMap.toSpanSingleton (ZMod q) G s.1)) Prod.snd (Function.Embedding.refl _)

/-- The protocol of Example 20.3 and Figure 20.1: the OR-proof of two Chaum–Pedersen protocols on
`((u, v, e), (u, v, e - g))`. -/
noncomputable def encryptedBit :
    SigmaProtocol (ZMod q ⊕ ZMod q) (G × G × G) ((G × G) × (G × G)) (ZMod q)
      (ZMod q × ZMod q × ZMod q) :=
  (orProof (chaumPedersen (Function.Embedding.refl _) g)
    (chaumPedersen (Function.Embedding.refl _) g)
    (cpSimulate q g) (cpSimulate q g)).comap (fun x _ => x) (bitStmt g)

theorem encryptedBit_complete : (encryptedBit q g).Complete (bitRel q g) :=
  (languageReduction_bit q g).complete
    (orProof_complete chaumPedersen_complete chaumPedersen_complete chaumPedersen_specialHVZK
      chaumPedersen_specialHVZK)

theorem encryptedBit_specialHVZK :
    (encryptedBit q g).SpecialHVZK (bitRel q g)
      fun y => orSimulate (cpSimulate q g) (cpSimulate q g) (bitStmt g y) :=
  (languageReduction_bit q g).specialHVZK
    (orProof_specialHVZK chaumPedersen_specialHVZK chaumPedersen_specialHVZK)

variable [Fact q.Prime]

/-- Soundness with error `1 / q`, for the language "`(v, e)` encrypts a bit under `u`". -/
theorem encryptedBit_sound :
    (encryptedBit q g).toInteractiveVerifier.Sound World.plain
      (language (Function.swap (bitRel q g))) Set.univ (1 / (Fintype.card (ZMod q) : ℝ≥0∞)) :=
  (languageReduction_bit q g).sound
    (orProof_specialSoundness chaumPedersen_specialSoundness chaumPedersen_specialSoundness)

/-- Here a witness can be mapped back (by the identity), so the protocol is special sound for the
relation itself. -/
theorem encryptedBit_specialSoundness :
    (encryptedBit q g).SpecialSoundness (bitRel q g) fun y t c z c' z' =>
      orExtract (linearExtract (Function.Embedding.refl _))
        (linearExtract (Function.Embedding.refl _)) (bitStmt g y) t c z c' z' :=
  ((orProof_specialSoundness chaumPedersen_specialSoundness
    chaumPedersen_specialSoundness).comap (fun x _ => x) (bitStmt g)).mapWitness (fun x' _ => x')
      fun x' y h => (bitRel_iff q g x' y).mp h

end EncryptedBit

/-! ### B. Probes: each condition is needed -/

section Probes

/-- A protocol that sends its witness as commitment and as response; the verifier accepts when
both equal the statement. It is complete and special HVZK for the relation `x = y`. -/
noncomputable def revealProtocol : SigmaProtocol Bool Bool Bool Unit Bool where
  State := Unit
  commit x _ := PMF.pure (x, ())
  respond x _ _ _ := x
  verify y t _ z := t == y && z == y

theorem revealProtocol_transcript (x y : Bool) (c : Unit) :
    revealProtocol.transcript x y c = PMF.pure (x, x) := by
  simp [transcript, revealProtocol, PMF.pure_map]

theorem revealProtocol_complete : revealProtocol.Complete fun x y => x = y := by
  intro x y hxy c tz htz
  rw [revealProtocol_transcript, PMF.mem_support_pure_iff] at htz
  subst htz hxy
  simp [Accepts, revealProtocol]

theorem revealProtocol_specialHVZK :
    revealProtocol.SpecialHVZK (fun x y => x = y) fun y _ => PMF.pure (y, y) where
  accepts y c tz htz := by
    rw [PMF.mem_support_pure_iff] at htz
    subst htz
    simp [Accepts, revealProtocol]
  transcript_eq x y hxy c := by rw [revealProtocol_transcript, hxy]

/-- Condition (i) fails: the statement map sends `()` to `true`, the witness map is the identity,
and every Boolean is declared a witness of `()`, although `false` is no witness of `true`.
Condition (ii) holds. The derived protocol is not complete. -/
example :
    ¬ (revealProtocol.comap (fun x (_ : Unit) => x) fun _ => true).Complete fun _ _ => True := by
  intro h
  have := h false () trivial () (false, false) (by
    rw [comap_transcript, revealProtocol_transcript, PMF.mem_support_pure_iff])
  simp [Accepts, comap, revealProtocol] at this

/-- In the same case no simulator is special HVZK: honest transcripts depend on the witness. -/
example (simulate : Unit → Unit → PMF (Bool × Bool)) :
    ¬ (revealProtocol.comap (fun x (_ : Unit) => x) fun _ => true).SpecialHVZK
      (fun _ _ => True) simulate := by
  intro h
  have h0 := h.transcript_eq false () trivial ()
  have h1 := h.transcript_eq true () trivial ()
  rw [comap_transcript, revealProtocol_transcript] at h0 h1
  have := h0.symm.trans h1
  have hmem :
      ((false, false) : Bool × Bool) ∈ (PMF.pure (true, true) : PMF (Bool × Bool)).support :=
    this ▸ (PMF.mem_support_pure_iff _ _).mpr rfl
  simp at hmem

/-- A protocol whose verifier accepts exactly the statement `true`, with two challenges. It is
special sound for the relation "the statement is `true`", for every extractor. -/
noncomputable def constProtocol (X : Type) : SigmaProtocol X Bool Unit Bool Unit where
  State := Unit
  commit _ _ := PMF.pure ((), ())
  respond _ _ _ _ := ()
  verify y _ _ _ := y

theorem constProtocol_specialSoundness (X : Type) (extract : Bool → Unit → Bool → Unit → Bool →
    Unit → X) :
    (constProtocol X).SpecialSoundness (fun _ y => y = true) extract :=
  fun _ _ _ _ _ _ _ hz _ => hz

/-- Condition (ii) fails: `()` has no witness and is sent to the true statement `true`.
Condition (i) holds. The derived verifier is not sound with any error below `1`: the honest prover
of the derived protocol is accepted with probability `1` on the false statement. -/
example {ε : ℝ≥0∞} (hε : ε < 1) :
    ¬ ((constProtocol Unit).comap (fun x (_ : Unit) => x)
        fun _ => true).toInteractiveVerifier.Sound World.plain
      (language (Function.swap fun (_ : Unit) (_ : Unit) => False)) Set.univ ε := by
  intro h
  let P := (constProtocol Unit).comap (fun x (_ : Unit) => x) fun _ : Unit => true
  have hcommit : P.CommitRealizedBy fun _ _ => pure ((), ()) := fun x y => by
    simp [P, comap, constProtocol]
  have hrun := P.eval_toInteractiveReduction_run hcommit () ()
  have hb := h () (by rintro ⟨w, hw⟩; exact hw) _
    ((P.toInteractiveReduction fun _ _ => pure ((), ())).prover () ())
  change (World.plain.eval ((P.toInteractiveReduction fun _ _ => pure ((), ())).run () ())
    ).toOuterMeasure _ ≤ ε at hb
  rw [hrun, PMF.toOuterMeasure_map_apply] at hb
  have hle : (1 : ℝ≥0∞) ≤ ε := by
    refine le_trans (le_of_eq ?_) hb
    symm
    rw [PMF.toOuterMeasure_apply_eq_one_iff]
    intro x _
    simp [P, comap, constProtocol]
  exact absurd hle (not_le.mpr hε)

/-- Conditions (i) and (ii) hold and still the extractor of the original protocol, run on the
mapped statement, is not an extractor for `R`: a witness of `g y` need not be a witness of `y`.
Composing `(h.comap f g).mapWitness k hk` with a map back repairs this (here the constant
`true`). -/
example :
    LanguageReduction (fun x y : Bool => y = true ∧ x = true) (fun (_ : Bool) y => y = true)
      (fun x _ => x) id ∧
    (constProtocol Bool).SpecialSoundness (fun _ y => y = true) (fun _ _ _ _ _ _ => false) ∧
    ¬ ((constProtocol Bool).comap (fun x (_ : Bool) => x) id).SpecialSoundness
      (fun x y => y = true ∧ x = true) (fun _ _ _ _ _ _ => false) ∧
    ((constProtocol Bool).comap (fun x (_ : Bool) => x) id).SpecialSoundness
      (fun x y => y = true ∧ x = true) (fun _ _ _ _ _ _ => true) := by
  refine ⟨⟨fun _ _ h => h.1, fun y ⟨_, hy⟩ => ⟨true, hy, rfl⟩⟩,
    constProtocol_specialSoundness _ _, fun h => ?_, ?_⟩
  · have := h true () false () true () (by decide) rfl rfl
    simp at this
  · exact ((constProtocol_specialSoundness Bool fun _ _ _ _ _ _ => false).comap
      (fun x _ => x) id).mapWitness (fun _ _ => true) fun _ _ h => ⟨h, rfl⟩

/-! ### B′. Generic verifier knowledge-soundness transfer (`Verifier.KnowledgeSound.comap`) -/

section VerifierPredicates

variable {X Y X' Y' T C Z : Type} [Fintype C] [Nonempty C]
  {P' : SigmaProtocol X' Y' T C Z} {f : X → Y → X'} {g : Y → Y'}

/-- Knowledge soundness of the derived verifier for the relation "`w` is a witness of `g y`", by
`Verifier.KnowledgeSound.comap`. -/
example {W' : Type} {R' : W' → Y' → Prop} {E : Y' → Spec.Transcript P'.interactiveSpec → Unit → W'}
    {ε : ℝ≥0∞} (h : P'.toInteractiveVerifier.KnowledgeSound (Function.swap R') Accept E ε) :
    (P'.comap f g).toInteractiveVerifier.KnowledgeSound (fun y w => R' w (g y)) Accept
      (fun y => E (g y)) ε :=
  Verifier.KnowledgeSound.comap h g

end VerifierPredicates

end Probes

end Cslib.Crypto.Protocols.SigmaProtocol

/-! ### C. Client of the efficiency transfers: Schnorr's protocol on the sum of two statements -/

namespace Cslib.Crypto.PrimeOrderGroupFamily

open Probability Turing.MultiTapeTM Cslib.Crypto.Protocols Cslib.Crypto.Protocols.SigmaProtocol
open scoped ENNReal

variable (F : PrimeOrderGroupFamily)

/-- Statement map: a pair of group elements to their sum. -/
def sumStatement (i : ℕ × F.Desc) (y : F.Carrier i.2 × F.Carrier i.2) : F.Carrier i.2 := y.1 + y.2

/-- Pairs of group elements as words. -/
def encSumStatement (i : ℕ × F.Desc) : F.Carrier i.2 × F.Carrier i.2 ↪ List Bool :=
  encPair (F.encodeEmbedding i.2) (F.encodeEmbedding i.2)

/-- The statement map on words: split the pair and add with the family's word addition. -/
def sumStatementWord (p : (ℕ × F.Desc) × List Bool) : List Bool :=
  F.add (p.1.2, unframe p.2, dropFrame p.2)

theorem computableInPolyTime_sumStatementWord :
    ComputableInPolyTime F.sumStatementWord (encPair F.schnorrEncoding.index encBits) encBits := by
  have hd : ComputableInPolyTime (fun p : (ℕ × F.Desc) × List Bool => p.1.2)
      (encPair (encPair encUnary F.encDesc) encBits) F.encDesc := by fun_prop
  have hw : ComputableInPolyTime (fun p : (ℕ × F.Desc) × List Bool => p.2)
      (encPair (encPair encUnary F.encDesc) encBits) encBits := by fun_prop
  exact F.computableInPolyTime_add.comp
    (hd.prod ((ComputableInPolyTime.unframe.comp hw).prod (ComputableInPolyTime.dropFrame.comp hw)))

theorem sumStatementWord_encSumStatement (i : ℕ × F.Desc)
    (y : F.Carrier i.2 × F.Carrier i.2) :
    F.sumStatementWord (i, F.encSumStatement i y) =
      F.schnorrEncoding.statement i (F.sumStatement i y) := by
  obtain ⟨u₀, u₁⟩ := y
  simp only [sumStatementWord, encSumStatement, unframe_encPair, dropFrame_encPair,
    schnorrEncoding, encodeEmbedding, Function.Embedding.coeFn_mk, sumStatement]
  exact F.add_encode i.2 u₀ u₁

/-- Schnorr's protocol on `u₀ + u₁`, as a protocol for "both `u₀` and `u₁` have known discrete
logarithms", with witness map `(α₀, α₁) ↦ α₀ + α₁`. -/
noncomputable def schnorrSumFamily (i : ℕ × F.Desc) :
    SigmaProtocol (ZMod (F.order i.2) × ZMod (F.order i.2)) (F.Carrier i.2 × F.Carrier i.2)
      (F.Carrier i.2) (ZMod (F.order i.2)) (ZMod (F.order i.2)) :=
  (F.schnorrFamily i).comap (fun x _ => x.1 + x.2) (F.sumStatement i)

/-- Efficient special HVZK transfers, with the same error. -/
theorem efficientSpecialHVZK_schnorrSum :
    EfficientSpecialHVZK F.schnorrSumFamily
      (fun i x y => x.1 • F.generator i.2 = y.1 ∧ x.2 • F.generator i.2 = y.2)
      (F.schnorrEncoding.withStatement F.encSumStatement)
      (fun i y c => linearSimulate (fun _ => LinearMap.toSpanSingleton (ZMod (F.order i.2))
        (F.Carrier i.2) (F.generator i.2)) id (Function.Embedding.refl _) (F.sumStatement i y) c)
      (fun i => 1 / 2 ^ i.1) :=
  F.efficientSpecialHVZK_schnorr.comap
    (fun i x y h => by simp only [sumStatement, add_smul, h.1, h.2])
    F.computableInPolyTime_sumStatementWord F.sumStatementWord_encSumStatement

/-- Efficient special soundness transfers for the relation "`α` is a discrete logarithm of
`u₀ + u₁`": the extracted witness is one for the mapped statement only. -/
theorem efficientSpecialSoundness_schnorrSum :
    EfficientSpecialSoundness F.schnorrSumFamily
      (fun i (α : ZMod (F.order i.2)) y => α • F.generator i.2 = F.sumStatement i y)
      (F.schnorrEncoding.withStatement F.encSumStatement) (fun i => F.encScalar i.2)
      (fun i y => F.schnorrExtract i (F.sumStatement i y)) :=
  F.efficientSpecialSoundness_schnorr.comap _
    F.computableInPolyTime_sumStatementWord F.sumStatementWord_encSumStatement

/-- The hypotheses of `EfficientSpecialSoundness.mapWitness` can be met: the identity witness map,
computed on words by a projection. -/
example :
    EfficientSpecialSoundness F.schnorrFamily (fun i α u => α • F.generator i.2 = u)
      F.schnorrEncoding (fun i => F.encScalar i.2)
      (fun i y t c z c' z' => F.schnorrExtract i y t c z c' z') :=
  F.efficientSpecialSoundness_schnorr.mapWitness (fun _ w _ => w) (fun _ _ _ h => h) _
    (kw := fun p => p.2.1) (by fun_prop) fun _ _ _ => rfl

/-- The relation of `schnorrSumFamily` reduces to Schnorr's: condition (i) by adding the
exponents, condition (ii) because every element is a multiple of the generator. The extractor
above returns a discrete logarithm of `u₀ + u₁`, from which the two discrete logarithms are not
computed: this is the case in which knowledge soundness is not inherited. -/
example (i : ℕ × F.Desc) :
    LanguageReduction
      (fun (x : ZMod (F.order i.2) × ZMod (F.order i.2)) (y : F.Carrier i.2 × F.Carrier i.2) =>
        x.1 • F.generator i.2 = y.1 ∧ x.2 • F.generator i.2 = y.2)
      (fun (α : ZMod (F.order i.2)) (u : F.Carrier i.2) => α • F.generator i.2 = u)
      (fun x _ => x.1 + x.2) (F.sumStatement i) :=
  ⟨fun x y h => by simp only [sumStatement, add_smul, h.1, h.2], fun y _ => by
    obtain ⟨α₀, h₀⟩ := F.smul_generator_surjective i.2 y.1
    obtain ⟨α₁, h₁⟩ := F.smul_generator_surjective i.2 y.2
    exact ⟨(α₀, α₁), h₀, h₁⟩⟩

end Cslib.Crypto.PrimeOrderGroupFamily

/-! ### D. Encoded counterpart: a `LevinReduction` gives a `LanguageReduction` -/

/-- A Levin reduction of NP relations (instance map, forward and backward witness maps, all
polynomial time) is a language reduction; its backward witness map gives condition (ii). -/
example {α β : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {R : Cslib.Complexity.NPRelation encA} {S : Cslib.Complexity.NPRelation encB}
    (r : Cslib.Complexity.LevinReduction R S) :
    Cslib.Crypto.Protocols.SigmaProtocol.LanguageReduction (fun w a => R.IsWitness a w)
      (fun w b => S.IsWitness b w) (fun w a => r.forwardWitness (a, w)) r.toFun :=
  .of_witnessMap (fun w a h => r.isWitness_forwardWitness a w h)
    (fun w a => r.backwardWitness (a, w)) fun w a h => r.isWitness_backwardWitness a w h

/-! ### E. Efficient verification under a non-identity statement map -/

section

open Cslib.Crypto.Protocols.SigmaProtocol Turing.MultiTapeTM

/-- Forgetting an auxiliary tag attached to a Lyubashevsky statement yields a polynomial-time
verifier for the derived protocol (`EfficientVerifier.comap` with non-identity `gw`). -/
example :
    EfficientVerifier
      (fun p => (lyubashevskyFamily p).comap (fun x _ => x) (fun y : _ × List Bool => y.1))
      (lyubashevskyEncoding.withStatement fun p =>
        encPair (lyubashevskyEncoding.statement p) encBits) :=
  efficientVerifier_lyubashevsky.comap (fun _ x _ => x) (gw := fun p => unframe p.2)
    (by fun_prop) fun _ y => unframe_encPair _ _ y.1 y.2

end
