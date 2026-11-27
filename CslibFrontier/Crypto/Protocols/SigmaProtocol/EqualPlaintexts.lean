/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.SigmaProtocol.Interactive
public import CslibFrontier.Crypto.Protocols.SigmaProtocol.Linear
public import CslibFrontier.Crypto.Protocols.SigmaProtocol.LanguageReduction

/-!
# Equal plaintexts under one ElGamal key

Example 20.2 of [BonehShoup2023] (pp. 825–826), in additive notation: for a public key `u` and two
multiplicative-ElGamal ciphertexts `(v₀, e₀)` and `(v₁, e₁)`, the Chaum–Pedersen protocol on the
triple `(u, v₀ - v₁, e₀ - e₁)` proves the relation (20.2): there is a `β` with
`β • g = v₀ - v₁` and `β • u = e₀ - e₁` ([BonehShoup2023], p. 826). When `g` generates the group,
this says that both ciphertexts encrypt the same message (`exists_equalPlaintextsRelation_iff`).
Neither the message nor the two encryption exponents are needed.

The protocol is `SigmaProtocol.comap` of `chaumPedersen` along the statement map
`equalPlaintextsTriple`, with the identity on witnesses, so completeness, special soundness and
special HVZK are those of `chaumPedersen`. Special soundness and special HVZK here are the
library's `SigmaProtocol.SpecialSoundness` and `SigmaProtocol.SpecialHVZK`: an extractor that
returns a witness from two accepting transcripts, and a simulator whose transcript law equals the
honest one at each fixed challenge. The efficiency of the extractor and simulator, which
[BonehShoup2023], Definitions 19.4 and 19.5, also ask for, is a separate property
(`EfficientSpecialSoundness`, `EfficientSpecialHVZK`) that is not proved here.

## Main definitions

* `Cslib.Crypto.Protocols.SigmaProtocol.equalPlaintextsRelation`: the relation (20.2).
* `Cslib.Crypto.Protocols.SigmaProtocol.equalPlaintextsTriple`: the statement map.
* `Cslib.Crypto.Protocols.SigmaProtocol.equalPlaintexts`: the protocol.

## Main results

* `Cslib.Crypto.Protocols.SigmaProtocol.exists_equalPlaintextsRelation_iff`: when `g` generates
  the group, a statement has a witness iff the two ciphertexts encrypt one message.
* `Cslib.Crypto.Protocols.SigmaProtocol.equalPlaintextsRelation_reencrypt`: a pair and its
  re-encryption satisfy (20.2), with the re-encryption exponent (with opposite sign) as witness.
* `Cslib.Crypto.Protocols.SigmaProtocol.equalPlaintexts_complete`,
  `Cslib.Crypto.Protocols.SigmaProtocol.equalPlaintexts_specialHVZK`: the protocol is complete
  and special HVZK for (20.2), with no primality or generator hypothesis.
* `Cslib.Crypto.Protocols.SigmaProtocol.equalPlaintexts_specialSoundness`,
  `Cslib.Crypto.Protocols.SigmaProtocol.equalPlaintexts_sound`: for prime `q` the protocol is
  special sound for (20.2), and when in addition `g` generates the group every prover makes the
  verifier accept a non-equal-plaintext pair with probability at most `1 / |C|`.

## References

* [D. Boneh and V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Theorem 20.1 (eq. (20.1), p. 824) and Example 20.2 (eq. (20.2),
  pp. 825–826).
-/

public section

namespace Cslib.Crypto.Protocols.SigmaProtocol

open Interactive
open scoped ENNReal

section EqualPlaintexts

variable {q : ℕ} {G : Type} [AddCommGroup G] [Module (ZMod q) G]

/-- The relation of [BonehShoup2023], Example 20.2, equation (20.2) (p. 826), in additive notation:
a witness for a public key `u` and ciphertexts `(v₀, e₀)` and `(v₁, e₁)` is `β` with
`β • g = v₀ - v₁` and `β • u = e₀ - e₁`. -/
@[expose] def equalPlaintextsRelation (g : G) (β : ZMod q) :
    G × (G × G) × (G × G) → Prop
  | (u, ct₀, ct₁) => β • g = ct₀.1 - ct₁.1 ∧ β • u = ct₀.2 - ct₁.2

/-- The statement map of [BonehShoup2023], Example 20.2 (p. 826): a public key `u` and ciphertexts
`(v₀, e₀)` and `(v₁, e₁)` go to the triple `(u, v₀ - v₁, e₀ - e₁)`. -/
@[expose] def equalPlaintextsTriple : G × (G × G) × (G × G) → G × G × G
  | (u, ct₀, ct₁) => (u, ct₀.1 - ct₁.1, ct₀.2 - ct₁.2)

/-! ### The language -/

/-- Two encryptions `(β₀ • g, β₀ • u + m)` and `(β₁ • g, β₁ • u + m)` of one message under one key
satisfy (20.2) with `β = β₀ - β₁` ([BonehShoup2023], Example 20.2, p. 826). -/
theorem equalPlaintextsRelation_sub (g u m : G) (β₀ β₁ : ZMod q) :
    equalPlaintextsRelation g (β₀ - β₁) (u, (β₀ • g, β₀ • u + m), (β₁ • g, β₁ • u + m)) := by
  simp only [equalPlaintextsRelation, sub_smul, add_sub_add_right_eq_sub, and_self]

/-- When `g` generates the group, a statement has a witness of (20.2) iff the two ciphertexts
encrypt one message under the key `u` ([BonehShoup2023], Example 20.2, p. 826). The generator
hypothesis is used only from left to right. -/
theorem exists_equalPlaintextsRelation_iff {g : G}
    (hg : Function.Surjective fun β : ZMod q => β • g) (u : G) (ct₀ ct₁ : G × G) :
    (∃ β : ZMod q, equalPlaintextsRelation g β (u, ct₀, ct₁)) ↔
      ∃ (m : G) (β₀ β₁ : ZMod q),
        ct₀ = (β₀ • g, β₀ • u + m) ∧ ct₁ = (β₁ • g, β₁ • u + m) := by
  constructor
  · rintro ⟨β, hv, he⟩
    obtain ⟨β₁, hβ₁⟩ := hg ct₁.1
    refine ⟨ct₁.2 - β₁ • u, β + β₁, β₁, Prod.ext ?_ ?_, Prod.ext hβ₁.symm ?_⟩
    · simp only [add_smul, hv, hβ₁, sub_add_cancel]
    · simp only [add_smul, he]
      abel
    · simp only [add_sub_cancel]
  · rintro ⟨m, β₀, β₁, rfl, rfl⟩
    exact ⟨β₀ - β₁, equalPlaintextsRelation_sub g u m β₀ β₁⟩

/-- Re-encryption ([BonehShoup2023], Example 20.2, p. 826): for any pair `(v, e)` and exponent
`β`, the pair `(v, e)` and its re-encryption `(v + β • g, e + β • u)` satisfy (20.2), with witness
`-β`. Both are encryptions of one message under `u` when `(v, e)` is an encryption
`(β₀ • g, β₀ • u + m)`, or, for every pair, when `g` generates the group
(`exists_equalPlaintextsRelation_iff`). Without either, the relation can hold for a pair that is
no encryption: with `g = u = 0`, a pair whose first component is nonzero. The book writes `β` for
both this exponent and the witness of (20.2); they differ by a sign. -/
theorem equalPlaintextsRelation_reencrypt (g u : G) (ct : G × G) (β : ZMod q) :
    equalPlaintextsRelation g (-β) (u, ct, (ct.1 + β • g, ct.2 + β • u)) := by
  simp only [equalPlaintextsRelation, neg_smul, sub_add_cancel_left, and_self]

/-! ### The protocol -/

variable [NeZero q] {C : Type} [DecidableEq G]

variable (ι : C ↪ ZMod q) in
/-- The protocol of [BonehShoup2023], Example 20.2 (p. 826): the Chaum–Pedersen protocol on the
triple `(u, v₀ - v₁, e₀ - e₁)`. -/
@[expose] noncomputable def equalPlaintexts (g : G) :
    SigmaProtocol (ZMod q) (G × (G × G) × (G × G)) (G × G) C (ZMod q) :=
  (chaumPedersen ι g).comap (fun β _ => β) equalPlaintextsTriple

variable {ι : C ↪ ZMod q} {g : G}

/-- The verification equations `z • g = t₁ + c • (v₀ - v₁)` and `z • u = t₂ + c • (e₀ - e₁)`. -/
@[simp] theorem equalPlaintexts_accepts_iff {u : G} {ct₀ ct₁ t : G × G} {c : C} {z : ZMod q} :
    (equalPlaintexts ι g).Accepts (u, ct₀, ct₁) t c z ↔
      z • g = t.1 + ι c • (ct₀.1 - ct₁.1) ∧ z • u = t.2 + ι c • (ct₀.2 - ct₁.2) :=
  chaumPedersen_accepts_iff

/-- Honest conversations are accepting. -/
theorem equalPlaintexts_complete :
    (equalPlaintexts ι g).Complete (equalPlaintextsRelation g) :=
  chaumPedersen_complete.comap fun _ _ h => h

/-- Special soundness as `SigmaProtocol.SpecialSoundness`: from two accepting conversations with a
common commitment and distinct challenges, the Chaum–Pedersen extractor, run on the triple,
returns a witness of (20.2). The extractor's efficiency is a separate property, not proved
here. -/
theorem equalPlaintexts_specialSoundness [Fact q.Prime] :
    (equalPlaintexts ι g).SpecialSoundness (equalPlaintextsRelation (q := q) g)
      fun y => linearExtract ι (equalPlaintextsTriple y) :=
  chaumPedersen_specialSoundness.comap _ _

/-- Special honest-verifier zero knowledge as `SigmaProtocol.SpecialHVZK`, with the Chaum–Pedersen
simulator run on the triple: its conversations are accepting, and for a witness-statement pair its
transcript law at each fixed challenge equals the honest prover's. The simulator's efficiency is a
separate property, not proved here. -/
theorem equalPlaintexts_specialHVZK :
    (equalPlaintexts ι g).SpecialHVZK (equalPlaintextsRelation g) fun y =>
      linearSimulate (fun s : G × G × G => (LinearMap.toSpanSingleton (ZMod q) G g).prod
        (LinearMap.toSpanSingleton (ZMod q) G s.1)) Prod.snd ι (equalPlaintextsTriple y) :=
  chaumPedersen_specialHVZK.comap fun _ _ h => h

/-- Soundness with error `1 / |C|` against arbitrary provers ([BonehShoup2023], Theorem 20.1,
eq. (20.1), p. 824, applied to Example 20.2, p. 826): when `q` is prime and `g` generates the
group, on a public key and two ciphertexts that do not encrypt one message, every prover makes
the verifier accept with output in `langOut` with probability at most `1 / |C|`. -/
theorem equalPlaintexts_sound [Fact q.Prime] [Fintype C] [Nonempty C]
    (hg : Function.Surjective fun β : ZMod q => β • g) (langOut : Set Unit := Set.univ) :
    (equalPlaintexts ι g).toInteractiveVerifier.Sound World.plain
      {y | let (u, ct₀, ct₁) := y; ∃ (m : G) (β₀ β₁ : ZMod q),
        ct₀ = (β₀ • g, β₀ • u + m) ∧ ct₁ = (β₁ • g, β₁ • u + m)}
      langOut (1 / (Fintype.card C : ℝ≥0∞)) := by
  rintro ⟨u, ct₀, ct₁⟩ hy
  exact (equalPlaintexts_specialSoundness (ι := ι) (g := g)).sound langOut (u, ct₀, ct₁)
    fun h => hy ((exists_equalPlaintextsRelation_iff hg u ct₀ ct₁).mp h)

end EqualPlaintexts

end Cslib.Crypto.Protocols.SigmaProtocol
