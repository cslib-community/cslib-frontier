/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.DiscreteLog
import CslibFrontier.Crypto.Computational.DiffieHellman
import Mathlib.LinearAlgebra.BilinearMap

/-!
# Pairing-group infrastructure

Infrastructure for cryptographic pairing groups, after [BonehShoup2023], Section 15.4
(Definition 15.2 and equation (15.7), p. 625), where a pairing is an efficiently computable
bilinear map `e : G₀ × G₁ → GT` between cyclic groups of the same prime order `q`, with generators
`g₀` and `g₁` of the source groups, such that `e(g₀, g₁)` generates the target group `GT`.

`PairingGroupFamily` states this for a family of groups indexed by public parameters, as
`PrimeOrderGroupFamily` does for one group. The first source group is a `PrimeOrderGroupFamily`,
which supplies the parameters, their encoding and the order. The second source group and the
target group are `PrimeOrderGroupFamily.Companion`s of it: further groups of the same order over
the same parameters, each with its own generator, encoding and polynomial-time operations. The
pairing is a `ZMod q`-bilinear map for each choice of parameters, together with a function on
encodings that computes it in polynomial time.

Groups are written additively, as in `PrimeOrderGroupFamily`: the source's `u ^ α` is `α • u`, its
`u · u'` is `u + u'` and its identity is `0`. Bilinearity is stated as linearity over `ZMod q` in
each argument (`PairingGroupFamily.pair_smul_smul`,
`PairingGroupFamily.pair_smul_generator_smul_generator` for (15.7)), and non-degeneracy as the
equation `pair d g₀ g₁ = gT` for the generator `gT` that the target group carries
(`PairingGroupFamily.pair_generator_ne_zero`). Using the supporting algebraic equivalence
`biadditive_iff_apply_smul_generator` (after the remark following (15.7) on p. 625),
`bilinearOfSmulGenerator` and `PairingGroupFamily.ofSmulGenerator` build the `ZMod q`-bilinear
pairing and family directly from a plain map satisfying the generator product rule (15.7).

A companion is a prime-order group family of its own (`Companion.toFamily`), so `DiscreteLog` (and,
for clients importing `CslibFrontier.Crypto.Computational.DiffieHellman`, `CDH` and `DDH`) are
stated for the second source group and for the target group as they are for the first, and
`Companion` forwards `fun_prop` rules for encoded group operations. A family is a companion of
itself (`PrimeOrderGroupFamily.self`); a pairing is symmetric when its second source group is the
first one, `P.G₁ = P.G₀.self`.

This module provides pairing-group definitions and supporting infrastructure only; it constructs no
elliptic-curve pairing and states no hardness assumption or published theorem endpoint. Co-CDH and
decision BDH, BLS signatures, pairing-based identity-based encryption, and tripartite/multilinear
Diffie–Hellman key exchange ([BonehShoup2023], Sections 15.4–15.6 and 15.8) are tracked in
[#640](https://github.com/cslib-community/cslib-frontier/issues/640) and
[#5739](https://github.com/cslib-community/cslib-frontier/issues/5739).

## Main definitions

* `Cslib.Crypto.PrimeOrderGroupFamily.Companion`: a further group of the same order over the
  parameters of a prime-order group family.
* `Cslib.Crypto.PrimeOrderGroupFamily.Companion.toFamily`: a companion as a family of its own.
* `Cslib.Crypto.PrimeOrderGroupFamily.self`: a family as its own companion.
* `Cslib.Crypto.bilinearOfSmulGenerator`: constructs a `ZMod q`-bilinear map between cyclic
  `ZMod q`-modules from a function satisfying the generator product rule (15.7).
* `Cslib.Crypto.PairingGroupFamily`: two source groups, a target group and a pairing computable in
  polynomial time on encodings.
* `Cslib.Crypto.PairingGroupFamily.ofSmulGenerator`: constructs a `PairingGroupFamily` from a plain
  pairing function satisfying `pair d (α • g₀) (β • g₁) = (α * β) • gT`.

## Main results

* `Cslib.Crypto.PairingGroupFamily.computableInPolyTime_encode_pair`: `fun_prop` certificate showing
  that the encoded pairing of polynomial-time computed elements is computable in polynomial time
  (original infrastructure).

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 15.4 (Definition 15.2 and (15.7), p. 625).
-/

public section

namespace Cslib.Crypto

open Turing.MultiTapeTM

namespace PrimeOrderGroupFamily

/-- A further family of cyclic groups over the public parameters of `F`: for each `d : F.Desc` a
group `Carrier d` of the same prime order `F.order d`, with its own generator, encoding and
polynomial-time operations on encoded elements. The second source group and the target group of a
pairing are companions of the first source group. -/
structure Companion (F : PrimeOrderGroupFamily) where
  /-- The groups, written additively. -/
  Carrier : F.Desc → Type
  /-- Each group is commutative. -/
  [addCommGroup : ∀ d, AddCommGroup (Carrier d)]
  /-- Each group is a `ZMod q`-module, where `q` is its order. -/
  [module : ∀ d, Module (ZMod (F.order d)) (Carrier d)]
  /-- The generator of each group. -/
  generator : ∀ d, Carrier d
  /-- Each group has `q` elements. -/
  card_carrier : ∀ d, Nat.card (Carrier d) = F.order d
  /-- The generator is not the identity, so it generates the group of prime order. -/
  generator_ne_zero : ∀ d, generator d ≠ 0
  /-- Group elements as words. -/
  encode : ∀ d, Carrier d → List Bool
  /-- Distinct elements have distinct encodings. -/
  encode_injective : ∀ d, Function.Injective (encode d)
  /-- Addition of encoded elements. -/
  add : F.Desc × List Bool × List Bool → List Bool
  /-- `add` adds encoded elements. -/
  add_encode : ∀ d x y, add (d, encode d x, encode d y) = encode d (x + y)
  /-- Multiplication of an encoded element by a natural number. -/
  smul : F.Desc × ℕ × List Bool → List Bool
  /-- `smul` multiplies encoded elements by natural numbers. -/
  smul_encode : ∀ d (a : ℕ) x, smul (d, a, encode d x) = encode d ((a : ZMod (F.order d)) • x)
  /-- The encoded generator is computable in polynomial time from the public group parameters. -/
  computableInPolyTime_generator :
    ComputableInPolyTime (fun d => encode d (generator d)) F.encDesc encBits
  /-- Addition is computable in polynomial time. -/
  computableInPolyTime_add :
    ComputableInPolyTime add (encDescBitsPair F.encDesc) encBits
  /-- Multiplication by a binary natural number is computable in polynomial time. -/
  computableInPolyTime_smul :
    ComputableInPolyTime smul (encPair F.encDesc (encPair encNat encBits)) encBits

attribute [instance] Companion.addCommGroup Companion.module

variable {F : PrimeOrderGroupFamily}

/-- Equality of elements of a companion, decided on their injective encodings. -/
instance (C : F.Companion) (d : F.Desc) : DecidableEq (C.Carrier d) := fun x y =>
  decidable_of_iff (C.encode d x = C.encode d y) (C.encode_injective d).eq_iff

/-- A companion of `F` as a prime-order group family of its own, with the parameters, their
encoding and the orders of `F`. The assumptions `DiscreteLog`, `CDH` and `DDH` for a companion are
those of `C.toFamily`. -/
abbrev Companion.toFamily (C : F.Companion) : PrimeOrderGroupFamily where
  Desc := F.Desc
  encDesc := F.encDesc
  order := F.order
  prime_order := F.prime_order
  Carrier := C.Carrier
  addCommGroup := C.addCommGroup
  module := C.module
  generator := C.generator
  card_carrier := C.card_carrier
  generator_ne_zero := C.generator_ne_zero
  encode := C.encode
  encode_injective := C.encode_injective
  add := C.add
  add_encode := C.add_encode
  smul := C.smul
  smul_encode := C.smul_encode
  computableInPolyTime_order := F.computableInPolyTime_order
  computableInPolyTime_generator := C.computableInPolyTime_generator
  computableInPolyTime_add := C.computableInPolyTime_add
  computableInPolyTime_smul := C.computableInPolyTime_smul

variable (F) in
/-- `F` as a companion of itself: the same groups, generators, encodings and operations. A pairing
`P` is symmetric when `P.G₁ = P.G₀.self`. -/
abbrev self : F.Companion where
  Carrier := F.Carrier
  addCommGroup := F.addCommGroup
  module := F.module
  generator := F.generator
  card_carrier := F.card_carrier
  generator_ne_zero := F.generator_ne_zero
  encode := F.encode
  encode_injective := F.encode_injective
  add := F.add
  add_encode := F.add_encode
  smul := F.smul
  smul_encode := F.smul_encode
  computableInPolyTime_generator := F.computableInPolyTime_generator
  computableInPolyTime_add := F.computableInPolyTime_add
  computableInPolyTime_smul := F.computableInPolyTime_smul

namespace Companion

variable (C : F.Companion) {α : Type} {enc : α ↪ List Bool} {d : α → F.Desc}

/-- The encoded generator of a companion at computed group parameters. -/
@[fun_prop] theorem computableInPolyTime_encode_generator
    (hd : ComputableInPolyTime d enc F.encDesc) :
    ComputableInPolyTime (fun a => C.encode (d a) (C.generator (d a))) enc encBits :=
  PrimeOrderGroupFamily.computableInPolyTime_encode_generator (F := C.toFamily) hd

/-- The encoded identity of a companion at computed group parameters. -/
@[fun_prop] theorem computableInPolyTime_encode_zero
    (hd : ComputableInPolyTime d enc F.encDesc) :
    ComputableInPolyTime (fun a => C.encode (d a) 0) enc encBits :=
  PrimeOrderGroupFamily.computableInPolyTime_encode_zero (F := C.toFamily) hd

/-- The encoded sum of computed elements of a companion. -/
@[fun_prop] theorem computableInPolyTime_encode_add {x y : (a : α) → C.Carrier (d a)}
    (hd : ComputableInPolyTime d enc F.encDesc)
    (hx : ComputableInPolyTime (fun a => C.encode (d a) (x a)) enc encBits)
    (hy : ComputableInPolyTime (fun a => C.encode (d a) (y a)) enc encBits) :
    ComputableInPolyTime (fun a => C.encode (d a) (x a + y a)) enc encBits :=
  PrimeOrderGroupFamily.computableInPolyTime_encode_add (F := C.toFamily) hd hx hy

/-- The encoded multiple of a computed element of a companion by a computed natural number. -/
@[fun_prop] theorem computableInPolyTime_encode_natCast_smul {k : α → ℕ}
    {x : (a : α) → C.Carrier (d a)} (hd : ComputableInPolyTime d enc F.encDesc)
    (hk : ComputableInPolyTime k enc encNat)
    (hx : ComputableInPolyTime (fun a => C.encode (d a) (x a)) enc encBits) :
    ComputableInPolyTime (fun a => C.encode (d a) ((k a : ZMod (F.order (d a))) • x a)) enc
      encBits :=
  PrimeOrderGroupFamily.computableInPolyTime_encode_natCast_smul (F := C.toFamily) hd hk hx

end Companion

end PrimeOrderGroupFamily

/-- Supporting algebraic step for `bilinearOfSmulGenerator` (after [BonehShoup2023], Section 15.4,
equation (15.7), p. 625): between `ZMod q`-modules generated by `g₀` and `g₁`, a map `e` is
additive in each argument if and only if `e (α • g₀) (β • g₁) = (α * β) • e g₀ g₁` for all `α` and
`β`. -/
theorem biadditive_iff_apply_smul_generator {G₀ G₁ GT : Type*} [AddCommGroup G₀] [AddCommGroup G₁]
    [AddCommGroup GT] {q : ℕ} [Module (ZMod q) G₀] [Module (ZMod q) G₁] [Module (ZMod q) GT]
    {g₀ : G₀} {g₁ : G₁} (h₀ : Function.Surjective fun α : ZMod q => α • g₀)
    (h₁ : Function.Surjective fun β : ZMod q => β • g₁) (e : G₀ → G₁ → GT) :
    ((∀ u u' v, e (u + u') v = e u v + e u' v) ∧ ∀ u v v', e u (v + v') = e u v + e u v') ↔
      ∀ α β : ZMod q, e (α • g₀) (β • g₁) = (α * β) • e g₀ g₁ := by
  refine ⟨fun ⟨hleft, hright⟩ α β => ?_, fun h => ⟨fun u u' v => ?_, fun u v v' => ?_⟩⟩
  · -- An additive map between `ZMod q`-modules commutes with scalars.
    have hα := ZMod.map_smul (AddMonoidHom.mk' (e · (β • g₁)) (hleft · · _)) α g₀
    have hβ := ZMod.map_smul (AddMonoidHom.mk' (e g₀) (hright g₀)) β g₁
    simp only [AddMonoidHom.mk'_apply] at hα hβ
    rw [hα, hβ, mul_smul]
  · obtain ⟨α, rfl⟩ := h₀ u
    obtain ⟨α', rfl⟩ := h₀ u'
    obtain ⟨β, rfl⟩ := h₁ v
    simp only [← add_smul, h, add_mul]
  · obtain ⟨α, rfl⟩ := h₀ u
    obtain ⟨β, rfl⟩ := h₁ v
    obtain ⟨β', rfl⟩ := h₁ v'
    simp only [← add_smul, h, mul_add]

/-- Construct a `ZMod q`-bilinear map between `ZMod q`-modules generated by `g₀` and `g₁` from a
plain function `e` satisfying the generator product rule `e (α • g₀) (β • g₁) = (α * β) • e g₀ g₁`
(after [BonehShoup2023], Section 15.4, equation (15.7), p. 625). -/
def bilinearOfSmulGenerator {G₀ G₁ GT : Type*} [AddCommGroup G₀] [AddCommGroup G₁]
    [AddCommGroup GT] {q : ℕ} [Module (ZMod q) G₀] [Module (ZMod q) G₁] [Module (ZMod q) GT]
    {g₀ : G₀} {g₁ : G₁} (h₀ : Function.Surjective fun α : ZMod q => α • g₀)
    (h₁ : Function.Surjective fun β : ZMod q => β • g₁) (e : G₀ → G₁ → GT)
    (he : ∀ α β : ZMod q, e (α • g₀) (β • g₁) = (α * β) • e g₀ g₁) :
    G₀ →ₗ[ZMod q] G₁ →ₗ[ZMod q] GT :=
  let hadd := (biadditive_iff_apply_smul_generator h₀ h₁ e).mpr he
  LinearMap.mk₂ (ZMod q) e hadd.1
    (fun c u v => ZMod.map_smul (AddMonoidHom.mk' (e · v) (hadd.1 · · v)) c u)
    hadd.2
    (fun c u v => ZMod.map_smul (AddMonoidHom.mk' (e u) (hadd.2 u)) c v)

/-- Evaluating `bilinearOfSmulGenerator` recovers the underlying function `e`. -/
@[simp] theorem bilinearOfSmulGenerator_apply {G₀ G₁ GT : Type*} [AddCommGroup G₀]
    [AddCommGroup G₁] [AddCommGroup GT] {q : ℕ} [Module (ZMod q) G₀] [Module (ZMod q) G₁]
    [Module (ZMod q) GT] {g₀ : G₀} {g₁ : G₁}
    (h₀ : Function.Surjective fun α : ZMod q => α • g₀)
    (h₁ : Function.Surjective fun β : ZMod q => β • g₁) (e : G₀ → G₁ → GT)
    (he : ∀ α β : ZMod q, e (α • g₀) (β • g₁) = (α * β) • e g₀ g₁) (u : G₀) (v : G₁) :
    bilinearOfSmulGenerator h₀ h₁ e he u v = e u v := by
  dsimp only [bilinearOfSmulGenerator]
  exact LinearMap.mk₂_apply _ _ u v

/-- A family of pairing groups ([BonehShoup2023], Section 15.4, Definition 15.2, p. 625): for each
choice of public parameters `d`, groups `G₀ d`, `G₁ d` and `GT d` of the same prime order `q` with
generators `g₀`, `g₁` and `gT`, and a bilinear map `pair d : G₀ d → G₁ d → GT d` with
`pair d g₀ g₁ = gT`, computable in polynomial time on encodings.

The source groups are `G₀` and `G₁` and the target group is `GT`. Groups are written additively,
so bilinearity is linearity over `ZMod q` in each argument. The source names `e(g₀, g₁)` as the
generator `gT` of the target group; here `GT` carries a generator, which its polynomial-time
operations use, and `pair_generator` states that it is the pairing of the two generators. -/
structure PairingGroupFamily where
  /-- The first source group, which fixes the public parameters and the order. -/
  G₀ : PrimeOrderGroupFamily
  /-- The second source group. -/
  G₁ : G₀.Companion
  /-- The target group. -/
  GT : G₀.Companion
  /-- The pairing, bilinear over `ZMod q`. -/
  pair : ∀ d, G₀.Carrier d →ₗ[ZMod (G₀.order d)] G₁.Carrier d →ₗ[ZMod (G₀.order d)] GT.Carrier d
  /-- Non-degeneracy: the pairing of the two generators is the generator of the target group. -/
  pair_generator : ∀ d, pair d (G₀.generator d) (G₁.generator d) = GT.generator d
  /-- The pairing on encoded elements. -/
  pairEncoded : G₀.Desc × List Bool × List Bool → List Bool
  /-- `pairEncoded` pairs encoded elements. -/
  pairEncoded_encode : ∀ d u v,
    pairEncoded (d, G₀.encode d u, G₁.encode d v) = GT.encode d (pair d u v)
  /-- The pairing is computable in polynomial time. -/
  computableInPolyTime_pairEncoded :
    ComputableInPolyTime pairEncoded (encDescBitsPair G₀.encDesc) encBits

namespace PairingGroupFamily

private theorem pair_generator_of_smul {G₀ : PrimeOrderGroupFamily} {G₁ GT : G₀.Companion}
    {pair : ∀ d, G₀.Carrier d → G₁.Carrier d → GT.Carrier d}
    (hpair : ∀ d (α β : ZMod (G₀.order d)),
      pair d (α • G₀.generator d) (β • G₁.generator d) = (α * β) • GT.generator d)
    (d : G₀.Desc) :
    pair d (G₀.generator d) (G₁.generator d) = GT.generator d := by
  simpa only [one_smul, one_mul] using hpair d 1 1

/-- Construct a `PairingGroupFamily` from a plain pairing function `pair` satisfying the generator
product rule `pair d (α • g₀) (β • g₁) = (α * β) • gT` (after [BonehShoup2023], Section 15.4,
equation (15.7), p. 625), deriving `ZMod q`-bilinearity via `bilinearOfSmulGenerator` and
`pair_generator` at `α = β = 1`. -/
abbrev ofSmulGenerator (G₀ : PrimeOrderGroupFamily) (G₁ GT : G₀.Companion)
    (pair : ∀ d, G₀.Carrier d → G₁.Carrier d → GT.Carrier d)
    (hpair : ∀ d (α β : ZMod (G₀.order d)),
      pair d (α • G₀.generator d) (β • G₁.generator d) = (α * β) • GT.generator d)
    (pairEncoded : G₀.Desc × List Bool × List Bool → List Bool)
    (pairEncoded_encode : ∀ d u v,
      pairEncoded (d, G₀.encode d u, G₁.encode d v) = GT.encode d (pair d u v))
    (computableInPolyTime_pairEncoded :
      ComputableInPolyTime pairEncoded (encDescBitsPair G₀.encDesc) encBits) :
    PairingGroupFamily where
  G₀ := G₀
  G₁ := G₁
  GT := GT
  pair d := bilinearOfSmulGenerator (G₀.smul_generator_surjective d)
    (G₁.toFamily.smul_generator_surjective d) (pair d) fun α β => by
      dsimp only [PrimeOrderGroupFamily.Companion.toFamily]
      rw [hpair d α β, pair_generator_of_smul hpair d]
  pair_generator d := by
    rw [bilinearOfSmulGenerator_apply, pair_generator_of_smul hpair d]
  pairEncoded := pairEncoded
  pairEncoded_encode d u v := by
    rw [bilinearOfSmulGenerator_apply]
    exact pairEncoded_encode d u v
  computableInPolyTime_pairEncoded := computableInPolyTime_pairEncoded

variable (P : PairingGroupFamily)

/-- Scalars of both arguments of a pairing multiply: the source's
`e(u ^ α, v ^ β) = e(u, v) ^ (α · β)`. -/
theorem pair_smul_smul {d : P.G₀.Desc} (α β : ZMod (P.G₀.order d)) (u : P.G₀.Carrier d)
    (v : P.G₁.Carrier d) : P.pair d (α • u) (β • v) = (α * β) • P.pair d u v := by
  rw [LinearMap.map_smul₂, map_smul, smul_smul]

/-- The identity `e(g₀ ^ α, g₁ ^ β) = e(g₀, g₁) ^ (α · β)` of [BonehShoup2023], (15.7), first
equality (p. 625), with `e(g₀, g₁)` written as the generator of the target group. -/
theorem pair_smul_generator_smul_generator {d : P.G₀.Desc} (α β : ZMod (P.G₀.order d)) :
    P.pair d (α • P.G₀.generator d) (β • P.G₁.generator d) = (α * β) • P.GT.generator d := by
  rw [pair_smul_smul, P.pair_generator]

/-- The pairing of the two generators is not the identity of the target group. -/
theorem pair_generator_ne_zero {d : P.G₀.Desc} :
    P.pair d (P.G₀.generator d) (P.G₁.generator d) ≠ 0 :=
  P.pair_generator d ▸ P.GT.generator_ne_zero d

/-- The encoded pairing of computed elements. -/
@[fun_prop] theorem computableInPolyTime_encode_pair {α : Type} {enc : α ↪ List Bool}
    {d : α → P.G₀.Desc} {u : (a : α) → P.G₀.Carrier (d a)} {v : (a : α) → P.G₁.Carrier (d a)}
    (hd : ComputableInPolyTime d enc P.G₀.encDesc)
    (hu : ComputableInPolyTime (fun a => P.G₀.encode (d a) (u a)) enc encBits)
    (hv : ComputableInPolyTime (fun a => P.G₁.encode (d a) (v a)) enc encBits) :
    ComputableInPolyTime (fun a => P.GT.encode (d a) (P.pair (d a) (u a) (v a))) enc encBits :=
  .of_enc_eq (P.computableInPolyTime_pairEncoded.comp (hd.prod (hu.prod hv))) fun a => by
    simp [P.pairEncoded_encode]

end PairingGroupFamily

end Cslib.Crypto
