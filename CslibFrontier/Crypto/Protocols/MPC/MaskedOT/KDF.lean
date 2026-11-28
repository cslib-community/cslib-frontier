/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.ElGamal
public import CslibFrontier.Crypto.Protocols.MPC.MaskedOT
public import CslibFrontier.Languages.Probabilistic.BitString

/-!
# The masked oblivious transfer with a key-derivation mask

Over a `PrimeOrderGroupFamily` `F` with a key-derivation function
`H : F.Desc × List Bool → List Bool`, this module instantiates the masked transfer `maskedOT` of
`CslibFrontier/Crypto/Protocols/MPC/MaskedOT.lean` with pads in the group `F.Carrier d` and values
in `List Bool`: the mask `F.kdfMask H d r m` is the xor of the word `m` with the key
`H (d, F.encode d r)` derived from the pad `r`, and the sender's pads `F.kdfPads d` are
`c₀ • g` and `c₁ • g` for independent uniform exponents. It then identifies the pad-hiding
experiments of a corrupted receiver with the key-derivation experiments `F.kdfRealGame` and
`F.kdfIdealGame` of `CslibFrontier/Crypto/Computational/ElGamal.lean` ([BonehShoup2023],
Section 11.5.2, Attack Game 11.3), run with an explicit distinguisher. This is original library
infrastructure; no cited theorem is claimed.

## What is proved

All statements are concrete, in the hybrid model with the ideal pad transfer
`otWorld (F.Carrier d)`. All but the last are exact, with exponents drawn exactly uniformly from
`ZMod (F.order d)`.

* `F.kdfMask H d r` is its own inverse on words of the length of the key `H (d, F.encode d r)`
  (`kdfMask_kdfMask`).
* For every setup law, family of inputs `x` and family of distinguishers `D`, the real
  key-derivation game of the explicit distinguisher `F.maskedOTReceiverToKDFDistinguisher H x D`
  *is* the experiment that gives `maskedOTPadTest` the receiver's pad and the sender's unchosen
  value masked by the other pad (`kdfRealGame_maskedOTReceiverToKDFDistinguisher`), and its ideal
  key-derivation game *is* the experiment that gives it the receiver's pad and a uniform
  `msgLen n`-bit word (`kdfIdealGame_maskedOTReceiverToKDFDistinguisher`). Neither needs a
  hypothesis.
* Hence, at fixed group parameters `d`, when the keys and the receiver's output have length
  `msgLen n`, the semi-honest advantage of `D n d` against a corrupted receiver, with the simulator
  `maskedOTReceiverSim` that fills the unchosen component with a uniform `msgLen n`-bit word,
  *equals* the key-derivation advantage of `F.maskedOTReceiverToKDFDistinguisher H x D` under the
  setup that returns `d` (`semiHonestAdvantage_kdfMaskedOT_receiver_eq_kdf`).
* For every setup law and every sampled environment `E` of the masked transfer, a program that
  either decides a bit or stops at a `Composition.RoundChallenge`, whose challenges corrupt the
  receiver: the game `Composition.roundGame` on the ideal joint distribution, under the sampled
  setup and environment, *is* `F.kdfIdealGame` of the one distinguisher
  `F.roundEnvToKDFDistinguisher H E` (`bind_roundGame_idealJoint_kdfMaskedOT_eq_kdfIdealGame`),
  and, when the keys and the receiver's outputs have length `msgLen n` on the support of the
  setup, the game on the real joint distribution *is* its `F.kdfRealGame`
  (`bind_roundGame_realJoint_kdfMaskedOT_eq_kdfRealGame`). Hence the two advantages are equal,
  with the absolute value outside the expectation over the setup and the environment
  (`advantage_bind_roundGame_kdfMaskedOT_eq_kdf`).
* When the pads are drawn by any sampler within `ε` of the exactly uniform pads against every
  test, such as pads with fair-coin exponents, the advantage between the two round games of that
  masked transfer is at most the same key-derivation advantage plus `ε + ε`
  (`advantage_bind_roundGame_kdfMaskedOT_le_kdf`).

## What is not proved

* No efficiency statement: neither `F.maskedOTReceiverToKDFDistinguisher H x D` nor
  `F.roundEnvToKDFDistinguisher H E` is shown to be uniform strict PPT
  (`KDFDistinguisher.IsPPT`) when `x`, `D` and `E` are efficient, so `F.SecureKDF` is not applied
  and no negligible bound is derived.
* No asymptotic statement (`ProtocolFamily.SemiHonestSecure`) is made. The equality of semi-honest
  advantages is for the point setup at a fixed `d`; under a setup law only the round games of a
  sampled environment are identified; they are used for a composed protocol in
  `CslibFrontier/Crypto/Protocols/MPC/Yao/PlainDDHOT/DrawnTransfer.lean`.
* The pads `F.kdfPads d` are sampled with exactly uniform exponents (`ProbComp.uniform`). No
  fair-coin sampler is defined here; the fair-coin pads `F.kdfPadsProb n d` and their distance
  from `F.kdfPads d` are in `CslibFrontier/Crypto/Protocols/MPC/MaskedOT/KDFDDHProb.lean`.
* The pad transfer is ideal. Substituting a protocol for it, for one distinguisher, is
  `semiHonestAdvantage_maskedOT_compose_le_transfer` in
  `CslibFrontier/Crypto/Protocols/MPC/MaskedOT/DDH.lean`.
* The locator for [BonehShoup2023] is the one recorded in
  `CslibFrontier/Crypto/Computational/ElGamal.lean`; it was not re-verified against the source.

## Main definitions

* `Cslib.Crypto.PrimeOrderGroupFamily.kdfMask`: the xor with the key derived from a pad.
* `Cslib.Crypto.PrimeOrderGroupFamily.kdfPads`: two pads with independent uniform exponents.
* `Cslib.Crypto.PrimeOrderGroupFamily.maskedOTReceiverToKDFDistinguisher`: the reduction from a
  distinguisher of a corrupted receiver's view to a key-derivation distinguisher.
* `Cslib.Crypto.PrimeOrderGroupFamily.roundEnvToKDFDistinguisher`: the key-derivation
  distinguisher that samples an environment of the masked transfer and runs the reduction on its
  challenge.

## Main results

* `Cslib.Crypto.PrimeOrderGroupFamily.kdfRealGame_maskedOTReceiverToKDFDistinguisher`,
  `Cslib.Crypto.PrimeOrderGroupFamily.kdfIdealGame_maskedOTReceiverToKDFDistinguisher`: the
  key-derivation games of the reduction are the two pad-hiding experiments.
* `Cslib.Crypto.PrimeOrderGroupFamily.semiHonestAdvantage_kdfMaskedOT_receiver_eq_kdf`: at fixed
  group parameters, the advantage against a corrupted receiver is the key-derivation advantage of
  the reduction.
* `Cslib.Crypto.PrimeOrderGroupFamily.bind_roundGame_idealJoint_kdfMaskedOT_eq_kdfIdealGame`,
  `Cslib.Crypto.PrimeOrderGroupFamily.bind_roundGame_realJoint_kdfMaskedOT_eq_kdfRealGame`: under
  a sampled setup, the two round games of a sampled environment are the key-derivation games of
  `roundEnvToKDFDistinguisher`.
* `Cslib.Crypto.PrimeOrderGroupFamily.advantage_bind_roundGame_kdfMaskedOT_eq_kdf`: hence the
  round-game advantage of the environment is the key-derivation advantage of that distinguisher.
* `Cslib.Crypto.PrimeOrderGroupFamily.advantage_bind_roundGame_kdfMaskedOT_le_kdf`: with pads drawn
  by a sampler within `ε` of the exactly uniform pads, such as pads with fair-coin exponents, the
  round-game advantage is at most that key-derivation advantage plus `ε + ε`.

## References

* [D. Boneh and V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 11.5.2 (Attack Game 11.3), as formalized by `kdfRealGame`
  and `kdfIdealGame`.
-/

public section

namespace Cslib.Crypto.PrimeOrderGroupFamily

open Cslib Cslib.Probability Cslib.Crypto.Protocols.MPC
open scoped NNReal

variable (F : PrimeOrderGroupFamily)

/-! ### The mask, the pads and the reduction -/

/-- The key-derivation mask at group parameters `d`: `F.kdfMask H d r m` is the xor
`Cslib.BitString.listXor key.length [key, m]` of the word `m` with the key
`key = H (d, F.encode d r)` derived from the pad `r`, at the width of the key. On words of that
length it is its own inverse (`kdfMask_kdfMask`). -/
@[expose] def kdfMask (H : F.Desc × List Bool → List Bool) (d : F.Desc) :
    F.Carrier d → List Bool → List Bool :=
  fun r m => Cslib.BitString.listXor (H (d, F.encode d r)).length [H (d, F.encode d r), m]

/-- Masking twice with the key derived from the same pad recovers a word of the key's length. -/
theorem kdfMask_kdfMask (H : F.Desc × List Bool → List Bool) (d : F.Desc) (r : F.Carrier d)
    {m : List Bool} (hm : m.length = (H (d, F.encode d r)).length) :
    F.kdfMask H d r (F.kdfMask H d r m) = m :=
  Cslib.BitString.listXor_pair_self_left_of_length _ hm

/-- The sender's pads at group parameters `d`: `c₀ • g` and `c₁ • g` for the generator `g` and
independent uniform exponents `c₀, c₁ : ZMod (F.order d)`. -/
@[expose] noncomputable def kdfPads (d : F.Desc) : ProbComp (F.Carrier d × F.Carrier d) := do
  let c₀ ← ProbComp.uniform (ZMod (F.order d))
  let c₁ ← ProbComp.uniform (ZMod (F.order d))
  return (c₀ • F.generator d, c₁ • F.generator d)

/-- **The reduction from a corrupted receiver's distinguisher to a key-derivation
distinguisher.** Given the group parameters `d`, a group element `u` and a candidate key `key`
(its second group element is ignored), it runs the pad test `maskedOTPadTest` of the inputs
`x n d` and the distinguisher `D n d` with `u` as the receiver's pad and, as the candidate for
the masked unchosen value, the sender's unchosen value xored with `key` via
`Cslib.BitString.listXor key.length [key, _]`. -/
@[expose] def maskedOTReceiverToKDFDistinguisher (H : F.Desc × List Bool → List Bool)
    (x : (n : ℕ) → (d : F.Desc) → (i : Fin 2) → OTIn (List Bool) i)
    (D : (n : ℕ) → (d : F.Desc) →
      ((i : ({1} : Finset (Fin 2))) → PartyView (OTIn (List Bool)) (MaskedOTCoins (F.Carrier d))
          (maskedOTSchedule (F.Carrier d) (List Bool)) i) ×
        ((i : Fin 2) → OTOut (List Bool) i) → ProbComp Bool) :
    F.KDFDistinguisher :=
  fun n d u _ key =>
    let σ : Bool := x n d 1
    maskedOTPadTest (F.kdfMask H d) (x n d) (D n d) u
      (Cslib.BitString.listXor key.length [key, if σ then (x n d 0).1 else (x n d 0).2])

/-! ### The key-derivation games of the reduction -/

/-- At fixed group parameters, the pad test on a uniform pad and the xor of a uniform key with the
sender's unchosen value is the ideal pad-hiding experiment. -/
private theorem bind_eval_maskedOTPadTest_uniformList (H : F.Desc × List Bool → List Bool)
    (len : ℕ) (d : F.Desc) (x : (i : Fin 2) → OTIn (List Bool) i)
    (D : ((i : ({1} : Finset (Fin 2))) → PartyView (OTIn (List Bool)) (MaskedOTCoins (F.Carrier d))
        (maskedOTSchedule (F.Carrier d) (List Bool)) i) ×
      ((i : Fin 2) → OTOut (List Bool) i) → ProbComp Bool) :
    ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun a =>
      (PMF.uniformOfFintype (ZMod (F.order d))).bind fun _ =>
        (Cslib.BitString.uniformList len).bind fun key =>
          ProbComp.eval (
            let σ : Bool := x 1
            maskedOTPadTest (F.kdfMask H d) x D (a • F.generator d)
              (Cslib.BitString.listXor key.length [key, if σ then (x 0).1 else (x 0).2]))) =
      ProbComp.eval (do
        let r ← F.kdfPads d
        let u ← Cslib.BitString.sampleList len
        let σ : Bool := x 1
        maskedOTPadTest (F.kdfMask H d) x D (if σ then r.2 else r.1) u) := by
  have hpad (w : List Bool) (f : List Bool → PMF Bool) :
      ((Cslib.BitString.uniformList len).bind fun key =>
        f (Cslib.BitString.listXor key.length [key, w])) =
        (Cslib.BitString.uniformList len).bind f := by
    simpa only [PMF.bind_map, Function.comp_def] using
      congrArg (·.bind f) (Cslib.BitString.uniformList_map_listXor_length len w)
  simp only [kdfPads, bind_assoc, pure_bind, ProbComp.eval_bind, ProbComp.eval_uniform,
    Cslib.BitString.eval_sampleList]
  cases hσ : (x 1 : Bool) <;> simp only [Bool.false_eq_true, ↓reduceIte, PMF.bind_const] <;>
    exact congrArg (PMF.bind _) (funext fun a => hpad _ fun u => ProbComp.eval
      (maskedOTPadTest (F.kdfMask H d) x D (a • F.generator d) u))

/-- At fixed group parameters, the pad test on a uniform pad and the xor of the key derived from
an independent uniform pad with the sender's unchosen value is the real pad-hiding experiment. -/
private theorem bind_eval_maskedOTPadTest_key (H : F.Desc × List Bool → List Bool)
    (d : F.Desc) (x : (i : Fin 2) → OTIn (List Bool) i)
    (D : ((i : ({1} : Finset (Fin 2))) → PartyView (OTIn (List Bool)) (MaskedOTCoins (F.Carrier d))
        (maskedOTSchedule (F.Carrier d) (List Bool)) i) ×
      ((i : Fin 2) → OTOut (List Bool) i) → ProbComp Bool) :
    ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun a =>
      (PMF.uniformOfFintype (ZMod (F.order d))).bind fun _ =>
        (PMF.uniformOfFintype (ZMod (F.order d))).bind fun c =>
          ProbComp.eval (
            let σ : Bool := x 1
            maskedOTPadTest (F.kdfMask H d) x D (a • F.generator d)
              (Cslib.BitString.listXor (H (d, F.encode d (c • F.generator d))).length
                [H (d, F.encode d (c • F.generator d)), if σ then (x 0).1 else (x 0).2]))) =
      ProbComp.eval (do
        let r ← F.kdfPads d
        let σ : Bool := x 1
        maskedOTPadTest (F.kdfMask H d) x D (if σ then r.2 else r.1)
          (if σ then F.kdfMask H d r.1 (x 0).1 else F.kdfMask H d r.2 (x 0).2)) := by
  simp only [kdfPads, bind_assoc, pure_bind, ProbComp.eval_bind, ProbComp.eval_uniform]
  cases hσ : (x 1 : Bool)
  · simp only [Bool.false_eq_true, ↓reduceIte, PMF.bind_const, kdfMask]
  · simp only [↓reduceIte, PMF.bind_const, kdfMask]
    exact PMF.bind_comm _ _ _

/-- **The real key-derivation game of the reduction is the real pad-hiding experiment.** For
every setup law, `F.kdfRealGame` run with `F.maskedOTReceiverToKDFDistinguisher H x D` draws
`d ← setup n` and the pads `r ← F.kdfPads d`, and gives the pad test the receiver's pad and the
sender's unchosen value masked by the other pad: at each `d` this is the second experiment of
`semiHonestAdvantage_maskedOT_receiver_eq` for `F.kdfMask H d` and `F.kdfPads d`. The receiver's
pad plays the role of the first group element of the key-derivation game and the other pad that
of the element the key is derived from. -/
theorem kdfRealGame_maskedOTReceiverToKDFDistinguisher (setup : ℕ → PMF F.Desc)
    (H : F.Desc × List Bool → List Bool)
    (x : (n : ℕ) → (d : F.Desc) → (i : Fin 2) → OTIn (List Bool) i)
    (D : (n : ℕ) → (d : F.Desc) →
      ((i : ({1} : Finset (Fin 2))) → PartyView (OTIn (List Bool)) (MaskedOTCoins (F.Carrier d))
          (maskedOTSchedule (F.Carrier d) (List Bool)) i) ×
        ((i : Fin 2) → OTOut (List Bool) i) → ProbComp Bool) (n : ℕ) :
    F.kdfRealGame setup H (F.maskedOTReceiverToKDFDistinguisher H x D) n =
      (do
        let d ← setup n
        ProbComp.eval (do
          let r ← F.kdfPads d
          let σ : Bool := x n d 1
          maskedOTPadTest (F.kdfMask H d) (x n d) (D n d) (if σ then r.2 else r.1)
            (if σ then F.kdfMask H d r.1 (x n d 0).1 else F.kdfMask H d r.2 (x n d 0).2)) :
        Game) := by
  simp only [kdfRealGame, maskedOTReceiverToKDFDistinguisher, PMF.monad_bind_eq_bind]
  exact congrArg (PMF.bind _) (funext fun d =>
    F.bind_eval_maskedOTPadTest_key H d (x n d) (D n d))

/-- **The ideal key-derivation game of the reduction is the ideal pad-hiding experiment.** For
every setup law, `F.kdfIdealGame` run with `F.maskedOTReceiverToKDFDistinguisher H x D` draws
`d ← setup n`, the pads `r ← F.kdfPads d` and a uniform `msgLen n`-bit word, and gives the pad
test the receiver's pad and that word: at each `d` this is the first experiment of
`semiHonestAdvantage_maskedOT_receiver_eq` for `F.kdfMask H d`, `F.kdfPads d` and the sampler
`Cslib.BitString.sampleList (msgLen n)`. The xor of a uniform key with the sender's unchosen
value is uniform, whatever the length of that value. -/
theorem kdfIdealGame_maskedOTReceiverToKDFDistinguisher (setup : ℕ → PMF F.Desc)
    (H : F.Desc × List Bool → List Bool) (msgLen : ℕ → ℕ)
    (x : (n : ℕ) → (d : F.Desc) → (i : Fin 2) → OTIn (List Bool) i)
    (D : (n : ℕ) → (d : F.Desc) →
      ((i : ({1} : Finset (Fin 2))) → PartyView (OTIn (List Bool)) (MaskedOTCoins (F.Carrier d))
          (maskedOTSchedule (F.Carrier d) (List Bool)) i) ×
        ((i : Fin 2) → OTOut (List Bool) i) → ProbComp Bool) (n : ℕ) :
    F.kdfIdealGame setup msgLen (F.maskedOTReceiverToKDFDistinguisher H x D) n =
      (do
        let d ← setup n
        ProbComp.eval (do
          let r ← F.kdfPads d
          let u ← Cslib.BitString.sampleList (msgLen n)
          let σ : Bool := x n d 1
          maskedOTPadTest (F.kdfMask H d) (x n d) (D n d) (if σ then r.2 else r.1) u) :
        Game) := by
  simp only [kdfIdealGame, maskedOTReceiverToKDFDistinguisher, PMF.monad_bind_eq_bind]
  exact congrArg (PMF.bind _) (funext fun d =>
    F.bind_eval_maskedOTPadTest_uniformList H (msgLen n) d (x n d) (D n d))

/-! ### A corrupted receiver at fixed group parameters -/

/-- Concrete per-instance step toward #6045 criterion 2, not an asymptotic security theorem; no
efficiency (PPT) certificate for the reduction is proved here. At fixed group parameters `d` and
security parameter `n`, when every key `H (d, F.encode d r)` and the receiver's output (the
sender's chosen value) have length `msgLen n`, the semi-honest advantage of `D n d` against
`maskedOT` with the
key-derivation mask `F.kdfMask H d` and the pads `F.kdfPads d`, with the ideal pad transfer, for
the corrupted receiver `{1}` and the simulator that fills the unchosen component with a uniform
`msgLen n`-bit word, *equals* the advantage of the explicit key-derivation distinguisher
`F.maskedOTReceiverToKDFDistinguisher H x D` between `F.kdfIdealGame` and `F.kdfRealGame` under
the setup that returns `d`. Nothing is assumed about the reduction, and the right-hand side is
not bounded here. -/
theorem semiHonestAdvantage_kdfMaskedOT_receiver_eq_kdf (H : F.Desc × List Bool → List Bool)
    (msgLen : ℕ → ℕ)
    (x : (n : ℕ) → (d : F.Desc) → (i : Fin 2) → OTIn (List Bool) i)
    (D : (n : ℕ) → (d : F.Desc) →
      ((i : ({1} : Finset (Fin 2))) → PartyView (OTIn (List Bool)) (MaskedOTCoins (F.Carrier d))
          (maskedOTSchedule (F.Carrier d) (List Bool)) i) ×
        ((i : Fin 2) → OTOut (List Bool) i) → ProbComp Bool) (n : ℕ) (d : F.Desc)
    (hH : ∀ r : F.Carrier d, (H (d, F.encode d r)).length = msgLen n)
    (hout : (otOutputs (x n d) 1 : List Bool).length = msgLen n) :
    semiHonestAdvantage (maskedOT (F.kdfMask H d) (F.kdfMask H d) (F.kdfPads d))
        (otWorld (F.Carrier d)) (otFunctionality (List Bool)) {1}
        (maskedOTReceiverSim (F.kdfMask H d) (F.kdfPads d)
          (Cslib.BitString.sampleList (msgLen n))) (x n d) (D n d) =
      Game.advantage
        (F.kdfIdealGame (fun _ => PMF.pure d) msgLen
          (F.maskedOTReceiverToKDFDistinguisher H x D) n)
        (F.kdfRealGame (fun _ => PMF.pure d) H
          (F.maskedOTReceiverToKDFDistinguisher H x D) n) := by
  rw [semiHonestAdvantage_maskedOT_receiver_eq (F.kdfMask H d) (F.kdfMask H d) (F.kdfPads d)
      (Cslib.BitString.sampleList (msgLen n)) (x n d)
      (fun r => F.kdfMask_kdfMask H d r (hout.trans (hH r).symm)) (D n d),
    F.kdfIdealGame_maskedOTReceiverToKDFDistinguisher,
    F.kdfRealGame_maskedOTReceiverToKDFDistinguisher]
  simp only [PMF.monad_bind_eq_bind, PMF.pure_bind]

/-! ### The key-derivation games of a sampled environment -/

section RoundEnv

open Cslib.Crypto.Protocols.MPC.Composition

/-- A draw commutes past three earlier independent draws. -/
private theorem bind_bind_bind_comm {α β γ δ ε : Type} (p₁ : PMF α) (p₂ : PMF β) (p₃ : PMF γ)
    (q : PMF δ) (f : α → β → γ → δ → PMF ε) :
    (p₁.bind fun a => p₂.bind fun b => p₃.bind fun c => q.bind fun e => f a b c e) =
      q.bind fun e => p₁.bind fun a => p₂.bind fun b => p₃.bind fun c => f a b c e :=
  (congrArg p₁.bind (funext fun _ => (congrArg p₂.bind (funext fun _ =>
    PMF.bind_comm p₃ q _)).trans (PMF.bind_comm p₂ q _))).trans (PMF.bind_comm p₁ q _)

/-- **The key-derivation distinguisher of a sampled environment of the masked transfer.** Step
toward #6045; original bookkeeping, not a cited construction, and no efficiency certificate
(`KDFDistinguisher.IsPPT`) is proved for it. Given the group parameters `d`, a group element `u`
and a candidate key `key` (its second group element is ignored), it samples the environment
`E n d`. If the environment has already decided a bit, it returns that bit. If the environment
stops at a challenged transfer `c` whose corrupted slots are the receiver `{1}`, it runs the pad
test `maskedOTPadTest` of the query `c.query` and the guessing stage `c.guess` with `u` as the
receiver's pad and, as the candidate for the masked unchosen value, the sender's unchosen value
xored with `key` via `Cslib.BitString.listXor key.length [key, _]`: the program
`F.maskedOTReceiverToKDFDistinguisher` on the sampled challenge. On every other coalition it
returns `false`. -/
@[expose] def roundEnvToKDFDistinguisher (H : F.Desc × List Bool → List Bool)
    (E : (n : ℕ) → (d : F.Desc) → ProbComp (Bool ⊕ RoundChallenge (spec₁ := otSpec (List Bool))
      (fun _ => maskedOTSchedule (F.Carrier d) (List Bool))
      (fun _ => MaskedOTCoins (F.Carrier d)))) : F.KDFDistinguisher :=
  fun n d u _ key => do
    match ← E n d with
    | .inl b => pure b
    | .inr c =>
      if h : c.coalition = ({1} : Finset (Fin 2)) then
        let σ : Bool := c.query 1
        maskedOTPadTest (F.kdfMask H d) c.query
          (fun r => c.guess (fun s => r.1 ⟨s.val, h ▸ s.property⟩, r.2)) u
          (Cslib.BitString.listXor key.length [key, if σ then (c.query 0).1 else (c.query 0).2])
      else pure false

/-- **The ideal round game of a sampled environment is its ideal key-derivation game.** Step
toward #6045; original bookkeeping, not a cited result. Draw `d ← setup n` and a challenge from
the environment `E n d`, and play `Composition.roundGame` on the ideal joint distribution of the
single transfer `otWorld (List Bool)` with the simulators `Sm d`. When `Sm d {1}` is
`maskedOTReceiverSim` with the key-derivation mask `F.kdfMask H d`, the pads `F.kdfPads d`
(exactly uniform exponents, not fair coins) and a uniform `msgLen n`-bit word in the unchosen
component, and every challenge of the environment corrupts the receiver `{1}`, this game *is*
`F.kdfIdealGame setup msgLen` of the one distinguisher `F.roundEnvToKDFDistinguisher H E`. No
length hypothesis is needed, and no efficiency of the distinguisher is claimed. -/
theorem bind_roundGame_idealJoint_kdfMaskedOT_eq_kdfIdealGame (setup : ℕ → PMF F.Desc)
    (H : F.Desc × List Bool → List Bool) (msgLen : ℕ → ℕ) (n : ℕ)
    (Sm : (d : F.Desc) → (J : Finset (Fin 2)) → CoalitionSimulator
      (maskedOTSchedule (F.Carrier d) (List Bool)) (OTIn (List Bool))
      (MaskedOTCoins (F.Carrier d)) (OTOut (List Bool)) J)
    (hSm : ∀ d, Sm d {1} = maskedOTReceiverSim (F.kdfMask H d) (F.kdfPads d)
      (Cslib.BitString.sampleList (msgLen n)))
    (E : (n : ℕ) → (d : F.Desc) → ProbComp (Bool ⊕ RoundChallenge (spec₁ := otSpec (List Bool))
      (fun _ => maskedOTSchedule (F.Carrier d) (List Bool))
      (fun _ => MaskedOTCoins (F.Carrier d))))
    (hE : ∀ d ∈ (setup n).support, ∀ c, Sum.inr c ∈ (ProbComp.eval (E n d)).support →
      c.coalition = ({1} : Finset (Fin 2))) :
    ((setup n).bind fun d => (ProbComp.eval (E n d)).bind
      (roundGame fun op J q =>
        ProbComp.eval (idealJoint (otWorld (List Bool) op) J (Sm d J) q))) =
      F.kdfIdealGame setup msgLen (F.roundEnvToKDFDistinguisher H E) n := by
  simp only [kdfIdealGame, roundEnvToKDFDistinguisher, ProbComp.eval_bind,
    PMF.monad_bind_eq_bind]
  refine PMF.bind_congr_on_support _ _ _ fun d hd => ?_
  rw [bind_bind_bind_comm]
  refine PMF.bind_congr_on_support _ _ _ fun
    | .inl _, _ => by simp only [roundGame, Sum.elim_inl, ProbComp.eval_pure, PMF.bind_const]
    | .inr ⟨_, J, q, g⟩, he => by
      obtain rfl : J = ({1} : Finset (Fin 2)) := hE d hd _ he
      simp only [roundGame, Sum.elim_inr, hSm d, ↓reduceDIte]
      exact (bind_eval_idealJoint_maskedOT_receiver _ _ _ q g).trans
        (F.bind_eval_maskedOTPadTest_uniformList H (msgLen n) d q g).symm

/-- **The real round game of a sampled environment is its real key-derivation game.** Step toward
#6045; original bookkeeping, not a cited result. Draw `d ← setup n` and a challenge from the
environment `E n d`, and play `Composition.roundGame` on the real joint distribution of `maskedOT`
with the key-derivation mask `F.kdfMask H d` and the pads `F.kdfPads d` (exactly uniform
exponents, not fair coins), with the ideal pad transfer `otWorld (F.Carrier d)`. When, for every
`d` in the support of the setup, every key `H (d, F.encode d r)` has length `msgLen n` and every
challenge of the environment corrupts the receiver `{1}` and has a receiver's output of length
`msgLen n`, this game *is* `F.kdfRealGame setup H` of the one distinguisher
`F.roundEnvToKDFDistinguisher H E`. No efficiency of the distinguisher is claimed. -/
theorem bind_roundGame_realJoint_kdfMaskedOT_eq_kdfRealGame (setup : ℕ → PMF F.Desc)
    (H : F.Desc × List Bool → List Bool) (msgLen : ℕ → ℕ) (n : ℕ)
    (E : (n : ℕ) → (d : F.Desc) → ProbComp (Bool ⊕ RoundChallenge (spec₁ := otSpec (List Bool))
      (fun _ => maskedOTSchedule (F.Carrier d) (List Bool))
      (fun _ => MaskedOTCoins (F.Carrier d))))
    (hH : ∀ d ∈ (setup n).support, ∀ r : F.Carrier d, (H (d, F.encode d r)).length = msgLen n)
    (hE : ∀ d ∈ (setup n).support, ∀ c, Sum.inr c ∈ (ProbComp.eval (E n d)).support →
      c.coalition = ({1} : Finset (Fin 2)) ∧
        (otOutputs (M := List Bool) c.query 1 : List Bool).length = msgLen n) :
    ((setup n).bind fun d => (ProbComp.eval (E n d)).bind
      (roundGame fun _ J q =>
        (maskedOT (F.kdfMask H d) (F.kdfMask H d) (F.kdfPads d)).realJoint
          (otWorld (F.Carrier d)) J q)) =
      F.kdfRealGame setup H (F.roundEnvToKDFDistinguisher H E) n := by
  simp only [kdfRealGame, roundEnvToKDFDistinguisher, ProbComp.eval_bind,
    PMF.monad_bind_eq_bind]
  refine PMF.bind_congr_on_support _ _ _ fun d hd => ?_
  rw [bind_bind_bind_comm]
  refine PMF.bind_congr_on_support _ _ _ fun
    | .inl _, _ => by simp only [roundGame, Sum.elim_inl, ProbComp.eval_pure, PMF.bind_const]
    | .inr ⟨_, J, q, g⟩, he => by
      obtain ⟨rfl, hout⟩ : J = ({1} : Finset (Fin 2)) ∧
          (otOutputs (M := List Bool) q 1 : List Bool).length = msgLen n := hE d hd _ he
      simp only [roundGame, Sum.elim_inr, ↓reduceDIte]
      exact (bind_realJoint_maskedOT_receiver _ _ _ q
        (fun r => F.kdfMask_kdfMask H d r (hout.trans (hH d hd r).symm)) g).trans
        (F.bind_eval_maskedOTPadTest_key H d q g).symm

/-- **The round-game advantage of a sampled environment is its key-derivation advantage.** Step
toward #6045; original bookkeeping, not a cited result and not a security theorem: the right-hand
side is not bounded, and no efficiency of `F.roundEnvToKDFDistinguisher H E` is claimed. Under the
hypotheses of `bind_roundGame_idealJoint_kdfMaskedOT_eq_kdfIdealGame` and
`bind_roundGame_realJoint_kdfMaskedOT_eq_kdfRealGame`, the advantage between the ideal and the
real round game of the masked transfer with the ideal pad transfer, under the sampled setup and
the sampled environment `E`, *equals* the advantage of the one distinguisher
`F.roundEnvToKDFDistinguisher H E` between `F.kdfIdealGame setup msgLen` and
`F.kdfRealGame setup H`. The absolute value is outside the expectation over the setup and the
environment on both sides. -/
theorem advantage_bind_roundGame_kdfMaskedOT_eq_kdf (setup : ℕ → PMF F.Desc)
    (H : F.Desc × List Bool → List Bool) (msgLen : ℕ → ℕ) (n : ℕ)
    (Sm : (d : F.Desc) → (J : Finset (Fin 2)) → CoalitionSimulator
      (maskedOTSchedule (F.Carrier d) (List Bool)) (OTIn (List Bool))
      (MaskedOTCoins (F.Carrier d)) (OTOut (List Bool)) J)
    (hSm : ∀ d, Sm d {1} = maskedOTReceiverSim (F.kdfMask H d) (F.kdfPads d)
      (Cslib.BitString.sampleList (msgLen n)))
    (E : (n : ℕ) → (d : F.Desc) → ProbComp (Bool ⊕ RoundChallenge (spec₁ := otSpec (List Bool))
      (fun _ => maskedOTSchedule (F.Carrier d) (List Bool))
      (fun _ => MaskedOTCoins (F.Carrier d))))
    (hH : ∀ d ∈ (setup n).support, ∀ r : F.Carrier d, (H (d, F.encode d r)).length = msgLen n)
    (hE : ∀ d ∈ (setup n).support, ∀ c, Sum.inr c ∈ (ProbComp.eval (E n d)).support →
      c.coalition = ({1} : Finset (Fin 2)) ∧
        (otOutputs (M := List Bool) c.query 1 : List Bool).length = msgLen n) :
    Game.advantage
        ((setup n).bind fun d => (ProbComp.eval (E n d)).bind
          (roundGame fun op J q =>
            ProbComp.eval (idealJoint (otWorld (List Bool) op) J (Sm d J) q)))
        ((setup n).bind fun d => (ProbComp.eval (E n d)).bind
          (roundGame fun _ J q =>
            (maskedOT (F.kdfMask H d) (F.kdfMask H d) (F.kdfPads d)).realJoint
              (otWorld (F.Carrier d)) J q)) =
      Game.advantage (F.kdfIdealGame setup msgLen (F.roundEnvToKDFDistinguisher H E) n)
        (F.kdfRealGame setup H (F.roundEnvToKDFDistinguisher H E) n) :=
  congrArg₂ Game.advantage
    (F.bind_roundGame_idealJoint_kdfMaskedOT_eq_kdfIdealGame setup H msgLen n Sm hSm E
      fun d hd c hc => (hE d hd c hc).1)
    (F.bind_roundGame_realJoint_kdfMaskedOT_eq_kdfRealGame setup H msgLen n E hH hE)

/-- A sampler that every challenged game draws first can be replaced under the environment: if
`p` and `p'` are within `ε` against every test, and on every challenge `c` of the environment `e`
the games `A c` and `B c` draw from `p` and from `p'` and then continue in the same way, the two
games after `e` are within `ε`. -/
private theorem advantage_bind_elim_le_of_exists_bind {C R : Type} (e : PMF (Bool ⊕ C))
    (p p' : PMF R) {ε : ℝ≥0} (hp : ∀ k : R → Game, Game.advantage (p.bind k) (p'.bind k) ≤ ε)
    (A B : C → Game)
    (h : ∀ c, Sum.inr c ∈ e.support → ∃ K : R → Game, A c = p.bind K ∧ B c = p'.bind K) :
    Game.advantage (e.bind (Sum.elim PMF.pure A)) (e.bind (Sum.elim PMF.pure B)) ≤ ε := by
  classical
  have h' : ∀ c, ∃ K : R → Game, Sum.inr c ∈ e.support → A c = p.bind K ∧ B c = p'.bind K :=
    fun c =>
      if hc : Sum.inr c ∈ e.support then
        let ⟨K, hK⟩ := h c hc
        ⟨K, fun _ => hK⟩
      else ⟨fun _ => PMF.pure false, fun hc' => absurd hc' hc⟩
  choose K hK using h'
  have hpull {X : C → Game} {q : PMF R} (hq : ∀ c, Sum.inr c ∈ e.support → X c = q.bind (K c)) :
      e.bind (Sum.elim PMF.pure X) = q.bind fun r => e.bind (Sum.elim PMF.pure fun c => K c r) :=
    (PMF.bind_congr_on_support e _ (fun z => q.bind fun r => Sum.elim PMF.pure (fun c => K c r) z)
      fun | .inl _, _ => (PMF.bind_const _ _).symm | .inr c, hz => hq c hz).trans
      (PMF.bind_comm e q _)
  rw [hpull fun c hc => (hK c hc).1, hpull fun c hc => (hK c hc).2]
  exact hp _

/-- **The round-game advantage of a sampled environment with pads close to uniform.** Step toward
#6045; original bookkeeping, not a cited result and not a security theorem: the right-hand side is
not bounded, and no efficiency of `F.roundEnvToKDFDistinguisher H E` is claimed. Let the pads of
the masked transfer be drawn by any sampler `samplePads d` that is within `ε` of the exactly
uniform pads `F.kdfPads d` against every test, such as pads with fair-coin exponents. When every
key `H (d, F.encode d r)` has length `msgLen n`, every challenge of the environment corrupts the
receiver `{1}` and has a receiver's output of length `msgLen n`, and the simulator for the receiver
is `maskedOTReceiverSim` with these pads and a uniform `msgLen n`-bit word, the advantage between
the ideal and the real round game of the masked transfer with the ideal pad transfer, under the
sampled setup and the sampled environment `E`, is at most the advantage of the one distinguisher
`F.roundEnvToKDFDistinguisher H E` between `F.kdfIdealGame setup msgLen` and
`F.kdfRealGame setup H`, plus `ε` for the pads of each of the two games. The two absolute values
of the statement are outside the expectation over the setup and the environment; the two
replacements of the pads are statistical. -/
theorem advantage_bind_roundGame_kdfMaskedOT_le_kdf (setup : ℕ → PMF F.Desc)
    (H : F.Desc × List Bool → List Bool) (msgLen : ℕ → ℕ) (n : ℕ)
    (samplePads : (d : F.Desc) → ProbComp (F.Carrier d × F.Carrier d)) {ε : ℝ≥0}
    (hpads : ∀ d (k : F.Carrier d × F.Carrier d → Game),
      Game.advantage ((ProbComp.eval (samplePads d)).bind k)
        ((ProbComp.eval (F.kdfPads d)).bind k) ≤ ε)
    (Sm : (d : F.Desc) → (J : Finset (Fin 2)) → CoalitionSimulator
      (maskedOTSchedule (F.Carrier d) (List Bool)) (OTIn (List Bool))
      (MaskedOTCoins (F.Carrier d)) (OTOut (List Bool)) J)
    (hSm : ∀ d, Sm d {1} = maskedOTReceiverSim (F.kdfMask H d) (samplePads d)
      (Cslib.BitString.sampleList (msgLen n)))
    (E : (n : ℕ) → (d : F.Desc) → ProbComp (Bool ⊕ RoundChallenge (spec₁ := otSpec (List Bool))
      (fun _ => maskedOTSchedule (F.Carrier d) (List Bool))
      (fun _ => MaskedOTCoins (F.Carrier d))))
    (hH : ∀ d (r : F.Carrier d), (H (d, F.encode d r)).length = msgLen n)
    (hE : ∀ d c, Sum.inr c ∈ (ProbComp.eval (E n d)).support →
      c.coalition = ({1} : Finset (Fin 2)) ∧
        (otOutputs (M := List Bool) c.query 1 : List Bool).length = msgLen n) :
    Game.advantage
        ((setup n).bind fun d => (ProbComp.eval (E n d)).bind
          (roundGame fun op J q =>
            ProbComp.eval (idealJoint (otWorld (List Bool) op) J (Sm d J) q)))
        ((setup n).bind fun d => (ProbComp.eval (E n d)).bind
          (roundGame fun _ J q =>
            (maskedOT (F.kdfMask H d) (F.kdfMask H d) (samplePads d)).realJoint
              (otWorld (F.Carrier d)) J q)) ≤
      Game.advantage (F.kdfIdealGame setup msgLen (F.roundEnvToKDFDistinguisher H E) n)
        (F.kdfRealGame setup H (F.roundEnvToKDFDistinguisher H E) n) + (ε + ε) := by
  let Sm₀ (d : F.Desc) := Function.update (Sm d) {1}
    (maskedOTReceiverSim (F.kdfMask H d) (F.kdfPads d) (Cslib.BitString.sampleList (msgLen n)))
  have hSm₀ (d : F.Desc) : Sm₀ d {1} = maskedOTReceiverSim (F.kdfMask H d) (F.kdfPads d)
      (Cslib.BitString.sampleList (msgLen n)) := Function.update_self ..
  have hkdf := F.advantage_bind_roundGame_kdfMaskedOT_eq_kdf setup H msgLen n Sm₀ hSm₀ E
    (fun d _ => hH d) (fun d _ => hE d)
  have hI := Game.advantage_bind_le_nnreal (setup n)
    (fun d => (ProbComp.eval (E n d)).bind (roundGame fun op J q =>
      ProbComp.eval (idealJoint (otWorld (List Bool) op) J (Sm d J) q)))
    (fun d => (ProbComp.eval (E n d)).bind (roundGame fun op J q =>
      ProbComp.eval (idealJoint (otWorld (List Bool) op) J (Sm₀ d J) q))) (ε := ε) fun d =>
    advantage_bind_elim_le_of_exists_bind _ _ _ (hpads d) _ _ fun ⟨_, J, q, g⟩ hc => by
      obtain rfl : J = ({1} : Finset (Fin 2)) := (hE d _ hc).1
      dsimp only
      rw [hSm d, hSm₀ d]
      exact ⟨_, (bind_eval_idealJoint_maskedOT_receiver _ _ _ q g).trans (ProbComp.eval_bind _ _),
        (bind_eval_idealJoint_maskedOT_receiver _ _ _ q g).trans (ProbComp.eval_bind _ _)⟩
  have hR := Game.advantage_bind_le_nnreal (setup n)
    (fun d => (ProbComp.eval (E n d)).bind (roundGame fun _ J q =>
      (maskedOT (F.kdfMask H d) (F.kdfMask H d) (samplePads d)).realJoint
        (otWorld (F.Carrier d)) J q))
    (fun d => (ProbComp.eval (E n d)).bind (roundGame fun _ J q =>
      (maskedOT (F.kdfMask H d) (F.kdfMask H d) (F.kdfPads d)).realJoint
        (otWorld (F.Carrier d)) J q)) (ε := ε) fun d =>
    advantage_bind_elim_le_of_exists_bind _ _ _ (hpads d) _ _ fun ⟨_, J, q, g⟩ hc => by
      obtain ⟨rfl, hout⟩ := hE d _ hc
      have hmask (r : F.Carrier d) := F.kdfMask_kdfMask H d r (hout.trans (hH d r).symm)
      exact ⟨_, (bind_realJoint_maskedOT_receiver _ _ (samplePads d) q hmask g).trans
          (ProbComp.eval_bind _ _),
        (bind_realJoint_maskedOT_receiver _ _ (F.kdfPads d) q hmask g).trans
          (ProbComp.eval_bind _ _)⟩
  exact ((Game.advantage_triangle _ _ _).trans (add_le_add hI
    ((Game.advantage_triangle _ _ _).trans (add_le_add hkdf.le
      ((Game.advantage_comm _ _).trans_le hR))))).trans_eq (by ring)

end RoundEnv

end Cslib.Crypto.PrimeOrderGroupFamily
