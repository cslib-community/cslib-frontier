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

All statements are concrete and exact, in the hybrid model with the ideal pad transfer
`otWorld (F.Carrier d)`, with exponents drawn exactly uniformly from `ZMod (F.order d)`.

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

## What is not proved

* No efficiency statement: `F.maskedOTReceiverToKDFDistinguisher H x D` is not shown to be
  uniform strict PPT (`KDFDistinguisher.IsPPT`) when `x` and `D` are efficient, so `F.SecureKDF` is
  not applied and no negligible bound is derived.
* No asymptotic statement (`ProtocolFamily.SemiHonestSecure`) is made, and the per-instance
  equality is for the point setup at a fixed `d`; averaging it over a setup law is not done here.
* The pads are sampled with exactly uniform exponents (`ProbComp.uniform`), not by a fair-coin
  sampler such as `F.sampleExp`.
* The pad transfer is ideal. Substituting a protocol for it, for one distinguisher, is
  `semiHonestAdvantage_maskedOT_compose_le_transfer` in
  `CslibFrontier/Crypto/Protocols/MPC/MaskedOT/DDH.lean`; it is not combined with the
  key-derivation mask here.
* The locator for [BonehShoup2023] is the one recorded in
  `CslibFrontier/Crypto/Computational/ElGamal.lean`; it was not re-verified against the source.

## Main definitions

* `Cslib.Crypto.PrimeOrderGroupFamily.kdfMask`: the xor with the key derived from a pad.
* `Cslib.Crypto.PrimeOrderGroupFamily.kdfPads`: two pads with independent uniform exponents.
* `Cslib.Crypto.PrimeOrderGroupFamily.maskedOTReceiverToKDFDistinguisher`: the reduction from a
  distinguisher of a corrupted receiver's view to a key-derivation distinguisher.

## Main results

* `Cslib.Crypto.PrimeOrderGroupFamily.kdfRealGame_maskedOTReceiverToKDFDistinguisher`,
  `Cslib.Crypto.PrimeOrderGroupFamily.kdfIdealGame_maskedOTReceiverToKDFDistinguisher`: the
  key-derivation games of the reduction are the two pad-hiding experiments.
* `Cslib.Crypto.PrimeOrderGroupFamily.semiHonestAdvantage_kdfMaskedOT_receiver_eq_kdf`: at fixed
  group parameters, the advantage against a corrupted receiver is the key-derivation advantage of
  the reduction.

## References

* [D. Boneh and V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 11.5.2 (Attack Game 11.3), as formalized by `kdfRealGame`
  and `kdfIdealGame`.
-/

public section

namespace Cslib.Crypto.PrimeOrderGroupFamily

open Cslib Cslib.Probability Cslib.Crypto.Protocols.MPC

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
  simp only [kdfRealGame, maskedOTReceiverToKDFDistinguisher, kdfPads, bind_assoc, pure_bind,
    ProbComp.eval_bind, ProbComp.eval_uniform, PMF.monad_bind_eq_bind]
  refine congrArg (PMF.bind _) (funext fun d => ?_)
  cases hσ : (x n d 1 : Bool)
  · simp only [Bool.false_eq_true, ↓reduceIte, PMF.bind_const, kdfMask]
  · simp only [↓reduceIte, PMF.bind_const, kdfMask]
    exact PMF.bind_comm _ _ _

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
  have hpad (w : List Bool) (f : List Bool → PMF Bool) :
      ((Cslib.BitString.uniformList (msgLen n)).bind fun key =>
        f (Cslib.BitString.listXor key.length [key, w])) =
        (Cslib.BitString.uniformList (msgLen n)).bind f := by
    simpa only [PMF.bind_map, Function.comp_def] using
      congrArg (·.bind f) (Cslib.BitString.uniformList_map_listXor_length (msgLen n) w)
  simp only [kdfIdealGame, maskedOTReceiverToKDFDistinguisher, kdfPads, bind_assoc, pure_bind,
    ProbComp.eval_bind, ProbComp.eval_uniform, Cslib.BitString.eval_sampleList,
    PMF.monad_bind_eq_bind]
  refine congrArg (PMF.bind _) (funext fun d => ?_)
  cases hσ : (x n d 1 : Bool)
  · simp only [Bool.false_eq_true, ↓reduceIte, PMF.bind_const]
    exact congrArg (PMF.bind _) (funext fun a => hpad _ fun u => ProbComp.eval
      (maskedOTPadTest (F.kdfMask H d) (x n d) (D n d) (a • F.generator d) u))
  · simp only [↓reduceIte, PMF.bind_const]
    exact congrArg (PMF.bind _) (funext fun a => hpad _ fun u => ProbComp.eval
      (maskedOTPadTest (F.kdfMask H d) (x n d) (D n d) (a • F.generator d) u))

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

end Cslib.Crypto.PrimeOrderGroupFamily
