/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.MPC.DDHOT.Family
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Captured
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.DPi
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Crypto.Computational.DiffieHellman.SampleExp
import CslibFrontier.Crypto.Protocols.MPC.EmptyCoalition
import CslibFrontier.Foundations.Data.ZMod.NatCast
import CslibFrontier.Tactic.Negligible
import CslibFrontier.Tactic.PMFSwap

/-!
# Stand-alone semi-honest security of fair-coin DDH oblivious transfer with PPT simulators

`CslibFrontier/Crypto/Protocols/MPC/DDHOT/Family.lean` defines `ddhOTProbFamily`
(`ddhOTProbProtocol`), the three-message DDH oblivious transfer protocol over a
`PrimeOrderGroupFamily` `F` whose honest parties draw raw fair-coin bit strings via
`sampleExpBits n d` (Remark 23.5, p. 1059) and retain those unreduced bit strings in
`PartyView.coins`, together with the machine encoding `ddhOTEncoding` and the certified DDH
reduction `ddhOTReceiverToDDHDistinguisher`.

This module gives uniform strict-PPT simulator families for all four static coalitions
`I : Finset (Fin 2)` that likewise generate only raw fair-coin bit strings via `sampleExpBits n d`,
and proves stand-alone `ProtocolFamily.SemiHonestSecure` of `ddhOTProbFamily` under `F.DDH setup`
(`DDH.ddhOTProbFamily_semiHonestSecure`) as a step toward [BonehShoup2023], Section 23.5.7.2,
Theorem 23.7 (p. 1058; #5829, #5293):
* `I = ∅` (no corrupted parties): `SimulatorFamily.empty` reproduces the real joint distribution
  with zero advantage;
* `I = {0}` (corrupted sender): `ddhOTSenderSimProb` draws the sender's five raw bit strings from
  `sampleDDHOTSenderBitCoins n d` (matching the real sender's coin law with zero loss) and one
  receiver bit string from `sampleExpBits n d`, achieving unconditional statistical security with
  advantage at most `2 / 2 ^ n` against every environment, efficient or not
  (`advantage_ddhOTProbSenderGame_le`, `ddhOTProbFamily_semiHonestSecure_sender`);
* `I = {1}` (corrupted receiver): `ddhOTReceiverSimProb` draws the receiver's raw bit string from
  `sampleExpBits n d` (matching the real receiver's coin law with zero loss) and five sender/mask
  bit strings from `sampleExpBits n d`, within `5 / 2 ^ n` of `ddhOTReceiverSimOf`
  (`advantage_bind_ddhOTReceiverSimProb_le`), so every environment's advantage is at most the DDH
  advantage of `ddhOTReceiverToDDHDistinguisher Z` plus `14 / 2 ^ n`
  (`advantage_ddhOTProbReceiverGame_le`);
* `I = Finset.univ` (both parties corrupted): `ddhOTFullSimProb` runs `ddhOTProbProtocol`'s raw
  bit-string coin draws on both parties' inputs, reproducing the real joint distribution with zero
  advantage.

## Remaining gap to [BonehShoup2023], Theorem 23.7

`DDH.ddhOTProbFamily_semiHonestSecure` is a stand-alone semi-honest step toward [BonehShoup2023],
Section 23.5.7.2, Theorem 23.7 (p. 1058), not the cited result (#5829, #5293):

* **Execution model (`ProtocolFamily.SemiHonestSecure` vs. Section 23.5.6 & Definition 23.5,
  pp. 1043–1044, 1054–1056):** `SemiHonestSecure` is a two-stage stand-alone game in which a
  uniform strict-PPT environment chooses all inputs after seeing `(1ⁿ, d)` from `setup n` and
  distinguishes the corrupted coalition's final `(PartyView, outputs)` tuple, rather than
  exchanging interactive report and control messages during protocol execution to implement `F_ot`
  in the restricted UC framework of Section 23.5.6. In addition, `IsPPTOn` bounds running time on
  every execution rather than with overwhelming probability (Section 23.5.2.2, p. 1043).
* **Protocol variant (`ddhOTProbProtocol` vs. Figure 23.17, p. 1057):** as documented in
  `DDHOT.lean`, the sender derives `u = a • g` from a sampled exponent bit string (knowing `a`,
  whereas Figure 23.17 samples `d` from `G`), encrypts each branch `i` with independent coins
  `(rᵢ, sᵢ)` rather than a single shared exponent `β`, and performs the check `w₀ + w₁ = u` of
  Section 23.5.7.3, Remark 23.6 (p. 1061), sending zeros when violated.

Both parties and simulators draw raw fair-coin bit strings (`sampleExpBits n d`), and
`PartyView.coins` retains those unreduced bit strings verbatim, discharging the coin-representation
requirement of Section 23.5.7.2 ("Further assumptions about randomness", p. 1059) and
[Lindell2017], Section 4.2, Definition 4.1 (p. 7; up to the uniform post-setup input-choice
conventions of `ProtocolFamily.SemiHonestSecure` documented in
`CslibFrontier/Crypto/Protocols/MPC/Asymptotic.lean`).

## Main definitions

* `Cslib.Crypto.PrimeOrderGroupFamily.ddhOTSenderSimProb`,
  `Cslib.Crypto.PrimeOrderGroupFamily.ddhOTReceiverSimProb`: the simulator families for `{0}` and
  `{1}` that draw raw fair-coin bit strings via `sampleExpBits`.

## Main results

* `Cslib.Crypto.PrimeOrderGroupFamily.isPPT_ddhOTSenderSimProb`,
  `Cslib.Crypto.PrimeOrderGroupFamily.isPPT_ddhOTReceiverSimProb`: the simulator families are
  uniform strict PPT for `ddhOTEncoding`.
* `Cslib.Crypto.PrimeOrderGroupFamily.advantage_bind_ddhOTReceiverSimProb_le`: on every input,
  `ddhOTReceiverSimProb` is within statistical distance `5 / 2 ^ n` of `ddhOTReceiverSimOf`.
* `Cslib.Crypto.PrimeOrderGroupFamily.advantage_ddhOTProbSenderGame_le`,
  `Cslib.Crypto.PrimeOrderGroupFamily.ddhOTProbFamily_semiHonestSecure_sender`: against a corrupted
  sender, every environment (efficient or not) has advantage at most `2 / 2 ^ n`, giving
  unconditional stand-alone semi-honest security of `ddhOTProbFamily` at `{0}` (step toward
  Theorem 23.7).
* `Cslib.Crypto.PrimeOrderGroupFamily.advantage_ddhOTProbReceiverGame_le`: against a corrupted
  receiver, every environment has advantage at most the DDH advantage of
  `ddhOTReceiverToDDHDistinguisher Z` plus `14 / 2 ^ n`.
* `Cslib.Crypto.PrimeOrderGroupFamily.DDH.ddhOTProbFamily_semiHonestSecure`: under `F.DDH setup`,
  `ddhOTProbFamily` satisfies stand-alone `ProtocolFamily.SemiHonestSecure` for every static
  coalition `I : Finset (Fin 2)` (step toward [BonehShoup2023], Theorem 23.7; #5829, #5293).

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 23.5 (Section 23.5.2.2, p. 1043; Definition 23.5, p. 1044;
  Section 23.5.6, pp. 1054–1056; Figure 23.17, p. 1057; Theorem 23.7, p. 1058; Remark 23.5,
  p. 1059; Remark 23.6, p. 1061).
* [Y. Lindell, *How To Simulate It – A Tutorial on the Simulation Proof Technique*, ECCC
  TR17-112][Lindell2017], Section 2 (p. 3) and Section 4.2 (Definition 4.1, p. 7).
-/

public section

namespace Cslib.Crypto.PrimeOrderGroupFamily

open Probability Turing.MultiTapeTM Cslib.Crypto.Protocols.MPC
open scoped NNReal

variable (F : PrimeOrderGroupFamily)

/-! ### The simulator families -/

/-- Simulator family for a corrupted sender (`{0}`) in `ddhOTProbFamily`: draws the sender's five
raw fair-coin bit strings via `sampleDDHOTSenderBitCoins n d` (recording them unreduced in
`PartyView.coins`, with the exact same law as the real sender) and one bit string `bBits` via
`sampleExpBits n d` for the simulated Round 2 message. -/
@[expose] noncomputable def ddhOTSenderSimProb : SimulatorFamily F.ddhOTProbFamily {0} :=
  fun n d xI _ => do
    let c₀ ← F.sampleDDHOTSenderBitCoins n d
    let bBits ← F.sampleExpBits n d
    return ddhOTSenderSimWithCoinsOf (C₁ := List Bool) (F.generator d)
      (DDHOTSenderBitCoins.toSenderCoins (F.order d))
      c₀ (BitString.binaryValue bBits : ZMod (F.order d)) xI

/-- Simulator family for a corrupted receiver (`{1}`) in `ddhOTProbFamily`: draws six raw fair-coin
bit strings via `sampleExpBits n d`, recording `bBits` unreduced in the receiver's
`PartyView.coins` (with the exact same law as the real receiver) and using the remaining five bit
strings for `ddhOTReceiverSimWithCoinsOf`. -/
@[expose] noncomputable def ddhOTReceiverSimProb : SimulatorFamily F.ddhOTProbFamily {1} :=
  fun n d xI yI => do
    let aBits ← F.sampleExpBits n d
    let bBits ← F.sampleExpBits n d
    let rBits ← F.sampleExpBits n d
    let sBits ← F.sampleExpBits n d
    let kBits ← F.sampleExpBits n d
    let cBits ← F.sampleExpBits n d
    let q := F.order d
    return ddhOTReceiverSimWithCoinsOf (C₀ := DDHOTSenderBitCoins) (F.generator d)
      (fun bs : List Bool => (BitString.binaryValue bs : ZMod q))
      (BitString.binaryValue aBits : ZMod q) bBits
      (BitString.binaryValue rBits : ZMod q) (BitString.binaryValue sBits : ZMod q)
      (BitString.binaryValue kBits : ZMod q) (BitString.binaryValue cBits : ZMod q) xI yI

/-! ### Statistical closeness to `ddhOTReceiverSimOf` -/

/-- On every input, `ddhOTReceiverSimProb` and `ddhOTReceiverSimOf` (which shares the receiver's
exact `sampleExpBits n d` draw `bBits` and draws the five sender/mask exponents uniformly) are
within statistical distance `5 / 2 ^ n`. -/
theorem advantage_bind_ddhOTReceiverSimProb_le (n : ℕ) (d : F.Desc)
    (xI : (i : ({1} : Finset (Fin 2))) → OTIn (F.Carrier d) i)
    (yI : (i : ({1} : Finset (Fin 2))) → OTOut (F.Carrier d) i)
    (k : ((i : ({1} : Finset (Fin 2))) →
      PartyView (OTIn (F.Carrier d)) (DDHOTCoinsWith DDHOTSenderBitCoins (List Bool))
        (ddhOTSchedule (F.Carrier d)) i) → Game) :
    Game.advantage
      ((ProbComp.eval (ddhOTReceiverSimOf (F.generator d) (F.order d) (F.sampleExpBits n d)
        (fun bs : List Bool => (BitString.binaryValue bs : ZMod (F.order d))) xI yI)).bind k)
      ((ProbComp.eval (F.ddhOTReceiverSimProb n d xI yI)).bind k) ≤ 5 / 2 ^ n := by
  simp only [ddhOTReceiverSimOf, ddhOTReceiverSimProb, ProbComp.eval_bind, ProbComp.eval_pure,
    ProbComp.eval_uniform, PMF.bind_bind, PMF.pure_bind]
  rw [PMF.bind_comm (PMF.uniformOfFintype (ZMod (F.order d))) (ProbComp.eval (F.sampleExpBits n d)),
    PMF.bind_comm (ProbComp.eval (F.sampleExpBits n d)) (ProbComp.eval (F.sampleExpBits n d))
      (fun aBits bBits => (ProbComp.eval (F.sampleExpBits n d)).bind fun rBits =>
        (ProbComp.eval (F.sampleExpBits n d)).bind fun sBits =>
          (ProbComp.eval (F.sampleExpBits n d)).bind fun kBits =>
            (ProbComp.eval (F.sampleExpBits n d)).bind fun cBits =>
              k (ddhOTReceiverSimWithCoinsOf (C₀ := DDHOTSenderBitCoins) (F.generator d)
                (fun bs : List Bool => (BitString.binaryValue bs : ZMod (F.order d)))
                (BitString.binaryValue aBits : ZMod (F.order d)) bBits
                (BitString.binaryValue rBits : ZMod (F.order d))
                (BitString.binaryValue sBits : ZMod (F.order d))
                (BitString.binaryValue kBits : ZMod (F.order d))
                (BitString.binaryValue cBits : ZMod (F.order d)) xI yI))]
  refine Game.advantage_bind_le_nnreal _ _ _ fun bBits => ?_
  rw [Game.advantage_comm]
  simpa only [sampleDDHOTSenderBitCoins, DDHOTSenderBitCoins.toSenderCoins, sampleDDHOTSenderCoins,
    ProbComp.eval_bind, ProbComp.eval_pure, ProbComp.eval_uniform, PMF.bind_bind,
    PMF.pure_bind] using
    F.advantage_bind_sampleDDHOTSenderBitCoins_le n d fun ⟨a, r, s, k', c⟩ =>
      k (ddhOTReceiverSimWithCoinsOf (C₀ := DDHOTSenderBitCoins) (F.generator d)
        (fun bs : List Bool => (BitString.binaryValue bs : ZMod (F.order d)))
        a bBits r s k' c xI yI)

/-! ### Efficiency of the simulator families -/

private structure SixBitsCtx (α : Type) where
  input : α
  s₁ : List Bool
  s₂ : List Bool
  s₃ : List Bool
  s₄ : List Bool
  s₅ : List Bool
  s₆ : List Bool

private enc_structure encSixBitsCtx (α : Type) (enc : α ↪ List Bool) : SixBitsCtx α where
  input : enc, s₁ : encBits, s₂ : encBits, s₃ : encBits, s₄ : encBits, s₅ : encBits, s₆ : encBits

/-- Six `sampleExpBits` draws followed by an efficiently computable function of the input and the
six bit strings are uniform strict PPT. -/
private theorem isPPTOn_sampleExpBits_six {α β : Type} {enc : α ↪ List Bool}
    {encOut : β ↪ List Bool} {n : α → ℕ} {d : α → F.Desc}
    (hn : ComputableInPolyTime n enc encUnary) (hd : ComputableInPolyTime d enc F.encDesc)
    {W : α → List Bool → List Bool → List Bool → List Bool → List Bool → List Bool → β}
    (hW : ∀ {γ : Type} {encγ : γ ↪ List Bool} {x : γ → α}
      {s₁ s₂ s₃ s₄ s₅ s₆ : γ → List Bool},
      ComputableInPolyTime x encγ enc → ComputableInPolyTime s₁ encγ encBits →
      ComputableInPolyTime s₂ encγ encBits → ComputableInPolyTime s₃ encγ encBits →
      ComputableInPolyTime s₄ encγ encBits → ComputableInPolyTime s₅ encγ encBits →
      ComputableInPolyTime s₆ encγ encBits →
      ComputableInPolyTime (fun c => W (x c) (s₁ c) (s₂ c) (s₃ c) (s₄ c) (s₅ c) (s₆ c)) encγ
        encOut) :
    IsPPTOn enc encOut (fun x => do
      let s₁ ← F.sampleExpBits (n x) (d x)
      let s₂ ← F.sampleExpBits (n x) (d x)
      let s₃ ← F.sampleExpBits (n x) (d x)
      let s₄ ← F.sampleExpBits (n x) (d x)
      let s₅ ← F.sampleExpBits (n x) (d x)
      let s₆ ← F.sampleExpBits (n x) (d x)
      pure (W x s₁ s₂ s₃ s₄ s₅ s₆)) := by
  have hsample {γ : Type} {encγ : γ ↪ List Bool} {x : γ → α}
      (hx : ComputableInPolyTime x encγ enc) :
      IsPPTOn encγ encBits fun c => F.sampleExpBits (n (x c)) (d (x c)) :=
    F.isPPTOn_sampleExpBits (hn.comp hx) (hd.comp hx)
  let sampleSix (x : α) : ProbComp (SixBitsCtx α) := do
    let s₁ ← F.sampleExpBits (n x) (d x)
    let s₂ ← F.sampleExpBits (n x) (d x)
    let s₃ ← F.sampleExpBits (n x) (d x)
    let s₄ ← F.sampleExpBits (n x) (d x)
    let s₅ ← F.sampleExpBits (n x) (d x)
    let s₆ ← F.sampleExpBits (n x) (d x)
    pure ⟨x, s₁, s₂, s₃, s₄, s₅, s₆⟩
  have hsix : IsPPTOn enc (encSixBitsCtx α enc) sampleSix := by
    refine IsPPTOn.bind_with (hsample .id') ?_
    refine IsPPTOn.bind_with (hsample (by fun_prop)) ?_
    refine IsPPTOn.bind_with (hsample (by fun_prop)) ?_
    refine IsPPTOn.bind_with (hsample (by fun_prop)) ?_
    refine IsPPTOn.bind_with (hsample (by fun_prop)) ?_
    refine IsPPTOn.bind_with (hsample (by fun_prop)) ?_
    exact (encSixBitsCtx_mk_polyTime α enc (by fun_prop) (by fun_prop) (by fun_prop)
      (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)).isPPTOn
  refine (hsix.map (hW (encγ := encSixBitsCtx α enc) (x := SixBitsCtx.input)
    (s₁ := SixBitsCtx.s₁) (s₂ := SixBitsCtx.s₂) (s₃ := SixBitsCtx.s₃)
    (s₄ := SixBitsCtx.s₄) (s₅ := SixBitsCtx.s₅) (s₆ := SixBitsCtx.s₆) (by fun_prop)
    (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop))).congr
    fun x => ?_
  simp only [sampleSix, ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_pure, PMF.map_bind,
    PMF.pure_map]

/-- The view words that `ddhOTSenderSimProb` writes at group parameters `d` on the sender's
messages `m = (m₀, m₁)` and six raw bit strings `aBits, r₀Bits, s₀Bits, r₁Bits, s₁Bits, bBits`. -/
private def ddhOTSenderSimWords (d : F.Desc) (m : F.Carrier d × F.Carrier d)
    (aBits r₀Bits s₀Bits r₁Bits s₁Bits bBits : List Bool) : DDHOTSenderViewWords :=
  let q := F.order d
  let g := F.generator d
  let a := BitString.binaryValue aBits
  let b := BitString.binaryValue bBits
  ⟨F.encode d m.1, F.encode d m.2, aBits, r₀Bits, s₀Bits, r₁Bits, s₁Bits,
    F.encode d ((b : ZMod q) • g), F.encode d ((a : ZMod q) • g + ((q - b % q : ℕ) : ZMod q) • g)⟩

/-- The party `0` of the coalition `{0}`. -/
private abbrev sender : ({0} : Finset (Fin 2)) := ⟨0, Finset.mem_singleton_self 0⟩

/-- `ddhOTSenderSimProb` is uniform strict PPT for `ddhOTEncoding`. -/
theorem isPPT_ddhOTSenderSimProb : F.ddhOTSenderSimProb.IsPPT F.ddhOTEncoding := by
  let E := F.ddhOTEncoding
  refine isPPTOn_iff_encoded.mpr ((F.isPPTOn_sampleExpBits_six
    (n := fun x : SimInput F.ddhOTProbFamily {0} => x.secParam) (d := fun x => x.desc)
    (encSimInput_secParam_polyTime E .id')
    (encSimInput_desc_polyTime E .id')
    (W := fun x aBits r₀Bits s₀Bits r₁Bits s₁Bits bBits =>
      encPi encBits fun _ : ({0} : Finset (Fin 2)) =>
        encDDHOTSenderViewWords
          (F.ddhOTSenderSimWords x.desc (x.inputs sender)
            aBits r₀Bits s₀Bits r₁Bits s₁Bits bBits))
    fun {γ encγ x _ _ _ _ _ _} hx haBits hr₀Bits hs₀Bits hr₁Bits hs₁Bits hbBits => ?_).congr
      fun x => ?_)
  · have hd : ComputableInPolyTime (fun c => (x c).desc) encγ F.encDesc :=
      encSimInput_desc_polyTime E hx
    have hm : ComputableInPolyTime (fun c => (F.encode (x c).desc ((x c).inputs sender).1,
        F.encode (x c).desc ((x c).inputs sender).2)) encγ (encPair encBits encBits) :=
      E.input.encCoalition_apply_polyTime (encSimInput_inputs_polyTime E hx) sender
    have hq := F.computableInPolyTime_order.comp hd
    have hg := computableInPolyTime_encode_generator hd
    have ha := ComputableInPolyTime.bitsBinaryValue.comp haBits
    have hb := ComputableInPolyTime.bitsBinaryValue.comp hbBits
    exact (ComputableInPolyTime.pi fun _ => (encDDHOTSenderViewWords_mk_polyTime hm.fst' hm.snd'
      haBits hr₀Bits hs₀Bits hr₁Bits hs₁Bits (computableInPolyTime_encode_natCast_smul hd hb hg)
      (computableInPolyTime_encode_add hd (computableInPolyTime_encode_natCast_smul hd ha hg)
        (computableInPolyTime_encode_natCast_smul hd (hq.binary_sub' (hb.binary_mod' hq))
          hg))).encoding_comp).encoding_comp
  · simp only [ddhOTSenderSimProb, sampleDDHOTSenderBitCoins, ProbComp.eval_bind,
      ProbComp.eval_map, ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind, PMF.map_bind,
      PMF.pure_map]
    refine congrArg (PMF.bind _) (funext fun aBits =>
      congrArg (PMF.bind _) (funext fun r₀Bits =>
        congrArg (PMF.bind _) (funext fun s₀Bits =>
          congrArg (PMF.bind _) (funext fun r₁Bits =>
            congrArg (PMF.bind _) (funext fun s₁Bits =>
              congrArg (PMF.bind _) (funext fun bBits => congrArg PMF.pure ?_))))))
    refine Eq.trans ?_ (E.view.encCoalition_singleton x.secParam x.desc 0 _).symm
    refine congrArg (encPi encBits) (funext fun _ => congrArg encDDHOTSenderViewWords ?_)
    obtain ⟨n, d, xs, ys⟩ := x
    let q := F.order d
    let g := F.generator d
    let a := BitString.binaryValue aBits
    let b := BitString.binaryValue bBits
    change _ = F.ddhOTSenderViewWords d (ddhOTSenderViewWith (xs sender)
      ⟨aBits, r₀Bits, s₀Bits, r₁Bits, s₁Bits⟩
      ((b : ZMod q) • g, (a : ZMod q) • g - (b : ZMod q) • g))
    simp only [ddhOTSenderSimWords, ddhOTSenderViewWords, ddhOTSenderViewWith,
      ZMod.natCast_sub_mod_eq_neg, neg_smul, ← sub_eq_add_neg]
    rfl

/-- The view words that `ddhOTReceiverSimProb` writes at group parameters `d` on the choice bit
`σ`, the receiver's output `m` and six raw bit strings `aBits, bBits, rBits, sBits, kBits,
cBits`. -/
private def ddhOTReceiverSimWords (d : F.Desc) (σ : Bool) (m : F.Carrier d)
    (aBits bBits rBits sBits kBits cBits : List Bool) : DDHOTReceiverViewWords :=
  let q := F.order d
  let g := F.generator d
  let a := BitString.binaryValue aBits
  let b := BitString.binaryValue bBits
  let r := BitString.binaryValue rBits
  let s := BitString.binaryValue sBits
  let k := BitString.binaryValue kBits
  let c := BitString.binaryValue cBits
  let e := (r : ZMod q) • g + (s : ZMod q) • (a : ZMod q) • g
  let chosen₁ := F.encode d e
  let chosen₂ := F.encode d ((b : ZMod q) • e + m)
  let other₁ := F.encode d ((k : ZMod q) • g)
  let other₂ := F.encode d ((c : ZMod q) • g)
  ⟨σ, bBits, F.encode d ((a : ZMod q) • g), if σ then other₁ else chosen₁,
    if σ then other₂ else chosen₂, if σ then chosen₁ else other₁, if σ then chosen₂ else other₂⟩

/-- The party `1` of the coalition `{1}`. -/
private abbrev receiver : ({1} : Finset (Fin 2)) := ⟨1, Finset.mem_singleton_self 1⟩

/-- `ddhOTReceiverSimProb` is uniform strict PPT for `ddhOTEncoding`. -/
theorem isPPT_ddhOTReceiverSimProb : F.ddhOTReceiverSimProb.IsPPT F.ddhOTEncoding := by
  let E := F.ddhOTEncoding
  refine isPPTOn_iff_encoded.mpr ((F.isPPTOn_sampleExpBits_six
    (n := fun x : SimInput F.ddhOTProbFamily {1} => x.secParam) (d := fun x => x.desc)
    (encSimInput_secParam_polyTime E .id')
    (encSimInput_desc_polyTime E .id')
    (W := fun x aBits bBits rBits sBits kBits cBits =>
      encPi encBits fun _ : ({1} : Finset (Fin 2)) =>
        encDDHOTReceiverViewWords
          (F.ddhOTReceiverSimWords x.desc (x.inputs receiver) (x.outputs receiver)
            aBits bBits rBits sBits kBits cBits))
    fun {γ encγ x _ _ _ _ _ _} hx haBits hbBits hrBits hsBits hkBits hcBits => ?_).congr
      fun x => ?_)
  · have hd : ComputableInPolyTime (fun c => (x c).desc) encγ F.encDesc :=
      encSimInput_desc_polyTime E hx
    have hσ : ComputableInPolyTime (fun c => ((x c).inputs receiver : Bool)) encγ encBool :=
      E.input.encCoalition_apply_polyTime (encSimInput_inputs_polyTime E hx) receiver
    have hm : ComputableInPolyTime (fun c => F.encode (x c).desc ((x c).outputs receiver)) encγ
        encBits :=
      E.output.encCoalition_apply_polyTime (encSimInput_outputs_polyTime E hx) receiver
    have hg := computableInPolyTime_encode_generator hd
    have ha := ComputableInPolyTime.bitsBinaryValue.comp haBits
    have hb := ComputableInPolyTime.bitsBinaryValue.comp hbBits
    have hr := ComputableInPolyTime.bitsBinaryValue.comp hrBits
    have hs := ComputableInPolyTime.bitsBinaryValue.comp hsBits
    have hk := ComputableInPolyTime.bitsBinaryValue.comp hkBits
    have hc := ComputableInPolyTime.bitsBinaryValue.comp hcBits
    have hu := computableInPolyTime_encode_natCast_smul hd ha hg
    have he := computableInPolyTime_encode_add hd
      (computableInPolyTime_encode_natCast_smul hd hr hg)
      (computableInPolyTime_encode_natCast_smul hd hs hu)
    have hbody := computableInPolyTime_encode_add hd
      (computableInPolyTime_encode_natCast_smul hd hb he) hm
    have hk' := computableInPolyTime_encode_natCast_smul hd hk hg
    have hc' := computableInPolyTime_encode_natCast_smul hd hc hg
    exact (ComputableInPolyTime.pi fun _ => (encDDHOTReceiverViewWords_mk_polyTime hσ
      hbBits hu (hσ.ite' hk' he) (hσ.ite' hc' hbody) (hσ.ite' he hk')
      (hσ.ite' hbody hc')).encoding_comp).encoding_comp
  · simp only [ddhOTReceiverSimProb, ProbComp.eval_bind, ProbComp.eval_map,
      ProbComp.eval_pure, PMF.map_bind, PMF.pure_map]
    refine congrArg (PMF.bind _) (funext fun aBits =>
      congrArg (PMF.bind _) (funext fun bBits =>
        congrArg (PMF.bind _) (funext fun rBits =>
          congrArg (PMF.bind _) (funext fun sBits =>
            congrArg (PMF.bind _) (funext fun kBits =>
              congrArg (PMF.bind _) (funext fun cBits => congrArg PMF.pure ?_))))))
    refine Eq.trans ?_ (E.view.encCoalition_singleton x.secParam x.desc 1 _).symm
    refine congrArg (encPi encBits) (funext fun _ => congrArg encDDHOTReceiverViewWords ?_)
    obtain ⟨n, d, xs, ys⟩ := x
    let q := F.order d
    let g := F.generator d
    dsimp only
    simp only [ddhOTReceiverSimWithCoinsOf]
    obtain ⟨σ, hσ⟩ : ∃ σ : Bool, xs receiver = σ := ⟨_, rfl⟩
    obtain ⟨m, hm⟩ : ∃ m : F.Carrier d, ys receiver = m := ⟨_, rfl⟩
    rw [hσ, hm]
    let a := BitString.binaryValue aBits
    let b := BitString.binaryValue bBits
    let r := BitString.binaryValue rBits
    let s := BitString.binaryValue sBits
    let k := BitString.binaryValue kBits
    let c := BitString.binaryValue cBits
    let e := (r : ZMod q) • g + (s : ZMod q) • (a : ZMod q) • g
    change _ = F.ddhOTReceiverViewWords d (ddhOTReceiverViewWith σ bBits ((a : ZMod q) • g)
      (if σ then (((k : ZMod q) • g, (c : ZMod q) • g), (e, (b : ZMod q) • e + m))
        else ((e, (b : ZMod q) • e + m), ((k : ZMod q) • g, (c : ZMod q) • g))))
    cases σ <;> simp only [ddhOTReceiverSimWords, ddhOTReceiverViewWords, ddhOTReceiverViewWith,
      Bool.false_eq_true, ↓reduceIte] <;> rfl

/-! ### Empty and full coalitions -/

/-- When no party is corrupted, `SimulatorFamily.empty` reproduces `ddhOTProbProtocol`'s real joint
law exactly. -/
private theorem idealJoint_ddhOTProb_empty (n : ℕ) (d : F.Desc)
    (x : (i : Fin 2) → OTIn (F.Carrier d) i) :
    ProbComp.eval (idealJoint (otFunctionality (F.Carrier d)) ∅
        (SimulatorFamily.empty F.ddhOTProbFamily n d) x) =
      (F.ddhOTProbProtocol n d).realJoint noOracleWorld ∅ x := by
  simp only [ddhOTProbProtocol, evalWith_ddhOTProtocolWith, Protocol.realJoint, eval_idealJoint,
    otFunctionality, Functionality.ofDeterministic, SimulatorFamily.empty, ProbComp.eval_pure,
    PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.pure_bind, PMF.pure_map, PMF.map_bind,
    Prod.map, id]
  have hconst (raw₀ : DDHOTSenderBitCoins) (bBits : List Bool) :
      (Finset.restrict ∅ (ddhOTViewsWith (F.generator d)
          (DDHOTSenderBitCoins.toSenderCoins (F.order d))
          (fun bs : List Bool => (BitString.binaryValue bs : ZMod (F.order d))) x raw₀ bBits),
        otOutputs x) =
        ((fun i : (∅ : Finset (Fin 2)) => isEmptyElim i), otOutputs x) :=
    Prod.ext (funext fun i => nomatch i.2) rfl
  simp only [hconst, PMF.bind_const]

/-- Parties `0` and `1` as members of `Finset.univ`. -/
private abbrev senderUniv : (Finset.univ : Finset (Fin 2)) := ⟨0, Finset.mem_univ 0⟩
private abbrev receiverUniv : (Finset.univ : Finset (Fin 2)) := ⟨1, Finset.mem_univ 1⟩

/-- Simulator for `I = Finset.univ` (both parties corrupted): receives both parties' inputs and
runs the honest fair-coin protocol `ddhOTProbProtocol` directly on raw bit-string coins. -/
private noncomputable def ddhOTFullSimProb :
    SimulatorFamily F.ddhOTProbFamily Finset.univ :=
  fun n d xI _ => do
    let c₀ ← F.sampleDDHOTSenderBitCoins n d
    let bBits ← F.sampleExpBits n d
    return Finset.univ.restrict (ddhOTViewsWith (F.generator d)
      (DDHOTSenderBitCoins.toSenderCoins (F.order d))
      (fun bs : List Bool => (BitString.binaryValue bs : ZMod (F.order d)))
      (fun i => xI ⟨i, Finset.mem_univ i⟩) c₀ bBits)

/-- View words produced by `ddhOTFullSimProb` on six `sampleExpBits` draws. -/
private def ddhOTFullSimWords (d : F.Desc) (m : F.Carrier d × F.Carrier d) (σ : Bool)
    (aBits r₀Bits s₀Bits r₁Bits s₁Bits bBits : List Bool)
    (i : (Finset.univ : Finset (Fin 2))) : DDHOTViewWords i :=
  let q := F.order d
  let g := F.generator d
  let a := BitString.binaryValue aBits
  let r₀ := BitString.binaryValue r₀Bits
  let s₀ := BitString.binaryValue s₀Bits
  let r₁ := BitString.binaryValue r₁Bits
  let s₁ := BitString.binaryValue s₁Bits
  let b := BitString.binaryValue bBits
  let u := (a : ZMod q) • g
  let v := (b : ZMod q) • g
  let uSubV := u + ((q - b % q : ℕ) : ZMod q) • g
  let w₀ := cond σ uSubV v
  let w₁ := cond σ v uSubV
  let e₀ := (r₀ : ZMod q) • g + (s₀ : ZMod q) • u
  let c₀ := (r₀ : ZMod q) • w₀ + (s₀ : ZMod q) • ((a : ZMod q) • w₀) + m.1
  let e₁ := (r₁ : ZMod q) • g + (s₁ : ZMod q) • u
  let c₁ := (r₁ : ZMod q) • w₁ + (s₁ : ZMod q) • ((a : ZMod q) • w₁) + m.2
  Fin.cases (motive := fun j => DDHOTViewWords j)
    ⟨F.encode d m.1, F.encode d m.2, aBits, r₀Bits, s₀Bits, r₁Bits, s₁Bits,
      F.encode d w₀, F.encode d w₁⟩
    (fun _ => ⟨σ, bBits, F.encode d u, F.encode d e₀, F.encode d c₀, F.encode d e₁,
      F.encode d c₁⟩)
    i.1

/-- `ddhOTFullSimProb` is uniform strict PPT for `ddhOTEncoding`. -/
private theorem isPPT_ddhOTFullSimProb : F.ddhOTFullSimProb.IsPPT F.ddhOTEncoding := by
  let E := F.ddhOTEncoding
  refine isPPTOn_iff_encoded.mpr ((F.isPPTOn_sampleExpBits_six
    (n := fun x : SimInput F.ddhOTProbFamily Finset.univ => x.secParam) (d := fun x => x.desc)
    (encSimInput_secParam_polyTime E .id')
    (encSimInput_desc_polyTime E .id')
    (W := fun x aBits r₀Bits s₀Bits r₁Bits s₁Bits bBits =>
      encDPi (fun i : (Finset.univ : Finset (Fin 2)) => E.view.enc i.1)
        (F.ddhOTFullSimWords x.desc (x.inputs senderUniv) (x.inputs receiverUniv)
          aBits r₀Bits s₀Bits r₁Bits s₁Bits bBits))
    fun {γ encγ x aBits _ _ _ _ bBits} hx haBits hr₀Bits hs₀Bits hr₁Bits hs₁Bits hbBits =>
      ?_).congr fun x => ?_)
  · have hd : ComputableInPolyTime (fun c => (x c).desc) encγ F.encDesc :=
      encSimInput_desc_polyTime E hx
    have hm : ComputableInPolyTime (fun c => (F.encode (x c).desc ((x c).inputs senderUniv).1,
        F.encode (x c).desc ((x c).inputs senderUniv).2)) encγ (encPair encBits encBits) :=
      E.input.encCoalition_apply_polyTime (encSimInput_inputs_polyTime E hx) senderUniv
    have hσ : ComputableInPolyTime (fun c => ((x c).inputs receiverUniv : Bool)) encγ encBool :=
      E.input.encCoalition_apply_polyTime (encSimInput_inputs_polyTime E hx) receiverUniv
    have hq := F.computableInPolyTime_order.comp hd
    have hg := computableInPolyTime_encode_generator hd
    have ha := ComputableInPolyTime.bitsBinaryValue.comp haBits
    have hr₀ := ComputableInPolyTime.bitsBinaryValue.comp hr₀Bits
    have hs₀ := ComputableInPolyTime.bitsBinaryValue.comp hs₀Bits
    have hr₁ := ComputableInPolyTime.bitsBinaryValue.comp hr₁Bits
    have hs₁ := ComputableInPolyTime.bitsBinaryValue.comp hs₁Bits
    have hb := ComputableInPolyTime.bitsBinaryValue.comp hbBits
    have hu := computableInPolyTime_encode_natCast_smul hd ha hg
    have hv := computableInPolyTime_encode_natCast_smul hd hb hg
    have huSubV := computableInPolyTime_encode_add hd hu
      (computableInPolyTime_encode_natCast_smul hd (hq.binary_sub' (hb.binary_mod' hq)) hg)
    have hw₀ : ComputableInPolyTime (fun c => F.encode (x c).desc
        (cond ((x c).inputs receiverUniv : Bool)
          ((BitString.binaryValue (aBits c) : ZMod (F.order (x c).desc)) • F.generator (x c).desc +
            ((F.order (x c).desc - BitString.binaryValue (bBits c) % F.order (x c).desc : ℕ) :
              ZMod (F.order (x c).desc)) • F.generator (x c).desc)
          ((BitString.binaryValue (bBits c) : ZMod (F.order (x c).desc)) •
            F.generator (x c).desc))) encγ encBits :=
      .of_enc_eq (hσ.ite' huSubV hv) fun c => by
        obtain ⟨b', hb'⟩ : ∃ b' : Bool, (x c).inputs receiverUniv = b' := ⟨_, rfl⟩
        rw [hb']; cases b' <;> rfl
    have hw₁ : ComputableInPolyTime (fun c => F.encode (x c).desc
        (cond ((x c).inputs receiverUniv : Bool)
          ((BitString.binaryValue (bBits c) : ZMod (F.order (x c).desc)) •
            F.generator (x c).desc)
          ((BitString.binaryValue (aBits c) : ZMod (F.order (x c).desc)) • F.generator (x c).desc +
            ((F.order (x c).desc - BitString.binaryValue (bBits c) % F.order (x c).desc : ℕ) :
              ZMod (F.order (x c).desc)) • F.generator (x c).desc))) encγ encBits :=
      .of_enc_eq (hσ.ite' hv huSubV) fun c => by
        obtain ⟨b', hb'⟩ : ∃ b' : Bool, (x c).inputs receiverUniv = b' := ⟨_, rfl⟩
        rw [hb']; cases b' <;> rfl
    have he₀ := computableInPolyTime_encode_add hd
      (computableInPolyTime_encode_natCast_smul hd hr₀ hg)
      (computableInPolyTime_encode_natCast_smul hd hs₀ hu)
    have hc₀ := computableInPolyTime_encode_add hd
      (computableInPolyTime_encode_add hd
        (computableInPolyTime_encode_natCast_smul hd hr₀ hw₀)
        (computableInPolyTime_encode_natCast_smul hd hs₀
          (computableInPolyTime_encode_natCast_smul hd ha hw₀)))
      hm.fst'
    have he₁ := computableInPolyTime_encode_add hd
      (computableInPolyTime_encode_natCast_smul hd hr₁ hg)
      (computableInPolyTime_encode_natCast_smul hd hs₁ hu)
    have hc₁ := computableInPolyTime_encode_add hd
      (computableInPolyTime_encode_add hd
        (computableInPolyTime_encode_natCast_smul hd hr₁ hw₁)
        (computableInPolyTime_encode_natCast_smul hd hs₁
          (computableInPolyTime_encode_natCast_smul hd ha hw₁)))
      hm.snd'
    refine (ComputableInPolyTime.dpi fun i => ?_).encoding_comp
    obtain ⟨j, hj⟩ := i
    fin_cases j
    · exact encDDHOTSenderViewWords_mk_polyTime hm.fst' hm.snd' haBits hr₀Bits hs₀Bits hr₁Bits
        hs₁Bits hw₀ hw₁
    · exact encDDHOTReceiverViewWords_mk_polyTime hσ hbBits hu he₀ hc₀ he₁ hc₁
  · simp only [ddhOTFullSimProb, sampleDDHOTSenderBitCoins, ProbComp.eval_bind, ProbComp.eval_map,
      ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind, PMF.map_bind, PMF.pure_map]
    refine congrArg (PMF.bind _) (funext fun aBits =>
      congrArg (PMF.bind _) (funext fun r₀Bits =>
        congrArg (PMF.bind _) (funext fun s₀Bits =>
          congrArg (PMF.bind _) (funext fun r₁Bits =>
            congrArg (PMF.bind _) (funext fun s₁Bits =>
              congrArg (PMF.bind _) (funext fun bBits => congrArg PMF.pure ?_))))))
    change encDPi (fun i : (Finset.univ : Finset (Fin 2)) => E.view.enc i.1) _ =
      encDPi (fun i : (Finset.univ : Finset (Fin 2)) => E.view.enc i.1) _
    refine congrArg (encDPi _) (funext fun i => ?_)
    obtain ⟨n, d, xs, ys⟩ := x
    obtain ⟨j, hj⟩ := i
    let q := F.order d
    let g := F.generator d
    obtain ⟨σ, hσ⟩ : ∃ σ : Bool, xs receiverUniv = σ := ⟨_, rfl⟩
    let c₀ : DDHOTSenderBitCoins := ⟨aBits, r₀Bits, s₀Bits, r₁Bits, s₁Bits⟩
    fin_cases j
    · change F.ddhOTFullSimWords d (xs senderUniv) (xs receiverUniv)
          aBits r₀Bits s₀Bits r₁Bits s₁Bits bBits ⟨0, hj⟩ =
        F.ddhOTSenderViewWords d (ddhOTSenderViewWith (xs senderUniv) c₀
          (ddhOTReceiverMsg g (xs receiverUniv) (BitString.binaryValue bBits : ZMod q)
            ((c₀.toSenderCoins q).exponent • g)))
      rw [hσ]
      cases σ <;> simp only [ddhOTFullSimWords, ddhOTSenderViewWords, ddhOTSenderViewWith,
        DDHOTSenderBitCoins.toSenderCoins, ddhOTReceiverMsg, Bool.false_eq_true, ↓reduceIte,
        ZMod.natCast_sub_mod_eq_neg, neg_smul, ← sub_eq_add_neg] <;> rfl
    · change F.ddhOTFullSimWords d (xs senderUniv) (xs receiverUniv)
          aBits r₀Bits s₀Bits r₁Bits s₁Bits bBits ⟨1, hj⟩ =
        F.ddhOTReceiverViewWords d (ddhOTReceiverViewWith (xs receiverUniv) bBits
          ((c₀.toSenderCoins q).exponent • g)
          (ddhOTSenderReplyUnchecked g (xs senderUniv) (c₀.toSenderCoins q)
            (ddhOTReceiverMsg g (xs receiverUniv) (BitString.binaryValue bBits : ZMod q)
              ((c₀.toSenderCoins q).exponent • g))))
      rw [hσ]
      cases σ <;> simp only [ddhOTFullSimWords, ddhOTReceiverViewWords, ddhOTReceiverViewWith,
        DDHOTSenderBitCoins.toSenderCoins, ddhOTSenderReplyUnchecked, ddhOTEncryptBranch,
        ddhOTReceiverMsg, Bool.false_eq_true, ↓reduceIte, ZMod.natCast_sub_mod_eq_neg, neg_smul,
        ← sub_eq_add_neg] <;> rfl

/-- When both parties are corrupted, `ddhOTFullSimProb` reproduces `ddhOTProbProtocol`'s real joint
law exactly. -/
private theorem idealJoint_ddhOTProb_univ (n : ℕ) (d : F.Desc)
    (x : (i : Fin 2) → OTIn (F.Carrier d) i) :
    ProbComp.eval (idealJoint (otFunctionality (F.Carrier d)) Finset.univ
        (F.ddhOTFullSimProb n d) x) =
      (F.ddhOTProbProtocol n d).realJoint noOracleWorld Finset.univ x := by
  simp only [ddhOTProbProtocol, evalWith_ddhOTProtocolWith,
    Protocol.realJoint, eval_idealJoint, otFunctionality, Functionality.ofDeterministic,
    ddhOTFullSimProb, ProbComp.eval_bind, ProbComp.eval_pure,
    PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.pure_bind, PMF.pure_map, PMF.map_bind,
    Prod.map, id]
  rfl

/-! ### Security -/

/-- **Concrete statistical sender security of `ddhOTProbFamily`**: against a corrupted sender
(`{0}`), every environment `Z`—with no running-time bound and no computational assumption—has
advantage at most `2 / 2 ^ n` between the fair-coin real game and the ideal game with
`ddhOTSenderSimProb` (`1 / 2 ^ n` from the honest receiver's `sampleExpBits` draw plus `1 / 2 ^ n`
from the simulator's `bBits` draw, while the sender's five raw bit strings are drawn from the exact
same law in both games). -/
theorem advantage_ddhOTProbSenderGame_le (setup : ℕ → PMF F.Desc)
    (Z : Environment F.ddhOTProbFamily {0}) (n : ℕ) :
    Game.advantage (F.ddhOTProbFamily.realGame setup {0} Z n)
      (F.ddhOTProbFamily.idealGame setup {0} F.ddhOTSenderSimProb Z n) ≤ 2 / 2 ^ n := by
  simp only [ProtocolFamily.realGame, ProtocolFamily.idealGame, ddhOTProbProtocol,
    evalWith_ddhOTProtocolWith, Protocol.realJoint, eval_idealJoint, otFunctionality,
    Functionality.ofDeterministic, ddhOTSenderSimProb, ProbComp.eval_bind, ProbComp.eval_pure,
    PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind, PMF.map_bind,
    PMF.pure_map, Prod.map, id, restrict_singleton]
  refine Game.advantage_bind_le_nnreal _ _ _ fun d =>
    Game.advantage_bind_le_nnreal _ _ _ fun c => ?_
  let q := F.order d
  let g := F.generator d
  let realMid : Game :=
    (ProbComp.eval (F.sampleDDHOTSenderBitCoins n d)).bind fun raw₀ =>
      (PMF.uniformOfFintype (ZMod q)).bind fun b =>
        ProbComp.eval (Z.guess n d c.state
          (singletonView (ddhOTSenderViewWith (c.inputs 0) raw₀
            (ddhOTReceiverMsg g (c.inputs 1) b ((raw₀.toSenderCoins q).exponent • g))),
            otOutputs c.inputs))
  let idealMid : Game :=
    (ProbComp.eval (F.sampleDDHOTSenderBitCoins n d)).bind fun raw₀ =>
      (PMF.uniformOfFintype (ZMod q)).bind fun b =>
        ProbComp.eval (Z.guess n d c.state
          (ddhOTSenderSimWithCoinsOf (C₁ := List Bool) g (DDHOTSenderBitCoins.toSenderCoins q)
            raw₀ b (Finset.restrict {0} c.inputs), otOutputs c.inputs))
  have hmid : realMid = idealMid := by
    have h := idealJoint_ddhOT_sender_with (C₁ := List Bool) g q
      (F.sampleDDHOTSenderBitCoins n d) (DDHOTSenderBitCoins.toSenderCoins q) c.inputs
    simpa only [realMid, idealMid, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_bind,
      PMF.pure_bind] using
      congrArg (fun p => p.bind (Z.guess n d c.state · |>.eval)) h.symm
  have h1 : Game.advantage
      ((ProbComp.eval (F.sampleDDHOTSenderBitCoins n d)).bind fun raw₀ =>
        (ProbComp.eval (F.sampleExpBits n d)).bind fun bBits =>
          ProbComp.eval (Z.guess n d c.state
            (singletonView (ddhOTViewsWith g (DDHOTSenderBitCoins.toSenderCoins q)
              (fun bs => (BitString.binaryValue bs : ZMod q)) c.inputs raw₀ bBits 0),
              otOutputs c.inputs))) realMid ≤ 1 / 2 ^ n :=
    Game.advantage_bind_le_nnreal _ _ _ fun raw₀ =>
      F.advantage_bind_sampleExpBits_le n d fun b =>
        ProbComp.eval (Z.guess n d c.state
          (singletonView (ddhOTSenderViewWith (c.inputs 0) raw₀
            (ddhOTReceiverMsg g (c.inputs 1) b ((raw₀.toSenderCoins q).exponent • g))),
            otOutputs c.inputs))
  have h2 : Game.advantage idealMid
      ((ProbComp.eval (F.sampleDDHOTSenderBitCoins n d)).bind fun raw₀ =>
        (ProbComp.eval (F.sampleExpBits n d)).bind fun bBits =>
          ProbComp.eval (Z.guess n d c.state
            (ddhOTSenderSimWithCoinsOf (C₁ := List Bool) g (DDHOTSenderBitCoins.toSenderCoins q)
              raw₀ (BitString.binaryValue bBits : ZMod q) (Finset.restrict {0} c.inputs),
              otOutputs c.inputs))) ≤ 1 / 2 ^ n := by
    rw [Game.advantage_comm]
    exact Game.advantage_bind_le_nnreal _ _ _ fun raw₀ =>
      F.advantage_bind_sampleExpBits_le n d fun b =>
        ProbComp.eval (Z.guess n d c.state
          (ddhOTSenderSimWithCoinsOf (C₁ := List Bool) g (DDHOTSenderBitCoins.toSenderCoins q)
            raw₀ b (Finset.restrict {0} c.inputs), otOutputs c.inputs))
  calc _ ≤ (1 : ℝ≥0) / 2 ^ n + 1 / 2 ^ n :=
        (Game.advantage_triangle _ realMid _).trans (add_le_add h1 (hmid ▸ h2))
    _ = 2 / 2 ^ n := by rw [← add_div, one_add_one_eq_two]

/-- Step toward the corrupted-sender case of [BonehShoup2023], Section 23.5.7.2, Theorem 23.7
(pp. 1058, 1060), not the cited result: this proves two-stage stand-alone
`ProtocolFamily.SemiHonestSecure` at `{0}` for the checked per-branch-coin variant
`ddhOTProbFamily` rather than Section 23.5.6 interactive emulation of `F_ot` for Figure 23.17
(#5829, #5293). `F.ddhOTProbFamily` is semi-honest secure against a corrupted sender (`{0}`) for
every setup law `setup`, with no hardness assumption (`advantage_ddhOTProbSenderGame_le`,
`≤ 2 / 2 ^ n`). -/
theorem ddhOTProbFamily_semiHonestSecure_sender (setup : ℕ → PMF F.Desc) :
    F.ddhOTProbFamily.SemiHonestSecure setup {0} F.ddhOTEncoding :=
  ⟨F.ddhOTSenderSimProb, F.isPPT_ddhOTSenderSimProb, fun Z _ => by
    negligible using F.advantage_ddhOTProbSenderGame_le setup Z⟩

/-- **Concrete receiver reduction bound for `ddhOTProbFamily`**: against a corrupted receiver
(`{1}`), every environment `Z` has advantage between the fair-coin real game and the ideal game
with `ddhOTReceiverSimProb` at most the DDH advantage of `ddhOTReceiverToDDHDistinguisher Z` plus
`14 / 2 ^ n` (`9 / 2 ^ n` from `advantage_ddhOTReceiverGame_le` plus `5 / 2 ^ n` from
`advantage_bind_ddhOTReceiverSimProb_le`, with zero loss on the receiver's raw coin bit string). -/
theorem advantage_ddhOTProbReceiverGame_le (setup : ℕ → PMF F.Desc)
    (Z : Environment F.ddhOTProbFamily {1}) (n : ℕ) :
    Game.advantage (F.ddhOTProbFamily.realGame setup {1} Z n)
        (F.ddhOTProbFamily.idealGame setup {1} F.ddhOTReceiverSimProb Z n) ≤
      Game.advantage (F.ddhRealGame setup (F.ddhOTReceiverToDDHDistinguisher Z) n)
        (F.ddhRandomGame setup (F.ddhOTReceiverToDDHDistinguisher Z) n) + 14 / 2 ^ n := by
  calc _ ≤ (Game.advantage (F.ddhRealGame setup (F.ddhOTReceiverToDDHDistinguisher Z) n)
          (F.ddhRandomGame setup (F.ddhOTReceiverToDDHDistinguisher Z) n) + 9 / 2 ^ n) +
        5 / 2 ^ n :=
      (Game.advantage_triangle _ _ _).trans (add_le_add
        (F.advantage_ddhOTReceiverGame_le setup Z n)
        (ProtocolFamily.advantage_idealGame_le
          (F.advantage_bind_ddhOTReceiverSimProb_le n) Z))
    _ = _ := by ring

/-- Step toward [BonehShoup2023], Section 23.5.7.2, Theorem 23.7 (p. 1058), not the cited result:
this proves two-stage stand-alone `ProtocolFamily.SemiHonestSecure` for the checked
per-branch-coin variant `ddhOTProbFamily` rather than execution indistinguishability against
interactive report/control environments implementing `F_ot` in the restricted framework of
Section 23.5.6 (pp. 1054–1056) for Figure 23.17 (#5829, #5293).

Under `F.DDH setup`, `F.ddhOTProbFamily`—whose parties draw raw fair-coin bit strings via
`sampleExpBits` and record those unreduced bit strings in `PartyView.coins`, as in Remark 23.5
(p. 1059) and [Lindell2017], Section 4.2, Definition 4.1 (p. 7)—satisfies
`ProtocolFamily.SemiHonestSecure` across every static coalition `I : Finset (Fin 2)` with
certified uniform strict-PPT simulators and DDH reduction:
* `I = ∅` (no corruption): exact simulation (`SimulatorFamily.empty`, advantage `0`);
* `I = {0}` (corrupted sender): unconditional statistical simulation (`ddhOTSenderSimProb`,
  advantage `≤ 2 / 2 ^ n`);
* `I = {1}` (corrupted receiver): computational simulation (`ddhOTReceiverSimProb`) via the
  certified reduction `ddhOTReceiverToDDHDistinguisher` (advantage `≤ ddhAdv + 14 / 2 ^ n`);
* `I = Finset.univ` (full corruption): exact simulation (`ddhOTFullSimProb`, advantage `0`). -/
theorem DDH.ddhOTProbFamily_semiHonestSecure {F : PrimeOrderGroupFamily} {setup : ℕ → PMF F.Desc}
    (hDDH : F.DDH setup) (I : Finset (Fin 2)) :
    F.ddhOTProbFamily.SemiHonestSecure setup I F.ddhOTEncoding := by
  have hcases : I = ∅ ∨ I = {0} ∨ I = {1} ∨ I = Finset.univ := by
    by_cases h0 : (0 : Fin 2) ∈ I <;> by_cases h1 : (1 : Fin 2) ∈ I
    · right; right; right; ext i; fin_cases i <;> simp [h0, h1]
    · right; left; ext i; fin_cases i <;> simp [h0, h1]
    · right; right; left; ext i; fin_cases i <;> simp [h0, h1]
    · left; ext i; fin_cases i <;> simp [h0, h1]
  rcases hcases with rfl | rfl | rfl | rfl
  · exact ProtocolFamily.SemiHonestSecure.of_perfect
      (SimulatorFamily.isPPT_empty _) F.idealJoint_ddhOTProb_empty
  · exact F.ddhOTProbFamily_semiHonestSecure_sender setup
  · refine ⟨F.ddhOTReceiverSimProb, F.isPPT_ddhOTReceiverSimProb, fun Z hZ => ?_⟩
    have hB := hDDH _ (F.isPPT_ddhOTReceiverToDDHDistinguisher hZ)
    negligible using F.advantage_ddhOTProbReceiverGame_le setup Z
  · exact ProtocolFamily.SemiHonestSecure.of_perfect
      F.isPPT_ddhOTFullSimProb F.idealJoint_ddhOTProb_univ

end Cslib.Crypto.PrimeOrderGroupFamily
