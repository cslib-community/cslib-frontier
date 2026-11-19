/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.MPC.DDHOT.Family
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Captured
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.DPi
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Crypto.Computational.DiffieHellman.SampleExp
import CslibFrontier.Foundations.Data.ZMod.NatCast
import CslibFrontier.Tactic.Negligible

/-!
# Fair-coin semi-honest security of DDH oblivious transfer with PPT simulators

`CslibFrontier/Crypto/Protocols/MPC/DDHOT/Family.lean` runs both the exact-coin reference protocol
`ddhOTFamily` and the fair-coin protocol `ddhOTProbFamily` (`ddhOTProbProtocol`, whose parties
derive exponents from random bit strings via `sampleExp n d` as in [BonehShoup2023], Remark 23.5,
p. 1059) over a `PrimeOrderGroupFamily` `F`, with the encoding `ddhOTEncoding`, and reduces a
corrupted receiver to DDH. Because no bounded-time fair-coin machine can draw an exact uniform
element of `ZMod (F.order d)` for an odd prime order, this module also runs the simulator algorithms
(`ddhOTSenderSimWithCoins`, `ddhOTReceiverSimWithCoins`) on six exponents drawn with `sampleExp n d`
(`ddhOTSenderSimSampleExp`, `ddhOTReceiverSimSampleExp`), proves them PPT for `ddhOTEncoding`, and
bounds their statistical distance from the exact-sampling simulators by `6 / 2 ^ n`.

Combining these simulators (together with exact simulators when neither or both parties are
corrupted) with `advantage_realGame_ddhOTProbFamily_le` (`≤ 6 / 2 ^ n` for the six honest-party
`sampleExp` draws) gives semi-honest security of the fair-coin protocol `ddhOTProbFamily` across
every static coalition `I : Finset (Fin 2)` under `F.DDH setup` alone (`DDH.ddhOTSemiHonestSecure`,
[BonehShoup2023], Theorem 23.7, p. 1058):
* against a corrupted sender (`I = {0}`), security is unconditional and statistical: every
  environment, efficient or not, has advantage at most `12 / 2 ^ n`
  (`advantage_ddhOTProbSenderGame_le`, `ddhOTProbFamily_semiHonestSecure_sender`);
* against a corrupted receiver (`I = {1}`), every environment's advantage is at most the DDH
  advantage of `ddhOTReceiverToDDHDistinguisher Z` plus `18 / 2 ^ n`
  (`advantage_ddhOTProbReceiverGame_le`);
* when neither (`I = ∅`) or both (`I = Finset.univ`) parties are corrupted, simulation is exact
  (`advantage = 0`).

## Comparison with [BonehShoup2023], Theorem 23.7

`DDH.ddhOTSemiHonestSecure` formalizes [BonehShoup2023], Section 23.5.7.2, Theorem 23.7 (p. 1058),
for the fair-coin protocol `ddhOTProbFamily` over every static coalition `I : Finset (Fin 2)`, with
certified uniform strict-PPT simulators and DDH reduction, and with the following differences:

* **Protocol variant (`ddhOTProbProtocol` vs. Figure 23.17, p. 1057):** as documented in
  `DDHOT.lean`, the sender draws five exponents `(a, r₀, s₀, r₁, s₁)` via `sampleExp n d` and sends
  `u = a • g` (knowing the discrete logarithm `a`, whereas Figure 23.17 samples `d` directly from
  `G`), encrypts each branch `i` with independent randomization coins `(rᵢ, sᵢ)` rather than one
  shared exponent `β`, and checks `w₀ + w₁ = u` (the check of Section 23.5.7.3, Remark 23.6,
  p. 1061, returning zeros instead of aborting when violated);
* **Party coin representation (`DDHOTCoins` vs. p. 1059):** both honest parties and simulators
  generate random bit strings and reduce modulo `F.order d` via `sampleExp n d` (Remark 23.5,
  p. 1059, incurring statistical distance `≤ 1 / 2 ^ n` per draw); a party's `PartyView` records
  these derived `ZMod (F.order d)` exponents (encoded as natural numbers below `F.order d`) rather
  than the unreduced bit strings before modular reduction;
* **Stand-alone semi-honest execution model (`ProtocolFamily.SemiHonestSecure` vs. Section 23.5.6 &
  Definition 23.5, pp. 1043–1044, 1054–1056):** a two-stage uniform strict-PPT environment chooses
  inputs after seeing `(1ⁿ, d)` drawn from an arbitrary setup law `setup n` and distinguishes the
  corrupted coalition's views paired with all parties' outputs (`otFunctionality`), rather than
  exchanging control and report messages during execution in the restricted framework of
  Section 23.5.6, and `IsPPTOn` bounds running time on every execution rather than with overwhelming
  probability (Section 23.5.2.2, p. 1043).

## Comparison with [Lindell2017], Definition 4.1

For two parties, [Lindell2017], Section 4.2, Definition 4.1 (p. 7) corresponds to
`SemiHonestSecure` at `I = {0}` and `I = {1}`, up to the general differences of
`ProtocolFamily.SemiHonestSecure` documented in `CslibFrontier/Crypto/Protocols/MPC/Asymptotic.lean`
(uniform environments that choose inputs after seeing `d` from `setup n`) and the representation of
a party's coins in `PartyView` as the `ZMod (F.order d)` exponents derived by `sampleExp n d`
rather than its raw random tape.

## Main definitions

* `Cslib.Crypto.PrimeOrderGroupFamily.ddhOTSenderSimSampleExp`,
  `Cslib.Crypto.PrimeOrderGroupFamily.ddhOTReceiverSimSampleExp`: the simulator families for `{0}`
  and `{1}` that draw their exponents with `sampleExp`.

## Main results

* `Cslib.Crypto.PrimeOrderGroupFamily.isPPT_ddhOTSenderSimSampleExp`,
  `Cslib.Crypto.PrimeOrderGroupFamily.isPPT_ddhOTReceiverSimSampleExp`: the simulator families are
  PPT for `ddhOTEncoding`.
* `Cslib.Crypto.PrimeOrderGroupFamily.advantage_bind_ddhOTSenderSimSampleExp_le`,
  `Cslib.Crypto.PrimeOrderGroupFamily.advantage_bind_ddhOTReceiverSimSampleExp_le`: on every input,
  they are within statistical distance `6 / 2 ^ n` of the exact-sampling simulators.
* `Cslib.Crypto.PrimeOrderGroupFamily.advantage_ddhOTProbSenderGame_le`,
  `Cslib.Crypto.PrimeOrderGroupFamily.ddhOTProbFamily_semiHonestSecure_sender`: against a corrupted
  sender, every environment (efficient or not) has advantage at most `12 / 2 ^ n`, giving
  unconditional semi-honest security of `ddhOTProbFamily` at `{0}`.
* `Cslib.Crypto.PrimeOrderGroupFamily.advantage_ddhOTProbReceiverGame_le`: against a corrupted
  receiver, every environment has advantage at most the DDH advantage of
  `ddhOTReceiverToDDHDistinguisher Z` plus `18 / 2 ^ n`.
* `Cslib.Crypto.PrimeOrderGroupFamily.DDH.ddhOTSemiHonestSecure`: under `F.DDH setup`,
  `ddhOTProbFamily` is semi-honest secure for every static coalition `I : Finset (Fin 2)`
  ([BonehShoup2023], Theorem 23.7).

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

/-- The simulator family for a corrupted sender that runs the algorithm of `ddhOTSenderSim`,
`ddhOTSenderSimWithCoins`, on six exponents drawn with `sampleExp n d` instead of exact uniform
ones. -/
@[expose] noncomputable def ddhOTSenderSimSampleExp
    {proto : (n : ℕ) → (d : F.Desc) →
      Protocol 2 noOracleSpec (ddhOTSchedule (F.Carrier d)) (OTIn (F.Carrier d))
        (DDHOTCoins (F.order d)) (OTOut (F.Carrier d))} :
    SimulatorFamily (F.ddhOTFamilyWith proto) {0} :=
  fun n d xI _ => do
    let a ← F.sampleExp n d
    let r₀ ← F.sampleExp n d
    let s₀ ← F.sampleExp n d
    let r₁ ← F.sampleExp n d
    let s₁ ← F.sampleExp n d
    let b ← F.sampleExp n d
    return ddhOTSenderSimWithCoins (F.generator d) ((a : ZMod (F.order d)),
      (r₀ : ZMod (F.order d)), (s₀ : ZMod (F.order d)), (r₁ : ZMod (F.order d)),
      (s₁ : ZMod (F.order d))) b xI

/-- The simulator family for a corrupted receiver that runs the algorithm of `ddhOTReceiverSim`,
`ddhOTReceiverSimWithCoins`, on six exponents drawn with `sampleExp n d` instead of exact uniform
ones. -/
@[expose] noncomputable def ddhOTReceiverSimSampleExp
    {proto : (n : ℕ) → (d : F.Desc) →
      Protocol 2 noOracleSpec (ddhOTSchedule (F.Carrier d)) (OTIn (F.Carrier d))
        (DDHOTCoins (F.order d)) (OTOut (F.Carrier d))} :
    SimulatorFamily (F.ddhOTFamilyWith proto) {1} :=
  fun n d xI yI => do
    let a ← F.sampleExp n d
    let b ← F.sampleExp n d
    let r ← F.sampleExp n d
    let s ← F.sampleExp n d
    let k ← F.sampleExp n d
    let c ← F.sampleExp n d
    return ddhOTReceiverSimWithCoins (F.generator d) a b r s k c xI yI

/-! ### Statistical closeness to the exact-sampling simulators -/

/-- On every input, no test `k` tells `ddhOTSenderSimSampleExp` from `ddhOTSenderSim` with
advantage more than `6 / 2 ^ n`. -/
theorem advantage_bind_ddhOTSenderSimSampleExp_le
    {proto : (n : ℕ) → (d : F.Desc) →
      Protocol 2 noOracleSpec (ddhOTSchedule (F.Carrier d)) (OTIn (F.Carrier d))
        (DDHOTCoins (F.order d)) (OTOut (F.Carrier d))}
    (n : ℕ) (d : F.Desc)
    (xI : (i : ({0} : Finset (Fin 2))) → OTIn (F.Carrier d) i)
    (yI : (i : ({0} : Finset (Fin 2))) → OTOut (F.Carrier d) i)
    (k : ((i : ({0} : Finset (Fin 2))) →
      PartyView (OTIn (F.Carrier d)) (DDHOTCoins (F.order d)) (ddhOTSchedule (F.Carrier d)) i) →
        Game) :
    Game.advantage ((ProbComp.eval (ddhOTSenderSim (F.generator d) (F.order d) xI yI)).bind k)
      ((ProbComp.eval (F.ddhOTSenderSimSampleExp (proto := proto) n d xI yI)).bind k) ≤
        6 / 2 ^ n := by
  simp only [ddhOTSenderSim, ddhOTSenderSimSampleExp, sampleDDHOTSenderCoins, ProbComp.eval_bind,
    ProbComp.eval_pure, ProbComp.eval_uniform, PMF.bind_bind, PMF.pure_bind]
  rw [Game.advantage_comm]
  have h := F.advantage_bind_iid_sampleExp_le n d 6 fun a =>
    k (ddhOTSenderSimWithCoins (F.generator d) (a 0, a 1, a 2, a 3, a 4) (a 5) xI)
  simp only [PMF.iid, PMF.monad_bind_eq_bind, PMF.bind_bind, PMF.bind_map, PMF.pure_bind,
    Function.comp_def, Nat.cast_ofNat] at h
  exact h

/-- On every input, no test `k` tells `ddhOTReceiverSimSampleExp` from `ddhOTReceiverSim` with
advantage more than `6 / 2 ^ n`. -/
theorem advantage_bind_ddhOTReceiverSimSampleExp_le
    {proto : (n : ℕ) → (d : F.Desc) →
      Protocol 2 noOracleSpec (ddhOTSchedule (F.Carrier d)) (OTIn (F.Carrier d))
        (DDHOTCoins (F.order d)) (OTOut (F.Carrier d))}
    (n : ℕ) (d : F.Desc)
    (xI : (i : ({1} : Finset (Fin 2))) → OTIn (F.Carrier d) i)
    (yI : (i : ({1} : Finset (Fin 2))) → OTOut (F.Carrier d) i)
    (k : ((i : ({1} : Finset (Fin 2))) →
      PartyView (OTIn (F.Carrier d)) (DDHOTCoins (F.order d)) (ddhOTSchedule (F.Carrier d)) i) →
        Game) :
    Game.advantage ((ProbComp.eval (ddhOTReceiverSim (F.generator d) (F.order d) xI yI)).bind k)
      ((ProbComp.eval (F.ddhOTReceiverSimSampleExp (proto := proto) n d xI yI)).bind k) ≤
        6 / 2 ^ n := by
  simp only [ddhOTReceiverSim, ddhOTReceiverSimSampleExp, ProbComp.eval_bind, ProbComp.eval_pure,
    ProbComp.eval_uniform, PMF.bind_bind, PMF.pure_bind]
  rw [Game.advantage_comm]
  have h := F.advantage_bind_iid_sampleExp_le n d 6 fun a =>
    k (ddhOTReceiverSimWithCoins (F.generator d) (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) xI yI)
  simp only [PMF.iid, PMF.monad_bind_eq_bind, PMF.bind_bind, PMF.bind_map, PMF.pure_bind,
    Function.comp_def, Nat.cast_ofNat] at h
  exact h

/-! ### Efficiency of the simulator families -/

/-- Six `sampleExp` draws followed by an efficiently computable function of the input and the
draws are uniform strict PPT. -/
private theorem isPPTOn_sampleExp_six {α β : Type} {enc : α ↪ List Bool}
    {encOut : β ↪ List Bool} {n : α → ℕ} {d : α → F.Desc}
    (hn : ComputableInPolyTime n enc encUnary) (hd : ComputableInPolyTime d enc F.encDesc)
    {W : α → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → β}
    (hW : ∀ {γ : Type} {encγ : γ ↪ List Bool} {x : γ → α} {a₁ a₂ a₃ a₄ a₅ a₆ : γ → ℕ},
      ComputableInPolyTime x encγ enc → ComputableInPolyTime a₁ encγ encNat →
      ComputableInPolyTime a₂ encγ encNat → ComputableInPolyTime a₃ encγ encNat →
      ComputableInPolyTime a₄ encγ encNat → ComputableInPolyTime a₅ encγ encNat →
      ComputableInPolyTime a₆ encγ encNat →
      ComputableInPolyTime (fun c => W (x c) (a₁ c) (a₂ c) (a₃ c) (a₄ c) (a₅ c) (a₆ c)) encγ
        encOut) :
    IsPPTOn enc encOut (fun x => do
      let a₁ ← F.sampleExp (n x) (d x)
      let a₂ ← F.sampleExp (n x) (d x)
      let a₃ ← F.sampleExp (n x) (d x)
      let a₄ ← F.sampleExp (n x) (d x)
      let a₅ ← F.sampleExp (n x) (d x)
      let a₆ ← F.sampleExp (n x) (d x)
      pure (W x a₁ a₂ a₃ a₄ a₅ a₆)) := by
  have hsample {γ : Type} {encγ : γ ↪ List Bool} {x : γ → α}
      (hx : ComputableInPolyTime x encγ enc) :
      IsPPTOn encγ encNat fun c => F.sampleExp (n (x c)) (d (x c)) :=
    F.isPPTOn_sampleExp (hn.comp hx) (hd.comp hx)
  refine IsPPTOn.bind_with (hsample .id') ?_
  refine IsPPTOn.bind_with (hsample (by fun_prop)) ?_
  refine IsPPTOn.bind_with (hsample (by fun_prop)) ?_
  refine IsPPTOn.bind_with (hsample (by fun_prop)) ?_
  refine IsPPTOn.bind_with (hsample (by fun_prop)) ?_
  refine IsPPTOn.bind_with (hsample (by fun_prop)) ?_
  exact (hW (γ := ((((((α × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ)) (x := fun p => p.1.1.1.1.1.1)
    (a₁ := fun p => p.1.1.1.1.1.2) (a₂ := fun p => p.1.1.1.1.2) (a₃ := fun p => p.1.1.1.2)
    (a₄ := fun p => p.1.1.2) (a₅ := fun p => p.1.2) (a₆ := fun p => p.2) (by fun_prop)
    (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)).isPPTOn

/-- The view words that `ddhOTSenderSimSampleExp` writes at group parameters `d` on the sender's
messages `m = (m₀, m₁)` and exponents `a, r₀, s₀, r₁, s₁, b`: the exponents reduced modulo
`q = F.order d`, and the branch keys `b • g` and `a • g + (q - b % q) • g`. -/
private def ddhOTSenderSimWords (d : F.Desc) (m : F.Carrier d × F.Carrier d)
    (a r₀ s₀ r₁ s₁ b : ℕ) : DDHOTSenderViewWords :=
  let q := F.order d
  let g := F.generator d
  ⟨F.encode d m.1, F.encode d m.2, a % q, r₀ % q, s₀ % q, r₁ % q, s₁ % q,
    F.encode d ((b : ZMod q) • g), F.encode d ((a : ZMod q) • g + ((q - b % q : ℕ) : ZMod q) • g)⟩

/-- The party `0` of the coalition `{0}`. -/
private abbrev sender : ({0} : Finset (Fin 2)) := ⟨0, Finset.mem_singleton_self 0⟩

/-- `ddhOTSenderSimSampleExp` is PPT for `ddhOTEncoding`. -/
theorem isPPT_ddhOTSenderSimSampleExp
    {proto : (n : ℕ) → (d : F.Desc) →
      Protocol 2 noOracleSpec (ddhOTSchedule (F.Carrier d)) (OTIn (F.Carrier d))
        (DDHOTCoins (F.order d)) (OTOut (F.Carrier d))} :
    (F.ddhOTSenderSimSampleExp (proto := proto)).IsPPT F.ddhOTEncoding := by
  let E := F.ddhOTEncoding (proto := proto)
  refine isPPTOn_iff_encoded.mpr ((F.isPPTOn_sampleExp_six
    (n := fun x : SimInput (F.ddhOTFamilyWith proto) {0} => x.secParam) (d := fun x => x.desc)
    (encSimInput_secParam_polyTime E .id')
    (encSimInput_desc_polyTime E .id')
    (W := fun x a r₀ s₀ r₁ s₁ b => encPi encBits fun _ : ({0} : Finset (Fin 2)) =>
      encDDHOTSenderViewWords (F.ddhOTSenderSimWords x.desc (x.inputs sender) a r₀ s₀ r₁ s₁ b))
    fun {γ encγ x _ _ _ _ _ _} hx ha hr₀ hs₀ hr₁ hs₁ hb => ?_).congr fun x => ?_)
  · have hd : ComputableInPolyTime (fun c => (x c).desc) encγ F.encDesc :=
      encSimInput_desc_polyTime E hx
    have hm : ComputableInPolyTime (fun c => (F.encode (x c).desc ((x c).inputs sender).1,
        F.encode (x c).desc ((x c).inputs sender).2)) encγ (encPair encBits encBits) :=
      E.input.encCoalition_apply_polyTime (encSimInput_inputs_polyTime E hx) sender
    have hq := F.computableInPolyTime_order.comp hd
    have hg := computableInPolyTime_encode_generator hd
    exact (ComputableInPolyTime.pi fun _ => (encDDHOTSenderViewWords_mk_polyTime hm.fst' hm.snd'
      (ha.binary_mod' hq) (hr₀.binary_mod' hq) (hs₀.binary_mod' hq) (hr₁.binary_mod' hq)
      (hs₁.binary_mod' hq) (computableInPolyTime_encode_natCast_smul hd hb hg)
      (computableInPolyTime_encode_add hd (computableInPolyTime_encode_natCast_smul hd ha hg)
        (computableInPolyTime_encode_natCast_smul hd (hq.binary_sub' (hb.binary_mod' hq))
          hg))).encoding_comp).encoding_comp
  · simp only [ddhOTSenderSimSampleExp, ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_pure,
      PMF.map_bind, PMF.pure_map]
    refine congrArg (PMF.bind _) (funext fun a => congrArg (PMF.bind _) (funext fun r₀ =>
      congrArg (PMF.bind _) (funext fun s₀ => congrArg (PMF.bind _) (funext fun r₁ =>
        congrArg (PMF.bind _) (funext fun s₁ => congrArg (PMF.bind _) (funext fun b =>
          congrArg PMF.pure ?_))))))
    refine Eq.trans ?_ (E.view.encCoalition_singleton x.secParam x.desc 0 _).symm
    refine congrArg (encPi encBits) (funext fun _ => congrArg encDDHOTSenderViewWords ?_)
    obtain ⟨n, d, xs, ys⟩ := x
    let q := F.order d
    let g := F.generator d
    change _ = F.ddhOTSenderViewWords d (ddhOTSenderView (xs sender)
      ((a : ZMod q), (r₀ : ZMod q), (s₀ : ZMod q), (r₁ : ZMod q), (s₁ : ZMod q))
      ((b : ZMod q) • g, (a : ZMod q) • g - (b : ZMod q) • g))
    simp only [ddhOTSenderSimWords, ddhOTSenderViewWords, ddhOTSenderView,
      ZMod.natCast_sub_mod_eq_neg, neg_smul, ← sub_eq_add_neg, ZMod.val_natCast]
    rfl

/-- The view words that `ddhOTReceiverSimSampleExp` writes at group parameters `d` on the choice
bit `σ`, the receiver's output `m` and exponents `a, b, r, s, k, c`: the coin reduced modulo
`F.order d`, the first message `a • g`, and the branches `(e, b • e + m)` with
`e = r • g + s • (a • g)` and `(k • g, c • g)`, in the order given by the choice bit. -/
private def ddhOTReceiverSimWords (d : F.Desc) (σ : Bool) (m : F.Carrier d) (a b r s k c : ℕ) :
    DDHOTReceiverViewWords :=
  let q := F.order d
  let g := F.generator d
  let e := (r : ZMod q) • g + (s : ZMod q) • (a : ZMod q) • g
  let chosen₁ := F.encode d e
  let chosen₂ := F.encode d ((b : ZMod q) • e + m)
  let other₁ := F.encode d ((k : ZMod q) • g)
  let other₂ := F.encode d ((c : ZMod q) • g)
  ⟨σ, b % q, F.encode d ((a : ZMod q) • g), if σ then other₁ else chosen₁,
    if σ then other₂ else chosen₂, if σ then chosen₁ else other₁, if σ then chosen₂ else other₂⟩

/-- The party `1` of the coalition `{1}`. -/
private abbrev receiver : ({1} : Finset (Fin 2)) := ⟨1, Finset.mem_singleton_self 1⟩

/-- `ddhOTReceiverSimSampleExp` is PPT for `ddhOTEncoding`. -/
theorem isPPT_ddhOTReceiverSimSampleExp
    {proto : (n : ℕ) → (d : F.Desc) →
      Protocol 2 noOracleSpec (ddhOTSchedule (F.Carrier d)) (OTIn (F.Carrier d))
        (DDHOTCoins (F.order d)) (OTOut (F.Carrier d))} :
    (F.ddhOTReceiverSimSampleExp (proto := proto)).IsPPT F.ddhOTEncoding := by
  let E := F.ddhOTEncoding (proto := proto)
  refine isPPTOn_iff_encoded.mpr ((F.isPPTOn_sampleExp_six
    (n := fun x : SimInput (F.ddhOTFamilyWith proto) {1} => x.secParam) (d := fun x => x.desc)
    (encSimInput_secParam_polyTime E .id')
    (encSimInput_desc_polyTime E .id')
    (W := fun x a b r s k c => encPi encBits fun _ : ({1} : Finset (Fin 2)) =>
      encDDHOTReceiverViewWords
        (F.ddhOTReceiverSimWords x.desc (x.inputs receiver) (x.outputs receiver) a b r s k c))
    fun {γ encγ x _ _ _ _ _ _} hx ha hb hr hs hk hc => ?_).congr fun x => ?_)
  · have hd : ComputableInPolyTime (fun c => (x c).desc) encγ F.encDesc :=
      encSimInput_desc_polyTime E hx
    have hσ : ComputableInPolyTime (fun c => ((x c).inputs receiver : Bool)) encγ encBool :=
      E.input.encCoalition_apply_polyTime (encSimInput_inputs_polyTime E hx) receiver
    have hm : ComputableInPolyTime (fun c => F.encode (x c).desc ((x c).outputs receiver)) encγ
        encBits :=
      E.output.encCoalition_apply_polyTime (encSimInput_outputs_polyTime E hx) receiver
    have hg := computableInPolyTime_encode_generator hd
    have hu := computableInPolyTime_encode_natCast_smul hd ha hg
    have he := computableInPolyTime_encode_add hd
      (computableInPolyTime_encode_natCast_smul hd hr hg)
      (computableInPolyTime_encode_natCast_smul hd hs hu)
    have hbody := computableInPolyTime_encode_add hd
      (computableInPolyTime_encode_natCast_smul hd hb he) hm
    have hk' := computableInPolyTime_encode_natCast_smul hd hk hg
    have hc' := computableInPolyTime_encode_natCast_smul hd hc hg
    exact (ComputableInPolyTime.pi fun _ => (encDDHOTReceiverViewWords_mk_polyTime hσ
      (hb.binary_mod' (F.computableInPolyTime_order.comp hd)) hu (hσ.ite' hk' he)
      (hσ.ite' hc' hbody) (hσ.ite' he hk') (hσ.ite' hbody hc')).encoding_comp).encoding_comp
  · simp only [ddhOTReceiverSimSampleExp, ProbComp.eval_bind, ProbComp.eval_map,
      ProbComp.eval_pure, PMF.map_bind, PMF.pure_map]
    refine congrArg (PMF.bind _) (funext fun a => congrArg (PMF.bind _) (funext fun b =>
      congrArg (PMF.bind _) (funext fun r => congrArg (PMF.bind _) (funext fun s =>
        congrArg (PMF.bind _) (funext fun k => congrArg (PMF.bind _) (funext fun c =>
          congrArg PMF.pure ?_))))))
    refine Eq.trans ?_ (E.view.encCoalition_singleton x.secParam x.desc 1 _).symm
    refine congrArg (encPi encBits) (funext fun _ => congrArg encDDHOTReceiverViewWords ?_)
    obtain ⟨n, d, xs, ys⟩ := x
    let q := F.order d
    let g := F.generator d
    dsimp only
    simp only [ddhOTReceiverSimWithCoins]
    obtain ⟨σ, hσ⟩ : ∃ σ : Bool, xs receiver = σ := ⟨_, rfl⟩
    obtain ⟨m, hm⟩ : ∃ m : F.Carrier d, ys receiver = m := ⟨_, rfl⟩
    rw [hσ, hm]
    let e := (r : ZMod q) • g + (s : ZMod q) • (a : ZMod q) • g
    change _ = F.ddhOTReceiverViewWords d (ddhOTReceiverView σ (b : ZMod q) ((a : ZMod q) • g)
      (if σ then (((k : ZMod q) • g, (c : ZMod q) • g), (e, (b : ZMod q) • e + m))
        else ((e, (b : ZMod q) • e + m), ((k : ZMod q) • g, (c : ZMod q) • g))))
    cases σ <;> simp only [ddhOTReceiverSimWords, ddhOTReceiverViewWords, ddhOTReceiverView,
      Bool.false_eq_true, ↓reduceIte, ZMod.val_natCast] <;> rfl

/-! ### Empty and full coalitions -/

/-- Simulator for `I = ∅` (no corrupted parties): returns the unique empty view table. -/
private def ddhOTEmptySim : SimulatorFamily F.ddhOTProbFamily ∅ :=
  fun _ _ _ _ => pure fun i => nomatch i.2

/-- `ddhOTEmptySim` is PPT for `ddhOTEncoding`. -/
private theorem isPPT_ddhOTEmptySim : F.ddhOTEmptySim.IsPPT F.ddhOTEncoding :=
  (ComputableInPolyTime.dpi fun i : (∅ : Finset (Fin 2)) => nomatch i.2).isPPTOn.congr fun _ => rfl

/-- When no party is corrupted, `ddhOTEmptySim` reproduces `ddhOTProbProtocol`'s real joint law
exactly. -/
private theorem idealJoint_ddhOTProb_empty (n : ℕ) (d : F.Desc)
    (x : (i : Fin 2) → OTIn (F.Carrier d) i) :
    ProbComp.eval (idealJoint (otFunctionality (F.Carrier d)) ∅ (F.ddhOTEmptySim n d) x) =
      (F.ddhOTProbProtocol n d).realJoint noOracleWorld ∅ x := by
  simp only [ddhOTProbProtocol, evalWith_ddhOTProtocolWith, Protocol.realJoint, eval_idealJoint,
    otFunctionality, Functionality.ofDeterministic, ddhOTEmptySim, ProbComp.eval_pure,
    PMF.pure_bind, PMF.pure_map, PMF.map_bind, PMF.map_comp, Function.comp_def, Prod.map, id]
  have hconst (c₀ : DDHOTSenderCoins (F.order d)) (b : ZMod (F.order d)) :
      (Finset.restrict ∅ (ddhOTViews (F.generator d) x c₀ b), otOutputs x) =
        ((fun i : (∅ : Finset (Fin 2)) => nomatch i.2), otOutputs x) :=
    Prod.ext (funext fun i => nomatch i.2) rfl
  simp only [hconst, ← PMF.bind_pure_comp, Function.comp_def, PMF.bind_const]

/-- Parties `0` and `1` as members of `Finset.univ`. -/
private abbrev senderUniv : (Finset.univ : Finset (Fin 2)) := ⟨0, Finset.mem_univ 0⟩
private abbrev receiverUniv : (Finset.univ : Finset (Fin 2)) := ⟨1, Finset.mem_univ 1⟩

/-- Simulator for `I = Finset.univ` (both parties corrupted): receives both parties' inputs and
runs the honest fair-coin protocol `ddhOTProbProtocol` directly. -/
private noncomputable def ddhOTFullSimSampleExp :
    SimulatorFamily F.ddhOTProbFamily Finset.univ :=
  fun n d xI _ => do
    let a ← F.sampleExp n d
    let r₀ ← F.sampleExp n d
    let s₀ ← F.sampleExp n d
    let r₁ ← F.sampleExp n d
    let s₁ ← F.sampleExp n d
    let b ← F.sampleExp n d
    return Finset.univ.restrict (ddhOTViews (F.generator d)
      (fun i => xI ⟨i, Finset.mem_univ i⟩)
      ((a : ZMod (F.order d)), (r₀ : ZMod (F.order d)), (s₀ : ZMod (F.order d)),
        (r₁ : ZMod (F.order d)), (s₁ : ZMod (F.order d)))
      (b : ZMod (F.order d)))

/-- View words produced by `ddhOTFullSimSampleExp` on six `sampleExp` draws. -/
private def ddhOTFullSimWords (d : F.Desc) (m : F.Carrier d × F.Carrier d) (σ : Bool)
    (a r₀ s₀ r₁ s₁ b : ℕ) (i : (Finset.univ : Finset (Fin 2))) : DDHOTViewWords i :=
  let q := F.order d
  let g := F.generator d
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
    ⟨F.encode d m.1, F.encode d m.2, a % q, r₀ % q, s₀ % q, r₁ % q, s₁ % q,
      F.encode d w₀, F.encode d w₁⟩
    (fun _ => ⟨σ, b % q, F.encode d u, F.encode d e₀, F.encode d c₀, F.encode d e₁,
      F.encode d c₁⟩)
    i.1

/-- `ddhOTFullSimSampleExp` is PPT for `ddhOTEncoding`. -/
private theorem isPPT_ddhOTFullSimSampleExp : F.ddhOTFullSimSampleExp.IsPPT F.ddhOTEncoding := by
  let E := F.ddhOTEncoding (proto := F.ddhOTProbProtocol)
  refine isPPTOn_iff_encoded.mpr ((F.isPPTOn_sampleExp_six
    (n := fun x : SimInput F.ddhOTProbFamily Finset.univ => x.secParam) (d := fun x => x.desc)
    (encSimInput_secParam_polyTime E .id')
    (encSimInput_desc_polyTime E .id')
    (W := fun x a r₀ s₀ r₁ s₁ b =>
      encDPi (fun i : (Finset.univ : Finset (Fin 2)) => E.view.enc i.1)
        (F.ddhOTFullSimWords x.desc (x.inputs senderUniv) (x.inputs receiverUniv)
          a r₀ s₀ r₁ s₁ b))
    fun {γ encγ x a _ _ _ _ b} hx ha hr₀ hs₀ hr₁ hs₁ hb => ?_).congr fun x => ?_)
  · have hd : ComputableInPolyTime (fun c => (x c).desc) encγ F.encDesc :=
      encSimInput_desc_polyTime E hx
    have hm : ComputableInPolyTime (fun c => (F.encode (x c).desc ((x c).inputs senderUniv).1,
        F.encode (x c).desc ((x c).inputs senderUniv).2)) encγ (encPair encBits encBits) :=
      E.input.encCoalition_apply_polyTime (encSimInput_inputs_polyTime E hx) senderUniv
    have hσ : ComputableInPolyTime (fun c => ((x c).inputs receiverUniv : Bool)) encγ encBool :=
      E.input.encCoalition_apply_polyTime (encSimInput_inputs_polyTime E hx) receiverUniv
    have hq := F.computableInPolyTime_order.comp hd
    have hg := computableInPolyTime_encode_generator hd
    have hu := computableInPolyTime_encode_natCast_smul hd ha hg
    have hv := computableInPolyTime_encode_natCast_smul hd hb hg
    have huSubV := computableInPolyTime_encode_add hd hu
      (computableInPolyTime_encode_natCast_smul hd (hq.binary_sub' (hb.binary_mod' hq)) hg)
    have hw₀ : ComputableInPolyTime (fun c => F.encode (x c).desc
        (cond ((x c).inputs receiverUniv : Bool)
          ((a c : ZMod (F.order (x c).desc)) • F.generator (x c).desc +
            ((F.order (x c).desc - b c % F.order (x c).desc : ℕ) :
              ZMod (F.order (x c).desc)) • F.generator (x c).desc)
          ((b c : ZMod (F.order (x c).desc)) • F.generator (x c).desc))) encγ encBits :=
      .of_enc_eq (hσ.ite' huSubV hv) fun c => by
        obtain ⟨b', hb'⟩ : ∃ b' : Bool, (x c).inputs receiverUniv = b' := ⟨_, rfl⟩
        rw [hb']; cases b' <;> rfl
    have hw₁ : ComputableInPolyTime (fun c => F.encode (x c).desc
        (cond ((x c).inputs receiverUniv : Bool)
          ((b c : ZMod (F.order (x c).desc)) • F.generator (x c).desc)
          ((a c : ZMod (F.order (x c).desc)) • F.generator (x c).desc +
            ((F.order (x c).desc - b c % F.order (x c).desc : ℕ) :
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
    · exact encDDHOTSenderViewWords_mk_polyTime hm.fst' hm.snd' (ha.binary_mod' hq)
        (hr₀.binary_mod' hq) (hs₀.binary_mod' hq) (hr₁.binary_mod' hq) (hs₁.binary_mod' hq)
        hw₀ hw₁
    · exact encDDHOTReceiverViewWords_mk_polyTime hσ (hb.binary_mod' hq) hu he₀ hc₀ he₁ hc₁
  · simp only [ddhOTFullSimSampleExp, ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_pure,
      PMF.map_bind, PMF.pure_map]
    refine congrArg (PMF.bind _) (funext fun a => congrArg (PMF.bind _) (funext fun r₀ =>
      congrArg (PMF.bind _) (funext fun s₀ => congrArg (PMF.bind _) (funext fun r₁ =>
        congrArg (PMF.bind _) (funext fun s₁ => congrArg (PMF.bind _) (funext fun b =>
          congrArg PMF.pure ?_))))))
    change encDPi (fun i : (Finset.univ : Finset (Fin 2)) => E.view.enc i.1) _ =
      encDPi (fun i : (Finset.univ : Finset (Fin 2)) => E.view.enc i.1) _
    refine congrArg (encDPi _) (funext fun i => ?_)
    obtain ⟨n, d, xs, ys⟩ := x
    obtain ⟨j, hj⟩ := i
    let q := F.order d
    let g := F.generator d
    obtain ⟨σ, hσ⟩ : ∃ σ : Bool, xs receiverUniv = σ := ⟨_, rfl⟩
    fin_cases j
    · change F.ddhOTFullSimWords d (xs senderUniv) (xs receiverUniv) a r₀ s₀ r₁ s₁ b ⟨0, hj⟩ =
        F.ddhOTSenderViewWords d (ddhOTSenderView (xs senderUniv)
          ((a : ZMod q), (r₀ : ZMod q), (s₀ : ZMod q), (r₁ : ZMod q), (s₁ : ZMod q))
          (ddhOTReceiverMsg g (xs receiverUniv) (b : ZMod q) ((a : ZMod q) • g)))
      rw [hσ]
      cases σ <;> simp only [ddhOTFullSimWords, ddhOTSenderViewWords, ddhOTSenderView,
        ddhOTReceiverMsg, Bool.false_eq_true, ↓reduceIte, ZMod.natCast_sub_mod_eq_neg, neg_smul,
        ← sub_eq_add_neg, ZMod.val_natCast] <;> rfl
    · change F.ddhOTFullSimWords d (xs senderUniv) (xs receiverUniv) a r₀ s₀ r₁ s₁ b ⟨1, hj⟩ =
        F.ddhOTReceiverViewWords d (ddhOTReceiverView (xs receiverUniv) (b : ZMod q)
          ((a : ZMod q) • g) (ddhOTSenderReplyUnchecked g (xs senderUniv)
            ((a : ZMod q), (r₀ : ZMod q), (s₀ : ZMod q), (r₁ : ZMod q), (s₁ : ZMod q))
            (ddhOTReceiverMsg g (xs receiverUniv) (b : ZMod q) ((a : ZMod q) • g))))
      rw [hσ]
      cases σ <;> simp only [ddhOTFullSimWords, ddhOTReceiverViewWords, ddhOTReceiverView,
        ddhOTSenderReplyUnchecked, ddhOTEncryptBranch, ddhOTReceiverMsg, Bool.false_eq_true,
        ↓reduceIte, ZMod.natCast_sub_mod_eq_neg, neg_smul, ← sub_eq_add_neg,
        ZMod.val_natCast] <;> rfl

/-- When both parties are corrupted, `ddhOTFullSimSampleExp` reproduces `ddhOTProbProtocol`'s real
joint law exactly. -/
private theorem idealJoint_ddhOTProb_univ (n : ℕ) (d : F.Desc)
    (x : (i : Fin 2) → OTIn (F.Carrier d) i) :
    ProbComp.eval (idealJoint (otFunctionality (F.Carrier d)) Finset.univ
        (F.ddhOTFullSimSampleExp n d) x) =
      (F.ddhOTProbProtocol n d).realJoint noOracleWorld Finset.univ x := by
  simp only [ddhOTProbProtocol, evalWith_ddhOTProtocolWith, sampleDDHOTSenderCoinsProb,
    Protocol.realJoint, eval_idealJoint, otFunctionality, Functionality.ofDeterministic,
    ddhOTFullSimSampleExp, ProbComp.eval_bind, ProbComp.eval_pure, ProbComp.eval_map,
    PMF.pure_bind, PMF.bind_bind, PMF.pure_map, PMF.map_bind, PMF.map_comp,
    Function.comp_def, Prod.map, id]
  rfl

/-! ### Security -/

/-- Ideal-coins step: against a corrupted sender, `ddhOTFamily` (exact uniform party coins) is
within `6 / 2 ^ n` of `ddhOTSenderSimSampleExp` for every environment. -/
private theorem advantage_ddhOTSenderGame_le (setup : ℕ → PMF F.Desc)
    (Z : Environment F.ddhOTFamily {0}) (n : ℕ) :
    Game.advantage (F.ddhOTFamily.realGame setup {0} Z n)
      (F.ddhOTFamily.idealGame setup {0} F.ddhOTSenderSimSampleExp Z n) ≤ 6 / 2 ^ n := by
  rw [ProtocolFamily.realGame_eq_idealGame
    (S := fun _ d => ddhOTSenderSim (F.generator d) (F.order d))
    (fun _ d => idealJoint_ddhOT_sender _ _)]
  exact ProtocolFamily.advantage_idealGame_le (F.advantage_bind_ddhOTSenderSimSampleExp_le n) Z

/-- **Concrete statistical sender security of `ddhOTProbFamily`**: against a corrupted sender
(`{0}`), every environment `Z`—with no running-time bound and no computational assumption—has
advantage at most `12 / 2 ^ n` between the fair-coin real game and the ideal game with
`ddhOTSenderSimSampleExp` (`6 / 2 ^ n` from the six honest-party `sampleExp` draws plus `6 / 2 ^ n`
from the six simulator `sampleExp` draws). -/
theorem advantage_ddhOTProbSenderGame_le (setup : ℕ → PMF F.Desc)
    (Z : Environment F.ddhOTProbFamily {0}) (n : ℕ) :
    Game.advantage (F.ddhOTProbFamily.realGame setup {0} Z n)
      (F.ddhOTProbFamily.idealGame setup {0} F.ddhOTSenderSimSampleExp Z n) ≤ 12 / 2 ^ n := by
  rw [← F.idealGame_recastDDHOTEnv (p₂ := fun _ d => ddhOTProtocol (F.generator d) (F.order d))]
  calc _ ≤ 6 / 2 ^ n + 6 / 2 ^ n :=
        (Game.advantage_triangle _
            (F.ddhOTFamily.realGame setup {0} (F.recastDDHOTEnv Z) n) _).trans
          (add_le_add (F.advantage_realGame_ddhOTProbFamily_le setup {0} Z n)
            (F.advantage_ddhOTSenderGame_le setup (F.recastDDHOTEnv Z) n))
    _ = 12 / 2 ^ n := by ring

/-- **Unconditional semi-honest sender security of `ddhOTProbFamily`** ([BonehShoup2023],
Section 23.5.7.2, p. 1060): `ddhOTProbFamily` is semi-honest secure against a corrupted sender
(`{0}`) for every setup law `setup`, with no hardness assumption. -/
theorem ddhOTProbFamily_semiHonestSecure_sender (setup : ℕ → PMF F.Desc) :
    F.ddhOTProbFamily.SemiHonestSecure setup {0} F.ddhOTEncoding :=
  ⟨F.ddhOTSenderSimSampleExp, F.isPPT_ddhOTSenderSimSampleExp, fun Z _ => by
    negligible using F.advantage_ddhOTProbSenderGame_le setup Z⟩

/-- **Concrete receiver reduction bound for `ddhOTProbFamily`**: against a corrupted receiver
(`{1}`), every environment `Z` has advantage between the fair-coin real game and the ideal game
with `ddhOTReceiverSimSampleExp` at most the DDH advantage of `ddhOTReceiverToDDHDistinguisher Z`
plus `18 / 2 ^ n`. -/
theorem advantage_ddhOTProbReceiverGame_le (setup : ℕ → PMF F.Desc)
    (Z : Environment F.ddhOTProbFamily {1}) (n : ℕ) :
    Game.advantage (F.ddhOTProbFamily.realGame setup {1} Z n)
        (F.ddhOTProbFamily.idealGame setup {1} F.ddhOTReceiverSimSampleExp Z n) ≤
      Game.advantage (F.ddhRealGame setup (F.ddhOTReceiverToDDHDistinguisher Z) n)
        (F.ddhRandomGame setup (F.ddhOTReceiverToDDHDistinguisher Z) n) + 18 / 2 ^ n := by
  rw [← F.idealGame_recastDDHOTEnv (p₂ := fun _ d => ddhOTProtocol (F.generator d) (F.order d))]
  have hd_eq (n : ℕ) (d : F.Desc) (u v w : F.Carrier d) :
      ProbComp.eval (F.ddhOTReceiverToDDHDistinguisher
          (proto := fun _ d => ddhOTProtocol (F.generator d) (F.order d))
          (F.recastDDHOTEnv Z) n d u v w) =
        ProbComp.eval (F.ddhOTReceiverToDDHDistinguisher Z n d u v w) := by
    simp only [ddhOTReceiverToDDHDistinguisher, recastDDHOTEnv, ProbComp.eval_bind,
      ProbComp.eval_map, PMF.bind_map, Function.comp_def]
  have hreal_ddh : F.ddhRealGame setup
      (F.ddhOTReceiverToDDHDistinguisher
        (proto := fun _ d => ddhOTProtocol (F.generator d) (F.order d))
        (F.recastDDHOTEnv Z)) n =
      F.ddhRealGame setup (F.ddhOTReceiverToDDHDistinguisher Z) n := by
    simp only [ddhRealGame, Game.withSetup, eval_ddhRealExperiment, hd_eq]
  have hrand_ddh : F.ddhRandomGame setup
      (F.ddhOTReceiverToDDHDistinguisher
        (proto := fun _ d => ddhOTProtocol (F.generator d) (F.order d))
        (F.recastDDHOTEnv Z)) n =
      F.ddhRandomGame setup (F.ddhOTReceiverToDDHDistinguisher Z) n := by
    simp only [ddhRandomGame, Game.withSetup, eval_ddhRandomExperiment, hd_eq]
  have hrec := F.advantage_ddhOTReceiverGame_le setup (F.recastDDHOTEnv Z) n
  rw [hreal_ddh, hrand_ddh] at hrec
  calc _ ≤ 6 / 2 ^ n +
        ((Game.advantage (F.ddhRealGame setup (F.ddhOTReceiverToDDHDistinguisher Z) n)
            (F.ddhRandomGame setup (F.ddhOTReceiverToDDHDistinguisher Z) n) + 6 / 2 ^ n) +
          6 / 2 ^ n) :=
      (Game.advantage_triangle _ (F.ddhOTFamily.realGame setup {1} (F.recastDDHOTEnv Z) n) _).trans
        (add_le_add (F.advantage_realGame_ddhOTProbFamily_le setup {1} Z n)
          ((Game.advantage_triangle _ _ _).trans (add_le_add hrec
            (ProtocolFamily.advantage_idealGame_le
              (F.advantage_bind_ddhOTReceiverSimSampleExp_le n) (F.recastDDHOTEnv Z)))))
    _ = _ := by ring

/-- **Semi-honest security of fair-coin DDH oblivious transfer** ([BonehShoup2023],
Section 23.5.7.2, Theorem 23.7, p. 1058, for the `ddhOTProbProtocol` variant of Figure 23.17 with
`sampleExp` coins from Remark 23.5, p. 1059, in the stand-alone `ProtocolFamily.SemiHonestSecure`
model): under `F.DDH setup` alone, `ddhOTProbFamily` is semi-honest secure against every static
coalition `I : Finset (Fin 2)` for `ddhOTEncoding`. The simulators are certified strict PPT
(`isPPT_ddhOTSenderSimSampleExp`, `isPPT_ddhOTReceiverSimSampleExp`), and the DDH reduction is
certified strict PPT (`isPPT_ddhOTReceiverToDDHDistinguisher`). The module docstring records the
protocol, coin-representation and execution-model differences from Theorem 23.7. -/
theorem DDH.ddhOTSemiHonestSecure {F : PrimeOrderGroupFamily} {setup : ℕ → PMF F.Desc}
    (hDDH : F.DDH setup) (I : Finset (Fin 2)) :
    F.ddhOTProbFamily.SemiHonestSecure setup I F.ddhOTEncoding := by
  by_cases h0 : (0 : Fin 2) ∈ I <;> by_cases h1 : (1 : Fin 2) ∈ I
  · have hI : I = Finset.univ := by ext i; fin_cases i <;> simp [h0, h1]
    subst hI
    exact ProtocolFamily.SemiHonestSecure.of_perfect F.isPPT_ddhOTFullSimSampleExp
      F.idealJoint_ddhOTProb_univ
  · have hI : I = {0} := by ext i; fin_cases i <;> simp [h0, h1]
    subst hI
    exact F.ddhOTProbFamily_semiHonestSecure_sender setup
  · have hI : I = {1} := by ext i; fin_cases i <;> simp [h0, h1]
    subst hI
    refine ⟨F.ddhOTReceiverSimSampleExp, F.isPPT_ddhOTReceiverSimSampleExp, fun Z hZ => ?_⟩
    have hB := hDDH _ (F.isPPT_ddhOTReceiverToDDHDistinguisher hZ)
    negligible using F.advantage_ddhOTProbReceiverGame_le setup Z
  · have hI : I = ∅ := by ext i; fin_cases i <;> simp [h0, h1]
    subst hI
    exact ProtocolFamily.SemiHonestSecure.of_perfect F.isPPT_ddhOTEmptySim
      F.idealJoint_ddhOTProb_empty

end Cslib.Crypto.PrimeOrderGroupFamily
