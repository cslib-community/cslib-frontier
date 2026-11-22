/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.CorrelationRobust
public import CslibFrontier.Crypto.Protocols.MPC.Asymptotic
public import CslibFrontier.Crypto.Protocols.MPC.IKNP
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.DPi
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListMap
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.PPT.Extension
import CslibFrontier.Computability.Probabilistic.Repeat
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Languages.Probabilistic.Repeat
import CslibFrontier.Tactic.PMFSwap

/-!
# IKNP oblivious-transfer extension as a protocol family

`CslibFrontier/Crypto/Protocols/MPC/IKNP.lean` defines `iknpProtocol H` for one hash family `H`
and proves its privacy at one instance. This module runs it as the protocol family
`iknpFamily hash m` (`Cslib.Crypto.Protocols.MPC.ProtocolFamily`): at the security parameter `n`,
`n` base transfers of `(m n)`-bit strings, the hybrid `batchOTSpec n (BitString (m n))`, extend to
`m n` transfers of bits, with the hash `CorrelationRobust.atLevel hash n (m n)`, which hashes the
bits of a row with the word function `hash`. There are no public parameters. `iknpEncoding`
writes inputs, outputs and views as bit words (`IKNPSenderViewWords`, `IKNPReceiverViewWords`).

`CorrelationRobust.iknpSemiHonestSecure` proves that the family is semi-honest secure against a
corrupted sender and against a corrupted receiver (`ProtocolFamily.SemiHonestSecure`), assuming
only that `hash` is correlation robust (`Cslib.Crypto.CorrelationRobust`) and that `m` is
polynomially bounded.

**Proof.** Against the sender, the simulator `iknpSenderSim` is perfect
(`idealJoint_iknp_sender`), and it is PPT (`isPPT_iknpSenderSim`): it draws `n` bits for the
choice string and `n` words of `m n` bits for the columns. Against the receiver, the reduction
`iknpReceiverToCR Z` turns an environment `Z` into a correlation-robustness distinguisher: it runs
`Z.choose`, then the per-instance reduction `iknpReduction`. The real game is the real
correlation-robustness game of the reduction at level `n` with `m n` queries, and the ideal game
with `iknpReceiverSim` is its ideal game, with no loss (`realGame_iknp_receiver_eq`,
`idealGame_iknp_receiver_eq`). `isPPT_iknpReceiverToCR` proves the reduction PPT whenever `Z` is,
and `isPPT_iknpReceiverSim` proves the receiver's simulator PPT; both use the assumption's
`polyTime`.

## Comparison with [IshaiKilianNissimPetrank2003]

`CorrelationRobust.iknpSemiHonestSecure` formalizes the two Claims of §3.1 for Fig. 1 (p. 152),
with the random oracle replaced by a correlation robust hash as §5 describes (p. 157):
* the sender Claim (p. 153, the protocol "is perfectly secure with respect to an arbitrary
  sender"), in its semi-honest case: the p. 153 simulator for the honest sender is
  `iknpSenderSim`;
* the receiver Claim (p. 154, a semi-honest receiver). Its random-oracle bound, Lemma 1 (p. 154),
  is replaced by §5's argument that the masks of the unchosen entries are jointly pseudorandom
  given the receiver's view; here that argument is an exact game equality.

Theorems 2 (p. 147) and 3 (p. 157) are not formalized. They concern oblivious transfer in the
source's default sense, secure against malicious parties (p. 146): the fully secure variant of
§4 (p. 154), modified for correlation robustness in Theorem 3, composed with the reduction of
`OT^k_m` to `OT^k_k` with a pseudorandom generator (§2.2, p. 151, and Appendix B). The
formalized statement differs from the two Claims as follows.

* **Protocol and parameters.** Fig. 1 with `ℓ = 1`, bit transfers, and `h(u)` in place of the
  random oracle's `H(j, u)`, which is how §5 (p. 157, footnote 10) instantiates it with a
  correlation robust `h`. There are `k = n` base transfers and `m n` extended ones, for any
  polynomially bounded `m`, the "polynomially many" of §5.
* **Hybrid model.** The base transfers are the ideal primitive `OT^k_m` of Fig. 1, `k` transfers
  of `m`-bit strings (`batchOTSpec`), in the hybrid model of §2.1 (pp. 149–150). No composition
  theorem replaces them by a protocol.
* **Corruption.** One static party at a time, semi-honest. The source's definition (Appendix A,
  p. 160) is the stand-alone one against a non-adaptive adversary, as here.
* **Environments.** Uniform strict PPT environments that choose the inputs, the uniform variant
  of `ProtocolFamily.SemiHonestSecure`; its module documentation lists the differences of the
  notion.
* **Assumption.** `CorrelationRobust hash` admits fewer distinguishers than Definition 1 (§5,
  p. 157), which implies it for a hash computed in polynomial time.

## Main definitions

* `Cslib.Crypto.Protocols.MPC.IKNPSenderViewWords`,
  `Cslib.Crypto.Protocols.MPC.IKNPReceiverViewWords`, their encodings, and
  `Cslib.Crypto.Protocols.MPC.iknpSenderViewWords`,
  `Cslib.Crypto.Protocols.MPC.iknpReceiverViewWords`: a party's view as words.
* `Cslib.Crypto.Protocols.MPC.iknpFamily`: IKNP bit-transfer extension as a protocol family.
* `Cslib.Crypto.Protocols.MPC.iknpEncoding`: its encoding for machines.
* `Cslib.Crypto.Protocols.MPC.iknpReceiverToCR`: the reduction to correlation robustness.

## Main results

* `Cslib.Crypto.Protocols.MPC.isPPT_iknpSenderSim`,
  `Cslib.Crypto.Protocols.MPC.isPPT_iknpReceiverSim`: the simulator families are PPT.
* `Cslib.Crypto.Protocols.MPC.realGame_iknp_receiver_eq`,
  `Cslib.Crypto.Protocols.MPC.idealGame_iknp_receiver_eq`: against a corrupted receiver, the games
  are the correlation-robustness games of the reduction.
* `Cslib.Crypto.Protocols.MPC.isPPT_iknpReceiverToCR`: the reduction is PPT.
* `Cslib.Crypto.CorrelationRobust.iknpSemiHonestSecure`: semi-honest security against either
  party under correlation robustness.

## References

* [Y. Ishai, J. Kilian, K. Nissim, E. Petrank, *Extending Oblivious Transfers
  Efficiently*][IshaiKilianNissimPetrank2003], §1.1–1.2 (pp. 146–147), §2 (pp. 149–151), Fig. 1
  and §3.1 (pp. 152–154), §4 (p. 154), §5 (Definition 1, p. 157) and Appendix A (p. 160).
-/

public section

namespace Cslib.Crypto.Protocols.MPC

open Probability Turing.MultiTapeTM

/-! ### Views as words -/

/-- The words of a corrupted sender's view in `iknpProtocol` with bit values: the first and the
second entries of its pairs, its base choice string `s`, and the columns of the matrix it received
from the base transfers. -/
structure IKNPSenderViewWords where
  /-- The bits `x_{j,0}`. -/
  pairs₀ : List Bool
  /-- The bits `x_{j,1}`. -/
  pairs₁ : List Bool
  /-- The base choice string `s`. -/
  choice : List Bool
  /-- The columns `qⁱ` received from the base transfers. -/
  columns : List (List Bool)

/-- The encoding of a sender's view words: each field in turn, all but the last framed. -/
enc_structure encIKNPSenderViewWords : IKNPSenderViewWords where
  pairs₀ : encBits, pairs₁ : encBits, choice : encBits, columns : (encList encBits)

/-- The words of a corrupted receiver's view in `iknpProtocol` with bit values: its choice bits
`r`, the rows `tⱼ` of its matrix, and the first and the second entries of the masked pairs it
received. -/
structure IKNPReceiverViewWords where
  /-- The choice bits `r`. -/
  choices : List Bool
  /-- The rows `tⱼ` of the receiver's matrix. -/
  rows : List (List Bool)
  /-- The masked bits `y_{j,0}`. -/
  masked₀ : List Bool
  /-- The masked bits `y_{j,1}`. -/
  masked₁ : List Bool

/-- The encoding of a receiver's view words: each field in turn, all but the last framed. -/
enc_structure encIKNPReceiverViewWords : IKNPReceiverViewWords where
  choices : encBits, rows : (encList encBits), masked₀ : encBits, masked₁ : encBits

/-- The view words of the two parties of `iknpProtocol`: `IKNPSenderViewWords` for the sender
(party `0`) and `IKNPReceiverViewWords` for the receiver (party `1`). -/
abbrev IKNPViewWords : Fin 2 → Type :=
  fun i => Fin.cases (motive := fun _ => Type) IKNPSenderViewWords
    (fun _ => IKNPReceiverViewWords) i

section ViewWords

variable {κ m : ℕ}

/-- The words of a sender's view: its pairs as two bit words, its choice string, and the received
columns as bit words. -/
@[expose] def iknpSenderViewWords
    (view : PartyView ((batchOTSpec m Bool).Query ()) (IKNPCoins κ m) (iknpSchedule κ m Bool) 0) :
    IKNPSenderViewWords :=
  let (Q, _, _) := view.received
  ⟨List.ofFn fun j => view.input j false, List.ofFn fun j => view.input j true,
    List.ofFn view.coins, List.ofFn fun i => List.ofFn (Q 1 rfl i)⟩

/-- The words of a receiver's view: its choice bits, the rows of its matrix, and the masked pairs
as two bit words. -/
@[expose] def iknpReceiverViewWords
    (view : PartyView ((batchOTSpec m Bool).Query ()) (IKNPCoins κ m) (iknpSchedule κ m Bool) 1) :
    IKNPReceiverViewWords :=
  let (_, Y, _) := view.received
  ⟨List.ofFn view.input, List.ofFn fun j => List.ofFn (view.coins j),
    List.ofFn fun j => Y rfl j false, List.ofFn fun j => Y rfl j true⟩

/-- The words determine a sender's view. -/
theorem iknpSenderViewWords_injective :
    Function.Injective (iknpSenderViewWords (κ := κ) (m := m)) := by
  rintro ⟨X, s, ⟨Q, Y, ⟨⟩⟩⟩ ⟨X', s', ⟨Q', Y', ⟨⟩⟩⟩ h
  simp only [iknpSenderViewWords, IKNPSenderViewWords.mk.injEq] at h
  obtain ⟨h₀, h₁, hs, hQ⟩ := h
  have h₀ := List.ofFn_injective h₀
  have h₁ := List.ofFn_injective h₁
  refine PartyView.ext ?_ (List.ofFn_injective hs) (Prod.ext ?_ (Prod.ext ?_ rfl))
  · funext j b
    cases b
    · exact congrFun h₀ j
    · exact congrFun h₁ j
  · refine Round.received_oracle_ext fun sl hsl => ?_
    fin_cases sl
    · exact absurd hsl (by simp [iknpRoleReversal])
    · funext i
      exact List.ofFn_injective (congrFun (List.ofFn_injective hQ) i)
  · exact Round.received_message_eq_of_ne (by simp) _ _

/-- The words determine a receiver's view. -/
theorem iknpReceiverViewWords_injective :
    Function.Injective (iknpReceiverViewWords (κ := κ) (m := m)) := by
  rintro ⟨r, T, ⟨Q, Y, ⟨⟩⟩⟩ ⟨r', T', ⟨Q', Y', ⟨⟩⟩⟩ h
  simp only [iknpReceiverViewWords, IKNPReceiverViewWords.mk.injEq] at h
  obtain ⟨hr, hT, h₀, h₁⟩ := h
  have h₀ := List.ofFn_injective h₀
  have h₁ := List.ofFn_injective h₁
  refine PartyView.ext (List.ofFn_injective hr)
    (funext fun j => List.ofFn_injective (congrFun (List.ofFn_injective hT) j))
    (Prod.ext ?_ (Prod.ext ?_ rfl))
  · refine Round.received_oracle_ext fun sl hsl => ?_
    fin_cases sl
    · rfl
    · exact absurd hsl (by simp [iknpRoleReversal])
  · refine Round.received_message_ext fun _ => funext fun j => funext fun b => ?_
    cases b
    · exact congrFun h₀ j
    · exact congrFun h₁ j

end ViewWords

variable (hash : List Bool → Bool) (m : ℕ → ℕ)

/-! ### The protocol family and its encoding -/

/-- **IKNP bit-transfer extension** as a protocol family: at the security parameter `n`,
`iknpProtocol` with the hash `CorrelationRobust.atLevel hash n (m n)` extends `n` base transfers
of `(m n)`-bit strings (the `batchOTSpec n (BitString (m n))` hybrid) to `m n` transfers of bits.
There are no public parameters. -/
noncomputable abbrev iknpFamily : ProtocolFamily 2 where
  Desc := Unit
  spec n _ := batchOTSpec n (BitString (m n))
  sc n _ := iknpSchedule n (m n) Bool
  In n _ := (batchOTSpec (m n) Bool).Query ()
  Coins n _ := IKNPCoins n (m n)
  Out n _ := (batchOTSpec (m n) Bool).Answer ()
  protocol n _ := iknpProtocol (CorrelationRobust.atLevel hash n (m n))
  world n _ := batchOTWorld n (BitString (m n))
  functionality n _ := batchOTFunctionality (m n) Bool

/-- The words of a party's input: the sender's pairs as two bit words, the receiver's choice bits
as one. -/
abbrev IKNPInputWords : Fin 2 → Type :=
  fun i => Fin.cases (motive := fun _ => Type) (List Bool × List Bool) (fun _ => List Bool) i

/-- The words of a party's output: nothing for the sender, the received bits for the receiver. -/
abbrev IKNPOutputWords : Fin 2 → Type :=
  fun i => Fin.cases (motive := fun _ => Type) Unit (fun _ => List Bool) i

/-- The encoding of `iknpFamily hash m` for machines. There are no public parameters
(`encUnit`). The sender's input `X` is the pair of bit words `(x_{j,0})ⱼ` and `(x_{j,1})ⱼ`
(`encPair encBits encBits`), and the receiver's input is the word of its choice bits. The
sender's output `()` is the empty word, and the receiver's output is the word of its bits. The
views are their view words (`iknpSenderViewWords`, `iknpReceiverViewWords`), encoded by
`encIKNPSenderViewWords` and `encIKNPReceiverViewWords`. -/
@[expose] noncomputable def iknpEncoding : (iknpFamily hash m).Encoding where
  desc := encUnit
  input :=
    { Rep := IKNPInputWords
      enc := fun i => Fin.cases (motive := fun i => IKNPInputWords i ↪ List Bool)
        (encPair encBits encBits) (fun _ => encBits) i
      rep := fun n _ i =>
        Fin.cases (motive := fun i => (batchOTSpec (m n) Bool).Query () i ↪ IKNPInputWords i)
          ⟨fun X => (List.ofFn fun j => X j false, List.ofFn fun j => X j true),
            fun X X' h => funext fun j => funext fun b => by
              cases b
              · exact congrFun (List.ofFn_injective (congrArg Prod.fst h)) j
              · exact congrFun (List.ofFn_injective (congrArg Prod.snd h)) j⟩
          (fun _ => ⟨List.ofFn, List.ofFn_injective⟩) i }
  output :=
    { Rep := IKNPOutputWords
      enc := fun i => Fin.cases (motive := fun i => IKNPOutputWords i ↪ List Bool) encUnit
        (fun _ => encBits) i
      rep := fun n _ i =>
        Fin.cases (motive := fun i => (batchOTSpec (m n) Bool).Answer () i ↪ IKNPOutputWords i)
          (Function.Embedding.refl Unit) (fun _ => ⟨List.ofFn, List.ofFn_injective⟩) i }
  view :=
    { Rep := IKNPViewWords
      enc := fun i => Fin.cases (motive := fun i => IKNPViewWords i ↪ List Bool)
        encIKNPSenderViewWords (fun _ => encIKNPReceiverViewWords) i
      rep := fun n _ i => Fin.cases (motive := fun i =>
          PartyView ((batchOTSpec (m n) Bool).Query ()) (IKNPCoins n (m n))
            (iknpSchedule n (m n) Bool) i ↪ IKNPViewWords i)
        ⟨iknpSenderViewWords, iknpSenderViewWords_injective⟩
        (Fin.cases (motive := fun j => PartyView ((batchOTSpec (m n) Bool).Query ())
            (IKNPCoins n (m n)) (iknpSchedule n (m n) Bool) j.succ ↪ IKNPViewWords j.succ)
          ⟨iknpReceiverViewWords, iknpReceiverViewWords_injective⟩
          fun k => k.elim0) i }

/-! ### Efficiency of the simulator families -/

/-- The party `0` of the coalition `{0}`. -/
private abbrev sender : ({0} : Finset (Fin 2)) := ⟨0, Finset.mem_singleton_self 0⟩

/-- The word that the sender's simulator writes from the sender's pair words `p`, the choice
string `s` and the columns `Q`: the one-entry table of the sender's view words. -/
private noncomputable def senderSimWord (p : List Bool × List Bool) (s : List Bool)
    (Q : List (List Bool)) : List Bool :=
  encPi encBits fun _ : ({0} : Finset (Fin 2)) => encIKNPSenderViewWords ⟨p.1, p.2, s, Q⟩

/-- `senderSimWord` of computed parts is computed in polynomial time. -/
private theorem senderSimWord_polyTime {γ : Type} {enc : γ ↪ List Bool}
    {p : γ → List Bool × List Bool} {s : γ → List Bool} {Q : γ → List (List Bool)}
    (hp : ComputableInPolyTime p enc (encPair encBits encBits))
    (hs : ComputableInPolyTime s enc encBits) (hQ : ComputableInPolyTime Q enc (encList encBits)) :
    ComputableInPolyTime (fun c => senderSimWord (p c) (s c) (Q c)) enc encBits :=
  (ComputableInPolyTime.pi fun _ =>
    (encIKNPSenderViewWords_mk_polyTime hp.fst' hp.snd' hs hQ).encoding_comp).encoding_comp

/-- The simulator family `iknpSenderSim` for a corrupted sender is PPT for `iknpEncoding`: it
draws `n` bits for `s` and `n` words of `m n` bits for the columns. -/
theorem isPPT_iknpSenderSim :
    SimulatorFamily.IsPPT (iknpEncoding hash m) (P := iknpFamily hash m)
      fun n _ => iknpSenderSim n (m n) Bool := by
  have hpair : ComputableInPolyTime (fun x : SimInput (iknpFamily hash m) {0} =>
      (iknpEncoding hash m).input.rep x.secParam x.desc 0 (x.inputs sender))
      (encSimInput (iknpEncoding hash m)) (encPair encBits encBits) :=
    (iknpEncoding hash m).input.encCoalition_apply_polyTime
      (encSimInput_inputs_polyTime (iknpEncoding hash m) .id') sender
  have hn : ComputableInPolyTime (fun x : SimInput (iknpFamily hash m) {0} => x.secParam)
      (encSimInput (iknpEncoding hash m)) encUnary :=
    encSimInput_secParam_polyTime (iknpEncoding hash m) .id'
  have hprog : IsPPTOn (encSimInput (iknpEncoding hash m)) encBits fun x =>
      BitString.sampleList x.secParam >>= fun s =>
        OracleComp.replicate x.secParam (BitString.sampleList
          ((iknpEncoding hash m).input.rep x.secParam x.desc 0 (x.inputs sender)).1.length) >>=
          fun Q => pure (senderSimWord
            ((iknpEncoding hash m).input.rep x.secParam x.desc 0 (x.inputs sender)) s Q) := by
    refine IsPPTOn.bind_with hn.sampleList ?_
    refine IsPPTOn.bind_with (left := encList encBits) ?_ ?_
    · exact IsPPTOn.replicate
        (ComputableInPolyTime.length_bits.comp (hpair.fst'.comp (.fst _ encBits))).sampleList
        (hn.comp (.fst _ encBits))
    · exact (senderSimWord_polyTime (hpair.comp ((ComputableInPolyTime.fst _ encBits).comp
        (.fst _ (encList encBits)))) ((ComputableInPolyTime.snd _ encBits).comp
          (.fst _ (encList encBits))) (.snd _ (encList encBits))).isPPTOn
  refine isPPTOn_iff_encoded.mpr (hprog.congr fun x => ?_)
  obtain ⟨n, d, xs, ys⟩ := x
  have hlen : ((iknpEncoding hash m).input.rep n d 0 (xs sender)).1.length = m n :=
    List.length_ofFn
  simp only [hlen, iknpSenderSim, ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_pure,
    ProbComp.eval_uniform, BitString.eval_sampleList, ProbComp.eval_replicate_sampleList,
    BitString.uniformList, PMF.bind_map, PMF.map_bind, PMF.pure_map, Function.comp_def]
  refine congrArg _ (funext fun s => congrArg _ (funext fun Q => congrArg PMF.pure ?_))
  refine Eq.trans ?_ ((iknpEncoding hash m).view.encCoalition_singleton n d 0 _).symm
  simp only [senderSimWord, List.map_ofFn, Function.comp_def]
  rfl

/-- Combine four bit words entrywise with `g`, up to the shortest of them. -/
private def bitsZipWith4 (g : Bool → Bool → Bool → Bool → Bool) (a b c e : List Bool) :
    List Bool :=
  ((a.zip b).zip (c.zip e)).map fun ((x, y), (z, w)) => g x y z w

/-- On the words of four bit strings of one length, `bitsZipWith4` is entrywise. -/
private theorem bitsZipWith4_ofFn {count : ℕ} (g : Bool → Bool → Bool → Bool → Bool)
    (a b c e : Fin count → Bool) :
    bitsZipWith4 g (List.ofFn a) (List.ofFn b) (List.ofFn c) (List.ofFn e) =
      List.ofFn fun j => g (a j) (b j) (c j) (e j) := by
  refine List.ext_getElem (by simp [bitsZipWith4]) fun j h₁ h₂ => ?_
  simp [bitsZipWith4]

/-- `bitsZipWith4` of computed bit words is computed in polynomial time. -/
private theorem bitsZipWith4_polyTime (g : Bool → Bool → Bool → Bool → Bool) {γ : Type}
    {enc : γ ↪ List Bool} {a b c e : γ → List Bool}
    (ha : ComputableInPolyTime a enc encBits) (hb : ComputableInPolyTime b enc encBits)
    (hc : ComputableInPolyTime c enc encBits) (he : ComputableInPolyTime e enc encBits) :
    ComputableInPolyTime (fun x => bitsZipWith4 g (a x) (b x) (c x) (e x)) enc encBits := by
  have hzip {u v : γ → List Bool} (hu : ComputableInPolyTime u enc encBits)
      (hv : ComputableInPolyTime v enc encBits) :
      ComputableInPolyTime (fun x => (u x).zip (v x)) enc (encList (encPair encBool encBool)) :=
    (ComputableInPolyTime.zip encBool encBool).comp
      ((ComputableInPolyTime.bitsToList.comp hu).prod (ComputableInPolyTime.bitsToList.comp hv))
  have hpairs := (ComputableInPolyTime.zip _ _).comp ((hzip ha hb).prod (hzip hc he))
  exact ComputableInPolyTime.listToBits.comp (ComputableInPolyTime.mapWithInput hpairs
    ((ComputableInPolyTime.of_finite fun ((x, y), (z, w)) => g x y z w).comp (.snd _ _)))

/-- The hashes of a list of words, as a bit word. -/
private theorem map_hash_polyTime {hash : List Bool → Bool}
    (hh : ComputableInPolyTime hash encBits encBool) {γ : Type} {enc : γ ↪ List Bool}
    {T : γ → List (List Bool)} (hT : ComputableInPolyTime T enc (encList encBits)) :
    ComputableInPolyTime (fun x => (T x).map hash) enc encBits :=
  ComputableInPolyTime.listToBits.comp (ComputableInPolyTime.mapWithInput hT (hh.comp (.snd _ _)))

/-- The masked bit `b` that the receiver's simulator writes for a pair with choice bit `rj`,
output bit `zj`, uniform bit `uj` and hash `hj` of its row: `zj + hj` when `b = rj`, else
`uj`. -/
private def simMask (b rj zj uj hj : Bool) : Bool :=
  if b = rj then zj ^^ hj else uj

/-- The word that the receiver's simulator writes from the choice bits `r`, the output bits `z`,
the rows `T` and the uniform bits `u`: the one-entry table of the receiver's view words. -/
private noncomputable def receiverSimWord (r z : List Bool) (T : List (List Bool))
    (u : List Bool) : List Bool :=
  encPi encBits fun _ : ({1} : Finset (Fin 2)) => encIKNPReceiverViewWords
    ⟨r, T, bitsZipWith4 (simMask false) r z u (T.map hash),
      bitsZipWith4 (simMask true) r z u (T.map hash)⟩

/-- `receiverSimWord` of computed parts is computed in polynomial time. -/
private theorem receiverSimWord_polyTime (hh : ComputableInPolyTime hash encBits encBool)
    {γ : Type} {enc : γ ↪ List Bool} {r z u : γ → List Bool} {T : γ → List (List Bool)}
    (hr : ComputableInPolyTime r enc encBits) (hz : ComputableInPolyTime z enc encBits)
    (hT : ComputableInPolyTime T enc (encList encBits))
    (hu : ComputableInPolyTime u enc encBits) :
    ComputableInPolyTime (fun c => receiverSimWord hash (r c) (z c) (T c) (u c)) enc encBits :=
  (ComputableInPolyTime.pi fun _ => (encIKNPReceiverViewWords_mk_polyTime hr hT
    (bitsZipWith4_polyTime _ hr hz hu (map_hash_polyTime hh hT))
    (bitsZipWith4_polyTime _ hr hz hu (map_hash_polyTime hh hT))).encoding_comp).encoding_comp

/-- The party `1` of the coalition `{1}`. -/
private abbrev receiver : ({1} : Finset (Fin 2)) := ⟨1, Finset.mem_singleton_self 1⟩

/-- The simulator family `iknpReceiverSim` for a corrupted receiver is PPT for `iknpEncoding`
when the hash is computed in polynomial time: it draws `m n` words of `n` bits for the rows and
`m n` bits for the unchosen entries, and hashes the rows. -/
theorem isPPT_iknpReceiverSim (hh : ComputableInPolyTime hash encBits encBool) :
    SimulatorFamily.IsPPT (iknpEncoding hash m) (P := iknpFamily hash m)
      fun n _ => iknpReceiverSim (CorrelationRobust.atLevel hash n (m n)) := by
  have hr : ComputableInPolyTime (fun x : SimInput (iknpFamily hash m) {1} =>
      (iknpEncoding hash m).input.rep x.secParam x.desc 1 (x.inputs receiver))
      (encSimInput (iknpEncoding hash m)) encBits :=
    (iknpEncoding hash m).input.encCoalition_apply_polyTime
      (encSimInput_inputs_polyTime (iknpEncoding hash m) .id') receiver
  have hz : ComputableInPolyTime (fun x : SimInput (iknpFamily hash m) {1} =>
      (iknpEncoding hash m).output.rep x.secParam x.desc 1 (x.outputs receiver))
      (encSimInput (iknpEncoding hash m)) encBits :=
    (iknpEncoding hash m).output.encCoalition_apply_polyTime
      (encSimInput_outputs_polyTime (iknpEncoding hash m) .id') receiver
  have hn : ComputableInPolyTime (fun x : SimInput (iknpFamily hash m) {1} => x.secParam)
      (encSimInput (iknpEncoding hash m)) encUnary :=
    encSimInput_secParam_polyTime (iknpEncoding hash m) .id'
  have hcount := ComputableInPolyTime.length_bits.comp hr
  have hprog : IsPPTOn (encSimInput (iknpEncoding hash m)) encBits fun x =>
      OracleComp.replicate
        ((iknpEncoding hash m).input.rep x.secParam x.desc 1 (x.inputs receiver)).length
        (BitString.sampleList x.secParam) >>= fun T =>
      BitString.sampleList
        ((iknpEncoding hash m).input.rep x.secParam x.desc 1 (x.inputs receiver)).length >>=
        fun u => pure (receiverSimWord hash
          ((iknpEncoding hash m).input.rep x.secParam x.desc 1 (x.inputs receiver))
          ((iknpEncoding hash m).output.rep x.secParam x.desc 1 (x.outputs receiver)) T u) := by
    refine IsPPTOn.bind_with (left := encList encBits)
      (IsPPTOn.replicate hn.sampleList hcount) ?_
    refine IsPPTOn.bind_with (left := encBits) (hcount.comp (.fst _ _)).sampleList ?_
    have hx : ComputableInPolyTime
        (fun q : (SimInput (iknpFamily hash m) {1} × List (List Bool)) × List Bool => q.1.1)
        (encPair (encPair (encSimInput (iknpEncoding hash m)) (encList encBits)) encBits)
        (encSimInput (iknpEncoding hash m)) :=
      (ComputableInPolyTime.fst _ (encList encBits)).comp (.fst _ encBits)
    exact (receiverSimWord_polyTime hash hh (hr.comp hx) (hz.comp hx)
      ((ComputableInPolyTime.snd _ (encList encBits)).comp (.fst _ encBits))
      (.snd _ encBits)).isPPTOn
  refine isPPTOn_iff_encoded.mpr (hprog.congr fun x => ?_)
  obtain ⟨n, d, xs, ys⟩ := x
  have hlen : ((iknpEncoding hash m).input.rep n d 1 (xs receiver)).length = m n :=
    List.length_ofFn
  simp only [hlen, iknpReceiverSim, ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_pure,
    ProbComp.eval_uniform, BitString.eval_sampleList, ProbComp.eval_replicate_sampleList,
    BitString.uniformList, PMF.bind_map, PMF.map_bind, PMF.pure_map, Function.comp_def]
  refine congrArg _ (funext fun T => congrArg _ (funext fun u => congrArg PMF.pure ?_))
  refine Eq.trans ?_ ((iknpEncoding hash m).view.encCoalition_singleton n d 1 _).symm
  obtain ⟨r, hr⟩ : ∃ r : Fin (m n) → Bool, xs receiver = r := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z : Fin (m n) → Bool, ys receiver = z := ⟨_, rfl⟩
  have hr' : (iknpEncoding hash m).input.rep n d 1 (xs receiver) = List.ofFn r := by rw [hr]; rfl
  have hz' : (iknpEncoding hash m).output.rep n d 1 (ys receiver) = List.ofFn z := by rw [hz]; rfl
  simp only [receiverSimWord, hr', hz', List.map_ofFn, Function.comp_def, bitsZipWith4_ofFn]
  simp only [receiver] at hr hz
  simp only [hr, hz]
  rfl

/-! ### Corrupted receiver: the reduction to correlation robustness -/

/-- The correlation-robustness distinguisher built from an environment `Z` that corrupts the
receiver: at level `k`, given the inputs `t` and the bits `w`, run `Z.choose`, then
`iknpReduction` with `Z.guess`, which writes `t` as the receiver's matrix and masks the chosen
entries with `hash tⱼ` and the unchosen ones with `wⱼ`. -/
noncomputable def iknpReceiverToCR (Z : Environment (iknpFamily hash m) {1}) :
    CorrelationRobust.Distinguisher m := fun k p => do
  let c ← Z.choose k ()
  iknpReduction (CorrelationRobust.atLevel hash k (m k)) c.inputs (Z.guess k () c.state) p

/-- The real game against a corrupted receiver is the real correlation-robustness game of the
reduction. -/
theorem realGame_iknp_receiver_eq (Z : Environment (iknpFamily hash m) {1}) (n : ℕ) :
    (iknpFamily hash m).realGame (fun _ => PMF.pure ()) {1} Z n =
      CorrelationRobust.realGame (CorrelationRobust.atLevel hash n (m n))
        (iknpReceiverToCR hash m Z n) := by
  simp only [ProtocolFamily.realGame, PMF.monad_bind_eq_bind, PMF.pure_bind]
  simp only [realJoint_iknp_receiver_bind]
  simp only [CorrelationRobust.realGame, iknpReceiverToCR, ProbComp.eval_bind]
  pmf_swap

/-- The ideal game against a corrupted receiver with `iknpReceiverSim` is the ideal
correlation-robustness game of the reduction. -/
theorem idealGame_iknp_receiver_eq (Z : Environment (iknpFamily hash m) {1}) (n : ℕ) :
    (iknpFamily hash m).idealGame (fun _ => PMF.pure ()) {1}
        (fun n _ => iknpReceiverSim (CorrelationRobust.atLevel hash n (m n))) Z n =
      CorrelationRobust.idealGame (iknpReceiverToCR hash m Z n) := by
  simp only [ProtocolFamily.idealGame, PMF.monad_bind_eq_bind, PMF.pure_bind]
  simp only [← ProbComp.eval_bind, idealJoint_iknp_receiver_bind]
  simp only [CorrelationRobust.idealGame, iknpReceiverToCR, ProbComp.eval_bind]
  pmf_swap

/-! ### Corrupted receiver: efficiency of the reduction -/

/-- The masked bit `b` that the reduction writes for a pair with choice bit `rj`, sender's bit
`xj`, challenge bit `wj` and hash `hj` of the input: `xj + hj` when `b = rj`, else `xj + wj`. -/
private def redMask (b rj xj wj hj : Bool) : Bool :=
  xj ^^ (if b = rj then hj else wj)

/-- The receiver's output bit for a pair with choice bit `rj` and entries `x0j`, `x1j`. -/
private def chosenBit (rj x0j x1j _ : Bool) : Bool :=
  if rj then x1j else x0j

/-- The words of the guessing-stage input that `iknpReceiverToCR` gives the environment, laid out
as `encGuessInputFields`, from the level `k`, the input words `t`, the challenge bits `w`, the
sender's pair words `p`, the choice bits `r` and the state: the table of the receiver's view
words, and the table of the empty word and the receiver's output bits. -/
private noncomputable def reductionGuessWords (k : ℕ) (t : List (List Bool)) (w : List Bool)
    (p : List Bool × List Bool) (r state : List Bool) :
    ℕ × Unit × List Bool × List Bool × List Bool :=
  (k, (), state,
    encPi encBits fun _ : ({1} : Finset (Fin 2)) => encIKNPReceiverViewWords
      ⟨r, t, bitsZipWith4 (redMask false) r p.1 w (t.map hash),
        bitsZipWith4 (redMask true) r p.2 w (t.map hash)⟩,
    encPi encBits fun i : Fin 2 =>
      Fin.cases (motive := fun _ => List Bool) [] (fun _ => bitsZipWith4 chosenBit r p.1 p.2 r) i)

/-- `reductionGuessWords` of computed parts is computed in polynomial time. -/
private theorem reductionGuessWords_polyTime (hh : ComputableInPolyTime hash encBits encBool)
    {γ : Type} {enc : γ ↪ List Bool} {k : γ → ℕ} {t : γ → List (List Bool)}
    {w r state : γ → List Bool} {p : γ → List Bool × List Bool}
    (hk : ComputableInPolyTime k enc encUnary) (ht : ComputableInPolyTime t enc (encList encBits))
    (hw : ComputableInPolyTime w enc encBits)
    (hp : ComputableInPolyTime p enc (encPair encBits encBits))
    (hr : ComputableInPolyTime r enc encBits) (hs : ComputableInPolyTime state enc encBits) :
    ComputableInPolyTime
      (fun c => reductionGuessWords hash (k c) (t c) (w c) (p c) (r c) (state c)) enc
      (encGuessInputFields (iknpEncoding hash m)) := by
  have hviews := (ComputableInPolyTime.pi fun _ : ({1} : Finset (Fin 2)) =>
    (encIKNPReceiverViewWords_mk_polyTime hr ht
      (bitsZipWith4_polyTime (redMask false) hr hp.fst' hw (map_hash_polyTime hh ht))
      (bitsZipWith4_polyTime (redMask true) hr hp.snd' hw
        (map_hash_polyTime hh ht))).encoding_comp).encoding_comp
  have houtputs : ComputableInPolyTime (fun c => encPi encBits fun i : Fin 2 =>
      Fin.cases (motive := fun _ => List Bool) []
        (fun _ => bitsZipWith4 chosenBit (r c) (p c).1 (p c).2 (r c)) i) enc encBits := by
    refine (ComputableInPolyTime.pi fun i => ?_).encoding_comp
    refine Fin.cases ?_ (fun _ => ?_) i
    · exact ComputableInPolyTime.const []
    · exact bitsZipWith4_polyTime _ hr hp.fst' hp.snd' hr
  exact hk.prod ((ComputableInPolyTime.const ()).prod (hs.prod (hviews.prod houtputs)))

/-- `iknpReceiverToCR Z` is uniform strict PPT whenever `Z` is and the hash is computed in
polynomial time. -/
theorem isPPT_iknpReceiverToCR (hh : ComputableInPolyTime hash encBits encBool)
    {Z : Environment (iknpFamily hash m) {1}} (hZ : Z.IsPPT (iknpEncoding hash m)) :
    (iknpReceiverToCR hash m Z).IsPPT := by
  obtain ⟨W, hW, hWeq⟩ := hZ.guess.exists_bool_factor (encGuessInput_apply (iknpEncoding hash m))
  have hprog : IsPPTOn (CorrelationRobust.encInput m) encBool fun x =>
      (fun c => ((fun i => (iknpEncoding hash m).input.rep x.level () i (c.inputs i)), c.state)) <$>
        Z.choose x.level () >>= fun cw =>
          W (reductionGuessWords hash x.level (List.ofFn fun j => List.ofFn (x.inputs j))
            (List.ofFn x.outputs) (cw.1 0) (cw.1 1) cw.2) := by
    refine IsPPTOn.bind_with (hZ.choose.preprocess
      (prepare := fun x : CorrelationRobust.Input m => (x.level, ()))
      ((CorrelationRobust.encInput_level_polyTime m .id').prod (.const ()))) ?_
    have hx : ComputableInPolyTime
        (fun q : CorrelationRobust.Input m × (((i : Fin 2) → IKNPInputWords i) × List Bool) => q.1)
        (encPair (CorrelationRobust.encInput m)
          (encPair (encDPi (iknpEncoding hash m).input.enc) encBits))
        (CorrelationRobust.encInput m) := .fst _ _
    have htable : ComputableInPolyTime
        (fun q : CorrelationRobust.Input m × (((i : Fin 2) → IKNPInputWords i) × List Bool) =>
          q.2.1)
        (encPair (CorrelationRobust.encInput m)
          (encPair (encDPi (iknpEncoding hash m).input.enc) encBits))
        (encDPi (iknpEncoding hash m).input.enc) := (ComputableInPolyTime.snd _ _).fst'
    have ht : ComputableInPolyTime
        (fun q : CorrelationRobust.Input m × (((i : Fin 2) → IKNPInputWords i) × List Bool) =>
          List.ofFn fun j => List.ofFn (q.1.inputs j))
        (encPair (CorrelationRobust.encInput m)
          (encPair (encDPi (iknpEncoding hash m).input.enc) encBits)) (encList encBits) :=
      (CorrelationRobust.encInput_inputs_polyTime m hx).of_enc_eq fun _ => rfl
    have hp : ComputableInPolyTime
        (fun q : CorrelationRobust.Input m × (((i : Fin 2) → IKNPInputWords i) × List Bool) =>
          (q.2.1 0 : List Bool × List Bool))
        (encPair (CorrelationRobust.encInput m)
          (encPair (encDPi (iknpEncoding hash m).input.enc) encBits)) (encPair encBits encBits) :=
      (ComputableInPolyTime.dpi_apply (iknpEncoding hash m).input.enc 0).comp htable
    have hr : ComputableInPolyTime
        (fun q : CorrelationRobust.Input m × (((i : Fin 2) → IKNPInputWords i) × List Bool) =>
          (q.2.1 1 : List Bool))
        (encPair (CorrelationRobust.encInput m)
          (encPair (encDPi (iknpEncoding hash m).input.enc) encBits)) encBits :=
      (ComputableInPolyTime.dpi_apply (iknpEncoding hash m).input.enc 1).comp htable
    exact hW.preprocess (reductionGuessWords_polyTime (m := m) hash hh
      (CorrelationRobust.encInput_level_polyTime m hx) ht
      (CorrelationRobust.encInput_outputs_polyTime m hx) hp hr (ComputableInPolyTime.snd _ _).snd')
  refine hprog.congr fun x => ?_
  simp only [iknpReceiverToCR, ProbComp.eval_bind, ProbComp.eval_map, PMF.bind_map]
  refine congrArg (PMF.bind _) (funext fun c => ?_)
  obtain ⟨xs, state⟩ := c
  obtain ⟨X, r, rfl⟩ : ∃ (X : Fin (m x.level) → Bool → Bool) (r : Fin (m x.level) → Bool),
      xs = fun i => Fin.cases (motive := fun i => (batchOTSpec (m x.level) Bool).Query () i) X
        (fun _ => r) i :=
    ⟨xs 0, xs 1, funext fun i => Fin.cases rfl (fun j => Fin.cases rfl (fun k => k.elim0) j) i⟩
  refine congrArg ProbComp.eval (Eq.trans (congrArg W ?_) (hWeq ⟨x.level, (), state, _, _⟩).symm)
  have hp : (iknpEncoding hash m).input.rep x.level () 0
      (Fin.cases (motive := fun i => (batchOTSpec (m x.level) Bool).Query () i) X (fun _ => r) 0) =
        (List.ofFn fun j => X j false, List.ofFn fun j => X j true) := rfl
  have hr : (iknpEncoding hash m).input.rep x.level () 1
      (Fin.cases (motive := fun i => (batchOTSpec (m x.level) Bool).Query () i) X (fun _ => r) 1) =
        List.ofFn r := rfl
  simp only [reductionGuessWords, hp, hr, List.map_ofFn, Function.comp_def, bitsZipWith4_ofFn]
  refine Prod.ext rfl (Prod.ext rfl (Prod.ext rfl (Prod.ext ?_ ?_)))
  · refine Eq.trans ?_
      ((iknpEncoding hash m).view.encCoalition_singleton x.level () 1 _).symm
    rfl
  · simp only [PartyEncoding.encAll, Function.Embedding.coeFn_mk, encDPi_apply]
    congr 1
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    obtain rfl := Fin.fin_one_eq_zero j
    refine congrArg List.ofFn (funext fun j => ?_)
    change (if r j then X j true else X j false) = X j (r j)
    cases r j <;> rfl

end Cslib.Crypto.Protocols.MPC

namespace Cslib.Crypto.CorrelationRobust

open Cslib.Crypto.Protocols.MPC

/-- **Semi-honest security of IKNP oblivious-transfer extension**: if `hash` is correlation
robust and the number `m n` of extended transfers is polynomially bounded, then
`iknpFamily hash m` is semi-honest secure against a corrupted sender (`{0}`) and against a
corrupted receiver (`{1}`), for the encoding `iknpEncoding` (`ProtocolFamily.SemiHonestSecure`).
These are the two Claims of [IshaiKilianNissimPetrank2003] §3.1 for Fig. 1, the sender's
(p. 153) in its semi-honest case and the receiver's (p. 154), with the random oracle replaced by a
correlation robust hash as §5 describes (p. 157): `n` ideal base transfers of `(m n)`-bit strings
(the source's `OT^k_m` hybrid), and bit transfers with one hash at every position. Theorems 2 and
3 of the source, which concern the fully secure variant of §4 composed with the reduction of
`OT^k_m` to `OT^k_k`, are not formalized. Environments are uniform and choose the inputs, and
corruption is static and of one party (module documentation). The simulators are
`iknpSenderSim`, perfect, and `iknpReceiverSim`, certified by `isPPT_iknpSenderSim` and
`isPPT_iknpReceiverSim`; the reduction is certified by `isPPT_iknpReceiverToCR`. -/
theorem iknpSemiHonestSecure {hash : List Bool → Bool} {m : ℕ → ℕ} (h : CorrelationRobust hash)
    (hm : PolynomiallyBounded m) :
    (iknpFamily hash m).SemiHonestSecure (fun _ => PMF.pure ()) {0} (iknpEncoding hash m) ∧
      (iknpFamily hash m).SemiHonestSecure (fun _ => PMF.pure ()) {1} (iknpEncoding hash m) := by
  refine ⟨ProtocolFamily.SemiHonestSecure.of_perfect (isPPT_iknpSenderSim hash m)
    fun _ _ x => idealJoint_iknp_sender _ x,
    ⟨_, isPPT_iknpReceiverSim hash m h.polyTime, fun Z hZ => ?_⟩⟩
  simpa only [realGame_iknp_receiver_eq, idealGame_iknp_receiver_eq] using
    h.secure m hm _ (isPPT_iknpReceiverToCR hash m h.polyTime hZ)

end Cslib.Crypto.CorrelationRobust
