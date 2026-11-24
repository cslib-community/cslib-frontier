/-
Copyright (c) 2026 Samuel Schlesinger, Phillipp Schoppmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Phillipp Schoppmann
-/

import CslibFrontier.Crypto.Primitives.Garbling.OutputSimulatable
import CslibFrontier.Crypto.Negligible.Dyadic
import CslibFrontier.Crypto.Game.HiddenBit
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Computability.Probabilistic.PPT.Composition
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Tactic.PolyTime

/-!
# Tests and boundary separations for output simulatability and token-checked decoding

This suite checks both `PointPermute` token-checked decoding vs unauthenticated `decodeWord` and
a self-contained 1-gate garbling scheme `tokenGateScheme` constructed via
`Scheme.withTokenDecoding`:

* `PointPermute.scheme (fun _ _ => [])` fails `aut` with advantage `1` (`PointPermute.flipForger`)
  and fails `OutSimSecure` (`PointPermute.not_outSimSecure`), while wrapping it with
  `PointPermute.withTokenDecoding` preserves `IsValid`, `WellTyped`, and `IsEfficient` and
  rejects the flipped output forgery (`decode_withTokenDecoding_flip_eq_none`).
* `tokenGateScheme` satisfies unconditional `Aut` (`autAdvantage ≤ 2^(-(k+1))`), perfect `ObvSim`
  (`obvSimAdvantage = 0`), universal output simulatability (`OutSimSecureUniversal`, via
  `outSimSecureUniversal_of_obvSim_and_aut`), and universal privacy (`PrvSimSecureUniversal`, via
  `prvSimSecureUniversal_of_outSimSecureUniversal_and_decSim`), whereas its parity-decoded sibling
  `baseGateScheme` shares the exact same `(F, X)` distribution (`obv.sim = 0`) yet fails `aut`
  with advantage `1`.
* `leakyDecTokenScheme` separates `OutSimSecureUniversal` from `PrvSimSecure`: prepending the
  secret gate bit to `decInfo` preserves `ObvSim`, `Aut`, and `OutSimSecureUniversal`, while
  breaking `PrvSimSecure`.
-/

namespace CslibFrontierTests.Crypto.GarblingOutputSim

open Cslib Cslib.Crypto Cslib.Crypto.Garbling Cslib.Probability Turing.MultiTapeTM
open scoped NNReal

/-! ## `PointPermute`: unauthenticated `decodeWord` vs `withTokenDecoding` -/

private def emptyFamily : List Bool → List Bool → List Bool := fun _ _ => []

private theorem emptyFamily_polyTime :
    ComputableInPolyTime (fun p : List Bool × List Bool => emptyFamily p.1 p.2)
      (encPair encBits encBits) encBits :=
  ComputableInPolyTime.const []

theorem pointPermute_flip_aut_one (k : ℕ) :
    autAdvantage (PointPermute.scheme emptyFamily) k (PointPermute.flipForger emptyFamily) = 1 :=
  PointPermute.autAdvantage_flipForger emptyFamily k

theorem pointPermute_not_outSim :
    ¬ (PointPermute.scheme emptyFamily).OutSimSecure phiTopo encValidCircuit encValidTopo :=
  PointPermute.not_outSimSecure emptyFamily_polyTime phiTopo

theorem pointPermute_withTokenDecoding_valid :
    ((PointPermute.scheme emptyFamily).withTokenDecoding
      (PointPermute.outputTokenSpec emptyFamily)).IsValid :=
  PointPermute.withTokenDecoding_isValid emptyFamily

theorem pointPermute_withTokenDecoding_wellTyped :
    ((PointPermute.scheme emptyFamily).withTokenDecoding
      (PointPermute.outputTokenSpec emptyFamily)).WellTyped :=
  PointPermute.withTokenDecoding_wellTyped emptyFamily

theorem pointPermute_withTokenDecoding_efficient :
    ((PointPermute.scheme emptyFamily).withTokenDecoding
      (PointPermute.outputTokenSpec emptyFamily)).IsEfficient encValidCircuit :=
  PointPermute.withTokenDecoding_isEfficient emptyFamily_polyTime

/-- Concrete run at `k = 1` on `oneGateCircuit` with all-false coins (`length = 15`), showing
`decodeWord` accepts the flipped forgery while `withTokenDecoding` rejects it. -/
theorem pointPermute_concrete_flip_separation :
    let coins : List Bool := List.replicate 15 false
    let G0 := PointPermute.scheme emptyFamily
    let G1 := G0.withTokenDecoding (PointPermute.outputTokenSpec emptyFamily)
    let g0 := G0.gb 1 PointPermute.oneGateCircuit coins
    let g1 := G1.gb 1 PointPermute.oneGateCircuit coins
    let Y := PointPermute.evalWord emptyFamily g0.fn (G0.encode g0.encInfo [false, false])
    (G0.decode g0.decInfo (Y.map (!·))).isSome = true ∧
      G1.decode g1.decInfo Y = some (G1.ev PointPermute.oneGateCircuit [false, false]) ∧
      G1.decode g1.decInfo (Y.map (!·)) = none := by
  intro coins G0 G1 g0 g1 Y
  have hn : PointPermute.oneGateCircuit.1.n = 2 := rfl
  have hm : PointPermute.oneGateCircuit.1.m = 1 := rfl
  have hq : PointPermute.oneGateCircuit.1.q = 1 := rfl
  have hc : coins.length = G0.coinLen 1 2 1 1 := by simp [G0, PointPermute.scheme, coins]
  have hc1 : coins.length = G0.coinLen 1 (G0.inLen PointPermute.oneGateCircuit)
      (G0.outLen PointPermute.oneGateCircuit) (G0.size PointPermute.oneGateCircuit) := by
    simpa [G0, PointPermute.scheme, hn, hm, hq] using hc
  have hx1 : ([false, false] : List Bool).length = G0.inLen PointPermute.oneGateCircuit := by
    simp [G0, PointPermute.scheme, hn]
  have hev := (PointPermute.outputTokenSpec_id_sound emptyFamily).eval_eq_activeTokens
    1 PointPermute.oneGateCircuit coins hc1 [false, false] hx1
  have hlen_ev : (G0.ev PointPermute.oneGateCircuit [false, false]).length = 1 := by
    simp [G0, PointPermute.scheme,
      ConventionalCircuit.length_evalCirc PointPermute.oneGateCircuit.1 [false, false]
        PointPermute.oneGateCircuit.2.m_le_q, hm]
  obtain ⟨b, hb_eq⟩ := List.length_eq_one_iff.mp hlen_ev
  have hzip_tok : Y = PointPermute.labelOf 1 3 coins 2
      (if b then !(PointPermute.permOf coins 2) else PointPermute.permOf coins 2) := by
    have hYeq : Y = G0.evalGarbled (G0.gb 1 PointPermute.oneGateCircuit coins).fn
        (G0.encode (G0.gb 1 PointPermute.oneGateCircuit coins).encInfo [false, false]) := by
      simp only [Y, g0, G0, PointPermute.scheme]
    rw [hYeq, hev, hb_eq]
    simp only [PointPermute.outputTokenSpec, PointPermute.scheme]
    rw [List.ofFn_congr hm]
    simp [List.ofFn_succ, List.ofFn_zero, hn, hm, hq]
    cases b <;> simp
  have hkey_false : ∀ col : Bool, (PointPermute.keyOf 1 3 coins 2 col).getD 0 false = false := by
    intro col
    rw [PointPermute.keyOf, BitString.getD_listRow (by omega)]
    cases col <;> simp [coins]
  have hlab0 : ∀ col : Bool, (PointPermute.labelOf 1 3 coins 2 col).getD 0 false = false := by
    intro col
    have hlen_key : (PointPermute.keyOf 1 3 coins 2 col).length = 2 := by
      simp [PointPermute.keyOf]
    rw [PointPermute.labelOf, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by rw [hlen_key]; omega), ← List.getD_eq_getElem?_getD]
    exact hkey_false col
  refine ⟨?_, ?_, ?_⟩
  · have hdlen : g0.decInfo.length = 1 := by
      simp [g0, G0, PointPermute.scheme, PointPermute.decInfoWord, hm]
    simp [G0, PointPermute.scheme, PointPermute.decodeWord, hdlen, Nat.mod_one]
  · have hY_g1 : Y = G1.evalGarbled g1.fn (G1.encode g1.encInfo [false, false]) := by
      simp only [Y, g0, g1, G1, G0, Scheme.withTokenDecoding, PointPermute.scheme]
    have hg1 : g1 ∈ (ProbComp.eval (G1.garble 1 PointPermute.oneGateCircuit)).support :=
      G1.mem_support_eval_garble_iff.mpr
        ⟨coins, by simpa [G1, G0, Scheme.withTokenDecoding, Scheme.coins] using hc1, rfl⟩
    have hx1' : ([false, false] : List Bool).length =
        ((PointPermute.scheme emptyFamily).withTokenDecoding
          (PointPermute.outputTokenSpec emptyFamily)).inLen PointPermute.oneGateCircuit := by
      simpa [G1, G0, Scheme.withTokenDecoding] using hx1
    have hg1' : g1 ∈ (ProbComp.eval (((PointPermute.scheme emptyFamily).withTokenDecoding
        (PointPermute.outputTokenSpec emptyFamily)).garble 1
          PointPermute.oneGateCircuit)).support :=
      by simpa only [G1, G0] using hg1
    have hcorr : ((PointPermute.scheme emptyFamily).withTokenDecoding
        (PointPermute.outputTokenSpec emptyFamily)).decode g1.decInfo
        (((PointPermute.scheme emptyFamily).withTokenDecoding
          (PointPermute.outputTokenSpec emptyFamily)).evalGarbled g1.fn
          (((PointPermute.scheme emptyFamily).withTokenDecoding
            (PointPermute.outputTokenSpec emptyFamily)).encode g1.encInfo [false, false])) =
        some (((PointPermute.scheme emptyFamily).withTokenDecoding
          (PointPermute.outputTokenSpec emptyFamily)).ev PointPermute.oneGateCircuit
          [false, false]) :=
      pointPermute_withTokenDecoding_valid.correct 1 Nat.zero_lt_one
        PointPermute.oneGateCircuit [false, false] hx1' g1 hg1'
    rw [hY_g1]
    exact hcorr
  · have hY0 : (Y.map (!·)).getD 0 false = true := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, hzip_tok,
        List.getElem?_eq_getElem (by rw [PointPermute.length_labelOf]; omega),
        Option.map_some, Option.getD_some]
      have hget0 := hlab0
        (if b then !(PointPermute.permOf coins 2) else PointPermute.permOf coins 2)
      rw [List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by rw [PointPermute.length_labelOf]; omega),
        Option.getD_some] at hget0
      simp [hget0]
    dsimp only [Y, g0, G0, PointPermute.scheme, Scheme.gb, Scheme.encode] at hY0
    refine PointPermute.decode_withTokenDecoding_flip_eq_none emptyFamily hc ⟨?_, ?_⟩
    · intro heq
      have h0 := congrArg (fun l => l.getD 0 false) heq
      simp only [hn, hm, hq, Nat.add_zero, Nat.reduceAdd, Nat.reduceSub] at h0
      rw [hY0, hlab0] at h0
      exact Bool.noConfusion h0
    · intro heq
      have h0 := congrArg (fun l => l.getD 0 false) heq
      simp only [hn, hm, hq, Nat.add_zero, Nat.reduceAdd, Nat.reduceSub] at h0
      rw [hY0, hlab0] at h0
      exact Bool.noConfusion h0

/-! ## Self-contained 1-gate scheme: `baseGateScheme` vs `tokenGateScheme` -/

/-- Minimal unit side information for 1-bit `Bool`-gate functions `(1, 1, 1)`. -/
def unitSideInfo : SideInfo Bool Unit where
  phi _ := ()
  inLen _ := 1
  outLen _ := 1
  size _ := 1

private theorem unitSideInfo_phi_polyTime :
    ComputableInPolyTime unitSideInfo.phi encBool encUnit :=
  ComputableInPolyTime.const ()

private def baseGateCoinLen (k : ℕ) : ℕ := 2 + 4 * (k + 1)

private def coinInPerm (coins : List Bool) : Bool := coins.getD 0 false

private def coinOutPerm (coins : List Bool) : Bool := coins.getD 1 false

private def coinInKey (k : ℕ) (coins : List Bool) (c : Bool) : List Bool :=
  BitString.listRow (k + 1) (if c then 1 else 0) (coins.drop 2)

private def coinOutKey (k : ℕ) (coins : List Bool) (c : Bool) : List Bool :=
  BitString.listRow (k + 1) (if c then 3 else 2) (coins.drop 2)

private def inLabel (k : ℕ) (coins : List Bool) (c : Bool) : List Bool :=
  coinInKey k coins c ++ [c]

private def outLabel (k : ℕ) (coins : List Bool) (c : Bool) : List Bool :=
  coinOutKey k coins c ++ [c]

private theorem length_inLabel (k : ℕ) (coins : List Bool) (c : Bool) :
    (inLabel k coins c).length = k + 2 := by
  simp [inLabel, coinInKey]

private theorem length_outLabel (k : ℕ) (coins : List Bool) (c : Bool) :
    (outLabel k coins c).length = k + 2 := by
  simp [outLabel, coinOutKey]

private theorem outLabel_perm_ne_not (k : ℕ) (coins : List Bool) (q : Bool) :
    outLabel k coins q ≠ outLabel k coins (!q) := by
  intro h
  have hbit := congrArg (fun l => l.getD (k + 1) false) h
  have h0 : (coinOutKey k coins q).length = k + 1 := by simp [coinOutKey]
  have h1 : (coinOutKey k coins (!q)).length = k + 1 := by simp [coinOutKey]
  simp only [outLabel, List.getD_eq_getElem?_getD] at hbit
  rw [List.getElem?_append_right (by omega), h0, Nat.sub_self] at hbit
  rw [List.getElem?_append_right (by omega), h1, Nat.sub_self] at hbit
  cases q <;> simp at hbit

private def baseGateFn (k : ℕ) (b : Bool) (coins : List Bool) : List Bool :=
  List.zipWith xor (inLabel k coins false)
    (outLabel k coins (coinInPerm coins ^^ b ^^ coinOutPerm coins)) ++
  List.zipWith xor (inLabel k coins true)
    (outLabel k coins (!(coinInPerm coins) ^^ b ^^ coinOutPerm coins))

private def baseGateEncInfo (k : ℕ) (coins : List Bool) : List Bool :=
  inLabel k coins (coinInPerm coins) ++ inLabel k coins (!(coinInPerm coins))

private def baseGateEncode (e x : List Bool) : List Bool :=
  let w := e.length / 2
  if x.headD false then e.drop w else e.take w

private def baseGateEval (F X : List Bool) : List Bool :=
  let w := F.length / 2
  let c := X.getD (X.length - 1) false
  let row := if c then F.drop w else F.take w
  List.zipWith xor X row

private def parityDecode (d Y : List Bool) : Option (List Bool) :=
  if Y.isEmpty then none else some [Y.getD (Y.length - 1) false ^^ d.headD false]

/-- A 1-gate scheme with one-time-pad encrypted rows (`F`) and unauthenticated parity decoding
(`parityDecode`). -/
def baseGateScheme : Scheme Bool where
  inLen _ := 1
  outLen _ := 1
  size _ := 1
  ev b x := [x.headD false ^^ b]
  coinLen k _ _ _ := baseGateCoinLen k
  gb k b coins := ⟨baseGateFn k b coins, baseGateEncInfo k coins, [coinOutPerm coins]⟩
  encode := baseGateEncode
  evalGarbled := baseGateEval
  decode := parityDecode

private theorem eval_baseGate_eq (k : ℕ) (b : Bool) (coins x : List Bool) (_hx : x.length = 1) :
    baseGateEval (baseGateFn k b coins) (baseGateEncode (baseGateEncInfo k coins) x) =
      outLabel k coins ((x.headD false ^^ b) ^^ coinOutPerm coins) := by
  have hl_e : (baseGateEncInfo k coins).length = 2 * (k + 2) := by
    simp [baseGateEncInfo, length_inLabel]; omega
  have hl_F : (baseGateFn k b coins).length = 2 * (k + 2) := by
    simp [baseGateFn, length_inLabel, length_outLabel]; omega
  have hw_e : (baseGateEncInfo k coins).length / 2 = k + 2 := by omega
  have hw_F : (baseGateFn k b coins).length / 2 = k + 2 := by omega
  have henc : baseGateEncode (baseGateEncInfo k coins) x =
      inLabel k coins (x.headD false ^^ coinInPerm coins) := by
    simp only [baseGateEncode, baseGateEncInfo]
    cases hx0 : x.headD false <;> cases hp : coinInPerm coins
    · exact List.take_left' (by simp [length_inLabel]; omega)
    · exact List.take_left' (by simp [length_inLabel]; omega)
    · exact List.drop_left' (by simp [length_inLabel]; omega)
    · exact List.drop_left' (by simp [length_inLabel]; omega)
  rw [henc]
  simp only [baseGateEval, hw_F]
  have hcol : (inLabel k coins (x.headD false ^^ coinInPerm coins)).getD
      ((inLabel k coins (x.headD false ^^ coinInPerm coins)).length - 1) false =
      (x.headD false ^^ coinInPerm coins) := by
    simp [inLabel, coinInKey, List.getD_eq_getElem?_getD]
  rw [hcol]
  cases hxp : x.headD false ^^ coinInPerm coins
  · have hrow : (baseGateFn k b coins).take (k + 2) =
        List.zipWith xor (inLabel k coins false)
          (outLabel k coins (coinInPerm coins ^^ b ^^ coinOutPerm coins)) := by
      simp only [baseGateFn]
      have hlen_w : (List.zipWith xor (inLabel k coins false)
          (outLabel k coins (coinInPerm coins ^^ b ^^ coinOutPerm coins))).length = k + 2 := by
        simp [length_inLabel, length_outLabel]
      exact List.take_left' hlen_w
    have hpeq : coinInPerm coins = x.headD false := by
      revert hxp; cases x.headD false <;> cases coinInPerm coins <;> decide
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [hrow, hpeq]
    apply List.ext_getElem (by simp [length_inLabel, length_outLabel])
    intro i hi1 hi2
    simp only [List.getElem_zipWith]
    rw [← Bool.xor_assoc, Bool.xor_self, Bool.false_xor]
  · have hrow : (baseGateFn k b coins).drop (k + 2) =
        List.zipWith xor (inLabel k coins true)
          (outLabel k coins (!(coinInPerm coins) ^^ b ^^ coinOutPerm coins)) := by
      simp only [baseGateFn]
      have hlen_w : (List.zipWith xor (inLabel k coins false)
          (outLabel k coins (coinInPerm coins ^^ b ^^ coinOutPerm coins))).length = k + 2 := by
        simp [length_inLabel, length_outLabel]
      exact List.drop_left' hlen_w
    have hpeq : (!coinInPerm coins) = x.headD false := by
      revert hxp; cases x.headD false <;> cases coinInPerm coins <;> decide
    simp only [↓reduceIte]
    rw [hrow, hpeq]
    apply List.ext_getElem (by simp [length_inLabel, length_outLabel])
    intro i hi1 hi2
    simp only [List.getElem_zipWith]
    rw [← Bool.xor_assoc, Bool.xor_self, Bool.false_xor]

theorem baseGateScheme_isValid : baseGateScheme.IsValid where
  length k _ f f' _ g hg g' hg' := by
    obtain ⟨coins, _, rfl⟩ := baseGateScheme.mem_support_eval_garble_iff.mp hg
    obtain ⟨coins', _, rfl⟩ := baseGateScheme.mem_support_eval_garble_iff.mp hg'
    simp [baseGateScheme, baseGateFn, baseGateEncInfo, length_inLabel, length_outLabel]
  nonDegenerate k _ f f' _ coins _ := by
    simp [baseGateScheme, baseGateEncInfo]
  correct k _ f x hx g hg := by
    obtain ⟨coins, _, rfl⟩ := baseGateScheme.mem_support_eval_garble_iff.mp hg
    have hev := eval_baseGate_eq k f coins x hx
    simp only [baseGateScheme] at hev ⊢
    rw [hev, parityDecode]
    have hlen : (outLabel k coins ((x.headD false ^^ f) ^^ coinOutPerm coins)).length = k + 2 :=
      length_outLabel _ _ _
    have hne : (outLabel k coins ((x.headD false ^^ f) ^^ coinOutPerm coins)).isEmpty = false := by
      rw [Bool.eq_false_iff, ne_eq, List.isEmpty_iff, ← List.length_eq_zero_iff]
      omega
    simp only [hne, Bool.false_eq_true, ↓reduceIte]
    have hcol : (outLabel k coins ((x.headD false ^^ f) ^^ coinOutPerm coins)).getD
        ((outLabel k coins ((x.headD false ^^ f) ^^ coinOutPerm coins)).length - 1) false =
        ((x.headD false ^^ f) ^^ coinOutPerm coins) := by
      simp [outLabel, coinOutKey, List.getD_eq_getElem?_getD]
    rw [hcol]
    cases x.headD false <;> cases f <;> cases coinOutPerm coins <;> rfl

theorem baseGateScheme_wellTyped : baseGateScheme.WellTyped :=
  ⟨fun _ _ _ => rfl,
   fun _ _ _ _ _ Y y hy => by
     simp only [baseGateScheme, parityDecode] at hy
     split_ifs at hy with he
     · simp at hy
     · rw [Option.mem_def] at hy
       cases Option.some.inj hy
       rfl⟩

private theorem zipWithXor_polyTime {γ : Type} {enc : γ ↪ List Bool} {a b : γ → List Bool}
    (ha : ComputableInPolyTime a enc encBits) (hb : ComputableInPolyTime b enc encBits) :
    ComputableInPolyTime (fun x => List.zipWith xor (a x) (b x)) enc encBits := by
  have haL := (bits_encList_polyTime encBool).1.comp ha
  have hbL := (bits_encList_polyTime encBool).1.comp hb
  have hz := (ComputableInPolyTime.zip encBool encBool).comp (haL.prod hbL)
  have hm := (ComputableInPolyTime.map ComputableInPolyTime.bool_xor).comp hz
  have hbits := (bits_encList_polyTime encBool).2.comp hm
  convert hbits using 1
  funext x
  apply List.ext_getElem (by simp)
  intro i hi1 hi2
  simp

private theorem coinInKey_polyTime {γ : Type} {enc : γ ↪ List Bool}
    {k : γ → ℕ} {c : γ → List Bool} {col : γ → Bool}
    (hk : ComputableInPolyTime k enc encUnary) (hc : ComputableInPolyTime c enc encBits)
    (hcol : ComputableInPolyTime col enc encBool) :
    ComputableInPolyTime (fun a => coinInKey (k a) (c a) (col a)) enc encBits :=
  ComputableInPolyTime.bitsRowWithInput (ComputableInPolyTime.unary_add' hk (.const 1))
    (hcol.ite (.const 1) (.const 0)) (ComputableInPolyTime.bitsDropWithInput hc (.const 2))

private theorem coinOutKey_polyTime {γ : Type} {enc : γ ↪ List Bool}
    {k : γ → ℕ} {c : γ → List Bool} {col : γ → Bool}
    (hk : ComputableInPolyTime k enc encUnary) (hc : ComputableInPolyTime c enc encBits)
    (hcol : ComputableInPolyTime col enc encBool) :
    ComputableInPolyTime (fun a => coinOutKey (k a) (c a) (col a)) enc encBits :=
  ComputableInPolyTime.bitsRowWithInput (ComputableInPolyTime.unary_add' hk (.const 1))
    (hcol.ite (.const 3) (.const 2)) (ComputableInPolyTime.bitsDropWithInput hc (.const 2))

private theorem baseGate_polyTime : baseGateScheme.IsEfficient encBool := by
  have hk0 : ComputableInPolyTime (fun p : ℕ × Bool × List Bool => p.1)
      (encSchemeCoinsArg Bool encBool) encUnary := by fun_prop
  have hperm0 : ∀ {γ : Type} {enc : γ ↪ List Bool} (c : γ → List Bool),
      ComputableInPolyTime c enc encBits →
      ComputableInPolyTime (fun a => coinInPerm (c a)) enc encBool := by
    intro γ enc c hc; unfold coinInPerm; polytime
  have hperm1 : ∀ {γ : Type} {enc : γ ↪ List Bool} (c : γ → List Bool),
      ComputableInPolyTime c enc encBits →
      ComputableInPolyTime (fun a => coinOutPerm (c a)) enc encBool := by
    intro γ enc c hc; unfold coinOutPerm; polytime
  have hinLab : ∀ {γ : Type} {enc : γ ↪ List Bool} (k : γ → ℕ) (c : γ → List Bool)
      (col : γ → Bool),
      ComputableInPolyTime k enc encUnary → ComputableInPolyTime c enc encBits →
      ComputableInPolyTime col enc encBool →
      ComputableInPolyTime (fun a => inLabel (k a) (c a) (col a)) enc encBits := by
    intro γ enc k c col hk hc hcol
    exact ComputableInPolyTime.bitsAppend (coinInKey_polyTime hk hc hcol)
      (ComputableInPolyTime.bitsCons hcol (.const []))
  refine ⟨.const 1, .const 1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hcoin : ComputableInPolyTime (fun p : ℕ × Bool => 2 + 4 * (p.1 + 1))
        (encPair encUnary encBool) encUnary :=
      ComputableInPolyTime.unary_add' (.const 2)
        (ComputableInPolyTime.unary_mul' (.const 4)
          (ComputableInPolyTime.unary_add' (ComputableInPolyTime.fst _ _) (.const 1)))
    exact hcoin.of_enc_eq fun _ => rfl
  · let E := encSchemeCoinsArg Bool encBool
    have hb : ComputableInPolyTime (fun p : ℕ × Bool × List Bool => p.2.1) E encBool := by
      fun_prop
    have hc : ComputableInPolyTime (fun p : ℕ × Bool × List Bool => p.2.2) E encBits := by
      fun_prop
    have hp0 := hperm0 _ hc
    have hp1 := hperm1 _ hc
    have hl0 := hinLab _ _ (fun _ => false) hk0 hc (.const false)
    have hl1 := hinLab _ _ (fun _ => true) hk0 hc (.const true)
    have hlp := hinLab _ _ (fun p => coinInPerm p.2.2) hk0 hc hp0
    have hlnp := hinLab _ _ (fun p => !(coinInPerm p.2.2)) hk0 hc
      (ComputableInPolyTime.bool_not.comp hp0)
    have ho0col : ComputableInPolyTime
        (fun p : ℕ × Bool × List Bool => coinInPerm p.2.2 ^^ p.2.1 ^^ coinOutPerm p.2.2) E
        encBool :=
      ComputableInPolyTime.bool_xor.comp
        ((ComputableInPolyTime.bool_xor.comp (hp0.prod hb)).prod hp1)
    have ho1col : ComputableInPolyTime
        (fun p : ℕ × Bool × List Bool => !(coinInPerm p.2.2) ^^ p.2.1 ^^ coinOutPerm p.2.2) E
        encBool :=
      ComputableInPolyTime.bool_xor.comp
        ((ComputableInPolyTime.bool_xor.comp
          ((ComputableInPolyTime.bool_not.comp hp0).prod hb)).prod hp1)
    have ho0 := ComputableInPolyTime.bitsAppend (coinOutKey_polyTime hk0 hc ho0col)
      (ComputableInPolyTime.bitsCons ho0col (.const []))
    have ho1 := ComputableInPolyTime.bitsAppend (coinOutKey_polyTime hk0 hc ho1col)
      (ComputableInPolyTime.bitsCons ho1col (.const []))
    have hfn : ComputableInPolyTime (fun p : ℕ × Bool × List Bool => baseGateFn p.1 p.2.1 p.2.2)
        E encBits := by
      unfold baseGateFn
      exact ComputableInPolyTime.bitsAppend (zipWithXor_polyTime hl0 ho0)
        (zipWithXor_polyTime hl1 ho1)
    have henc : ComputableInPolyTime (fun p : ℕ × Bool × List Bool => baseGateEncInfo p.1 p.2.2)
        E encBits := by
      unfold baseGateEncInfo
      exact ComputableInPolyTime.bitsAppend hlp hlnp
    have hdec : ComputableInPolyTime (fun p : ℕ × Bool × List Bool => [coinOutPerm p.2.2])
        E encBits :=
      ComputableInPolyTime.bitsCons hp1 (.const [])
    exact Scheme.encGarbled_mk_polyTime hfn henc hdec
  · unfold baseGateScheme baseGateEncode; polytime
  · unfold baseGateScheme baseGateEval
    have hF : ComputableInPolyTime (fun p : List Bool × List Bool => p.1) (encPair encBits encBits)
        encBits := by fun_prop
    have hX : ComputableInPolyTime (fun p : List Bool × List Bool => p.2) (encPair encBits encBits)
        encBits := by fun_prop
    have hw : ComputableInPolyTime (fun p : List Bool × List Bool => p.1.length / 2)
        (encPair encBits encBits) encUnary :=
      ComputableInPolyTime.unary_div' (ComputableInPolyTime.length_bits_comp hF) (.const 2)
    have hc : ComputableInPolyTime
        (fun p : List Bool × List Bool => p.2.getD (p.2.length - 1) false)
        (encPair encBits encBits) encBool := by polytime
    have hrow : ComputableInPolyTime
        (fun p : List Bool × List Bool =>
          if p.2.getD (p.2.length - 1) false then p.1.drop (p.1.length / 2)
          else p.1.take (p.1.length / 2))
        (encPair encBits encBits) encBits :=
      hc.ite (hF.bitsDropWithInput hw) (hF.bitsTakeWithInput hw)
    exact zipWithXor_polyTime hX hrow
  · unfold baseGateScheme parityDecode; polytime
  · have hb : ComputableInPolyTime (fun p : Bool × List Bool => p.1) (encPair encBool encBits)
        encBool := by fun_prop
    have hx : ComputableInPolyTime (fun p : Bool × List Bool => p.2) (encPair encBool encBits)
        encBits := by fun_prop
    have hx0 : ComputableInPolyTime (fun p : Bool × List Bool => p.2.headD false)
        (encPair encBool encBits) encBool :=
      (ComputableInPolyTime.headD (encA := encBool) (encL := encBits) false).comp hx
    exact ComputableInPolyTime.bitsCons (ComputableInPolyTime.bool_xor.comp (hx0.prod hb))
      (.const [])

/-- Output token specification for `baseGateScheme`: `(outLabel k coins q, outLabel k coins (!q))`
where `q = coinOutPerm coins`. -/
def tokenGateSpec : OutputTokenSpec Bool baseGateScheme where
  tokenLen k _ := k + 2
  tokens k _ coins :=
    [(outLabel k coins (coinOutPerm coins), outLabel k coins (!(coinOutPerm coins)))]
  tag _ := id

theorem tokenGateSpec_sound : tokenGateSpec.Sound where
  length_tokens _ _ _ _ := rfl
  tokenLen_pos _ _ _ := by simp [tokenGateSpec]
  token_lengths k _ coins _ p hp := by
    simp only [tokenGateSpec, List.mem_singleton] at hp
    subst hp
    exact ⟨length_outLabel _ _ _, length_outLabel _ _ _⟩
  tag_distinct k _ coins _ p hp := by
    simp only [tokenGateSpec, List.mem_singleton] at hp
    subst hp
    exact outLabel_perm_ne_not k coins (coinOutPerm coins)
  eval_eq_activeTokens k f coins _ x hx := by
    have hev := eval_baseGate_eq k f coins x hx
    simp only [baseGateScheme, tokenGateSpec] at hev ⊢
    rw [hev]
    cases hbit : x.headD false ^^ f <;> simp
  decInfo_length_eq k f f' coins coins' _ _ _ _ _ := by
    let L := k + 2
    have hl0 : (outLabel k coins (coinOutPerm coins)).length = L := length_outLabel _ _ _
    have hl1 : (outLabel k coins (!(coinOutPerm coins))).length = L := length_outLabel _ _ _
    have hl0' : (outLabel k coins' (coinOutPerm coins')).length = L := length_outLabel _ _ _
    have hl1' : (outLabel k coins' (!(coinOutPerm coins'))).length = L := length_outLabel _ _ _
    simp only [tokenDecInfo, tokenGateSpec, encTokenDecInfo, encPair, encList, List.map_cons,
      List.map_nil]
    simp [hl0, hl1, hl0', hl1']
  nonDegenerate _ _ _ _ _ _ _ _ := ⟨rfl, rfl⟩

/-- The token-checked 1-gate scheme `baseGateScheme.withTokenDecoding tokenGateSpec`. -/
def tokenGateScheme : Scheme Bool := baseGateScheme.withTokenDecoding tokenGateSpec

theorem tokenGateScheme_isValid : tokenGateScheme.IsValid :=
  baseGateScheme_isValid.withTokenDecoding baseGateScheme_wellTyped tokenGateSpec_sound

theorem tokenGateScheme_wellTyped : tokenGateScheme.WellTyped :=
  baseGateScheme_wellTyped.withTokenDecoding tokenGateSpec_sound

theorem tokenGateScheme_isEfficient : tokenGateScheme.IsEfficient encBool := by
  refine baseGate_polyTime.withTokenDecoding
    (ComputableInPolyTime.unary_add' (ComputableInPolyTime.fst _ _) (.const 2)) ?_
    (ComputableInPolyTime.snd _ _)
  have hk : ComputableInPolyTime (fun p : ℕ × Bool × List Bool => p.1)
      (encSchemeCoinsArg Bool encBool) encUnary :=
    ComputableInPolyTime.fst encUnary (encPair encBool encBits)
  have hc : ComputableInPolyTime (fun p : ℕ × Bool × List Bool => p.2.2)
      (encSchemeCoinsArg Bool encBool) encBits :=
    (ComputableInPolyTime.snd encBool encBits).comp
      (ComputableInPolyTime.snd encUnary (encPair encBool encBits))
  have hp1 : ComputableInPolyTime (fun p : ℕ × Bool × List Bool => coinOutPerm p.2.2)
      (encSchemeCoinsArg Bool encBool) encBool :=
    ComputableInPolyTime.bitsGetDWithInput hc (.const 1) false
  have houtLab : ∀ (col : (ℕ × Bool × List Bool) → Bool),
      ComputableInPolyTime col (encSchemeCoinsArg Bool encBool) encBool →
      ComputableInPolyTime (fun p => outLabel p.1 p.2.2 (col p))
        (encSchemeCoinsArg Bool encBool) encBits :=
    fun col hcol => ComputableInPolyTime.bitsAppend (coinOutKey_polyTime hk hc hcol)
      (ComputableInPolyTime.bitsCons hcol (.const []))
  have hp := (houtLab _ hp1).prod (houtLab _ (ComputableInPolyTime.bool_not.comp hp1))
  have hcons := (ComputableInPolyTime.cons (encPair encBits encBits)).comp
    (hp.prod (.const ([] : List (List Bool × List Bool))))
  convert hcons using 1
  funext ⟨_, _, _⟩
  rfl

/-- Parity-decoded `baseGateScheme` fails `aut` unconditionally with advantage `1`: flipping the
evaluated output word produces a valid forgery under `parityDecode`. -/
theorem baseGateScheme_flip_aut_one (k : ℕ) :
    autAdvantage baseGateScheme k
      ⟨fun _ => pure (⟨false, [false]⟩, ()),
       fun _ view => pure ((baseGateEval view.fn view.input).map (!·))⟩ = 1 := by
  have hexp : ProbComp.eval (autExperiment baseGateScheme k
      ⟨fun _ => pure (⟨false, [false]⟩, ()),
       fun _ view => pure ((baseGateEval view.fn view.input).map (!·))⟩) = PMF.pure true := by
    have hvalid : ([false] : List Bool).length = baseGateScheme.inLen false := rfl
    simp only [autExperiment, ProbComp.eval_bind, ProbComp.eval_pure, PMF.pure_bind,
      hvalid, ↓reduceIte]
    rw [← PMF.bind_const (ProbComp.eval (baseGateScheme.garble k false)) (PMF.pure true)]
    refine PMF.bind_congr_on_support _ _ _ fun g hg => ?_
    obtain ⟨coins, _, rfl⟩ := baseGateScheme.mem_support_eval_garble_iff.mp hg
    have hev := eval_baseGate_eq k false coins [false] rfl
    have hlen : (baseGateEval (baseGateFn k false coins)
        (baseGateEncode (baseGateEncInfo k coins) [false])).length = k + 2 := by
      rw [hev, length_outLabel]
    have hne : ((baseGateEval (baseGateFn k false coins)
        (baseGateEncode (baseGateEncInfo k coins) [false])).map (!·)) ≠
        baseGateEval (baseGateFn k false coins)
          (baseGateEncode (baseGateEncInfo k coins) [false]) := by
      intro heq
      have h0 := congrArg (fun l => l.getD 0 false) heq
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_eq_getElem (by omega : 0 < _)] at h0
      cases (baseGateEval (baseGateFn k false coins)
        (baseGateEncode (baseGateEncInfo k coins) [false]))[0] <;> simp at h0
    have hne_empty : ((baseGateEval (baseGateFn k false coins)
        (baseGateEncode (baseGateEncInfo k coins) [false])).map (!·)).isEmpty = false := by
      rw [Bool.eq_false_iff, ne_eq, List.isEmpty_iff, ← List.length_eq_zero_iff, List.length_map,
        hlen]
      omega
    simp [baseGateScheme, parityDecode, hne_empty, bne_iff_ne.mpr hne]
  simp [autAdvantage, Experiment.succProbability, Game.succProbability, hexp]

/-! ### Coin tuple equivalence for `tokenGateScheme` security proofs -/

private abbrev GateCoins (k : ℕ) :=
  Bool × Bool × BitString (k + 1) × BitString (k + 1) × BitString (k + 1) × BitString (k + 1)

private def packCoins (k : ℕ) (c : GateCoins k) : BitString (baseGateCoinLen k) :=
  fun i =>
    if h0 : i.val = 0 then c.1
    else if h1 : i.val = 1 then c.2.1
    else if h2 : i.val < 2 + (k + 1) then c.2.2.1 ⟨i.val - 2, by omega⟩
    else if h3 : i.val < 2 + 2 * (k + 1) then c.2.2.2.1 ⟨i.val - (2 + (k + 1)), by omega⟩
    else if h4 : i.val < 2 + 3 * (k + 1) then c.2.2.2.2.1 ⟨i.val - (2 + 2 * (k + 1)), by omega⟩
    else c.2.2.2.2.2 ⟨i.val - (2 + 3 * (k + 1)), by
      have := i.isLt; simp [baseGateCoinLen] at this; omega⟩

private def unpackCoins (k : ℕ) (w : BitString (baseGateCoinLen k)) : GateCoins k :=
  (w ⟨0, by simp [baseGateCoinLen]⟩,
   w ⟨1, by simp [baseGateCoinLen]; omega⟩,
   fun j => w ⟨2 + j.val, by have := j.isLt; simp [baseGateCoinLen]; omega⟩,
   fun j => w ⟨2 + (k + 1) + j.val, by have := j.isLt; simp [baseGateCoinLen]; omega⟩,
   fun j => w ⟨2 + 2 * (k + 1) + j.val, by have := j.isLt; simp [baseGateCoinLen]; omega⟩,
   fun j => w ⟨2 + 3 * (k + 1) + j.val, by have := j.isLt; simp [baseGateCoinLen]; omega⟩)

private theorem packCoins_zero {k : ℕ} (c : GateCoins k)
    (h : 0 < baseGateCoinLen k := by simp [baseGateCoinLen]) :
    packCoins k c ⟨0, h⟩ = c.1 := by
  simp [packCoins]

private theorem packCoins_one {k : ℕ} (c : GateCoins k)
    (h : 1 < baseGateCoinLen k := by simp [baseGateCoinLen]; omega) :
    packCoins k c ⟨1, h⟩ = c.2.1 := by
  simp [packCoins]

private theorem packCoins_in0 {k : ℕ} (c : GateCoins k) (j : Fin (k + 1))
    (h : 2 + j.val < baseGateCoinLen k) :
    packCoins k c ⟨2 + j.val, h⟩ = c.2.2.1 j := by
  obtain ⟨jv, hjv⟩ := j
  dsimp [packCoins, baseGateCoinLen] at h ⊢
  split_ifs <;> first | omega | exact congrArg c.2.2.1 (Fin.ext (by dsimp; omega))

private theorem packCoins_in1 {k : ℕ} (c : GateCoins k) (j : Fin (k + 1))
    (h : 2 + (k + 1) + j.val < baseGateCoinLen k) :
    packCoins k c ⟨2 + (k + 1) + j.val, h⟩ = c.2.2.2.1 j := by
  obtain ⟨jv, hjv⟩ := j
  dsimp [packCoins, baseGateCoinLen] at h ⊢
  split_ifs <;> first | omega | exact congrArg c.2.2.2.1 (Fin.ext (by dsimp; omega))

private theorem packCoins_out0 {k : ℕ} (c : GateCoins k) (j : Fin (k + 1))
    (h : 2 + 2 * (k + 1) + j.val < baseGateCoinLen k) :
    packCoins k c ⟨2 + 2 * (k + 1) + j.val, h⟩ = c.2.2.2.2.1 j := by
  obtain ⟨jv, hjv⟩ := j
  dsimp [packCoins, baseGateCoinLen] at h ⊢
  split_ifs <;> first | omega | exact congrArg c.2.2.2.2.1 (Fin.ext (by dsimp; omega))

private theorem packCoins_out1 {k : ℕ} (c : GateCoins k) (j : Fin (k + 1))
    (h : 2 + 3 * (k + 1) + j.val < baseGateCoinLen k) :
    packCoins k c ⟨2 + 3 * (k + 1) + j.val, h⟩ = c.2.2.2.2.2 j := by
  obtain ⟨jv, hjv⟩ := j
  dsimp [packCoins, baseGateCoinLen] at h ⊢
  split_ifs <;> first | omega | exact congrArg c.2.2.2.2.2 (Fin.ext (by dsimp; omega))

private def gateCoinsEquiv (k : ℕ) : GateCoins k ≃ BitString (baseGateCoinLen k) where
  toFun := packCoins k
  invFun := unpackCoins k
  left_inv c := by
    rcases c with ⟨p, q, K0, K1, T0, T1⟩
    refine Prod.ext (packCoins_zero _) (Prod.ext (packCoins_one _)
      (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))))
    · funext j; exact packCoins_in0 _ j (by have := j.isLt; simp [baseGateCoinLen]; omega)
    · funext j; exact packCoins_in1 _ j (by have := j.isLt; simp [baseGateCoinLen]; omega)
    · funext j; exact packCoins_out0 _ j (by have := j.isLt; simp [baseGateCoinLen]; omega)
    · funext j; exact packCoins_out1 _ j (by have := j.isLt; simp [baseGateCoinLen]; omega)
  right_inv w := by
    funext i
    obtain ⟨iv, hiv⟩ := i
    have hlen : iv < 2 + 4 * (k + 1) := by simpa [baseGateCoinLen] using hiv
    simp only [packCoins, unpackCoins]
    split_ifs <;> exact congrArg w (Fin.ext (by dsimp; omega))

private theorem coinInPerm_pack {k : ℕ} (c : GateCoins k) :
    coinInPerm (List.ofFn (packCoins k c)) = c.1 := by
  have hlen : 0 < (List.ofFn (packCoins k c)).length := by
    rw [List.length_ofFn]; simp [baseGateCoinLen]
  rw [coinInPerm, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen, Option.getD_some,
    List.getElem_ofFn]
  exact packCoins_zero c

private theorem coinOutPerm_pack {k : ℕ} (c : GateCoins k) :
    coinOutPerm (List.ofFn (packCoins k c)) = c.2.1 := by
  have hlen : 1 < (List.ofFn (packCoins k c)).length := by
    rw [List.length_ofFn]; simp [baseGateCoinLen]; omega
  rw [coinOutPerm, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen, Option.getD_some,
    List.getElem_ofFn]
  exact packCoins_one c

private theorem coinInKey_pack {k : ℕ} (c : GateCoins k) (col : Bool) :
    coinInKey k (List.ofFn (packCoins k c)) col =
      List.ofFn (if col then c.2.2.2.1 else c.2.2.1) := by
  apply List.ext_getElem (by simp [coinInKey])
  intro i hi1 hi2
  have hi : i < k + 1 := by simpa [coinInKey] using hi1
  have hlen : 2 + (if col then 1 else 0) * (k + 1) + i <
      (List.ofFn (packCoins k c)).length := by
    rw [List.length_ofFn]; simp only [baseGateCoinLen]; cases col <;> (simp; omega)
  have hget : (coinInKey k (List.ofFn (packCoins k c)) col)[i]'hi1 =
      (coinInKey k (List.ofFn (packCoins k c)) col).getD i false := by
    simp [List.getD_eq_getElem?_getD, hi1]
  rw [hget, coinInKey, BitString.getD_listRow hi, List.getD_eq_getElem?_getD, List.getElem?_drop,
    ← Nat.add_assoc, List.getElem?_eq_getElem hlen, Option.getD_some, List.getElem_ofFn,
    List.getElem_ofFn]
  cases col
  · simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_mul]
    exact packCoins_in0 c ⟨i, hi⟩ (by simp [baseGateCoinLen]; omega)
  · simp only [↓reduceIte, Nat.one_mul]
    exact packCoins_in1 c ⟨i, hi⟩ (by simp [baseGateCoinLen]; omega)

private theorem coinOutKey_pack {k : ℕ} (c : GateCoins k) (col : Bool) :
    coinOutKey k (List.ofFn (packCoins k c)) col =
      List.ofFn (if col then c.2.2.2.2.2 else c.2.2.2.2.1) := by
  apply List.ext_getElem (by simp [coinOutKey])
  intro i hi1 hi2
  have hi : i < k + 1 := by simpa [coinOutKey] using hi1
  have hlen : 2 + (if col then 3 else 2) * (k + 1) + i <
      (List.ofFn (packCoins k c)).length := by
    rw [List.length_ofFn]; simp only [baseGateCoinLen]; cases col <;> (simp; omega)
  have hget : (coinOutKey k (List.ofFn (packCoins k c)) col)[i]'hi1 =
      (coinOutKey k (List.ofFn (packCoins k c)) col).getD i false := by
    simp [List.getD_eq_getElem?_getD, hi1]
  rw [hget, coinOutKey, BitString.getD_listRow hi, List.getD_eq_getElem?_getD, List.getElem?_drop,
    ← Nat.add_assoc, List.getElem?_eq_getElem hlen, Option.getD_some, List.getElem_ofFn,
    List.getElem_ofFn]
  cases col
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact packCoins_out0 c ⟨i, hi⟩ (by simp [baseGateCoinLen]; omega)
  · simp only [↓reduceIte]
    exact packCoins_out1 c ⟨i, hi⟩ (by simp [baseGateCoinLen]; omega)

/-- One-time-pad involution masking the inactive input key `K_{!(x ^^ p)}` with the inactive
output key `T_{!(x ^^ b) ^^ q}` so that `(F, X)` is completely independent of
`T_{!(x ^^ b) ^^ q}`. -/
private def otpMaskInactiveEquiv (k : ℕ) (b x : Bool) : GateCoins k ≃ GateCoins k where
  toFun c :=
    let p := c.1; let q := c.2.1; let K0 := c.2.2.1; let K1 := c.2.2.2.1
    let T0 := c.2.2.2.2.1; let T1 := c.2.2.2.2.2
    let colIn := x ^^ p
    let colOut := (x ^^ b) ^^ q
    let T_inact := if !colOut then T1 else T0
    if colIn then (p, q, K0 + T_inact, K1, T0, T1)
    else (p, q, K0, K1 + T_inact, T0, T1)
  invFun c :=
    let p := c.1; let q := c.2.1; let K0 := c.2.2.1; let K1 := c.2.2.2.1
    let T0 := c.2.2.2.2.1; let T1 := c.2.2.2.2.2
    let colIn := x ^^ p
    let colOut := (x ^^ b) ^^ q
    let T_inact := if !colOut then T1 else T0
    if colIn then (p, q, K0 + T_inact, K1, T0, T1)
    else (p, q, K0, K1 + T_inact, T0, T1)
  left_inv c := by
    rcases c with ⟨p, q, K0, K1, T0, T1⟩
    dsimp only
    by_cases h : x ^^ p <;> simp [h, add_assoc]
  right_inv c := by
    rcases c with ⟨p, q, K0, K1, T0, T1⟩
    dsimp only
    by_cases h : x ^^ p <;> simp [h, add_assoc]

private theorem eval_sampleList_gateCoins (k : ℕ) :
    ProbComp.eval (BitString.sampleList (baseGateCoinLen k)) =
      (PMF.uniformOfFintype (GateCoins k)).map (fun c => List.ofFn (packCoins k c)) := by
  rw [BitString.eval_sampleList, BitString.uniformList,
    ← PMF.uniformOfFintype_map_equiv (gateCoinsEquiv k), PMF.map_comp]
  rfl

private theorem zipWith_xor_ofFn {n : ℕ} (a b : BitString n) :
    List.zipWith xor (List.ofFn a) (List.ofFn b) = List.ofFn (a + b) := by
  apply List.ext_getElem (by simp)
  intro i hi1 hi2
  simp [Pi.add_apply, Bool.add_eq_xor]

private theorem zipWith_xor_append {a1 a2 b1 b2 : List Bool} (ha : a1.length = b1.length) :
    List.zipWith xor (a1 ++ a2) (b1 ++ b2) = List.zipWith xor a1 b1 ++ List.zipWith xor a2 b2 := by
  induction a1 generalizing b1 with
  | nil =>
    simp only [List.length_nil] at ha
    have hb : b1 = [] := List.eq_nil_iff_length_eq_zero.mpr ha.symm
    subst hb; rfl
  | cons x xs ih =>
    cases b1 with
    | nil => simp at ha
    | cons y ys =>
      simp only [List.cons_append, List.zipWith_cons_cons]
      congr 1
      exact ih (by simpa using ha)

private def gateSplitOut {k : ℕ} (b x0 p q_out : Bool)
    (K0 K1 T_act T_inact : BitString (k + 1)) : GateCoins k :=
  (p, q_out, K0, K1,
    if (x0 ^^ b) ^^ q_out then T_inact else T_act,
    if (x0 ^^ b) ^^ q_out then T_act else T_inact)

private def gateSplitEquiv (k : ℕ) (b x0 : Bool) :
    (Bool × Bool × BitString (k + 1) × BitString (k + 1) × BitString (k + 1)) ×
      BitString (k + 1) ≃ GateCoins k where
  toFun x := gateSplitOut b x0 x.1.1 x.1.2.1 x.1.2.2.1 x.1.2.2.2.1 x.1.2.2.2.2 x.2
  invFun c := ((c.1, c.2.1, c.2.2.1, c.2.2.2.1,
    if (x0 ^^ b) ^^ c.2.1 then c.2.2.2.2.2 else c.2.2.2.2.1),
    if (x0 ^^ b) ^^ c.2.1 then c.2.2.2.2.1 else c.2.2.2.2.2)
  left_inv x := by
    rcases x with ⟨⟨p, q_out, K0, K1, Ta⟩, Ti⟩
    dsimp only; by_cases h : ((x0 ^^ b) ^^ q_out) = true <;> simp [gateSplitOut, h]
  right_inv c := by
    rcases c with ⟨p, q_out, K0, K1, T0, T1⟩
    dsimp only; by_cases h : ((x0 ^^ b) ^^ q_out) = true <;> simp [gateSplitOut, h]

private theorem obvView_otpMask_split_indep (k : ℕ) (b x0 p q_out : Bool)
    (K0 K1 T_act T_inact T_inact' : BitString (k + 1)) (input : List Bool)
    (hx0 : input.headD false = x0) :
    let equiv := otpMaskInactiveEquiv k b x0
    let c1 : GateCoins k := gateSplitOut b x0 p q_out K0 K1 T_act T_inact
    let c2 : GateCoins k := gateSplitOut b x0 p q_out K0 K1 T_act T_inact'
    let g1 := tokenGateScheme.gb k b (List.ofFn (packCoins k (equiv c1)))
    let g2 := tokenGateScheme.gb k b (List.ofFn (packCoins k (equiv c2)))
    ObvView.mk g1.fn (tokenGateScheme.encode g1.encInfo input) =
      ObvView.mk g2.fn (tokenGateScheme.encode g2.encInfo input) := by
  intro equiv c1 c2 g1 g2
  have hc1 : ∀ col : Bool, (if col then c1.2.2.2.2.2 else c1.2.2.2.2.1) =
      if col = ((x0 ^^ b) ^^ q_out) then T_act else T_inact := by
    intro col; cases col <;> cases h : (x0 ^^ b) ^^ q_out <;> simp [c1, gateSplitOut, h]
  have hc2 : ∀ col : Bool, (if col then c2.2.2.2.2.2 else c2.2.2.2.2.1) =
      if col = ((x0 ^^ b) ^^ q_out) then T_act else T_inact' := by
    intro col; cases col <;> cases h : (x0 ^^ b) ^^ q_out <;> simp [c2, gateSplitOut, h]
  have hfn_eq : baseGateFn k b (List.ofFn (packCoins k (equiv c1))) =
      baseGateFn k b (List.ofFn (packCoins k (equiv c2))) := by
    have hperm_c1 : (equiv c1).1 = p ∧ (equiv c1).2.1 = q_out := by
      dsimp [equiv, otpMaskInactiveEquiv, c1, gateSplitOut]; split_ifs <;> exact ⟨rfl, rfl⟩
    have hperm_c2 : (equiv c2).1 = p ∧ (equiv c2).2.1 = q_out := by
      dsimp [equiv, otpMaskInactiveEquiv, c2, gateSplitOut]; split_ifs <;> exact ⟨rfl, rfl⟩
    have hperm_in : coinInPerm (List.ofFn (packCoins k (equiv c1))) = p :=
      (coinInPerm_pack _).trans hperm_c1.1
    have hperm_in' : coinInPerm (List.ofFn (packCoins k (equiv c2))) = p :=
      (coinInPerm_pack _).trans hperm_c2.1
    have hperm_out : coinOutPerm (List.ofFn (packCoins k (equiv c1))) = q_out :=
      (coinOutPerm_pack _).trans hperm_c1.2
    have hperm_out' : coinOutPerm (List.ofFn (packCoins k (equiv c2))) = q_out :=
      (coinOutPerm_pack _).trans hperm_c2.2
    have hrow : ∀ colIn : Bool,
        List.zipWith xor (inLabel k (List.ofFn (packCoins k (equiv c1))) colIn)
          (outLabel k (List.ofFn (packCoins k (equiv c1)))
            ((if colIn then !p else p) ^^ b ^^ q_out)) =
        List.zipWith xor (inLabel k (List.ofFn (packCoins k (equiv c2))) colIn)
          (outLabel k (List.ofFn (packCoins k (equiv c2)))
            ((if colIn then !p else p) ^^ b ^^ q_out)) := by
      intro colIn
      simp only [inLabel, outLabel, coinInKey_pack, coinOutKey_pack]
      rw [zipWith_xor_append (by simp), zipWith_xor_append (by simp)]
      congr 1
      rw [zipWith_xor_ofFn, zipWith_xor_ofFn]
      congr 1
      funext i
      by_cases hact : colIn = (x0 ^^ p)
      · have h_in1 : (if colIn then (equiv c1).2.2.2.1 else (equiv c1).2.2.1) =
            if colIn then K1 else K0 := by
          dsimp [equiv, otpMaskInactiveEquiv, c1, gateSplitOut]
          cases hxp : x0 ^^ p <;> cases hcol : colIn <;> simp_all
        have h_in2 : (if colIn then (equiv c2).2.2.2.1 else (equiv c2).2.2.1) =
            if colIn then K1 else K0 := by
          dsimp [equiv, otpMaskInactiveEquiv, c2, gateSplitOut]
          cases hxp : x0 ^^ p <;> cases hcol : colIn <;> simp_all
        have hcol_out : ((if colIn then !p else p) ^^ b ^^ q_out) = ((x0 ^^ b) ^^ q_out) := by
          rw [hact]
          cases x0 <;> cases p <;> cases b <;> cases q_out <;> rfl
        rw [h_in1, h_in2, hcol_out]
        have ho1' : (if (x0 ^^ b) ^^ q_out then c1.2.2.2.2.2 else c1.2.2.2.2.1) = T_act := by
          simpa using hc1 ((x0 ^^ b) ^^ q_out)
        have ho2' : (if (x0 ^^ b) ^^ q_out then c2.2.2.2.2.2 else c2.2.2.2.2.1) = T_act := by
          simpa using hc2 ((x0 ^^ b) ^^ q_out)
        have heq1 : (equiv c1).2.2.2.2 = c1.2.2.2.2 := by
          dsimp [equiv, otpMaskInactiveEquiv]; split_ifs <;> rfl
        have heq2 : (equiv c2).2.2.2.2 = c2.2.2.2.2 := by
          dsimp [equiv, otpMaskInactiveEquiv]; split_ifs <;> rfl
        rw [heq1, heq2, ho1', ho2']
      · have hcol : colIn = !(x0 ^^ p) := by
          cases colIn <;> cases h : x0 ^^ p <;> simp_all
        have h_in1 : (if colIn then (equiv c1).2.2.2.1 else (equiv c1).2.2.1) =
            (if colIn then K1 else K0) + T_inact := by
          rw [hcol]
          cases x0 <;> cases p <;> cases b <;> cases q_out <;>
            simp [equiv, otpMaskInactiveEquiv, c1, gateSplitOut]
        have h_in2 : (if colIn then (equiv c2).2.2.2.1 else (equiv c2).2.2.1) =
            (if colIn then K1 else K0) + T_inact' := by
          rw [hcol]
          cases x0 <;> cases p <;> cases b <;> cases q_out <;>
            simp [equiv, otpMaskInactiveEquiv, c2, gateSplitOut]
        have hcol_out : ((if colIn then !p else p) ^^ b ^^ q_out) = !((x0 ^^ b) ^^ q_out) := by
          rw [hcol]
          cases x0 <;> cases p <;> cases b <;> cases q_out <;> rfl
        rw [h_in1, h_in2, hcol_out]
        have ho1 : (if !((x0 ^^ b) ^^ q_out) then (equiv c1).2.2.2.2.2
            else (equiv c1).2.2.2.2.1) = T_inact := by
          cases x0 <;> cases p <;> cases b <;> cases q_out <;>
            simp [equiv, otpMaskInactiveEquiv, c1, gateSplitOut]
        have ho2 : (if !((x0 ^^ b) ^^ q_out) then (equiv c2).2.2.2.2.2
            else (equiv c2).2.2.2.2.1) = T_inact' := by
          cases x0 <;> cases p <;> cases b <;> cases q_out <;>
            simp [equiv, otpMaskInactiveEquiv, c2, gateSplitOut]
        rw [ho1, ho2, Pi.add_apply, Pi.add_apply, Pi.add_apply, Pi.add_apply,
          add_assoc, add_assoc]
        cases (if colIn then K1 else K0) i <;> cases T_inact i <;> cases T_inact' i <;> rfl
    simp only [baseGateFn, hperm_in, hperm_in', hperm_out, hperm_out']
    congr 1
    · exact hrow false
    · exact hrow true
  have henc_eq :
      baseGateEncode (baseGateEncInfo k (List.ofFn (packCoins k (equiv c1)))) input =
      baseGateEncode (baseGateEncInfo k (List.ofFn (packCoins k (equiv c2)))) input := by
    have hlen1 : (baseGateEncInfo k (List.ofFn (packCoins k (equiv c1)))).length / 2 = k + 2 := by
      simp [baseGateEncInfo, length_inLabel]; omega
    have hlen2 : (baseGateEncInfo k (List.ofFn (packCoins k (equiv c2)))).length / 2 = k + 2 := by
      simp [baseGateEncInfo, length_inLabel]; omega
    have hperm1 : coinInPerm (List.ofFn (packCoins k (equiv c1))) = p := by
      rw [coinInPerm_pack]
      dsimp [equiv, otpMaskInactiveEquiv]; split_ifs <;> rfl
    have hperm2 : coinInPerm (List.ofFn (packCoins k (equiv c2))) = p := by
      rw [coinInPerm_pack]
      dsimp [equiv, otpMaskInactiveEquiv]; split_ifs <;> rfl
    have hin_act : coinInKey k (List.ofFn (packCoins k (equiv c1))) (x0 ^^ p) =
        coinInKey k (List.ofFn (packCoins k (equiv c2))) (x0 ^^ p) := by
      rw [coinInKey_pack, coinInKey_pack]
      congr 1
      cases x0 <;> cases p <;>
        dsimp [equiv, otpMaskInactiveEquiv, c1, c2, gateSplitOut]
    rw [baseGateEncode, baseGateEncode, hlen1, hlen2, baseGateEncInfo, baseGateEncInfo,
      hperm1, hperm2, hx0]
    cases hx : x0 <;> cases hp : p <;>
      simp only [Bool.false_eq_true, ↓reduceIte]
    · rw [List.take_left' (by simp [length_inLabel]),
        List.take_left' (by simp [length_inLabel]), inLabel, inLabel]
      congr 1
      simpa [hx, hp] using hin_act
    · rw [List.take_left' (by simp [length_inLabel]),
        List.take_left' (by simp [length_inLabel]), inLabel, inLabel]
      congr 1
      simpa [hx, hp] using hin_act
    · rw [List.drop_left' (by simp [length_inLabel]),
        List.drop_left' (by simp [length_inLabel]), inLabel, inLabel]
      congr 1
      simpa [hx, hp] using hin_act
    · rw [List.drop_left' (by simp [length_inLabel]),
        List.drop_left' (by simp [length_inLabel]), inLabel, inLabel]
      congr 1
      simpa [hx, hp] using hin_act
  dsimp only [g1, g2, tokenGateScheme, Scheme.withTokenDecoding, baseGateScheme]
  exact congrArg₂ ObvView.mk hfn_eq henc_eq

/-- Unconditional **authenticity** of `tokenGateScheme`: for every security parameter `k` and
every adversary `A`, `autAdvantage tokenGateScheme k A ≤ 2^(-(k + 1))`. -/
theorem tokenGateScheme_autAdvantage_le (k : ℕ) {σ : Type} (A : AutAdversary Bool σ) :
    autAdvantage tokenGateScheme k A ≤ ((2 : ℝ≥0) ^ (k + 1))⁻¹ := by
  rw [autAdvantage, autExperiment]
  refine Experiment.succProbability_bind_le_of_support _ _ fun ⟨q, st⟩ _ => ?_
  by_cases hlen : q.input.length = tokenGateScheme.inLen q.fn
  · simp only [hlen, ↓reduceIte]
    have hx1 : q.input.length = 1 := hlen
    let x0 := q.input.headD false
    let b := q.fn
    let equiv := (otpMaskInactiveEquiv k b x0)
    have hgarb : ProbComp.eval (tokenGateScheme.garble k b) =
        (PMF.uniformOfFintype (GateCoins k)).map
          (fun c => tokenGateScheme.gb k b (List.ofFn (packCoins k (equiv c)))) := by
      rw [Scheme.eval_garble, BitString.uniformList]
      change (PMF.map List.ofFn (PMF.uniformOfFintype (BitString (baseGateCoinLen k)))).map
        (tokenGateScheme.gb k b) = _
      conv_lhs =>
        rw [← PMF.uniformOfFintype_map_equiv (gateCoinsEquiv k),
          ← PMF.uniformOfFintype_map_equiv equiv, PMF.map_comp, PMF.map_comp, PMF.map_comp]
      rfl
    rw [Experiment.succProbability]
    simp only [ProbComp.eval_bind, ProbComp.eval_pure]
    rw [hgarb, PMF.bind_map]
    -- Split `GateCoins k` into `(p, q, K0, K1, T_act, T_inact)` so `(F, X)` ignores `T_inact`
    let viewOf (c : GateCoins k) : ObvView :=
      let g := tokenGateScheme.gb k b (List.ofFn (packCoins k (equiv c)))
      ⟨g.fn, tokenGateScheme.encode g.encInfo q.input⟩
    have hview_indep : ∀ (p q_out : Bool) (K0 K1 T_act T_inact T_inact' : BitString (k + 1)),
        viewOf (gateSplitOut b x0 p q_out K0 K1 T_act T_inact) =
          viewOf (gateSplitOut b x0 p q_out K0 K1 T_act T_inact') :=
      fun p q_out K0 K1 T_act T_inact T_inact' =>
        obvView_otpMask_split_indep k b x0 p q_out K0 K1 T_act T_inact T_inact' q.input rfl
    let splitOut := @gateSplitOut k b x0
    let splitEquiv := gateSplitEquiv k b x0
    rw [← PMF.uniformOfFintype_map_equiv splitEquiv, ← PMF.uniformOfFintype_prod,
      PMF.bind_map, PMF.bind_bind]
    rw [← Game.advantage_pure_false]
    conv_lhs =>
      arg 2
      rw [← PMF.bind_const
        (PMF.uniformOfFintype
          (Bool × Bool × BitString (k + 1) × BitString (k + 1) × BitString (k + 1)))
        (PMF.pure false)]
    refine Game.advantage_bind_le_of_support _ _ _ fun pre _ => ?_
    rw [Game.advantage_pure_false]
    simp only [PMF.bind_map, Function.comp_def]
    rcases pre with ⟨p, q_out, K0, K1, T_act⟩
    let v := viewOf (splitOut p q_out K0 K1 T_act 0)
    have hv_eq : ∀ T_inact : BitString (k + 1), viewOf (splitOut p q_out K0 K1 T_act T_inact) = v :=
      fun T_inact => hview_indep p q_out K0 K1 T_act T_inact 0
    have hswap : ((PMF.uniformOfFintype (BitString (k + 1))).bind fun T_inact =>
        (ProbComp.eval (A.guess st (viewOf (splitOut p q_out K0 K1 T_act T_inact)))).bind
          fun forged => PMF.pure ((forged != tokenGateScheme.evalGarbled
            (viewOf (splitOut p q_out K0 K1 T_act T_inact)).fn
            (viewOf (splitOut p q_out K0 K1 T_act T_inact)).input) &&
            (tokenGateScheme.decode (tokenGateScheme.gb k b (List.ofFn (packCoins k
              (equiv (splitOut p q_out K0 K1 T_act T_inact))))).decInfo forged).isSome)) =
        (ProbComp.eval (A.guess st v)).bind fun forged =>
          (PMF.uniformOfFintype (BitString (k + 1))).bind fun T_inact =>
            PMF.pure ((forged != tokenGateScheme.evalGarbled v.fn v.input) &&
              (tokenGateScheme.decode (tokenGateScheme.gb k b (List.ofFn (packCoins k
                (equiv (splitOut p q_out K0 K1 T_act T_inact))))).decInfo forged).isSome) := by
      simp_rw [hv_eq]
      exact PMF.bind_comm _ _ _
    change Game.succProbability ((PMF.uniformOfFintype (BitString (k + 1))).bind fun T_inact =>
        (ProbComp.eval (A.guess st (viewOf (splitOut p q_out K0 K1 T_act T_inact)))).bind
          fun forged => PMF.pure ((forged != tokenGateScheme.evalGarbled
            (viewOf (splitOut p q_out K0 K1 T_act T_inact)).fn
            (viewOf (splitOut p q_out K0 K1 T_act T_inact)).input) &&
            (tokenGateScheme.decode (tokenGateScheme.gb k b (List.ofFn (packCoins k
              (equiv (splitOut p q_out K0 K1 T_act T_inact))))).decInfo forged).isSome)) ≤ _
    rw [hswap]
    rw [← Game.advantage_pure_false]
    conv_lhs => arg 2; rw [← PMF.bind_const (ProbComp.eval (A.guess st v)) (PMF.pure false)]
    refine Game.advantage_bind_le_of_support _ _ _ fun forged _ => ?_
    rw [Game.advantage_pure_false]
    let target : BitString (k + 1) := BitString.ofList (k + 1) forged
    have hhit : ∀ T_inact : BitString (k + 1), T_inact ≠ target →
        ((forged != tokenGateScheme.evalGarbled v.fn v.input) &&
          (tokenGateScheme.decode (tokenGateScheme.gb k b (List.ofFn (packCoins k
            (equiv (splitOut p q_out K0 K1 T_act T_inact))))).decInfo forged).isSome) = false := by
      intro T_inact hne_T
      by_cases hev_ne : forged = tokenGateScheme.evalGarbled v.fn v.input
      · simp [hev_ne]
      · have hbne : (forged != tokenGateScheme.evalGarbled v.fn v.input) = true :=
          bne_iff_ne.mpr hev_ne
        rw [hbne, Bool.true_and]
        by_contra hsome
        have hsome' : (tokenGateScheme.decode (tokenGateScheme.gb k b (List.ofFn (packCoins k
            (equiv (splitOut p q_out K0 K1 T_act T_inact))))).decInfo forged).isSome =
            true := by
          cases hdec : (tokenGateScheme.decode (tokenGateScheme.gb k b (List.ofFn (packCoins k
              (equiv (splitOut p q_out K0 K1 T_act T_inact))))).decInfo forged).isSome <;>
            simp_all
        obtain ⟨y', hy'⟩ := Option.isSome_iff_exists.mp hsome'
        let coins' := List.ofFn (packCoins k (equiv (splitOut p q_out K0 K1 T_act T_inact)))
        have hc' : coins'.length = baseGateScheme.coinLen k 1 1 1 := by
          dsimp only [coins']
          rw [List.length_ofFn]
          rfl
        have hev_ne' : forged ≠ baseGateScheme.evalGarbled (baseGateScheme.gb k b coins').fn
            (baseGateScheme.encode (baseGateScheme.gb k b coins').encInfo q.input) := by
          rw [← hv_eq T_inact] at hev_ne
          simpa [coins', viewOf, tokenGateScheme, Scheme.withTokenDecoding] using hev_ne
        have hwit := decode_withTokenDecoding_forgery_witness baseGateScheme_wellTyped
          tokenGateSpec_sound hc' hx1 hev_ne' hy'
        obtain ⟨o, ho_ne, ho_tag⟩ := hwit
        dsimp only [baseGateScheme, tokenGateSpec] at o ho_ne ho_tag
        have ho0 : o = 0 := Fin.eq_zero o
        subst ho0
        have hev_eq := eval_baseGate_eq k b coins' q.input hx1
        have hrow_eq : BitString.listRow (k + 2) 0 forged = forged := by
          obtain ⟨_, h0, hpos⟩ := (decode_withTokenDecoding_eq_some_iff tokenGateSpec_sound hc'
            forged y').mp hy'
          obtain ⟨hf_len, _⟩ := hpos (by simp [baseGateScheme])
          simp [BitString.listRow, baseGateScheme, tokenGateSpec, hf_len]
        simp only [List.getD_eq_getElem?_getD, Fin.val_zero,
          List.getElem?_cons_zero, Option.getD_some, id_eq] at ho_ne ho_tag
        rw [hrow_eq] at ho_ne ho_tag
        have hx0_def : q.input.headD false = x0 := rfl
        rw [hx0_def] at ho_ne
        have hq_eq : coinOutPerm coins' = q_out := by
          rw [coinOutPerm_pack]
          dsimp [equiv, otpMaskInactiveEquiv, splitOut, gateSplitOut]
          split_ifs <;> rfl
        rw [hq_eq] at ho_ne ho_tag
        have hforged_inact : forged = outLabel k coins' (!((x0 ^^ b) ^^ q_out)) := by
          cases hxb : x0 ^^ b
          · simp only [hxb, Bool.false_eq_true, ↓reduceIte, Bool.false_xor] at ho_ne ⊢
            rcases ho_tag with h0 | h1
            · exact absurd h0 ho_ne
            · exact h1
          · simp only [hxb, ↓reduceIte, Bool.true_xor, Bool.not_not] at ho_ne ⊢
            rcases ho_tag with h0 | h1
            · exact h0
            · exact absurd h1 ho_ne
        have hkey_take : BitString.ofList (k + 1) forged =
            BitString.ofList (k + 1) (coinOutKey k coins' (!((x0 ^^ b) ^^ q_out))) := by
          rw [hforged_inact]
          simp only [outLabel]
          have hle : k + 1 ≤ (coinOutKey k coins' (!((x0 ^^ b) ^^ q_out))).length := by
            simp [coinOutKey]
          exact BitString.ofList_append_of_le hle _
        have hkey_T : BitString.ofList (k + 1) (coinOutKey k coins' (!((x0 ^^ b) ^^ q_out))) =
            T_inact := by
          rw [coinOutKey_pack]
          have hT_eq : (if !((x0 ^^ b) ^^ q_out) then
              (equiv (splitOut p q_out K0 K1 T_act T_inact)).2.2.2.2.2
              else (equiv (splitOut p q_out K0 K1 T_act T_inact)).2.2.2.2.1) = T_inact := by
            dsimp only [equiv, splitOut]
            generalize x0 = x0'
            generalize b = b'
            cases x0' <;> cases b' <;> cases p <;> cases q_out <;>
              simp [otpMaskInactiveEquiv, gateSplitOut]
          rw [hT_eq, BitString.ofList_ofFn]
        exact hne_T (hkey_T.symm.trans hkey_take.symm)
    -- Now bound success probability by `(Fintype.card (BitString (k + 1)))⁻¹ = (2^(k + 1))⁻¹`
    have hle_single : Game.succProbability ((PMF.uniformOfFintype (BitString (k + 1))).bind
        fun T_inact => PMF.pure ((forged != tokenGateScheme.evalGarbled v.fn v.input) &&
          (tokenGateScheme.decode (tokenGateScheme.gb k b (List.ofFn (packCoins k
            (equiv (splitOut p q_out K0 K1 T_act T_inact))))).decInfo forged).isSome)) ≤
        (Fintype.card (BitString (k + 1)) : ℝ≥0)⁻¹ := by
      have hadv := Game.advantage_bind_uniformOfFintype_of_ne_le target
        (fun T_inact => PMF.pure ((forged != tokenGateScheme.evalGarbled v.fn v.input) &&
          (tokenGateScheme.decode (tokenGateScheme.gb k b (List.ofFn (packCoins k
            (equiv (splitOut p q_out K0 K1 T_act T_inact))))).decInfo forged).isSome))
        (PMF.pure false) (fun T hne => by simp [hhit T hne])
      rwa [Game.advantage_pure_false] at hadv
    simpa [Experiment.succProbability, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] using
      hle_single
  · simp only [hlen, ↓reduceIte]
    simp [Experiment.succProbability, Game.succProbability]

/-- Uniform strict PPT obliviousness simulator for `baseGateScheme` / `tokenGateScheme`:
samples uniform `(c0, c1)` and three uniform `(k + 1)`-bit strings for `X`, `row₀`, `row₁`. -/
noncomputable def tokenGateObvSim (k : ℕ) (_ : Unit) : ProbComp ObvView := do
  let c0 ← ProbComp.uniform Bool
  let c1 ← ProbComp.uniform Bool
  let kX ← BitString.sampleList (k + 1)
  let kR0 ← BitString.sampleList (k + 1)
  let kR1 ← BitString.sampleList (k + 1)
  pure ⟨(kR0 ++ [c1]) ++ (kR1 ++ [c1]), kX ++ [c0]⟩

private theorem tokenGateObvSim_isPPT :
    IsPPTOn (encObvSimIn Unit encUnit) OutSim.encObvView
      (fun (k, φ) => tokenGateObvSim k φ) := by
  unfold tokenGateObvSim
  have hbool : IsPPTOn (encObvSimIn Unit encUnit) encBool (fun _ => ProbComp.uniform Bool) :=
    Probability.isPPTOn_uniform_bool _
  have hkeys : IsPPTOn (encObvSimIn Unit encUnit) encBits
      (fun (k, _) => BitString.sampleList (k + 1)) := by
    refine Probability.isPPTOn_sampleList.preprocess ?_
    exact ComputableInPolyTime.unary_add' (ComputableInPolyTime.fst _ _) (.const 1)
  refine hbool.bind_with ?_
  refine (Probability.isPPTOn_uniform_bool _).bind_with ?_
  refine (hkeys.preprocess (ComputableInPolyTime.fst _ _ |>.comp
    (ComputableInPolyTime.fst _ _))).bind_with ?_
  refine (hkeys.preprocess (ComputableInPolyTime.fst _ _ |>.comp
    (ComputableInPolyTime.fst _ _ |>.comp (ComputableInPolyTime.fst _ _)))).bind_with ?_
  refine (hkeys.preprocess (ComputableInPolyTime.fst _ _ |>.comp
    (ComputableInPolyTime.fst _ _ |>.comp (ComputableInPolyTime.fst _ _ |>.comp
      (ComputableInPolyTime.fst _ _))))).bind_with ?_
  refine ComputableInPolyTime.isPPTOn ?_
  let EG := encPair (encPair (encPair (encPair (encPair (encObvSimIn Unit encUnit) encBool)
    encBool) encBits) encBits) encBits
  have hc0 : ComputableInPolyTime (fun p => p.1.1.1.1.2) EG encBool := by fun_prop
  have hc1 : ComputableInPolyTime (fun p => p.1.1.1.2) EG encBool := by fun_prop
  have hkX : ComputableInPolyTime (fun p => p.1.1.2) EG encBits := by fun_prop
  have hkR0 : ComputableInPolyTime (fun p => p.1.2) EG encBits := by fun_prop
  have hkR1 : ComputableInPolyTime (fun p => p.2) EG encBits := by fun_prop
  have hF := ComputableInPolyTime.bitsAppend
    (ComputableInPolyTime.bitsAppend hkR0 (ComputableInPolyTime.bitsCons hc1 (.const [])))
    (ComputableInPolyTime.bitsAppend hkR1 (ComputableInPolyTime.bitsCons hc1 (.const [])))
  have hX := ComputableInPolyTime.bitsAppend hkX (ComputableInPolyTime.bitsCons hc0 (.const []))
  exact (hF.prod hX).of_enc_eq fun _ => rfl

/-- Exact distributional equivalence of `tokenGateScheme.obvView k q` and `tokenGateObvSim k ()`
on every valid query `q.input.length = 1`. -/
theorem eval_obvView_tokenGateScheme (k : ℕ) (q : Query Bool) (hx : q.input.length = 1) :
    ProbComp.eval (tokenGateScheme.obvView k q) = ProbComp.eval (tokenGateObvSim k ()) := by
  have _ := hx
  let x0 := q.input.headD false
  let b := q.fn
  have hadd_cancel : ∀ a b : Bool, a + (b + a) = b := fun a b => by cases a <;> cases b <;> rfl
  let viewEquiv : GateCoins k ≃
      (Bool × Bool × BitString (k + 1) × BitString (k + 1) × BitString (k + 1)) ×
        BitString (k + 1) :=
    { toFun c :=
        let p := c.1; let q_out := c.2.1; let K0 := c.2.2.1; let K1 := c.2.2.2.1
        let T0 := c.2.2.2.2.1; let T1 := c.2.2.2.2.2
        let c0 := x0 ^^ p
        let c1 := p ^^ b ^^ q_out
        let kX := if c0 then K1 else K0
        let kR0 := K0 + (if c1 then T1 else T0)
        let kR1 := K1 + (if !c1 then T1 else T0)
        let free := if c0 then K0 else K1
        ((c0, c1, kX, kR0, kR1), free)
      invFun s :=
        let c0 := s.1.1; let c1 := s.1.2.1
        let kX := s.1.2.2.1; let kR0 := s.1.2.2.2.1; let kR1 := s.1.2.2.2.2
        let free := s.2
        let p := c0 ^^ x0
        let q_out := c1 ^^ p ^^ b
        let K0 := if c0 then free else kX
        let K1 := if c0 then kX else free
        let Tc1 := kR0 + K0
        let Tnc1 := kR1 + K1
        let T0 := if c1 then Tnc1 else Tc1
        let T1 := if c1 then Tc1 else Tnc1
        (p, q_out, K0, K1, T0, T1)
      left_inv c := by
        rcases c with ⟨p, q_out, K0, K1, T0, T1⟩
        dsimp only
        have hx0p : ((x0 ^^ p) ^^ x0) = p := by cases x0 <;> cases p <;> rfl
        have hq' : ((p ^^ b ^^ q_out) ^^ ((x0 ^^ p) ^^ x0) ^^ b) = q_out := by
          cases x0 <;> cases p <;> cases b <;> cases q_out <;> rfl
        refine Prod.ext hx0p (Prod.ext hq' (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))))
        · funext i; cases x0 <;> cases p <;> simp
        · funext i; cases x0 <;> cases p <;> simp
        · funext i
          cases hq : p ^^ b ^^ q_out <;> cases hp : x0 ^^ p <;>
            (simp only [↓reduceIte, Bool.false_eq_true, Bool.not_true, Pi.add_apply];
              first | cases K0 i <;> cases T0 i <;> rfl | cases K1 i <;> cases T0 i <;> rfl)
        · funext i
          cases hq : p ^^ b ^^ q_out <;> cases hp : x0 ^^ p <;>
            (simp only [↓reduceIte, Bool.false_eq_true, Bool.not_false, Pi.add_apply];
              first | cases K0 i <;> cases T1 i <;> rfl | cases K1 i <;> cases T1 i <;> rfl)
      right_inv s := by
        rcases s with ⟨⟨c0, c1, kX, kR0, kR1⟩, free⟩
        dsimp only
        have hc0' : (x0 ^^ (c0 ^^ x0)) = c0 := by cases x0 <;> cases c0 <;> rfl
        have hc1' : ((c0 ^^ x0) ^^ b ^^ (c1 ^^ (c0 ^^ x0) ^^ b)) = c1 := by
          cases x0 <;> cases c0 <;> cases b <;> cases c1 <;> rfl
        refine Prod.ext (Prod.ext hc0' (Prod.ext hc1'
          (Prod.ext ?_ (Prod.ext ?_ ?_)))) ?_
        · funext i; cases c0 <;> simp
        · funext i
          rw [hc1']
          cases c1 <;> cases c0 <;>
            simp only [↓reduceIte, Bool.false_eq_true, Pi.add_apply, hadd_cancel]
        · funext i
          rw [hc1']
          cases c1 <;> cases c0 <;>
            simp only [↓reduceIte, Bool.false_eq_true, Bool.not_true, Bool.not_false,
              Pi.add_apply, hadd_cancel]
        · funext i; cases c0 <;> simp }
  have hreal : ProbComp.eval (tokenGateScheme.obvView k q) =
      (PMF.uniformOfFintype
        (Bool × Bool × BitString (k + 1) × BitString (k + 1) × BitString (k + 1))).map
        fun (c0, c1, kX, kR0, kR1) =>
          ⟨(List.ofFn kR0 ++ [c1]) ++ (List.ofFn kR1 ++ [c1]), List.ofFn kX ++ [c0]⟩ := by
    have hcoins : tokenGateScheme.coins k q.fn = baseGateCoinLen k := rfl
    rw [Scheme.obvView, ProbComp.eval_bind, Scheme.eval_garble, hcoins, BitString.uniformList]
    simp only [tokenGateScheme, Scheme.withTokenDecoding, ProbComp.eval_pure, PMF.bind_map,
      Function.comp_def]
    rw [← PMF.uniformOfFintype_map_equiv (gateCoinsEquiv k),
      ← PMF.uniformOfFintype_map_equiv viewEquiv.symm, PMF.map_comp, PMF.bind_map,
      ← PMF.uniformOfFintype_prod]
    simp only [PMF.map, Function.comp_def, PMF.bind_bind, PMF.pure_bind]
    have hconst : ∀ s : Bool × Bool × BitString (k + 1) × BitString (k + 1) × BitString (k + 1),
        ∀ free : BitString (k + 1),
          (let g := baseGateScheme.gb k b (List.ofFn (packCoins k (viewEquiv.symm (s, free))))
           ObvView.mk g.fn (baseGateScheme.encode g.encInfo q.input)) =
          ⟨(List.ofFn s.2.2.2.1 ++ [s.2.1]) ++ (List.ofFn s.2.2.2.2 ++ [s.2.1]),
            List.ofFn s.2.2.1 ++ [s.1]⟩ := by
      intro ⟨c0, c1, kX, kR0, kR1⟩ free
      let c := viewEquiv.symm ((c0, c1, kX, kR0, kR1), free)
      have hpin : (coinInPerm (List.ofFn (packCoins k c))) = (c0 ^^ x0) := coinInPerm_pack c
      have hpout : (coinOutPerm (List.ofFn (packCoins k c))) = (c1 ^^ (c0 ^^ x0) ^^ b) :=
        coinOutPerm_pack c
      have hrow0 : List.zipWith xor (inLabel k (List.ofFn (packCoins k c)) false)
          (outLabel k (List.ofFn (packCoins k c)) (coinInPerm (List.ofFn (packCoins k c)) ^^ b ^^
            coinOutPerm (List.ofFn (packCoins k c)))) =
          List.ofFn kR0 ++ [c1] := by
        simp only [inLabel, outLabel, coinInKey_pack, coinOutKey_pack, hpin, hpout]
        rw [zipWith_xor_append (by simp)]
        have hcol1 : ((c0 ^^ x0) ^^ b ^^ (c1 ^^ (c0 ^^ x0) ^^ b)) = c1 := by
          cases c0 <;> cases x0 <;> cases b <;> cases c1 <;> rfl
        rw [hcol1, zipWith_xor_ofFn]
        refine congrArg₂ (· ++ ·) (congrArg List.ofFn (funext fun i => ?_)) ?_
        · cases c1 <;> cases c0 <;>
            (simp only [c, viewEquiv, Equiv.coe_fn_symm_mk, ↓reduceIte, Bool.false_eq_true,
              Pi.add_apply, hadd_cancel])
        · cases c1 <;> rfl
      have hrow1 : List.zipWith xor (inLabel k (List.ofFn (packCoins k c)) true)
          (outLabel k (List.ofFn (packCoins k c)) (!(coinInPerm (List.ofFn (packCoins k c))) ^^ b ^^
            coinOutPerm (List.ofFn (packCoins k c)))) =
          List.ofFn kR1 ++ [c1] := by
        simp only [inLabel, outLabel, coinInKey_pack, coinOutKey_pack, hpin, hpout]
        rw [zipWith_xor_append (by simp)]
        have hcol1 : (!(c0 ^^ x0) ^^ b ^^ (c1 ^^ (c0 ^^ x0) ^^ b)) = !c1 := by
          cases c0 <;> cases x0 <;> cases b <;> cases c1 <;> rfl
        rw [hcol1, zipWith_xor_ofFn]
        refine congrArg₂ (· ++ ·) (congrArg List.ofFn (funext fun i => ?_)) ?_
        · cases c1 <;> cases c0 <;>
            (simp only [c, viewEquiv, Equiv.coe_fn_symm_mk, ↓reduceIte, Bool.false_eq_true,
              Bool.not_true, Bool.not_false, Pi.add_apply, hadd_cancel])
        · cases c1 <;> rfl
      have henc : baseGateEncode (baseGateEncInfo k (List.ofFn (packCoins k c))) q.input =
          List.ofFn kX ++ [c0] := by
        have hlen : (baseGateEncInfo k (List.ofFn (packCoins k c))).length / 2 = k + 2 := by
          simp [baseGateEncInfo, length_inLabel]; omega
        rw [baseGateEncode, hlen, baseGateEncInfo]
        have hx0_eq : q.input.headD false = x0 := rfl
        rw [hx0_eq, hpin]
        cases hc0 : c0 <;> cases hx0 : x0 <;>
          simp only [Bool.false_eq_true, ↓reduceIte]
        · rw [List.take_left' (by simp [length_inLabel])]
          simp [inLabel, coinInKey_pack, c, viewEquiv, hc0]
        · rw [List.drop_left' (by simp [length_inLabel])]
          simp [inLabel, coinInKey_pack, c, viewEquiv, hc0]
        · rw [List.take_left' (by simp [length_inLabel])]
          simp [inLabel, coinInKey_pack, c, viewEquiv, hc0]
        · rw [List.drop_left' (by simp [length_inLabel])]
          simp [inLabel, coinInKey_pack, c, viewEquiv, hc0]
      simp only [baseGateScheme, baseGateFn]
      rw [hrow0, hrow1, henc]
    have hproj : ∀ s : Bool × Bool × BitString (k + 1) × BitString (k + 1) × BitString (k + 1),
        (PMF.uniformOfFintype (BitString (k + 1))).bind
          (fun free => PMF.pure (ObvView.mk
            (baseGateScheme.gb k b (List.ofFn (packCoins k (viewEquiv.symm (s, free))))).fn
            (baseGateScheme.encode
              (baseGateScheme.gb k b
                (List.ofFn (packCoins k (viewEquiv.symm (s, free))))).encInfo
              q.input))) =
        PMF.pure ⟨(List.ofFn s.2.2.2.1 ++ [s.2.1]) ++ (List.ofFn s.2.2.2.2 ++ [s.2.1]),
          List.ofFn s.2.2.1 ++ [s.1]⟩ := by
      intro s
      refine (PMF.bind_const (PMF.uniformOfFintype (BitString (k + 1))) _).symm.trans ?_ |>.symm
      exact PMF.bind_congr_on_support _ _ _ fun free _ => (congrArg PMF.pure (hconst s free)).symm
    have hb_eq : q.fn = b := rfl
    rw [hb_eq]
    dsimp only [gateCoinsEquiv]
    exact (PMF.bind_congr_on_support _ _ _ fun s _ => hproj s).trans rfl
  have hsim : ProbComp.eval (tokenGateObvSim k ()) =
      (PMF.uniformOfFintype
        (Bool × Bool × BitString (k + 1) × BitString (k + 1) × BitString (k + 1))).map
        fun (c0, c1, kX, kR0, kR1) =>
          ⟨(List.ofFn kR0 ++ [c1]) ++ (List.ofFn kR1 ++ [c1]), List.ofFn kX ++ [c0]⟩ := by
    simp only [tokenGateObvSim, ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_pure,
      BitString.eval_sampleList, BitString.uniformList, PMF.map, Function.comp_def, PMF.bind_bind,
      PMF.pure_bind, ← PMF.uniformOfFintype_prod]
  exact hreal.trans hsim.symm

theorem obvSimAdvantage_tokenGateScheme_eq_zero (k : ℕ) {σ : Type} (B : ObvSimAdversary Bool σ) :
    obvSimAdvantage tokenGateScheme unitSideInfo k (tokenGateObvSim k) B = 0 := by
  have hexp : ProbComp.eval (obvSimExperiment tokenGateScheme unitSideInfo k (tokenGateObvSim k) B
      true) =
      ProbComp.eval (obvSimExperiment tokenGateScheme unitSideInfo k (tokenGateObvSim k) B
        false) := by
    simp only [obvSimExperiment, ProbComp.eval_bind]
    refine PMF.bind_congr_on_support _ _ _ fun ⟨q, st⟩ _ => ?_
    by_cases hlen : q.input.length = tokenGateScheme.inLen q.fn
    · simp only [hlen, ↓reduceIte, Bool.false_eq_true, ProbComp.eval_bind]
      rw [eval_obvView_tokenGateScheme k q hlen]
    · simp [hlen]
  rw [obvSimAdvantage, Experiment.advantage, hexp, Game.advantage_self]

/-- **Universal output simulatability** of `tokenGateScheme`, proved via
`outSimSecureUniversal_of_obvSim_and_aut`. -/
theorem tokenGateScheme_outSimSecureUniversal :
    tokenGateScheme.OutSimSecureUniversal unitSideInfo encBool encUnit := by
  refine outSimSecureUniversal_of_obvSim_and_aut tokenGateScheme_isValid.correct
    tokenGateScheme_isEfficient ?_ ?_
  · refine ⟨tokenGateObvSim, tokenGateObvSim_isPPT, fun σ encσ B hB => ?_⟩
    simp only [obvSimAdvantage_tokenGateScheme_eq_zero]
    exact negligible_zero
  · intro σ encσ A hA
    refine negligible_of_le (negligible_inv_two_pow_of_le (fun k => Nat.le_succ k)) fun k => ?_
    simpa [one_div] using tokenGateScheme_autAdvantage_le k (A k)

private def tokenGateDecBody (k : ℕ) (view : ObvView) (y T_inact : List Bool) : List Bool :=
  let Y := baseGateEval view.fn view.input
  let tokInact := T_inact ++ [!(Y.getD (Y.length - 1) false)]
  tokenDecInfo k (k + 2) [if y.headD false then (tokInact, Y) else (Y, tokInact)]

/-- Uniform strict PPT decoding-information simulator for `tokenGateScheme`: evaluates
`Y = baseGateEval view.fn view.input`, samples a uniform `(k + 1)`-bit inactive output key, and
packs `(Y, T_inact ++ [!col(Y)])` ordered by `y.headD false`. -/
noncomputable def tokenGateDecSim (k : ℕ) (_ : Unit) (view : ObvView) (y : List Bool) :
    ProbComp (List Bool) := do
  let T_inact ← BitString.sampleList (k + 1)
  pure (tokenGateDecBody k view y T_inact)

private theorem tokenGateDecBody_polyTime :
    ComputableInPolyTime
      (fun p : (ℕ × Unit × ObvView × List Bool) × List Bool =>
        tokenGateDecBody p.1.1 p.1.2.2.1 p.1.2.2.2 p.2)
      (encPair (encDecSimIn Unit encUnit) encBits) encBits := by
  let E := encPair (encDecSimIn Unit encUnit) encBits
  have hk : ComputableInPolyTime (fun p : (ℕ × Unit × ObvView × List Bool) × List Bool => p.1.1)
      E encUnary := by fun_prop
  have hT : ComputableInPolyTime (fun p : (ℕ × Unit × ObvView × List Bool) × List Bool => p.2)
      E encBits := by fun_prop
  have hvfn : ComputableInPolyTime
      (fun p : (ℕ × Unit × ObvView × List Bool) × List Bool => p.1.2.2.1.fn) E encBits :=
    OutSim.encObvView_fn_polyTime
      ((ComputableInPolyTime.fst OutSim.encObvView encBits).comp (by fun_prop))
  have hvin : ComputableInPolyTime
      (fun p : (ℕ × Unit × ObvView × List Bool) × List Bool => p.1.2.2.1.input) E encBits :=
    OutSim.encObvView_input_polyTime
      ((ComputableInPolyTime.fst OutSim.encObvView encBits).comp (by fun_prop))
  have hY : ComputableInPolyTime
      (fun p : (ℕ × Unit × ObvView × List Bool) × List Bool =>
        baseGateEval p.1.2.2.1.fn p.1.2.2.1.input) E encBits :=
    baseGate_polyTime.evalGarbled.comp (hvfn.prod hvin)
  have hybit : ComputableInPolyTime
      (fun p : (ℕ × Unit × ObvView × List Bool) × List Bool => p.1.2.2.2.headD false)
      E encBool :=
    (ComputableInPolyTime.headD (encA := encBool) (encL := encBits) false).comp (by fun_prop)
  have hc := ComputableInPolyTime.bitsGetDWithInput hY
    (ComputableInPolyTime.unary_sub' (ComputableInPolyTime.length_bits_comp hY) (.const 1)) false
  have htok := ComputableInPolyTime.bitsAppend hT
    (ComputableInPolyTime.bitsCons (ComputableInPolyTime.bool_not.comp hc) (.const []))
  have hpair := hybit.ite (htok.prod hY) (hY.prod htok)
  have hlist := (ComputableInPolyTime.cons (encPair encBits encBits)).comp
    (hpair.prod (.const ([] : List (List Bool × List Bool))))
  have hw := ComputableInPolyTime.unary_add' hk (.const 2)
  exact (hk.prod (hw.prod hlist)).of_enc_eq fun _ => rfl

private theorem tokenGateDecSim_isPPT :
    IsPPTOn (encDecSimIn Unit encUnit) encBits
      (fun (k, φ, view, y) => tokenGateDecSim k φ view y) := by
  unfold tokenGateDecSim
  have hk : ComputableInPolyTime (fun p : ℕ × Unit × ObvView × List Bool => p.1)
      (encDecSimIn Unit encUnit) encUnary :=
    ComputableInPolyTime.fst encUnary (encPair encUnit (encPair OutSim.encObvView encBits))
  have hkeys : IsPPTOn (encDecSimIn Unit encUnit) encBits
      (fun p => BitString.sampleList (p.1 + 1)) :=
    Probability.isPPTOn_sampleList.preprocess (ComputableInPolyTime.unary_add' hk (.const 1))
  exact hkeys.bind_with tokenGateDecBody_polyTime.isPPTOn

/-- Exact zero decoding-simulation advantage for `tokenGateScheme` against `tokenGateDecSim`. -/
theorem decSimAdvantage_tokenGateScheme_eq_zero (k : ℕ) {σ : Type} (B : PrvSimAdversary Bool σ) :
    decSimAdvantage tokenGateScheme unitSideInfo k (tokenGateDecSim k) B = 0 := by
  have hexp : ProbComp.eval (decSimExperiment tokenGateScheme unitSideInfo k (tokenGateDecSim k) B
      true) =
      ProbComp.eval (decSimExperiment tokenGateScheme unitSideInfo k (tokenGateDecSim k) B
        false) := by
    simp only [decSimExperiment, ProbComp.eval_bind]
    refine PMF.bind_congr_on_support _ _ _ fun ⟨q, st⟩ _ => ?_
    by_cases hlen : q.input.length = tokenGateScheme.inLen q.fn
    · simp only [hlen, ↓reduceIte]
      have hx1 : q.input.length = 1 := hlen
      let x0 := q.input.headD false
      let b := q.fn
      let equiv := otpMaskInactiveEquiv k b x0
      have hreal : ProbComp.eval (tokenGateScheme.prvView k q) =
          (PMF.uniformOfFintype (GateCoins k)).map fun c =>
            let g := tokenGateScheme.gb k b (List.ofFn (packCoins k (equiv c)))
            ⟨g.fn, tokenGateScheme.encode g.encInfo q.input, g.decInfo⟩ := by
        have hcoins : tokenGateScheme.coins k q.fn = baseGateCoinLen k := rfl
        rw [Scheme.prvView, ProbComp.eval_bind, Scheme.eval_garble, hcoins, BitString.uniformList,
          PMF.bind_map]
        conv_lhs =>
          rw [← PMF.uniformOfFintype_map_equiv (gateCoinsEquiv k), PMF.bind_map,
            ← PMF.uniformOfFintype_map_equiv equiv, PMF.bind_map]
        simp only [ProbComp.eval_pure, PMF.map, Function.comp_def, PMF.bind_bind, PMF.pure_bind]
        rfl
      have hsim : (ProbComp.eval (tokenGateScheme.obvView k q)).bind (fun view =>
            (ProbComp.eval (tokenGateDecSim k () view (tokenGateScheme.ev b q.input))).map
              fun d => (⟨view.fn, view.input, d⟩ : PrvView)) =
          (PMF.uniformOfFintype (GateCoins k)).map fun c =>
            let g := tokenGateScheme.gb k b (List.ofFn (packCoins k (equiv c)))
            ⟨g.fn, tokenGateScheme.encode g.encInfo q.input, g.decInfo⟩ := by
        let splitOut := @gateSplitOut k b x0
        let splitEquiv := gateSplitEquiv k b x0
        have hcoins : tokenGateScheme.coins k q.fn = baseGateCoinLen k := rfl
        conv_rhs =>
          rw [← PMF.uniformOfFintype_map_equiv splitEquiv, ← PMF.uniformOfFintype_prod]
          simp only [PMF.map, Function.comp_def, PMF.bind_bind, PMF.pure_bind]
        rw [Scheme.obvView, ProbComp.eval_bind, Scheme.eval_garble, hcoins, BitString.uniformList,
          PMF.bind_map]
        simp only [tokenGateDecSim, tokenGateDecBody, ProbComp.eval_bind, ProbComp.eval_pure,
          BitString.eval_sampleList, BitString.uniformList, PMF.bind_map]
        conv_lhs =>
          rw [← PMF.uniformOfFintype_map_equiv (gateCoinsEquiv k), PMF.bind_map,
            ← PMF.uniformOfFintype_map_equiv equiv, PMF.bind_map,
            ← PMF.uniformOfFintype_map_equiv splitEquiv, PMF.bind_map, ← PMF.uniformOfFintype_prod]
          simp only [PMF.map, Function.comp_def, PMF.bind_bind, PMF.pure_bind]
        refine PMF.bind_congr_on_support _ _ _ fun pre _ => ?_
        rcases pre with ⟨p, q_out, K0, K1, T_act⟩
        have hview_const : ∀ T1 T2 : BitString (k + 1),
            (let g := tokenGateScheme.gb k q.fn (List.ofFn ((gateCoinsEquiv k)
              (equiv (splitEquiv ((p, q_out, K0, K1, T_act), T1)))))
             ObvView.mk g.fn (tokenGateScheme.encode g.encInfo q.input)) =
            (let g := tokenGateScheme.gb k q.fn (List.ofFn ((gateCoinsEquiv k)
              (equiv (splitEquiv ((p, q_out, K0, K1, T_act), T2)))))
             ObvView.mk g.fn (tokenGateScheme.encode g.encInfo q.input)) :=
          fun T1 T2 =>
            obvView_otpMask_split_indep k b x0 p q_out K0 K1 T_act T1 T2 q.input rfl
        have hfn_const : ∀ T1 T2 : BitString (k + 1),
            (tokenGateScheme.gb k q.fn (List.ofFn ((gateCoinsEquiv k)
              (equiv (splitEquiv ((p, q_out, K0, K1, T_act), T1)))))).fn =
            (tokenGateScheme.gb k q.fn (List.ofFn ((gateCoinsEquiv k)
              (equiv (splitEquiv ((p, q_out, K0, K1, T_act), T2)))))).fn :=
          fun T1 T2 => congrArg ObvView.fn (hview_const T1 T2)
        have hin_const : ∀ T1 T2 : BitString (k + 1),
            tokenGateScheme.encode (tokenGateScheme.gb k q.fn (List.ofFn ((gateCoinsEquiv k)
              (equiv (splitEquiv ((p, q_out, K0, K1, T_act), T1)))))).encInfo q.input =
            tokenGateScheme.encode (tokenGateScheme.gb k q.fn (List.ofFn ((gateCoinsEquiv k)
              (equiv (splitEquiv ((p, q_out, K0, K1, T_act), T2)))))).encInfo q.input :=
          fun T1 T2 => congrArg ObvView.input (hview_const T1 T2)
        conv_lhs =>
          arg 2; ext T_unused
          simp only [hfn_const T_unused (0 : BitString (k + 1)),
            hin_const T_unused (0 : BitString (k + 1))]
        rw [PMF.bind_const]
        refine PMF.bind_congr_on_support _ _ _ fun T_inact _ => ?_
        rw [hfn_const (0 : BitString (k + 1)) T_inact,
          hin_const (0 : BitString (k + 1)) T_inact]
        let coins' := List.ofFn (packCoins k (equiv (splitOut p q_out K0 K1 T_act T_inact)))
        have hev := eval_baseGate_eq k b coins' q.input hx1
        have hperm_out : coinOutPerm coins' = q_out := by
          rw [coinOutPerm_pack]
          dsimp [equiv, otpMaskInactiveEquiv, splitOut, gateSplitOut]
          split_ifs <;> rfl
        have hcol : (outLabel k coins' ((x0 ^^ b) ^^ q_out)).getD
            ((outLabel k coins' ((x0 ^^ b) ^^ q_out)).length - 1) false = ((x0 ^^ b) ^^ q_out) := by
          have hlen_o : (outLabel k coins' ((x0 ^^ b) ^^ q_out)).length - 1 =
              (coinOutKey k coins' ((x0 ^^ b) ^^ q_out)).length := by
            rw [length_outLabel, coinOutKey, BitString.length_listRow]; omega
          rw [hlen_o, outLabel, List.getD_eq_getElem?_getD,
            List.getElem?_append_right le_rfl, Nat.sub_self, List.getElem?_cons_zero,
            Option.getD_some]
        have hT_inact : coinOutKey k coins' (!((x0 ^^ b) ^^ q_out)) = List.ofFn T_inact := by
          rw [coinOutKey_pack]
          dsimp [equiv, otpMaskInactiveEquiv, splitOut, gateSplitOut]
          cases x0 ^^ p <;> cases (x0 ^^ b) ^^ q_out <;> simp
        have hT_act : coinOutKey k coins' ((x0 ^^ b) ^^ q_out) = List.ofFn T_act := by
          rw [coinOutKey_pack]
          dsimp [equiv, otpMaskInactiveEquiv, splitOut, gateSplitOut]
          cases x0 ^^ p <;> cases (x0 ^^ b) ^^ q_out <;> simp
        have hcoin_eq1 : List.ofFn
            ((gateCoinsEquiv k) (equiv (splitEquiv ((p, q_out, K0, K1, T_act), T_inact)))) =
            coins' := rfl
        have hcoin_eq2 : List.ofFn
            (packCoins k (equiv (splitEquiv ((p, q_out, K0, K1, T_act), T_inact)))) =
            coins' := rfl
        have hb_eq : q.fn = b := rfl
        rw [hcoin_eq1, hcoin_eq2, hb_eq]
        refine congrArg PMF.pure (congrArg (PrvView.mk _ _) ?_)
        have hx0_eq : q.input.headD false = x0 := rfl
        have heq_pair : (if x0 ^^ b then (List.ofFn T_inact ++ [!((x0 ^^ b) ^^ q_out)],
              outLabel k coins' ((x0 ^^ b) ^^ q_out))
            else (outLabel k coins' ((x0 ^^ b) ^^ q_out),
              List.ofFn T_inact ++ [!((x0 ^^ b) ^^ q_out)])) =
            (outLabel k coins' q_out, outLabel k coins' (!q_out)) := by
          cases hxb : x0 ^^ b <;> cases hq : q_out
          · have h1 : coinOutKey k coins' false = List.ofFn T_act := by
              simpa [hxb, hq] using hT_act
            have h2 : coinOutKey k coins' true = List.ofFn T_inact := by
              simpa [hxb, hq] using hT_inact
            simp only [Bool.false_eq_true, ↓reduceIte, Bool.false_xor, Bool.not_false, outLabel,
              h1, h2]
          · have h1 : coinOutKey k coins' true = List.ofFn T_act := by
              simpa [hxb, hq] using hT_act
            have h2 : coinOutKey k coins' false = List.ofFn T_inact := by
              simpa [hxb, hq] using hT_inact
            simp only [Bool.false_eq_true, ↓reduceIte, Bool.false_xor, Bool.not_true, outLabel,
              h1, h2]
          · have h1 : coinOutKey k coins' true = List.ofFn T_act := by
              simpa [hxb, hq] using hT_act
            have h2 : coinOutKey k coins' false = List.ofFn T_inact := by
              simpa [hxb, hq] using hT_inact
            simp only [↓reduceIte, Bool.true_xor, Bool.not_false, Bool.not_true, outLabel, h1, h2]
          · have h1 : coinOutKey k coins' false = List.ofFn T_act := by
              simpa [hxb, hq] using hT_act
            have h2 : coinOutKey k coins' true = List.ofFn T_inact := by
              simpa [hxb, hq] using hT_inact
            simp only [↓reduceIte, Bool.true_xor, Bool.not_true, Bool.not_false, outLabel, h1, h2]
        simp only [tokenGateScheme, Scheme.withTokenDecoding, baseGateScheme, tokenGateSpec, hev,
          hx0_eq, hcol, hperm_out, List.headD_cons, List.map_cons, List.map_nil, id_eq, heq_pair]
      have hsim' : (ProbComp.eval (tokenGateScheme.obvView k q)).bind (fun view =>
          (ProbComp.eval (tokenGateDecSim k () view (tokenGateScheme.ev b q.input))).bind fun d =>
            ProbComp.eval (B.guess st (some ⟨view.fn, view.input, d⟩))) =
          ((ProbComp.eval (tokenGateScheme.obvView k q)).bind fun view =>
            (ProbComp.eval (tokenGateDecSim k () view (tokenGateScheme.ev b q.input))).map
              fun d => (⟨view.fn, view.input, d⟩ : PrvView)).bind
            fun view => ProbComp.eval (B.guess st (some view)) := by
        simp [PMF.map, Function.comp_def, PMF.bind_bind]
      simp only [ProbComp.eval_bind, Bool.false_eq_true, ↓reduceIte, unitSideInfo]
      change (ProbComp.eval (tokenGateScheme.prvView k q)).bind
          (fun view => ProbComp.eval (B.guess st (some view))) =
        (ProbComp.eval (tokenGateScheme.obvView k q)).bind fun view =>
          (ProbComp.eval (tokenGateDecSim k () view (tokenGateScheme.ev b q.input))).bind fun d =>
            ProbComp.eval (B.guess st (some ⟨view.fn, view.input, d⟩))
      rw [hreal, hsim', hsim, PMF.bind_map]
    · simp [hlen]
  rw [decSimAdvantage, Experiment.advantage, hexp, Game.advantage_self]

/-- **Universal privacy (`PrvSimSecureUniversal`)** of `tokenGateScheme`, deduced from
`tokenGateScheme_outSimSecureUniversal` and `decSimAdvantage_tokenGateScheme_eq_zero` via
`prvSimSecureUniversal_of_outSimSecureUniversal_and_decSim`. -/
theorem tokenGateScheme_prvSimSecureUniversal :
    tokenGateScheme.PrvSimSecureUniversal unitSideInfo encBool encUnit := by
  refine prvSimSecureUniversal_of_outSimSecureUniversal_and_decSim unitSideInfo_phi_polyTime
    tokenGateScheme_isEfficient.ev tokenGateScheme_outSimSecureUniversal tokenGateDecSim
    tokenGateDecSim_isPPT fun σ encσ B hB => ?_
  simp only [decSimAdvantage_tokenGateScheme_eq_zero]
  exact negligible_zero

/-! ## Boundary separation: `OutSimSecureUniversal` does NOT imply `PrvSimSecure` -/

/-- Variant of `tokenGateScheme` that prepends the secret gate bit `b : Bool` to `decInfo` and
ignores that leading bit during `decode`. -/
def leakyDecTokenScheme : Scheme Bool where
  inLen := tokenGateScheme.inLen
  outLen := tokenGateScheme.outLen
  size := tokenGateScheme.size
  ev := tokenGateScheme.ev
  coinLen := tokenGateScheme.coinLen
  gb k b coins :=
    let g := tokenGateScheme.gb k b coins
    ⟨g.fn, g.encInfo, b :: g.decInfo⟩
  encode := tokenGateScheme.encode
  evalGarbled := tokenGateScheme.evalGarbled
  decode d Y := tokenGateScheme.decode d.tail Y

theorem leakyDecTokenScheme_outSimSecureUniversal :
    leakyDecTokenScheme.OutSimSecureUniversal unitSideInfo encBool encUnit := by
  have heq : ∀ k (S : ObvSimulator Unit) {σ₁ σ₂ : Type} (A : OutSimAdversary Bool σ₁ σ₂),
      outSimAdvantage leakyDecTokenScheme unitSideInfo k S A =
        outSimAdvantage tokenGateScheme unitSideInfo k S A := by
    intro k S σ₁ σ₂ A
    have htrue :
        ProbComp.eval (outSimExperiment leakyDecTokenScheme unitSideInfo k S A true) =
        ProbComp.eval (outSimExperiment tokenGateScheme unitSideInfo k S A true) := by
      simp only [outSimExperiment, ↓reduceIte, ProbComp.eval_bind]
      refine PMF.bind_congr_on_support _ _ _ fun ⟨q, st⟩ _ => ?_
      by_cases hlen : q.input.length = tokenGateScheme.inLen q.fn
      · simp only [leakyDecTokenScheme, hlen, ↓reduceIte, Scheme.garble, Scheme.coins,
          ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind]
        rfl
      · simp [leakyDecTokenScheme, hlen]
    have hfalse :
        ProbComp.eval (outSimExperiment leakyDecTokenScheme unitSideInfo k S A false) =
        ProbComp.eval (outSimExperiment tokenGateScheme unitSideInfo k S A false) := rfl
    rw [outSimAdvantage, Experiment.advantage, htrue, hfalse]
    rfl
  obtain ⟨S, hS, hneg⟩ := tokenGateScheme_outSimSecureUniversal
  refine ⟨S, hS, fun σ₁ σ₂ encσ₁ encσ₂ A hA => ?_⟩
  simpa only [heq] using hneg σ₁ σ₂ encσ₁ encσ₂ A hA

/-- `leakyDecTokenScheme` is NOT `PrvSimSecure`: choosing a uniform gate `b ← Bool` and input
`[b]` fixes `ev b [b] = [false]` in both worlds while `decInfo.headD false = b` reveals `b`
with certainty in the real world vs `1/2` for any simulator. -/
theorem leakyDecTokenScheme_not_prvSimSecure :
    ¬ leakyDecTokenScheme.PrvSimSecure unitSideInfo encBool encUnit := by
  intro hprv
  let B : ℕ → PrvSimAdversary Bool Bool := fun _ =>
    { choose _ := do
        let b ← ProbComp.uniform Bool
        pure (⟨b, [b]⟩, b)
      guess b mview :=
        pure (match mview with
        | none => false
        | some view => view.decInfo.headD false == b) }
  have hBPPT : TwoStage.IsPPT encUnit (encQuery Bool encBool) (encOption encPrvView) encBool
      encBool B := by
    refine ⟨?_, ?_⟩
    · refine (Probability.isPPTOn_uniform_bool _).bind_with ?_
      refine ComputableInPolyTime.isPPTOn ?_
      have hb : ComputableInPolyTime (fun p : (ℕ × Unit) × Bool => p.2)
          (encPair encUnaryUnit encBool) encBool :=
        ComputableInPolyTime.snd encUnaryUnit encBool
      have hq : ComputableInPolyTime (fun p : (ℕ × Unit) × Bool => (⟨p.2, [p.2]⟩ : Query Bool))
          (encPair encUnaryUnit encBool) (encQuery Bool encBool) :=
        (hb.prod (ComputableInPolyTime.bitsCons hb (.const []))).of_enc_eq fun _ => rfl
      exact hq.prod hb
    · refine ComputableInPolyTime.isPPTOn ?_
      have hb : ComputableInPolyTime (fun p : ℕ × Bool × Option PrvView => p.2.1)
          (encPair encUnary (encPair encBool (encOption encPrvView))) encBool :=
        (ComputableInPolyTime.fst encBool (encOption encPrvView)).comp
          (ComputableInPolyTime.snd encUnary (encPair encBool (encOption encPrvView)))
      have hmv : ComputableInPolyTime (fun p : ℕ × Bool × Option PrvView => p.2.2)
          (encPair encUnary (encPair encBool (encOption encPrvView))) (encOption encPrvView) :=
        (ComputableInPolyTime.snd encBool (encOption encPrvView)).comp
          (ComputableInPolyTime.snd encUnary (encPair encBool (encOption encPrvView)))
      have hnone : ComputableInPolyTime (fun _ : ℕ × Bool × Option PrvView => false)
          (encPair encUnary (encPair encBool (encOption encPrvView))) encBool :=
        .const false
      have hsome : ComputableInPolyTime
          (fun p : (ℕ × Bool × Option PrvView) × PrvView => p.2.decInfo.headD false == p.1.2.1)
          (encPair (encPair encUnary (encPair encBool (encOption encPrvView))) encPrvView)
          encBool := by
        have hv : ComputableInPolyTime
            (fun p : (ℕ × Bool × Option PrvView) × PrvView => p.2)
            (encPair (encPair encUnary (encPair encBool (encOption encPrvView))) encPrvView)
            encPrvView :=
          ComputableInPolyTime.snd
            (encPair encUnary (encPair encBool (encOption encPrvView))) encPrvView
        have hd : ComputableInPolyTime
            (fun p : (ℕ × Bool × Option PrvView) × PrvView => p.2.decInfo)
            (encPair (encPair encUnary (encPair encBool (encOption encPrvView))) encPrvView)
            encBits :=
          ((ComputableInPolyTime.snd encBits encBits).comp
            (ComputableInPolyTime.snd encBits (encPair encBits encBits))).comp
            (hv.of_enc_eq fun _ => rfl)
        have hhd : ComputableInPolyTime
            (fun p : (ℕ × Bool × Option PrvView) × PrvView => p.2.decInfo.headD false)
            (encPair (encPair encUnary (encPair encBool (encOption encPrvView))) encPrvView)
            encBool :=
          (ComputableInPolyTime.headD (encA := encBool) (encL := encBits) false).comp hd
        have hbm : ComputableInPolyTime
            (fun p : (ℕ × Bool × Option PrvView) × PrvView => p.1.2.1)
            (encPair (encPair encUnary (encPair encBool (encOption encPrvView))) encPrvView)
            encBool :=
          hb.comp (ComputableInPolyTime.fst
            (encPair encUnary (encPair encBool (encOption encPrvView))) encPrvView)
        convert ComputableInPolyTime.decide_eq' hhd hbm using 1
      convert ComputableInPolyTime.optionElimWithInput
        (body := fun p (v : PrvView) => v.decInfo.headD false == p.2.1) hmv hnone hsome using 1
      funext ⟨_, (_, mv)⟩
      cases mv <;> rfl
  obtain ⟨S, _, hneg⟩ := hprv Bool encBool B hBPPT
  have hadv : ∀ k, prvSimAdvantage leakyDecTokenScheme unitSideInfo k (S k) (B k) = 1 / 2 := by
    intro k
    have htrue :
        ProbComp.eval (prvSimExperiment leakyDecTokenScheme unitSideInfo k (S k) (B k) true) =
        PMF.pure true := by
      simp only [prvSimExperiment, B, Scheme.prvView, Scheme.garble, leakyDecTokenScheme,
        ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind]
      rw [← PMF.bind_const (PMF.uniformOfFintype Bool) (PMF.pure true)]
      refine PMF.bind_congr_on_support _ _ _ fun b _ => ?_
      have hlen1 : ([b] : List Bool).length = tokenGateScheme.inLen b := rfl
      simp only [hlen1, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure,
        BitString.eval_sampleList, PMF.bind_bind, PMF.pure_bind]
      rw [← PMF.bind_const (BitString.uniformList _) (PMF.pure true)]
      exact PMF.bind_congr_on_support _ _ _ fun _ _ => by simp
    have hfalse :
        ProbComp.eval (prvSimExperiment leakyDecTokenScheme unitSideInfo k (S k) (B k) false) =
        PMF.uniformOfFintype Bool := by
      simp only [prvSimExperiment, B, leakyDecTokenScheme, unitSideInfo, ProbComp.eval_bind,
        ProbComp.eval_uniform, ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind]
      have hlen1 : ∀ a : Bool, ([a] : List Bool).length = tokenGateScheme.inLen a := fun _ => rfl
      have hev_const : ∀ b : Bool, tokenGateScheme.ev b [b] = [false] := fun b => by
        cases b <;> rfl
      simp only [hlen1, ↓reduceIte, Bool.false_eq_true, hev_const, ProbComp.eval_bind,
        ProbComp.eval_pure]
      have hlhs : ((PMF.uniformOfFintype Bool).bind fun a =>
          (ProbComp.eval (S k [false] ())).bind fun view =>
            PMF.pure (view.decInfo.headD false == a)) =
          ((PMF.uniformOfFintype Bool).bind fun a =>
            ((ProbComp.eval (S k [false] ())).map fun view => view.decInfo.headD false).map
              (· == a)) := by
        congr 1 with a : 1
        simp [PMF.map, Function.comp_def, PMF.bind_bind, PMF.pure_bind]
      exact hlhs.trans (Game.uniform_bool_bind_map_beq_const _)
    rw [prvSimAdvantage, Experiment.advantage, htrue, hfalse, Game.advantage_comm,
      Game.advantage_pure_true_left, Game.failProbability, PMF.uniformOfFintype_apply,
      Fintype.card_bool, Nat.cast_ofNat, ENNReal.toNNReal_inv, ENNReal.toNNReal_ofNat]
    norm_num
  exact not_negligible_const (c := (1 / 2 : ℝ≥0)) (by norm_num) (by simpa [hadv] using hneg)

end CslibFrontierTests.Crypto.GarblingOutputSim
