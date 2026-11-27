/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.Garbling.FreeXOR.Scheme
public import CslibFrontier.Crypto.Primitives.Garbling.HalfGates.Efficient
public import CslibFrontier.Crypto.Primitives.Garbling.PointPermute.Efficient
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import CslibFrontier.Tactic.PolyTime
import CslibFrontier.Foundations.Data.List.GetD
import CslibFrontier.Foundations.Data.List.Lookup

/-!
# Free-XOR garbling is efficient

`FreeXOR.scheme hash` of `CslibFrontier.Crypto.Primitives.Garbling.FreeXOR.Scheme` is an efficient
garbling scheme (`Scheme.IsEfficient`) for valid conventional circuits encoded by `encValidCircuit`
whenever the hash family `hash` is computed in polynomial time (`FreeXOR.scheme_isEfficient`).

`En`, `De` and `ev` reuse `projectiveEncode_polyTime`, `PointPermute.decodeWord_polyTime` and
`evalCirc_polyTime`. The garbler propagates zero labels by a fold over the gates, writes the body of
`F` with `PointPermute.bodyWith`, and reads the decoding bits from the zero labels. The evaluator is
a fold over the gates whose state is the labels so far and the position of the next gate's block.

We also define the Free-XOR side information `phiXor : SideInfo ValidCircuit XorTopology`, which
exposes the circuit topology together with one boolean per gate indicating whether the gate computes
XOR while hiding the truth tables of all non-XOR gates, together with its polynomial-time
projection certificate `phiXor_polyTime`.

## Main definitions

* `Cslib.Crypto.Garbling.FreeXOR.XorTopology`: topology together with XOR gate flags.
* `Cslib.Crypto.Garbling.FreeXOR.encXorTopology`: encoding of `XorTopology`.
* `Cslib.Crypto.Garbling.FreeXOR.phiXor`: side information revealing topology and XOR gate flags.

## Main results

* `Cslib.Crypto.Garbling.FreeXOR.scheme_isEfficient`: Free-XOR garbling is efficient.
* `Cslib.Crypto.Garbling.FreeXOR.phiXor_compatible`: `phiXor` agrees with `scheme`'s length
  readers.
* `Cslib.Crypto.Garbling.FreeXOR.phiXor_polyTime`: `phiXor` is computed in polynomial time.
-/

public section

namespace Cslib.Crypto.Garbling.FreeXOR

open Turing.MultiTapeTM

/-! ### Side information -/

/-- Side information for Free-XOR garbling: the circuit's valid topology `topo` together with the
list of booleans recording which gates compute XOR. -/
structure XorTopology where
  /-- The circuit topology (input/output counts and argument wires). -/
  topo : ValidTopo
  /-- For each gate `g`, whether it computes XOR. -/
  free : List Bool
  deriving DecidableEq

/-- Encoding of `XorTopology` via `encValidTopo` and `encBits`. -/
enc_structure encXorTopology : XorTopology where
  topo : encValidTopo, free : encBits

/-- Free-XOR side information `Φ_xor(f)`: reveals `f`'s valid topology and which gates compute XOR,
while hiding the truth tables of all non-XOR gates. -/
@[expose] def phiXor : SideInfo ValidCircuit XorTopology where
  phi f := ⟨phiTopo.phi f, List.ofFn fun g => isXorGate f.1 g⟩
  inLen t := t.topo.1.n
  outLen t := t.topo.1.m
  size t := t.topo.1.q

/-- `phiXor` is compatible with `FreeXOR.scheme hash`. -/
theorem phiXor_compatible (hash : List Bool → List Bool → List Bool) :
    phiXor.Compatible (scheme hash) :=
  fun _ => ⟨rfl, rfl, rfl⟩

/-- `phiXor` runs in polynomial time from `encValidCircuit`. -/
theorem phiXor_polyTime : ComputableInPolyTime phiXor.phi encValidCircuit encXorTopology := by
  have hmap : ComputableInPolyTime
      (fun ts : List (ℕ × ℕ × List Bool) => ts.map fun t => isXorTable t.2.2)
      (encList (encPair encNat (encPair encNat encBits))) encBits := by
    polytime [isXorTable]
  have hfree : ComputableInPolyTime (fun f : ValidCircuit =>
      List.ofFn fun g => isXorGate f.1 g) encValidCircuit encBits := by
    have heq : (fun f : ValidCircuit => List.ofFn fun g => isXorGate f.1 g) = fun f =>
        f.1.gateList.map fun t => isXorTable t.2.2 := by
      funext f
      simp only [ConventionalCircuit.gateList, List.map_ofFn]
      refine congrArg List.ofFn (funext fun g => ?_)
      exact (isXorTable_eq (f.1.G g)).symm
    rw [heq]
    exact hmap.comp circuitData_polyTime.snd'.snd'
  exact encXorTopology_mk_polyTime phiTopo_polyTime hfree

section Words

variable (hash : List Bool → List Bool → List Bool)

/-! ### Lengths of labels -/

private theorem length_le_of_mem_propagateWords (k : ℕ) (f : ConventionalCircuit)
    (coins : List Bool) (s : ℕ) : ∀ w ∈ propagateWords k f coins s, w.length ≤ k + 2 :=
  length_le_of_mem_simPropWords k f.topo (List.ofFn (isXorGate f)) (coins.drop (k + 1)) s

private theorem length_propagateWords (k : ℕ) (f : ConventionalCircuit) (coins : List Bool) {s : ℕ}
    (hs : s ≤ f.q) : (propagateWords k f coins s).length = f.n + s :=
  length_simPropWords k f.topo (List.ofFn (isXorGate f)) (coins.drop (k + 1)) hs

/-! ### Zero-label propagation as a fold -/

private def propagateWordStep (k : ℕ) (coins : List Bool) (ws : List (List Bool))
    (gate : ℕ × ℕ × List Bool) : List (List Bool) :=
  ws ++ [if isXorTable gate.2.2 then
    (List.zipWith xor (ws.getD (min (ws.length + 1) gate.1 - 1) [])
      (ws.getD (min (ws.length + 1) gate.2.1 - 1) [])).take (k + 2)
  else baseWord k coins ws.length]

private theorem propagateWords_eq_foldl (k : ℕ) (f : ConventionalCircuit) (coins : List Bool)
    {s : ℕ} (hs : s ≤ f.q) :
    propagateWords k f coins s =
      (f.gateList.take s).foldl (propagateWordStep k coins)
        ((List.range f.n).map (HalfGates.inputWord k coins)) := by
  induction s with
  | zero => simp [propagateWords, simPropWords, List.map_range_eq_ofFn]; rfl
  | succ s ih =>
    have hsq : s < f.q := hs
    have hdef (t : ℕ) : propagateWords k f coins t =
        simPropWords k f.topo (List.ofFn (isXorGate f)) (coins.drop (k + 1)) t := rfl
    rw [List.take_add_one, List.foldl_append, ← ih hsq.le, hdef, simPropWords,
      dite_eq_left (show s < f.topo.q from hsq), ← hdef]
    have hget : f.gateList[s]? = some (f.A ⟨s, hsq⟩, f.B ⟨s, hsq⟩,
        [f.G ⟨s, hsq⟩ false false, f.G ⟨s, hsq⟩ false true, f.G ⟨s, hsq⟩ true false,
          f.G ⟨s, hsq⟩ true true]) := by
      simp [ConventionalCircuit.gateList, hsq]
    rw [hget]
    simp only [Option.toList_some, List.foldl_cons, List.foldl_nil, propagateWordStep,
      List.getD_min_length_succ_sub_one, isXorTable_eq, ConventionalCircuit.topo]
    rw [length_propagateWords k f coins hsq.le,
      show (List.ofFn (isXorGate f)).getD s false = isXorGate f ⟨s, hsq⟩ by
        simp [List.getD_eq_getElem?_getD, hsq]]
    by_cases hxor : isXorGate f ⟨s, hsq⟩ = true
    · have hxor' : decide (f.G ⟨s, hsq⟩ = xor) = true := hxor
      rw [ite_eq_left hxor, ite_eq_left hxor']
      have ha := HalfGates.length_getD_le (length_le_of_mem_propagateWords k f coins s)
        (f.A ⟨s, hsq⟩ - 1)
      rw [List.take_of_length_le (by rw [List.length_zipWith]; omega)]
    · have hxor' : ¬ decide (f.G ⟨s, hsq⟩ = xor) = true := hxor
      rw [ite_eq_right hxor, ite_eq_right hxor']
      rfl

/-! ### Evaluator as a fold with bounded growth -/

private def evalUnmasked (k w g : ℕ) (block a b : List Bool) : List Bool :=
  let i := (if HalfGates.colourWord k a then 2 else 0) +
    (if HalfGates.colourWord k b then 1 else 0)
  let row := (block.drop (2 * w + 1 + i * (k + 2))).take (k + 2)
  List.zipWith xor row
    (List.zipWith xor (keyHashWord hash k a (PointPermute.tweak k g i 0))
      (keyHashWord hash k b (PointPermute.tweak k g i 1)))

private def evalGateCut (k w : ℕ) (body : List Bool) (state : List (List Bool) × ℕ) (g : ℕ) :
    List (List Bool) × ℕ :=
  let (labels, pos) := state
  let block := body.drop pos
  let a := labels.getD
    (BitString.boundedBinaryValue labels.length (block.take w).reverse - 1) []
  let b := labels.getD
    (BitString.boundedBinaryValue labels.length ((block.drop w).take w).reverse - 1) []
  if block.getD (2 * w) false then
    (labels ++ [(List.zipWith xor a b).take (k + 2)], pos + (2 * w + 1))
  else
    (labels ++ [evalUnmasked hash k w g block a b], pos + (2 * w + 1 + 4 * (k + 2)))

private theorem evalGate_eq_evalGateCut (k w : ℕ) (body : List Bool)
    (state : List (List Bool) × ℕ) (g : ℕ) (hstate : ∀ l ∈ state.1, l.length ≤ k + 2) :
    evalGate hash k w body state g = evalGateCut hash k w body state g ∧
      ∀ l ∈ (evalGate hash k w body state g).1, l.length ≤ k + 2 := by
  obtain ⟨labels, pos⟩ := state
  simp only [evalGate, evalGateCut, evalUnmasked]
  split
  · have hzip (a b : List Bool) (ha : a.length ≤ k + 2) :
        (List.zipWith xor a b).length ≤ k + 2 := by
      rw [List.length_zipWith]
      omega
    refine ⟨by rw [List.take_of_length_le (hzip _ _ (HalfGates.length_getD_le hstate _))],
      fun l hl => ?_⟩
    rcases List.mem_append.mp hl with hl | hl
    · exact hstate l hl
    · rw [List.mem_singleton.mp hl]
      exact hzip _ _ (HalfGates.length_getD_le hstate _)
  · refine ⟨rfl, fun l hl => ?_⟩
    rcases List.mem_append.mp hl with hl | hl
    · exact hstate l hl
    · rw [List.mem_singleton.mp hl]
      simp only [List.length_zipWith, List.length_take]
      omega

private theorem foldl_evalGate_eq (k w : ℕ) (body : List Bool) (gates : List ℕ) :
    ∀ state : List (List Bool) × ℕ, (∀ l ∈ state.1, l.length ≤ k + 2) →
      gates.foldl (evalGate hash k w body) state =
        gates.foldl (evalGateCut hash k w body) state := by
  induction gates with
  | nil => intro _ _; rfl
  | cons g gates ih =>
    intro state hstate
    obtain ⟨heq, hnext⟩ := evalGate_eq_evalGateCut hash k w body state g hstate
    rw [List.foldl_cons, List.foldl_cons, ← heq]
    exact ih _ hnext

private theorem length_evalGateCut_le (k w : ℕ) (body : List Bool)
    (state : List (List Bool) × ℕ) (g : ℕ) :
    (encPair (encList encBits) encUnary (evalGateCut hash k w body state g)).length ≤
      (encPair (encList encBits) encUnary state).length + (8 * (k + 2) + 2 * w + 10) := by
  obtain ⟨labels, pos⟩ := state
  simp only [evalGateCut, evalUnmasked]
  split
  · simp only [length_encPair, length_encList, List.map_append, List.sum_append, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, encBits_apply, encUnary_apply,
      List.length_replicate, List.length_take]
    omega
  · simp only [length_encPair, length_encList, List.map_append, List.sum_append, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, encBits_apply, encUnary_apply,
      List.length_replicate, List.length_zipWith, List.length_take]
    omega

/-! ### The garbled function from gate data -/

private def rowFromTable (k : ℕ) (Δ aLabel bLabel gLabel table : List Bool) (g i : ℕ) :
    List Bool :=
  let b₀ := i.testBit 1 ^^ HalfGates.colourWord k aLabel
  let b₁ := i.testBit 0 ^^ HalfGates.colourWord k bLabel
  let bit := table.getD ((if b₀ then 2 else 0) + (if b₁ then 1 else 0)) false
  let out := List.zipWith xor gLabel (HalfGates.maskWord k Δ bit)
  let m₀ := keyHashWord hash k (List.zipWith xor aLabel (HalfGates.maskWord k Δ b₀))
    (PointPermute.tweak k g i 0)
  let m₁ := keyHashWord hash k (List.zipWith xor bLabel (HalfGates.maskWord k Δ b₁))
    (PointPermute.tweak k g i 1)
  List.zipWith xor out (List.zipWith xor m₀ m₁)

private def gateRow (k n : ℕ) (Δ : List Bool) (labels : List (List Bool)) (table : List Bool)
    (g a b i : ℕ) : List Bool :=
  let isXor := isXorTable table
  (if i = 0 then [isXor] else []) ++
    if isXor then [] else
      rowFromTable hash k Δ (labels.getD a []) (labels.getD b []) (labels.getD (n + g) [])
        table g i

private theorem fnWord_eq (k : ℕ) (f : ConventionalCircuit) (coins : List Bool) :
    fnWord hash k f coins = PointPermute.encFn ((k, f.n, f.m, f.gateList.length),
      PointPermute.bodyWith f.n f.gateList.length ((propagateWords k f coins f.q).length + 1)
        (fun g => (f.gateList.getD g (0, 0, [])).1) (fun g => (f.gateList.getD g (0, 0, [])).2.1)
        (fun g a b i => gateRow hash k f.n (HalfGates.offsetWord k coins)
          (propagateWords k f coins f.q) ((f.gateList.getD g (0, 0, [])).2.2) g a b i)) := by
  have hgate (g : Fin f.q) : f.gateList.getD g (0, 0, []) = (f.A g, f.B g,
      [f.G g false false, f.G g false true, f.G g true false, f.G g true true]) := by
    simp [ConventionalCircuit.gateList, List.getD_eq_getElem?_getD]
  rw [ConventionalCircuit.length_gateList, PointPermute.bodyWith_eq_ofFn f.A f.B
    (fun g i => gateRow hash k f.n (HalfGates.offsetWord k coins)
      (propagateWords k f coins f.q)
      [f.G g false false, f.G g false true, f.G g true false, f.G g true true]
      g (f.A g - 1) (f.B g - 1) i)
    (fun g => by rw [hgate]) (fun g => by rw [hgate])
    (fun g i => by simp only [hgate, gateRow, List.getD_min_length_succ_sub_one])]
  simp only [fnWord]
  congr 2
  refine congrArg List.flatten (congrArg List.ofFn (funext fun g => ?_))
  simp only [gateWord, gateRow, rowFromTable, isXorTable_eq, getD_table, rowWord,
    List.ofFn_succ, List.ofFn_zero, List.flatten_cons, List.flatten_nil, List.append_assoc]
  by_cases hxor : f.G g = xor
  · simp [isXorGate, hxor]
  · simp [isXorGate, hxor]

end Words

/-! ### Certificates -/

variable {hash : List Bool → List Bool → List Bool}
  (hf : ComputableInPolyTime (fun p : List Bool × List Bool => hash p.1 p.2)
    (encPair encBits encBits) encBits)

include hf in
/-- The key-only hash on words is computed in polynomial time. -/
theorem keyHashWord_polyTime {γ : Type} {encIn : γ ↪ List Bool} {k : γ → ℕ}
    {a t : γ → List Bool} (hk : ComputableInPolyTime k encIn encUnary)
    (ha : ComputableInPolyTime a encIn encBits) (ht : ComputableInPolyTime t encIn encBits) :
    ComputableInPolyTime (fun x => keyHashWord hash (k x) (a x) (t x)) encIn encBits := by
  have h : ComputableInPolyTime (fun p : ℕ × List Bool × List Bool =>
      keyHashWord hash p.1 p.2.1 p.2.2) (encPair encUnary (encPair encBits encBits)) encBits := by
    have h1 : ComputableInPolyTime (fun p : ℕ × List Bool × List Bool =>
        BitString.listRow (p.1 + 1) 0 p.2.1 ++ [false])
        (encPair encUnary (encPair encBits encBits)) encBits := by
      polytime [BitString.listRow]
    exact HalfGates.hashWord_polyTime hf (ComputableInPolyTime.fst _ _) h1
      (ComputableInPolyTime.snd _ _).snd'
  exact h.comp (hk.prod (ha.prod ht))

attribute [local fun_prop] keyHashWord_polyTime PointPermute.tweak_polyTime
  PointPermute.wireWidth_polyTime

private theorem propagateWordStep_polyTime :
    ComputableInPolyTime (fun p : ((ℕ × List Bool) × List (List Bool)) × (ℕ × ℕ × List Bool) =>
        propagateWordStep p.1.1.1 p.1.1.2 p.1.2 p.2)
      (encPair (encPair (encPair encUnary encBits) (encList encBits))
        (encPair encNat (encPair encNat encBits))) (encList encBits) := by
  polytime [propagateWordStep, baseWord, isXorTable, BitString.listRow]

private abbrev encEvalGateIn :
    (((ℕ × ℕ × List Bool) × (List (List Bool) × ℕ)) × ℕ) ↪ List Bool :=
  encPair (encPair (encPair encUnary (encPair encUnary encBits))
    (encPair (encList encBits) encUnary)) encUnary

include hf in
private theorem evalUnmasked_polyTime :
    ComputableInPolyTime (fun p : (ℕ × ℕ × ℕ) × (List Bool × List Bool × List Bool) =>
        evalUnmasked hash p.1.1 p.1.2.1 p.1.2.2 p.2.1 p.2.2.1 p.2.2.2)
      (encPair (encPair encUnary (encPair encUnary encUnary))
        (encPair encBits (encPair encBits encBits))) encBits := by
  polytime [evalUnmasked, HalfGates.colourWord]

include hf in
private theorem evalGateCut_polyTime :
    ComputableInPolyTime (fun p : ((ℕ × ℕ × List Bool) × (List (List Bool) × ℕ)) × ℕ =>
        evalGateCut hash p.1.1.1 p.1.1.2.1 p.1.1.2.2 p.1.2 p.2)
      encEvalGateIn (encPair (encList encBits) encUnary) := by
  have hp := ComputableInPolyTime.fst (encPair (encPair encUnary (encPair encUnary encBits))
    (encPair (encList encBits) encUnary)) encUnary
  have hg := ComputableInPolyTime.snd (encPair (encPair encUnary (encPair encUnary encBits))
    (encPair (encList encBits) encUnary)) encUnary
  have hk := hp.fst'.fst'
  have hw := hp.fst'.snd'.fst'
  have hlabels := hp.snd'.fst'
  have hpos := hp.snd'.snd'
  have hblock := ComputableInPolyTime.bitsDropWithInput hp.fst'.snd'.snd' hpos
  have ha := HalfGates.labelAt_polyTime hlabels (ComputableInPolyTime.bitsTakeWithInput hblock hw)
  have hb := HalfGates.labelAt_polyTime hlabels (ComputableInPolyTime.bitsTakeWithInput
    (ComputableInPolyTime.bitsDropWithInput hblock hw) hw)
  have h2w : ComputableInPolyTime (fun x : ((ℕ × ℕ × List Bool) × (List (List Bool) × ℕ)) × ℕ =>
      2 * (x.1.1.2.1)) encEvalGateIn encUnary := by polytime
  have hstepXor : ComputableInPolyTime
      (fun x : ((ℕ × ℕ × List Bool) × (List (List Bool) × ℕ)) × ℕ => 2 * x.1.1.2.1 + 1)
      encEvalGateIn encUnary := by polytime
  have hstepNo : ComputableInPolyTime
      (fun x : ((ℕ × ℕ × List Bool) × (List (List Bool) × ℕ)) × ℕ =>
        2 * x.1.1.2.1 + 1 + 4 * (x.1.1.1 + 2)) encEvalGateIn encUnary := by polytime
  have hunmasked := (evalUnmasked_polyTime hf).comp
    ((hk.prod (hw.prod hg)).prod (hblock.prod (ha.prod hb)))
  have hnil : ComputableInPolyTime
      (fun _ : ((ℕ × ℕ × List Bool) × (List (List Bool) × ℕ)) × ℕ => ([] : List (List Bool)))
      encEvalGateIn (encList encBits) := ComputableInPolyTime.const _
  exact ComputableInPolyTime.ite' (ComputableInPolyTime.bitsGetDWithInput hblock h2w false)
    ((ComputableInPolyTime.listAppend' hlabels
      (ComputableInPolyTime.cons' (HalfGates.xorCut_polyTime hk ha hb) hnil)).prod
      (ComputableInPolyTime.unary_add' hpos hstepXor))
    ((ComputableInPolyTime.listAppend' hlabels (ComputableInPolyTime.cons' hunmasked hnil)).prod
      (ComputableInPolyTime.unary_add' hpos hstepNo))

include hf in
private theorem evalWord_polyTime :
    ComputableInPolyTime (fun (F, X) => evalWord hash F X) (encPair encBits encBits) encBits := by
  have hdec : ComputableInPolyTime (fun p : List Bool × List Bool =>
      PointPermute.fnDecoder.decode p.1) (encPair encBits encBits) PointPermute.encFn :=
    PointPermute.fnDecoder.computableInPolyTime.comp (ComputableInPolyTime.fst _ _)
  have hk := hdec.fst'.fst'
  have hw := PointPermute.wireWidth_polyTime hdec.fst'.snd'.fst' hdec.fst'.snd'.snd'.snd'
  have hgrowth : ComputableInPolyTime (fun p : List Bool × List Bool =>
      8 * ((PointPermute.fnDecoder.decode p.1).1.1 + 2) +
        2 * PointPermute.wireWidth (PointPermute.fnDecoder.decode p.1).1.2.1
          (PointPermute.fnDecoder.decode p.1).1.2.2.2 + 10) (encPair encBits encBits) encUnary := by
    polytime
  have hfold := ComputableInPolyTime.foldlWith_of_bounded_growth
    (encP := encPair encUnary (encPair encUnary encBits)) (encL := encList encUnary)
    (encB := encPair (encList encBits) encUnary) (encA := encUnary)
    (encIn := encPair encBits encBits)
    (step := fun par state g => evalGateCut hash par.1 par.2.1 par.2.2 state g)
    (par := fun p : List Bool × List Bool => ((PointPermute.fnDecoder.decode p.1).1.1,
      PointPermute.wireWidth (PointPermute.fnDecoder.decode p.1).1.2.1
        (PointPermute.fnDecoder.decode p.1).1.2.2.2, (PointPermute.fnDecoder.decode p.1).2))
    (list := fun p => List.range (PointPermute.fnDecoder.decode p.1).1.2.2.2)
    (init := fun p => (BitString.listRows (PointPermute.fnDecoder.decode p.1).1.2.1
      ((PointPermute.fnDecoder.decode p.1).1.1 + 2) p.2, 0))
    (hk.prod (hw.prod hdec.snd')) (by polytime)
    (by polytime [BitString.listRows, BitString.listRow])
    (evalGateCut_polyTime hf)
    (hgrowth.polyBounded_length.mono fun p => by simp)
    (fun p state g _ => length_evalGateCut_le hash _ _ _ _ _)
  have heq : (fun (F, X) => evalWord hash F X) = fun p : List Bool × List Bool =>
      ((((List.range (PointPermute.fnDecoder.decode p.1).1.2.2.2).foldl
        (fun state g => evalGateCut hash (PointPermute.fnDecoder.decode p.1).1.1
          (PointPermute.wireWidth (PointPermute.fnDecoder.decode p.1).1.2.1
            (PointPermute.fnDecoder.decode p.1).1.2.2.2)
          (PointPermute.fnDecoder.decode p.1).2 state g)
        (BitString.listRows (PointPermute.fnDecoder.decode p.1).1.2.1
          ((PointPermute.fnDecoder.decode p.1).1.1 + 2) p.2, 0)).1).drop
        ((PointPermute.fnDecoder.decode p.1).1.2.1 + (PointPermute.fnDecoder.decode p.1).1.2.2.2 -
          (PointPermute.fnDecoder.decode p.1).1.2.2.1)).flatten := by
    funext p
    have hinit : ∀ l ∈ (BitString.listRows (PointPermute.fnDecoder.decode p.1).1.2.1
        ((PointPermute.fnDecoder.decode p.1).1.1 + 2) p.2, 0).1,
        l.length ≤ (PointPermute.fnDecoder.decode p.1).1.1 + 2 := by
      intro l hl
      simp only [BitString.listRows, List.mem_map] at hl
      obtain ⟨i, -, rfl⟩ := hl
      simp
    rw [← foldl_evalGate_eq hash _ _ _ _ _ hinit]
    rfl
  rw [heq]
  have hc : ComputableInPolyTime (fun p : List Bool × List Bool =>
      (PointPermute.fnDecoder.decode p.1).1.2.1 + (PointPermute.fnDecoder.decode p.1).1.2.2.2 -
        (PointPermute.fnDecoder.decode p.1).1.2.2.1) (encPair encBits encBits) encUnary := by
    polytime
  have hfin : ComputableInPolyTime (fun p : List (List Bool) × ℕ => (p.1.drop p.2).flatten)
      (encPair (encList encBits) encUnary) encBits :=
    ComputableInPolyTime.bitsFlatten (ComputableInPolyTime.listDropWithInput
      (ComputableInPolyTime.fst _ _) (ComputableInPolyTime.snd _ _))
  exact hfin.comp (hfold.fst'.prod hc)

private abbrev encGbInput : (ℕ × ValidCircuit × List Bool) ↪ List Bool :=
  encPair encUnary (encPair encValidCircuit encBits)

private theorem data_polyTime :
    ComputableInPolyTime (fun x : ℕ × ValidCircuit × List Bool =>
      (x.2.1.1.n, x.2.1.1.m, x.2.1.1.gateList)) encGbInput encCircuitData :=
  circuitData_polyTime.comp (ComputableInPolyTime.snd _ _).fst'

private theorem offset_polyTime :
    ComputableInPolyTime (fun x : ℕ × ValidCircuit × List Bool =>
      HalfGates.offsetWord x.1 x.2.2) encGbInput encBits := by
  have hk := ComputableInPolyTime.fst encUnary (encPair encValidCircuit encBits)
  have hcoins := (ComputableInPolyTime.snd encUnary (encPair encValidCircuit encBits)).snd'
  polytime [HalfGates.offsetWord, BitString.listRow]

private theorem propagateWords_polyTime :
    ComputableInPolyTime (fun x : ℕ × ValidCircuit × List Bool =>
      propagateWords x.1 x.2.1.1 x.2.2 x.2.1.1.q) encGbInput (encList encBits) := by
  have hk := ComputableInPolyTime.fst encUnary (encPair encValidCircuit encBits)
  have hcoins := (ComputableInPolyTime.snd encUnary (encPair encValidCircuit encBits)).snd'
  have hn := data_polyTime.fst'
  have hinit : ComputableInPolyTime (fun x : ℕ × ValidCircuit × List Bool =>
      (List.range x.2.1.1.n).map (HalfGates.inputWord x.1 x.2.2)) encGbInput (encList encBits) := by
    polytime [HalfGates.inputWord, BitString.listRow]
  have hgrowth : ComputableInPolyTime (fun x : ℕ × ValidCircuit × List Bool =>
      2 * (x.1 + 2) + 1) encGbInput encUnary := by
    polytime
  have hfold := ComputableInPolyTime.foldlWith_of_bounded_growth
    (encP := encPair encUnary encBits)
    (encL := encList (encPair encNat (encPair encNat encBits))) (encB := encList encBits)
    (encA := encPair encNat (encPair encNat encBits)) (encIn := encGbInput)
    (step := fun par ws gate => propagateWordStep par.1 par.2 ws gate)
    (par := fun x => (x.1, x.2.2))
    (list := fun x => x.2.1.1.gateList)
    (init := fun x => (List.range x.2.1.1.n).map (HalfGates.inputWord x.1 x.2.2))
    (hk.prod hcoins) data_polyTime.snd'.snd' hinit propagateWordStep_polyTime
    (growth := fun x => 2 * (x.1 + 2) + 1) (hgrowth.polyBounded_length.mono fun x => by simp)
    (fun x ws gate _ => by
      simp only [propagateWordStep, length_encList, List.map_append, List.sum_append,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, encBits_apply]
      split
      · simp only [List.length_take]; omega
      · simp [baseWord])
  have heq : (fun x : ℕ × ValidCircuit × List Bool =>
      propagateWords x.1 x.2.1.1 x.2.2 x.2.1.1.q) = fun x =>
      x.2.1.1.gateList.foldl (propagateWordStep x.1 x.2.2)
        ((List.range x.2.1.1.n).map (HalfGates.inputWord x.1 x.2.2)) := by
    funext x
    rw [propagateWords_eq_foldl _ _ _ le_rfl,
      List.take_of_length_le (ConventionalCircuit.length_gateList _).le]
  rw [heq]
  exact hfold

private theorem isXorTable_polyTime : ComputableInPolyTime isXorTable encBits encBool := by
  polytime [isXorTable]

include hf in
private theorem rowFromTable_polyTime :
    ComputableInPolyTime (fun p : (ℕ × List Bool × List Bool × List Bool) ×
        (List Bool × List Bool × ℕ × ℕ) =>
        rowFromTable hash p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2
          p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)
      (encPair (encPair encUnary (encPair encBits (encPair encBits encBits)))
        (encPair encBits (encPair encBits (encPair encUnary encUnary)))) encBits := by
  polytime [rowFromTable, HalfGates.maskWord, HalfGates.colourWord]

include hf in
private theorem gateRow_polyTime {γ : Type} {encIn : γ ↪ List Bool} {k n g a b i : γ → ℕ}
    {Δ table : γ → List Bool} {labels : γ → List (List Bool)}
    (hk : ComputableInPolyTime k encIn encUnary) (hn : ComputableInPolyTime n encIn encUnary)
    (hΔ : ComputableInPolyTime Δ encIn encBits)
    (hlabels : ComputableInPolyTime labels encIn (encList encBits))
    (htable : ComputableInPolyTime table encIn encBits)
    (hg : ComputableInPolyTime g encIn encUnary) (ha : ComputableInPolyTime a encIn encUnary)
    (hb : ComputableInPolyTime b encIn encUnary) (hi : ComputableInPolyTime i encIn encUnary) :
    ComputableInPolyTime (fun x => gateRow hash (k x) (n x) (Δ x) (labels x) (table x)
      (g x) (a x) (b x) (i x)) encIn encBits := by
  have hisXor := isXorTable_polyTime.comp htable
  have hi0 : ComputableInPolyTime (fun x => decide (i x = 0)) encIn encBool := by polytime
  have hsing : ComputableInPolyTime (fun b : Bool => [b]) encBool encBits := by polytime
  have hpre : ComputableInPolyTime (fun x => if i x = 0 then [isXorTable (table x)] else [])
      encIn encBits := by
    have h := ComputableInPolyTime.ite' hi0 (hsing.comp hisXor) (ComputableInPolyTime.const [])
    rwa [show (fun x => if decide (i x = 0) = true then ((fun b => [b]) ∘ isXorTable ∘ table) x
        else []) = (fun x => if i x = 0 then [isXorTable (table x)] else []) from
      funext fun x => by simp] at h
  have hrow := (rowFromTable_polyTime hf).comp
    ((hk.prod (hΔ.prod ((ComputableInPolyTime.listGetDWithInput hlabels ha []).prod
      (ComputableInPolyTime.listGetDWithInput hlabels hb [])))).prod
      ((ComputableInPolyTime.listGetDWithInput hlabels (ComputableInPolyTime.unary_add' hn hg)
        []).prod (htable.prod (hg.prod hi))))
  have hpost : ComputableInPolyTime (fun x => if isXorTable (table x) then [] else
      rowFromTable hash (k x) (Δ x) ((labels x).getD (a x) []) ((labels x).getD (b x) [])
        ((labels x).getD (n x + g x) []) (table x) (g x) (i x)) encIn encBits :=
    ComputableInPolyTime.ite' hisXor (ComputableInPolyTime.const []) hrow
  exact ComputableInPolyTime.bitsAppend hpre hpost

include hf in
private theorem fnWord_polyTime :
    ComputableInPolyTime (fun x : ℕ × ValidCircuit × List Bool =>
      fnWord hash x.1 x.2.1.1 x.2.2) encGbInput encBits := by
  have hd := data_polyTime
  have hP := propagateWords_polyTime
  have hn := hd.fst'
  have hm := hd.snd'.fst'
  have hg := hd.snd'.snd'
  have hq := (ComputableInPolyTime.length_list _).comp hg
  have hk := ComputableInPolyTime.fst encUnary (encPair encValidCircuit encBits)
  have hx := ComputableInPolyTime.fst encGbInput
    (encPair encUnary (encPair encUnary (encPair encUnary encUnary)))
  have hrest := ComputableInPolyTime.snd encGbInput
    (encPair encUnary (encPair encUnary (encPair encUnary encUnary)))
  have hgi := hrest.fst'
  have htable := (ComputableInPolyTime.listGetDWithInput (hg.comp hx) hgi (0, 0, [])).snd'.snd'
  have hrow := gateRow_polyTime hf (hk.comp hx) (hn.comp hx) (offset_polyTime.comp hx)
    (hP.comp hx) htable hgi hrest.snd'.fst' hrest.snd'.snd'.fst' hrest.snd'.snd'.snd'
  have hgate := ComputableInPolyTime.listGetDWithInput
    (hg.comp (ComputableInPolyTime.fst encGbInput encUnary)) (ComputableInPolyTime.snd _ _)
    (0, 0, [])
  have hcap : ComputableInPolyTime (fun x : ℕ × ValidCircuit × List Bool =>
      (propagateWords x.1 x.2.1.1 x.2.2 x.2.1.1.q).length + 1) encGbInput encUnary := by
    polytime
  have hbody := PointPermute.bodyWith_polyTime
    (n := fun x : ℕ × ValidCircuit × List Bool => x.2.1.1.n)
    (q := fun x => x.2.1.1.gateList.length)
    (cap := fun x => (propagateWords x.1 x.2.1.1 x.2.2 x.2.1.1.q).length + 1)
    (A := fun x g => (x.2.1.1.gateList.getD g (0, 0, [])).1)
    (B := fun x g => (x.2.1.1.gateList.getD g (0, 0, [])).2.1)
    (row := fun x g a b i => gateRow hash x.1 x.2.1.1.n (HalfGates.offsetWord x.1 x.2.2)
      (propagateWords x.1 x.2.1.1 x.2.2 x.2.1.1.q) ((x.2.1.1.gateList.getD g (0, 0, [])).2.2)
      g a b i)
    hn hq hcap hgate.fst' hgate.snd'.fst' hrow
  have hhead : ComputableInPolyTime (fun x : ℕ × ValidCircuit × List Bool =>
      (x.1, x.2.1.1.n, x.2.1.1.m, x.2.1.1.gateList.length)) encGbInput PointPermute.encHeader :=
    hk.prod (hn.prod (hm.prod hq))
  have henc : ComputableInPolyTime (fun y : (ℕ × ℕ × ℕ × ℕ) × List Bool => PointPermute.encFn y)
      PointPermute.encFn encBits := .of_eq fun _ => rfl
  simp only [fnWord_eq]
  exact henc.comp (hhead.prod hbody)

/-- The encoding information is computed in polynomial time. -/
private theorem encInfoWord_polyTime :
    ComputableInPolyTime (fun x : ℕ × ValidCircuit × List Bool =>
      HalfGates.encInfoWord x.1 x.2.1.1 x.2.2) encGbInput encBits :=
  HalfGates.encInfoWord_polyTime_of (ComputableInPolyTime.fst _ _) data_polyTime.fst'
    (ComputableInPolyTime.snd encUnary (encPair encValidCircuit encBits)).snd'

private theorem decInfoWord_polyTime :
    ComputableInPolyTime (fun x : ℕ × ValidCircuit × List Bool =>
      decInfoWord x.1 x.2.1.1 x.2.2) encGbInput encBits := by
  have hrange : ComputableInPolyTime (fun p : ℕ × ℕ × ℕ × List (List Bool) =>
      (List.range p.2.1).map fun o => HalfGates.colourWord p.1 (p.2.2.2.getD (p.2.2.1 + o) []))
      (encPair encUnary (encPair encUnary (encPair encUnary (encList encBits)))) encBits := by
    polytime [HalfGates.colourWord]
  have hd := data_polyTime
  have hs : ComputableInPolyTime (fun x : ℕ × ValidCircuit × List Bool =>
      x.2.1.1.n + x.2.1.1.q - x.2.1.1.m) encGbInput encUnary := by
    have hn := hd.fst'
    have hm := hd.snd'.fst'
    have hq : ComputableInPolyTime (fun x : ℕ × ValidCircuit × List Bool => x.2.1.1.q)
        encGbInput encUnary := by
      simpa only [Function.comp_def, ConventionalCircuit.length_gateList] using
        (ComputableInPolyTime.length_list _).comp hd.snd'.snd'
    polytime
  have heq : (fun x : ℕ × ValidCircuit × List Bool => decInfoWord x.1 x.2.1.1 x.2.2) =
      fun x => (List.range x.2.1.1.m).map fun o => HalfGates.colourWord x.1
        ((propagateWords x.1 x.2.1.1 x.2.2 x.2.1.1.q).getD
          (x.2.1.1.n + x.2.1.1.q - x.2.1.1.m + o) []) := by
    funext x
    rw [decInfoWord, List.map_range_eq_ofFn]
  rw [heq]
  exact hrange.comp ((ComputableInPolyTime.fst _ _).prod (hd.snd'.fst'.prod
    (hs.prod propagateWords_polyTime)))

include hf in
private theorem gb_polyTime :
    ComputableInPolyTime (fun (k, f, coins) => (scheme hash).gb k f coins) encGbInput
      Scheme.encGarbled :=
  Scheme.encGarbled_mk_polyTime (fnWord_polyTime hf) encInfoWord_polyTime decInfoWord_polyTime

private theorem coins_polyTime :
    ComputableInPolyTime (fun (k, f) => (scheme hash).coins k f)
      (encPair encUnary encValidCircuit) encUnary := by
  have hk := ComputableInPolyTime.fst encUnary encValidCircuit
  have hd := circuitData_polyTime.comp (ComputableInPolyTime.snd encUnary encValidCircuit)
  have hn : ComputableInPolyTime (fun x : ℕ × ValidCircuit => x.2.1.n)
      (encPair encUnary encValidCircuit) encUnary := hd.fst'
  have hq : ComputableInPolyTime (fun x : ℕ × ValidCircuit => x.2.1.q)
      (encPair encUnary encValidCircuit) encUnary := by
    simpa only [Function.comp_def, ConventionalCircuit.length_gateList] using
      (ComputableInPolyTime.length_list _).comp hd.snd'.snd'
  have heq : (fun (k, f) => (scheme hash).coins k f) = fun x : ℕ × ValidCircuit =>
      (x.1 + 1) + (x.2.1.n + x.2.1.q) * (x.1 + 2) := by
    funext x
    rfl
  rw [heq]
  polytime

include hf in
/-- **Free-XOR garbling is efficient** for every hash family computed in polynomial time
(`CircularCorrelationRobust.polyTime` supplies `hf`): the length readers `n` and `m`, the number of
coins and the garbler on `(1^k, f, r)`, and `En`, `Ev`, `De` and `ev` on their encoded arguments,
run in polynomial time, for valid conventional circuits encoded by `encValidCircuit`. -/
theorem scheme_isEfficient : (scheme hash).IsEfficient encValidCircuit where
  inLen := circuitData_polyTime.fst'
  outLen := circuitData_polyTime.snd'.fst'
  coins := coins_polyTime
  gb := gb_polyTime hf
  encode := projectiveEncode_polyTime
  evalGarbled := evalWord_polyTime hf
  decode := PointPermute.decodeWord_polyTime
  ev := evalCirc_polyTime

end Cslib.Crypto.Garbling.FreeXOR
