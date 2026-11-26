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
* `Cslib.Crypto.Garbling.FreeXOR.xorFlags`: XOR gate flags projected from four-bit gate records
  via `isXorTable`.

## Main results

* `Cslib.Crypto.Garbling.FreeXOR.scheme_isEfficient`: Free-XOR garbling is efficient.
* `Cslib.Crypto.Garbling.FreeXOR.phiXor_compatible`: `phiXor` agrees with `scheme`'s length
  readers.
* `Cslib.Crypto.Garbling.FreeXOR.xorFlags_polyTime`: `xorFlags` is computed in polynomial time.
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

/-- Library infrastructure (no cited result): `isXorTable` is computed in polynomial time. -/
theorem isXorTable_polyTime : ComputableInPolyTime isXorTable encBits encBool := by
  polytime [isXorTable]

/-- Library construction (no cited definition): XOR-gate flags projected from four-bit gate
records `(A, B, tt)` via `isXorTable`. -/
@[expose] def xorFlags (gates : List (ℕ × ℕ × List Bool)) : List Bool :=
  gates.map fun (_, _, tt) => isXorTable tt

/-- Library infrastructure (no cited result): `xorFlags` on a valid circuit's gate list equals
`(phiXor.phi f).free`. -/
theorem xorFlags_gateList (f : ValidCircuit) : xorFlags f.1.gateList = (phiXor.phi f).free := by
  simp only [xorFlags, phiXor, ConventionalCircuit.gateList, List.map_ofFn]
  exact congrArg List.ofFn (funext fun g => isXorTable_eq (f.1.G g))

/-- Library infrastructure (no cited result): `xorFlags` is computed in polynomial time. -/
theorem xorFlags_polyTime :
    ComputableInPolyTime xorFlags (encList (encPair encNat (encPair encNat encBits))) encBits := by
  exact (by polytime : ComputableInPolyTime (fun l : List Bool => l) (encList encBool) encBits).comp
    (by polytime [isXorTable])

/-- `phiXor` runs in polynomial time from `encValidCircuit`. -/
theorem phiXor_polyTime : ComputableInPolyTime phiXor.phi encValidCircuit encXorTopology :=
  encXorTopology_mk_polyTime phiTopo_polyTime <| by
    rw [show (fun f : ValidCircuit => List.ofFn fun g => isXorGate f.1 g) =
        fun f => xorFlags f.1.gateList from funext fun f => (xorFlags_gateList f).symm]
    exact xorFlags_polyTime.comp circuitData_polyTime.snd'.snd'

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
    rw [List.take_add_one, List.foldl_append, ← ih hsq.le, propagateWords, simPropWords,
      dite_eq_left (show s < f.topo.q from hsq)]
    simp only [ConventionalCircuit.gateList, List.getElem?_ofFn, hsq, ↓reduceDIte,
      Option.toList_some, List.foldl_cons, List.foldl_nil, propagateWordStep,
      List.getD_min_length_succ_sub_one, isXorTable_eq, ConventionalCircuit.topo]
    rw [length_propagateWords k f coins hsq.le,
      show (List.ofFn (isXorGate f)).getD s false = isXorGate f ⟨s, hsq⟩ by
        simp [List.getD_eq_getElem?_getD, hsq]]
    by_cases hxor : isXorGate f ⟨s, hsq⟩ = true
    · rw [ite_eq_left hxor, ite_eq_left (show decide (f.G ⟨s, hsq⟩ = xor) = true from hxor)]
      have ha := HalfGates.length_getD_le (length_le_of_mem_propagateWords k f coins s)
        (f.A ⟨s, hsq⟩ - 1)
      rw [List.take_of_length_le (by rw [List.length_zipWith]; omega)]; rfl
    · rw [ite_eq_right hxor, ite_eq_right (show ¬ decide (f.G ⟨s, hsq⟩ = xor) = true from hxor)]
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
  dsimp only at hstate
  simp only [evalGate, evalGateCut, evalUnmasked]
  split
  · have hzip : (List.zipWith xor
        (labels.getD
          (BitString.boundedBinaryValue labels.length ((body.drop pos).take w).reverse - 1) [])
        (labels.getD
          (BitString.boundedBinaryValue labels.length (((body.drop pos).drop w).take w).reverse - 1)
          [])).length ≤ k + 2 := by
      have := HalfGates.length_getD_le hstate
        (BitString.boundedBinaryValue labels.length ((body.drop pos).take w).reverse - 1)
      rw [List.length_zipWith]; omega
    exact ⟨by rw [List.take_of_length_le hzip], fun l hl =>
      (List.mem_append.mp hl).elim (hstate l) fun hl => (List.mem_singleton.mp hl) ▸ hzip⟩
  · exact ⟨rfl, fun l hl => (List.mem_append.mp hl).elim (hstate l) fun hl => by
      rw [List.mem_singleton.mp hl]
      simp only [List.length_zipWith, List.length_take]
      omega⟩

private theorem foldl_evalGate_eq (k w : ℕ) (body : List Bool) (gates : List ℕ) :
    ∀ state : List (List Bool) × ℕ, (∀ l ∈ state.1, l.length ≤ k + 2) →
      gates.foldl (evalGate hash k w body) state =
        gates.foldl (evalGateCut hash k w body) state := by
  induction gates with
  | nil => exact fun _ _ => rfl
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
  split <;>
    simp only [length_encPair, length_encList, List.map_append, List.sum_append, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, encBits_apply, encUnary_apply,
      List.length_replicate, List.length_zipWith, List.length_take] <;> omega

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
  by_cases hxor : f.G g = xor <;> simp [isXorGate, hxor]

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
    ComputableInPolyTime (fun x => keyHashWord hash (k x) (a x) (t x)) encIn encBits :=
  (HalfGates.hashWord_polyTime hf (ComputableInPolyTime.fst _ _)
    (by polytime [BitString.listRow] : ComputableInPolyTime (fun p : ℕ × List Bool × List Bool =>
      BitString.listRow (p.1 + 1) 0 p.2.1 ++ [false])
      (encPair encUnary (encPair encBits encBits)) encBits)
    (ComputableInPolyTime.snd _ _).snd').comp (hk.prod (ha.prod ht))

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
  have hblock := hp.fst'.snd'.snd'.bitsDropWithInput hp.snd'.snd'
  have ha := HalfGates.labelAt_polyTime hp.snd'.fst' (hblock.bitsTakeWithInput hp.fst'.snd'.fst')
  have hb := HalfGates.labelAt_polyTime hp.snd'.fst'
    ((hblock.bitsDropWithInput hp.fst'.snd'.fst').bitsTakeWithInput hp.fst'.snd'.fst')
  have hnil : ComputableInPolyTime
      (fun _ : ((ℕ × ℕ × List Bool) × (List (List Bool) × ℕ)) × ℕ => ([] : List (List Bool)))
      encEvalGateIn (encList encBits) := .const _
  exact ComputableInPolyTime.ite' (hblock.bitsGetDWithInput (by polytime) false)
    ((hp.snd'.fst'.listAppend'
      ((HalfGates.xorCut_polyTime hp.fst'.fst' ha hb).cons' hnil)).prod
      (hp.snd'.snd'.unary_add' (by polytime)))
    ((hp.snd'.fst'.listAppend'
      (((evalUnmasked_polyTime hf).comp
        ((hp.fst'.fst'.prod (hp.fst'.snd'.fst'.prod hg)).prod (hblock.prod (ha.prod hb)))).cons'
        hnil)).prod
      (hp.snd'.snd'.unary_add' (by polytime)))

include hf in
private theorem evalWord_polyTime :
    ComputableInPolyTime (fun (F, X) => evalWord hash F X) (encPair encBits encBits) encBits := by
  have hdec : ComputableInPolyTime (fun p : List Bool × List Bool =>
      PointPermute.fnDecoder.decode p.1) (encPair encBits encBits) PointPermute.encFn :=
    PointPermute.fnDecoder.computableInPolyTime.comp (ComputableInPolyTime.fst _ _)
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
    (hdec.fst'.fst'.prod ((PointPermute.wireWidth_polyTime hdec.fst'.snd'.fst'
      hdec.fst'.snd'.snd'.snd').prod hdec.snd'))
    (by polytime)
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
          (PointPermute.fnDecoder.decode p.1).1.2.2.1)).flatten := funext fun p => by
    rw [← foldl_evalGate_eq hash _ _ _ _ _ fun l hl => by
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hl
      simp]
    rfl
  rw [heq]
  exact (ComputableInPolyTime.bitsFlatten (ComputableInPolyTime.listDropWithInput
    (ComputableInPolyTime.fst _ _) (ComputableInPolyTime.snd _ _))).comp
    (hfold.fst'.prod (by polytime))

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
  have hgrowth : ComputableInPolyTime (fun x : ℕ × ValidCircuit × List Bool =>
      2 * (x.1 + 2) + 1) encGbInput encUnary := by polytime
  have hprop : (fun x : ℕ × ValidCircuit × List Bool =>
      propagateWords x.1 x.2.1.1 x.2.2 x.2.1.1.q) = fun x =>
      x.2.1.1.gateList.foldl (propagateWordStep x.1 x.2.2)
        ((List.range x.2.1.1.n).map (HalfGates.inputWord x.1 x.2.2)) := funext fun x => by
    rw [propagateWords_eq_foldl _ _ _ le_rfl,
      List.take_of_length_le (ConventionalCircuit.length_gateList _).le]
  rw [hprop]
  exact ComputableInPolyTime.foldlWith_of_bounded_growth
    (encP := encPair encUnary encBits)
    (encL := encList (encPair encNat (encPair encNat encBits))) (encB := encList encBits)
    (encA := encPair encNat (encPair encNat encBits)) (encIn := encGbInput)
    (step := fun par ws gate => propagateWordStep par.1 par.2 ws gate)
    (par := fun x => (x.1, x.2.2))
    (list := fun x => x.2.1.1.gateList)
    (init := fun x => (List.range x.2.1.1.n).map (HalfGates.inputWord x.1 x.2.2))
    (hk.prod hcoins) data_polyTime.snd'.snd'
    (by polytime [HalfGates.inputWord, BitString.listRow]) propagateWordStep_polyTime
    (growth := fun x => 2 * (x.1 + 2) + 1) (hgrowth.polyBounded_length.mono fun x => by simp)
    fun x ws gate _ => by
      simp only [propagateWordStep, length_encList, List.map_append, List.sum_append,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, encBits_apply]
      split
      · simp only [List.length_take]; omega
      · simp [baseWord]

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
  have hpre : ComputableInPolyTime (fun x => if i x = 0 then [isXorTable (table x)] else [])
      encIn encBits := by
    have h := ComputableInPolyTime.ite' (by polytime : ComputableInPolyTime
      (fun x => decide (i x = 0)) encIn encBool)
      ((by polytime : ComputableInPolyTime (fun b : Bool => [b]) encBool encBits).comp hisXor)
      (.const [])
    rwa [show (fun x => if decide (i x = 0) = true then ((fun b => [b]) ∘ isXorTable ∘ table) x
        else []) = (fun x => if i x = 0 then [isXorTable (table x)] else []) from
      funext fun x => by simp] at h
  exact hpre.bitsAppend (ComputableInPolyTime.ite' hisXor (.const [])
    ((rowFromTable_polyTime hf).comp
      ((hk.prod (hΔ.prod ((hlabels.listGetDWithInput ha []).prod
        (hlabels.listGetDWithInput hb [])))).prod
        ((hlabels.listGetDWithInput (hn.unary_add' hg) []).prod (htable.prod (hg.prod hi))))))

include hf in
private theorem fnWord_polyTime :
    ComputableInPolyTime (fun x : ℕ × ValidCircuit × List Bool =>
      fnWord hash x.1 x.2.1.1 x.2.2) encGbInput encBits := by
  have hd := data_polyTime
  have hP := propagateWords_polyTime
  have hg := hd.snd'.snd'
  have hq := (ComputableInPolyTime.length_list _).comp hg
  have hk := ComputableInPolyTime.fst encUnary (encPair encValidCircuit encBits)
  have hx := ComputableInPolyTime.fst encGbInput
    (encPair encUnary (encPair encUnary (encPair encUnary encUnary)))
  have hrest := ComputableInPolyTime.snd encGbInput
    (encPair encUnary (encPair encUnary (encPair encUnary encUnary)))
  have hgate := (hg.comp (ComputableInPolyTime.fst encGbInput encUnary)).listGetDWithInput
    (ComputableInPolyTime.snd _ _) (0, 0, [])
  simp only [fnWord_eq]
  exact (ComputableInPolyTime.of_eq (encIn := PointPermute.encFn) (encOut := encBits)
    (f := fun y : (ℕ × ℕ × ℕ × ℕ) × List Bool => PointPermute.encFn y) fun _ => rfl).comp
    ((hk.prod (hd.fst'.prod (hd.snd'.fst'.prod hq))).prod
      (PointPermute.bodyWith_polyTime
        (n := fun x : ℕ × ValidCircuit × List Bool => x.2.1.1.n)
        (q := fun x => x.2.1.1.gateList.length)
        (cap := fun x => (propagateWords x.1 x.2.1.1 x.2.2 x.2.1.1.q).length + 1)
        (A := fun x g => (x.2.1.1.gateList.getD g (0, 0, [])).1)
        (B := fun x g => (x.2.1.1.gateList.getD g (0, 0, [])).2.1)
        (row := fun x g a b i => gateRow hash x.1 x.2.1.1.n (HalfGates.offsetWord x.1 x.2.2)
          (propagateWords x.1 x.2.1.1 x.2.2 x.2.1.1.q) ((x.2.1.1.gateList.getD g (0, 0, [])).2.2)
          g a b i)
        hd.fst' hq (by polytime) hgate.fst' hgate.snd'.fst'
        (gateRow_polyTime hf (hk.comp hx) (hd.fst'.comp hx) (offset_polyTime.comp hx)
          (hP.comp hx) (((hg.comp hx).listGetDWithInput hrest.fst' (0, 0, [])).snd'.snd')
          hrest.fst' hrest.snd'.fst' hrest.snd'.snd'.fst' hrest.snd'.snd'.snd')))

/-- The encoding information is computed in polynomial time. -/
private theorem encInfoWord_polyTime :
    ComputableInPolyTime (fun x : ℕ × ValidCircuit × List Bool =>
      HalfGates.encInfoWord x.1 x.2.1.1 x.2.2) encGbInput encBits :=
  HalfGates.encInfoWord_polyTime_of (ComputableInPolyTime.fst _ _) data_polyTime.fst'
    (ComputableInPolyTime.snd encUnary (encPair encValidCircuit encBits)).snd'

private theorem decInfoWord_polyTime :
    ComputableInPolyTime (fun x : ℕ × ValidCircuit × List Bool =>
      decInfoWord x.1 x.2.1.1 x.2.2) encGbInput encBits := by
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
  exact (by polytime [HalfGates.colourWord] :
    ComputableInPolyTime (fun p : ℕ × ℕ × ℕ × List (List Bool) =>
      (List.range p.2.1).map fun o => HalfGates.colourWord p.1 (p.2.2.2.getD (p.2.2.1 + o) []))
      (encPair encUnary (encPair encUnary (encPair encUnary (encList encBits)))) encBits).comp
    ((ComputableInPolyTime.fst _ _).prod (hd.snd'.fst'.prod (hs.prod propagateWords_polyTime)))

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
  have hn := hd.fst'
  have hq : ComputableInPolyTime (fun x : ℕ × ValidCircuit => x.2.1.q)
      (encPair encUnary encValidCircuit) encUnary := by
    simpa only [Function.comp_def, ConventionalCircuit.length_gateList] using
      (ComputableInPolyTime.length_list _).comp hd.snd'.snd'
  change ComputableInPolyTime (fun x : ℕ × ValidCircuit =>
    (x.1 + 1) + (x.2.1.n + x.2.1.q) * (x.1 + 2)) _ _
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
