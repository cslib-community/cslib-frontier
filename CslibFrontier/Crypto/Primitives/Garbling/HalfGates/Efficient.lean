/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.Garbling.HalfGates.Scheme
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
# Half-gates garbling is efficient

`HalfGates.scheme hash` of `CslibFrontier.Crypto.Primitives.Garbling.HalfGates.Scheme` is an
efficient garbling scheme (`Scheme.IsEfficient`) for XOR–AND circuits encoded by
`encXorAndCircuit` whenever the hash family `hash` is computed in polynomial time, as
`CircularCorrelationRobust.polyTime` provides: `HalfGates.scheme_isEfficient`.

`En` and `De` are those of point-and-permute garbling and `ev` is the semantics of conventional
circuits, so their certificates are `projectiveEncode_polyTime`,
`PointPermute.decodeWord_polyTime` and `evalCirc_polyTime`. The garbler computes the
zero labels by a fold over the gates of the encoded circuit whose state grows by one label per
gate, writes the body of the garbled function with `PointPermute.bodyWith`, whose four rows per
gate are here the AND bit, the two ciphertexts of an AND gate and an empty row, and reads the
decoding bits from the zero labels. The evaluator is a fold over the gates whose state is the
labels so far and the position of the next gate's block.

In both folds a new label is cut to `k + 2` bits, which changes nothing since no label has more,
and which bounds the growth of the state; and wire numbers read in binary are capped at one past
the number of labels so far, which changes no lookup (`List.getD_min_length_succ_sub_one`).

A body whose rows read only the gate, its AND bit and the row number, as the bodies written by
the simulator and by the privacy reduction do, is certified once from gate data
(`HalfGates.bodyWith_gateData_polyTime`).

## Main results

* `Cslib.Crypto.Garbling.HalfGates.scheme_isEfficient`: half-gates garbling is efficient.
* `Cslib.Crypto.Garbling.HalfGates.bodyWith_gateData_polyTime`: bodies from gate data whose rows
  read the gate, its AND bit and the row number are computed in polynomial time.
-/

public section

namespace Cslib.Crypto.Garbling

open Turing.MultiTapeTM

namespace HalfGates

section Words

variable (hash : List Bool → List Bool → List Bool)

/-! ### Lengths of labels -/

/-- A defaulted lookup in words of at most `k + 2` bits has at most `k + 2` bits. -/
theorem length_getD_le {k : ℕ} {ws : List (List Bool)}
    (hws : ∀ w ∈ ws, w.length ≤ k + 2) (i : ℕ) : (ws.getD i []).length ≤ k + 2 := by
  rw [List.getD_eq_getElem?_getD]
  cases h : ws[i]? with
  | none => simp
  | some w => exact hws w (List.mem_of_getElem? h)

/-- The evaluator's AND gate writes at most `k + 2` bits. -/
theorem length_andWord_le (k g : ℕ) (TG TE a b : List Bool) :
    (andWord hash k g TG TE a b).length ≤ k + 2 := by
  simp only [andWord, List.length_zipWith, length_hashWord]
  omega

/-- The zero label of a gate has at most `k + 2` bits when its first argument does. -/
private theorem length_zeroGate_le (k g : ℕ) (Δ a b : List Bool) (isAnd : Bool)
    (ha : a.length ≤ k + 2) : (zeroGate hash k g Δ a b isAnd).length ≤ k + 2 := by
  unfold zeroGate
  split
  · exact length_andWord_le hash _ _ _ _ _ _
  · simp only [List.length_zipWith]
    omega

/-- Every zero label word has at most `k + 2` bits. -/
private theorem length_le_of_mem_zeroWords (k : ℕ) (f : ConventionalCircuit) (coins : List Bool)
    (s : ℕ) : ∀ w ∈ zeroWords hash k f coins s, w.length ≤ k + 2 := by
  induction s with
  | zero =>
    intro w hw
    simp only [zeroWords, List.mem_ofFn] at hw
    obtain ⟨i, rfl⟩ := hw
    simp [inputWord]
  | succ s ih =>
    rw [zeroWords]
    split
    · intro w hw
      rcases List.mem_append.mp hw with hw | hw
      · exact ih w hw
      · rw [List.mem_singleton.mp hw]
        exact length_zeroGate_le hash _ _ _ _ _ _ (length_getD_le ih _)
    · exact ih

/-- The first `n + s` zero label words, for `s ≤ q`. -/
private theorem length_zeroWords (k : ℕ) (f : ConventionalCircuit) (coins : List Bool) {s : ℕ}
    (hs : s ≤ f.q) : (zeroWords hash k f coins s).length = f.n + s := by
  induction s with
  | zero => simp [zeroWords]
  | succ s ih =>
    rw [zeroWords, dite_eq_left (show s < f.q by omega), List.length_append, ih (by omega)]
    rfl

/-! ### The zero labels as a fold -/


/-- One gate of the garbler's zero labels, from the gate's data `(A, B, table)`: the zero label of
gate `|ws| - n`, cut to `k + 2` bits, with the argument wires capped at `|ws| + 1`. -/
private def zeroStep (k n : ℕ) (Δ : List Bool) (ws : List (List Bool))
    (gate : ℕ × ℕ × List Bool) : List (List Bool) :=
  ws ++ [(zeroGate hash k (ws.length - n) Δ (ws.getD (min (ws.length + 1) gate.1 - 1) [])
    (ws.getD (min (ws.length + 1) gate.2.1 - 1) []) (gate.2.2.getD 3 false)).take (k + 2)]

/-- **The zero labels in fold form.** The garbler's zero label words of the first `n + s` wires,
`s ≤ q`, are the fold of `zeroStep` over the data of the first `s` gates. -/
private theorem zeroWords_eq_foldl (k : ℕ) (f : ConventionalCircuit) (coins : List Bool) {s : ℕ}
    (hs : s ≤ f.q) :
    zeroWords hash k f coins s =
      (f.gateList.take s).foldl (zeroStep hash k f.n (offsetWord k coins))
      ((List.range f.n).map (inputWord k coins)) := by
  induction s with
  | zero => simp [zeroWords, List.map_range_eq_ofFn]
  | succ s ih =>
    have hsq : s < f.q := hs
    rw [List.take_add_one, List.foldl_append, ← ih hsq.le, zeroWords, dite_eq_left hsq]
    have hget : f.gateList[s]? = some (f.A ⟨s, hsq⟩, f.B ⟨s, hsq⟩,
        [f.G ⟨s, hsq⟩ false false, f.G ⟨s, hsq⟩ false true, f.G ⟨s, hsq⟩ true false,
          f.G ⟨s, hsq⟩ true true]) := by
      simp [ConventionalCircuit.gateList, hsq]
    rw [hget]
    simp only [Option.toList_some, List.foldl_cons, List.foldl_nil, zeroStep,
      List.getD_min_length_succ_sub_one]
    rw [length_zeroWords hash k f coins hsq.le, Nat.add_sub_cancel_left,
      List.take_of_length_le (length_zeroGate_le hash _ _ _ _ _ _
        (length_getD_le (length_le_of_mem_zeroWords hash k f coins s) _))]
    rfl

/-! ### The evaluator as a fold with bounded growth -/


/-- `evalGate` with the label of an XOR gate cut to `k + 2` bits. -/
private def evalGateCut (k w : ℕ) (body : List Bool) (state : List (List Bool) × ℕ) (g : ℕ) :
    List (List Bool) × ℕ :=
  let block := body.drop state.2
  let a := state.1.getD
    (BitString.boundedBinaryValue state.1.length (block.take w).reverse - 1) []
  let b := state.1.getD
    (BitString.boundedBinaryValue state.1.length ((block.drop w).take w).reverse - 1) []
  if block.getD (2 * w) false then
    (state.1 ++ [andWord hash k g ((block.drop (2 * w + 1)).take (k + 2))
      ((block.drop (2 * w + 1 + (k + 2))).take (k + 2)) a b], state.2 + (2 * w + 1 + 2 * (k + 2)))
  else (state.1 ++ [(List.zipWith xor a b).take (k + 2)], state.2 + (2 * w + 1))

/-- On labels of at most `k + 2` bits, one gate of `Ev` is `evalGateCut`, and the new labels have at
most `k + 2` bits. -/
private theorem evalGate_eq_evalGateCut (k w : ℕ) (body : List Bool)
    (state : List (List Bool) × ℕ) (g : ℕ) (hstate : ∀ l ∈ state.1, l.length ≤ k + 2) :
    evalGate hash k w body state g = evalGateCut hash k w body state g ∧
      ∀ l ∈ (evalGate hash k w body state g).1, l.length ≤ k + 2 := by
  obtain ⟨labels, pos⟩ := state
  simp only [evalGate, evalGateCut]
  split
  · refine ⟨rfl, fun l hl => ?_⟩
    rcases List.mem_append.mp hl with hl | hl
    · exact hstate l hl
    · rw [List.mem_singleton.mp hl]
      exact length_andWord_le hash _ _ _ _ _ _
  · have hzip (a b : List Bool) (ha : a.length ≤ k + 2) :
        (List.zipWith xor a b).length ≤ k + 2 := by
      rw [List.length_zipWith]
      omega
    refine ⟨by rw [List.take_of_length_le (hzip _ _ (length_getD_le hstate _))],
      fun l hl => ?_⟩
    rcases List.mem_append.mp hl with hl | hl
    · exact hstate l hl
    · rw [List.mem_singleton.mp hl]
      exact hzip _ _ (length_getD_le hstate _)

/-- On labels of at most `k + 2` bits, `Ev`'s fold is the fold of `evalGateCut`. -/
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

/-- One gate of `evalGateCut` adds at most one label of `k + 2` bits and moves by at most one
block. -/
private theorem length_evalGateCut_le (k w : ℕ) (body : List Bool)
    (state : List (List Bool) × ℕ) (g : ℕ) :
    (encPair (encList encBits) encUnary (evalGateCut hash k w body state g)).length ≤
      (encPair (encList encBits) encUnary state).length + (8 * (k + 2) + 2 * w + 4) := by
  obtain ⟨labels, pos⟩ := state
  simp only [evalGateCut]
  split
  · have h := length_andWord_le hash k g ((((body.drop pos)).drop (2 * w + 1)).take (k + 2))
      ((((body.drop pos)).drop (2 * w + 1 + (k + 2))).take (k + 2))
      (labels.getD (BitString.boundedBinaryValue labels.length ((body.drop pos).take w).reverse - 1)
        [])
      (labels.getD (BitString.boundedBinaryValue labels.length
        (((body.drop pos).drop w).take w).reverse - 1) [])
    simp only [length_encPair, length_encList, List.map_append, List.sum_append, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, encBits_apply, encUnary_apply,
      List.length_replicate]
    omega
  · simp only [length_encPair, length_encList, List.map_append, List.sum_append, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, encBits_apply, encUnary_apply,
      List.length_replicate, List.length_take]
    omega

/-! ### The garbled function from gate data -/


/-- Row `i` of gate `g` of the garbled function in the layout of `PointPermute.bodyWith`, from the
gate's AND bit and the zero labels, reading the argument wires `a` and `b`: row `0` is the AND bit,
rows `1` and `2` are the generator and evaluator halves of an AND gate, and every other row is
empty. -/
private def gateRow (k : ℕ) (Δ : List Bool) (labels : List (List Bool)) (isAnd : Bool)
    (g a b i : ℕ) : List Bool :=
  if i = 0 then [isAnd]
  else if isAnd then
    if i = 1 then genWord hash k g Δ (labels.getD a []) (labels.getD b [])
    else if i = 2 then evWord hash k g Δ (labels.getD a []) (labels.getD b [])
    else []
  else []

/-- The garbled function of `f` from its data: the header, and the body `bodyWith` of the gate list
with the rows `gateRow` on argument wires capped at one past the number of zero labels. -/
private theorem fnWord_eq (k : ℕ) (f : ConventionalCircuit) (coins : List Bool) :
    fnWord hash k f coins = PointPermute.encFn ((k, f.n, f.m, f.gateList.length),
      PointPermute.bodyWith f.n f.gateList.length ((zeroWords hash k f coins f.q).length + 1)
        (fun g => (f.gateList.getD g (0, 0, [])).1) (fun g => (f.gateList.getD g (0, 0, [])).2.1)
        (fun g a b i => gateRow hash k (offsetWord k coins) (zeroWords hash k f coins f.q)
          ((f.gateList.getD g (0, 0, [])).2.2.getD 3 false) g a b i)) := by
  have hgate (g : Fin f.q) : f.gateList.getD g (0, 0, []) = (f.A g, f.B g,
      [f.G g false false, f.G g false true, f.G g true false, f.G g true true]) := by
    simp [ConventionalCircuit.gateList, List.getD_eq_getElem?_getD]
  rw [ConventionalCircuit.length_gateList, PointPermute.bodyWith_eq_ofFn f.A f.B
    (fun g i => gateRow hash k (offsetWord k coins) (zeroWords hash k f coins f.q)
      (f.G g true true) g (f.A g - 1) (f.B g - 1) i)
    (fun g => by rw [hgate]) (fun g => by rw [hgate])
    (fun g i => by simp only [hgate, gateRow, List.getD_min_length_succ_sub_one]; rfl)]
  simp only [fnWord]
  congr 2
  refine congrArg List.flatten (congrArg List.ofFn (funext fun g => ?_))
  simp only [gateWord, gateRow, List.ofFn_succ, List.ofFn_zero, List.flatten_cons,
    List.flatten_nil, List.append_assoc]
  cases f.G g true true <;> simp

end Words

/-! ### Certificates -/

variable {hash : List Bool → List Bool → List Bool}
  (hf : ComputableInPolyTime (fun p : List Bool × List Bool => hash p.1 p.2)
    (encPair encBits encBits) encBits)

include hf in
/-- The hash on words is computed in polynomial time. -/
theorem hashWord_polyTime {γ : Type} {encIn : γ ↪ List Bool} {k : γ → ℕ}
    {x t : γ → List Bool} (hk : ComputableInPolyTime k encIn encUnary)
    (hx : ComputableInPolyTime x encIn encBits) (ht : ComputableInPolyTime t encIn encBits) :
    ComputableInPolyTime (fun a => hashWord hash (k a) (x a) (t a)) encIn encBits := by
  have h : ComputableInPolyTime (fun p : ℕ × List Bool × List Bool =>
      hashWord hash p.1 p.2.1 p.2.2) (encPair encUnary (encPair encBits encBits)) encBits := by
    polytime [hashWord]
  exact h.comp (hk.prod (hx.prod ht))

/-- Tweaks are computed in polynomial time. -/
theorem tweakWord_polyTime {γ : Type} {encIn : γ ↪ List Bool} {k g : γ → ℕ}
    {s : γ → Bool} (hk : ComputableInPolyTime k encIn encUnary)
    (hg : ComputableInPolyTime g encIn encUnary) (hs : ComputableInPolyTime s encIn encBool) :
    ComputableInPolyTime (fun a => tweakWord (k a) (g a) (s a)) encIn encBits := by
  have hs' : ComputableInPolyTime (fun a => (s a).toNat) encIn encUnary :=
    ComputableInPolyTime.bool_toUnary.comp hs
  unfold tweakWord
  polytime

attribute [local fun_prop] hashWord_polyTime tweakWord_polyTime

include hf in
/-- The generator half is computed in polynomial time. -/
private theorem genWord_polyTime {γ : Type} {encIn : γ ↪ List Bool} {k g : γ → ℕ}
    {Δ a b : γ → List Bool} (hk : ComputableInPolyTime k encIn encUnary)
    (hg : ComputableInPolyTime g encIn encUnary) (hΔ : ComputableInPolyTime Δ encIn encBits)
    (ha : ComputableInPolyTime a encIn encBits) (hb : ComputableInPolyTime b encIn encBits) :
    ComputableInPolyTime (fun x => genWord hash (k x) (g x) (Δ x) (a x) (b x)) encIn encBits := by
  have h : ComputableInPolyTime (fun p : (ℕ × ℕ) × List Bool × List Bool × List Bool =>
      genWord hash p.1.1 p.1.2 p.2.1 p.2.2.1 p.2.2.2)
      (encPair (encPair encUnary encUnary) (encPair encBits (encPair encBits encBits)))
      encBits := by
    polytime [genWord, maskWord, colourWord]
  exact h.comp ((hk.prod hg).prod (hΔ.prod (ha.prod hb)))

include hf in
/-- The evaluator half is computed in polynomial time. -/
private theorem evWord_polyTime {γ : Type} {encIn : γ ↪ List Bool} {k g : γ → ℕ}
    {Δ a b : γ → List Bool} (hk : ComputableInPolyTime k encIn encUnary)
    (hg : ComputableInPolyTime g encIn encUnary) (hΔ : ComputableInPolyTime Δ encIn encBits)
    (ha : ComputableInPolyTime a encIn encBits) (hb : ComputableInPolyTime b encIn encBits) :
    ComputableInPolyTime (fun x => evWord hash (k x) (g x) (Δ x) (a x) (b x)) encIn encBits := by
  have h : ComputableInPolyTime (fun p : (ℕ × ℕ) × List Bool × List Bool × List Bool =>
      evWord hash p.1.1 p.1.2 p.2.1 p.2.2.1 p.2.2.2)
      (encPair (encPair encUnary encUnary) (encPair encBits (encPair encBits encBits)))
      encBits := by
    polytime [evWord]
  exact h.comp ((hk.prod hg).prod (hΔ.prod (ha.prod hb)))

include hf in
/-- The evaluator's AND gate is computed in polynomial time. -/
theorem andWord_polyTime {γ : Type} {encIn : γ ↪ List Bool} {k g : γ → ℕ}
    {TG TE a b : γ → List Bool} (hk : ComputableInPolyTime k encIn encUnary)
    (hg : ComputableInPolyTime g encIn encUnary) (hTG : ComputableInPolyTime TG encIn encBits)
    (hTE : ComputableInPolyTime TE encIn encBits) (ha : ComputableInPolyTime a encIn encBits)
    (hb : ComputableInPolyTime b encIn encBits) :
    ComputableInPolyTime (fun x => andWord hash (k x) (g x) (TG x) (TE x) (a x) (b x)) encIn
      encBits := by
  have h : ComputableInPolyTime (fun p : (ℕ × ℕ) × (List Bool × List Bool) ×
      List Bool × List Bool => andWord hash p.1.1 p.1.2 p.2.1.1 p.2.1.2 p.2.2.1 p.2.2.2)
      (encPair (encPair encUnary encUnary) (encPair (encPair encBits encBits)
        (encPair encBits encBits))) encBits := by
    polytime [andWord, maskWord, colourWord]
  exact h.comp ((hk.prod hg).prod ((hTG.prod hTE).prod (ha.prod hb)))

attribute [local fun_prop] genWord_polyTime evWord_polyTime andWord_polyTime

include hf in
private theorem zeroStep_polyTime :
    ComputableInPolyTime (fun p : ((ℕ × ℕ × List Bool) × List (List Bool)) × (ℕ × ℕ × List Bool) =>
        zeroStep hash p.1.1.1 p.1.1.2.1 p.1.1.2.2 p.1.2 p.2)
      (encPair (encPair (encPair encUnary (encPair encUnary encBits)) (encList encBits))
        (encPair encNat (encPair encNat encBits))) (encList encBits) := by
  polytime [zeroStep, zeroGate]

/-- A label read at a wire number written in binary, capped by the number of labels. -/
theorem labelAt_polyTime {γ : Type} {encIn : γ ↪ List Bool}
    {labels : γ → List (List Bool)} {u : γ → List Bool}
    (hlabels : ComputableInPolyTime labels encIn (encList encBits))
    (hu : ComputableInPolyTime u encIn encBits) :
    ComputableInPolyTime (fun x => (labels x).getD
      (BitString.boundedBinaryValue (labels x).length (u x).reverse - 1) []) encIn encBits := by
  polytime

/-- The sum of two words, cut to `k + 2` bits. -/
theorem xorCut_polyTime {γ : Type} {encIn : γ ↪ List Bool} {k : γ → ℕ}
    {a b : γ → List Bool} (hk : ComputableInPolyTime k encIn encUnary)
    (ha : ComputableInPolyTime a encIn encBits) (hb : ComputableInPolyTime b encIn encBits) :
    ComputableInPolyTime (fun x => (List.zipWith xor (a x) (b x)).take (k x + 2)) encIn
      encBits := by
  polytime

/-- The offsets of the parts of a gate block. -/
private theorem offsets_polyTime {γ : Type} {encIn : γ ↪ List Bool} {k w : γ → ℕ}
    (hk : ComputableInPolyTime k encIn encUnary) (hw : ComputableInPolyTime w encIn encUnary) :
    ComputableInPolyTime (fun x => 2 * w x) encIn encUnary ∧
      ComputableInPolyTime (fun x => 2 * w x + 1) encIn encUnary ∧
      ComputableInPolyTime (fun x => 2 * w x + 1 + (k x + 2)) encIn encUnary ∧
      ComputableInPolyTime (fun x => k x + 2) encIn encUnary ∧
      ComputableInPolyTime (fun x => 2 * w x + 1 + 2 * (k x + 2)) encIn encUnary := by
  have htwice := ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const 2) hw
  have hstart := ComputableInPolyTime.unary_add.comp (htwice.prod (.const 1))
  have hwidth := ComputableInPolyTime.unary_add.comp (hk.prod (.const 2))
  exact ⟨htwice, hstart, ComputableInPolyTime.unary_add.comp (hstart.prod hwidth), hwidth,
    ComputableInPolyTime.unary_add.comp
      (hstart.prod (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const 2) hwidth))⟩

include hf in
/-- One gate of `evalGateCut` is computed in polynomial time. -/
private theorem evalGateCut_polyTime :
    ComputableInPolyTime (fun p : ((ℕ × ℕ × List Bool) × (List (List Bool) × ℕ)) × ℕ =>
        evalGateCut hash p.1.1.1 p.1.1.2.1 p.1.1.2.2 p.1.2 p.2)
      (encPair (encPair (encPair encUnary (encPair encUnary encBits))
        (encPair (encList encBits) encUnary)) encUnary)
      (encPair (encList encBits) encUnary) := by
  have hp := ComputableInPolyTime.fst (encPair (encPair encUnary (encPair encUnary encBits))
    (encPair (encList encBits) encUnary)) encUnary
  have hg := ComputableInPolyTime.snd (encPair (encPair encUnary (encPair encUnary encBits))
    (encPair (encList encBits) encUnary)) encUnary
  have hk := hp.fst'.fst'
  have hw := hp.fst'.snd'.fst'
  have hlabels := hp.snd'.fst'
  have hpos := hp.snd'.snd'
  obtain ⟨h2w, h2w1, h2w1k, hk2, hlenAnd⟩ := offsets_polyTime hk hw
  have hblock := ComputableInPolyTime.bitsDropWithInput hp.fst'.snd'.snd' hpos
  have ha := labelAt_polyTime hlabels (ComputableInPolyTime.bitsTakeWithInput hblock hw)
  have hb := labelAt_polyTime hlabels (ComputableInPolyTime.bitsTakeWithInput
    (ComputableInPolyTime.bitsDropWithInput hblock hw) hw)
  have hTG := ComputableInPolyTime.bitsTakeWithInput
    (ComputableInPolyTime.bitsDropWithInput hblock h2w1) hk2
  have hTE := ComputableInPolyTime.bitsTakeWithInput
    (ComputableInPolyTime.bitsDropWithInput hblock h2w1k) hk2
  have hnil : ComputableInPolyTime
      (fun _ : ((ℕ × ℕ × List Bool) × (List (List Bool) × ℕ)) × ℕ => ([] : List (List Bool)))
      (encPair (encPair (encPair encUnary (encPair encUnary encBits))
        (encPair (encList encBits) encUnary)) encUnary) (encList encBits) :=
    ComputableInPolyTime.const _
  exact ComputableInPolyTime.ite' (ComputableInPolyTime.bitsGetDWithInput hblock h2w false)
    ((ComputableInPolyTime.listAppend' hlabels (ComputableInPolyTime.cons'
      (andWord_polyTime hf hk hg hTG hTE ha hb) hnil)).prod
      (ComputableInPolyTime.unary_add' hpos hlenAnd))
    ((ComputableInPolyTime.listAppend' hlabels (ComputableInPolyTime.cons'
      (xorCut_polyTime hk ha hb) hnil)).prod
      (ComputableInPolyTime.unary_add' hpos h2w1))

include hf in
/-- A row of a garbled function is computed in polynomial time. -/
private theorem gateRow_polyTime {γ : Type} {encIn : γ ↪ List Bool} {k g a b i : γ → ℕ}
    {Δ : γ → List Bool} {labels : γ → List (List Bool)} {isAnd : γ → Bool}
    (hk : ComputableInPolyTime k encIn encUnary) (hΔ : ComputableInPolyTime Δ encIn encBits)
    (hlabels : ComputableInPolyTime labels encIn (encList encBits))
    (hisAnd : ComputableInPolyTime isAnd encIn encBool)
    (hg : ComputableInPolyTime g encIn encUnary) (ha : ComputableInPolyTime a encIn encUnary)
    (hb : ComputableInPolyTime b encIn encUnary) (hi : ComputableInPolyTime i encIn encUnary) :
    ComputableInPolyTime (fun x => gateRow hash (k x) (Δ x) (labels x) (isAnd x) (g x) (a x)
      (b x) (i x)) encIn encBits := by
  polytime [gateRow]

/-! ### Evaluation -/

include hf in
/-- `Ev` runs in polynomial time. -/
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
          (PointPermute.fnDecoder.decode p.1).1.2.2.2 + 4) (encPair encBits encBits) encUnary := by
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
    (ComputableInPolyTime.bitsFlatten (ComputableInPolyTime.listDropWithInput
      (ComputableInPolyTime.fst _ _)
        (ComputableInPolyTime.snd _ _)))
  exact hfin.comp (hfold.fst'.prod hc)

/-! ### Bodies from gate data -/

/-- **A garbled function body from gate data** is computed in polynomial time when each row
reads only the number of its gate, the gate's AND bit and its own number, and is computed in
polynomial time from them. -/
theorem bodyWith_gateData_polyTime {γ : Type} {encIn : γ ↪ List Bool} {n : γ → ℕ}
    {gates : γ → List (ℕ × ℕ × List Bool)} {row : γ × ℕ × Bool × ℕ → List Bool}
    (hn : ComputableInPolyTime n encIn encUnary)
    (hgates : ComputableInPolyTime gates encIn (encList (encPair encNat (encPair encNat encBits))))
    (hrow : ComputableInPolyTime row
      (encPair encIn (encPair encUnary (encPair encBool encUnary))) encBits) :
    ComputableInPolyTime (fun x => PointPermute.bodyWith (n x) (gates x).length 0
      (fun g => ((gates x).getD g (0, 0, [])).1) (fun g => ((gates x).getD g (0, 0, [])).2.1)
      (fun g _ _ i => row (x, g, ((gates x).getD g (0, 0, [])).2.2.getD 3 false, i))) encIn
      encBits := by
  have hx := ComputableInPolyTime.fst encIn
    (encPair encUnary (encPair encUnary (encPair encUnary encUnary)))
  have hrest := ComputableInPolyTime.snd encIn
    (encPair encUnary (encPair encUnary (encPair encUnary encUnary)))
  have hisAnd := ComputableInPolyTime.bitsGetDWithInput
    (ComputableInPolyTime.listGetDWithInput (hgates.comp hx) hrest.fst' (0, 0, [])).snd'.snd'
    (ComputableInPolyTime.const 3) false
  have hgate := ComputableInPolyTime.listGetDWithInput
    (hgates.comp (ComputableInPolyTime.fst encIn encUnary)) (ComputableInPolyTime.snd _ _)
    (0, 0, [])
  exact PointPermute.bodyWith_polyTime
    (row := fun x g _ _ i => row (x, g, ((gates x).getD g (0, 0, [])).2.2.getD 3 false, i)) hn
    ((ComputableInPolyTime.length_list _).comp hgates) (ComputableInPolyTime.const 0) hgate.fst'
    hgate.snd'.fst' (hrow.comp (hx.prod (hrest.fst'.prod (hisAnd.prod hrest.snd'.snd'.snd'))))

/-! ### Garbling -/

/-- The input `(1^k, f, r)` of the garbler. -/
private abbrev encGbInput : (ℕ × XorAndCircuit × List Bool) ↪ List Bool :=
  encPair encUnary (encPair encXorAndCircuit encBits)

private theorem data_polyTime :
    ComputableInPolyTime (fun x : ℕ × XorAndCircuit × List Bool =>
      (x.2.1.circuit.n, x.2.1.circuit.m, x.2.1.circuit.gateList)) encGbInput encCircuitData :=
  (circuitData_polyTime.comp XorAndCircuit.val_polyTime).comp (ComputableInPolyTime.snd _ _).fst'

private theorem offset_polyTime :
    ComputableInPolyTime (fun x : ℕ × XorAndCircuit × List Bool => offsetWord x.1 x.2.2)
      encGbInput encBits := by
  have hk := ComputableInPolyTime.fst encUnary (encPair encXorAndCircuit encBits)
  have hcoins := (ComputableInPolyTime.snd encUnary (encPair encXorAndCircuit encBits)).snd'
  polytime [offsetWord, BitString.listRow]

include hf in
/-- The garbler's zero labels are computed in polynomial time. -/
private theorem zeroWords_polyTime :
    ComputableInPolyTime (fun x : ℕ × XorAndCircuit × List Bool =>
      zeroWords hash x.1 x.2.1.circuit x.2.2 x.2.1.circuit.q) encGbInput (encList encBits) := by
  have hk := ComputableInPolyTime.fst encUnary (encPair encXorAndCircuit encBits)
  have hcoins := (ComputableInPolyTime.snd encUnary (encPair encXorAndCircuit encBits)).snd'
  have hn := data_polyTime.fst'
  have hinit : ComputableInPolyTime (fun x : ℕ × XorAndCircuit × List Bool =>
      (List.range x.2.1.circuit.n).map (inputWord x.1 x.2.2)) encGbInput (encList encBits) := by
    polytime [inputWord, BitString.listRow]
  have hgrowth : ComputableInPolyTime (fun x : ℕ × XorAndCircuit × List Bool =>
      2 * (x.1 + 2) + 1) encGbInput encUnary := by
    polytime
  have hfold := ComputableInPolyTime.foldlWith_of_bounded_growth
    (encP := encPair encUnary (encPair encUnary encBits))
    (encL := encList (encPair encNat (encPair encNat encBits))) (encB := encList encBits)
    (encA := encPair encNat (encPair encNat encBits)) (encIn := encGbInput)
    (step := fun par ws gate => zeroStep hash par.1 par.2.1 par.2.2 ws gate)
    (par := fun x => (x.1, x.2.1.circuit.n, offsetWord x.1 x.2.2))
    (list := fun x => x.2.1.circuit.gateList)
    (init := fun x => (List.range x.2.1.circuit.n).map (inputWord x.1 x.2.2))
    (hk.prod (hn.prod offset_polyTime)) data_polyTime.snd'.snd' hinit (zeroStep_polyTime hf)
    (growth := fun x => 2 * (x.1 + 2) + 1) (hgrowth.polyBounded_length.mono fun x => by simp)
    (fun x ws gate _ => by
      simp only [zeroStep, length_encList, List.map_append, List.sum_append, List.map_cons,
        List.map_nil, List.sum_cons, List.sum_nil, encBits_apply, List.length_take]
      omega)
  have heq : (fun x : ℕ × XorAndCircuit × List Bool =>
      zeroWords hash x.1 x.2.1.circuit x.2.2 x.2.1.circuit.q) = fun x =>
      x.2.1.circuit.gateList.foldl (zeroStep hash x.1 x.2.1.circuit.n (offsetWord x.1 x.2.2))
        ((List.range x.2.1.circuit.n).map (inputWord x.1 x.2.2)) := by
    funext x
    rw [zeroWords_eq_foldl hash _ _ _ le_rfl,
      List.take_of_length_le (ConventionalCircuit.length_gateList _).le]
  rw [heq]
  exact hfold

include hf in
/-- The garbled function is computed in polynomial time. -/
private theorem fnWord_polyTime :
    ComputableInPolyTime (fun x : ℕ × XorAndCircuit × List Bool =>
      fnWord hash x.1 x.2.1.circuit x.2.2) encGbInput encBits := by
  have hd := data_polyTime
  have hZ := zeroWords_polyTime hf
  have hn := hd.fst'
  have hm := hd.snd'.fst'
  have hg := hd.snd'.snd'
  have hq := (ComputableInPolyTime.length_list _).comp hg
  have hk := ComputableInPolyTime.fst encUnary (encPair encXorAndCircuit encBits)
  have hx := ComputableInPolyTime.fst encGbInput
    (encPair encUnary (encPair encUnary (encPair encUnary encUnary)))
  have hrest := ComputableInPolyTime.snd encGbInput
    (encPair encUnary (encPair encUnary (encPair encUnary encUnary)))
  have hgi := hrest.fst'
  have hisAnd := ComputableInPolyTime.bitsGetDWithInput
    (ComputableInPolyTime.listGetDWithInput (hg.comp hx) hgi (0, 0, [])).snd'.snd'
    (ComputableInPolyTime.const 3) false
  have hrow := gateRow_polyTime hf (hk.comp hx) (offset_polyTime.comp hx) (hZ.comp hx) hisAnd
    hgi hrest.snd'.fst' hrest.snd'.snd'.fst' hrest.snd'.snd'.snd'
  have hgate := ComputableInPolyTime.listGetDWithInput
    (hg.comp (ComputableInPolyTime.fst encGbInput encUnary)) (ComputableInPolyTime.snd _ _)
    (0, 0, [])
  have hcap : ComputableInPolyTime (fun x : ℕ × XorAndCircuit × List Bool =>
      (zeroWords hash x.1 x.2.1.circuit x.2.2 x.2.1.circuit.q).length + 1) encGbInput
      encUnary := by
    polytime
  have hbody := PointPermute.bodyWith_polyTime (n := fun x : ℕ × XorAndCircuit × List Bool =>
      x.2.1.circuit.n) (q := fun x => x.2.1.circuit.gateList.length)
    (cap := fun x => (zeroWords hash x.1 x.2.1.circuit x.2.2 x.2.1.circuit.q).length + 1)
    (A := fun x g => (x.2.1.circuit.gateList.getD g (0, 0, [])).1)
    (B := fun x g => (x.2.1.circuit.gateList.getD g (0, 0, [])).2.1)
    (row := fun x g a b i => gateRow hash x.1 (offsetWord x.1 x.2.2)
      (zeroWords hash x.1 x.2.1.circuit x.2.2 x.2.1.circuit.q)
      ((x.2.1.circuit.gateList.getD g (0, 0, [])).2.2.getD 3 false) g a b i)
    hn hq hcap hgate.fst' hgate.snd'.fst' hrow
  have hhead : ComputableInPolyTime (fun x : ℕ × XorAndCircuit × List Bool =>
      (x.1, x.2.1.circuit.n, x.2.1.circuit.m, x.2.1.circuit.gateList.length)) encGbInput
      PointPermute.encHeader :=
    hk.prod (hn.prod (hm.prod hq))
  have henc : ComputableInPolyTime (fun y : (ℕ × ℕ × ℕ × ℕ) × List Bool => PointPermute.encFn y)
      PointPermute.encFn encBits := .of_eq fun _ => rfl
  simp only [fnWord_eq]
  exact henc.comp (hhead.prod hbody)

/-- Encoding information `encInfoWord` is computed in polynomial time from the security
parameter, the input count `f.n`, and the coins. -/
theorem encInfoWord_polyTime_of {γ : Type} {encIn : γ ↪ List Bool}
    {k : γ → ℕ} {f : γ → ConventionalCircuit} {coins : γ → List Bool}
    (hk : ComputableInPolyTime k encIn encUnary)
    (hn : ComputableInPolyTime (fun x => (f x).n) encIn encUnary)
    (hcoins : ComputableInPolyTime coins encIn encBits) :
    ComputableInPolyTime (fun x => encInfoWord (k x) (f x) (coins x)) encIn encBits := by
  have hrange : ComputableInPolyTime (fun p : ℕ × ℕ × List Bool =>
      ((List.range (2 * p.2.1)).map fun j => List.zipWith xor (inputWord p.1 p.2.2 (j / 2))
        (maskWord p.1 (offsetWord p.1 p.2.2) (j.testBit 0))).flatten)
      (encPair encUnary (encPair encUnary encBits)) encBits := by
    have hp := ComputableInPolyTime.id'
      (encIn := encPair encUnary (encPair encUnary encBits))
    have hcount := ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const 2) hp.snd'.fst'
    have hlist := ComputableInPolyTime.range.comp hcount
    have hx := ComputableInPolyTime.fst
      (encPair encUnary (encPair encUnary encBits)) encUnary
    have hj := ComputableInPolyTime.snd
      (encPair encUnary (encPair encUnary encBits)) encUnary
    have hk := hx.fst'
    have hcoins := hx.snd'.snd'
    have hone := ComputableInPolyTime.unary_add.comp (hk.prod (.const 1))
    have hwidth := ComputableInPolyTime.unary_add.comp (hk.prod (.const 2))
    have hin := ComputableInPolyTime.bitsRowWithInput hwidth
      ((ComputableInPolyTime.unary_div_const 2).comp hj)
      (hcoins.bitsDropWithInput hone)
    have hoff := ComputableInPolyTime.bitsAppend
      (ComputableInPolyTime.bitsRowWithInput hone (.const 0) hcoins) (.const [true])
    have hmask := (ComputableInPolyTime.unary_testBit' hj (.const 0)).ite hoff
      ((ComputableInPolyTime.bitsReplicate false).comp hwidth)
    have hrow := ComputableInPolyTime.bitsZipWithInput xor hin hmask
    simpa only [inputWord, maskWord, offsetWord, Function.comp_def] using
      ComputableInPolyTime.bitsFlatten (ComputableInPolyTime.mapWithInput hlist hrow)
  have heq : (fun x => encInfoWord (k x) (f x) (coins x)) =
      fun x => ((List.range (2 * (f x).n)).map fun j =>
        List.zipWith xor (inputWord (k x) (coins x) (j / 2))
          (maskWord (k x) (offsetWord (k x) (coins x)) (j.testBit 0))).flatten := by
    funext x
    rw [encInfoWord, List.map_range_eq_ofFn]
  rw [heq]
  exact hrange.comp (hk.prod (hn.prod hcoins))

/-- The encoding information is computed in polynomial time. -/
private theorem encInfoWord_polyTime :
    ComputableInPolyTime (fun x : ℕ × XorAndCircuit × List Bool =>
      encInfoWord x.1 x.2.1.circuit x.2.2) encGbInput encBits :=
  encInfoWord_polyTime_of (ComputableInPolyTime.fst _ _) data_polyTime.fst'
    (ComputableInPolyTime.snd encUnary (encPair encXorAndCircuit encBits)).snd'

include hf in
/-- The decoding information is computed in polynomial time. -/
private theorem decInfoWord_polyTime :
    ComputableInPolyTime (fun x : ℕ × XorAndCircuit × List Bool =>
      decInfoWord hash x.1 x.2.1.circuit x.2.2) encGbInput encBits := by
  have hrange : ComputableInPolyTime (fun p : ℕ × ℕ × ℕ × List (List Bool) =>
      (List.range p.2.1).map fun o => colourWord p.1 (p.2.2.2.getD (p.2.2.1 + o) []))
      (encPair encUnary (encPair encUnary (encPair encUnary (encList encBits)))) encBits := by
    polytime [colourWord]
  have hd := data_polyTime
  have hs : ComputableInPolyTime (fun x : ℕ × XorAndCircuit × List Bool =>
      x.2.1.circuit.n + x.2.1.circuit.q - x.2.1.circuit.m) encGbInput encUnary := by
    have hn := hd.fst'
    have hm := hd.snd'.fst'
    have hq : ComputableInPolyTime (fun x : ℕ × XorAndCircuit × List Bool => x.2.1.circuit.q)
        encGbInput encUnary := by
      simpa only [Function.comp_def, ConventionalCircuit.length_gateList] using
        (ComputableInPolyTime.length_list _).comp hd.snd'.snd'
    polytime
  have heq : (fun x : ℕ × XorAndCircuit × List Bool => decInfoWord hash x.1 x.2.1.circuit x.2.2) =
      fun x => (List.range x.2.1.circuit.m).map fun o => colourWord x.1
        ((zeroWords hash x.1 x.2.1.circuit x.2.2 x.2.1.circuit.q).getD
          (x.2.1.circuit.n + x.2.1.circuit.q - x.2.1.circuit.m + o) []) := by
    funext x
    rw [decInfoWord, List.map_range_eq_ofFn]
  rw [heq]
  exact hrange.comp ((ComputableInPolyTime.fst _ _).prod (hd.snd'.fst'.prod
    (hs.prod (zeroWords_polyTime hf))))

include hf in
/-- The garbler runs in polynomial time. -/
private theorem gb_polyTime :
    ComputableInPolyTime (fun (k, f, coins) => (scheme hash).gb k f coins) encGbInput
      Scheme.encGarbled :=
  Scheme.encGarbled_mk_polyTime (fnWord_polyTime hf) encInfoWord_polyTime (decInfoWord_polyTime hf)

/-- The number of coins is computed in polynomial time. -/
private theorem coins_polyTime :
    ComputableInPolyTime (fun (k, f) => (scheme hash).coins k f)
      (encPair encUnary encXorAndCircuit) encUnary := by
  have hk := ComputableInPolyTime.fst encUnary encXorAndCircuit
  have hn : ComputableInPolyTime (fun x : ℕ × XorAndCircuit => x.2.circuit.n)
      (encPair encUnary encXorAndCircuit) encUnary :=
    ((circuitData_polyTime.comp XorAndCircuit.val_polyTime).comp
      (ComputableInPolyTime.snd _ _)).fst'
  have heq : (fun (k, f) => (scheme hash).coins k f) = fun x : ℕ × XorAndCircuit =>
      (x.1 + 1) + x.2.circuit.n * (x.1 + 2) := by
    funext x
    rfl
  rw [heq]
  polytime

include hf in
/-- **Half-gates garbling is efficient** for every hash family computed in polynomial time
(`CircularCorrelationRobust.polyTime` supplies `hf`): the length readers `n` and `m`, the number of
coins and the garbler on `(1^k, f, r)`, and `En`, `Ev`, `De` and `ev` on their encoded arguments,
run in polynomial time, for XOR–AND circuits encoded by `encXorAndCircuit`. -/
theorem scheme_isEfficient : (scheme hash).IsEfficient encXorAndCircuit where
  inLen := (circuitData_polyTime.comp XorAndCircuit.val_polyTime).fst'
  outLen := (circuitData_polyTime.comp XorAndCircuit.val_polyTime).snd'.fst'
  coins := coins_polyTime
  gb := gb_polyTime hf
  encode := projectiveEncode_polyTime
  evalGarbled := evalWord_polyTime hf
  decode := PointPermute.decodeWord_polyTime
  ev := evalCirc_polyTime.comp
    ((XorAndCircuit.val_polyTime.comp (ComputableInPolyTime.fst _ _)).prod
      (ComputableInPolyTime.snd _ _))

end HalfGates

end Cslib.Crypto.Garbling
