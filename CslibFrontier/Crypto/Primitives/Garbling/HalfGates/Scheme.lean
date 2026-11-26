/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.CircularCorrelationRobust
public import CslibFrontier.Crypto.Primitives.Garbling.HalfGates.Conventional
public import CslibFrontier.Crypto.Primitives.Garbling.PointPermute
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.OfBits
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Foundations.Data.List.Flatten

/-!
# Half-gates garbling as a garbling scheme

Definitions and correctness only. The efficiency certificates of the scheme
(`CslibFrontier.Crypto.Primitives.Garbling.HalfGates.Efficient`), its word simulator
(`CslibFrontier.Crypto.Primitives.Garbling.HalfGates.Simulator`) and its simulation privacy
(`prv.sim`) under `CircularCorrelationRobust`, by a certified reduction
(`CslibFrontier.Crypto.Primitives.Garbling.HalfGates.PrvSim`), build on it.

The half-gates garbling of `CslibFrontier.Crypto.Primitives.Garbling.HalfGates`, after Zahur,
Rosulek and Evans [ZahurRosulekEvans2015] (Figure 2, p. 9), as a garbling scheme in the sense of
Bellare, Hoang and Rogaway [BellareHoangRogaway2012] (`Garbling.Scheme`) over XOR–AND
conventional circuits (`XorAndCircuit`): `HalfGates.scheme hash`, with the hash family `hash`.

At security parameter `k`, a label is a `(k + 1)`-bit key followed by its colour bit, and the hash
of a label and a `k`-bit tweak is `CCR.atLevel hash k` (`HalfGates.hashWord` on words). Slot `s` of
gate `g`, `false` for the generator half and `true` for the evaluator half, has the tweak `2 g + s`,
reduced modulo `2 ^ k` (`HalfGates.tweakWord`). The coins are the `k + 1` bits of the offset key
`R`, then the `n` input zero labels; the offset is `CCR.offset R = (R, true)`.

The tweaks of different slots need not differ: at `k = 0` every tweak is empty, and at `k = 1` the
generator halves of gates `0` and `1` both get the tweak `[false]`. For a circuit with `q` gates
they are all distinct when `2 q ≤ 2 ^ k`. Correctness does not use distinct tweaks, and
`HalfGates.scheme_correct` holds for every hash family.

`Gb` writes the garbled function `F` as the header `(k, n, m, q)`, in unary, followed for each gate
by its two argument wires `A g` and `B g` as `w`-bit numbers, `w` the bit length of `n + q`, a bit
that is set for an AND gate, and for an AND gate its two ciphertexts, the generator half then the
evaluator half. XOR gates have no ciphertexts [KolesnikovSchneider2008]. The encoding information
`e` lists the two labels of each input wire, for bit `0` and bit `1`, as in point-and-permute
garbling, so `En` is the projective encoding `projectiveEncode`; the decoding information `d`
lists the colours of the zero labels of the `m` output wires, and `De` is
`PointPermute.decodeWord`.

Three choices differ from Figure 2 of [ZahurRosulekEvans2015] (p. 9): the tweaks are numbered by
gate, `2 g + s` modulo `2 ^ k`, where Figure 2 takes `j` and `j'` from the counter `NextIndex`,
which advances only at AND gates; `e` is projective, listing both labels of each input, where
Figure 2 sets `e_i = W_i^0` and encodes `X_i = e_i ⊕ x_i R`; and labels have `k + 2` bits, where
Figure 2 has `k`-bit labels and `R ∈ {0,1}^{k-1}1`.

The scheme is correct (`HalfGates.scheme_correct`) but not valid in the sense of
[BellareHoangRogaway2012] (§3.1, p. 7). The length of `F` depends on the number of AND gates, so
the length condition fails, and `d` holds the colours of output zero labels derived through the
hash from the gates, so it depends on `f` and non-degeneracy fails too. The scheme of
[ZahurRosulekEvans2015] behaves the same way: Figure 2 sends `F_i` only for AND gates and sets
`d_i = lsb(W_i^0)`. Simulation privacy does not use validity.

The garbler and the evaluator are list programs. The garbler writes the typed garbling
`HalfGates.garbleWith` of `HalfGates.toCircuit f` (`HalfGates.gb_eq_encodeGarbled`), and the
evaluator follows every fixed point of the typed evaluation round
(`HalfGates.evalWord_encodeFn`), so correctness follows from `HalfGates.Garbled.run_garbleWith`
and `HalfGates.eval_toCircuit`.

## Main definitions

* `Cslib.Crypto.Garbling.HalfGates.scheme`: half-gates garbling as a garbling scheme.
* `Cslib.Crypto.Garbling.HalfGates.encodeFn`, `Cslib.Crypto.Garbling.HalfGates.encodeGarbled`: the
  words of a typed garbled table and of a typed garbled circuit.

## Main results

* `Cslib.Crypto.Garbling.HalfGates.gb_eq_encodeGarbled`: the garbler computes `garbleWith`.
* `Cslib.Crypto.Garbling.HalfGates.evalWord_encodeFn`: the evaluator computes the typed
  evaluation.
* `Cslib.Crypto.Garbling.HalfGates.scheme_correct`: the scheme is correct.

## References

* [S. Zahur, M. Rosulek, D. Evans, *Two Halves Make a Whole: Reducing Data Transfer in Garbled
  Circuits using Half Gates*][ZahurRosulekEvans2015]
* [M. Bellare, V. T. Hoang, P. Rogaway, *Foundations of Garbled Circuits*][BellareHoangRogaway2012]
* [V. Kolesnikov, T. Schneider, *Improved Garbled Circuit: Free XOR Gates and
  Applications*][KolesnikovSchneider2008]
-/

public section

namespace Cslib.Crypto.Garbling.HalfGates

open Cslib.Circuits Turing.MultiTapeTM

/-! ### Words -/

/-- The tweak of slot `s` of gate `g` at parameter `k`, `s = false` for the generator half: the
`k` low bits of `2 g + s`, least significant first. Different slots get the same tweak when
`2 g + s` agree modulo `2 ^ k`; correctness does not need distinct tweaks. -/
@[expose] def tweakWord (k g : ℕ) (s : Bool) : List Bool :=
  BitString.lowBits k (2 * g + s.toNat)

variable (hash : List Bool → List Bool → List Bool)

/-- The hash at parameter `k` on words: the first `k + 2` bits of `hash x t`, padded with `false`.
On a label and a `k`-bit tweak it is `CCR.atLevel hash k` (`labelBits_atLevel`). -/
@[expose] def hashWord (k : ℕ) (x t : List Bool) : List Bool :=
  (hash x t ++ List.replicate (k + 2) false).take (k + 2)

/-- `bitOffset Δ b` on words at parameter `k`: `Δ` when `b` is set, the zero label otherwise. -/
@[expose] def maskWord (k : ℕ) (Δ : List Bool) (b : Bool) : List Bool :=
  if b then Δ else List.replicate (k + 2) false

/-- The colour of a label word at parameter `k`: its bit `k + 1`. -/
@[expose] def colourWord (k : ℕ) (a : List Bool) : Bool := a.getD (k + 1) false

/-- The generator half `H(a, t) + H(a + Δ, t) + p_b Δ` of gate `g`, from the zero labels `a`, `b`
of its arguments (`genCt`). -/
@[expose] def genWord (k g : ℕ) (Δ a b : List Bool) : List Bool :=
  List.zipWith xor (List.zipWith xor (hashWord hash k a (tweakWord k g false))
    (hashWord hash k (List.zipWith xor a Δ) (tweakWord k g false))) (maskWord k Δ (colourWord k b))

/-- The evaluator half `H(b, t') + H(b + Δ, t') + a` of gate `g`, from the zero labels `a`, `b` of
its arguments (`evCt`). -/
@[expose] def evWord (k g : ℕ) (Δ a b : List Bool) : List Bool :=
  List.zipWith xor (List.zipWith xor (hashWord hash k b (tweakWord k g true))
    (hashWord hash k (List.zipWith xor b Δ) (tweakWord k g true))) a

/-- The evaluator's AND gate `g` on words, from its ciphertexts `TG`, `TE` and the labels `a`, `b`
of its arguments: `(H(a, t) + s_a TG) + (H(b, t') + s_b (TE + a))` (`andEval`). -/
@[expose] def andWord (k g : ℕ) (TG TE a b : List Bool) : List Bool :=
  List.zipWith xor
    (List.zipWith xor (hashWord hash k a (tweakWord k g false)) (maskWord k TG (colourWord k a)))
    (List.zipWith xor (hashWord hash k b (tweakWord k g true))
      (maskWord k (List.zipWith xor TE a) (colourWord k b)))

/-- The zero label of gate `g` from the zero labels `a`, `b` of its arguments under the offset
`Δ`: the evaluator's AND gate on the gate's own ciphertexts, or the sum for an XOR gate. -/
@[expose] def zeroGate (k g : ℕ) (Δ a b : List Bool) (isAnd : Bool) : List Bool :=
  if isAnd then andWord hash k g (genWord hash k g Δ a b) (evWord hash k g Δ a b) a b
  else List.zipWith xor a b

/-- The offset `Δ = (R, 1)` read from the coins: their first `k + 1` bits, padded with `false`,
then `true`. -/
@[expose] def offsetWord (k : ℕ) (coins : List Bool) : List Bool :=
  BitString.listRow (k + 1) 0 coins ++ [true]

/-- The zero label of input `i` read from the coins: block `i` of `k + 2` bits after the offset
key. -/
@[expose] def inputWord (k : ℕ) (coins : List Bool) (i : ℕ) : List Bool :=
  BitString.listRow (k + 2) i (coins.drop (k + 1))

/-- The zero labels of the first `n + s` wires of `f` at parameter `k`, in wire order: the input
zero labels read from the coins, then gate by gate `zeroGate` on the zero labels of the gate's
arguments. -/
@[expose] def zeroWords (k : ℕ) (f : ConventionalCircuit) (coins : List Bool) :
    ℕ → List (List Bool)
  | 0 => List.ofFn fun i : Fin f.n => inputWord k coins i
  | s + 1 =>
    if h : s < f.q then
      let ws := zeroWords k f coins s
      ws ++ [zeroGate hash k s (offsetWord k coins) (ws.getD (f.A ⟨s, h⟩ - 1) [])
        (ws.getD (f.B ⟨s, h⟩ - 1) []) (f.G ⟨s, h⟩ true true)]
    else zeroWords k f coins s

/-- The block of gate `g` in the garbled function, from the zero labels `labels` of all wires:
the numbers of its argument wires as `w`-bit numbers, its AND bit, and for an AND gate its two
ciphertexts. -/
@[expose] def gateWord (k w : ℕ) (f : ConventionalCircuit) (Δ : List Bool)
    (labels : List (List Bool)) (g : Fin f.q) : List Bool :=
  BitString.lowBits w (f.A g) ++ BitString.lowBits w (f.B g) ++ [f.G g true true] ++
    if f.G g true true then
      genWord hash k g Δ (labels.getD (f.A g - 1) []) (labels.getD (f.B g - 1) []) ++
        evWord hash k g Δ (labels.getD (f.A g - 1) []) (labels.getD (f.B g - 1) [])
    else []

/-- The garbled function of `f`: the header `(k, n, m, q)`, then the blocks of its gates. -/
@[expose] def fnWord (k : ℕ) (f : ConventionalCircuit) (coins : List Bool) : List Bool :=
  PointPermute.encFn ((k, f.n, f.m, f.q), (List.ofFn fun g : Fin f.q =>
    gateWord hash k (PointPermute.wireWidth f.n f.q) f (offsetWord k coins)
      (zeroWords hash k f coins f.q) g).flatten)

/-- The encoding information of `f`: for each input wire, the labels encoding `0` and `1`; label
`j` encodes bit `j mod 2` of input `j / 2`. -/
@[expose] def encInfoWord (k : ℕ) (f : ConventionalCircuit) (coins : List Bool) : List Bool :=
  (List.ofFn fun j : Fin (2 * f.n) => List.zipWith xor (inputWord k coins (j / 2))
    (maskWord k (offsetWord k coins) (j.val.testBit 0))).flatten

/-- The decoding information of `f`: the colours of the zero labels of its last `m` wires. -/
@[expose] def decInfoWord (k : ℕ) (f : ConventionalCircuit) (coins : List Bool) : List Bool :=
  List.ofFn fun o : Fin f.m =>
    colourWord k ((zeroWords hash k f coins f.q).getD (f.n + f.q - f.m + o) [])

/-- One gate of `Ev`, with the labels of the earlier wires and the position `pos` of the gate's
block in the body: read the gate's argument wires and their labels, and append the sum of the
labels for an XOR gate, or the evaluator's AND gate on the two ciphertexts for an AND gate. -/
@[expose] def evalGate (k w : ℕ) (body : List Bool) (state : List (List Bool) × ℕ) (g : ℕ) :
    List (List Bool) × ℕ :=
  let (labels, pos) := state
  let block := body.drop pos
  let a := labels.getD (BitString.boundedBinaryValue labels.length (block.take w).reverse - 1) []
  let b := labels.getD
    (BitString.boundedBinaryValue labels.length ((block.drop w).take w).reverse - 1) []
  if block.getD (2 * w) false then
    (labels ++ [andWord hash k g ((block.drop (2 * w + 1)).take (k + 2))
      ((block.drop (2 * w + 1 + (k + 2))).take (k + 2)) a b], pos + (2 * w + 1 + 2 * (k + 2)))
  else (labels ++ [List.zipWith xor a b], pos + (2 * w + 1))

/-- `Ev(F, X)`: read the header `(k, n, m, q)` of `F`, start from the `n` labels of `X`, evaluate
the gates in order, and return the labels of the last `m` wires. -/
@[expose] def evalWord (F X : List Bool) : List Bool :=
  let ((k, n, m, q), body) := PointPermute.fnDecoder.decode F
  let (labels, _) := (List.range q).foldl (evalGate hash k (PointPermute.wireWidth n q) body)
    (BitString.listRows n (k + 2) X, 0)
  (labels.drop (n + q - m)).flatten

/-- **Half-gates garbling** as a garbling scheme over XOR–AND conventional circuits, with the hash
family `hash`. -/
@[expose] def scheme : Scheme XorAndCircuit where
  inLen f := f.circuit.n
  outLen f := f.circuit.m
  size f := f.circuit.q
  ev f x := f.circuit.evalCirc x
  coinLen k n _ _ := (k + 1) + n * (k + 2)
  gb k f coins :=
    ⟨fnWord hash k f.circuit coins, encInfoWord k f.circuit coins,
      decInfoWord hash k f.circuit coins⟩
  encode := projectiveEncode
  evalGarbled := evalWord hash
  decode := PointPermute.decodeWord

/-! ### The typed garbling -/

/-- The tweaks of the slots of a circuit at parameter `k`: slot `s` of gate `g` gets
`tweakWord k g s`. -/
@[expose] def slotTweak {n m : ℕ} (C : Circuit signature n m) (k : ℕ) : Slot C → BitString k
  | (⟨g, _⟩, s) => BitString.ofList k (tweakWord k g s)

/-- The offset key read from the coins: their first `k + 1` bits. -/
@[expose] def offsetKey (k : ℕ) (coins : List Bool) : BitString (k + 1) :=
  BitString.ofList (k + 1) coins

/-- The input zero labels read from the coins. -/
@[expose] def inputLabels {n : ℕ} (k : ℕ) (coins : List Bool) (i : Fin n) :
    BitString (k + 1) × Bool :=
  labelOfWord k (inputWord k coins i)

/-- The block of gate `g` of a garbled table over `C` at parameter `k`: the numbers of its
argument wires, from `1`, as `w`-bit numbers, its AND bit, and for an AND gate its two
ciphertexts, the generator half first. -/
@[expose] def encodeGate {n m : ℕ} (k w : ℕ) (C : Circuit signature n m)
    (table : Slot C → BitString (k + 1) × Bool) (g : Fin C.size) : List Bool :=
  BitString.lowBits w ((left C g).toNat + 1) ++ BitString.lowBits w ((right C g).toNat + 1) ++
    [decide (op C g = .and)] ++
    if h : op C g = .and then
      labelBits (table (⟨g, h⟩, false)) ++
        labelBits (table (⟨g, h⟩, true))
    else []

/-- The garbled function of a table over `C` at parameter `k`: the header `(k, n, m, s)`, then the
blocks of the gates. -/
@[expose] def encodeFn {n m : ℕ} (k : ℕ) (C : Circuit signature n m)
    (table : Slot C → BitString (k + 1) × Bool) : List Bool :=
  PointPermute.encFn ((k, n, m, C.size), (List.ofFn fun g =>
    encodeGate k (PointPermute.wireWidth n C.size) C table g).flatten)

/-- The words `(F, e, d)` of a typed garbling of `toCircuit f` at parameter `k`. -/
@[expose] noncomputable def encodeGarbled (k : ℕ) (f : XorAndCircuit)
    (G : Garbled (toCircuit f) (BitString (k + 1))) : Scheme.Garbled where
  fn := encodeFn k (toCircuit f) G.table
  encInfo := (List.ofFn fun j : Fin (2 * f.circuit.n) =>
    labelBits (G.encoding ⟨j / 2, by omega⟩ (j.val.testBit 0))).flatten
  decInfo := List.ofFn G.decoding

/-- A tweak word has `k` bits. -/
@[simp] theorem length_tweakWord (k g : ℕ) (s : Bool) : (tweakWord k g s).length = k := by
  simp [tweakWord]

/-- The tweak of a slot, as a word, is `tweakWord`. -/
theorem ofFn_slotTweak {n m : ℕ} (C : Circuit signature n m) (k : ℕ) (g : Fin C.size)
    (h : op C g = .and) (s : Bool) :
    List.ofFn (slotTweak C k (⟨g, h⟩, s)) = tweakWord k g s :=
  BitString.ofFn_ofList (length_tweakWord k g s)

/-- A hash word has `k + 2` bits. -/
@[simp] theorem length_hashWord (k : ℕ) (x t : List Bool) :
    (hashWord hash k x t).length = k + 2 := by
  simp [hashWord]

/-- **The hash on words is `CCR.atLevel`.** -/
theorem labelBits_atLevel (k : ℕ) (x : BitString (k + 1) × Bool) (t : BitString k) :
    labelBits (CCR.atLevel hash k x t) =
      hashWord hash k (labelBits x) (List.ofFn t) := by
  have hpad : labelOfWord k (hash (labelBits x) (List.ofFn t)) =
      labelOfWord k (hashWord hash k (labelBits x) (List.ofFn t)) := by
    rw [labelOfWord, labelOfWord, hashWord,
      ← BitString.ofFn_ofList_eq_take, BitString.ofList_ofFn]
  rw [CCR.atLevel, hpad, labelBits_labelOfWord (length_hashWord hash k _ _)]

/-- The zero label as a word. -/
private theorem labelBits_zero (k : ℕ) :
    labelBits (0 : BitString (k + 1) × Bool) = List.replicate (k + 2) false := by
  rw [labelBits_apply, List.eq_replicate_iff]
  refine ⟨by simp, fun b hb => ?_⟩
  simp only [List.mem_append, List.mem_ofFn, List.mem_singleton] at hb
  rcases hb with ⟨_, rfl⟩ | rfl <;> rfl

/-- `bitOffset` on words is `maskWord`. -/
theorem labelBits_bitOffset (k : ℕ) (Δ : BitString (k + 1) × Bool) (b : Bool) :
    labelBits (bitOffset Δ b) = maskWord k (labelBits Δ) b := by
  cases b <;> simp [bitOffset_false, bitOffset_true, labelBits_zero, maskWord]

/-- The colour of a label word is the label's colour. -/
theorem colourWord_labelBits {k : ℕ} (x : BitString (k + 1) × Bool) :
    colourWord k (labelBits x) = x.2 :=
  getD_labelBits x

/-- The generator half on words is `genCt`. -/
theorem labelBits_genCt (k g : ℕ) {t : BitString k} (ht : List.ofFn t = tweakWord k g false)
    (Δ a b : BitString (k + 1) × Bool) :
    labelBits (genCt (CCR.atLevel hash k) Δ t a b) =
      genWord hash k g (labelBits Δ) (labelBits a)
        (labelBits b) := by
  simp only [genCt, genWord, labelBits_add, labelBits_atLevel, ht,
    labelBits_bitOffset, colourWord_labelBits]

/-- The evaluator half on words is `evCt`. -/
theorem labelBits_evCt (k g : ℕ) {t : BitString k} (ht : List.ofFn t = tweakWord k g true)
    (Δ a b : BitString (k + 1) × Bool) :
    labelBits (evCt (CCR.atLevel hash k) Δ t a b) =
      evWord hash k g (labelBits Δ) (labelBits a)
        (labelBits b) := by
  simp only [evCt, evWord, labelBits_add, labelBits_atLevel, ht]

/-- The evaluator's AND gate on words is `andEval`. -/
theorem labelBits_andEval (k g : ℕ) {t t' : BitString k} (ht : List.ofFn t = tweakWord k g false)
    (ht' : List.ofFn t' = tweakWord k g true) (TG TE a b : BitString (k + 1) × Bool) :
    labelBits (andEval (CCR.atLevel hash k) t t' TG TE a b) =
      andWord hash k g (labelBits TG) (labelBits TE)
        (labelBits a) (labelBits b) := by
  simp only [andEval, andWord, labelBits_add, labelBits_atLevel, ht, ht',
    labelBits_bitOffset, colourWord_labelBits]

/-- The offset read from the coins, as a word, is `offsetWord`. -/
theorem labelBits_offset (k : ℕ) (coins : List Bool) :
    labelBits (CCR.offset (offsetKey k coins)) = offsetWord k coins := by
  rw [offsetWord, BitString.listRow_zero]
  rfl

/-- An input zero label read from the coins, as a word, is `inputWord`. -/
theorem labelBits_inputLabels {n : ℕ} (k : ℕ) (coins : List Bool) (i : Fin n) :
    labelBits (inputLabels k coins i) = inputWord k coins i :=
  labelBits_labelOfWord (BitString.length_listRow _ _ _)

/-- An entry of a prefix of the label words of a labelling. -/
theorem getD_take_labels {n s k : ℕ} (A : Wire n s → BitString (k + 1) × Bool) {j i : ℕ}
    (hij : i < j) (hj : j ≤ n + s) :
    ((List.ofFn fun v : Fin (n + s) =>
      labelBits (A (Wire.ofNat v v.isLt))).take j).getD i [] =
        labelBits (A (Wire.ofNat i (by omega))) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hij, List.getElem?_ofFn]
  simp [show i < n + s by omega]

/-- An entry of the label words of a labelling. -/
theorem getD_ofFn_labels {n s k : ℕ} (A : Wire n s → BitString (k + 1) × Bool) {i : ℕ}
    (hi : i < n + s) :
    (List.ofFn fun v : Fin (n + s) =>
      labelBits (A (Wire.ofNat v v.isLt))).getD i [] =
        labelBits (A (Wire.ofNat i hi)) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [hi]

/-- The first argument of gate `g` of `toCircuit f` as a wire number. -/
private theorem left_toCircuit (f : XorAndCircuit) (g : Fin (toCircuit f).size) :
    left (toCircuit f) g = Wire.ofNat (f.circuit.A (g.cast (size_toCircuit f)) - 1) (by
      have h₁ := toNat_left_lt (toCircuit f) g
      have h₂ := toNat_left_toCircuit f g
      omega) :=
  Wire.toNat_injective (by simp only [Wire.toNat_ofNat]; exact toNat_left_toCircuit f g)

/-- The second argument of gate `g` of `toCircuit f` as a wire number. -/
private theorem right_toCircuit (f : XorAndCircuit) (g : Fin (toCircuit f).size) :
    right (toCircuit f) g = Wire.ofNat (f.circuit.B (g.cast (size_toCircuit f)) - 1) (by
      have h₁ := toNat_right_lt (toCircuit f) g
      have h₂ := toNat_right_toCircuit f g
      omega) :=
  Wire.toNat_injective (by simp only [Wire.toNat_ofNat]; exact toNat_right_toCircuit f g)

/-- **The garbler's zero labels are the typed zero labels.** The first `n + s` zero label words
that `Gb` computes are the words of the zero labels of the typed garbling of `toCircuit f`, with the
offset key and input zero labels read from the coins. -/
theorem zeroWords_eq (k : ℕ) (f : XorAndCircuit) (coins : List Bool) {s : ℕ}
    (hs : s ≤ f.circuit.q) :
    zeroWords hash k f.circuit coins s =
      (List.ofFn fun v : Fin (f.circuit.n + (toCircuit f).size) =>
        labelBits (zeroLabels (toCircuit f) (CCR.atLevel hash k) (slotTweak _ k)
          (CCR.offset (offsetKey k coins)) (inputLabels k coins)
          (Wire.ofNat v v.isLt))).take (f.circuit.n + s) := by
  set W := zeroLabels (toCircuit f) (CCR.atLevel hash k) (slotTweak _ k)
    (CCR.offset (offsetKey k coins)) (inputLabels k coins) with hWdef
  have hW := zeroLabels_isFixed (toCircuit f) (CCR.atLevel hash k) (slotTweak _ k)
    (CCR.offset (offsetKey k coins)) (inputLabels k coins)
  rw [← hWdef] at hW
  induction s with
  | zero =>
    apply List.ext_getElem (by simp [zeroWords])
    intro i h₁ h₂
    simp only [zeroWords, List.length_ofFn] at h₁
    have hin : (Wire.ofNat i (by omega) : Wire f.circuit.n (toCircuit f).size) = .input ⟨i, h₁⟩ :=
      Wire.toNat_injective (by simp)
    simp only [zeroWords, List.getElem_ofFn, List.getElem_take, hin, ← congrFun hW (.input ⟨i, h₁⟩),
      evalStep, labelBits_inputLabels]
  | succ s ih =>
    have hsq : s < f.circuit.q := hs
    have hsize := size_toCircuit f
    set g : Fin (toCircuit f).size := ⟨s, by omega⟩ with hg
    have hgcast : g.cast (size_toCircuit f) = ⟨s, hsq⟩ := Fin.ext rfl
    have hA₁ := f.isValid.one_le_A ⟨s, hsq⟩
    have hAB := f.isValid.A_lt_B ⟨s, hsq⟩
    have hBg := f.isValid.B_lt_gate ⟨s, hsq⟩
    simp only [ConventionalCircuit.topo] at hA₁ hAB hBg
    rw [zeroWords, dite_eq_left hsq, ih hsq.le, ← Nat.add_assoc, List.take_add_one,
      List.getElem?_ofFn]
    have hgate : (Wire.ofNat (f.circuit.n + s) (by omega) : Wire f.circuit.n (toCircuit f).size) =
        .gate g := Wire.toNat_injective (by simp [hg])
    simp only [show f.circuit.n + s < f.circuit.n + (toCircuit f).size by omega, dite_true,
      Option.toList_some, hgate]
    congr 1
    rw [getD_take_labels W (by omega) (by omega), getD_take_labels W (by omega) (by omega)]
    have hl : (Wire.ofNat (f.circuit.A ⟨s, hsq⟩ - 1) (by omega) :
        Wire f.circuit.n (toCircuit f).size) =
        left (toCircuit f) g :=
      Wire.toNat_injective (by rw [Wire.toNat_ofNat, toNat_left_toCircuit, hgcast])
    have hr : (Wire.ofNat (f.circuit.B ⟨s, hsq⟩ - 1) (by omega) :
        Wire f.circuit.n (toCircuit f).size) =
        right (toCircuit f) g :=
      Wire.toNat_injective (by rw [Wire.toNat_ofNat, toNat_right_toCircuit, hgcast])
    have hop : op (toCircuit f) g = opOf (f.circuit.G ⟨s, hsq⟩) := by
      rw [op_toCircuit, hgcast]
    rw [hl, hr, ← congrFun hW (.gate g)]
    simp only [evalStep, garbleTable, Slot.gate, Bool.false_eq_true, ↓reduceIte]
    cases hG : f.circuit.G ⟨s, hsq⟩ true true
    · have hop' : op (toCircuit f) g = .xor := by simp [hop, opOf, hG]
      rw [dite_eq_right (by rw [hop']; decide)]
      simp only [zeroGate, Bool.false_eq_true, ↓reduceIte, labelBits_add]
    · have hop' : op (toCircuit f) g = .and := by simp [hop, opOf, hG]
      rw [dite_eq_left hop']
      simp only [zeroGate, ↓reduceIte]
      rw [labelBits_andEval hash k s (ofFn_slotTweak _ k g hop' false)
          (ofFn_slotTweak _ k g hop' true),
        labelBits_genCt hash k s (ofFn_slotTweak _ k g hop' false),
        labelBits_evCt hash k s (ofFn_slotTweak _ k g hop' true), labelBits_offset]

/-- The zero label words of all wires. -/
private theorem zeroWords_q (k : ℕ) (f : XorAndCircuit) (coins : List Bool) :
    zeroWords hash k f.circuit coins f.circuit.q =
      List.ofFn fun v : Fin (f.circuit.n + (toCircuit f).size) =>
        labelBits (zeroLabels (toCircuit f) (CCR.atLevel hash k) (slotTweak _ k)
          (CCR.offset (offsetKey k coins)) (inputLabels k coins) (Wire.ofNat v v.isLt)) := by
  rw [zeroWords_eq hash k f coins le_rfl, List.take_of_length_le (by simp [size_toCircuit])]

/-- Gate `g` of `toCircuit f` is an AND gate exactly when `G g 1 1` is set. -/
private theorem decide_op_toCircuit (f : XorAndCircuit) (g : Fin (toCircuit f).size) :
    decide (op (toCircuit f) g = .and) = f.circuit.G (g.cast (size_toCircuit f)) true true := by
  rw [op_toCircuit, opOf]
  cases f.circuit.G (g.cast (size_toCircuit f)) true true <;> rfl

/-- **Gate `g` of a typed garbled table over `toCircuit f`, as a word**: the argument wires
`A g` and `B g` of `f` as `w`-bit numbers, `w` the bit length of `n + q`, the AND bit `G g 1 1`,
and for an AND gate the words of its two ciphertexts, the generator half first. -/
theorem encodeGate_toCircuit (k : ℕ) (f : XorAndCircuit)
    (table : Slot (toCircuit f) → BitString (k + 1) × Bool) (g : Fin (toCircuit f).size) :
    encodeGate k (PointPermute.wireWidth f.circuit.n (toCircuit f).size) (toCircuit f) table g =
      BitString.lowBits (PointPermute.wireWidth f.circuit.n f.circuit.q)
          (f.circuit.A (g.cast (size_toCircuit f))) ++
        BitString.lowBits (PointPermute.wireWidth f.circuit.n f.circuit.q)
          (f.circuit.B (g.cast (size_toCircuit f))) ++
        [f.circuit.G (g.cast (size_toCircuit f)) true true] ++
        if h : op (toCircuit f) g = .and then
          labelBits (table (⟨g, h⟩, false)) ++ labelBits (table (⟨g, h⟩, true))
        else [] := by
  have hA₁ := f.isValid.one_le_A (g.cast (size_toCircuit f))
  have hAB := f.isValid.A_lt_B (g.cast (size_toCircuit f))
  simp only [ConventionalCircuit.topo] at hA₁ hAB
  simp only [encodeGate, size_toCircuit, toNat_left_toCircuit, toNat_right_toCircuit,
    Nat.sub_add_cancel hA₁, Nat.sub_add_cancel (hA₁.trans hAB.le), decide_op_toCircuit]

/-- The block of gate `g` of the typed garbled table, as a word, is `gateWord`. -/
private theorem encodeGate_garbleTable (k : ℕ) (f : XorAndCircuit) (coins : List Bool)
    (g : Fin (toCircuit f).size) :
    encodeGate k (PointPermute.wireWidth f.circuit.n (toCircuit f).size) (toCircuit f)
        (garbleTable (toCircuit f) (CCR.atLevel hash k) (slotTweak _ k)
          (CCR.offset (offsetKey k coins))
          (zeroLabels (toCircuit f) (CCR.atLevel hash k) (slotTweak _ k)
            (CCR.offset (offsetKey k coins)) (inputLabels k coins))) g =
      gateWord hash k (PointPermute.wireWidth f.circuit.n f.circuit.q) f.circuit
        (offsetWord k coins)
        (zeroWords hash k f.circuit coins f.circuit.q) (g.cast (size_toCircuit f)) := by
  set W := zeroLabels (toCircuit f) (CCR.atLevel hash k) (slotTweak _ k)
    (CCR.offset (offsetKey k coins)) (inputLabels k coins) with hWdef
  have hA₁ := f.isValid.one_le_A (g.cast (size_toCircuit f))
  have hAB := f.isValid.A_lt_B (g.cast (size_toCircuit f))
  have hBg := f.isValid.B_lt_gate (g.cast (size_toCircuit f))
  simp only [ConventionalCircuit.topo, Fin.val_cast] at hA₁ hAB hBg
  have hgs := g.isLt
  rw [encodeGate_toCircuit, zeroWords_q, ← hWdef]
  simp only [gateWord]
  rw [getD_ofFn_labels W (by omega), getD_ofFn_labels W (by omega),
    ← left_toCircuit f g, ← right_toCircuit f g]
  cases hG : f.circuit.G (g.cast (size_toCircuit f)) true true
  · have hop : op (toCircuit f) g = .xor := by simp [op_toCircuit, opOf, hG]
    simp only [hop, reduceCtorEq, ↓reduceDIte, Bool.false_eq_true, ↓reduceIte]
  · have hop : op (toCircuit f) g = .and := by simp [op_toCircuit, opOf, hG]
    simp only [hop, ↓reduceDIte, ↓reduceIte, garbleTable, Slot.gate, Bool.false_eq_true,
      Fin.val_cast, labelBits_genCt hash k g (ofFn_slotTweak _ k g hop false),
      labelBits_evCt hash k g (ofFn_slotTweak _ k g hop true), labelBits_offset]

/-- **The garbler computes the typed garbling.** At parameter `k`, `Gb` on any coins writes the
words of the typed half-gates garbling `garbleWith` of `toCircuit f`, with the hash
`CCR.atLevel hash k`, the tweaks `slotTweak` and the offset key and input zero labels read from
the coins. -/
theorem gb_eq_encodeGarbled (k : ℕ) (f : XorAndCircuit) (coins : List Bool) :
    (scheme hash).gb k f coins = encodeGarbled k f
      (garbleWith (toCircuit f) (CCR.atLevel hash k) (slotTweak _ k) (offsetKey k coins)
        (inputLabels k coins)) := by
  set W := zeroLabels (toCircuit f) (CCR.atLevel hash k) (slotTweak _ k)
    (CCR.offset (offsetKey k coins)) (inputLabels k coins) with hWdef
  have hsize := size_toCircuit f
  simp only [scheme, encodeGarbled, garbleWith, Scheme.Garbled.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · simp only [fnWord, encodeFn, encodeGate_garbleTable]
    congr 2
    · rw [size_toCircuit]
    · rw [List.ofFn_congr (size_toCircuit f)]
      rfl
  · simp only [encInfoWord, labelBits_add, labelBits_inputLabels,
      labelBits_bitOffset, labelBits_offset]
  · simp only [decInfoWord, zeroWords_q, ← hWdef]
    congr 1
    funext o
    have hm := f.isValid.m_le_q
    simp only [ConventionalCircuit.topo] at hm
    have hout : (Wire.ofNat (f.circuit.n + f.circuit.q - f.circuit.m + o) (by omega) :
        Wire f.circuit.n (toCircuit f).size) = (toCircuit f).outputs o :=
      Wire.toNat_injective (by rw [Wire.toNat_ofNat, toNat_outputs_toCircuit])
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp [show f.circuit.n + f.circuit.q - f.circuit.m + o < f.circuit.n + (toCircuit f).size by
        omega, hout,
      colourWord_labelBits]

/-! ### Evaluation -/

/-- The parts of a gate block followed by more of the body: its two wire numbers, its flag bit,
and its ciphertexts with the rest. -/
theorem block_parts {w : ℕ} {a b cts more : List Bool} (d : Bool) (ha : a.length = w)
    (hb : b.length = w) :
    (a ++ b ++ [d] ++ cts ++ more).take w = a ∧
      ((a ++ b ++ [d] ++ cts ++ more).drop w).take w = b ∧
      (a ++ b ++ [d] ++ cts ++ more).getD (2 * w) false = d ∧
        (a ++ b ++ [d] ++ cts ++ more).drop (2 * w + 1) = cts ++ more := by
  have hshape : a ++ b ++ [d] ++ cts ++ more = a ++ (b ++ (d :: (cts ++ more))) := by simp
  rw [hshape]
  subst ha
  refine ⟨by simp, by simp [hb], ?_, ?_⟩
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
      List.getElem?_append_right (by omega)]
    simp [hb, two_mul]
  · rw [two_mul, Nat.add_assoc, ← List.drop_drop, List.drop_left, ← hb, ← List.drop_drop,
      List.drop_left]
    rfl

/-- One gate of `Ev` on the labels of the earlier wires of a fixed point of an evaluation round, at
the position of the gate's block, appends the label of the gate and moves past the block. -/
private theorem evalGate_take (k : ℕ) (f : XorAndCircuit)
    (table : Slot (toCircuit f) → BitString (k + 1) × Bool)
    (X : Fin f.circuit.n → BitString (k + 1) × Bool)
    (A : Wire f.circuit.n (toCircuit f).size → BitString (k + 1) × Bool)
    (hA : ∀ w, evalStep (toCircuit f) (CCR.atLevel hash k) (slotTweak _ k) table X A w = A w)
    (g : Fin (toCircuit f).size) :
    evalGate hash k (PointPermute.wireWidth f.circuit.n (toCircuit f).size)
        (List.ofFn fun g => encodeGate k (PointPermute.wireWidth f.circuit.n (toCircuit f).size)
          (toCircuit f) table g).flatten
        ((List.ofFn fun v : Fin (f.circuit.n + (toCircuit f).size) =>
            labelBits (A (Wire.ofNat v v.isLt))).take (f.circuit.n + g),
          ((List.ofFn fun g => encodeGate k (PointPermute.wireWidth f.circuit.n (toCircuit f).size)
            (toCircuit f) table g).take g).flatten.length) g =
      ((List.ofFn fun v : Fin (f.circuit.n + (toCircuit f).size) =>
          labelBits (A (Wire.ofNat v v.isLt))).take (f.circuit.n + g + 1),
        ((List.ofFn fun g => encodeGate k (PointPermute.wireWidth f.circuit.n (toCircuit f).size)
          (toCircuit f) table g).take (g + 1)).flatten.length) := by
  set w := PointPermute.wireWidth f.circuit.n (toCircuit f).size with hw
  set blocks := fun g => encodeGate k w (toCircuit f) table g with hblocks
  have hl := toNat_left_lt (toCircuit f) g
  have hr := toNat_right_lt (toCircuit f) g
  have hgs := g.isLt
  have hsize : f.circuit.n + (toCircuit f).size < 2 ^ w := Nat.lt_size_self _
  have hval (a : ℕ) (ha : a ≤ f.circuit.n + g) :
      BitString.boundedBinaryValue
        ((List.ofFn fun v : Fin (f.circuit.n + (toCircuit f).size) =>
          labelBits (A (Wire.ofNat v v.isLt))).take (f.circuit.n + g)).length
        (BitString.lowBits w a).reverse = a := by
    rw [BitString.boundedBinaryValue_eq, ← ofBits_reverse, List.reverse_reverse,
      ofBits_lowBits (by omega), List.length_take, List.length_ofFn]
    omega
  have hg : (g : ℕ) < (List.ofFn blocks).length := by simp
  rw [evalGate, List.drop_flatten_take _ hg, List.length_flatten_take_succ _ hg,
    List.getElem_ofFn]
  obtain ⟨hp₁, hp₂, hp₃, hp₄⟩ := block_parts (decide (op (toCircuit f) g = .and))
    (cts := if h : op (toCircuit f) g = .and then
      labelBits (table (⟨g, h⟩, false)) ++
        labelBits (table (⟨g, h⟩, true))
      else [])
    (more := ((List.ofFn blocks).drop (g + 1)).flatten)
    (BitString.length_lowBits w ((left (toCircuit f) g).toNat + 1))
    (BitString.length_lowBits w ((right (toCircuit f) g).toNat + 1))
  simp only [hblocks, encodeGate] at hp₁ hp₂ hp₃ hp₄ ⊢
  rw [hp₁, hp₂, hp₃, ← List.drop_drop (i := k + 2) (j := 2 * w + 1), hp₄, hval _ (by omega),
    hval _ (by omega), Nat.add_sub_cancel, Nat.add_sub_cancel,
    getD_take_labels A (by omega) (by omega), getD_take_labels A (by omega) (by omega),
    Wire.ofNat_toNat, Wire.ofNat_toNat, List.take_add_one (i := f.circuit.n + g),
    List.getElem?_ofFn]
  have hgate : (Wire.ofNat (f.circuit.n + g) (by omega) : Wire f.circuit.n (toCircuit f).size) =
      .gate g := Wire.toNat_injective (by simp)
  simp only [show f.circuit.n + g < f.circuit.n + (toCircuit f).size by omega, dite_true,
    Option.toList_some, hgate, ← hA (.gate g), evalStep]
  by_cases hop : op (toCircuit f) g = .and
  · simp only [hop, decide_true, ↓reduceIte, dite_true, List.append_assoc,
      List.take_left' (length_labelBits _),
      List.drop_left' (length_labelBits _),
      labelBits_andEval hash k g (ofFn_slotTweak _ k g hop false) (ofFn_slotTweak _ k g hop true),
      List.length_append, BitString.length_lowBits, List.length_singleton,
      length_labelBits]
    exact Prod.ext rfl (by omega)
  · simp only [hop, decide_false, Bool.false_eq_true, ↓reduceIte, dite_false,
      labelBits_add, List.length_append, BitString.length_lowBits,
      List.length_singleton, List.length_nil]
    exact Prod.ext rfl (by omega)

/-- **`Ev` follows a fixed point of an evaluation round.** If the labelling `A` of the wires of
`toCircuit f` is left unchanged by one round of the typed evaluation of `table` on the input labels
`X`, then `Ev` on the garbled function of `table` and the words of `X` returns the labels `A` of the
output wires. -/
theorem evalWord_encodeFn (k : ℕ) (f : XorAndCircuit)
    (table : Slot (toCircuit f) → BitString (k + 1) × Bool)
    (X : Fin f.circuit.n → BitString (k + 1) × Bool)
    (A : Wire f.circuit.n (toCircuit f).size → BitString (k + 1) × Bool)
    (hA : ∀ w, evalStep (toCircuit f) (CCR.atLevel hash k) (slotTweak _ k) table X A w = A w) :
    evalWord hash (encodeFn k (toCircuit f) table)
        (List.ofFn fun i => labelBits (X i)).flatten =
      (List.ofFn fun o => labelBits (A ((toCircuit f).outputs o))).flatten := by
  have hinit : BitString.listRows f.circuit.n (k + 2)
      (List.ofFn fun i => labelBits (X i)).flatten =
      (List.ofFn fun v : Fin (f.circuit.n + (toCircuit f).size) =>
        labelBits (A (Wire.ofNat v v.isLt))).take f.circuit.n := by
    apply List.ext_getElem (by simp)
    intro i h₁ h₂
    simp only [BitString.length_listRows] at h₁
    have hin : (Wire.ofNat i (by omega) : Wire f.circuit.n (toCircuit f).size) = .input ⟨i, h₁⟩ :=
      Wire.toNat_injective (by simp)
    simp only [BitString.listRows, List.getElem_map, List.getElem_range, List.getElem_take,
      List.getElem_ofFn, hin, ← hA (.input ⟨i, h₁⟩), evalStep]
    exact BitString.listRow_flatten_ofFn (fun i => labelBits (X i))
      (fun _ => length_labelBits _) ⟨i, h₁⟩
  have hfold : ∀ g ≤ (toCircuit f).size,
      (List.range g).foldl (evalGate hash k (PointPermute.wireWidth f.circuit.n (toCircuit f).size)
          (List.ofFn fun g => encodeGate k (PointPermute.wireWidth f.circuit.n (toCircuit f).size)
            (toCircuit f) table g).flatten)
        (BitString.listRows f.circuit.n (k + 2)
          (List.ofFn fun i => labelBits (X i)).flatten, 0) =
      ((List.ofFn fun v : Fin (f.circuit.n + (toCircuit f).size) =>
          labelBits (A (Wire.ofNat v v.isLt))).take (f.circuit.n + g),
        ((List.ofFn fun g => encodeGate k (PointPermute.wireWidth f.circuit.n (toCircuit f).size)
          (toCircuit f) table g).take g).flatten.length) := by
    intro g hg
    induction g with
    | zero => simp [hinit]
    | succ g ih =>
      rw [List.range_succ, List.foldl_append, ih (by omega), List.foldl_cons, List.foldl_nil]
      exact evalGate_take hash k f table X A hA ⟨g, by omega⟩
  simp only [evalWord, encodeFn, PointPermute.fnDecoder.decode_enc]
  rw [hfold _ le_rfl, List.take_of_length_le (by simp)]
  have hm := f.isValid.m_le_q
  have hq := size_toCircuit f
  simp only [ConventionalCircuit.topo] at hm
  congr 1
  apply List.ext_getElem (by simp; omega)
  intro o h₁ h₂
  simp only [List.length_ofFn] at h₂
  have hout : (Wire.ofNat (f.circuit.n + (toCircuit f).size - f.circuit.m + o) (by omega) :
      Wire f.circuit.n (toCircuit f).size) = (toCircuit f).outputs ⟨o, h₂⟩ :=
    Wire.toNat_injective (by rw [Wire.toNat_ofNat, toNat_outputs_toCircuit, hq])
  simp only [List.getElem_drop, List.getElem_ofFn, hout]

/-! ### Correctness -/

/-- **Correctness**: decoding the evaluation of an encoded input gives the circuit's output, for
every hash family. -/
theorem scheme_correct : (scheme hash).Correct := by
  intro k _ f x hx g hg
  obtain ⟨coins, -, rfl⟩ := (scheme hash).mem_support_eval_garble_iff.mp hg
  replace hx : x.length = f.circuit.n := hx
  have hK : ∀ y : BitString (k + 1), y + y = 0 := BitString.add_self
  set W := zeroLabels (toCircuit f) (CCR.atLevel hash k) (slotTweak _ k)
    (CCR.offset (offsetKey k coins)) (inputLabels k coins) with hWdef
  have hfix := evalStep_activeLabel (toCircuit f) hK (CCR.atLevel hash k) (slotTweak _ k)
    (offsetKey k coins) (inputLabels k coins) (BitString.ofList f.circuit.n x) W
    (zeroLabels_isFixed _ _ _ _ _)
  have hev := (isLocal_evalStep_const (toCircuit f) (CCR.atLevel hash k) (slotTweak _ k) _
    _).iterate_eq_of_isFixed 0 hfix
  have hrun := Garbled.run_garbleWith (toCircuit f) hK (CCR.atLevel hash k) (slotTweak _ k)
    (offsetKey k coins) (inputLabels k coins) (BitString.ofList f.circuit.n x)
  rw [gb_eq_encodeGarbled]
  simp only [scheme, encodeGarbled, garbleWith]
  rw [PointPermute.projectiveEncode_labelBits (n := f.circuit.n)
      (fun i b => inputLabels k coins i + bitOffset (CCR.offset (offsetKey k coins)) b) hx,
    evalWord_encodeFn hash k f _ _ _ (fun w => congrFun hfix w), PointPermute.decodeWord_ofFn]
  conv_rhs => rw [← BitString.ofFn_ofList hx, ← eval_toCircuit, ← hrun]
  congr 2 with o
  simp only [Garbled.run, evaluate, garbleWith, Garbling.decode]
  exact congrArg (fun y : BitString (k + 1) × Bool => y.2 + _)
    (congrFun hev ((toCircuit f).outputs o)).symm

end Cslib.Crypto.Garbling.HalfGates
