/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.CircularCorrelationRobust
public import CslibFrontier.Crypto.Primitives.Garbling.Conventional
public import CslibFrontier.Crypto.Primitives.Garbling.FreeXOR
public import CslibFrontier.Crypto.Primitives.Garbling.HalfGates.Scheme
public import CslibFrontier.Crypto.Primitives.Garbling.PointPermute
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.OfBits
import CslibFrontier.Crypto.Primitives.Garbling.PointPermute.Simulator
import CslibFrontier.Foundations.Data.List.Flatten

/-!
# Free-XOR garbling as a garbling scheme

Definitions and correctness only. Later parts of this series add efficiency certificates, a word
simulator, and simulation privacy (`prv.sim`) under `CircularCorrelationRobust`.

The Free-XOR garbling of `CslibFrontier.Crypto.Primitives.Garbling.FreeXOR`, after Kolesnikov and
Schneider [KolesnikovSchneider2008] and Choi, Katz, Kumaresan and Zhou
[ChoiKatzKumaresanZhou2012], as a garbling scheme in the sense of Bellare, Hoang and Rogaway
[BellareHoangRogaway2012] (`Garbling.Scheme`) over valid conventional circuits (`ValidCircuit`):
`FreeXOR.scheme hash`, with the hash family `hash`. Every gate whose truth table is XOR is marked
free and emits no garbled rows; every other gate gets four point-and-permute rows masked by two
single-key calls to `H'(x, t) = CCR.atLevel hash k ((x, false), t)`.

At security parameter `k`, a label is a `(k + 1)`-bit key followed by its colour bit. Slot `a` of
row `i` of gate `g` has the tweak `8 g + 2 i + a` reduced modulo `2 ^ k` (`PointPermute.tweak`).
The coins are the `k + 1` bits of the offset key `R`, then the `n + q` base labels of the `n`
input wires and `q` gate wires; the offset is `CCR.offset R = (R, true)`. Correctness holds for
every hash family, even when tweaks collide (`FreeXOR.scheme_correct`).

`Gb` writes the garbled function `F` as the header `(k, n, m, q)`, in unary, followed for each gate
by its two argument wires `A g` and `B g` as `w`-bit numbers (`w` the bit length of `n + q`), a bit
that is set when the gate computes XOR, and four `(k + 2)`-bit rows when the gate does not compute
XOR. XOR gates have no rows [KolesnikovSchneider2008]. The encoding information `e` lists both
labels of each input wire, so `En` is `projectiveEncode`; the decoding information `d` lists the
colours of the zero labels of the `m` output wires, and `De` is `PointPermute.decodeWord`.

The scheme is correct (`FreeXOR.scheme_correct`) but not valid in the sense of
[BellareHoangRogaway2012] (§3.1, p. 7: the length condition requires `|F|`, `|e|`, and `|d|` to
depend only on `(k, f.n, f.m, |f|)`, and non-degeneracy requires `e` and `d` to depend only on
those and the coins). Here `|F|` depends on the number of non-XOR gates, so the length condition
fails, and `d` holds the colours of output zero labels propagated from the gate flags, so
non-degeneracy fails too. [ChoiKatzKumaresanZhou2012] (§2.2, p. 5, locator not verified) likewise
send no ciphertexts for XOR gates. Simulation privacy does not use validity.

The garbler and the evaluator are list programs. The garbler writes the typed garbling
`FreeXOR.garbleWith` of `ConventionalCircuit.toCircuit f` (`FreeXOR.gb_eq_encodeGarbled`), and the
evaluator follows every fixed point of the typed evaluation round
(`FreeXOR.evalWord_encodeFn`), so correctness follows from `FreeXOR.Garbled.run_garbleWith` and
`ConventionalCircuit.eval_toCircuit`.

## Main definitions

* `Cslib.Crypto.Garbling.FreeXOR.scheme`: Free-XOR garbling as a garbling scheme.
* `Cslib.Crypto.Garbling.FreeXOR.encodeFn`, `Cslib.Crypto.Garbling.FreeXOR.encodeGarbled`: the
  words of a typed garbled table and of a typed garbled circuit.

## Main results

* `Cslib.Crypto.Garbling.FreeXOR.gb_eq_encodeGarbled`: the garbler computes `garbleWith`.
* `Cslib.Crypto.Garbling.FreeXOR.evalWord_encodeFn`: the evaluator computes the typed evaluation.
* `Cslib.Crypto.Garbling.FreeXOR.scheme_correct`: the scheme is correct.

## References

* [V. Kolesnikov, T. Schneider, *Improved Garbled Circuit: Free XOR Gates and
  Applications*][KolesnikovSchneider2008]
* [S. G. Choi, J. Katz, R. Kumaresan, H.-S. Zhou, *On the Security of the "Free-XOR"
  Technique*][ChoiKatzKumaresanZhou2012]
* [M. Bellare, V. T. Hoang, P. Rogaway, *Foundations of Garbled Circuits*][BellareHoangRogaway2012]
-/

public section

namespace Cslib.Crypto.Garbling.FreeXOR

open Cslib.Circuits Turing.MultiTapeTM

/-! ### XOR gates -/

/-- Whether a four-bit truth table `[G 0 0, G 0 1, G 1 0, G 1 1]` is XOR. -/
@[expose] def isXorTable (t : List Bool) : Bool :=
  !t.getD 0 false && t.getD 1 false && t.getD 2 false && !t.getD 3 false

/-- Whether gate `g` of `f` computes XOR. -/
@[expose] def isXorGate (f : ConventionalCircuit) (g : Fin f.q) : Bool :=
  decide (f.G g = xor)

/-- `isXorTable` on a gate's truth table agrees with `decide (G = xor)`. -/
theorem isXorTable_eq (G : Bool → Bool → Bool) :
    isXorTable [G false false, G false true, G true false, G true true] = decide (G = xor) := by
  by_cases h : G = xor
  · subst h; decide
  · rw [decide_eq_false h]
    by_contra htrue
    apply h
    funext a b
    simp only [isXorTable, List.getD_cons_zero, List.getD_cons_succ] at htrue
    cases a <;> cases b <;> simp_all

/-! ### Words -/

variable (hash : List Bool → List Bool → List Bool)

/-- The key-only hash at parameter `k` on words: hash the `(k + 1)`-bit key of `a` paired with
colour `false` and the tweak `t`, reading the first `k + 2` bits. -/
@[expose] def keyHashWord (k : ℕ) (a t : List Bool) : List Bool :=
  HalfGates.hashWord hash k (BitString.listRow (k + 1) 0 a ++ [false]) t

/-- The base label of wire `v` read from the coins: block `v` of `k + 2` bits after the offset
key. -/
@[expose] def baseWord (k : ℕ) (coins : List Bool) (v : ℕ) : List Bool :=
  BitString.listRow (k + 2) v (coins.drop (k + 1))

/-- The zero labels of the first `n + s` wires of `f` at parameter `k`, in wire order: input wires
and non-XOR gates read their base labels from `coins`, and an XOR gate takes the sum of its
arguments' zero labels. -/
@[expose] def propagateWords (k : ℕ) (f : ConventionalCircuit) (coins : List Bool) :
    ℕ → List (List Bool)
  | 0 => List.ofFn fun i : Fin f.n => HalfGates.inputWord k coins i
  | s + 1 =>
    if h : s < f.q then
      let ws := propagateWords k f coins s
      ws ++ [if isXorGate f ⟨s, h⟩ then
        List.zipWith xor (ws.getD (f.A ⟨s, h⟩ - 1) []) (ws.getD (f.B ⟨s, h⟩ - 1) [])
      else baseWord k coins (f.n + s)]
    else propagateWords k f coins s

/-- Row `i` of non-XOR gate `g` of `f` at parameter `k`, from the offset `Δ` and the zero labels
`labels` of all wires. -/
@[expose] def rowWord (k : ℕ) (f : ConventionalCircuit) (Δ : List Bool)
    (labels : List (List Bool)) (g : Fin f.q) (i : ℕ) : List Bool :=
  let a := labels.getD (f.A g - 1) []
  let b := labels.getD (f.B g - 1) []
  let b₀ := i.testBit 1 ^^ HalfGates.colourWord k a
  let b₁ := i.testBit 0 ^^ HalfGates.colourWord k b
  let out := List.zipWith xor (labels.getD (f.n + g) []) (HalfGates.maskWord k Δ (f.G g b₀ b₁))
  let m₀ := keyHashWord hash k (List.zipWith xor a (HalfGates.maskWord k Δ b₀))
    (PointPermute.tweak k g i 0)
  let m₁ := keyHashWord hash k (List.zipWith xor b (HalfGates.maskWord k Δ b₁))
    (PointPermute.tweak k g i 1)
  List.zipWith xor out (List.zipWith xor m₀ m₁)

/-- The block of gate `g` in the garbled function, from the zero labels `labels` of all wires:
its argument wires `A g` and `B g` as `w`-bit numbers, its XOR bit, and four rows when it is not an
XOR gate. -/
@[expose] def gateWord (k w : ℕ) (f : ConventionalCircuit) (Δ : List Bool)
    (labels : List (List Bool)) (g : Fin f.q) : List Bool :=
  BitString.lowBits w (f.A g) ++ BitString.lowBits w (f.B g) ++ [isXorGate f g] ++
    if isXorGate f g then [] else
      (List.ofFn fun i : Fin 4 => rowWord hash k f Δ labels g i).flatten

/-- The garbled function of `f`: the header `(k, n, m, q)`, then the blocks of its gates. -/
@[expose] def fnWord (k : ℕ) (f : ConventionalCircuit) (coins : List Bool) : List Bool :=
  PointPermute.encFn ((k, f.n, f.m, f.q), (List.ofFn fun g : Fin f.q =>
    gateWord hash k (PointPermute.wireWidth f.n f.q) f (HalfGates.offsetWord k coins)
      (propagateWords k f coins f.q) g).flatten)

/-- The decoding information of `f`: the colours of the zero labels of its last `m` wires. -/
@[expose] def decInfoWord (k : ℕ) (f : ConventionalCircuit) (coins : List Bool) : List Bool :=
  List.ofFn fun o : Fin f.m =>
    HalfGates.colourWord k ((propagateWords k f coins f.q).getD (f.n + f.q - f.m + o) [])

/-- One gate of `Ev`, with the labels of the earlier wires and the position `pos` of the gate's
block in the body: read the gate's argument wires and their labels, and append their sum for an XOR
gate or the unmasked selected row for a non-XOR gate. -/
@[expose] def evalGate (k w : ℕ) (body : List Bool) (state : List (List Bool) × ℕ) (g : ℕ) :
    List (List Bool) × ℕ :=
  let (labels, pos) := state
  let block := body.drop pos
  let a := labels.getD
    (BitString.boundedBinaryValue labels.length (block.take w).reverse - 1) []
  let b := labels.getD
    (BitString.boundedBinaryValue labels.length ((block.drop w).take w).reverse - 1) []
  if block.getD (2 * w) false then
    (labels ++ [List.zipWith xor a b], pos + (2 * w + 1))
  else
    let i := (if HalfGates.colourWord k a then 2 else 0) +
      (if HalfGates.colourWord k b then 1 else 0)
    let row := (block.drop (2 * w + 1 + i * (k + 2))).take (k + 2)
    let unmasked := List.zipWith xor row
      (List.zipWith xor (keyHashWord hash k a (PointPermute.tweak k g i 0))
        (keyHashWord hash k b (PointPermute.tweak k g i 1)))
    (labels ++ [unmasked], pos + (2 * w + 1 + 4 * (k + 2)))

/-- `Ev(F, X)`: read the header `(k, n, m, q)` of `F`, start from the `n` labels of `X`, evaluate
the gates in order, and return the labels of the last `m` wires. -/
@[expose] def evalWord (F X : List Bool) : List Bool :=
  let ((k, n, m, q), body) := PointPermute.fnDecoder.decode F
  let (labels, _) := (List.range q).foldl (evalGate hash k (PointPermute.wireWidth n q) body)
    (BitString.listRows n (k + 2) X, 0)
  (labels.drop (n + q - m)).flatten

/-- **Free-XOR garbling** as a garbling scheme over valid conventional circuits, with the hash
family `hash`. -/
@[expose] def scheme : Scheme ValidCircuit where
  inLen f := f.1.n
  outLen f := f.1.m
  size f := f.1.q
  ev f x := f.1.evalCirc x
  coinLen k n _ q := (k + 1) + (n + q) * (k + 2)
  gb k f coins :=
    ⟨fnWord hash k f.1 coins, HalfGates.encInfoWord k f.1 coins, decInfoWord k f.1 coins⟩
  encode := projectiveEncode
  evalGarbled := evalWord hash
  decode := PointPermute.decodeWord

/-- Its length readers are `(n, m, q)` and its semantics is `ConventionalCircuit.evalCirc`. -/
theorem scheme_isCircuitScheme : (scheme hash).IsCircuitScheme :=
  ⟨fun _ => ⟨rfl, rfl, rfl⟩, fun _ _ => rfl⟩

/-! ### The typed garbling -/

open ConventionalCircuit

/-- Whether each gate of `toCircuit f` is free (computes XOR). -/
@[expose] noncomputable def freeCircuit (f : ValidCircuit) : Fin (toCircuit f).size → Bool :=
  fun g => isXorGate f.1 (g.cast (size_toCircuit f))

/-- Free gates of `toCircuit f` compute the XOR of their arguments under `fullInterpretation`. -/
theorem hfree_toCircuit (f : ValidCircuit) :
    ∀ g, freeCircuit f g = true →
      ∀ v, fullInterpretation ((toCircuit f).program.lines g).op v = ∑ k, v k := by
  intro g hg v
  have hop : ((toCircuit f).program.lines g).op =
      .fn fun a => f.1.G (g.cast (size_toCircuit f)) (a 0) (a 1) :=
    congrArg Line.op (lines_toCircuit f g)
  revert v
  rw [hop]
  intro v
  simp only [freeCircuit, isXorGate, decide_eq_true_eq] at hg
  simp only [fullInterpretation, hg]
  have hsum : ∀ w : Fin 2 → Bool, (w 0 ^^ w 1) = ∑ k : Fin 2, w k := fun w => by
    rw [Fin.sum_univ_two, Bool.add_eq_xor]
  exact hsum v

/-- Row `i` of non-free gate `g` of `τ`, with colours read in binary, first argument most
significant. -/
@[expose] def garbledRowOf {n m s : ℕ} (τ : Circuit.Topology n m s) {free : Fin s → Bool}
    (g : Fin s) (hg : free g = false) (i : ℕ) : GarbledRow τ free :=
  ⟨⟨g, hg⟩, fun a => i.testBit (τ.arity g - 1 - a)⟩

/-- The tweaks of the slots of `(τ, free)` at parameter `k`: slot `a` of row `ρ` of gate `g` gets
`PointPermute.tweak k g (PointPermute.rowIndex ρ) a`. -/
@[expose] def slotTweak {n m s : ℕ} (τ : Circuit.Topology n m s) (free : Fin s → Bool) (k : ℕ) :
    GarbledSlot τ free → BitString k
  | ⟨⟨⟨g, _⟩, colours⟩, a⟩ =>
    BitString.ofList k (PointPermute.tweak k g (PointPermute.rowIndex colours) a)

/-- The typed base labels of all wires read from the coins. -/
@[expose] def baseLabels {n s : ℕ} (k : ℕ) (coins : List Bool) (w : Wire n s) :
    BitString (k + 1) × Bool :=
  labelOfWord k (baseWord k coins w.toNat)

/-- The block of gate `g` of a garbled table over `(τ, free)` at parameter `k`: its argument wires,
from `1`, as `w`-bit numbers, its free bit, and for a non-free gate its rows in `garbledRowOf`
order. -/
@[expose] def encodeGate {n m s : ℕ} (k w : ℕ) (τ : Circuit.Topology n m s)
    (free : Fin s → Bool) (table : GarbledRow τ free → BitString (k + 1) × Bool)
    (g : Fin s) : List Bool :=
  (List.ofFn fun a => BitString.lowBits w ((τ.wires g a).toNat + 1)).flatten ++
    [free g] ++
    if hg : free g = false then
      (List.ofFn fun i : Fin (2 ^ τ.arity g) =>
        labelBits (table (garbledRowOf τ g hg i))).flatten
    else []

/-- The garbled function of a table over `(τ, free)` at parameter `k`: the header `(k, n, m, s)`,
then the blocks of the gates. -/
@[expose] def encodeFn {n m s : ℕ} (k : ℕ) (τ : Circuit.Topology n m s)
    (free : Fin s → Bool) (table : GarbledRow τ free → BitString (k + 1) × Bool) : List Bool :=
  PointPermute.encFn ((k, n, m, s), (List.ofFn fun g =>
    encodeGate k (PointPermute.wireWidth n s) τ free table g).flatten)

/-- The words `(F, e, d)` of a typed garbling of `toCircuit f` at parameter `k`. -/
@[expose] noncomputable def encodeGarbled (k : ℕ) (f : ValidCircuit)
    (G : Garbled (toCircuit f).topology (freeCircuit f) (BitString (k + 1))) : Scheme.Garbled where
  fn := encodeFn k (toCircuit f).topology (freeCircuit f) G.table
  encInfo := (List.ofFn fun j : Fin (2 * f.1.n) =>
    labelBits (G.encoding ⟨j / 2, by omega⟩ (j.val.testBit 0))).flatten
  decInfo := List.ofFn G.decoding

/-- A key-hash word has `k + 2` bits. -/
@[simp] theorem length_keyHashWord (k : ℕ) (a t : List Bool) :
    (keyHashWord hash k a t).length = k + 2 :=
  HalfGates.length_hashWord hash k _ t

/-- `CCR.atLevel hash k ((x, false), t)` as a word is `keyHashWord`. -/
theorem labelBits_atLevel_keyOnly (k : ℕ) (x : BitString (k + 1)) (t : BitString k) :
    labelBits (CCR.atLevel hash k (x, false) t) =
      keyHashWord hash k (List.ofFn x) (List.ofFn t) := by
  rw [HalfGates.labelBits_atLevel, keyHashWord]
  congr 1
  rw [BitString.listRow_zero, BitString.ofList_ofFn, labelBits_apply]

/-- `CCR.atLevel hash k ((labelOfWord k a).1, false) t` as a word is `keyHashWord`. -/
theorem labelBits_atLevel_labelOfWord (k : ℕ) (a : List Bool) (t : BitString k) :
    labelBits (CCR.atLevel hash k ((labelOfWord k a).1, false) t) =
      keyHashWord hash k a (List.ofFn t) := by
  rw [HalfGates.labelBits_atLevel, keyHashWord]
  congr 1
  rw [labelBits_apply, BitString.listRow_zero]
  rfl

/-- On a label word `a`, `keyHashWord` agrees with `CCR.atLevel` on the label's key. -/
theorem labelBits_atLevel_key {k : ℕ} (x : BitString (k + 1) × Bool) (t : BitString k) :
    labelBits (CCR.atLevel hash k (x.1, false) t) =
      keyHashWord hash k (labelBits x) (List.ofFn t) := by
  rw [labelBits_atLevel_keyOnly, keyHashWord, keyHashWord]
  congr 2
  rw [BitString.listRow_zero, BitString.listRow_zero, BitString.ofFn_ofList_eq_take,
    BitString.ofFn_ofList_eq_take, List.take_append_of_le_length (by simp),
    List.take_append_of_le_length (by simp [length_labelBits]), take_labelBits,
    List.take_of_length_le (by simp)]

private theorem ofFn_slotTweak_mk {k : ℕ} (f : ValidCircuit) (g : Fin (toCircuit f).size)
    (hg : freeCircuit f g = false) (colours : Fin ((toCircuit f).topology.arity g) → Bool)
    (a : Fin ((toCircuit f).topology.arity g)) :
    List.ofFn (slotTweak (toCircuit f).topology (freeCircuit f) k ⟨⟨⟨g, hg⟩, colours⟩, a⟩) =
      PointPermute.tweak k g (PointPermute.rowIndex colours) a :=
  BitString.ofFn_ofList (by simp [PointPermute.tweak])

/-- The tweak of `garbledRowOf` for `i < 4` is `PointPermute.tweak k g i a`. -/
theorem ofFn_slotTweak_garbledRowOf (f : ValidCircuit) (k : ℕ) (g : Fin (toCircuit f).size)
    (hg : freeCircuit f g = false) {i : ℕ} (hi : i < 4) (a : Fin ((toCircuit f).topology.arity g)) :
    List.ofFn (slotTweak (toCircuit f).topology (freeCircuit f) k
        ⟨garbledRowOf _ g hg i, a⟩) = PointPermute.tweak k g i a := by
  have harity := arity_topology_toCircuit f g
  dsimp only [slotTweak, garbledRowOf]
  rw [PointPermute.rowIndex_testBit_of_eq_two harity hi,
    BitString.ofFn_ofList (by simp [PointPermute.tweak])]

private theorem wires_toCircuit_zero (f : ValidCircuit) (g : Fin (toCircuit f).size)
    (hlt : f.1.A (g.cast (size_toCircuit f)) - 1 < f.1.n + (toCircuit f).size) :
    (toCircuit f).topology.wires g (Fin.cast (arity_topology_toCircuit f g).symm 0) =
      Wire.ofNat (f.1.A (g.cast (size_toCircuit f)) - 1) hlt := by
  have harity := arity_topology_toCircuit f g
  rw [show Fin.cast harity.symm 0 = ⟨0, by omega⟩ from Fin.ext rfl]
  refine Wire.toNat_injective ?_
  have h := congrArg (fun l => l.getD 0 0) (ofFn_toNat_wires_toCircuit f g)
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn,
    show 0 < (toCircuit f).topology.arity g by omega, ↓reduceDIte, Option.getD_some] at h
  rw [Wire.toNat_ofNat]
  exact h

private theorem wires_toCircuit_one (f : ValidCircuit) (g : Fin (toCircuit f).size)
    (hlt : f.1.B (g.cast (size_toCircuit f)) - 1 < f.1.n + (toCircuit f).size) :
    (toCircuit f).topology.wires g (Fin.cast (arity_topology_toCircuit f g).symm 1) =
      Wire.ofNat (f.1.B (g.cast (size_toCircuit f)) - 1) hlt := by
  have harity := arity_topology_toCircuit f g
  rw [show Fin.cast harity.symm 1 = ⟨1, by omega⟩ from Fin.ext rfl]
  refine Wire.toNat_injective ?_
  have h := congrArg (fun l => l.getD 1 0) (ofFn_toNat_wires_toCircuit f g)
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn,
    show 1 < (toCircuit f).topology.arity g by omega, ↓reduceDIte, Option.getD_some] at h
  rw [Wire.toNat_ofNat]
  exact h

/-- A base label read from the coins, as a word, is `baseWord`. -/
theorem labelBits_baseLabels {n s : ℕ} (k : ℕ) (coins : List Bool) (w : Wire n s) :
    labelBits (baseLabels k coins w) = baseWord k coins w.toNat :=
  labelBits_labelOfWord (BitString.length_listRow _ _ _)

/-- **The garbler's zero labels are the typed propagated zero labels.** -/
theorem propagateWords_eq (k : ℕ) (f : ValidCircuit) (coins : List Bool) {s : ℕ}
    (hs : s ≤ f.1.q) :
    propagateWords k f.1 coins s =
      (List.ofFn fun v : Fin (f.1.n + (toCircuit f).size) =>
        labelBits (propagate (toCircuit f).topology (freeCircuit f)
          (baseLabels k coins) (Wire.ofNat v v.isLt))).take (f.1.n + s) := by
  have hτ := (toCircuit f).isOrdered_topology
  induction s with
  | zero =>
    apply List.ext_getElem (by simp [propagateWords])
    intro i h₁ h₂
    simp only [propagateWords, List.length_ofFn] at h₁
    have hin : (Wire.ofNat i (by omega) : Wire f.1.n (toCircuit f).size) = .input ⟨i, h₁⟩ :=
      Wire.toNat_injective (by simp)
    simp only [propagateWords, List.getElem_ofFn, List.getElem_take, hin,
      propagate_input hτ, labelBits_baseLabels, Wire.toNat_input]
    rfl
  | succ s ih =>
    have hsq : s < f.1.q := hs
    have hsize := size_toCircuit f
    set g : Fin (toCircuit f).size := ⟨s, by omega⟩ with hg
    have hgcast : g.cast (size_toCircuit f) = ⟨s, hsq⟩ := Fin.ext rfl
    have hA₁ := f.2.one_le_A ⟨s, hsq⟩
    have hAB := f.2.A_lt_B ⟨s, hsq⟩
    have hBg := f.2.B_lt_gate ⟨s, hsq⟩
    simp only [ConventionalCircuit.topo] at hA₁ hAB hBg
    rw [propagateWords, dite_eq_left hsq]
    dsimp only
    rw [ih hsq.le, ← Nat.add_assoc, List.take_add_one, List.getElem?_ofFn]
    have hgate : (Wire.ofNat (f.1.n + s) (by omega) : Wire f.1.n (toCircuit f).size) =
        .gate g := Wire.toNat_injective (by simp [hg])
    simp only [show f.1.n + s < f.1.n + (toCircuit f).size by omega, dite_true,
      Option.toList_some, hgate]
    congr 1
    have hfree_eq : isXorGate f.1 ⟨s, hsq⟩ = freeCircuit f g := by simp [freeCircuit, hgcast]
    rw [hfree_eq]
    by_cases hfr : freeCircuit f g = true
    · rw [ite_eq_left hfr, propagate_gate_of_free hτ (baseLabels k coins) hfr,
        ← Fin.sum_congr' _ (arity_topology_toCircuit f g).symm, Fin.sum_univ_two, labelBits_add]
      have hl := wires_toCircuit_zero f g (by rw [hgcast]; omega)
      have hr := wires_toCircuit_one f g (by rw [hgcast]; omega)
      simp only [hgcast] at hl hr
      rw [hl, hr,
        HalfGates.getD_take_labels (propagate (toCircuit f).topology (freeCircuit f)
          (baseLabels k coins)) (by omega) (by omega),
        HalfGates.getD_take_labels (propagate (toCircuit f).topology (freeCircuit f)
          (baseLabels k coins)) (by omega) (by omega)]
    · have hfr' : freeCircuit f g = false := Bool.eq_false_iff.mpr hfr
      rw [ite_eq_right hfr, propagate_gate_of_not_free hτ (baseLabels k coins) hfr',
        labelBits_baseLabels, Wire.toNat_gate, hg]

private theorem propagateWords_q (k : ℕ) (f : ValidCircuit) (coins : List Bool) :
    propagateWords k f.1 coins f.1.q =
      List.ofFn fun v : Fin (f.1.n + (toCircuit f).size) =>
        labelBits (propagate (toCircuit f).topology (freeCircuit f)
          (baseLabels k coins) (Wire.ofNat v v.isLt)) := by
  rw [propagateWords_eq k f coins le_rfl, List.take_of_length_le (by simp [size_toCircuit])]

/-- Gate `g` of a typed garbled table over `toCircuit f`, as a word. -/
theorem encodeGate_toCircuit (k : ℕ) (f : ValidCircuit)
    (table : GarbledRow (toCircuit f).topology (freeCircuit f) → BitString (k + 1) × Bool)
    (g : Fin (toCircuit f).size) :
    encodeGate k (PointPermute.wireWidth f.1.n (toCircuit f).size) (toCircuit f).topology
        (freeCircuit f) table g =
      BitString.lowBits (PointPermute.wireWidth f.1.n f.1.q)
          (f.1.A (g.cast (size_toCircuit f))) ++
        BitString.lowBits (PointPermute.wireWidth f.1.n f.1.q)
          (f.1.B (g.cast (size_toCircuit f))) ++
        [isXorGate f.1 (g.cast (size_toCircuit f))] ++
        if hg : freeCircuit f g = false then
          (List.ofFn fun i : Fin 4 => labelBits (table (garbledRowOf _ g hg i))).flatten
        else [] := by
  have hA := f.2.one_le_A (g.cast (size_toCircuit f))
  have hB := f.2.A_lt_B (g.cast (size_toCircuit f))
  simp only [ConventionalCircuit.topo] at hA hB
  have hw : PointPermute.wireWidth f.1.n (toCircuit f).size =
      PointPermute.wireWidth f.1.n f.1.q := by rw [size_toCircuit]
  have hwires : (List.ofFn fun a => BitString.lowBits (PointPermute.wireWidth f.1.n f.1.q)
      (((toCircuit f).topology.wires g a).toNat + 1)).flatten =
      BitString.lowBits (PointPermute.wireWidth f.1.n f.1.q) (f.1.A (g.cast (size_toCircuit f))) ++
        BitString.lowBits (PointPermute.wireWidth f.1.n f.1.q)
          (f.1.B (g.cast (size_toCircuit f))) := by
    have hmap : (List.ofFn fun a => BitString.lowBits (PointPermute.wireWidth f.1.n f.1.q)
        (((toCircuit f).topology.wires g a).toNat + 1)) =
        (List.ofFn fun a => ((toCircuit f).topology.wires g a).toNat).map
          (fun v => BitString.lowBits (PointPermute.wireWidth f.1.n f.1.q) (v + 1)) := by
      rw [List.map_ofFn]; rfl
    rw [hmap, ofFn_toNat_wires_toCircuit]
    simp [Nat.sub_add_cancel hA, Nat.sub_add_cancel (hA.trans hB.le)]
  rw [encodeGate, hw, hwires]
  congr 1
  split_ifs with hg
  · have harity : 2 ^ (toCircuit f).topology.arity g = 4 := by
      rw [arity_topology_toCircuit]; rfl
    exact congrArg List.flatten (List.ofFn_congr harity _)
  · rfl

private theorem rowWord_garbleTable (k : ℕ) (f : ValidCircuit) (coins : List Bool)
    (g : Fin (toCircuit f).size) (hg : freeCircuit f g = false) {i : ℕ} (hi : i < 4) :
    labelBits (garbleTable (toCircuit f) fullInterpretation
        (fun key t => CCR.atLevel hash k (key, false) t)
        (slotTweak (toCircuit f).topology (freeCircuit f) k)
        (HalfGates.offsetKey k coins)
        (propagate (toCircuit f).topology (freeCircuit f) (baseLabels k coins))
        (garbledRowOf _ g hg i)) =
      rowWord hash k f.1 (HalfGates.offsetWord k coins)
        (propagateWords k f.1 coins f.1.q) (g.cast (size_toCircuit f)) i := by
  have hsize := size_toCircuit f
  have harity := arity_topology_toCircuit f g
  have hA₁ := f.2.one_le_A (g.cast (size_toCircuit f))
  have hAB := f.2.A_lt_B (g.cast (size_toCircuit f))
  have hBg := f.2.B_lt_gate (g.cast (size_toCircuit f))
  simp only [ConventionalCircuit.topo, Fin.val_cast] at hA₁ hAB hBg
  have hgs := g.isLt
  have hw₀ := wires_toCircuit_zero f g (by omega)
  have hw₁ := wires_toCircuit_one f g (by omega)
  have hc₀ : (Fin.cast harity.symm 0 : Fin ((toCircuit f).topology.arity g)) = ⟨0, by omega⟩ :=
    Fin.ext rfl
  have hc₁ : (Fin.cast harity.symm 1 : Fin ((toCircuit f).topology.arity g)) = ⟨1, by omega⟩ :=
    Fin.ext rfl
  rw [propagateWords_q]
  simp only [rowWord, Fin.val_cast,
    HalfGates.getD_ofFn_labels (propagate (toCircuit f).topology (freeCircuit f)
      (baseLabels k coins)) (i := f.1.n + g.val) (by omega),
    HalfGates.getD_ofFn_labels (propagate (toCircuit f).topology (freeCircuit f)
      (baseLabels k coins)) (i := f.1.A (g.cast (size_toCircuit f)) - 1) (by omega),
    HalfGates.getD_ofFn_labels (propagate (toCircuit f).topology (freeCircuit f)
      (baseLabels k coins)) (i := f.1.B (g.cast (size_toCircuit f)) - 1) (by omega)]
  set W := propagate (toCircuit f).topology (freeCircuit f) (baseLabels k coins)
  have hWg : (Wire.ofNat (f.1.n + g.val) (by omega) : Wire f.1.n (toCircuit f).size) = .gate g :=
    Wire.toNat_injective (by simp)
  have hWa : (Wire.ofNat (f.1.A (g.cast (size_toCircuit f)) - 1) (by omega) :
      Wire f.1.n (toCircuit f).size) =
      (toCircuit f).topology.wires g (Fin.cast harity.symm 0) := hw₀.symm
  have hWb : (Wire.ofNat (f.1.B (g.cast (size_toCircuit f)) - 1) (by omega) :
      Wire f.1.n (toCircuit f).size) =
      (toCircuit f).topology.wires g (Fin.cast harity.symm 1) := hw₁.symm
  rw [hWg, hWa, hWb]
  simp only [garbleTable, GarbledRow.gate, labelBits_add, label, garbledRowOf]
  have hsum : (∑ k_1 : Fin ((toCircuit f).topology.arity g),
      CCR.atLevel hash k
        ((W ((toCircuit f).topology.wires g k_1) +
            bitOffset (HalfGates.offsetKey k coins, true)
              (i.testBit ((toCircuit f).topology.arity g - 1 - k_1.val) +
                (W ((toCircuit f).topology.wires g k_1)).2)).1,
          false)
        (slotTweak (toCircuit f).topology (freeCircuit f) k
          ⟨⟨⟨g, hg⟩, fun a => i.testBit ((toCircuit f).topology.arity g - 1 - a.val)⟩,
            k_1⟩)) =
      ∑ k_1 : Fin 2, CCR.atLevel hash k
        ((W ((toCircuit f).topology.wires g (Fin.cast harity.symm k_1)) +
            bitOffset (HalfGates.offsetKey k coins, true)
              (i.testBit ((toCircuit f).topology.arity g - 1 -
                  (Fin.cast harity.symm k_1 : Fin _).val) +
                (W ((toCircuit f).topology.wires g (Fin.cast harity.symm k_1))).2)).1,
          false)
        (slotTweak (toCircuit f).topology (freeCircuit f) k
          ⟨⟨⟨g, hg⟩, fun a => i.testBit ((toCircuit f).topology.arity g - 1 - a.val)⟩,
            Fin.cast harity.symm k_1⟩) :=
    (Fin.sum_congr' _ harity.symm).symm
  erw [hsum]
  rw [Fin.sum_univ_two, labelBits_add, hc₀, hc₁]
  have hlines := lines_toCircuit f g
  have hbit : fullInterpretation ((toCircuit f).program.lines g).op
      (fun m => i.testBit ((toCircuit f).topology.arity g - 1 - m.val) +
        (W ((toCircuit f).topology.wires g m)).2) =
      f.1.G (g.cast (size_toCircuit f))
        (i.testBit 1 ^^ HalfGates.colourWord k (labelBits (W ((toCircuit f).topology.wires g
          (Fin.cast harity.symm 0)))))
        (i.testBit 0 ^^ HalfGates.colourWord k (labelBits (W ((toCircuit f).topology.wires g
          (Fin.cast harity.symm 1))))) := by
    have hop : ((toCircuit f).program.lines g).op =
        .fn fun a => f.1.G (g.cast (size_toCircuit f)) (a 0) (a 1) := congrArg Line.op hlines
    have hfin :
        ∀ ffn : Fin ((fullSignature 2 Bool).Arity ((toCircuit f).program.lines g).op) → Bool,
        (∀ a : Fin 2, ffn (Fin.cast (by rw [hop]; rfl) a) =
          (i.testBit (1 - a.val) ^^ HalfGates.colourWord k (labelBits (W
            ((toCircuit f).topology.wires g (Fin.cast harity.symm a)))))) →
        fullInterpretation ((toCircuit f).program.lines g).op ffn =
          f.1.G (g.cast (size_toCircuit f))
            (i.testBit 1 ^^ HalfGates.colourWord k (labelBits (W ((toCircuit f).topology.wires g
              (Fin.cast harity.symm 0)))))
            (i.testBit 0 ^^ HalfGates.colourWord k (labelBits (W ((toCircuit f).topology.wires g
              (Fin.cast harity.symm 1))))) := by
      revert hop
      generalize ((toCircuit f).program.lines g).op = op
      intro hop ffn hffn
      subst hop
      rw [fullInterpretation]
      exact congrArg₂ (f.1.G (g.cast (size_toCircuit f))) (hffn 0) (hffn 1)
    apply hfin
    intro a
    fin_cases a
    · simp only [Nat.sub_zero, harity, HalfGates.colourWord_labelBits, Bool.add_eq_xor]
      rfl
    · simp only [harity, HalfGates.colourWord_labelBits, Bool.add_eq_xor]
      rfl
  have hb₀ : i.testBit ((toCircuit f).topology.arity g - 1 - (Fin.cast harity.symm 0 : Fin _).val) +
      (W ((toCircuit f).topology.wires g (Fin.cast harity.symm 0))).2 =
      (i.testBit 1 ^^ HalfGates.colourWord k (labelBits (W ((toCircuit f).topology.wires g
        (Fin.cast harity.symm 0))))) := by
    simp only [HalfGates.colourWord_labelBits, Bool.add_eq_xor, hc₀, harity]
  have hb₁ : i.testBit ((toCircuit f).topology.arity g - 1 - (Fin.cast harity.symm 1 : Fin _).val) +
      (W ((toCircuit f).topology.wires g (Fin.cast harity.symm 1))).2 =
      (i.testBit 0 ^^ HalfGates.colourWord k (labelBits (W ((toCircuit f).topology.wires g
        (Fin.cast harity.symm 1))))) := by
    simp only [HalfGates.colourWord_labelBits, Bool.add_eq_xor, hc₁, harity]
  erw [hbit]
  rw [show (HalfGates.offsetKey k coins, true) = CCR.offset (HalfGates.offsetKey k coins) from rfl,
    HalfGates.labelBits_bitOffset, HalfGates.labelBits_offset]
  congr 1
  congr 1
  · rw [labelBits_atLevel_key, labelBits_add, HalfGates.labelBits_bitOffset,
      HalfGates.labelBits_offset]
    have ht₀ := ofFn_slotTweak_garbledRowOf f k g hg hi (Fin.cast harity.symm 0)
    dsimp only [garbledRowOf] at ht₀
    rw [hc₀] at ht₀ hb₀
    rw [ht₀, hb₀]
  · rw [labelBits_atLevel_key, labelBits_add, HalfGates.labelBits_bitOffset,
      HalfGates.labelBits_offset]
    have ht₁ := ofFn_slotTweak_garbledRowOf f k g hg hi (Fin.cast harity.symm 1)
    dsimp only [garbledRowOf] at ht₁
    rw [hc₁] at ht₁ hb₁
    rw [ht₁, hb₁]

private theorem encodeGate_garbleTable (k : ℕ) (f : ValidCircuit) (coins : List Bool)
    (g : Fin (toCircuit f).size) :
    encodeGate k (PointPermute.wireWidth f.1.n (toCircuit f).size) (toCircuit f).topology
        (freeCircuit f)
        (garbleTable (toCircuit f) fullInterpretation
          (fun key t => CCR.atLevel hash k (key, false) t)
          (slotTweak (toCircuit f).topology (freeCircuit f) k)
          (HalfGates.offsetKey k coins)
          (propagate (toCircuit f).topology (freeCircuit f) (baseLabels k coins))) g =
      gateWord hash k (PointPermute.wireWidth f.1.n f.1.q) f.1
        (HalfGates.offsetWord k coins) (propagateWords k f.1 coins f.1.q)
        (g.cast (size_toCircuit f)) := by
  rw [encodeGate_toCircuit]
  simp only [gateWord]
  have hfeq : isXorGate f.1 (g.cast (size_toCircuit f)) = freeCircuit f g := rfl
  rw [hfeq]
  by_cases hg : freeCircuit f g = true
  · have hg' : ¬ freeCircuit f g = false := by simp [hg]
    rw [dite_eq_right hg', ite_eq_left hg]
  · have hg' : freeCircuit f g = false := Bool.eq_false_iff.mpr hg
    rw [dite_eq_left hg', ite_eq_right hg]
    refine congrArg (_ ++ ·) (congrArg List.flatten (congrArg List.ofFn (funext fun i => ?_)))
    exact rowWord_garbleTable hash k f coins g hg' i.isLt

/-- **The garbler computes the typed garbling.** At parameter `k`, `Gb` on any coins writes the
words of the typed Free-XOR garbling `garbleWith` of `ConventionalCircuit.toCircuit f`, with the
hash `fun key t => CCR.atLevel hash k (key, false) t`, the tweaks `slotTweak` and the offset key
and base labels read from the coins. -/
theorem gb_eq_encodeGarbled (k : ℕ) (f : ValidCircuit) (coins : List Bool) :
    (scheme hash).gb k f coins = encodeGarbled k f
      (garbleWith (toCircuit f) fullInterpretation
        (fun key t => CCR.atLevel hash k (key, false) t)
        (slotTweak (toCircuit f).topology (freeCircuit f) k)
        (HalfGates.offsetKey k coins) (baseLabels k coins)) := by
  have hτ := (toCircuit f).isOrdered_topology
  simp only [scheme, encodeGarbled, garbleWith, Scheme.Garbled.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · simp only [fnWord, encodeFn, encodeGate_garbleTable]
    congr 2
    · rw [size_toCircuit]
    · rw [List.ofFn_congr (size_toCircuit f)]
      rfl
  · simp only [HalfGates.encInfoWord, label, labelBits_add, propagate_input hτ]
    refine congrArg List.flatten (congrArg List.ofFn (funext fun j => ?_))
    rw [labelBits_baseLabels, Wire.toNat_input,
      show (HalfGates.offsetKey k coins, true) = CCR.offset (HalfGates.offsetKey k coins) from rfl,
      HalfGates.labelBits_bitOffset, HalfGates.labelBits_offset]
    rfl
  · simp only [decInfoWord, propagateWords_q]
    refine congrArg List.ofFn (funext fun o => ?_)
    have hm := f.2.m_le_q
    have hsize := size_toCircuit f
    simp only [ConventionalCircuit.topo] at hm
    have hout : (Wire.ofNat (f.1.n + f.1.q - f.1.m + o) (by omega) :
        Wire f.1.n (toCircuit f).size) = (toCircuit f).outputs o :=
      Wire.toNat_injective (by rw [Wire.toNat_ofNat, toNat_outputs_toCircuit])
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn,
      dite_eq_left (by omega), Option.getD_some, hout, HalfGates.colourWord_labelBits]

/-! ### Evaluation -/

/-- `evalStep` on a non-free gate uses `garbledRowOf` at its binary colour index. -/
private theorem rowIndex_colours_lt {k : ℕ} (f : ValidCircuit) (g : Fin (toCircuit f).size)
    (A : Wire f.1.n (toCircuit f).size → BitString (k + 1) × Bool) :
    PointPermute.rowIndex (fun a => (A ((toCircuit f).topology.wires g a)).2) < 4 :=
  PointPermute.rowIndex_lt_four (arity_topology_toCircuit f g) _

/-- One gate of `Ev` on the labels of the earlier wires of a fixed point of an evaluation round, at
the position of the gate's block, appends the label of the gate and moves past the block. -/
private theorem evalGate_take (k : ℕ) (f : ValidCircuit)
    (table : GarbledRow (toCircuit f).topology (freeCircuit f) → BitString (k + 1) × Bool)
    (X : Fin f.1.n → BitString (k + 1) × Bool)
    (A : Wire f.1.n (toCircuit f).size → BitString (k + 1) × Bool)
    (hA : ∀ w, evalStep (toCircuit f).topology (freeCircuit f)
      (fun key t => CCR.atLevel hash k (key, false) t)
      (slotTweak (toCircuit f).topology (freeCircuit f) k) table X A w = A w)
    (g : Fin (toCircuit f).size) :
    evalGate hash k (PointPermute.wireWidth f.1.n (toCircuit f).size)
        (List.ofFn fun g => encodeGate k (PointPermute.wireWidth f.1.n (toCircuit f).size)
          (toCircuit f).topology (freeCircuit f) table g).flatten
        ((List.ofFn fun v : Fin (f.1.n + (toCircuit f).size) =>
            labelBits (A (Wire.ofNat v v.isLt))).take (f.1.n + g),
          ((List.ofFn fun g => encodeGate k (PointPermute.wireWidth f.1.n (toCircuit f).size)
            (toCircuit f).topology (freeCircuit f) table g).take g).flatten.length) g =
      ((List.ofFn fun v : Fin (f.1.n + (toCircuit f).size) =>
          labelBits (A (Wire.ofNat v v.isLt))).take (f.1.n + g + 1),
        ((List.ofFn fun g => encodeGate k (PointPermute.wireWidth f.1.n (toCircuit f).size)
          (toCircuit f).topology (freeCircuit f) table g).take (g + 1)).flatten.length) := by
  set w := PointPermute.wireWidth f.1.n (toCircuit f).size
  set blocks := fun g => encodeGate k w (toCircuit f).topology (freeCircuit f) table g with hblocks
  have harity := arity_topology_toCircuit f g
  have hA₁ := f.2.one_le_A (g.cast (size_toCircuit f))
  have hAB := f.2.A_lt_B (g.cast (size_toCircuit f))
  have hBg := f.2.B_lt_gate (g.cast (size_toCircuit f))
  simp only [ConventionalCircuit.topo, Fin.val_cast] at hA₁ hAB hBg
  have hgs := g.isLt
  have hw : PointPermute.wireWidth f.1.n f.1.q = w := by simp [w, size_toCircuit]
  have hl := wires_toCircuit_zero f g (by omega)
  have hr := wires_toCircuit_one f g (by omega)
  have hsize : f.1.n + (toCircuit f).size < 2 ^ w := Nat.lt_size_self _
  have hval (a : ℕ) (ha : a ≤ f.1.n + g) :
      BitString.boundedBinaryValue
        ((List.ofFn fun v : Fin (f.1.n + (toCircuit f).size) =>
          labelBits (A (Wire.ofNat v v.isLt))).take (f.1.n + g)).length
        (BitString.lowBits w a).reverse = a := by
    rw [BitString.boundedBinaryValue_eq, ← ofBits_reverse, List.reverse_reverse,
      ofBits_lowBits (by omega), List.length_take, List.length_ofFn]
    omega
  have hg : (g : ℕ) < (List.ofFn blocks).length := by simp
  rw [evalGate, List.drop_flatten_take _ hg, List.length_flatten_take_succ _ hg,
    List.getElem_ofFn]
  have hb_eq : blocks g = BitString.lowBits w (f.1.A (g.cast (size_toCircuit f))) ++
      BitString.lowBits w (f.1.B (g.cast (size_toCircuit f))) ++
      [freeCircuit f g] ++
      if h : freeCircuit f g = false then
        (List.ofFn fun i : Fin 4 => labelBits (table (garbledRowOf _ g h i))).flatten
      else [] := by
    change encodeGate k w (toCircuit f).topology (freeCircuit f) table g = _
    rw [encodeGate_toCircuit, hw]
    rfl
  obtain ⟨hp₁, hp₂, hp₃, hp₄⟩ := HalfGates.block_parts (freeCircuit f g)
    (cts := if h : freeCircuit f g = false then
      (List.ofFn fun i : Fin 4 => labelBits (table (garbledRowOf _ g h i))).flatten
      else [])
    (more := ((List.ofFn blocks).drop (g + 1)).flatten)
    (BitString.length_lowBits w (f.1.A (g.cast (size_toCircuit f))))
    (BitString.length_lowBits w (f.1.B (g.cast (size_toCircuit f))))
  rw [← hb_eq] at hp₁ hp₂ hp₃ hp₄
  rw [hp₁, hp₂, hp₃, hval _ (by omega), hval _ (by omega),
    HalfGates.getD_take_labels A (by omega) (by omega),
    HalfGates.getD_take_labels A (by omega) (by omega), ← hl, ← hr,
    List.take_add_one (i := f.1.n + g), List.getElem?_ofFn]
  have hgate : (Wire.ofNat (f.1.n + g) (by omega) : Wire f.1.n (toCircuit f).size) =
      .gate g := Wire.toNat_injective (by simp)
  simp only [show f.1.n + g < f.1.n + (toCircuit f).size by omega, dite_true,
    Option.toList_some, hgate, ← hA (.gate g), evalStep]
  have hc₀ : (Fin.cast harity.symm 0 : Fin ((toCircuit f).topology.arity g)) = ⟨0, by omega⟩ :=
    Fin.ext rfl
  have hc₁ : (Fin.cast harity.symm 1 : Fin ((toCircuit f).topology.arity g)) = ⟨1, by omega⟩ :=
    Fin.ext rfl
  by_cases hfr : freeCircuit f g = true
  · have hfr' : ¬ freeCircuit f g = false := by simp [hfr]
    rw [ite_eq_left hfr, dite_eq_right hfr']
    simp only [hb_eq, dite_eq_right hfr', List.length_append, BitString.length_lowBits,
      List.length_singleton, List.length_nil]
    rw [← Fin.sum_congr' _ harity.symm, Fin.sum_univ_two, labelBits_add]
    exact Prod.ext rfl (by omega)
  · have hfr' : freeCircuit f g = false := Bool.eq_false_iff.mpr hfr
    rw [ite_eq_right hfr, dite_eq_left hfr']
    set idx := (if HalfGates.colourWord k (labelBits (A ((toCircuit f).topology.wires g
        (Fin.cast harity.symm 0)))) then 2 else 0) +
      (if HalfGates.colourWord k (labelBits (A ((toCircuit f).topology.wires g
        (Fin.cast harity.symm 1)))) then 1 else 0) with hidx
    have hidx_eq : idx = PointPermute.rowIndex fun a =>
        (A ((toCircuit f).topology.wires g a)).2 := by
      rw [hidx, PointPermute.rowIndex_of_eq_two harity, hc₀, hc₁,
        HalfGates.colourWord_labelBits, HalfGates.colourWord_labelBits]
    have hidx_lt : idx < 4 := by
      rw [hidx_eq]
      exact rowIndex_colours_lt f g A
    have hrow_eq : garbledRowOf (toCircuit f).topology g hfr' idx =
        ⟨⟨g, hfr'⟩, fun a => (A ((toCircuit f).topology.wires g a)).2⟩ := by
      simp only [garbledRowOf, hidx_eq, PointPermute.testBit_rowIndex_of_eq_two harity]
    have htake_row : (((blocks g ++ ((List.ofFn blocks).drop (g + 1)).flatten).drop
        (2 * w + 1 + idx * (k + 2))).take (k + 2)) =
        labelBits (table ⟨⟨g, hfr'⟩, fun a => (A ((toCircuit f).topology.wires g a)).2⟩) := by
      rw [← List.drop_drop (i := idx * (k + 2)) (j := 2 * w + 1), hp₄, dite_eq_left hfr']
      have hlen_rows : (List.ofFn fun i : Fin 4 =>
          labelBits (table (garbledRowOf (toCircuit f).topology g hfr' i))).flatten.length =
          4 * (k + 2) := by
        simp only [List.length_flatten, List.map_ofFn, Function.comp_def, length_labelBits,
          List.sum_ofFn, Finset.sum_const, Finset.card_fin, smul_eq_mul]
      have hdrop_take_append : ∀ (A B : List Bool) (a b : ℕ), a + b ≤ A.length →
          ((A ++ B).drop a).take b = (A.drop a).take b := by
        intro A B a b hab
        apply List.ext_getElem
        · simp only [List.length_take, List.length_drop, List.length_append]
          omega
        · intro j hj₁ hj₂
          simp only [List.length_take, List.length_drop] at hj₂
          simp only [List.getElem_take, List.getElem_drop]
          rw [List.getElem_append_left (by omega)]
      have hlen_le : idx * (k + 2) + (k + 2) ≤
          (List.ofFn fun i : Fin 4 =>
            labelBits (table (garbledRowOf (toCircuit f).topology g hfr' i))).flatten.length := by
        rw [hlen_rows]
        calc idx * (k + 2) + (k + 2) = (idx + 1) * (k + 2) := by ring
          _ ≤ 4 * (k + 2) := Nat.mul_le_mul_right _ hidx_lt
      rw [hdrop_take_append _ _ _ _ hlen_le,
        ← List.take_append_of_le_length (l₂ := List.replicate (k + 2) false)
          (by simp only [List.length_drop]; omega),
        show List.take (k + 2) (List.drop (idx * (k + 2))
            (List.ofFn fun i : Fin 4 =>
              labelBits (table (garbledRowOf (toCircuit f).topology g hfr' i))).flatten ++
            List.replicate (k + 2) false) =
          BitString.listRow (k + 2) idx (List.ofFn fun i : Fin 4 =>
            labelBits (table (garbledRowOf (toCircuit f).topology g hfr' i))).flatten from rfl,
        show idx = (⟨idx, hidx_lt⟩ : Fin 4).val from rfl,
        BitString.listRow_flatten_ofFn _ (fun _ => length_labelBits _), hrow_eq]
    have hlen_block : (blocks g).length = 2 * w + 1 + 4 * (k + 2) := by
      simp only [hb_eq, dite_eq_left hfr', List.length_append, BitString.length_lowBits,
        List.length_singleton, List.length_flatten, List.map_ofFn, Function.comp_def,
        length_labelBits, List.sum_ofFn, Finset.sum_const, Finset.card_fin, smul_eq_mul]
      omega
    rw [htake_row, hlen_block]
    refine Prod.ext ?_ (by omega)
    have hneg : ∀ z : BitString (k + 1) × Bool, -z = z := fun z =>
      neg_eq_iff_add_eq_zero.mpr (Prod.ext (BitString.add_self z.1) (by
        cases h : z.2 <;> simp [h, Bool.add_eq_xor] <;> rfl))
    rw [sub_eq_add_neg, hneg, labelBits_add,
      ← Fin.sum_congr' _ harity.symm, Fin.sum_univ_two, labelBits_add, hc₀, hc₁,
      labelBits_atLevel_key, labelBits_atLevel_key,
      ofFn_slotTweak_mk, ofFn_slotTweak_mk, ← hidx_eq]

/-- **`Ev` follows a fixed point of an evaluation round.** If the labelling `A` of the wires of
`toCircuit f` is left unchanged by one round of the typed evaluation of `table` on the input labels
`X`, then `Ev` on the garbled function of `table` and the words of `X` returns the labels `A` of the
output wires. -/
theorem evalWord_encodeFn (k : ℕ) (f : ValidCircuit)
    (table : GarbledRow (toCircuit f).topology (freeCircuit f) → BitString (k + 1) × Bool)
    (X : Fin f.1.n → BitString (k + 1) × Bool)
    (A : Wire f.1.n (toCircuit f).size → BitString (k + 1) × Bool)
    (hA : ∀ w, evalStep (toCircuit f).topology (freeCircuit f)
      (fun key t => CCR.atLevel hash k (key, false) t)
      (slotTweak (toCircuit f).topology (freeCircuit f) k) table X A w = A w) :
    evalWord hash (encodeFn k (toCircuit f).topology (freeCircuit f) table)
        (List.ofFn fun i => labelBits (X i)).flatten =
      (List.ofFn fun o => labelBits (A ((toCircuit f).outputs o))).flatten := by
  have hinit : BitString.listRows f.1.n (k + 2)
      (List.ofFn fun i => labelBits (X i)).flatten =
      (List.ofFn fun v : Fin (f.1.n + (toCircuit f).size) =>
        labelBits (A (Wire.ofNat v v.isLt))).take f.1.n := by
    apply List.ext_getElem (by simp)
    intro i h₁ h₂
    simp only [BitString.length_listRows] at h₁
    have hin : (Wire.ofNat i (by omega) : Wire f.1.n (toCircuit f).size) = .input ⟨i, h₁⟩ :=
      Wire.toNat_injective (by simp)
    simp only [BitString.listRows, List.getElem_map, List.getElem_range, List.getElem_take,
      List.getElem_ofFn, hin, ← hA (.input ⟨i, h₁⟩), evalStep]
    exact BitString.listRow_flatten_ofFn (fun i => labelBits (X i))
      (fun _ => length_labelBits _) ⟨i, h₁⟩
  have hfold : ∀ g ≤ (toCircuit f).size,
      (List.range g).foldl (evalGate hash k (PointPermute.wireWidth f.1.n (toCircuit f).size)
          (List.ofFn fun g => encodeGate k (PointPermute.wireWidth f.1.n (toCircuit f).size)
            (toCircuit f).topology (freeCircuit f) table g).flatten)
        (BitString.listRows f.1.n (k + 2)
          (List.ofFn fun i => labelBits (X i)).flatten, 0) =
      ((List.ofFn fun v : Fin (f.1.n + (toCircuit f).size) =>
          labelBits (A (Wire.ofNat v v.isLt))).take (f.1.n + g),
        ((List.ofFn fun g => encodeGate k (PointPermute.wireWidth f.1.n (toCircuit f).size)
          (toCircuit f).topology (freeCircuit f) table g).take g).flatten.length) := by
    intro g hg
    induction g with
    | zero => simp [hinit]
    | succ g ih =>
      rw [List.range_succ, List.foldl_append, ih (by omega), List.foldl_cons, List.foldl_nil]
      exact evalGate_take hash k f table X A hA ⟨g, by omega⟩
  simp only [evalWord, encodeFn, PointPermute.fnDecoder.decode_enc]
  rw [hfold _ le_rfl, List.take_of_length_le (by simp)]
  have hm := f.2.m_le_q
  have hq := size_toCircuit f
  simp only [ConventionalCircuit.topo] at hm
  congr 1
  apply List.ext_getElem (by simp; omega)
  intro o h₁ h₂
  simp only [List.length_ofFn] at h₂
  have hout : (Wire.ofNat (f.1.n + (toCircuit f).size - f.1.m + o) (by omega) :
      Wire f.1.n (toCircuit f).size) = (toCircuit f).outputs ⟨o, h₂⟩ :=
    Wire.toNat_injective (by rw [Wire.toNat_ofNat, toNat_outputs_toCircuit, hq])
  simp only [List.getElem_drop, List.getElem_ofFn, hout]

/-! ### Correctness -/

/-- **Correctness**: decoding the evaluation of an encoded input gives the circuit's output, for
every hash family. -/
theorem scheme_correct : (scheme hash).Correct := by
  intro k _ f x hx g hg
  obtain ⟨coins, -, rfl⟩ := (scheme hash).mem_support_eval_garble_iff.mp hg
  replace hx : x.length = f.1.n := hx
  have hK : ∀ y : BitString (k + 1), y + y = 0 := BitString.add_self
  have hτ := (toCircuit f).isOrdered_topology
  have hfix := evalStep_activeLabel (toCircuit f) fullInterpretation
    (fun key t => CCR.atLevel hash k (key, false) t)
    (slotTweak (toCircuit f).topology (freeCircuit f) k) (BitString.ofList f.1.n x)
    (hfree_toCircuit f) hK (HalfGates.offsetKey k coins) (baseLabels k coins)
  have hev := (isLocal_evalStep hτ (freeCircuit f)
    (fun key t => CCR.atLevel hash k (key, false) t)
    (slotTweak (toCircuit f).topology (freeCircuit f) k)
    (garbleWith (toCircuit f) fullInterpretation
      (fun key t => CCR.atLevel hash k (key, false) t)
      (slotTweak (toCircuit f).topology (freeCircuit f) k)
      (HalfGates.offsetKey k coins) (baseLabels k coins)).table
    (encode (garbleWith (toCircuit f) fullInterpretation
      (fun key t => CCR.atLevel hash k (key, false) t)
      (slotTweak (toCircuit f).topology (freeCircuit f) k)
      (HalfGates.offsetKey k coins) (baseLabels k coins)).encoding
      (BitString.ofList f.1.n x))).iterate_eq_of_isFixed 0 (funext hfix)
  have hrun := Garbled.run_garbleWith (toCircuit f) fullInterpretation
    (fun key t => CCR.atLevel hash k (key, false) t)
    (slotTweak (toCircuit f).topology (freeCircuit f) k) (BitString.ofList f.1.n x)
    (hfree_toCircuit f) hK (HalfGates.offsetKey k coins) (baseLabels k coins)
  rw [gb_eq_encodeGarbled]
  simp only [scheme, encodeGarbled, garbleWith]
  rw [PointPermute.projectiveEncode_labelBits (n := f.1.n)
      (fun i b => label (HalfGates.offsetKey k coins)
        (propagate (toCircuit f).topology (freeCircuit f) (baseLabels k coins) (.input i)) b) hx]
  have heval := evalWord_encodeFn hash k f
    (garbleWith (toCircuit f) fullInterpretation
      (fun key t => CCR.atLevel hash k (key, false) t)
      (slotTweak (toCircuit f).topology (freeCircuit f) k)
      (HalfGates.offsetKey k coins) (baseLabels k coins)).table
    (encode (garbleWith (toCircuit f) fullInterpretation
      (fun key t => CCR.atLevel hash k (key, false) t)
      (slotTweak (toCircuit f).topology (freeCircuit f) k)
      (HalfGates.offsetKey k coins) (baseLabels k coins)).encoding
      (BitString.ofList f.1.n x))
    (activeLabel (toCircuit f) fullInterpretation (BitString.ofList f.1.n x) (freeCircuit f)
      (HalfGates.offsetKey k coins) (baseLabels k coins))
    hfix
  erw [heval]
  rw [PointPermute.decodeWord_ofFn]
  have h := congrArg List.ofFn hrun
  rw [eval_toCircuit, BitString.ofFn_ofList hx] at h
  rw [← h]
  congr 2
  funext o
  have hev' := congrFun hev ((toCircuit f).outputs o)
  unfold Garbled.run evaluate
  simp only [garbleWith, Garbling.decode]
  exact congrArg (fun y : BitString (k + 1) × Bool => y.2 + _) hev'.symm

end Cslib.Crypto.Garbling.FreeXOR
