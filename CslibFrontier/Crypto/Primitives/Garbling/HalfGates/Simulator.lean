/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.Garbling.HalfGates.Efficient
public import CslibFrontier.Crypto.Primitives.Garbling.HalfGates.Privacy
public import CslibFrontier.Crypto.Primitives.Garbling.Games
public import CslibFrontier.Computability.Probabilistic.PPT
import CslibFrontier.Probability.BitString.List
import CslibFrontier.Probability.Uniform
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Captured
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import CslibFrontier.Foundations.Data.BitString.Weight
import CslibFrontier.Foundations.Data.List.Lookup
import CslibFrontier.Tactic.PolyTime

/-!
# The simulator of half-gates garbling

The privacy simulator `HalfGates.simulate` of
`CslibFrontier.Crypto.Primitives.Garbling.HalfGates.Privacy`, written on words, for the scheme
`HalfGates.scheme hash` with the side information `Φ_circ`, which reveals the circuit itself
(`SideInfo.circ`). The simulator `simWord hash k y f` sees the parameter `k`, the output `y` and
the XOR–AND circuit `f`. It samples a uniform `(k + 2)`-bit label for each of the `n` input wires
and two for each AND gate, and writes the view `(F, X, d)` (`simViewWord`): `F` has the layout of
the real garbled function, with the two labels of each AND gate as its ciphertexts; `X` lists the
input labels; and `d` makes the evaluated output labels decode to `y`, by running `Ev` on `(F, X)`.
The labels of AND gate `g` are those numbered `n + 2 a` and `n + 2 a + 1`, where `a` is the number
of AND gates before `g` (`andRank`), so the coins are used without gaps.

The words written are those of the typed simulated view `simulateWith` of `toCircuit f`, with the
input labels and the table read from the coins, and the coins give uniform input labels and a
uniform table. So the simulator's output law is the typed simulator's (`eval_simWord`). Every view
it writes for an output of `m` bits decodes to that output
(`decodeWord_evalWord_simViewWord`), and the simulator is PPT whenever the hash is computed in
polynomial time (`isPPTOn_simWord`).

## Main definitions

* `Cslib.Crypto.Garbling.HalfGates.viewWord`: the words `(F, X, d)` of a typed view.
* `Cslib.Crypto.Garbling.HalfGates.simViewWord`, `Cslib.Crypto.Garbling.HalfGates.simWord`: the
  simulated view on given coins, and the simulator.

## Main results

* `Cslib.Crypto.Garbling.HalfGates.eval_simWord`: the simulator samples the words of the typed
  simulator's view.
* `Cslib.Crypto.Garbling.HalfGates.decodeWord_evalWord_simViewWord`: simulated views decode to the
  output.
* `Cslib.Crypto.Garbling.HalfGates.isPPTOn_simWord`: the simulator is PPT.

## References

* [S. Zahur, M. Rosulek, D. Evans, *Two Halves Make a Whole: Reducing Data Transfer in Garbled
  Circuits using Half Gates*][ZahurRosulekEvans2015]
* [M. Bellare, V. T. Hoang, P. Rogaway, *Foundations of Garbled Circuits*][BellareHoangRogaway2012]
-/

public section

namespace Cslib.Crypto.Garbling.HalfGates

open Cslib.Circuits Probability

/-! ### The simulated view -/

/-- The number of AND gates among the first `g` gates of `f`. -/
@[expose] def andRank (f : ConventionalCircuit) (g : ℕ) : ℕ :=
  ((List.ofFn fun g' : Fin f.q => f.G g' true true).take g).count true

/-- The number of coins of the simulator at parameter `k` for `f`: one label for each input, then
two for each AND gate. -/
@[expose] def simCoinLen (k : ℕ) (f : ConventionalCircuit) : ℕ :=
  (f.n + 2 * andRank f f.q) * (k + 2)

/-- The block of gate `g` of the simulated garbled function: the numbers of its argument wires as
`w`-bit numbers, its AND bit, and for an AND gate the labels `n + 2 a` and `n + 2 a + 1` of the
coins, `a` the number of AND gates before it. -/
@[expose] def simGateWord (k w : ℕ) (f : ConventionalCircuit) (coins : List Bool) (g : Fin f.q) :
    List Bool :=
  BitString.lowBits w (f.A g) ++ BitString.lowBits w (f.B g) ++ [f.G g true true] ++
    if f.G g true true then
      BitString.listRow (k + 2) (f.n + 2 * andRank f g) coins ++
        BitString.listRow (k + 2) (f.n + 2 * andRank f g + 1) coins
    else []

variable (hash : List Bool → List Bool → List Bool)

/-- The simulated view `(F, X, d)` at parameter `k` for the output `y` and the circuit `f`, on the
simulator's coins: the garbled function with the header and gates of `f` and the ciphertexts read
from the coins, the input labels read from the coins, and the decoding bits that make the colours
of the output labels that `Ev` computes from `F` and `X` decode to `y` when `y` has `m` bits. -/
@[expose] def simViewWord (k : ℕ) (y : List Bool) (f : ConventionalCircuit) (coins : List Bool) :
    PrvView :=
  let F := PointPermute.encFn ((k, f.n, f.m, f.q), (List.ofFn fun g =>
    simGateWord k (PointPermute.wireWidth f.n f.q) f coins g).flatten)
  let X := (List.ofFn fun i : Fin f.n => BitString.listRow (k + 2) i coins).flatten
  ⟨F, X, List.ofFn fun o : Fin f.m =>
    colourWord k (BitString.listRow (k + 2) o (evalWord hash F X)) ^^ y.getD o false⟩

/-- **The simulator** `S(1^k, y, f)` of half-gates garbling with the side information `Φ_circ`:
sample the coins and write the simulated view. -/
noncomputable def simWord (k : ℕ) (y : List Bool) (f : XorAndCircuit) : ProbComp PrvView := do
  let coins ← BitString.sampleList (simCoinLen k f.circuit)
  return simViewWord hash k y f.circuit coins

/-- The words `(F, X, d)` of a typed view at parameter `k`: the garbled function of its table, the
words of its input labels in order, and its decoding bits. -/
@[expose] def viewWord {n m : ℕ} (k : ℕ) (C : Circuit signature n m)
    (V : View C (BitString (k + 1))) : PrvView where
  fn := encodeFn k C V.table
  input := (List.ofFn fun i => labelBits (V.input i)).flatten
  decInfo := List.ofFn V.decoding

/-! ### The simulator's coins -/

/-- One more gate adds its AND bit to `andRank`. -/
private theorem andRank_succ (f : ConventionalCircuit) (g : Fin f.q) :
    andRank f (g + 1) = andRank f g + (f.G g true true).toNat := by
  simp only [andRank]
  rw [List.take_add_one, List.count_append, List.getElem?_ofFn]
  simp only [g.isLt, dite_true, Option.toList_some]
  cases f.G g true true <;> simp

private theorem andRank_mono (f : ConventionalCircuit) {g g' : ℕ} (h : g ≤ g') :
    andRank f g ≤ andRank f g' :=
  (List.take_sublist_take_left h).count_le _

/-- An AND gate comes before every later gate in `andRank`. -/
private theorem andRank_lt (f : ConventionalCircuit) (g : Fin f.q) {g' : ℕ}
    (hg : f.G g true true = true) (h : (g : ℕ) < g') : andRank f g < andRank f g' := by
  have := andRank_mono f (show (g : ℕ) + 1 ≤ g' from h)
  rw [andRank_succ, hg, Bool.toNat_true] at this
  omega

/-- `andRank` of all gates counts the AND gates. -/
private theorem andRank_q (f : ConventionalCircuit) :
    andRank f f.q = Fintype.card {g : Fin f.q // f.G g true true = true} := by
  rw [andRank, List.take_of_length_le (by simp), BitString.count_true_ofFn,
    BitString.weight_eq_card_subtype]

/-- A slot of `toCircuit f` is an AND gate of `f`. -/
private theorem op_toCircuit_eq_and_iff (f : XorAndCircuit) (g : Fin (toCircuit f).size) :
    op (toCircuit f) g = .and ↔ f.circuit.G (g.cast (size_toCircuit f)) true true = true := by
  rw [op_toCircuit, opOf]
  cases f.circuit.G (g.cast (size_toCircuit f)) true true <;> simp

/-- The ciphertext slots of `toCircuit f` are two per AND gate of `f`. -/
private theorem card_slot_toCircuit (f : XorAndCircuit) :
    Fintype.card (Slot (toCircuit f)) = 2 * andRank f.circuit f.circuit.q := by
  rw [Fintype.card_prod, Fintype.card_bool, andRank_q, mul_comm,
    Fintype.card_congr (Equiv.subtypeEquiv (p := fun g => op (toCircuit f) g = .and)
      (q := fun g : Fin f.circuit.q => f.circuit.G g true true = true)
      (finCongr (size_toCircuit f)) (op_toCircuit_eq_and_iff f))]

/-- The position of the label of a slot among the simulator's coins. -/
private noncomputable def slotIndex (f : XorAndCircuit) (p : Slot (toCircuit f)) : ℕ :=
  f.circuit.n + 2 * andRank f.circuit p.gate + p.2.toNat

/-- The input labels read from the simulator's coins. -/
private def simInputLabels {n : ℕ} (k : ℕ) (coins : List Bool) (i : Fin n) :
    BitString (k + 1) × Bool :=
  labelOfWord k (BitString.listRow (k + 2) i coins)

/-- The table read from the simulator's coins. -/
private noncomputable def simTable (k : ℕ) (f : XorAndCircuit) (coins : List Bool)
    (p : Slot (toCircuit f)) :
    BitString (k + 1) × Bool :=
  labelOfWord k (BitString.listRow (k + 2) (slotIndex f p) coins)

private theorem slotIndex_lt (f : XorAndCircuit) (p : Slot (toCircuit f)) :
    slotIndex f p < f.circuit.n + 2 * andRank f.circuit f.circuit.q := by
  have hg := (op_toCircuit_eq_and_iff f p.gate).mp p.1.property
  have hlt := andRank_lt f.circuit (p.gate.cast (size_toCircuit f)) hg
    (show (p.gate.cast (size_toCircuit f) : ℕ) < f.circuit.q from Fin.isLt _)
  have hs := Bool.toNat_le p.2
  simp only [Fin.val_cast] at hlt
  simp only [slotIndex]
  omega

/-- The position of each input label and each slot's label among the simulator's coins. -/
private noncomputable def simIndex (f : XorAndCircuit) :
    Fin f.circuit.n ⊕ Slot (toCircuit f) → Fin (f.circuit.n + 2 * andRank f.circuit f.circuit.q)
  | .inl i => ⟨i, by omega⟩
  | .inr p => ⟨slotIndex f p, slotIndex_lt f p⟩

private theorem simIndex_bijective (f : XorAndCircuit) : Function.Bijective (simIndex f) := by
  refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨?_, ?_⟩
  · rintro (i | ⟨⟨g, hg⟩, s⟩) (i' | ⟨⟨g', hg'⟩, s'⟩) h <;>
      simp only [simIndex, Fin.mk.injEq, slotIndex, Slot.gate] at h
    · exact congrArg Sum.inl (Fin.ext h)
    · omega
    · omega
    · have hs := Bool.toNat_le s
      have hs' := Bool.toNat_le s'
      have hrank : andRank f.circuit g = andRank f.circuit g' := by omega
      have hss : s.toNat = s'.toNat := by omega
      have hgg : g = g' := by
        have key {a b : Fin (toCircuit f).size} (ha : op (toCircuit f) a = .and)
            (hab : (a : ℕ) < b) : andRank f.circuit a < andRank f.circuit b := by
          simpa only [Fin.val_cast] using andRank_lt f.circuit (a.cast (size_toCircuit f))
            ((op_toCircuit_eq_and_iff f a).mp ha) hab
        rcases lt_trichotomy (g : ℕ) g' with hlt | heq | hgt
        · exact absurd hrank (key hg hlt).ne
        · exact Fin.ext heq
        · exact absurd hrank (key hg' hgt).ne'
      subst hgg
      have : s = s' := by cases s <;> cases s' <;> simp_all
      subst this
      rfl
  · rw [Fintype.card_sum, Fintype.card_fin, card_slot_toCircuit, Fintype.card_fin]

/-- **The simulator's coins are uniform labels.** The input labels and the table read from
uniform coins are uniform and independent. -/
private theorem uniformList_map_simCoins (k : ℕ) (f : XorAndCircuit) :
    (BitString.uniformList (simCoinLen k f.circuit)).map
        (fun coins => ((simInputLabels k coins : Fin f.circuit.n → _), simTable k f coins)) =
      PMF.uniformOfFintype ((Fin f.circuit.n → BitString (k + 1) × Bool) ×
        (Slot (toCircuit f) → BitString (k + 1) × Bool)) := by
  let e := Equiv.ofBijective _ (simIndex_bijective f)
  let E : (Fin f.circuit.n ⊕ Slot (toCircuit f) → BitString (k + 2)) ≃
      (Fin f.circuit.n → BitString (k + 1) × Bool) ×
        (Slot (toCircuit f) → BitString (k + 1) × Bool) :=
    (Equiv.sumArrowEquivProdArrow _ _ _).trans (Equiv.prodCongr
      (Equiv.arrowCongr (Equiv.refl _) (labelEquiv k))
      (Equiv.arrowCongr (Equiv.refl _) (labelEquiv k)))
  have h : (fun coins => ((simInputLabels k coins : Fin f.circuit.n → _), simTable k f coins)) =
      (E : _ → _) ∘
        fun coins i => BitString.ofList (k + 2) (BitString.listRow (k + 2) (e i) coins) := by
    funext coins
    rfl
  rw [h, ← PMF.map_comp, simCoinLen, BitString.uniformList_map_listRow_equiv e (k + 2)]
  exact PMF.uniformOfFintype_map_equiv E

/-! ### The simulated view is the typed simulator's -/

/-- Gate `g` of the typed simulated table, as a word, is `simGateWord`. -/
private theorem encodeGate_simTable (k : ℕ) (f : XorAndCircuit) (coins : List Bool)
    (g : Fin (toCircuit f).size) :
    encodeGate k (PointPermute.wireWidth f.circuit.n (toCircuit f).size) (toCircuit f)
        (simTable k f coins) g =
      simGateWord k (PointPermute.wireWidth f.circuit.n f.circuit.q) f.circuit coins
        (g.cast (size_toCircuit f)) := by
  rw [encodeGate_toCircuit]
  simp only [simGateWord]
  cases hG : f.circuit.G (g.cast (size_toCircuit f)) true true
  · have hop : ¬ op (toCircuit f) g = .and := by
      rw [op_toCircuit_eq_and_iff, hG]
      simp
    rw [dite_eq_right hop]
    rfl
  · have hop : op (toCircuit f) g = .and := (op_toCircuit_eq_and_iff f g).mpr hG
    rw [dite_eq_left hop]
    simp only [simTable, slotIndex, Slot.gate, Bool.toNat_false, Bool.toNat_true, Nat.add_zero,
      labelBits_labelOfWord (BitString.length_listRow _ _ _), Fin.val_cast,
      ↓reduceIte]

/-- On the simulator's coins, the evaluated labels are a fixed point of an evaluation round. -/
private theorem evalStep_evalLabels {n m : ℕ} {K T : Type} [AddCommGroup K]
    (C : Circuit signature n m) (H : K × Bool → T → K × Bool) (tw : Slot C → T)
    (ct : Slot C → K × Bool) (X : Fin n → K × Bool) (w : Wire n C.size) :
    evalStep C H tw ct X (evalLabels C H tw ct X) w = evalLabels C H tw ct X w :=
  congrFun ((isLocal_evalStep_const C H tw ct X).isFixed_iterate 0) w

/-- **The simulated view is the typed simulator's.** For every XOR–AND circuit `f`, the simulated
view for `f` and the output `y` is the words of the typed simulated view of `toCircuit f`, with the
input labels and the table read from the coins. -/
private theorem simViewWord_eq (k : ℕ) (f : XorAndCircuit) (y coins : List Bool) :
    simViewWord hash k y f.circuit coins = viewWord k (toCircuit f)
      (simulateWith (toCircuit f) (CCR.atLevel hash k) (slotTweak _ k)
        (BitString.ofList f.circuit.m y) (simInputLabels k coins) (simTable k f coins)) := by
  have hF : PointPermute.encFn ((k, f.circuit.n, f.circuit.m, f.circuit.q), (List.ofFn fun g =>
      simGateWord k (PointPermute.wireWidth f.circuit.n f.circuit.q) f.circuit coins g).flatten) =
      encodeFn k (toCircuit f) (simTable k f coins) := by
    simp only [encodeFn, encodeGate_simTable]
    congr 2
    · rw [size_toCircuit]
    · rw [List.ofFn_congr (size_toCircuit f)]
      rfl
  have hX : (List.ofFn fun i : Fin f.circuit.n => BitString.listRow (k + 2) i coins).flatten =
      (List.ofFn fun i : Fin f.circuit.n =>
        labelBits (simInputLabels k coins i)).flatten := by
    simp only [simInputLabels, labelBits_labelOfWord (BitString.length_listRow _ _ _)]
  simp only [simViewWord, viewWord, simulateWith, PrvView.mk.injEq]
  refine ⟨hF, hX, ?_⟩
  rw [hF, hX, evalWord_encodeFn hash k f _ _ _
    (evalStep_evalLabels _ (CCR.atLevel hash k) (slotTweak _ k) _ _)]
  congr 1
  funext o
  rw [BitString.listRow_flatten_ofFn _ (fun _ => length_labelBits _),
    colourWord_labelBits]
  rfl

/-- **The simulator samples the typed simulator's view.** For every XOR–AND circuit `f` and output
`y`, the simulator on `f` samples the words of the typed simulator's view of `toCircuit f`. -/
theorem eval_simWord (k : ℕ) (f : XorAndCircuit) (y : List Bool) :
    ProbComp.eval (simWord hash k y f) =
      (ProbComp.eval (simulate (toCircuit f) (CCR.atLevel hash k) (slotTweak _ k)
        (BitString.ofList f.circuit.m y))).map (viewWord k _) := by
  have hsim := uniformList_map_simCoins k f
  have hview : simViewWord hash k y f.circuit =
      (fun p : (Fin f.circuit.n → BitString (k + 1) × Bool) ×
          (Slot (toCircuit f) → BitString (k + 1) × Bool) =>
        viewWord k _ (simulateWith (toCircuit f) (CCR.atLevel hash k) (slotTweak _ k)
          (BitString.ofList f.circuit.m y) p.1 p.2)) ∘
        (fun coins => (simInputLabels k coins, simTable k f coins)) :=
    funext fun coins => simViewWord_eq hash k f y coins
  change ProbComp.eval (do
      let coins ← BitString.sampleList (simCoinLen k f.circuit)
      return simViewWord hash k y f.circuit coins) = _
  simp only [simulate, bind_pure_comp, ProbComp.eval_map, ProbComp.eval_bind,
    ProbComp.eval_uniform, BitString.eval_sampleList]
  rw [hview, ← PMF.map_comp, hsim, ← Cslib.Probability.PMF.uniformOfFintype_prod]
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]

/-- **Simulated views decode to the output.** For every XOR–AND circuit `f`, every output `y` of
`m` bits and all coins, decoding the evaluation of the simulated garbled input gives `y`. -/
theorem decodeWord_evalWord_simViewWord (k : ℕ) (f : XorAndCircuit) {y : List Bool}
    (hy : y.length = f.circuit.m) (coins : List Bool) :
    PointPermute.decodeWord (simViewWord hash k y f.circuit coins).decInfo
      (evalWord hash (simViewWord hash k y f.circuit coins).fn
        (simViewWord hash k y f.circuit coins).input) = some y := by
  rw [simViewWord_eq]
  simp only [viewWord]
  rw [evalWord_encodeFn hash k f _ _ _
    (evalStep_evalLabels _ (CCR.atLevel hash k) (slotTweak _ k) _ _),
    PointPermute.decodeWord_ofFn]
  congr 1
  conv_rhs => rw [← BitString.ofFn_ofList hy]
  congr 1
  funext o
  simp only [decode, simulateWith, evaluate]
  rw [← add_assoc, BooleanRing.add_self, zero_add]

/-! ### Efficiency -/

section Efficiency

open Turing.MultiTapeTM

/-- `andRank` read from the gate data: the number of gates among the first `g` whose truth table
has `G 1 1` set. -/
private theorem andRank_eq_gateList (f : ConventionalCircuit) (g : ℕ) :
    andRank f g = (f.gateList.take g).countP fun gate => gate.2.2.getD 3 false := by
  have hmap : (List.ofFn fun g' : Fin f.q => f.G g' true true) =
      f.gateList.map fun gate => gate.2.2.getD 3 false := by
    simp [ConventionalCircuit.gateList, List.map_ofFn, Function.comp_def]
  rw [andRank, hmap, ← List.map_take, List.count_eq_countP, List.countP_map]
  rfl

/-- Row `i` of a gate of the simulated garbled function in the layout of `PointPermute.bodyWith`,
from its AND bit and the number `rank` of AND gates before it: row `0` is the AND bit, rows `1` and
`2` are the labels `n + 2 rank` and `n + 2 rank + 1` of the coins when it is an AND gate, and every
other row is empty. -/
private def simRow (k n : ℕ) (coins : List Bool) (isAnd : Bool) (rank i : ℕ) : List Bool :=
  if i = 0 then [isAnd]
  else if isAnd then
    if i = 1 then BitString.listRow (k + 2) (n + 2 * rank) coins
    else if i = 2 then BitString.listRow (k + 2) (n + 2 * rank + 1) coins
    else []
  else []

/-- The simulated garbled function from the gate data: its body is `bodyWith` of the gate list with
the rows `simRow`, which read no argument wires. -/
private theorem simFn_eq (k : ℕ) (f : ConventionalCircuit) (coins : List Bool) :
    PointPermute.encFn ((k, f.n, f.m, f.q), (List.ofFn fun g =>
      simGateWord k (PointPermute.wireWidth f.n f.q) f coins g).flatten) =
      PointPermute.encFn ((k, f.n, f.m, f.gateList.length),
        PointPermute.bodyWith f.n f.gateList.length 0 (fun g => (f.gateList.getD g (0, 0, [])).1)
          (fun g => (f.gateList.getD g (0, 0, [])).2.1)
          (fun g _ _ i => simRow k f.n coins ((f.gateList.getD g (0, 0, [])).2.2.getD 3 false)
            ((f.gateList.take g).countP fun gate => gate.2.2.getD 3 false) i)) := by
  have hgate (g : Fin f.q) : f.gateList.getD g (0, 0, []) = (f.A g, f.B g,
      [f.G g false false, f.G g false true, f.G g true false, f.G g true true]) := by
    simp [ConventionalCircuit.gateList, List.getD_eq_getElem?_getD]
  rw [ConventionalCircuit.length_gateList, PointPermute.bodyWith_eq_ofFn f.A f.B
    (fun g i => simRow k f.n coins (f.G g true true) (andRank f g) i) (fun g => by rw [hgate])
    (fun g => by rw [hgate]) (fun g i => by rw [hgate, ← andRank_eq_gateList]; rfl)]
  congr 2
  refine congrArg List.flatten (congrArg List.ofFn (funext fun g => ?_))
  simp only [simGateWord, simRow, List.ofFn_succ, List.ofFn_zero, List.flatten_cons,
    List.flatten_nil, List.append_assoc]
  cases f.G g true true <;> simp

/-- The simulated view from the gate data. -/
private theorem simViewWord_eq_data (hash : List Bool → List Bool → List Bool) (k : ℕ)
    (y : List Bool) (f : ConventionalCircuit) (coins : List Bool) :
    simViewWord hash k y f coins =
      ⟨PointPermute.encFn ((k, f.n, f.m, f.gateList.length),
          PointPermute.bodyWith f.n f.gateList.length 0
            (fun g => (f.gateList.getD g (0, 0, [])).1)
            (fun g => (f.gateList.getD g (0, 0, [])).2.1)
            (fun g _ _ i => simRow k f.n coins ((f.gateList.getD g (0, 0, [])).2.2.getD 3 false)
              ((f.gateList.take g).countP fun gate => gate.2.2.getD 3 false) i)),
        ((List.range f.n).map fun i => BitString.listRow (k + 2) i coins).flatten,
        (List.range f.m).map fun o =>
          (evalWord hash (PointPermute.encFn ((k, f.n, f.m, f.gateList.length),
            PointPermute.bodyWith f.n f.gateList.length 0
              (fun g => (f.gateList.getD g (0, 0, [])).1)
              (fun g => (f.gateList.getD g (0, 0, [])).2.1)
              (fun g _ _ i => simRow k f.n coins ((f.gateList.getD g (0, 0, [])).2.2.getD 3 false)
                ((f.gateList.take g).countP fun gate => gate.2.2.getD 3 false) i)))
            ((List.range f.n).map fun i => BitString.listRow (k + 2) i coins).flatten).getD
              (o * (k + 2) + (k + 1)) false ^^ y.getD o false⟩ := by
  simp only [simViewWord, simFn_eq, List.map_range_eq_ofFn, colourWord,
    BitString.getD_listRow (show k + 1 < k + 2 by omega)]

/-- The input `(1^k, y, f)` of the simulator. -/
private abbrev encSimInput : (ℕ × List Bool × XorAndCircuit) ↪ List Bool :=
  encPair encUnary (encPair encBits encXorAndCircuit)

private theorem simData_polyTime :
    ComputableInPolyTime (fun x : ℕ × List Bool × XorAndCircuit =>
      (x.2.2.circuit.n, x.2.2.circuit.m, x.2.2.circuit.gateList)) encSimInput encCircuitData :=
  (circuitData_polyTime.comp XorAndCircuit.val_polyTime).comp (ComputableInPolyTime.snd _ _).snd'

/-- The number of AND gates among the first `g` gates is read from the gate data in polynomial
time. -/
private theorem andCount_polyTime {γ : Type} {encIn : γ ↪ List Bool}
    {gates : γ → List (ℕ × ℕ × List Bool)} {g : γ → ℕ}
    (hgates : ComputableInPolyTime gates encIn (encList (encPair encNat (encPair encNat encBits))))
    (hg : ComputableInPolyTime g encIn encUnary) :
    ComputableInPolyTime (fun x => ((gates x).take (g x)).countP fun gate =>
      gate.2.2.getD 3 false) encIn encUnary :=
  ComputableInPolyTime.countPWithInput (ComputableInPolyTime.listTakeWithInput hgates hg)
    (ComputableInPolyTime.bitsGetDWithInput
      (ComputableInPolyTime.snd encIn (encPair encNat (encPair encNat encBits))).snd'.snd'
      (ComputableInPolyTime.const 3) false)

/-- A row of the simulated garbled function is computed in polynomial time. -/
private theorem simRow_polyTime {γ : Type} {encIn : γ ↪ List Bool} {k n rank i : γ → ℕ}
    {coins : γ → List Bool} {isAnd : γ → Bool} (hk : ComputableInPolyTime k encIn encUnary)
    (hn : ComputableInPolyTime n encIn encUnary) (hcoins : ComputableInPolyTime coins encIn encBits)
    (hisAnd : ComputableInPolyTime isAnd encIn encBool)
    (hrank : ComputableInPolyTime rank encIn encUnary)
    (hi : ComputableInPolyTime i encIn encUnary) :
    ComputableInPolyTime (fun x => simRow (k x) (n x) (coins x) (isAnd x) (rank x) (i x)) encIn
      encBits := by
  have hwidth := ComputableInPolyTime.unary_add' hk (ComputableInPolyTime.const 2)
  have hrow := ComputableInPolyTime.unary_add' hn
    (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const 2) hrank)
  have hfirst := ComputableInPolyTime.bitsRowWithInput hwidth hrow hcoins
  have hsecond := ComputableInPolyTime.bitsRowWithInput hwidth
    (ComputableInPolyTime.unary_add' hrow (ComputableInPolyTime.const 1)) hcoins
  have hbit := ComputableInPolyTime.bitsCons hisAnd (ComputableInPolyTime.const [])
  simpa only [simRow] using ComputableInPolyTime.ite_decide
    (hi.decide_eq' (ComputableInPolyTime.const 0)) hbit
    (hisAnd.ite
      (ComputableInPolyTime.ite_decide (hi.decide_eq' (ComputableInPolyTime.const 1)) hfirst
        (ComputableInPolyTime.ite_decide (hi.decide_eq' (ComputableInPolyTime.const 2)) hsecond
          (ComputableInPolyTime.const [])))
      (ComputableInPolyTime.const []))

private theorem simCoinLen_polyTime :
    ComputableInPolyTime (fun x : ℕ × List Bool × XorAndCircuit => simCoinLen x.1 x.2.2.circuit)
      encSimInput encUnary := by
  have hk := ComputableInPolyTime.fst encUnary (encPair encBits encXorAndCircuit)
  have hn := simData_polyTime.fst'
  have hgates := simData_polyTime.snd'.snd'
  have ha := andCount_polyTime hgates ((ComputableInPolyTime.length_list _).comp hgates)
  have heq : (fun x : ℕ × List Bool × XorAndCircuit => simCoinLen x.1 x.2.2.circuit) = fun x =>
      (x.2.2.circuit.n + 2 * (x.2.2.circuit.gateList.take x.2.2.circuit.gateList.length).countP
        fun gate => gate.2.2.getD 3 false) * (x.1 + 2) := by
    funext x
    rw [simCoinLen, andRank_eq_gateList, ConventionalCircuit.length_gateList]
  rw [heq]
  exact ComputableInPolyTime.unary_mul.comp ((ComputableInPolyTime.unary_add' hn
    (ComputableInPolyTime.unary_mul.comp ((ComputableInPolyTime.const 2).prod ha))).prod
    (ComputableInPolyTime.unary_add' hk (ComputableInPolyTime.const 2)))

variable {hash : List Bool → List Bool → List Bool}
  (hf : ComputableInPolyTime (fun p : List Bool × List Bool => hash p.1 p.2)
    (encPair encBits encBits) encBits)

/-- The decoding bits of a simulated view from the output labels `Y` are computed in polynomial
time. -/
private theorem simDecInfo_polyTime :
    ComputableInPolyTime (fun p : ℕ × List Bool × ℕ × List Bool =>
      (List.range p.2.2.1).map fun o =>
        p.2.2.2.getD (o * (p.1 + 2) + (p.1 + 1)) false ^^ p.2.1.getD o false)
      (encPair encUnary (encPair encBits (encPair encUnary encBits))) encBits := by
  polytime

/-- The body of the simulated garbled function, from gate data, is computed in polynomial time. -/
private theorem simBody_polyTime {γ : Type} {encIn : γ ↪ List Bool} {k n : γ → ℕ}
    {gates : γ → List (ℕ × ℕ × List Bool)} {coins : γ → List Bool}
    (hk : ComputableInPolyTime k encIn encUnary) (hn : ComputableInPolyTime n encIn encUnary)
    (hgates : ComputableInPolyTime gates encIn (encList (encPair encNat (encPair encNat encBits))))
    (hcoins : ComputableInPolyTime coins encIn encBits) :
    ComputableInPolyTime (fun x => PointPermute.bodyWith (n x) (gates x).length 0
      (fun g => ((gates x).getD g (0, 0, [])).1) (fun g => ((gates x).getD g (0, 0, [])).2.1)
      (fun g _ _ i => simRow (k x) (n x) (coins x) (((gates x).getD g (0, 0, [])).2.2.getD 3 false)
        (((gates x).take g).countP fun gate => gate.2.2.getD 3 false) i)) encIn encBits := by
  have hx := ComputableInPolyTime.fst encIn (encPair encUnary (encPair encBool encUnary))
  have hrest := ComputableInPolyTime.snd encIn (encPair encUnary (encPair encBool encUnary))
  have hrow : ComputableInPolyTime (fun p : γ × ℕ × Bool × ℕ => simRow (k p.1) (n p.1) (coins p.1)
      p.2.2.1 (((gates p.1).take p.2.1).countP fun gate => gate.2.2.getD 3 false) p.2.2.2)
      (encPair encIn (encPair encUnary (encPair encBool encUnary))) encBits :=
    simRow_polyTime (hk.comp hx) (hn.comp hx) (hcoins.comp hx) hrest.snd'.fst'
      (andCount_polyTime (hgates.comp hx) hrest.fst') hrest.snd'.snd'
  exact bodyWith_gateData_polyTime hn hgates hrow

include hf in
private theorem simViewWord_polyTime :
    ComputableInPolyTime (fun p : (ℕ × List Bool × XorAndCircuit) × List Bool =>
      simViewWord hash p.1.1 p.1.2.1 p.1.2.2.circuit p.2) (encPair encSimInput encBits)
      encPrvView := by
  have hfst := ComputableInPolyTime.fst encSimInput encBits
  have hcoins := ComputableInPolyTime.snd encSimInput encBits
  have hk := (ComputableInPolyTime.fst encUnary (encPair encBits encXorAndCircuit)).comp hfst
  have hy := (ComputableInPolyTime.snd encUnary (encPair encBits encXorAndCircuit)).fst'.comp hfst
  have hn := simData_polyTime.fst'.comp hfst
  have hm := simData_polyTime.snd'.fst'.comp hfst
  have hgates := simData_polyTime.snd'.snd'.comp hfst
  have hq := (ComputableInPolyTime.length_list _).comp hgates
  have hbody := simBody_polyTime hk hn hgates hcoins
  have henc : ComputableInPolyTime (fun z : (ℕ × ℕ × ℕ × ℕ) × List Bool => PointPermute.encFn z)
      PointPermute.encFn encBits := .of_eq fun _ => rfl
  have hF := henc.comp ((hk.prod (hn.prod (hm.prod hq))).prod hbody)
  have hX : ComputableInPolyTime (fun p : (ℕ × List Bool × XorAndCircuit) × List Bool =>
      ((List.range p.1.2.2.circuit.n).map fun i => BitString.listRow (p.1.1 + 2) i p.2).flatten)
      (encPair encSimInput encBits) encBits := by
    polytime [BitString.listRow]
  have hev := (scheme_isEfficient hf).evalGarbled.comp (hF.prod hX)
  have hdec := simDecInfo_polyTime.comp (hk.prod (hy.prod (hm.prod hev)))
  simp only [simViewWord_eq_data]
  exact encPrvView_mk_polyTime hF hX hdec

include hf in
/-- **The simulator is PPT.** For every hash family computed in polynomial time
(`CircularCorrelationRobust.polyTime` supplies `hf`), the simulator runs in uniform strict
probabilistic polynomial time on the parameter in unary, the output and the encoded circuit. -/
theorem isPPTOn_simWord :
    IsPPTOn (encPair encUnary (encPair encBits encXorAndCircuit)) encPrvView
      (fun (k, y, f) => simWord hash k y f) := by
  have h : IsPPTOn encSimInput encPrvView (fun x : ℕ × List Bool × XorAndCircuit => do
      let coins ← BitString.sampleList (simCoinLen x.1 x.2.2.circuit)
      pure (simViewWord hash x.1 x.2.1 x.2.2.circuit coins)) :=
    (isPPTOn_sampleList.preprocess simCoinLen_polyTime).bind_with
      (simViewWord_polyTime hf).isPPTOn
  refine h.congr ?_
  rintro ⟨k, y, f⟩
  rfl

end Efficiency

end Cslib.Crypto.Garbling.HalfGates
