/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.Garbling.FreeXOR.Efficient
public import CslibFrontier.Crypto.Primitives.Garbling.FreeXOR.Propagate
public import CslibFrontier.Crypto.Primitives.Garbling.PointPermute.Simulator
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
# The simulator of Free-XOR garbling

The privacy simulator `FreeXOR.simulate` of `CslibFrontier.Crypto.Primitives.Garbling.FreeXOR`,
written on words, for `FreeXOR.scheme hash` with the side information `phiXor`, which reveals the
circuit topology and which gates compute XOR while hiding the truth tables of all non-XOR gates.

The simulator `simWord hash k y t` sees the parameter `k`, the output `y` and `t : XorTopology`
(`(topo, free)`). It samples one `(k + 2)`-bit label for each of the `n + q` wires and four filler
labels for each non-XOR gate (`nonXorRank`), propagates active labels through the XOR gates, writes
the garbled function with the active row of each non-XOR gate holding the gate's label masked under
the hash of its arguments' active labels and the remaining three rows filled from the coins, lists
the input labels in `X`, and sets `d` so that the output active labels decode to `y`.

The simulator's output law is the typed simulator's (`eval_simWord`), every view it writes for a
valid circuit and an `m`-bit output decodes to that output (`decodeWord_evalWord_simViewWord`),
and it is PPT whenever `hash` is computed in polynomial time (`isPPTOn_simWord`).

## Main definitions

* `Cslib.Crypto.Garbling.FreeXOR.viewWord`: the words `(F, X, d)` of a typed Free-XOR view.
* `Cslib.Crypto.Garbling.FreeXOR.simViewWord`, `Cslib.Crypto.Garbling.FreeXOR.simWord`: the
  simulated view on given coins, and the simulator.

## Main results

* `Cslib.Crypto.Garbling.FreeXOR.eval_simWord`: the simulator samples the words of the typed
  simulator's view.
* `Cslib.Crypto.Garbling.FreeXOR.decodeWord_evalWord_simViewWord`: simulated views decode to the
  output.
* `Cslib.Crypto.Garbling.FreeXOR.isPPTOn_simWord`: the simulator is PPT.
-/

public section

namespace Cslib.Crypto.Garbling.FreeXOR

open Cslib.Circuits Probability ConventionalCircuit

/-! ### The simulated view -/

/-- The number of non-XOR gates among the first `g` gates recorded in `free`. -/
@[expose] def nonXorRank (free : List Bool) (g : ℕ) : ℕ :=
  (free.take g).count false

/-- The number of coins of the simulator at parameter `k` for `t`: one label for each of the
`n + q` wires, then four filler labels for each non-XOR gate. -/
@[expose] def simCoinLen (k : ℕ) (t : XorTopology) : ℕ :=
  (t.topo.1.n + t.topo.1.q + 4 * nonXorRank t.free t.topo.1.q) * (k + 2)

variable (hash : List Bool → List Bool → List Bool)

/-- Row `i` of non-XOR gate `g` in the simulated table, from the active wire labels `labels` and
the coins. -/
@[expose] def simRow (k : ℕ) (t : Topo) (free : List Bool) (labels : List (List Bool))
    (coins : List Bool) (g : Fin t.q) (i : ℕ) : List Bool :=
  let a := labels.getD (t.A g - 1) []
  let b := labels.getD (t.B g - 1) []
  let idx := (if HalfGates.colourWord k a then 2 else 0) +
    (if HalfGates.colourWord k b then 1 else 0)
  if i = idx then
    List.zipWith xor (labels.getD (t.n + g) [])
      (List.zipWith xor (keyHashWord hash k a (PointPermute.tweak k g i 0))
        (keyHashWord hash k b (PointPermute.tweak k g i 1)))
  else PointPermute.simLabel k coins (t.n + t.q + 4 * nonXorRank free g + i)

/-- The block of gate `g` in the simulated garbled function. -/
@[expose] def simGateWord (k w : ℕ) (t : XorTopology) (labels : List (List Bool))
    (coins : List Bool) (g : Fin t.topo.1.q) : List Bool :=
  BitString.lowBits w (t.topo.1.A g) ++ BitString.lowBits w (t.topo.1.B g) ++
    [t.free.getD g false] ++
    if t.free.getD g false then [] else
      (List.ofFn fun i : Fin 4 => simRow hash k t.topo.1 t.free labels coins g i).flatten

/-- The simulated view `(F, X, d)` at parameter `k` for output `y` and `t : XorTopology`, on the
simulator's coins. -/
@[expose] def simViewWord (k : ℕ) (y : List Bool) (t : XorTopology) (coins : List Bool) :
    PrvView :=
  let labels := simPropWords k t.topo.1 t.free coins t.topo.1.q
  let F := PointPermute.encFn ((k, t.topo.1.n, t.topo.1.m, t.topo.1.q), (List.ofFn fun g =>
    simGateWord hash k (PointPermute.wireWidth t.topo.1.n t.topo.1.q) t labels coins g).flatten)
  let X := (List.ofFn fun i : Fin t.topo.1.n => PointPermute.simLabel k coins i).flatten
  let d := List.ofFn fun o : Fin t.topo.1.m =>
    HalfGates.colourWord k (labels.getD (t.topo.1.n + t.topo.1.q - t.topo.1.m + o) []) ^^
      y.getD o false
  ⟨F, X, d⟩

/-- **The simulator** `S(1^k, y, Φ_xor(f))` of Free-XOR garbling: sample the coins and write the
simulated view. -/
noncomputable def simWord (k : ℕ) (y : List Bool) (t : XorTopology) : ProbComp PrvView := do
  let coins ← BitString.sampleList (simCoinLen k t)
  return simViewWord hash k y t coins

/-- The words `(F, X, d)` of a typed Free-XOR view at parameter `k`. -/
@[expose] def viewWord {n m s : ℕ} (k : ℕ) (τ : Circuit.Topology n m s) (free : Fin s → Bool)
    (V : View τ free (BitString (k + 1))) : PrvView where
  fn := encodeFn k τ free V.table
  input := (List.ofFn fun i => labelBits (V.input i)).flatten
  decInfo := List.ofFn V.decoding

/-! ### The simulator's coins -/

private theorem nonXorRank_succ (free : List Bool) {g : ℕ} (hg : g < free.length) :
    nonXorRank free (g + 1) = nonXorRank free g + (!free[g]).toNat := by
  simp only [nonXorRank]
  rw [List.take_add_one, List.count_append, List.getElem?_eq_getElem hg]
  cases free[g] <;> simp

private theorem nonXorRank_mono (free : List Bool) {g g' : ℕ} (h : g ≤ g') :
    nonXorRank free g ≤ nonXorRank free g' :=
  (List.take_sublist_take_left h).count_le _

/-- A non-XOR gate strictly increases `nonXorRank`. -/
theorem nonXorRank_lt (free : List Bool) {g g' : ℕ} (hg : g < free.length)
    (hf : free[g] = false) (h : g < g') : nonXorRank free g < nonXorRank free g' := by
  have hsucc := nonXorRank_succ free hg
  rw [hf] at hsucc
  have := nonXorRank_mono free (show g + 1 ≤ g' from h)
  simp only [Bool.not_false, Bool.toNat_true] at hsucc
  omega

private theorem nonXorRank_phiXor_q (f : ValidCircuit) :
    nonXorRank (phiXor.phi f).free f.1.q =
      Fintype.card {g : Fin f.1.q // isXorGate f.1 g = false} := by
  have hmap : (List.ofFn fun g : Fin f.1.q => isXorGate f.1 g).count false =
      (List.ofFn fun g : Fin f.1.q => !(isXorGate f.1 g)).count true := by
    simp only [List.count_eq_countP, List.ofFn_eq_map, List.countP_map, Function.comp_def]
    congr 1
  rw [nonXorRank, phiXor, List.take_of_length_le (by simp), hmap, BitString.count_true_ofFn,
    BitString.weight_eq_card_subtype]
  refine Fintype.card_congr (Equiv.subtypeEquivRight fun g => ?_)
  simp

private theorem freeCircuit_eq_false_iff (f : ValidCircuit) (g : Fin (toCircuit f).size) :
    freeCircuit f g = false ↔ isXorGate f.1 (g.cast (size_toCircuit f)) = false :=
  Iff.rfl

private theorem card_garbledRow_toCircuit (f : ValidCircuit) :
    Fintype.card (GarbledRow (toCircuit f).topology (freeCircuit f)) =
      4 * nonXorRank (phiXor.phi f).free f.1.q := by
  let e : GarbledRow (toCircuit f).topology (freeCircuit f) ≃
      {g : Fin f.1.q // isXorGate f.1 g = false} × (Fin 2 → Bool) :=
    ⟨fun r => ⟨⟨r.1.1.cast (size_toCircuit f), (freeCircuit_eq_false_iff f r.1.1).mp r.1.2⟩,
        fun a => r.2 (Fin.cast (arity_topology_toCircuit f r.1.1).symm a)⟩,
      fun p => ⟨⟨p.1.1.cast (size_toCircuit f).symm,
        (freeCircuit_eq_false_iff f (p.1.1.cast (size_toCircuit f).symm)).mpr p.1.2⟩,
        fun a => p.2 (Fin.cast (arity_topology_toCircuit f _) a)⟩,
      fun ⟨⟨g, hg⟩, c⟩ => by
        refine Sigma.ext (Subtype.ext (Fin.ext rfl)) ?_
        apply heq_of_eqRec_eq ?_ (funext fun a => by congr)
        simp,
      fun ⟨⟨g, hg⟩, c⟩ => by
        refine Prod.ext (Subtype.ext (Fin.ext rfl)) ?_
        funext a
        congr⟩
  rw [Fintype.card_congr e, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_bool, nonXorRank_phiXor_q, mul_comm]
  rfl

private noncomputable def rowCoinIndex (f : ValidCircuit)
    (r : GarbledRow (toCircuit f).topology (freeCircuit f)) : ℕ :=
  f.1.n + f.1.q + 4 * nonXorRank (phiXor.phi f).free r.gate + PointPermute.rowIndex r.2

/-- The non-XOR rank strictly increases past the gate of a garbled row. -/
private theorem nonXorRank_gate_lt (f : ValidCircuit)
    (r : GarbledRow (toCircuit f).topology (freeCircuit f)) {j : ℕ} (hj : (r.gate : ℕ) < j) :
    nonXorRank (phiXor.phi f).free r.gate < nonXorRank (phiXor.phi f).free j := by
  have hq : (r.gate : ℕ) < f.1.q := r.gate.isLt.trans_eq (size_toCircuit f)
  have hfree : (phiXor.phi f).free[(r.gate : ℕ)]'(by simp [phiXor, hq]) = false := by
    simpa [phiXor] using (show isXorGate f.1 ⟨r.gate, hq⟩ = false from r.1.2)
  exact nonXorRank_lt (phiXor.phi f).free (by simp [phiXor, hq]) hfree hj

private theorem rowCoinIndex_lt (f : ValidCircuit)
    (r : GarbledRow (toCircuit f).topology (freeCircuit f)) :
    rowCoinIndex f r < f.1.n + f.1.q + 4 * nonXorRank (phiXor.phi f).free f.1.q := by
  have hrank := nonXorRank_gate_lt f r (r.gate.isLt.trans_eq (size_toCircuit f))
  have hrow := PointPermute.rowIndex_lt_four (arity_topology_toCircuit f r.gate) r.2
  simp only [rowCoinIndex]
  omega

private noncomputable def simFillerRows (k : ℕ) (f : ValidCircuit) (coins : List Bool)
    (r : GarbledRow (toCircuit f).topology (freeCircuit f)) : BitString (k + 1) × Bool :=
  labelOfWord k (PointPermute.simLabel k coins (rowCoinIndex f r))

private noncomputable def simIndex (f : ValidCircuit) :
    Wire f.1.n (toCircuit f).size ⊕ GarbledRow (toCircuit f).topology (freeCircuit f) →
      Fin (f.1.n + f.1.q + 4 * nonXorRank (phiXor.phi f).free f.1.q)
  | .inl w => ⟨w.toNat, by have hwt := w.toNat_lt; have hsz := size_toCircuit f; omega⟩
  | .inr r => ⟨rowCoinIndex f r, rowCoinIndex_lt f r⟩

private theorem simIndex_bijective (f : ValidCircuit) : Function.Bijective (simIndex f) := by
  refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨?_, ?_⟩
  · rintro (w | r) (w' | r') h <;> simp only [simIndex, Fin.mk.injEq] at h
    · exact congrArg Sum.inl (Wire.toNat_injective h)
    · have hwt := w.toNat_lt; have hsz := size_toCircuit f
      have hrc : f.1.n + f.1.q ≤ rowCoinIndex f r' := by dsimp [rowCoinIndex]; omega
      omega
    · have hwt := w'.toNat_lt; have hsz := size_toCircuit f
      have hrc : f.1.n + f.1.q ≤ rowCoinIndex f r := by dsimp [rowCoinIndex]; omega
      omega
    · simp only [rowCoinIndex] at h
      have hidx := PointPermute.rowIndex_lt_four (arity_topology_toCircuit f r.gate) r.2
      have hidx' := PointPermute.rowIndex_lt_four (arity_topology_toCircuit f r'.gate) r'.2
      have hrank : nonXorRank (phiXor.phi f).free r.gate =
          nonXorRank (phiXor.phi f).free r'.gate := by omega
      have hrow : PointPermute.rowIndex r.2 = PointPermute.rowIndex r'.2 := by omega
      have hgg : r.gate = r'.gate := by
        rcases lt_trichotomy (r.gate : ℕ) r'.gate with hlt | heq | hgt
        · exact absurd (nonXorRank_gate_lt f r hlt) (by omega)
        · exact Fin.ext heq
        · exact absurd (nonXorRank_gate_lt f r' hgt) (by omega)
      obtain ⟨⟨g, hg⟩, c⟩ := r
      obtain ⟨⟨g', hg'⟩, c'⟩ := r'
      change g = g' at hgg
      subst hgg
      obtain rfl := PointPermute.rowIndex_injective_of_eq_two (arity_topology_toCircuit f g) hrow
      rfl
  · have hcard := card_garbledRow_toCircuit f
    have hsz := size_toCircuit f
    rw [Fintype.card_sum, Wire.card, Fintype.card_fin, hcard, hsz]

private theorem uniformList_map_simCoins (k : ℕ) (f : ValidCircuit) :
    (BitString.uniformList (simCoinLen k (phiXor.phi f))).map
        (fun coins => ((simBaseLabels k coins : Wire f.1.n (toCircuit f).size → _),
          simFillerRows k f coins)) =
      PMF.uniformOfFintype ((Wire f.1.n (toCircuit f).size → BitString (k + 1) × Bool) ×
        (GarbledRow (toCircuit f).topology (freeCircuit f) → BitString (k + 1) × Bool)) := by
  let e := Equiv.ofBijective _ (simIndex_bijective f)
  let E : (Wire f.1.n (toCircuit f).size ⊕
        GarbledRow (toCircuit f).topology (freeCircuit f) → BitString (k + 2)) ≃
      (Wire f.1.n (toCircuit f).size → BitString (k + 1) × Bool) ×
        (GarbledRow (toCircuit f).topology (freeCircuit f) → BitString (k + 1) × Bool) :=
    (Equiv.sumArrowEquivProdArrow _ _ _).trans (Equiv.prodCongr
      (Equiv.arrowCongr (Equiv.refl _) (labelEquiv k))
      (Equiv.arrowCongr (Equiv.refl _) (labelEquiv k)))
  have h : (fun coins => ((simBaseLabels k coins : Wire f.1.n (toCircuit f).size → _),
        simFillerRows k f coins)) =
      (E : _ → _) ∘ fun coins i =>
        BitString.ofList (k + 2) (BitString.listRow (k + 2) (e i) coins) := by
    funext coins
    rfl
  dsimp only [simCoinLen]
  rw [show (phiXor.phi f).topo.1.n = f.1.n from rfl,
    show (phiXor.phi f).topo.1.q = f.1.q from rfl,
    h, ← PMF.map_comp, BitString.uniformList_map_listRow_equiv e (k + 2)]
  exact PMF.uniformOfFintype_map_equiv E

/-! ### The simulated view is the typed simulator's -/

/-- The simulated propagated words after all `q` gates match the typed propagated base labels. -/
theorem simPropWords_q (k : ℕ) (f : ValidCircuit) (coins : List Bool) :
    simPropWords k (phiXor.phi f).topo.1 (phiXor.phi f).free coins f.1.q =
      List.ofFn fun v : Fin (f.1.n + (toCircuit f).size) =>
        labelBits (propagate (toCircuit f).topology (freeCircuit f)
          (simBaseLabels k coins) (Wire.ofNat v v.isLt)) := by
  rw [show (phiXor.phi f).topo.1 = f.1.topo from rfl,
    simPropWords_eq_propagate k f (phiXor.phi f).free coins
      (fun g => by simp [phiXor, List.getD_eq_getElem?_getD]) le_rfl,
    List.take_of_length_le (by simp [size_toCircuit])]

private theorem simRow_eq_simulateWith (k : ℕ) (f : ValidCircuit) (y : Fin f.1.m → Bool)
    (coins : List Bool) (g : Fin (toCircuit f).size) (hg : freeCircuit f g = false)
    {i : ℕ} (hi : i < 4) :
    simRow hash k (phiXor.phi f).topo.1 (phiXor.phi f).free
        (simPropWords k (phiXor.phi f).topo.1 (phiXor.phi f).free coins f.1.q) coins
        (g.cast (size_toCircuit f)) i =
      labelBits ((simulateWith (toCircuit f).topology (freeCircuit f)
        (fun key t => CCR.atLevel hash k (key, false) t)
        (slotTweak (toCircuit f).topology (freeCircuit f) k) y
        (propagate (toCircuit f).topology (freeCircuit f) (simBaseLabels k coins))
        (simFillerRows k f coins)).table (garbledRowOf _ g hg i)) := by
  have harity := arity_topology_toCircuit f g
  have hc₀ : (Fin.cast harity.symm 0 : Fin ((toCircuit f).topology.arity g)) = ⟨0, by omega⟩ :=
    Fin.ext rfl
  have hc₁ : (Fin.cast harity.symm 1 : Fin ((toCircuit f).topology.arity g)) = ⟨1, by omega⟩ :=
    Fin.ext rfl
  set A := propagate (toCircuit f).topology (freeCircuit f) (simBaseLabels k coins)
  rw [simPropWords_q]
  dsimp only [simRow, phiXor, phiTopo, ConventionalCircuit.topo, Fin.val_cast]
  simp only [getD_ofFn_wire_gate, getD_ofFn_wire_A, getD_ofFn_wire_B,
    HalfGates.colourWord_labelBits]
  set idx := (if (A ((toCircuit f).topology.wires g (Fin.cast harity.symm 0))).2 then 2 else 0) +
    (if (A ((toCircuit f).topology.wires g (Fin.cast harity.symm 1))).2 then 1 else 0) with hidx
  have hidx_eq : idx = PointPermute.rowIndex fun a =>
      (A ((toCircuit f).topology.wires g a)).2 := by
    rw [hidx, PointPermute.rowIndex_of_eq_two harity, hc₀, hc₁]
  have hcond : (i = idx) ↔ (garbledRowOf (toCircuit f).topology g hg i).2 =
      fun a => (A ((toCircuit f).topology.wires g a)).2 := by
    dsimp only [garbledRowOf]
    conv_lhs => rw [hidx_eq, ← PointPermute.rowIndex_testBit_of_eq_two harity hi]
    exact (PointPermute.rowIndex_injective_of_eq_two harity).eq_iff
  dsimp only [simulateWith, GarbledRow.gate]
  rw [apply_ite labelBits]
  refine ite_congr (propext hcond) (fun _ => ?_) (fun _ => ?_)
  · conv_rhs =>
      change labelBits (A (.gate g) + ∑ k_1 : Fin ((toCircuit f).topology.arity g),
        CCR.atLevel hash k ((A ((toCircuit f).topology.wires g k_1)).1, false)
          (slotTweak (toCircuit f).topology (freeCircuit f) k
            ⟨garbledRowOf (toCircuit f).topology g hg i, k_1⟩))
    rw [labelBits_add, ← Fin.sum_congr' _ harity.symm, Fin.sum_univ_two, labelBits_add,
      labelBits_atLevel_key, labelBits_atLevel_key, ofFn_slotTweak_garbledRowOf _ _ _ _ hi,
      ofFn_slotTweak_garbledRowOf _ _ _ _ hi]
    rfl
  · rw [simFillerRows, labelBits_labelOfWord (PointPermute.length_simLabel k coins _),
      rowCoinIndex, GarbledRow.gate, garbledRowOf,
      PointPermute.rowIndex_testBit_of_eq_two harity hi]
    rfl

private theorem encodeGate_simulateWith (k : ℕ) (f : ValidCircuit) (y : Fin f.1.m → Bool)
    (coins : List Bool) (g : Fin (toCircuit f).size) :
    encodeGate k (PointPermute.wireWidth f.1.n (toCircuit f).size) (toCircuit f).topology
        (freeCircuit f)
        (simulateWith (toCircuit f).topology (freeCircuit f)
          (fun key t => CCR.atLevel hash k (key, false) t)
          (slotTweak (toCircuit f).topology (freeCircuit f) k) y
          (propagate (toCircuit f).topology (freeCircuit f) (simBaseLabels k coins))
          (simFillerRows k f coins)).table g =
      simGateWord hash k (PointPermute.wireWidth f.1.n f.1.q) (phiXor.phi f)
        (simPropWords k (phiXor.phi f).topo.1 (phiXor.phi f).free coins f.1.q) coins
        (g.cast (size_toCircuit f)) := by
  rw [encodeGate_toCircuit]
  simp only [simGateWord, phiXor, phiTopo, ConventionalCircuit.topo]
  have hfree_eq : (List.ofFn fun g' => isXorGate f.1 g').getD
      (g.cast (size_toCircuit f) : Fin f.1.q).val false = freeCircuit f g := by
    simp only [freeCircuit, List.getD_eq_getElem?_getD, List.getElem?_ofFn, Fin.val_cast,
      show (g : ℕ) < f.1.q from by have := g.isLt; have := size_toCircuit f; omega,
      dite_true, Option.getD_some]
    rfl
  simp only [hfree_eq]
  by_cases hg : freeCircuit f g = true
  · have hg' : ¬ freeCircuit f g = false := by simp [hg]
    rw [dite_eq_right hg', ite_eq_left hg]
    rfl
  · have hg' : freeCircuit f g = false := Bool.eq_false_iff.mpr hg
    rw [dite_eq_left hg', ite_eq_right hg]
    refine congrArg (_ ++ ·) (congrArg List.flatten (congrArg List.ofFn (funext fun i => ?_)))
    exact (simRow_eq_simulateWith hash k f y coins g hg' i.isLt).symm

/-- **The simulated view is the typed simulator's.** -/
private theorem simViewWord_eq (k : ℕ) (f : ValidCircuit) (y coins : List Bool) :
    simViewWord hash k y (phiXor.phi f) coins = viewWord k (toCircuit f).topology (freeCircuit f)
      (simulateWith (toCircuit f).topology (freeCircuit f)
        (fun key t => CCR.atLevel hash k (key, false) t)
        (slotTweak (toCircuit f).topology (freeCircuit f) k) (BitString.ofList f.1.m y)
        (propagate (toCircuit f).topology (freeCircuit f) (simBaseLabels k coins))
        (simFillerRows k f coins)) := by
  have hτ := (toCircuit f).isOrdered_topology
  have hF : PointPermute.encFn ((k, (phiXor.phi f).topo.1.n, (phiXor.phi f).topo.1.m,
      (phiXor.phi f).topo.1.q), (List.ofFn fun g =>
      simGateWord hash k (PointPermute.wireWidth (phiXor.phi f).topo.1.n (phiXor.phi f).topo.1.q)
        (phiXor.phi f) (simPropWords k (phiXor.phi f).topo.1 (phiXor.phi f).free coins
          (phiXor.phi f).topo.1.q) coins g).flatten) =
      encodeFn k (toCircuit f).topology (freeCircuit f)
        (simulateWith (toCircuit f).topology (freeCircuit f)
          (fun key t => CCR.atLevel hash k (key, false) t)
          (slotTweak (toCircuit f).topology (freeCircuit f) k) (BitString.ofList f.1.m y)
          (propagate (toCircuit f).topology (freeCircuit f) (simBaseLabels k coins))
          (simFillerRows k f coins)).table := by
    simp only [encodeFn, encodeGate_simulateWith]
    congr 2
    · rw [size_toCircuit]; rfl
    · rw [List.ofFn_congr (size_toCircuit f)]
      rfl
  have hX : (List.ofFn fun i : Fin (phiXor.phi f).topo.1.n =>
      PointPermute.simLabel k coins i).flatten =
      (List.ofFn fun i : Fin f.1.n =>
        labelBits ((simulateWith (toCircuit f).topology (freeCircuit f)
          (fun key t => CCR.atLevel hash k (key, false) t)
          (slotTweak (toCircuit f).topology (freeCircuit f) k) (BitString.ofList f.1.m y)
          (propagate (toCircuit f).topology (freeCircuit f) (simBaseLabels k coins))
          (simFillerRows k f coins)).input i)).flatten := by
    simp only [simulateWith, propagate_input hτ, simBaseLabels,
      labelBits_labelOfWord (PointPermute.length_simLabel k coins _)]
    rfl
  simp only [simViewWord, viewWord, PrvView.mk.injEq]
  refine ⟨hF, hX, ?_⟩
  rw [show (phiXor.phi f).topo.1.q = f.1.q from rfl, simPropWords_q]
  simp only [phiXor, phiTopo, ConventionalCircuit.topo]
  refine congrArg List.ofFn (funext fun o => ?_)
  rw [getD_ofFn_wire_output, HalfGates.colourWord_labelBits]
  rfl

/-- **The simulator samples the typed simulator's view.** -/
theorem eval_simWord (k : ℕ) (f : ValidCircuit) (y : List Bool) :
    ProbComp.eval (simWord hash k y (phiXor.phi f)) =
      (ProbComp.eval (simulate (toCircuit f).topology (freeCircuit f)
        (fun key t => CCR.atLevel hash k (key, false) t)
        (slotTweak (toCircuit f).topology (freeCircuit f) k)
        (BitString.ofList f.1.m y))).map (viewWord k _ _) := by
  have hsim := uniformList_map_simCoins k f
  have hview : simViewWord hash k y (phiXor.phi f) =
      (fun p : (Wire f.1.n (toCircuit f).size → BitString (k + 1) × Bool) ×
          (GarbledRow (toCircuit f).topology (freeCircuit f) → BitString (k + 1) × Bool) =>
        viewWord k _ _ (simulateWith (toCircuit f).topology (freeCircuit f)
          (fun key t => CCR.atLevel hash k (key, false) t)
          (slotTweak (toCircuit f).topology (freeCircuit f) k) (BitString.ofList f.1.m y)
          (propagate (toCircuit f).topology (freeCircuit f) p.1) p.2)) ∘
        (fun coins => (simBaseLabels k coins, simFillerRows k f coins)) :=
    funext fun coins => simViewWord_eq hash k f y coins
  change ProbComp.eval (do
      let coins ← BitString.sampleList (simCoinLen k (phiXor.phi f))
      return simViewWord hash k y (phiXor.phi f) coins) = _
  simp only [simulate, bind_pure_comp, ProbComp.eval_map, ProbComp.eval_bind,
    ProbComp.eval_uniform, BitString.eval_sampleList]
  rw [hview, ← PMF.map_comp, hsim, ← Cslib.Probability.PMF.uniformOfFintype_prod]
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]

/-- **Simulated views decode to the output.** -/
theorem decodeWord_evalWord_simViewWord (k : ℕ) (f : ValidCircuit) {y : List Bool}
    (hy : y.length = f.1.m) (coins : List Bool) :
    PointPermute.decodeWord (simViewWord hash k y (phiXor.phi f) coins).decInfo
      (evalWord hash (simViewWord hash k y (phiXor.phi f) coins).fn
        (simViewWord hash k y (phiXor.phi f) coins).input) = some y := by
  rw [simViewWord_eq]
  simp only [viewWord]
  rw [evalWord_encodeFn hash k f _ _ _
    (evalStep_simulateWith (toCircuit f).isOrdered_topology (freeCircuit f)
      (fun key t => CCR.atLevel hash k (key, false) t)
      (slotTweak (toCircuit f).topology (freeCircuit f) k) _ _ _),
    PointPermute.decodeWord_ofFn]
  congr 1
  conv_rhs => rw [← BitString.ofFn_ofList hy]
  congr 1
  funext o
  simp only [decode, simulateWith]
  rw [show (toCircuit f).outputs o = (toCircuit f).topology.outputs o from rfl,
    ← add_assoc, BooleanRing.add_self, zero_add]

/-! ### Efficiency -/

section Efficiency

open Turing.MultiTapeTM

private theorem nonXorRank_eq_countP (free : List Bool) (g : ℕ) :
    nonXorRank free g = (free.take g).countP fun b => !b := by
  rw [nonXorRank, List.count_eq_countP]
  rfl

private def simPropStep (k n : ℕ) (free coins : List Bool) (ws : List (List Bool))
    (gate : ℕ × ℕ) : List (List Bool) :=
  ws ++ [if free.getD (ws.length - n) false then
    (List.zipWith xor (ws.getD (min (ws.length + 1) gate.1 - 1) [])
      (ws.getD (min (ws.length + 1) gate.2 - 1) [])).take (k + 2)
  else PointPermute.simLabel k coins ws.length]

private theorem simPropWords_eq_foldl (k : ℕ) (t : Topo)
    (hA : ∀ g : Fin t.q, 1 ≤ t.A g) (hAB_lt : ∀ g : Fin t.q, t.A g < t.B g)
    (hBg_lt : ∀ g : Fin t.q, t.B g < t.n + 1 + g) (free coins : List Bool)
    {s : ℕ} (hs : s ≤ t.q) :
    simPropWords k t free coins s =
      (t.gateList.take s).foldl (simPropStep k t.n free coins)
        ((List.range t.n).map (PointPermute.simLabel k coins)) := by
  induction s with
  | zero => simp [simPropWords, List.map_range_eq_ofFn]
  | succ s ih =>
    have hsq : s < t.q := hs
    have hA₁ := hA ⟨s, hsq⟩
    have hAB := hAB_lt ⟨s, hsq⟩
    have hBg := hBg_lt ⟨s, hsq⟩
    dsimp only at hA₁ hAB hBg
    rw [List.take_add_one, List.foldl_append, ← ih hsq.le, simPropWords, dite_eq_left hsq]
    have hget : t.gateList[s]? = some (t.A ⟨s, hsq⟩, t.B ⟨s, hsq⟩) := by
      simp [Topo.gateList, hsq]
    rw [hget]
    simp only [Option.toList_some, List.foldl_cons, List.foldl_nil, simPropStep,
      length_simPropWords k t free coins hsq.le, Nat.add_sub_cancel_left,
      show min (t.n + s + 1) (t.A ⟨s, hsq⟩) = t.A ⟨s, hsq⟩ from Nat.min_eq_right (by omega),
      show min (t.n + s + 1) (t.B ⟨s, hsq⟩) = t.B ⟨s, hsq⟩ from Nat.min_eq_right (by omega)]
    by_cases hxor : free.getD s false = true
    · rw [ite_eq_left hxor, ite_eq_left hxor]
      have ha := HalfGates.length_getD_le (length_le_of_mem_simPropWords k t free coins s)
        (t.A ⟨s, hsq⟩ - 1)
      rw [List.take_of_length_le (by rw [List.length_zipWith]; omega)]
    · rw [ite_eq_right hxor, ite_eq_right hxor]

private def simRowData (k n q : ℕ) (free : List Bool) (labels : List (List Bool))
    (coins : List Bool) (g a b i : ℕ) : List Bool :=
  let isXor := free.getD g false
  (if i = 0 then [isXor] else []) ++
    if isXor then [] else
      let la := labels.getD a []
      let lb := labels.getD b []
      let idx := (if HalfGates.colourWord k la then 2 else 0) +
        (if HalfGates.colourWord k lb then 1 else 0)
      if i = idx then
        List.zipWith xor (labels.getD (n + g) [])
          (List.zipWith xor (keyHashWord hash k la (PointPermute.tweak k g i 0))
            (keyHashWord hash k lb (PointPermute.tweak k g i 1)))
      else PointPermute.simLabel k coins (n + q + 4 * nonXorRank free g + i)

private theorem simFn_eq (k : ℕ) (t : XorTopology) (coins : List Bool) :
    PointPermute.encFn ((k, t.topo.1.n, t.topo.1.m, t.topo.1.q), (List.ofFn fun g =>
      simGateWord hash k (PointPermute.wireWidth t.topo.1.n t.topo.1.q) t
        (simPropWords k t.topo.1 t.free coins t.topo.1.q) coins g).flatten) =
      PointPermute.encFn ((k, t.topo.1.n, t.topo.1.m, t.topo.1.gateList.length),
        PointPermute.bodyWith t.topo.1.n t.topo.1.gateList.length
          ((simPropWords k t.topo.1 t.free coins t.topo.1.q).length + 1)
          (fun g => (t.topo.1.gateList.getD g (0, 0)).1)
          (fun g => (t.topo.1.gateList.getD g (0, 0)).2)
          (fun g a b i => simRowData hash k t.topo.1.n t.topo.1.q t.free
            (simPropWords k t.topo.1 t.free coins t.topo.1.q) coins g a b i)) := by
  have hgate (g : Fin t.topo.1.q) :
      t.topo.1.gateList.getD g (0, 0) = (t.topo.1.A g, t.topo.1.B g) := by
    simp [Topo.gateList, List.getD_eq_getElem?_getD]
  have hA₁ (g : Fin t.topo.1.q) : 1 ≤ t.topo.1.A g := t.topo.2.one_le_A g
  have hAB (g : Fin t.topo.1.q) : t.topo.1.A g < t.topo.1.B g := t.topo.2.A_lt_B g
  have hBg (g : Fin t.topo.1.q) : t.topo.1.B g < t.topo.1.n + 1 + g := t.topo.2.B_lt_gate g
  have hlen : (simPropWords k t.topo.1 t.free coins t.topo.1.q).length = t.topo.1.n + t.topo.1.q :=
    length_simPropWords k t.topo.1 t.free coins le_rfl
  rw [Topo.length_gateList, PointPermute.bodyWith_eq_ofFn t.topo.1.A t.topo.1.B
    (fun g i => simRowData hash k t.topo.1.n t.topo.1.q t.free
      (simPropWords k t.topo.1 t.free coins t.topo.1.q) coins g (t.topo.1.A g - 1)
      (t.topo.1.B g - 1) i)
    (fun g => by rw [hgate]) (fun g => by rw [hgate])
    (fun g i => by
      have ha := hA₁ g
      have hab := hAB g
      have hb := hBg g
      have hg := g.isLt
      simp only [hlen, show min (t.topo.1.n + t.topo.1.q + 1) (t.topo.1.A g) = t.topo.1.A g
          from Nat.min_eq_right (by omega),
        show min (t.topo.1.n + t.topo.1.q + 1) (t.topo.1.B g) = t.topo.1.B g
          from Nat.min_eq_right (by omega)])]
  congr 2
  refine congrArg List.flatten (congrArg List.ofFn (funext fun g => ?_))
  simp only [simGateWord, simRowData, simRow, List.ofFn_succ, List.ofFn_zero, List.flatten_cons,
    List.flatten_nil, List.append_assoc]
  cases t.free.getD g false <;> simp

private theorem simViewWord_eq_data (k : ℕ) (y : List Bool) (t : XorTopology)
    (coins : List Bool) :
    simViewWord hash k y t coins =
      ⟨PointPermute.encFn ((k, t.topo.1.n, t.topo.1.m, t.topo.1.gateList.length),
          PointPermute.bodyWith t.topo.1.n t.topo.1.gateList.length
            ((simPropWords k t.topo.1 t.free coins t.topo.1.q).length + 1)
            (fun g => (t.topo.1.gateList.getD g (0, 0)).1)
            (fun g => (t.topo.1.gateList.getD g (0, 0)).2)
            (fun g a b i => simRowData hash k t.topo.1.n t.topo.1.q t.free
              (simPropWords k t.topo.1 t.free coins t.topo.1.q) coins g a b i)),
        ((List.range t.topo.1.n).map (PointPermute.simLabel k coins)).flatten,
        (List.range t.topo.1.m).map fun o =>
          HalfGates.colourWord k ((simPropWords k t.topo.1 t.free coins t.topo.1.q).getD
            (t.topo.1.n + t.topo.1.gateList.length - t.topo.1.m + o) []) ^^
            y.getD o false⟩ := by
  simp only [simViewWord, simFn_eq, Topo.length_gateList, List.map_range_eq_ofFn]

private abbrev encSimInput : (ℕ × List Bool × XorTopology) ↪ List Bool :=
  encPair encUnary (encPair encBits encXorTopology)

private theorem simData_polyTime :
    ComputableInPolyTime (fun x : ℕ × List Bool × XorTopology =>
      (x.2.2.topo.1.n, x.2.2.topo.1.m, x.2.2.topo.1.gateList)) encSimInput encTopoData :=
  topoData_polyTime.comp (encXorTopology_topo_polyTime (ComputableInPolyTime.snd _ _).snd')

private theorem simPropStep_polyTime :
    ComputableInPolyTime (fun p : ((ℕ × ℕ × List Bool × List Bool) × List (List Bool)) ×
        (ℕ × ℕ) => simPropStep p.1.1.1 p.1.1.2.1 p.1.1.2.2.1 p.1.1.2.2.2 p.1.2 p.2)
      (encPair (encPair (encPair encUnary (encPair encUnary (encPair encBits encBits)))
        (encList encBits)) (encPair encNat encNat)) (encList encBits) := by
  polytime [simPropStep, PointPermute.simLabel, BitString.listRow]

/-- `simPropWords` is computed in polynomial time for any polynomial-time topology satisfying the
circuit ordering bounds. -/
theorem simPropWords_polyTime_of {γ : Type} {encIn : γ ↪ List Bool}
    {k : γ → ℕ} {t : γ → Topo} {free coins : γ → List Bool}
    (hk : ComputableInPolyTime k encIn encUnary)
    (hd : ComputableInPolyTime (fun x => ((t x).n, (t x).m, (t x).gateList)) encIn encTopoData)
    (hfree : ComputableInPolyTime free encIn encBits)
    (hcoins : ComputableInPolyTime coins encIn encBits)
    (hA : ∀ x (g : Fin (t x).q), 1 ≤ (t x).A g)
    (hAB : ∀ x (g : Fin (t x).q), (t x).A g < (t x).B g)
    (hBg : ∀ x (g : Fin (t x).q), (t x).B g < (t x).n + 1 + g) :
    ComputableInPolyTime (fun x => simPropWords (k x) (t x) (free x) (coins x) (t x).q)
      encIn (encList encBits) := by
  have hn := hd.fst'
  have hgates := hd.snd'.snd'
  have hinit : ComputableInPolyTime (fun x =>
      (List.range (t x).n).map (PointPermute.simLabel (k x) (coins x)))
      encIn (encList encBits) := by
    polytime [PointPermute.simLabel, BitString.listRow]
  have hgrowth : ComputableInPolyTime (fun x => 2 * (k x + 2) + 1) encIn encUnary := by
    polytime
  have hfold := ComputableInPolyTime.foldlWith_of_bounded_growth
    (encP := encPair encUnary (encPair encUnary (encPair encBits encBits)))
    (encL := encList (encPair encNat encNat)) (encB := encList encBits)
    (encA := encPair encNat encNat) (encIn := encIn)
    (step := fun par ws gate => simPropStep par.1 par.2.1 par.2.2.1 par.2.2.2 ws gate)
    (par := fun x => (k x, (t x).n, free x, coins x))
    (list := fun x => (t x).gateList)
    (init := fun x => (List.range (t x).n).map (PointPermute.simLabel (k x) (coins x)))
    (hk.prod (hn.prod (hfree.prod hcoins))) hgates hinit simPropStep_polyTime
    (growth := fun x => 2 * (k x + 2) + 1) (hgrowth.polyBounded_length.mono fun x => by simp)
    (fun x ws gate _ => by
      simp only [simPropStep, length_encList, List.map_append, List.sum_append, List.map_cons,
        List.map_nil, List.sum_cons, List.sum_nil, encBits_apply]
      split
      · simp only [List.length_take]; omega
      · simp [PointPermute.length_simLabel])
  have heq : (fun x => simPropWords (k x) (t x) (free x) (coins x) (t x).q) = fun x =>
      (t x).gateList.foldl (simPropStep (k x) (t x).n (free x) (coins x))
        ((List.range (t x).n).map (PointPermute.simLabel (k x) (coins x))) := by
    funext x
    rw [simPropWords_eq_foldl _ _ (hA x) (hAB x) (hBg x) _ _ le_rfl,
      List.take_of_length_le (Topo.length_gateList _).le]
  rw [heq]
  exact hfold

private theorem simPropWords_polyTime :
    ComputableInPolyTime (fun p : (ℕ × List Bool × XorTopology) × List Bool =>
        simPropWords p.1.1 p.1.2.2.topo.1 p.1.2.2.free p.2 p.1.2.2.topo.1.q)
      (encPair encSimInput encBits) (encList encBits) :=
  have hfst := ComputableInPolyTime.fst encSimInput encBits
  have hcoins := ComputableInPolyTime.snd encSimInput encBits
  simPropWords_polyTime_of ((ComputableInPolyTime.fst _ _).comp hfst) (simData_polyTime.comp hfst)
    (encXorTopology_free_polyTime ((ComputableInPolyTime.snd _ _).snd'.comp hfst)) hcoins
    (fun p g => p.1.2.2.topo.2.one_le_A g) (fun p g => p.1.2.2.topo.2.A_lt_B g)
    (fun p g => p.1.2.2.topo.2.B_lt_gate g)

/-- The number of non-XOR gates in the first `g` gates is computed in polynomial time. -/
theorem nonXorCount_polyTime {γ : Type} {encIn : γ ↪ List Bool}
    {free : γ → List Bool} {g : γ → ℕ}
    (hfree : ComputableInPolyTime free encIn encBits)
    (hg : ComputableInPolyTime g encIn encUnary) :
    ComputableInPolyTime (fun x => nonXorRank (free x) (g x)) encIn encUnary := by
  have heq : (fun x => nonXorRank (free x) (g x)) = fun x =>
      ((free x).take (g x)).countP fun b => !b :=
    funext fun x => nonXorRank_eq_countP (free x) (g x)
  rw [heq]
  have hcast : ComputableInPolyTime (fun l : List Bool => l) encBits (encList encBool) := by
    polytime
  exact ComputableInPolyTime.countPWithInput
    (hcast.comp (ComputableInPolyTime.bitsTakeWithInput hfree hg)) (by polytime)

private theorem simCoinLen_polyTime :
    ComputableInPolyTime (fun x : ℕ × List Bool × XorTopology => simCoinLen x.1 x.2.2)
      encSimInput encUnary := by
  have hk := ComputableInPolyTime.fst encUnary (encPair encBits encXorTopology)
  have hd := simData_polyTime
  have hn := hd.fst'
  have hq : ComputableInPolyTime (fun x : ℕ × List Bool × XorTopology => x.2.2.topo.1.q)
      encSimInput encUnary := by
    simpa only [Function.comp_def, Topo.length_gateList] using
      (ComputableInPolyTime.length_list _).comp hd.snd'.snd'
  have hfree : ComputableInPolyTime (fun x : ℕ × List Bool × XorTopology => x.2.2.free)
      encSimInput encBits :=
    encXorTopology_free_polyTime (ComputableInPolyTime.snd _ _).snd'
  have hc := nonXorCount_polyTime hfree hq
  have heq : (fun x : ℕ × List Bool × XorTopology => simCoinLen x.1 x.2.2) = fun x =>
      (x.2.2.topo.1.n + x.2.2.topo.1.q + 4 * nonXorRank x.2.2.free x.2.2.topo.1.q) *
        (x.1 + 2) := by
    funext x; rfl
  rw [heq]
  polytime

variable {hash : List Bool → List Bool → List Bool}
  (hf : ComputableInPolyTime (fun p : List Bool × List Bool => hash p.1 p.2)
    (encPair encBits encBits) encBits)

/-- Library infrastructure (no cited result): polynomial-time gate-row prefixing shared between
the Free-XOR simulator and CCR reduction. -/
theorem rowData_polyTime {γ : Type} {encIn : γ ↪ List Bool}
    {g i : γ → ℕ} {free body : γ → List Bool}
    (hfree : ComputableInPolyTime free encIn encBits)
    (hg : ComputableInPolyTime g encIn encUnary)
    (hi : ComputableInPolyTime i encIn encUnary)
    (hbody : ComputableInPolyTime body encIn encBits) :
    ComputableInPolyTime (fun x =>
      (if i x = 0 then [(free x).getD (g x) false] else []) ++
        if (free x).getD (g x) false then [] else body x) encIn encBits := by
  polytime

attribute [local fun_prop] PointPermute.simLabel_polyTime

include hf in
private theorem simRowData_polyTime {γ : Type} {encIn : γ ↪ List Bool}
    {k n q g a b i : γ → ℕ} {free coins : γ → List Bool} {labels : γ → List (List Bool)}
    (hk : ComputableInPolyTime k encIn encUnary) (hn : ComputableInPolyTime n encIn encUnary)
    (hq : ComputableInPolyTime q encIn encUnary) (hfree : ComputableInPolyTime free encIn encBits)
    (hlabels : ComputableInPolyTime labels encIn (encList encBits))
    (hcoins : ComputableInPolyTime coins encIn encBits)
    (hg : ComputableInPolyTime g encIn encUnary) (ha : ComputableInPolyTime a encIn encUnary)
    (hb : ComputableInPolyTime b encIn encUnary) (hi : ComputableInPolyTime i encIn encUnary) :
    ComputableInPolyTime (fun x => simRowData hash (k x) (n x) (q x) (free x) (labels x)
      (coins x) (g x) (a x) (b x) (i x)) encIn encBits := by
  have hla := ComputableInPolyTime.listGetDWithInput hlabels ha []
  have hlb := ComputableInPolyTime.listGetDWithInput hlabels hb []
  have hm₀ := keyHashWord_polyTime hf hk hla
    (PointPermute.tweak_polyTime hk hg hi (ComputableInPolyTime.const 0))
  have hm₁ := keyHashWord_polyTime hf hk hlb
    (PointPermute.tweak_polyTime hk hg hi (ComputableInPolyTime.const 1))
  have hrank := nonXorCount_polyTime hfree hg
  have hbody : ComputableInPolyTime (fun x =>
      let la := (labels x).getD (a x) []
      let lb := (labels x).getD (b x) []
      let idx := (if HalfGates.colourWord (k x) la then 2 else 0) +
        (if HalfGates.colourWord (k x) lb then 1 else 0)
      if i x = idx then
        List.zipWith xor ((labels x).getD (n x + g x) [])
          (List.zipWith xor (keyHashWord hash (k x) la (PointPermute.tweak (k x) (g x) (i x) 0))
            (keyHashWord hash (k x) lb (PointPermute.tweak (k x) (g x) (i x) 1)))
      else PointPermute.simLabel (k x) (coins x)
        (n x + q x + 4 * nonXorRank (free x) (g x) + i x)) encIn encBits := by
    polytime [HalfGates.colourWord]
  exact rowData_polyTime hfree hg hi hbody

include hf in
private theorem simViewWord_polyTime :
    ComputableInPolyTime (fun p : (ℕ × List Bool × XorTopology) × List Bool =>
      simViewWord hash p.1.1 p.1.2.1 p.1.2.2 p.2) (encPair encSimInput encBits) encPrvView := by
  have hfst := ComputableInPolyTime.fst encSimInput encBits
  have hcoins := ComputableInPolyTime.snd encSimInput encBits
  have hk := hfst.fst'
  have hy := hfst.snd'.fst'
  have hd := simData_polyTime.comp hfst
  have hn := hd.fst'
  have hm := hd.snd'.fst'
  have hgates := hd.snd'.snd'
  have hq := (ComputableInPolyTime.length_list _).comp hgates
  have hfree := encXorTopology_free_polyTime hfst.snd'.snd'
  have hP := simPropWords_polyTime
  have hq_val : ComputableInPolyTime (fun p : (ℕ × List Bool × XorTopology) × List Bool =>
      p.1.2.2.topo.1.q) (encPair encSimInput encBits) encUnary := by
    simpa only [Function.comp_def, Topo.length_gateList] using hq
  have hcap := ComputableInPolyTime.unary_add' ((ComputableInPolyTime.length_list _).comp hP)
    (ComputableInPolyTime.const 1)
  have hx := ComputableInPolyTime.fst (encPair encSimInput encBits)
    (encPair encUnary (encPair encUnary (encPair encUnary encUnary)))
  have hrest := ComputableInPolyTime.snd (encPair encSimInput encBits)
    (encPair encUnary (encPair encUnary (encPair encUnary encUnary)))
  have hrow := simRowData_polyTime hf (hk.comp hx) (hn.comp hx) (hq_val.comp hx)
    (hfree.comp hx) (hP.comp hx) (hcoins.comp hx) hrest.fst' hrest.snd'.fst' hrest.snd'.snd'.fst'
    hrest.snd'.snd'.snd'
  have hgate := ComputableInPolyTime.listGetDWithInput
    (hgates.comp (ComputableInPolyTime.fst (encPair encSimInput encBits) encUnary))
    (ComputableInPolyTime.snd _ _) (0, 0)
  have hbody := PointPermute.bodyWith_polyTime
    (n := fun p : (ℕ × List Bool × XorTopology) × List Bool => p.1.2.2.topo.1.n)
    (q := fun p => p.1.2.2.topo.1.gateList.length)
    (cap := fun p =>
      (simPropWords p.1.1 p.1.2.2.topo.1 p.1.2.2.free p.2 p.1.2.2.topo.1.q).length + 1)
    (A := fun p g => (p.1.2.2.topo.1.gateList.getD g (0, 0)).1)
    (B := fun p g => (p.1.2.2.topo.1.gateList.getD g (0, 0)).2)
    (row := fun p g a b i => simRowData hash p.1.1 p.1.2.2.topo.1.n p.1.2.2.topo.1.q
      p.1.2.2.free (simPropWords p.1.1 p.1.2.2.topo.1 p.1.2.2.free p.2 p.1.2.2.topo.1.q) p.2
      g a b i)
    hn hq hcap hgate.fst' hgate.snd' (by convert hrow using 2; rcases ‹_› with ⟨_, _, _, _, _⟩; rfl)
  have henc : ComputableInPolyTime (fun z : (ℕ × ℕ × ℕ × ℕ) × List Bool => PointPermute.encFn z)
      PointPermute.encFn encBits := .of_eq fun _ => rfl
  have hF := henc.comp ((hk.prod (hn.prod (hm.prod hq))).prod hbody)
  have hX : ComputableInPolyTime (fun p : (ℕ × List Bool × XorTopology) × List Bool =>
      ((List.range p.1.2.2.topo.1.n).map (PointPermute.simLabel p.1.1 p.2)).flatten)
      (encPair encSimInput encBits) encBits := by
    polytime [PointPermute.simLabel, BitString.listRow]
  have hdecRange : ComputableInPolyTime (fun p : ℕ × List Bool × ℕ × ℕ × List (List Bool) =>
      (List.range p.2.2.1).map fun o => HalfGates.colourWord p.1
        (p.2.2.2.2.getD (p.2.2.2.1 + o) []) ^^ p.2.1.getD o false)
      (encPair encUnary (encPair encBits (encPair encUnary (encPair encUnary (encList encBits)))))
      encBits := by
    polytime [HalfGates.colourWord]
  have hdecOff := ComputableInPolyTime.unary_sub' (ComputableInPolyTime.unary_add' hn hq) hm
  have hdec := hdecRange.comp (hk.prod (hy.prod (hm.prod (hdecOff.prod hP))))
  simp only [simViewWord_eq_data]
  exact encPrvView_mk_polyTime hF hX hdec

include hf in
/-- **The simulator is PPT** whenever the hash family is computed in polynomial time. -/
theorem isPPTOn_simWord :
    IsPPTOn (encPair encUnary (encPair encBits encXorTopology)) encPrvView
      (fun (k, y, t) => simWord hash k y t) := by
  have h : IsPPTOn encSimInput encPrvView (fun x : ℕ × List Bool × XorTopology => do
      let coins ← BitString.sampleList (simCoinLen x.1 x.2.2)
      pure (simViewWord hash x.1 x.2.1 x.2.2 coins)) :=
    (isPPTOn_sampleList.preprocess simCoinLen_polyTime).bind_with
      (simViewWord_polyTime hf).isPPTOn
  refine h.congr ?_
  rintro ⟨k, y, t⟩
  rfl

end Efficiency

end Cslib.Crypto.Garbling.FreeXOR
