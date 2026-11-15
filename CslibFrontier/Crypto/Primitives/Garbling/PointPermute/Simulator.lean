/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.Garbling.PointPermute
public import CslibFrontier.Crypto.Primitives.Garbling.Privacy
public import CslibFrontier.Crypto.Primitives.Garbling.Games
import CslibFrontier.Probability.BitString.List

/-!
# The simulator of point-and-permute garbling

The privacy simulator of `CslibFrontier.Crypto.Primitives.Garbling.Privacy` written on words, for
the point-and-permute scheme `PointPermute.scheme family` with topology side information
(`phiTopo`). The simulator `simWord family k y t` sees the parameter `k`, the output `y` and the
topology `t = (n, m, q, A, B)`. It samples one `(k + 2)`-bit label for each of the `n + q` wires
and four filler labels for each gate, and writes the view `(F, X, d)` (`simViewWord`): in each
gate's table, the row named by the colours of its argument wires' labels holds the gate's label
masked under their keys, and every other row holds a filler label; `X` lists the input wires'
labels, and `d` makes the output wires' colours decode to `y`.

The words written are those of the typed simulator `simulateWith` on `toCircuit f`, for every
valid circuit `f` of topology `t`, with the labels read from the coins (`simViewWord_eq`), and the
coins give uniform wire labels and filler rows (`uniformList_map_simCoins`). So the simulator's
output law is the typed simulator's (`eval_simWord`). Every simulated view decodes to the output
(`decodeWord_evalWord_simViewWord`).

## Main definitions

* `Cslib.Crypto.Garbling.PointPermute.viewWord`: the words `(F, X, d)` of a typed view.
* `Cslib.Crypto.Garbling.PointPermute.simViewWord`, `Cslib.Crypto.Garbling.PointPermute.simWord`:
  the simulated view on given coins, and the simulator.

## Main results

* `Cslib.Crypto.Garbling.PointPermute.eval_simWord`: the simulator samples the words of the
  typed simulator's view.
* `Cslib.Crypto.Garbling.PointPermute.decodeWord_evalWord_simViewWord`: simulated views decode to
  the output.

## References

* [M. Bellare, V. T. Hoang, P. Rogaway, *Foundations of Garbled Circuits*][BellareHoangRogaway2012]
-/

public section

namespace Cslib.Crypto.Garbling.PointPermute

open Cslib.Circuits Probability ConventionalCircuit

/-! ### Labels as bit strings -/

/-- A label as a `(k + 2)`-bit string: the `k + 1` bits of its key, then its colour. -/
@[expose] def labelEquiv (k : ℕ) : BitString (k + 2) ≃ BitString (k + 1) × Bool where
  toFun bits := (Fin.init bits, bits (Fin.last _))
  invFun label := Fin.snoc label.1 label.2
  left_inv bits := Fin.snoc_init_self bits
  right_inv label := by simp

/-- The word of the label of a bit string is the bit string. -/
theorem labelBits_labelEquiv {k : ℕ} (bits : BitString (k + 2)) :
    labelBits (labelEquiv k bits) = List.ofFn bits := by
  simp only [labelBits, labelEquiv, Equiv.coe_fn_mk]
  rw [List.ofFn_succ' bits, List.concat_eq_append]
  rfl

/-- The label of a `(k + 2)`-bit word. -/
@[expose] def labelOfWord (k : ℕ) (word : List Bool) : BitString (k + 1) × Bool :=
  labelEquiv k (BitString.ofList (k + 2) word)

/-- The label of a `(k + 2)`-bit word has that word. -/
theorem labelBits_labelOfWord {k : ℕ} {word : List Bool} (hword : word.length = k + 2) :
    labelBits (labelOfWord k word) = word := by
  rw [labelOfWord, labelBits_labelEquiv, BitString.ofFn_ofList hword]

/-- The key of the label of a `(k + 2)`-bit word is its first `k + 1` bits. -/
theorem ofFn_labelOfWord_fst {k : ℕ} {word : List Bool} (hword : word.length = k + 2) :
    List.ofFn (labelOfWord k word).1 = word.take (k + 1) := by
  rw [← take_labelBits, labelBits_labelOfWord hword]

/-- The colour of the label of a word is its bit `k + 1`. -/
theorem labelOfWord_snd (k : ℕ) (word : List Bool) :
    (labelOfWord k word).2 = word.getD (k + 1) false := rfl

/-! ### The simulator's coins -/

/-- The number of coins of the simulator at parameter `k` for `n` inputs and `q` gates: one label
for each of the `n + q` wires, then four filler labels for each gate. -/
@[expose] def simCoinLen (k n q : ℕ) : ℕ := (n + q + q * 4) * (k + 2)

/-- Label `v` of the simulator's coins, their `(k + 2)`-bit block `v`. Wire `v` has label `v`;
row `i` of gate `g` has filler label `n + q + 4 g + i`. -/
@[expose] def simLabel (k : ℕ) (coins : List Bool) (v : ℕ) : List Bool :=
  BitString.listRow (k + 2) v coins

@[simp] theorem length_simLabel (k : ℕ) (coins : List Bool) (v : ℕ) :
    (simLabel k coins v).length = k + 2 :=
  BitString.length_listRow _ _ _

variable {n m s : ℕ}

/-- The wire labels read from the simulator's coins: wire `w` has label number `w`. -/
@[expose] def simWireLabels (k : ℕ) (coins : List Bool) (w : Wire n s) :
    BitString (k + 1) × Bool :=
  labelOfWord k (simLabel k coins w.toNat)

/-- The filler rows read from the simulator's coins: row `ρ` of gate `g` has label number
`n + s + 4 g + rowIndex ρ`. -/
@[expose] def simFillerRows (k : ℕ) (τ : Circuit.Topology n m s) (coins : List Bool)
    (r : Row τ) : BitString (k + 1) × Bool :=
  labelOfWord k (simLabel k coins (n + s + 4 * r.1 + rowIndex r.2))

/-- A row of a binary gate has number below `4`. -/
theorem rowIndex_lt_four {r : ℕ} (hr : r = 2) (colours : Fin r → Bool) : rowIndex colours < 4 := by
  rw [rowIndex_of_eq_two hr]
  split_ifs <;> omega

/-- The position of each wire's label and each row's filler label among the simulator's coins. -/
private def simIndex (τ : Circuit.Topology n m s) (hτ : ∀ g, τ.arity g = 2) :
    Wire n s ⊕ Row τ → Fin (n + s + s * 4)
  | .inl w => ⟨w.toNat, by have := w.toNat_lt; omega⟩
  | .inr r => ⟨n + s + 4 * r.1 + rowIndex r.2, by
      have := rowIndex_lt_four (hτ r.1) r.2
      have := r.1.isLt
      omega⟩

private theorem simIndex_bijective (τ : Circuit.Topology n m s) (hτ : ∀ g, τ.arity g = 2) :
    Function.Bijective (simIndex τ hτ) := by
  refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨?_, ?_⟩
  · rintro (w | ⟨g, ρ⟩) (w' | ⟨g', ρ'⟩) h <;> simp only [simIndex, Fin.mk.injEq] at h
    · exact congrArg Sum.inl (Wire.toNat_injective h)
    · have := w.toNat_lt; omega
    · have := w'.toNat_lt; omega
    · have hi := rowIndex_lt_four (hτ g) ρ
      have hi' := rowIndex_lt_four (hτ g') ρ'
      have hg : g = g' := Fin.ext (by omega)
      subst hg
      have hρ : rowIndex ρ = rowIndex ρ' := by omega
      have : ρ = ρ' := by
        rw [← testBit_rowIndex_of_eq_two (hτ g) ρ, ← testBit_rowIndex_of_eq_two (hτ g) ρ', hρ]
      subst this
      rfl
  · rw [Fintype.card_sum, Fintype.card_congr (Wire.equivFin n s), Fintype.card_fin,
      Fintype.card_sigma]
    simp [hτ, Finset.sum_const, Finset.card_univ]

/-- **The simulator's coins are uniform labels.** For a topology of binary gates, the wire labels
and filler rows read from uniform coins are uniform and independent. -/
theorem uniformList_map_simCoins (k : ℕ) (τ : Circuit.Topology n m s)
    (hτ : ∀ g, τ.arity g = 2) :
    (BitString.uniformList (simCoinLen k n s)).map
        (fun coins => ((simWireLabels k coins : Wire n s → _), simFillerRows k τ coins)) =
      PMF.uniformOfFintype
        ((Wire n s → BitString (k + 1) × Bool) × (Row τ → BitString (k + 1) × Bool)) := by
  let e := Equiv.ofBijective _ (simIndex_bijective τ hτ)
  let E : (Wire n s ⊕ Row τ → BitString (k + 2)) ≃
      (Wire n s → BitString (k + 1) × Bool) × (Row τ → BitString (k + 1) × Bool) :=
    (Equiv.sumArrowEquivProdArrow _ _ _).trans (Equiv.prodCongr
      (Equiv.arrowCongr (Equiv.refl _) (labelEquiv k))
      (Equiv.arrowCongr (Equiv.refl _) (labelEquiv k)))
  have h : (fun coins => ((simWireLabels k coins : Wire n s → _), simFillerRows k τ coins)) =
      (E : _ → _) ∘
        fun coins i => BitString.ofList (k + 2) (BitString.listRow (k + 2) (e i) coins) := by
    funext coins
    rfl
  rw [h, ← PMF.map_comp, simCoinLen, BitString.uniformList_map_listRow_equiv e (k + 2)]
  exact PMF.uniformOfFintype_map_equiv E

/-! ### The simulated view -/

variable (family : List Bool → List Bool → List Bool)

/-- Row `i` of gate `g` of the simulated garbled function at parameter `k` for the topology `t`:
the row named by the colours of the labels of the gate's argument wires holds the gate's label
masked by the keyed function at their keys; every other row holds its filler label. -/
@[expose] def simRow (k : ℕ) (t : Topo) (coins : List Bool) (g : Fin t.q) (i : ℕ) : List Bool :=
  let la := simLabel k coins (t.A g - 1)
  let lb := simLabel k coins (t.B g - 1)
  if i = (if la.getD (k + 1) false then 2 else 0) + (if lb.getD (k + 1) false then 1 else 0) then
    List.zipWith xor (simLabel k coins (t.n + g))
      (List.zipWith xor (labelWord family k (la.take (k + 1)) (tweak k g i 0))
        (labelWord family k (lb.take (k + 1)) (tweak k g i 1)))
  else simLabel k coins (t.n + t.q + 4 * g + i)

/-- The simulated view `(F, X, d)` at parameter `k` for the output `y` and the topology `t`, on the
simulator's coins: the garbled function with the header and wire numbers of `t` and the rows
`simRow`, the labels of the input wires, and the decoding bits that make the colours of the output
wires' labels decode to `y`. -/
@[expose] def simViewWord (k : ℕ) (y : List Bool) (t : Topo) (coins : List Bool) : PrvView where
  fn := encFn ((k, t.n, t.m, t.q), (List.ofFn fun g : Fin t.q =>
    BitString.lowBits (wireWidth t.n t.q) (t.A g) ++
      BitString.lowBits (wireWidth t.n t.q) (t.B g) ++
      (List.ofFn fun i : Fin 4 => simRow family k t coins g i).flatten).flatten)
  input := (List.ofFn fun i : Fin t.n => simLabel k coins i).flatten
  decInfo := List.ofFn fun o : Fin t.m =>
    (simLabel k coins (t.n + t.q - t.m + o)).getD (k + 1) false ^^ y.getD o false

/-- **The simulator** `S(1^k, y, φ)` of point-and-permute garbling with topology side information:
sample the coins and write the simulated view. -/
noncomputable def simWord (k : ℕ) (y : List Bool) (t : ValidTopo) : ProbComp PrvView := do
  let coins ← BitString.sampleList (simCoinLen k t.1.n t.1.q)
  return simViewWord family k y t.1 coins

/-- The words `(F, X, d)` of a typed view at parameter `k`: the garbled function of its table, the
words of its input labels in order, and its decoding bits. -/
@[expose] def viewWord (k : ℕ) (τ : Circuit.Topology n m s) (V : View τ (BitString (k + 1))) :
    PrvView where
  fn := encodeFn k τ V.table
  input := (List.ofFn fun i => labelBits (V.input i)).flatten
  decInfo := List.ofFn V.decoding

/-! ### The simulated view is the typed simulator's -/

/-- Row `i < 4` of a binary gate has number `i`. -/
private theorem rowIndex_testBit_of_eq_two {r i : ℕ} (hr : r = 2) (hi : i < 4) :
    rowIndex (fun a : Fin r => i.testBit (r - 1 - a)) = i := by
  subst hr
  exact rowIndex_testBit hi

/-- Row `i < 4` of a binary gate has the colours `colours` exactly when `i` is their number. -/
private theorem testBit_eq_iff_of_eq_two {r i : ℕ} (hr : r = 2) (hi : i < 4)
    (colours : Fin r → Bool) :
    (fun a : Fin r => i.testBit (r - 1 - a)) = colours ↔ i = rowIndex colours := by
  constructor
  · rintro rfl
    exact (rowIndex_testBit_of_eq_two hr hi).symm
  · rintro rfl
    exact testBit_rowIndex_of_eq_two hr colours

/-- Row `i` of gate `g` of the typed simulated table, as a word, is `simRow`. -/
private theorem labelBits_simulateWith (k : ℕ) (f : ValidCircuit) (y : Fin f.1.m → Bool)
    (coins : List Bool) (g : Fin (toCircuit f).size) {i : ℕ} (hi : i < 4) :
    labelBits ((simulateWith (toCircuit f).topology (PRF.label (PRF.atLevel family (k + 1)))
        (slotTweak _ k) y (simWireLabels k coins) (simFillerRows k _ coins)).table
          (rowOf _ g i)) =
      simRow family k f.1.topo coins (g.cast (size_toCircuit f)) i := by
  have harity := arity_topology_toCircuit f g
  have hw₀ : ((toCircuit f).topology.wires g ⟨0, by omega⟩).toNat =
      f.1.A (g.cast (size_toCircuit f)) - 1 := by
    rw [toNat_wires_toCircuit]; rfl
  have hw₁ : ((toCircuit f).topology.wires g ⟨1, by omega⟩).toNat =
      f.1.B (g.cast (size_toCircuit f)) - 1 := by
    rw [toNat_wires_toCircuit]; rfl
  simp only [simulateWith, rowOf, simFillerRows, slotTweak]
  simp only [rowIndex_testBit_of_eq_two harity hi]
  simp only [testBit_eq_iff_of_eq_two harity hi, rowIndex_of_eq_two harity]
  rw [← Fin.sum_congr' _ harity.symm, Fin.sum_univ_two]
  have hc₀ : (Fin.cast harity.symm 0 : Fin ((toCircuit f).topology.arity g)) = ⟨0, by omega⟩ :=
    Fin.ext rfl
  have hc₁ : (Fin.cast harity.symm 1 : Fin ((toCircuit f).topology.arity g)) = ⟨1, by omega⟩ :=
    Fin.ext rfl
  simp only [hc₀, hc₁, simRow, topo, simWireLabels, labelOfWord_snd, hw₀, hw₁, Wire.toNat_gate,
    Fin.val_cast]
  rw [apply_ite labelBits]
  refine ite_congr rfl (fun _ => ?_) (fun _ => ?_)
  · rw [labelBits_add, labelBits_add, ← labelWord_ofFn, ← labelWord_ofFn, ofFn_ofList_tweak,
      ofFn_ofList_tweak, labelBits_labelOfWord (length_simLabel _ _ _),
      ofFn_labelOfWord_fst (length_simLabel _ _ _), ofFn_labelOfWord_fst (length_simLabel _ _ _)]
  · have hq : f.1.n + (toCircuit f).size = f.1.n + f.1.q := by rw [size_toCircuit]
    rw [labelBits_labelOfWord (length_simLabel _ _ _), hq]

/-- Gate `g` of the garbled function of a table `T` over `toCircuit f`, as a word: the numbers of
its argument wires `A g` and `B g` and its four rows. -/
theorem gateWord_toCircuit (k : ℕ) (f : ValidCircuit)
    (T : Row (toCircuit f).topology → BitString (k + 1) × Bool) (g : Fin (toCircuit f).size) :
    ((List.ofFn fun a => BitString.lowBits (wireWidth f.1.n (toCircuit f).size)
        (((toCircuit f).topology.wires g a).toNat + 1)).flatten ++
      (List.ofFn fun i : Fin (2 ^ (toCircuit f).topology.arity g) =>
        labelBits (T (rowOf _ g i))).flatten) =
      BitString.lowBits (wireWidth f.1.n f.1.q) (f.1.A (g.cast (size_toCircuit f))) ++
        BitString.lowBits (wireWidth f.1.n f.1.q) (f.1.B (g.cast (size_toCircuit f))) ++
        (List.ofFn fun i : Fin 4 => labelBits (T (rowOf _ g i))).flatten := by
  have hA := f.2.one_le_A (g.cast (size_toCircuit f))
  have hB := f.2.A_lt_B (g.cast (size_toCircuit f))
  simp only [topo] at hA hB
  have hw : wireWidth f.1.n (toCircuit f).size = wireWidth f.1.n f.1.q := by rw [size_toCircuit]
  have hwires : (List.ofFn fun a => BitString.lowBits (wireWidth f.1.n f.1.q)
      (((toCircuit f).topology.wires g a).toNat + 1)) =
      (List.ofFn fun a => ((toCircuit f).topology.wires g a).toNat).map
        (fun v => BitString.lowBits (wireWidth f.1.n f.1.q) (v + 1)) := by
    rw [List.map_ofFn]; rfl
  have hrows := List.ofFn_congr (show 2 ^ (toCircuit f).topology.arity g = 4 by
    rw [arity_topology_toCircuit]; rfl) (fun i => labelBits (T (rowOf _ g i)))
  rw [hw, hwires, ofFn_toNat_wires_toCircuit, hrows]
  simp [Nat.sub_add_cancel hA, Nat.sub_add_cancel (hA.trans hB.le)]

/-- **The simulated view is the typed simulator's.** For every valid circuit `f`, the simulated
view for the topology of `f` and the output `y` is the words of the typed simulated view of
`toCircuit f`, with the wire labels and filler rows read from the coins. -/
theorem simViewWord_eq (k : ℕ) (f : ValidCircuit) (y coins : List Bool) :
    simViewWord family k y f.1.topo coins = viewWord k (toCircuit f).topology
      (simulateWith (toCircuit f).topology (PRF.label (PRF.atLevel family (k + 1)))
        (slotTweak _ k) (BitString.ofList f.1.m y) (simWireLabels k coins)
        (simFillerRows k _ coins)) := by
  have hrow : ∀ (g : Fin (toCircuit f).size) (i : Fin 4),
      labelBits ((simulateWith (toCircuit f).topology (PRF.label (PRF.atLevel family (k + 1)))
        (slotTweak _ k) (BitString.ofList f.1.m y) (simWireLabels k coins)
        (simFillerRows k _ coins)).table (rowOf _ g i)) =
      simRow family k f.1.topo coins (g.cast (size_toCircuit f)) i :=
    fun g i => labelBits_simulateWith family k f _ coins g i.isLt
  simp only [simViewWord, viewWord, encodeFn, encodeBody, PrvView.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · simp only [gateWord_toCircuit, hrow]
    congr 2
    · simp only [topo, size_toCircuit]
    · simp only [topo]
      rw [List.ofFn_congr (size_toCircuit f)]
      rfl
  · simp only [simulateWith, simWireLabels, labelBits_labelOfWord (length_simLabel _ _ _),
      Wire.toNat_input, topo]
  · apply List.ext_getElem (by simp [topo])
    intro o h₁ h₂
    have ho := toNat_outputs_toCircuit f ⟨o, by simpa using h₂⟩
    simp only [List.getElem_ofFn, simulateWith, simWireLabels, labelOfWord_snd, Circuit.topology,
      ho, BitString.ofList, Bool.add_eq_xor, topo]

/-- **The simulator samples the typed simulator's view.** For every valid circuit `f` and output
`y`, the simulator on the topology of `f` samples the words of the typed simulator's view of
`toCircuit f`. -/
theorem eval_simWord (k : ℕ) (f : ValidCircuit) (y : List Bool) :
    ProbComp.eval (simWord family k y (phiTopo.phi f)) =
      (ProbComp.eval (simulate (toCircuit f).topology (PRF.label (PRF.atLevel family (k + 1)))
        (slotTweak _ k) (BitString.ofList f.1.m y))).map (viewWord k _) := by
  have hcoins : simCoinLen k f.1.n f.1.q = simCoinLen k f.1.n (toCircuit f).size := by
    rw [size_toCircuit]
  have hsim := uniformList_map_simCoins k (toCircuit f).topology (arity_topology_toCircuit f)
  have hview : simViewWord family k y f.1.topo =
      (fun p : (Wire f.1.n (toCircuit f).size → BitString (k + 1) × Bool) ×
          (Row (toCircuit f).topology → BitString (k + 1) × Bool) =>
        viewWord k _ (simulateWith (toCircuit f).topology (PRF.label (PRF.atLevel family (k + 1)))
          (slotTweak _ k) (BitString.ofList f.1.m y) p.1 p.2)) ∘
        (fun coins => (simWireLabels k coins, simFillerRows k _ coins)) :=
    funext fun coins => simViewWord_eq family k f y coins
  change ProbComp.eval (do
      let coins ← BitString.sampleList (simCoinLen k f.1.n f.1.q)
      return simViewWord family k y f.1.topo coins) = _
  have hmap : ∀ {α β : Type} (p : PMF α) (g : α → β), p.bind (fun a => PMF.pure (g a)) = p.map g :=
    fun p g => PMF.bind_pure_comp g p
  simp only [simulate, ProbComp.eval_bind, ProbComp.eval_pure, ProbComp.eval_uniform,
    BitString.eval_sampleList, hcoins, hmap]
  rw [hview, ← PMF.map_comp, hsim, ← Cslib.Probability.PMF.uniformOfFintype_prod]
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]

end Cslib.Crypto.Garbling.PointPermute
