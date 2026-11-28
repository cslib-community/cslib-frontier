/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.Garbling.PointPermute.Simulator
public import CslibFrontier.Languages.Probabilistic.UniformNat
import CslibFrontier.Probability.BitString.List
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Tactic.UniformRelabel
import CslibFrontier.Crypto.Game.Hybrid
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.UniformNat
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Tactic.PolyTime
import CslibFrontier.Foundations.Data.List.Lookup

/-!
# The PRF reduction for the privacy of point-and-permute garbling

The `prv.sim` advantage of an adversary `B` against the simulator `simWord` of
`PointPermute.scheme family`, with topology side information, is exactly a step range times the
label advantage of an explicit, certified reduction (`prvSimAdvantage_simWord_eq`).

The proof is a hybrid over the wires. The garbler's coins give uniform keys and permutation bits,
so the real view of a query `(f, x)` is the typed real view of `toCircuit f` written as words; the
simulated view is the typed simulated view (`eval_simWord`). Hybrid view `j` on words is the typed
hybrid view `j` of `Privacy.lean`, and global hybrid `i` runs `B`'s choice and then hybrid `i` of
its circuit.

The reduction `prvSimReduction family B P` runs `B`'s choice of `(f, x)`, draws a step `j` below
`dyadicSize (P k)`, the garbler's coins and filler labels, asks its label oracle at the tweaks of
all `8 q` argument slots, and runs `B`'s guess on hybrid view `j` with the answers in the target
slots. Against any table it runs the typed reductions of `Privacy.lean`
(`eval_run_prvSimReduction`), so against the keyed label function it plays a uniform global hybrid
`j`, and against a random function global hybrid `j + 1` when distinct slots have distinct tweaks,
which holds while `8 q ≤ 2 ^ k`. When `P k` bounds the wires of every circuit `B` chooses, the
hybrids telescope (`Game.advantage_hybrid_average`). The reduction is uniform strict oracle PPT for
every adversary certified by `TwoStage.IsPPT` and every polynomial-time family
(`isOraclePPT_prvSimReduction`); the body of its hybrid view is written by `bodyWith`, whose
certificate it shares with the garbler and the simulator.

## Main definitions

* `Cslib.Crypto.Garbling.PointPermute.prvSimReduction`: the PRF reduction.

## Main results

* `Cslib.Crypto.Garbling.PointPermute.prvSimAdvantage_simWord_eq`: the `prv.sim` advantage is the
  step range times the reduction's label advantage.
* `Cslib.Crypto.Garbling.PointPermute.isOraclePPT_prvSimReduction`: the reduction is oracle PPT.

## References

* [M. Bellare, V. T. Hoang, P. Rogaway, *Foundations of Garbled Circuits*][BellareHoangRogaway2012]
-/

public section

namespace Cslib.Crypto.Garbling.PointPermute

open Cslib.Circuits Probability ConventionalCircuit

variable {n m s : ℕ}

/-! ### The garbler's coins -/

/-- The position of the key of colour `c` of wire `w` among the keys of the garbler's coins. -/
private def keyIndex (w : Wire n s) (c : Bool) : Fin ((n + s) * 2) :=
  ⟨2 * w.toNat + (if c then 1 else 0), by have := w.toNat_lt; split <;> omega⟩

private theorem keyIndex_bijective :
    Function.Bijective (fun p : Wire n s × Bool => keyIndex p.1 p.2) := by
  refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨?_, ?_⟩
  · rintro ⟨w, c⟩ ⟨w', c'⟩ h
    have h' : 2 * w.toNat + (if c then 1 else 0) = 2 * w'.toNat + (if c' then 1 else 0) :=
      congrArg Fin.val h
    have hc : c = c' := by cases c <;> cases c' <;> simp at h' ⊢ <;> omega
    subst hc
    have hw : w.toNat = w'.toNat := by cases c <;> simp at h' <;> omega
    rw [Wire.toNat_injective hw]
  · rw [Fintype.card_prod, Fintype.card_congr (Wire.equivFin n s), Fintype.card_fin,
      Fintype.card_bool, Fintype.card_fin]

/-- **The garbler's coins are uniform keys and permutation bits.** Reading the permutation bit of
each wire and the key of each colour of each wire from uniform coins of the scheme's length gives
uniform and independent keys and permutation bits. -/
private theorem uniformList_map_keyFn_permFn (k n s : ℕ) :
    (BitString.uniformList ((n + s) * (2 * (k + 1) + 1))).map
        (fun coins => ((keyFn k coins : Wire n s × Bool → BitString (k + 1)),
          (permFn coins : Wire n s → Bool))) =
      PMF.uniformOfFintype ((Wire n s × Bool → BitString (k + 1)) × (Wire n s → Bool)) := by
  let keys : List Bool → Wire n s × Bool → BitString (k + 1) := fun back p =>
    BitString.ofList (k + 1) (BitString.listRow (k + 1) (keyIndex p.1 p.2) back)
  let perms : List Bool → Wire n s → Bool := fun front w =>
    BitString.ofList 1 (BitString.listRow 1 w.toNat front) 0
  have hkeys : (BitString.uniformList ((n + s) * 2 * (k + 1))).map keys =
      PMF.uniformOfFintype (Wire n s × Bool → BitString (k + 1)) :=
    BitString.uniformList_map_listRow_equiv (Equiv.ofBijective _ keyIndex_bijective) (k + 1)
  have hperms : (BitString.uniformList (n + s)).map perms =
      PMF.uniformOfFintype (Wire n s → Bool) := by
    have h := BitString.uniformList_map_listRow_equiv (Wire.equivFin n s) 1
    rw [mul_one] at h
    have hcomp : perms = ((Equiv.arrowCongr (Equiv.refl (Wire n s))
        (Equiv.funUnique (Fin 1) Bool)) : _ → _) ∘
          fun word i => BitString.ofList 1 (BitString.listRow 1 (Wire.equivFin n s i) word) := rfl
    rw [hcomp, ← PMF.map_comp, h, PMF.uniformOfFintype_map_equiv]
  have hsplit : ∀ front, front.length = n + s → ∀ back : List Bool,
      ((keyFn k (front ++ back) : Wire n s × Bool → BitString (k + 1)),
        (permFn (front ++ back) : Wire n s → Bool)) = (keys back, perms front) := by
    intro front hfront back
    refine Prod.ext (funext fun ⟨w, c⟩ => ?_) (funext fun w => ?_)
    · simp only [keyFn, keyOf, keys, keyIndex, ← hfront, List.drop_left]
      congr 2
      cases c <;> simp
    · have hw := w.toNat_lt
      simp only [permFn, permOf, perms, BitString.ofList]
      rw [BitString.getD_listRow (by omega), List.getD_eq_getElem?_getD,
        List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega)]
      simp
  rw [show (n + s) * (2 * (k + 1) + 1) = (n + s) + (n + s) * 2 * (k + 1) by ring,
    BitString.uniformList_add, PMF.map_bind]
  calc _ = (BitString.uniformList (n + s)).bind (fun front =>
          (BitString.uniformList ((n + s) * 2 * (k + 1))).map fun back =>
            (keys back, perms front)) := by
        refine Probability.PMF.bind_congr_on_support _ _ _ fun front hfront => ?_
        rw [PMF.map_comp]
        congr 1
        funext back
        exact hsplit front (BitString.length_of_mem_support_uniformList hfront) back
    _ = ((PMF.uniformOfFintype (Wire n s → Bool)).bind fun perm =>
          (PMF.uniformOfFintype (Wire n s × Bool → BitString (k + 1))).map fun key =>
            (key, perm)) := by
        rw [← hperms, ← hkeys, PMF.bind_map]
        simp only [PMF.map_comp, Function.comp_def]
    _ = _ := by
        relabel_uniform (Equiv.prodComm (Wire n s → Bool)
          (Wire n s × Bool → BitString (k + 1)))

variable (family : List Bool → List Bool → List Bool)

/-- The real view on given coins is the typed view of the typed garbling with the keys and
permutation bits read from the coins. -/
private theorem prvViewWord_gb (k : ℕ) (f : ValidCircuit) {x : List Bool}
    (hx : x.length = f.val.n) (coins : List Bool) :
    (⟨((scheme family).gb k f coins).fn,
      (scheme family).encode ((scheme family).gb k f coins).encInfo x,
      ((scheme family).gb k f coins).decInfo⟩ : PrvView) =
      viewWord k _ ((garbleWith (toCircuit f) fullInterpretation
        (PRF.label (PRF.atLevel family (k + 1))) (slotTweak _ k) (keyFn k coins)
        (permFn coins)).view (BitString.ofList f.val.n x)) := by
  rw [gb_eq_encodeGarbled]
  simp only [viewWord, encodeGarbled, garbleWith, Garbled.view, PrvView.mk.injEq, true_and,
    and_true]
  exact projectiveEncode_labelBits (n := f.val.n) _ hx

/-- **The real view is the typed real view.** For a valid circuit `f` and an input `x` of `f.n`
bits, the real view `(F, X, d)` of the query `(f, x)` at parameter `k` is the typed view of the
typed garbling of `toCircuit f`, with the keyed function and tweaks of the scheme, written as
words. -/
private theorem eval_prvView (k : ℕ) (f : ValidCircuit) {x : List Bool} (hx : x.length = f.val.n) :
    ProbComp.eval ((scheme family).prvView k ⟨f, x⟩) =
      (ProbComp.eval (garble (toCircuit f) fullInterpretation
        (PRF.label (PRF.atLevel family (k + 1))) (slotTweak _ k))).map
          fun G => viewWord k _ (G.view (BitString.ofList f.val.n x)) := by
  have hcoins : (scheme family).coins k f = (f.val.n + (toCircuit f).size) * (2 * (k + 1) + 1) := by
    rw [size_toCircuit]
    rfl
  simp only [Scheme.prvView, garble, bind_pure_comp, ProbComp.eval_map, ProbComp.eval_bind,
    Scheme.eval_garble, ProbComp.eval_uniform, hcoins, PMF.map_comp]
  have hfun : ((fun a : Scheme.Garbled => (⟨a.fn, (scheme family).encode a.encInfo x, a.decInfo⟩ :
      PrvView)) ∘ (scheme family).gb k f) =
      (fun p : (Wire f.val.n (toCircuit f).size × Bool → BitString (k + 1)) ×
          (Wire f.val.n (toCircuit f).size → Bool) => viewWord k _ ((garbleWith (toCircuit f)
        fullInterpretation (PRF.label (PRF.atLevel family (k + 1))) (slotTweak _ k) p.1
          p.2).view (BitString.ofList f.val.n x))) ∘
        (fun coins => ((keyFn k coins : Wire f.val.n (toCircuit f).size × Bool → _),
          (permFn coins : Wire f.val.n (toCircuit f).size → Bool))) :=
    funext fun coins => prvViewWord_gb family k f hx coins
  rw [hfun, ← PMF.map_comp, uniformList_map_keyFn_permFn,
    ← Cslib.Probability.PMF.uniformOfFintype_prod]
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]

/-! ### Hybrid views on words -/

/-- The value of wire `v`, numbered from `0`, in the plaintext evaluation of `f` on `x`. -/
private def wireBit (f : ConventionalCircuit) (x : List Bool) (v : ℕ) : Bool :=
  (f.wires x f.q).getD v false

/-- Row `i` of gate `g` of hybrid view `j` on words, at parameter `k`, from the garbler's coins
`kc`, the filler labels `sc` and the oracle's answers `rs`: a row that reads an inactive colour on
a wire numbered below `j` holds its filler label; any other row holds the gate's label for the
bits its colours encode, masked by the keyed function at its argument keys, except that the mask
of an argument slot reading the inactive colour of wire `j` is the answer to that slot's tweak,
the answer numbered `8 g + 2 i + a` for slot `a`. -/
private def hybRow (k : ℕ) (f : ConventionalCircuit) (x : List Bool) (j : ℕ)
    (kc sc : List Bool) (rs : List (List Bool)) (g : Fin f.q) (i : ℕ) : List Bool :=
  let a := f.A g - 1
  let b := f.B g - 1
  let actA := wireBit f x a ^^ permOf kc a
  let actB := wireBit f x b ^^ permOf kc b
  if (i.testBit 1 ≠ actA ∧ a < j) ∨ (i.testBit 0 ≠ actB ∧ b < j) then
    simLabel k sc (f.n + f.q + 4 * g + i)
  else
    let bit := f.G g (i.testBit 1 ^^ permOf kc a) (i.testBit 0 ^^ permOf kc b)
    List.zipWith xor (labelOf k (f.n + f.q) kc (f.n + g) (bit ^^ permOf kc (f.n + g)))
      (List.zipWith xor
        (if i.testBit 1 ≠ actA ∧ a = j then rs.getD (8 * g + 2 * i) [] else
          labelWord family k (keyOf k (f.n + f.q) kc a (i.testBit 1)) (tweak k g i 0))
        (if i.testBit 0 ≠ actB ∧ b = j then rs.getD (8 * g + 2 * i + 1) [] else
          labelWord family k (keyOf k (f.n + f.q) kc b (i.testBit 0)) (tweak k g i 1)))

/-- Hybrid view `j` on words: the garbled function of the rows `hybRow`, the labels encoding `x`
and the permutation bits of the output wires. -/
private def hybViewWord (k : ℕ) (f : ConventionalCircuit) (x : List Bool) (j : ℕ)
    (kc sc : List Bool) (rs : List (List Bool)) : PrvView where
  fn := encFn ((k, f.n, f.m, f.q), (List.ofFn fun g : Fin f.q =>
    BitString.lowBits (wireWidth f.n f.q) (f.A g) ++
      BitString.lowBits (wireWidth f.n f.q) (f.B g) ++
      (List.ofFn fun i : Fin 4 => hybRow family k f x j kc sc rs g i).flatten).flatten)
  input := (List.ofFn fun i : Fin f.n =>
    labelOf k (f.n + f.q) kc i (x.getD i false ^^ permOf kc i)).flatten
  decInfo := List.ofFn fun o : Fin f.m => permOf kc (f.n + f.q - f.m + o)

/-- The answers `rs` to the tweaks of the slots, as an oracle on slots: slot `a` of row `ρ` of gate
`g` reads answer number `8 g + 2 rowIndex ρ + a`, the number of its tweak. -/
private def replyOracle (k : ℕ) {τ : Circuit.Topology n m s} (rs : List (List Bool)) :
    Slot τ → BitString (k + 1) × Bool
  | ⟨⟨g, ρ⟩, a⟩ => labelOfWord k (rs.getD (8 * g + 2 * rowIndex ρ + a) [])

/-- An existential over the two arguments of a binary gate. -/
private theorem exists_fin_of_eq_two {r : ℕ} (hr : r = 2) (P : Fin r → Prop) :
    (∃ a, P a) ↔ P ⟨0, by omega⟩ ∨ P ⟨1, by omega⟩ := by
  subst hr
  exact Fin.exists_fin_two

/-- The plaintext of row `i < 4` of gate `g` of `toCircuit f`, with keys and permutation bits
read from the coins, as a word. -/
private theorem labelBits_plainRow (k : ℕ) (f : ValidCircuit) (kc : List Bool)
    (g : Fin (toCircuit f).size) (i : ℕ) :
    labelBits (plainRow (toCircuit f) fullInterpretation (keyFn k kc) (permFn kc)
        ⟨g, fun a => i.testBit ((toCircuit f).topology.arity g - 1 - a)⟩) =
      labelOf k (f.val.n + f.val.q) kc (f.val.n + g)
        (f.val.G (g.cast (size_toCircuit f)) (i.testBit 1 ^^ permOf kc (f.val.A (g.cast
          (size_toCircuit f)) - 1)) (i.testBit 0 ^^ permOf kc (f.val.B (g.cast
            (size_toCircuit f)) - 1)) ^^ permOf kc (f.val.n + g)) := by
  have hq : f.val.n + (toCircuit f).size = f.val.n + f.val.q := by rw [size_toCircuit]
  simp only [plainRow, Circuit.topology]
  rw [lines_toCircuit f g]
  simp only [fullSignature, fullInterpretation, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_one, labelBits_keyFn, Wire.toNat_gate, Wire.toNat_ofNat, permFn, hq,
    Bool.add_eq_xor]
  rfl

/-- The value of wire `w` of `toCircuit f` on the input `x`. -/
private theorem trace_wires (f : ValidCircuit) {x : List Bool} (hx : x.length = f.val.n)
    (w : Wire f.val.n (toCircuit f).size) :
    (toCircuit f).program.trace fullInterpretation (BitString.ofList f.val.n x) w =
      wireBit f.val x w.toNat := by
  rw [trace_toCircuit, BitString.ofFn_ofList hx, wireBit]

/-- Row `i` of gate `g` of hybrid view `j`, with the keys, permutation bits and filler labels read
from the coins and the answers `rs` in the target slots, as a word, is `hybRow`. -/
private theorem labelBits_hybridView (k : ℕ) (f : ValidCircuit) {x : List Bool}
    (hx : x.length = f.val.n) (j : ℕ) (kc sc : List Bool) {rs : List (List Bool)}
    (hrs : ∀ w ∈ rs, w.length = k + 2) (hlen : 8 * f.val.q ≤ rs.length)
    (g : Fin (toCircuit f).size) {i : ℕ} (hi : i < 4) :
    labelBits ((hybridView (toCircuit f) fullInterpretation
        (PRF.label (PRF.atLevel family (k + 1))) (slotTweak _ k) (BitString.ofList f.val.n x) j
        (keyFn k kc) (permFn kc) (simFillerRows k _ sc) (replyOracle k rs)).table
          (rowOf _ g i)) =
      hybRow family k f.val x j kc sc rs (g.cast (size_toCircuit f)) i := by
  have harity := arity_topology_toCircuit f g
  have hw₀ : ((toCircuit f).topology.wires g ⟨0, by omega⟩).toNat =
      f.val.A (g.cast (size_toCircuit f)) - 1 := by
    rw [toNat_wires_toCircuit]; rfl
  have hw₁ : ((toCircuit f).topology.wires g ⟨1, by omega⟩).toNat =
      f.val.B (g.cast (size_toCircuit f)) - 1 := by
    rw [toNat_wires_toCircuit]; rfl
  have hq : f.val.n + (toCircuit f).size = f.val.n + f.val.q := by rw [size_toCircuit]
  have hg : g.val < f.val.q := size_toCircuit f ▸ g.isLt
  have hreply : ∀ a < 2, labelBits (labelOfWord k (rs.getD (8 * g + 2 * i + a) [])) =
      rs.getD (8 * g + 2 * i + a) [] := by
    intro a ha
    have hlt : 8 * g + 2 * i + a < rs.length := by omega
    apply labelBits_labelOfWord
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
    exact hrs _ (List.getElem_mem hlt)
  have hc₀ : (Fin.cast harity.symm 0 : Fin ((toCircuit f).topology.arity g)) = ⟨0, by omega⟩ :=
    Fin.ext rfl
  have hc₁ : (Fin.cast harity.symm 1 : Fin ((toCircuit f).topology.arity g)) = ⟨1, by omega⟩ :=
    Fin.ext rfl
  have htb₀ : i.testBit ((toCircuit f).topology.arity g - 1 - 0) = i.testBit 1 := by
    rw [harity]
  have htb₁ : i.testBit ((toCircuit f).topology.arity g - 1 - 1) = i.testBit 0 := by
    rw [harity]
  simp only [hybridView, rowOf, simFillerRows]
  simp only [rowIndex_testBit_of_eq_two harity hi]
  rw [apply_ite labelBits]
  unfold hybRow
  refine ite_congr (propext ?_) (fun _ => ?_) (fun _ => ?_)
  · simp only [IsHidden, exists_fin_of_eq_two harity, htb₀, htb₁, activeColour, trace_wires f hx,
      permFn, hw₀, hw₁, Bool.add_eq_xor]
  · rw [labelBits_labelOfWord (length_simLabel _ _ _), hq]
    rfl
  · rw [labelBits_add, labelBits_plainRow k f kc g i, ← Fin.sum_congr' _ harity.symm,
      Fin.sum_univ_two, labelBits_add, hc₀, hc₁]
    congr 2
    · rw [apply_ite labelBits]
      refine ite_congr (propext ?_) (fun _ => ?_) (fun _ => ?_)
      · simp only [IsTarget, htb₀, activeColour, trace_wires f hx, permFn, hw₀, Bool.add_eq_xor]
      · simpa only [replyOracle, rowIndex_testBit_of_eq_two harity hi, Fin.val_cast, add_zero] using
          hreply 0 (by omega)
      · rw [← labelWord_ofFn, ofFn_keyFn, hw₀]
        simp only [slotTweak, ofFn_ofList_tweak, rowIndex_testBit_of_eq_two harity hi, htb₀, hq,
          Fin.val_cast]
    · rw [apply_ite labelBits]
      refine ite_congr (propext ?_) (fun _ => ?_) (fun _ => ?_)
      · simp only [IsTarget, htb₁, activeColour, trace_wires f hx, permFn, hw₁, Bool.add_eq_xor]
      · simpa only [replyOracle, rowIndex_testBit_of_eq_two harity hi, Fin.val_cast] using
          hreply 1 (by omega)
      · rw [← labelWord_ofFn, ofFn_keyFn, hw₁]
        simp only [slotTweak, ofFn_ofList_tweak, rowIndex_testBit_of_eq_two harity hi, htb₁, hq,
          Fin.val_cast]

/-- **The hybrid view on words is the typed hybrid view.** For a valid circuit `f`, an input `x`
of `f.n` bits and answers `rs` of `k + 2` bits to the tweaks of all slots, hybrid view `j` on words
is the words of the typed hybrid view `j` of `toCircuit f`, with the keys, permutation bits and
filler labels read from the coins and the answers in the target slots. -/
private theorem hybViewWord_eq (k : ℕ) (f : ValidCircuit) {x : List Bool} (hx : x.length = f.val.n)
    (j : ℕ) (kc sc : List Bool) {rs : List (List Bool)} (hrs : ∀ w ∈ rs, w.length = k + 2)
    (hlen : 8 * f.val.q ≤ rs.length) :
    hybViewWord family k f.val x j kc sc rs = viewWord k (toCircuit f).topology
      (hybridView (toCircuit f) fullInterpretation (PRF.label (PRF.atLevel family (k + 1)))
        (slotTweak _ k) (BitString.ofList f.val.n x) j (keyFn k kc) (permFn kc)
        (simFillerRows k _ sc) (replyOracle k rs)) := by
  have hrow : ∀ (g : Fin (toCircuit f).size) (i : Fin 4),
      labelBits ((hybridView (toCircuit f) fullInterpretation
        (PRF.label (PRF.atLevel family (k + 1))) (slotTweak _ k) (BitString.ofList f.val.n x) j
        (keyFn k kc) (permFn kc) (simFillerRows k _ sc) (replyOracle k rs)).table
          (rowOf _ g i)) = hybRow family k f.val x j kc sc rs (g.cast (size_toCircuit f)) i :=
    fun g i => labelBits_hybridView family k f hx j kc sc hrs hlen g i.isLt
  have hq : f.val.n + (toCircuit f).size = f.val.n + f.val.q := by rw [size_toCircuit]
  simp only [hybViewWord, viewWord, encodeFn, encodeBody, PrvView.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · simp only [gateWord_toCircuit, hrow]
    congr 2
    · rw [size_toCircuit]
    · rw [List.ofFn_congr (size_toCircuit f)]
      rfl
  · simp only [hybridView, encode, inputEncoding, labelBits_keyFn, Wire.toNat_input, hq, permFn,
      BitString.ofList, Bool.add_eq_xor]
  · congr 1
    funext o
    simp only [hybridView, outputDecoding, permFn, toNat_outputs_toCircuit]

/-! ### The reduction -/

/-- One step of collecting the oracle's answers at label parameter `k`: ask the tweak numbered by
the answers collected so far, `lowBits k` of that number, and keep the first `k + 2` bits of the
reply. Answer `8 g + 2 i + a` is then the answer to the tweak of slot `a` of row `i` of gate `g`. -/
private noncomputable def replyStep (k : ℕ) (rs : List (List Bool)) :
    WordOracleComp Unit (List (List Bool)) :=
  replyStepWord (k + 2) (BitString.lowBits k rs.length) rs

/-- **The PRF reduction** for a `prv.sim` adversary `B`, at label parameter `k`, with step range
`dyadicSize (P k)`: run `B`'s choice of a query `(f, x)`; when `x` has `f.n` bits, draw a step `j`,
the garbler's coins and filler labels, ask the oracle at the tweaks of the `8 q` slots, and run
`B`'s guess on hybrid view `j`; otherwise run `B`'s guess on `⊥`. -/
noncomputable def prvSimReduction {σ : Type} (B : ℕ → PrvSimAdversary ValidCircuit σ)
    (P : ℕ → ℕ) : OracleDistinguisher :=
  fun k _ => do
    let (query, state) ← ProbOracleComp.sample ((B k).choose ())
    if query.input.length = query.fn.val.n then do
      let j ← ProbOracleComp.sample (ProbComp.sampleDyadicIndex (P k))
      let kc ← ProbOracleComp.sample
        (BitString.sampleList ((query.fn.val.n + query.fn.val.q) * (2 * (k + 1) + 1)))
      let sc ← ProbOracleComp.sample
        (BitString.sampleList (simCoinLen k query.fn.val.n query.fn.val.q))
      let rs ← OracleComp.iterate (8 * query.fn.val.q) (replyStep k) []
      ProbOracleComp.sample ((B k).guess state
        (some (hybViewWord family k query.fn.val query.input j kc sc rs)))
    else ProbOracleComp.sample ((B k).guess state none)

/-- Against a label table `T`, collecting `c` answers gives the words of `T` at the tweaks
`lowBits k 0`, ..., `lowBits k (c - 1)`. -/
private theorem run_iterate_replyStep (k : ℕ) (T : BitString k → BitString (k + 1) × Bool)
    (c : ℕ) :
    ProbOracleComp.run (OracleComp.iterate c (replyStep k) [])
        ((labelCodec k).wordOracle fun t => pure (T t)) =
      pure ((List.range c).map fun idx =>
        labelBits (T (BitString.ofList k (BitString.lowBits k idx)))) := by
  unfold replyStep
  simpa only [List.take_of_length_le (length_labelBits _).le] using
    run_iterate_replyStepWord (k + 2) c (BitString.lowBits k) _
      (fun idx => labelBits (T (BitString.ofList k (BitString.lowBits k idx)))) fun idx _ => by
        simp [OracleCodec.wordOracle, labelCodec, OracleCodec.bitString, labelBits]

/-- The answers collected from a label table, read as an oracle on the slots of `toCircuit f`,
are the table at the slots' tweaks. -/
private theorem replyOracle_table (k : ℕ) (f : ValidCircuit)
    (T : BitString k → BitString (k + 1) × Bool) (p : Slot (toCircuit f).topology) :
    replyOracle k ((List.range (8 * f.val.q)).map fun idx =>
        labelBits (T (BitString.ofList k (BitString.lowBits k idx)))) p =
      T (slotTweak _ k p) := by
  obtain ⟨⟨g, ρ⟩, a⟩ := p
  have hg : g.val < f.val.q := size_toCircuit f ▸ g.isLt
  have hρ := rowIndex_lt_four (arity_topology_toCircuit f g) ρ
  have ha : a.val < 2 := a.isLt.trans_eq (arity_topology_toCircuit f g)
  have hlt : 8 * g + 2 * rowIndex ρ + a < 8 * f.val.q := by omega
  simp only [replyOracle, slotTweak, tweak, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hlt, Option.map_some, Option.getD_some]
  apply ((labelCodec k).encodeReply 0).injective
  change labelBits _ = labelBits _
  rw [labelBits_labelOfWord (length_labelBits _)]

/-- **The word reduction runs the typed reductions.** Against every label table `T`, the reduction
for `B` at label parameter `k` runs `B`'s choice of `(f, x)` and, when `x` has `f.n` bits, the
typed reduction for a uniform step `j` below `dyadicSize (P k)` on `toCircuit f` with `B`'s guess
on the words of the view; otherwise `B`'s guess on `⊥`. -/
theorem eval_run_prvSimReduction {σ : Type} (B : ℕ → PrvSimAdversary ValidCircuit σ) (P : ℕ → ℕ)
    (k : ℕ) (T : BitString k → BitString (k + 1) × Bool) :
    ProbComp.eval (((labelCodec k).adapt (prvSimReduction family B P k [])).run
        fun t => pure (T t)) =
      (ProbComp.eval ((B k).choose ())).bind fun (query, state) =>
        if query.input.length = query.fn.val.n then
          (PMF.uniformOfFintype (Fin (Probability.dyadicSize (P k)))).bind fun j =>
            ProbComp.eval ((reduction (toCircuit query.fn) fullInterpretation
              (PRF.label (PRF.atLevel family (k + 1))) (slotTweak _ k)
              (BitString.ofList query.fn.val.n query.input)
              (fun V => (B k).guess state (some (viewWord k _ V))) j).run
                fun t => pure (T t))
        else ProbComp.eval ((B k).guess state none) := by
  simp only [prvSimReduction, OracleCodec.run_adapt, ProbOracleComp.run_bind,
    ProbOracleComp.run_sample, ProbComp.eval_bind]
  refine congrArg _ (funext fun ⟨query, state⟩ => ?_)
  dsimp only
  split_ifs with hx
  swap
  · simp only [ProbOracleComp.run_sample]
  set f := query.fn
  set x := query.input
  have hq : f.val.n + (toCircuit f).size = f.val.n + f.val.q := by rw [size_toCircuit]
  have hrs : ∀ w ∈ (List.range (8 * f.val.q)).map (fun idx =>
      labelBits (T (BitString.ofList k (BitString.lowBits k idx)))), w.length = k + 2 := by
    intro w hw
    obtain ⟨_, -, rfl⟩ := List.mem_map.mp hw
    exact length_labelBits _
  have hlen : 8 * f.val.q ≤ ((List.range (8 * f.val.q)).map (fun idx =>
      labelBits (T (BitString.ofList k (BitString.lowBits k idx))))).length := by simp
  have hfill : (BitString.uniformList (simCoinLen k f.val.n (toCircuit f).size)).map
      (simFillerRows k (toCircuit f).topology) =
        PMF.uniformOfFintype (Row (toCircuit f).topology → BitString (k + 1) × Bool) := by
    rw [← Cslib.Probability.PMF.uniformOfFintype_prod_map_snd
      (α := Wire f.val.n (toCircuit f).size →
      BitString (k + 1) × Bool), ← uniformList_map_simCoins k _ (arity_topology_toCircuit f),
      PMF.map_comp]
    rfl
  simp only [ProbOracleComp.run_bind, ProbOracleComp.run_sample, run_iterate_replyStep,
    ProbComp.eval_bind, pure_bind, ProbComp.eval_sampleDyadicIndex,
    BitString.eval_sampleList, PMF.bind_map, Function.comp_def,
    hybViewWord_eq family k f hx _ _ _ hrs hlen, eval_run_reduction]
  refine congrArg _ (funext fun j => ?_)
  rw [show simCoinLen k f.val.n f.val.q = simCoinLen k f.val.n (toCircuit f).size by
        rw [size_toCircuit],
    show (f.val.n + f.val.q) * (2 * (k + 1) + 1) =
        (f.val.n + (toCircuit f).size) * (2 * (k + 1) + 1) by
      rw [size_toCircuit]]
  have hreply : (replyOracle k ((List.range (8 * f.val.q)).map fun idx =>
      labelBits (T (BitString.ofList k (BitString.lowBits k idx)))) :
        Slot (toCircuit f).topology → BitString (k + 1) × Bool) =
      fun p => T (slotTweak _ k p) :=
    funext (replyOracle_table k f T)
  rw [hreply]
  set G : (Wire f.val.n (toCircuit f).size × Bool → BitString (k + 1)) →
      (Wire f.val.n (toCircuit f).size → Bool) →
        (Row (toCircuit f).topology → BitString (k + 1) × Bool) → PMF Bool :=
    fun key perm R => ProbComp.eval ((B k).guess state (some (viewWord k _
      (hybridView (toCircuit f) fullInterpretation (PRF.label (PRF.atLevel family (k + 1)))
        (slotTweak _ k) (BitString.ofList f.val.n x) j key perm R
          fun p => T (slotTweak _ k p)))))
  have hinner (key) (perm) :
      (BitString.uniformList (simCoinLen k f.val.n (toCircuit f).size)).bind
        (fun sc => G key perm (simFillerRows k _ sc)) =
      (PMF.uniformOfFintype (Row (toCircuit f).topology → BitString (k + 1) × Bool)).bind
        (G key perm) := by
    rw [← hfill, PMF.bind_map]; rfl
  change (BitString.uniformList ((f.val.n + (toCircuit f).size) * (2 * (k + 1) + 1))).bind
      (fun kc => (BitString.uniformList (simCoinLen k f.val.n (toCircuit f).size)).bind
        fun sc => G (keyFn k kc) (permFn kc) (simFillerRows k _ sc)) = _
  simp only [hinner]
  trans (((BitString.uniformList ((f.val.n + (toCircuit f).size) * (2 * (k + 1) + 1))).map
      fun kc => ((keyFn k kc : Wire f.val.n (toCircuit f).size × Bool → _),
        (permFn kc : Wire f.val.n (toCircuit f).size → Bool))).bind
      fun p => (PMF.uniformOfFintype _).bind (G p.1 p.2))
  · rw [PMF.bind_map]; rfl
  · rw [uniformList_map_keyFn_permFn, ← Cslib.Probability.PMF.uniformOfFintype_prod]
    simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def]; rfl

/-! ### The exact bound -/

/-- Global hybrid `i` for `B` at parameter `k`: `B`'s choice of `(f, x)`, then, when `x` has `f.n`
bits, hybrid experiment `i` of `toCircuit f` with `B`'s guess on the words of the view; otherwise
`B`'s guess on `⊥`. -/
private noncomputable def prvSimHybrid {σ : Type} (B : ℕ → PrvSimAdversary ValidCircuit σ)
    (k i : ℕ) : Game :=
  (ProbComp.eval ((B k).choose ())).bind fun (query, state) =>
    if query.input.length = query.fn.val.n then
      hybridGame (toCircuit query.fn) fullInterpretation (PRF.label (PRF.atLevel family (k + 1)))
        (slotTweak _ k) (BitString.ofList query.fn.val.n query.input)
        (fun V => (B k).guess state (some (viewWord k _ V))) i
    else ProbComp.eval ((B k).guess state none)

/-- The real `prv.sim` experiment is global hybrid `0`. -/
private theorem eval_prvSimExperiment_true {σ : Type} (B : ℕ → PrvSimAdversary ValidCircuit σ)
    (k : ℕ) (S : PrvSimulator ValidTopo) :
    ProbComp.eval (prvSimExperiment (scheme family) phiTopo k S (B k) true) =
      prvSimHybrid family B k 0 := by
  simp only [prvSimExperiment, prvSimHybrid, ProbComp.eval_bind]
  refine congrArg _ (funext fun ⟨query, state⟩ => ?_)
  have hin : (scheme family).inLen query.fn = query.fn.val.n := rfl
  dsimp only
  rw [hin]
  split_ifs with hx
  · simp only [hybridGame_zero, ProbComp.eval_bind, realGame, eval_prvView family k query.fn hx,
      PMF.bind_map]
    rfl
  · rfl

/-- The simulated `prv.sim` experiment is every global hybrid from the largest number of wires
on. -/
private theorem eval_prvSimExperiment_false {σ : Type} (B : ℕ → PrvSimAdversary ValidCircuit σ)
    (k c : ℕ)
    (hc : ∀ query state, (query, state) ∈ (ProbComp.eval ((B k).choose ())).support →
      query.input.length = query.fn.val.n → query.fn.val.n + query.fn.val.q ≤ c) :
    ProbComp.eval (prvSimExperiment (scheme family) phiTopo k (simWord family k) (B k) false) =
      prvSimHybrid family B k c := by
  simp only [prvSimExperiment, prvSimHybrid, ProbComp.eval_bind]
  refine Probability.PMF.bind_congr_on_support _ _ _ fun ⟨query, state⟩ hmem => ?_
  have hin : (scheme family).inLen query.fn = query.fn.val.n := rfl
  have hev : (scheme family).ev query.fn query.input = query.fn.val.evalCirc query.input := rfl
  simp only [hin, hev, Bool.false_eq_true, ↓reduceIte]
  split_ifs with hx
  · rw [hybridGame_of_le _ _ _ _ _ _ (by rw [size_toCircuit]; exact hc query state hmem hx)]
    have hy : BitString.ofList query.fn.val.m (query.fn.val.evalCirc query.input) =
        (toCircuit query.fn).eval fullInterpretation
          (BitString.ofList query.fn.val.n query.input) := by
      rw [← BitString.ofList_ofFn (bits := (toCircuit query.fn).eval _ _), eval_toCircuit,
        BitString.ofFn_ofList hx]
    simp only [ProbComp.eval_bind, simGame, eval_simWord, hy, PMF.bind_map]
    rfl
  · rfl

/-- Against the keyed label function, the reduction plays a uniform global hybrid below
`dyadicSize (P k)`. -/
private theorem eval_realExperiment_prvSimReduction {σ : Type}
    (B : ℕ → PrvSimAdversary ValidCircuit σ) (P : ℕ → ℕ) (k : ℕ) :
    ProbComp.eval (PRF.realExperiment (PRF.label (PRF.atLevel family (k + 1)))
        ((labelCodec k).adapt (prvSimReduction family B P k []))) =
      (PMF.uniformOfFintype (Fin (Probability.dyadicSize (P k)))).bind fun j =>
        prvSimHybrid family B k j := by
  simp only [PRF.realExperiment, ProbComp.eval_bind, ProbComp.eval_uniform,
    eval_run_prvSimReduction, prvSimHybrid]
  rw [PMF.bind_comm, PMF.bind_comm (PMF.uniformOfFintype (Fin _))]
  refine congrArg _ (funext fun ⟨query, state⟩ => ?_)
  dsimp only
  split_ifs with hx
  · rw [PMF.bind_comm]
    exact congrArg _ (funext fun j => by simp [← eval_realExperiment_reduction, PRF.realExperiment])
  · rw [PMF.bind_const, PMF.bind_const]

/-- Against a uniform random function, the reduction plays the next global hybrid, when every
valid query `B k` can choose has at most `P k` wires and `8 P k ≤ 2 ^ k`. -/
private theorem eval_idealExperiment_prvSimReduction {σ : Type}
    (B : ℕ → PrvSimAdversary ValidCircuit σ) (P : ℕ → ℕ) (k : ℕ)
    (hP : ∀ query state, (query, state) ∈ (ProbComp.eval ((B k).choose ())).support →
      query.input.length = query.fn.val.n → query.fn.val.n + query.fn.val.q ≤ P k)
    (hk : 8 * P k ≤ 2 ^ k) :
    ProbComp.eval (PRF.idealExperiment ((labelCodec k).adapt (prvSimReduction family B P k []))) =
      (PMF.uniformOfFintype (Fin (Probability.dyadicSize (P k)))).bind fun j =>
        prvSimHybrid family B k (j + 1) := by
  simp only [PRF.idealExperiment, ProbComp.eval_bind, ProbComp.eval_uniform,
    eval_run_prvSimReduction, prvSimHybrid]
  rw [PMF.bind_comm, PMF.bind_comm (PMF.uniformOfFintype (Fin _))]
  refine Probability.PMF.bind_congr_on_support _ _ _ fun ⟨query, state⟩ hmem => ?_
  dsimp only
  split_ifs with hx
  · have htw := slotTweak_injective k query.fn (by
      have := hP query state hmem hx
      omega)
    rw [PMF.bind_comm]
    exact congrArg _ (funext fun j => by
      simp [← eval_idealExperiment_reduction _ _ _ _ htw, PRF.idealExperiment])
  · rw [PMF.bind_const, PMF.bind_const]

/-- **The `prv.sim` advantage against the simulator is the reduction's label advantage, times the
step range.** At parameter `k`, if every valid query `B k` can choose has at most `P k` wires and
`8 P k ≤ 2 ^ k`, the `prv.sim` advantage of `B k` against `simWord` is `dyadicSize (P k)` times
the finite PRF advantage of `prvSimReduction family B P` at label parameter `k`, read through
`labelCodec k`, against the label function of `family` at parameter `k + 1`. -/
theorem prvSimAdvantage_simWord_eq {σ : Type} (B : ℕ → PrvSimAdversary ValidCircuit σ)
    (P : ℕ → ℕ) (k : ℕ)
    (hP : ∀ query state, (query, state) ∈ (ProbComp.eval ((B k).choose ())).support →
      query.input.length = query.fn.val.n → query.fn.val.n + query.fn.val.q ≤ P k)
    (hk : 8 * P k ≤ 2 ^ k) :
    prvSimAdvantage (scheme family) phiTopo k (simWord family k) (B k) =
      Probability.dyadicSize (P k) * PRF.advantage (PRF.label (PRF.atLevel family (k + 1)))
        ((labelCodec k).adapt (prvSimReduction family B P k [])) := by
  have hc : ∀ query state, (query, state) ∈ (ProbComp.eval ((B k).choose ())).support →
      query.input.length = query.fn.val.n →
        query.fn.val.n + query.fn.val.q ≤ Probability.dyadicSize (P k) :=
    fun query state hmem hx => (hP query state hmem hx).trans (Probability.lt_dyadicSize _).le
  rw [prvSimAdvantage, Experiment.advantage, eval_prvSimExperiment_false family B k _ hc,
    eval_prvSimExperiment_true, Game.advantage_comm,
    Game.advantage_hybrid_average (prvSimHybrid family B k) _ _ le_rfl, PRF.advantage,
    eval_realExperiment_prvSimReduction, eval_idealExperiment_prvSimReduction family B P k hP hk]
  simp only [Fin.is_lt, ↓reduceIte]

/-! ### Efficiency -/

section Efficiency

open Turing.MultiTapeTM

variable {family}

/-- The active colour of wire `v`: its plaintext value plus its permutation bit. -/
private def actBit (ws kc : List Bool) (v : ℕ) : Bool := permOf ws v ^^ permOf kc v

/-- Whether the colour `c` of wire `v` is inactive and the wire is numbered below `j`. -/
private def hiddenBit (ws kc : List Bool) (j v : ℕ) (c : Bool) : Bool :=
  c != actBit ws kc v && decide (v < j)

/-- Whether the colour `c` of wire `v` is inactive and the wire is wire `j`. -/
private def targetBit (ws kc : List Bool) (j v : ℕ) (c : Bool) : Bool :=
  c != actBit ws kc v && decide (v = j)

/-- The mask term of slot `slot` of row `i` of gate `g` reading wire `v` with colour `c`: the
answer to its tweak when it is a target, the keyed function at its key otherwise. -/
private def maskWord (k n q j : ℕ) (ws kc : List Bool) (rs : List (List Bool)) (v : ℕ) (c : Bool)
    (g i slot : ℕ) : List Bool :=
  if targetBit ws kc j v c then rs.getD (8 * g + 2 * i + slot) [] else
    labelWord family k (keyOf k (n + q) kc v c) (tweak k g i slot)

/-- The plaintext word of row `i` of gate `g`, from its 0-indexed argument wires and truth table. -/
private def plainWord (k n q : ℕ) (kc : List Bool) (a b : ℕ) (t : List Bool) (g i : ℕ) :
    List Bool :=
  labelOf k (n + q) kc (n + g)
    (t.getD ((if i.testBit 1 ^^ permOf kc a then 2 else 0) +
      (if i.testBit 0 ^^ permOf kc b then 1 else 0)) false ^^ permOf kc (n + g))

/-- Row `i` of gate `g` of hybrid view `j`, from the plaintext wire values `ws`, the 0-indexed
argument wires `a` and `b` and the truth table `t` of the gate. -/
private def hybRowData (k n q j : ℕ) (ws kc sc : List Bool) (rs : List (List Bool)) (a b : ℕ)
    (t : List Bool) (g i : ℕ) : List Bool :=
  if hiddenBit ws kc j a (i.testBit 1) || hiddenBit ws kc j b (i.testBit 0) then
    simLabel k sc (n + q + 4 * g + i)
  else List.zipWith xor (plainWord k n q kc a b t g i)
    (List.zipWith xor (maskWord (family := family) k n q j ws kc rs a (i.testBit 1) g i 0)
      (maskWord (family := family) k n q j ws kc rs b (i.testBit 0) g i 1))

/-- Hybrid view `j` on words from the data of the circuit and its plaintext wire values: the body
is `bodyWith` of the gate list, with the rows `hybRowData` on argument wires capped at the number of
wire values. -/
private theorem hybViewWord_eq_data (k : ℕ) (f : ValidCircuit) (x : List Bool) (j : ℕ)
    (kc sc : List Bool) (rs : List (List Bool)) :
    hybViewWord family k f.val x j kc sc rs =
      ⟨encFn ((k, f.val.n, f.val.m, f.val.gateList.length),
          bodyWith f.val.n f.val.gateList.length ((f.val.wires x f.val.q).length + 1)
            (fun g => (f.val.gateList.getD g (0, 0, [])).1)
            (fun g => (f.val.gateList.getD g (0, 0, [])).2.1)
            (fun g a b i => hybRowData (family := family) k f.val.n f.val.gateList.length j
              (f.val.wires x f.val.q) kc sc rs a b (f.val.gateList.getD g (0, 0, [])).2.2 g i)),
        ((List.range f.val.n).map fun i =>
          labelOf k (f.val.n + f.val.gateList.length) kc i (permOf x i ^^ permOf kc i)).flatten,
        decInfoWord f.val kc⟩ := by
  have hws : (f.val.wires x f.val.q).length = f.val.n + f.val.q := f.val.length_wires x le_rfl
  have hgate (g : Fin f.val.q) : f.val.gateList.getD g (0, 0, []) = (f.val.A g, f.val.B g,
      [f.val.G g false false, f.val.G g false true,
        f.val.G g true false, f.val.G g true true]) := by
    simp [ConventionalCircuit.gateList, List.getD_eq_getElem?_getD]
  have hrow (g : Fin f.val.q) (i : Fin 4) :
      hybRowData (family := family) k f.val.n f.val.q j (f.val.wires x f.val.q) kc sc rs
        (min ((f.val.wires x f.val.q).length + 1) (f.val.A g) - 1)
        (min ((f.val.wires x f.val.q).length + 1) (f.val.B g) - 1)
        (f.val.gateList.getD g (0, 0, [])).2.2 g i = hybRow family k f.val x j kc sc rs g i := by
    have hA := f.property.one_le_A g
    have hAB := f.property.A_lt_B g
    have hBg := f.property.B_lt_gate g
    simp only [topo] at hA hAB hBg
    have hcapA : min ((f.val.wires x f.val.q).length + 1) (f.val.A g) - 1 = f.val.A g - 1 := by
      rw [hws]; omega
    have hcapB : min ((f.val.wires x f.val.q).length + 1) (f.val.B g) - 1 = f.val.B g - 1 := by
      rw [hws]; omega
    simp only [hcapA, hcapB, hgate, hybRowData, hybRow, hiddenBit, targetBit, actBit, maskWord,
      plainWord, getD_table, add_zero]
    simp only [wireBit, permOf, Bool.or_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq,
      decide_eq_true_eq]
    rfl
  simp only [hybViewWord, ConventionalCircuit.length_gateList, List.map_range_eq_ofFn]
  rw [bodyWith_eq_ofFn f.val.A f.val.B (hybRow family k f.val x j kc sc rs) (fun g => by rw [hgate])
    (fun g => by rw [hgate]) hrow]
  rfl

variable (hf : ComputableInPolyTime (fun p : List Bool × List Bool => family p.1 p.2)
  (encPair encBits encBits) encBits)

attribute [local fun_prop] labelWord_polyTime tweak_polyTime wireWidth_polyTime permOf_polyTime
  keyOf_polyTime labelOf_polyTime simLabel_polyTime

private theorem actBit_polyTime {γ : Type} {encIn : γ ↪ List Bool} {ws kc : γ → List Bool}
    {v : γ → ℕ} (hws : ComputableInPolyTime ws encIn encBits)
    (hkc : ComputableInPolyTime kc encIn encBits) (hv : ComputableInPolyTime v encIn encUnary) :
    ComputableInPolyTime (fun x => actBit (ws x) (kc x) (v x)) encIn encBool := by
  unfold actBit
  polytime

attribute [local fun_prop] actBit_polyTime

private theorem hiddenBit_polyTime {γ : Type} {encIn : γ ↪ List Bool} {ws kc : γ → List Bool}
    {j v : γ → ℕ} {c : γ → Bool} (hws : ComputableInPolyTime ws encIn encBits)
    (hkc : ComputableInPolyTime kc encIn encBits) (hj : ComputableInPolyTime j encIn encUnary)
    (hv : ComputableInPolyTime v encIn encUnary) (hc : ComputableInPolyTime c encIn encBool) :
    ComputableInPolyTime (fun x => hiddenBit (ws x) (kc x) (j x) (v x) (c x)) encIn encBool := by
  unfold hiddenBit
  polytime

private theorem targetBit_polyTime {γ : Type} {encIn : γ ↪ List Bool} {ws kc : γ → List Bool}
    {j v : γ → ℕ} {c : γ → Bool} (hws : ComputableInPolyTime ws encIn encBits)
    (hkc : ComputableInPolyTime kc encIn encBits) (hj : ComputableInPolyTime j encIn encUnary)
    (hv : ComputableInPolyTime v encIn encUnary) (hc : ComputableInPolyTime c encIn encBool) :
    ComputableInPolyTime (fun x => targetBit (ws x) (kc x) (j x) (v x) (c x)) encIn encBool := by
  unfold targetBit
  polytime

attribute [local fun_prop] hiddenBit_polyTime targetBit_polyTime

include hf in
private theorem maskWord_polyTime {γ : Type} {encIn : γ ↪ List Bool} {k n q j v g i slot : γ → ℕ}
    {ws kc : γ → List Bool} {rs : γ → List (List Bool)} {c : γ → Bool}
    (hk : ComputableInPolyTime k encIn encUnary) (hn : ComputableInPolyTime n encIn encUnary)
    (hq : ComputableInPolyTime q encIn encUnary) (hj : ComputableInPolyTime j encIn encUnary)
    (hws : ComputableInPolyTime ws encIn encBits) (hkc : ComputableInPolyTime kc encIn encBits)
    (hrs : ComputableInPolyTime rs encIn (encList encBits))
    (hv : ComputableInPolyTime v encIn encUnary) (hc : ComputableInPolyTime c encIn encBool)
    (hg : ComputableInPolyTime g encIn encUnary) (hi : ComputableInPolyTime i encIn encUnary)
    (hslot : ComputableInPolyTime slot encIn encUnary) :
    ComputableInPolyTime (fun x => maskWord (family := family) (k x) (n x) (q x) (j x) (ws x)
      (kc x) (rs x) (v x) (c x) (g x) (i x) (slot x)) encIn encBits := by
  have hwidth := ComputableInPolyTime.unary_add.comp (hn.prod hq)
  have hindex := ComputableInPolyTime.unary_add.comp
    ((ComputableInPolyTime.unary_add.comp
      ((ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const 8) hg).prod
        (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const 2) hi))).prod hslot)
  exact (targetBit_polyTime hws hkc hj hv hc).ite
    (ComputableInPolyTime.listGetDWithInput hrs hindex [])
    (labelWord_polyTime hf hk (keyOf_polyTime hk hwidth hkc hv hc)
      (tweak_polyTime hk hg hi hslot))

attribute [local fun_prop] maskWord_polyTime

private theorem plainWord_polyTime {γ : Type} {encIn : γ ↪ List Bool} {k n q a b g i : γ → ℕ}
    {kc t : γ → List Bool}
    (hk : ComputableInPolyTime k encIn encUnary) (hn : ComputableInPolyTime n encIn encUnary)
    (hq : ComputableInPolyTime q encIn encUnary) (hkc : ComputableInPolyTime kc encIn encBits)
    (ha : ComputableInPolyTime a encIn encUnary) (hb : ComputableInPolyTime b encIn encUnary)
    (ht : ComputableInPolyTime t encIn encBits) (hg : ComputableInPolyTime g encIn encUnary)
    (hi : ComputableInPolyTime i encIn encUnary) :
    ComputableInPolyTime (fun x => plainWord (k x) (n x) (q x) (kc x) (a x) (b x) (t x) (g x)
      (i x)) encIn encBits := by
  unfold plainWord
  polytime

attribute [local fun_prop] plainWord_polyTime

include hf in
private theorem hybRowData_polyTime {γ : Type} {encIn : γ ↪ List Bool} {k n q j a b g i : γ → ℕ}
    {ws kc sc t : γ → List Bool} {rs : γ → List (List Bool)}
    (hk : ComputableInPolyTime k encIn encUnary) (hn : ComputableInPolyTime n encIn encUnary)
    (hq : ComputableInPolyTime q encIn encUnary) (hj : ComputableInPolyTime j encIn encUnary)
    (hws : ComputableInPolyTime ws encIn encBits) (hkc : ComputableInPolyTime kc encIn encBits)
    (hsc : ComputableInPolyTime sc encIn encBits)
    (hrs : ComputableInPolyTime rs encIn (encList encBits))
    (ha : ComputableInPolyTime a encIn encUnary) (hb : ComputableInPolyTime b encIn encUnary)
    (ht : ComputableInPolyTime t encIn encBits) (hg : ComputableInPolyTime g encIn encUnary)
    (hi : ComputableInPolyTime i encIn encUnary) :
    ComputableInPolyTime (fun x => hybRowData (family := family) (k x) (n x) (q x) (j x) (ws x)
      (kc x) (sc x) (rs x) (a x) (b x) (t x) (g x) (i x)) encIn encBits := by
  unfold hybRowData
  polytime

private theorem hybInput_polyTime :
    ComputableInPolyTime (fun p : ℕ × ℕ × ℕ × List Bool × List Bool =>
      ((List.range p.2.1).map fun i => labelOf p.1 (p.2.1 + p.2.2.1) p.2.2.2.2 i
        (permOf p.2.2.2.1 i ^^ permOf p.2.2.2.2 i)).flatten)
      (encPair encUnary (encPair encUnary (encPair encUnary (encPair encBits encBits))))
      encBits := by
  polytime

include hf in
/-- Hybrid view `j` on words is computed in polynomial time. -/
private theorem hybViewWord_polyTime {γ : Type} {encIn : γ ↪ List Bool}
    {k j : γ → ℕ} {f : γ → ValidCircuit} {x kc sc : γ → List Bool}
    {rs : γ → List (List Bool)}
    (hk : ComputableInPolyTime k encIn encUnary)
    (hf' : ComputableInPolyTime f encIn encValidCircuit)
    (hx : ComputableInPolyTime x encIn encBits)
    (hj : ComputableInPolyTime j encIn encUnary)
    (hkc : ComputableInPolyTime kc encIn encBits)
    (hsc : ComputableInPolyTime sc encIn encBits)
    (hrs : ComputableInPolyTime rs encIn (encList encBits)) :
    ComputableInPolyTime
      (fun p => hybViewWord family (k p) (f p).val (x p) (j p) (kc p) (sc p) (rs p))
      encIn encPrvView := by
  have hd := circuitData_polyTime.comp hf'
  have hn : ComputableInPolyTime (fun p => (f p).val.n) encIn encUnary := hd.fst'
  have hm : ComputableInPolyTime (fun p => (f p).val.m) encIn encUnary := hd.snd'.fst'
  have hg : ComputableInPolyTime (fun p => (f p).val.gateList) encIn
      (encList (encPair encNat (encPair encNat encBits))) := hd.snd'.snd'
  have hq : ComputableInPolyTime (fun p => (f p).val.gateList.length) encIn encUnary :=
    (ComputableInPolyTime.length_list _).comp hg
  have hws : ComputableInPolyTime (fun p => (f p).val.wires (x p) (f p).val.q) encIn encBits :=
    wires_polyTime.comp (hf'.prod hx)
  have hcap : ComputableInPolyTime (fun p => ((f p).val.wires (x p) (f p).val.q).length + 1) encIn
      encUnary :=
    ComputableInPolyTime.unary_add' hws.length_bits_comp (ComputableInPolyTime.const 1)
  have hp := ComputableInPolyTime.fst encIn (encPair encUnary (encPair encUnary
    (encPair encUnary encUnary)))
  have hr := ComputableInPolyTime.snd encIn (encPair encUnary (encPair encUnary
    (encPair encUnary encUnary)))
  have ht := (ComputableInPolyTime.listGetDWithInput (hg.comp hp) hr.fst' (0, 0, [])).snd'.snd'
  have hrow := hybRowData_polyTime hf (hk.comp hp) (hn.comp hp) (hq.comp hp) (hj.comp hp)
    (hws.comp hp) (hkc.comp hp) (hsc.comp hp) (hrs.comp hp) hr.snd'.fst' hr.snd'.snd'.fst' ht
    hr.fst' hr.snd'.snd'.snd'
  have hgate := ComputableInPolyTime.listGetDWithInput
    (hg.comp (ComputableInPolyTime.fst encIn encUnary)) (ComputableInPolyTime.snd _ _) (0, 0, [])
  have hbody := bodyWith_polyTime
    (n := fun p => (f p).val.n)
    (cap := fun p => ((f p).val.wires (x p) (f p).val.q).length + 1)
    (A := fun p g => ((f p).val.gateList.getD g (0, 0, [])).1)
    (B := fun p g => ((f p).val.gateList.getD g (0, 0, [])).2.1)
    (row := fun p g a b i =>
      hybRowData (family := family) (k p) (f p).val.n (f p).val.gateList.length
      (j p) ((f p).val.wires (x p) (f p).val.q) (kc p) (sc p) (rs p) a b
      ((f p).val.gateList.getD g (0, 0, [])).2.2 g i)
    hn hq hcap hgate.fst' hgate.snd'.fst' hrow
  have henc : ComputableInPolyTime (fun z : (ℕ × ℕ × ℕ × ℕ) × List Bool => encFn z) encFn
      encBits := .of_eq fun _ => rfl
  have hfn := henc.comp ((hk.prod (hn.prod (hm.prod hq))).prod hbody)
  have hinput := hybInput_polyTime.comp (hk.prod (hn.prod (hq.prod (hx.prod hkc))))
  have hdec := decInfoWord_polyTime.comp (hf'.prod hkc)
  simp only [hybViewWord_eq_data]
  exact encPrvView_mk_polyTime hfn hinput hdec

variable {σ : Type} {encσ : σ ↪ List Bool} {B : ℕ → PrvSimAdversary ValidCircuit σ}
  (hB : TwoStage.IsPPT encUnit (encQuery ValidCircuit encValidCircuit) (encOption encPrvView)
    encBool encσ B)

/-- The state before the replies: the chosen state, the step, the garbler's coins and the filler
labels. -/
private abbrev encDrawn (encσ : σ ↪ List Bool) :
    ((((ℕ × List Bool) × (Query ValidCircuit × σ)) × ℕ) × List Bool) × List Bool ↪ List Bool :=
  encPair (encPair (encPair (encPrvChosen encValidCircuit encσ) encUnary) encBits) encBits

include hf hB in
/-- The valid branch of the reduction after the draws: collect the answers and run `B`'s guess on
the hybrid view. -/
private theorem isOraclePPTOn_prvSimGuess :
    IsOraclePPTOn (encDrawn encσ) encBool
      (fun p : ((((ℕ × List Bool) × (Query ValidCircuit × σ)) × ℕ) × List Bool) × List Bool => do
        let rs ← OracleComp.iterate (8 * p.1.1.1.2.1.fn.val.q) (replyStep p.1.1.1.1.1) []
        ProbOracleComp.sample ((B p.1.1.1.1.1).guess p.1.1.1.2.2
          (some (hybViewWord family p.1.1.1.1.1 p.1.1.1.2.1.fn.val p.1.1.1.2.1.input p.1.1.2 p.1.2
            p.2 rs)))) := by
  let E := encDrawn encσ
  have h₀ := ComputableInPolyTime.fst
    (encPair (encPair (encPrvChosen encValidCircuit encσ) encUnary) encBits) encBits
  have h₁ := h₀.fst'
  have hchosen := h₁.fst'
  have hk := hchosen.fst'.fst'
  have hquery := hchosen.snd'.fst'
  have hstate := hchosen.snd'.snd'
  have hj := h₁.snd'
  have hkc := h₀.snd'
  have hsc := ComputableInPolyTime.snd
    (encPair (encPair (encPrvChosen encValidCircuit encσ) encUnary) encBits) encBits
  have hfn := encQuery_fn_polyTime _ _ hquery
  have hx := encQuery_input_polyTime _ _ hquery
  have hq : ComputableInPolyTime (fun p : ((((ℕ × List Bool) × (Query ValidCircuit × σ)) × ℕ) ×
      List Bool) × List Bool => p.1.1.1.2.1.fn.val.q) E encUnary := by
    simpa only [Function.comp_def, ConventionalCircuit.length_gateList] using
      (ComputableInPolyTime.length_list _).comp (circuitData_polyTime.comp hfn).snd'.snd'
  have hrs := isOraclePPTOn_iterate_replyStepWord
    (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const 8) hq)
    (ComputableInPolyTime.unary_add' hk (ComputableInPolyTime.const 2))
    (ComputableInPolyTime.bitsLow (hk.comp (ComputableInPolyTime.fst _ _))
      (ComputableInPolyTime.length_list_binary' (ComputableInPolyTime.snd _ _)))
  have hfst := ComputableInPolyTime.fst E (encList encBits)
  have hview := hybViewWord_polyTime hf (hk.comp hfst) (hfn.comp hfst) (hx.comp hfst)
    (hj.comp hfst) (hkc.comp hfst) (hsc.comp hfst) (ComputableInPolyTime.snd E (encList encBits))
  have hprep := (hk.comp hfst).prod ((hstate.comp hfst).prod
    ((ComputableInPolyTime.optionSome encPrvView).comp hview))
  exact hrs.bind_with (hB.guess.preprocess hprep).isOraclePPTOn

include hf hB in
/-- **Efficiency of the reduction.** For every family computed in polynomial time, every uniform
strict PPT `prv.sim` adversary `B` and every step range `P` computed in polynomial time in unary,
`prvSimReduction family B P` is uniform strict oracle PPT. -/
theorem isOraclePPT_prvSimReduction {P : ℕ → ℕ}
    (hP : ComputableInPolyTime P encUnary encUnary) :
    IsOraclePPT encBool (prvSimReduction family B P) := by
  let E := encPrvChosen encValidCircuit encσ
  have hk := (ComputableInPolyTime.fst (encPair encUnary encBits)
    (encPair (encQuery ValidCircuit encValidCircuit) encσ)).fst'
  have hquery := (ComputableInPolyTime.snd (encPair encUnary encBits)
    (encPair (encQuery ValidCircuit encValidCircuit) encσ)).fst'
  have hfn := encQuery_fn_polyTime _ _ hquery
  have hx := encQuery_input_polyTime _ _ hquery
  have hd := circuitData_polyTime.comp hfn
  have hn := hd.fst'
  have hq : ComputableInPolyTime (fun p : (ℕ × List Bool) × (Query ValidCircuit × σ) =>
      p.2.1.fn.val.q) E encUnary := by
    simpa only [Function.comp_def, ConventionalCircuit.length_gateList] using
      (ComputableInPolyTime.length_list _).comp hd.snd'.snd'
  have hcond := ComputableInPolyTime.decide_eq' (ComputableInPolyTime.length_bits_comp hx) hn
  have hj := (isPPTOn_sampleDyadicIndex (hP.comp hk)).isOraclePPTOn (Operation := Unit)
  have hf1 := ComputableInPolyTime.fst E encUnary
  have hlen : ComputableInPolyTime (fun p : ((ℕ × List Bool) × (Query ValidCircuit × σ)) × ℕ =>
      (p.1.2.1.fn.val.n + p.1.2.1.fn.val.q) * (2 * (p.1.1.1 + 1) + 1)) (encPair E encUnary)
      encUnary := by
    have := hn.comp hf1; have := hq.comp hf1; have := hk.comp hf1
    polytime
  have hkc := (isPPTOn_sampleList.preprocess hlen).isOraclePPTOn (Operation := Unit)
  have hf2 := hf1.comp (ComputableInPolyTime.fst (encPair E encUnary) encBits)
  have hsimLen : ComputableInPolyTime (fun p : (((ℕ × List Bool) × (Query ValidCircuit × σ)) × ℕ) ×
      List Bool => simCoinLen p.1.1.1.1 p.1.1.2.1.fn.val.n p.1.1.2.1.fn.val.q)
      (encPair (encPair E encUnary) encBits) encUnary := by
    have := hn.comp hf2; have := hq.comp hf2; have := hk.comp hf2
    unfold simCoinLen; polytime
  have hsc := (isPPTOn_sampleList.preprocess hsimLen).isOraclePPTOn (Operation := Unit)
  exact isOraclePPT_prvSimReduction_of_guard hB
    (fun _ query => query.input.length = query.fn.val.n) hcond
    (fun k query state => do
      let j ← ProbOracleComp.sample (ProbComp.sampleDyadicIndex (P k))
      let kc ← ProbOracleComp.sample
        (BitString.sampleList ((query.fn.val.n + query.fn.val.q) * (2 * (k + 1) + 1)))
      let sc ← ProbOracleComp.sample
        (BitString.sampleList (simCoinLen k query.fn.val.n query.fn.val.q))
      let rs ← OracleComp.iterate (8 * query.fn.val.q) (replyStep k) []
      ProbOracleComp.sample ((B k).guess state
        (some (hybViewWord family k query.fn.val query.input j kc sc rs))))
    (hj.bind_with (hkc.bind_with (hsc.bind_with (isOraclePPTOn_prvSimGuess hf hB))))

end Efficiency

end Cslib.Crypto.Garbling.PointPermute
