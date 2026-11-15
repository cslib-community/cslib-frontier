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
import CslibFrontier.Foundations.Data.BitString.List.LowBits
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Crypto.Game.Hybrid

/-!
# The real view of point-and-permute garbling as a typed view

Steps toward the privacy theorem for `PointPermute.scheme family`. The garbler's coins give uniform
keys and permutation bits (`uniformList_map_keyFn_permFn`), so the real view `(F, X, d)` of a
query is the typed view of the typed garbling of `toCircuit f`, written as words
(`eval_prvView`). Distinct argument slots get distinct tweaks while the table has at most
`2 ^ k / 8` gates (`slotTweak_injective`).

## Main results

* `Cslib.Crypto.Garbling.PointPermute.eval_prvView`: the real view is the typed real view.
* `Cslib.Crypto.Garbling.PointPermute.slotTweak_injective`: tweaks of distinct slots differ.
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
theorem uniformList_map_keyFn_permFn (k n s : ℕ) :
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
          fun word i => BitString.ofList 1 (BitString.listRow 1 (Wire.equivFin n s i) word) := by
      funext front w
      rfl
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
        rw [← PMF.uniformOfFintype_map_equiv (Equiv.prodComm (Wire n s → Bool)
          (Wire n s × Bool → BitString (k + 1))), ← Cslib.Probability.PMF.uniformOfFintype_prod,
          PMF.map_bind]
        simp only [PMF.map_comp, Function.comp_def, Equiv.prodComm_apply, Prod.swap_prod_mk]

variable (family : List Bool → List Bool → List Bool)

/-- The real view on given coins is the typed view of the typed garbling with the keys and
permutation bits read from the coins. -/
private theorem prvViewWord_gb (k : ℕ) (f : ValidCircuit) {x : List Bool}
    (hx : x.length = f.1.n) (coins : List Bool) :
    (⟨((scheme family).gb k f coins).fn,
      (scheme family).encode ((scheme family).gb k f coins).encInfo x,
      ((scheme family).gb k f coins).decInfo⟩ : PrvView) =
      viewWord k _ ((garbleWith (toCircuit f) fullInterpretation
        (PRF.label (PRF.atLevel family (k + 1))) (slotTweak _ k) (keyFn k coins)
        (permFn coins)).view (BitString.ofList f.1.n x)) := by
  rw [gb_eq_encodeGarbled]
  simp only [viewWord, encodeGarbled, garbleWith, Garbled.view, PrvView.mk.injEq, true_and,
    and_true]
  exact encodeWord_encInfo (n := f.1.n) _ hx

/-- **The real view is the typed real view.** For a valid circuit `f` and an input `x` of `f.n`
bits, the real view `(F, X, d)` of the query `(f, x)` at parameter `k` is the typed view of the
typed garbling of `toCircuit f`, with the keyed function and tweaks of the scheme, written as
words. -/
theorem eval_prvView (k : ℕ) (f : ValidCircuit) {x : List Bool} (hx : x.length = f.1.n) :
    ProbComp.eval ((scheme family).prvView k ⟨f, x⟩) =
      (ProbComp.eval (garble (toCircuit f) fullInterpretation
        (PRF.label (PRF.atLevel family (k + 1))) (slotTweak _ k))).map
          fun G => viewWord k _ (G.view (BitString.ofList f.1.n x)) := by
  have hcoins : (scheme family).coins k f = (f.1.n + (toCircuit f).size) * (2 * (k + 1) + 1) := by
    rw [size_toCircuit]
    rfl
  have hmap : ∀ {α β : Type} (p : PMF α) (g : α → β), p.bind (fun a => PMF.pure (g a)) = p.map g :=
    fun p g => PMF.bind_pure_comp g p
  simp only [Scheme.prvView, ProbComp.eval_bind, Scheme.eval_garble, ProbComp.eval_pure, garble,
    ProbComp.eval_uniform, hmap, hcoins, PMF.map_comp]
  have hfun : ((fun a : Scheme.Garbled => (⟨a.fn, (scheme family).encode a.encInfo x, a.decInfo⟩ :
      PrvView)) ∘ (scheme family).gb k f) =
      (fun p : (Wire f.1.n (toCircuit f).size × Bool → BitString (k + 1)) ×
          (Wire f.1.n (toCircuit f).size → Bool) => viewWord k _ ((garbleWith (toCircuit f)
        fullInterpretation (PRF.label (PRF.atLevel family (k + 1))) (slotTweak _ k) p.1
          p.2).view (BitString.ofList f.1.n x))) ∘
        (fun coins => ((keyFn k coins : Wire f.1.n (toCircuit f).size × Bool → _),
          (permFn coins : Wire f.1.n (toCircuit f).size → Bool))) :=
    funext fun coins => prvViewWord_gb family k f hx coins
  rw [hfun, ← PMF.map_comp, uniformList_map_keyFn_permFn,
    ← Cslib.Probability.PMF.uniformOfFintype_prod]
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]

/-! ### Tweaks -/

/-- **Distinct slots have distinct tweaks** while `8 q ≤ 2 ^ k`: slot `a` of row `ρ` of gate `g`
has the tweak `8 g + 2 rowIndex ρ + a`, which is below `2 ^ k`. -/
theorem slotTweak_injective (k : ℕ) (f : ValidCircuit) (hk : 8 * f.1.q ≤ 2 ^ k) :
    Function.Injective (slotTweak (toCircuit f).topology k) := by
  have hbound : ∀ p : Slot (toCircuit f).topology,
      8 * p.1.1 + 2 * rowIndex p.1.2 + p.2 < 2 ^ k := by
    rintro ⟨⟨g, ρ⟩, a⟩
    have hg : g.val < f.1.q := size_toCircuit f ▸ g.isLt
    have hρ := rowIndex_lt_four (arity_topology_toCircuit f g) ρ
    have ha : a.val < 2 := by
      have := a.isLt
      simp only [arity_topology_toCircuit] at this
      exact this
    dsimp only
    omega
  rintro ⟨⟨g, ρ⟩, a⟩ ⟨⟨g', ρ'⟩, a'⟩ h
  have h' := congrArg List.ofFn h
  simp only [slotTweak, tweak] at h'
  rw [BitString.ofFn_ofList (BitString.length_lowBits _ _),
    BitString.ofFn_ofList (BitString.length_lowBits _ _)] at h'
  have heq := BitString.lowBits_injective_of_lt (hbound ⟨⟨g, ρ⟩, a⟩) (hbound ⟨⟨g', ρ'⟩, a'⟩) h'
  dsimp only at heq
  have hρ := rowIndex_lt_four (arity_topology_toCircuit f g) ρ
  have hρ' := rowIndex_lt_four (arity_topology_toCircuit f g') ρ'
  have ha : a.val < 2 := by
    have := a.isLt
    simp only [arity_topology_toCircuit] at this
    exact this
  have ha' : a'.val < 2 := by
    have := a'.isLt
    simp only [arity_topology_toCircuit] at this
    exact this
  have hgv : g.val = g'.val := by omega
  have hg : g = g' := Fin.ext hgv
  subst hg
  have hi : rowIndex ρ = rowIndex ρ' := by omega
  have hρeq : ρ = ρ' := by
    rw [← testBit_rowIndex_of_eq_two (arity_topology_toCircuit f g) ρ,
      ← testBit_rowIndex_of_eq_two (arity_topology_toCircuit f g) ρ', hi]
  subst hρeq
  have haeq : a = a' := Fin.ext (by omega)
  subst haeq
  rfl

/-! ### Hybrid views on words -/

/-- The value of wire `v`, numbered from `0`, in the plaintext evaluation of `f` on `x`. -/
@[expose] def wireBit (f : ConventionalCircuit) (x : List Bool) (v : ℕ) : Bool :=
  (f.wires x f.q).getD v false

/-- Row `i` of gate `g` of hybrid view `j` on words, at parameter `k`, from the garbler's coins
`kc`, the filler labels `sc` and the oracle's answers `rs`: a row that reads an inactive colour on
a wire numbered below `j` holds its filler label; any other row holds the gate's label for the
bits its colours encode, masked by the keyed function at its argument keys, except that the mask
of an argument slot reading the inactive colour of wire `j` is the answer to that slot's tweak,
the answer numbered `8 g + 2 i + a` for slot `a`. -/
@[expose] def hybRow (k : ℕ) (f : ConventionalCircuit) (x : List Bool) (j : ℕ)
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
@[expose] def hybViewWord (k : ℕ) (f : ConventionalCircuit) (x : List Bool) (j : ℕ)
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
@[expose] def replyOracle (k : ℕ) {τ : Circuit.Topology n m s} (rs : List (List Bool)) :
    Slot τ → BitString (k + 1) × Bool
  | ⟨⟨g, ρ⟩, a⟩ => labelOfWord k (rs.getD (8 * g + 2 * rowIndex ρ + a) [])

/-- An existential over the two arguments of a binary gate. -/
private theorem exists_fin_of_eq_two {r : ℕ} (hr : r = 2) (P : Fin r → Prop) :
    (∃ a, P a) ↔ P ⟨0, by omega⟩ ∨ P ⟨1, by omega⟩ := by
  subst hr
  constructor
  · rintro ⟨a, ha⟩
    match a with
    | ⟨0, _⟩ => exact Or.inl ha
    | ⟨1, _⟩ => exact Or.inr ha
  · rintro (h | h)
    · exact ⟨_, h⟩
    · exact ⟨_, h⟩

/-- The plaintext of row `i < 4` of gate `g` of `toCircuit f`, with keys and permutation bits
read from the coins, as a word. -/
private theorem labelBits_plainRow (k : ℕ) (f : ValidCircuit) (kc : List Bool)
    (g : Fin (toCircuit f).size) (i : ℕ) :
    labelBits (plainRow (toCircuit f) fullInterpretation (keyFn k kc) (permFn kc)
        ⟨g, fun a => i.testBit ((toCircuit f).topology.arity g - 1 - a)⟩) =
      labelOf k (f.1.n + f.1.q) kc (f.1.n + g)
        (f.1.G (g.cast (size_toCircuit f)) (i.testBit 1 ^^ permOf kc (f.1.A (g.cast
          (size_toCircuit f)) - 1)) (i.testBit 0 ^^ permOf kc (f.1.B (g.cast
            (size_toCircuit f)) - 1)) ^^ permOf kc (f.1.n + g)) := by
  have hq : f.1.n + (toCircuit f).size = f.1.n + f.1.q := by rw [size_toCircuit]
  simp only [plainRow, Circuit.topology]
  rw [lines_toCircuit f g]
  simp only [fullSignature, fullInterpretation, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_one, labelBits_keyFn, Wire.toNat_gate, Wire.toNat_ofNat, permFn, hq,
    Bool.add_eq_xor]
  rfl

/-- The value of wire `w` of `toCircuit f` on the input `x`. -/
private theorem trace_wires (f : ValidCircuit) {x : List Bool} (hx : x.length = f.1.n)
    (w : Wire f.1.n (toCircuit f).size) :
    (toCircuit f).program.trace fullInterpretation (BitString.ofList f.1.n x) w =
      wireBit f.1 x w.toNat := by
  rw [trace_toCircuit, BitString.ofFn_ofList hx, wireBit]

/-- Row `i` of gate `g` of hybrid view `j`, with the keys, permutation bits and filler labels read
from the coins and the answers `rs` in the target slots, as a word, is `hybRow`. -/
private theorem labelBits_hybridView (k : ℕ) (f : ValidCircuit) {x : List Bool}
    (hx : x.length = f.1.n) (j : ℕ) (kc sc : List Bool) {rs : List (List Bool)}
    (hrs : ∀ w ∈ rs, w.length = k + 2) (hlen : 8 * f.1.q ≤ rs.length)
    (g : Fin (toCircuit f).size) {i : ℕ} (hi : i < 4) :
    labelBits ((hybridView (toCircuit f) fullInterpretation
        (PRF.label (PRF.atLevel family (k + 1))) (slotTweak _ k) (BitString.ofList f.1.n x) j
        (keyFn k kc) (permFn kc) (simFillerRows k _ sc) (replyOracle k rs)).table
          (rowOf _ g i)) =
      hybRow family k f.1 x j kc sc rs (g.cast (size_toCircuit f)) i := by
  have harity := arity_topology_toCircuit f g
  have hw₀ : ((toCircuit f).topology.wires g ⟨0, by omega⟩).toNat =
      f.1.A (g.cast (size_toCircuit f)) - 1 := by
    rw [toNat_wires_toCircuit]; rfl
  have hw₁ : ((toCircuit f).topology.wires g ⟨1, by omega⟩).toNat =
      f.1.B (g.cast (size_toCircuit f)) - 1 := by
    rw [toNat_wires_toCircuit]; rfl
  have hq : f.1.n + (toCircuit f).size = f.1.n + f.1.q := by rw [size_toCircuit]
  have hg : g.val < f.1.q := size_toCircuit f ▸ g.isLt
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
      · simp only [replyOracle, rowIndex_testBit_of_eq_two harity hi, Fin.val_mk, add_zero]
        exact hreply 0 (by omega)
      · rw [← labelWord_ofFn, ofFn_keyFn, hw₀]
        simp only [slotTweak, ofFn_ofList_tweak, rowIndex_testBit_of_eq_two harity hi, Fin.val_mk,
          htb₀, hq, Fin.val_cast]
    · rw [apply_ite labelBits]
      refine ite_congr (propext ?_) (fun _ => ?_) (fun _ => ?_)
      · simp only [IsTarget, htb₁, activeColour, trace_wires f hx, permFn, hw₁, Bool.add_eq_xor]
      · simp only [replyOracle, rowIndex_testBit_of_eq_two harity hi, Fin.val_mk]
        exact hreply 1 (by omega)
      · rw [← labelWord_ofFn, ofFn_keyFn, hw₁]
        simp only [slotTweak, ofFn_ofList_tweak, rowIndex_testBit_of_eq_two harity hi, Fin.val_mk,
          htb₁, hq, Fin.val_cast]

/-- **The hybrid view on words is the typed hybrid view.** For a valid circuit `f`, an input `x`
of `f.n` bits and answers `rs` of `k + 2` bits to the tweaks of all slots, hybrid view `j` on words
is the words of the typed hybrid view `j` of `toCircuit f`, with the keys, permutation bits and
filler labels read from the coins and the answers in the target slots. -/
theorem hybViewWord_eq (k : ℕ) (f : ValidCircuit) {x : List Bool} (hx : x.length = f.1.n)
    (j : ℕ) (kc sc : List Bool) {rs : List (List Bool)} (hrs : ∀ w ∈ rs, w.length = k + 2)
    (hlen : 8 * f.1.q ≤ rs.length) :
    hybViewWord family k f.1 x j kc sc rs = viewWord k (toCircuit f).topology
      (hybridView (toCircuit f) fullInterpretation (PRF.label (PRF.atLevel family (k + 1)))
        (slotTweak _ k) (BitString.ofList f.1.n x) j (keyFn k kc) (permFn kc)
        (simFillerRows k _ sc) (replyOracle k rs)) := by
  have hrow : ∀ (g : Fin (toCircuit f).size) (i : Fin 4),
      labelBits ((hybridView (toCircuit f) fullInterpretation
        (PRF.label (PRF.atLevel family (k + 1))) (slotTweak _ k) (BitString.ofList f.1.n x) j
        (keyFn k kc) (permFn kc) (simFillerRows k _ sc) (replyOracle k rs)).table
          (rowOf _ g i)) = hybRow family k f.1 x j kc sc rs (g.cast (size_toCircuit f)) i :=
    fun g i => labelBits_hybridView family k f hx j kc sc hrs hlen g i.isLt
  have hq : f.1.n + (toCircuit f).size = f.1.n + f.1.q := by rw [size_toCircuit]
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
@[expose] def replyStep (k : ℕ) (rs : List (List Bool)) : WordOracleComp Unit (List (List Bool)) := do
  let reply ← ProbOracleComp.query ((), BitString.lowBits k rs.length)
  return rs ++ [reply.take (k + 2)]

/-- **The PRF reduction** for a `prv.sim` adversary `B`, at label parameter `k`, with step range
`Probability.dyadicSize (P k)`: run `B`'s choice of a query `(f, x)`; when `x` has `f.n` bits, draw a step `j`,
the garbler's coins and filler labels, ask the oracle at the tweaks of the `8 q` slots, and run
`B`'s guess on hybrid view `j`; otherwise run `B`'s guess on `⊥`. -/
noncomputable def prvSimReduction {σ : Type} (B : ℕ → PrvSimAdversary ValidCircuit σ)
    (P : ℕ → ℕ) : OracleDistinguisher :=
  fun k _ => do
    let (query, state) ← ProbOracleComp.sample ((B k).choose ())
    if query.input.length = query.fn.1.n then do
      let j ← ProbOracleComp.sample (ProbComp.sampleDyadicIndex (P k))
      let kc ← ProbOracleComp.sample
        (BitString.sampleList ((query.fn.1.n + query.fn.1.q) * (2 * (k + 1) + 1)))
      let sc ← ProbOracleComp.sample (BitString.sampleList (simCoinLen k query.fn.1.n query.fn.1.q))
      let rs ← OracleComp.iterate (8 * query.fn.1.q) (replyStep k) []
      ProbOracleComp.sample ((B k).guess state
        (some (hybViewWord family k query.fn.1 query.input j kc sc rs)))
    else ProbOracleComp.sample ((B k).guess state none)

/-- Against a label table `T`, the word oracle of `labelCodec k` answers a `k`-bit request with the
word of `T` at that tweak, and any other request with the empty word. -/
private theorem wordOracle_labelCodec (k : ℕ) (T : BitString k → BitString (k + 1) × Bool)
    (request : Unit × List Bool) :
    (labelCodec k).wordOracle (fun t => (pure (T t) : ProbComp _)) request =
      pure (if request.2.length = k then labelBits (T (BitString.ofList k request.2)) else []) := by
  obtain ⟨⟨⟩, word⟩ := request
  by_cases hword : word.length = k <;>
    simp [OracleCodec.wordOracle, labelCodec, OracleCodec.bitString, hword, labelBits]

/-- Against a label table `T`, collecting `c` answers gives the words of `T` at the tweaks
`lowBits k 0`, ..., `lowBits k (c - 1)`. -/
private theorem run_iterate_replyStep (k : ℕ) (T : BitString k → BitString (k + 1) × Bool)
    (c : ℕ) :
    ProbOracleComp.run (OracleComp.iterate c (replyStep k) [])
        ((labelCodec k).wordOracle fun t => pure (T t)) =
      pure ((List.range c).map fun idx =>
        labelBits (T (BitString.ofList k (BitString.lowBits k idx)))) := by
  induction c with
  | zero => simp
  | succ c ih =>
    rw [OracleComp.iterate_succ, ProbOracleComp.run_bind, ih, pure_bind]
    simp only [replyStep, ProbOracleComp.run_bind, ProbOracleComp.run_query, wordOracle_labelCodec,
      BitString.length_lowBits, if_true, pure_bind, ProbOracleComp.run_pure, List.length_map,
      List.length_range, List.range_succ, List.map_append, List.map_cons, List.map_nil,
      List.take_of_length_le (le_of_eq (length_labelBits _))]

/-- The answers collected from a label table, read as an oracle on the slots of `toCircuit f`,
are the table at the slots' tweaks. -/
private theorem replyOracle_table (k : ℕ) (f : ValidCircuit)
    (T : BitString k → BitString (k + 1) × Bool) (p : Slot (toCircuit f).topology) :
    replyOracle k ((List.range (8 * f.1.q)).map fun idx =>
        labelBits (T (BitString.ofList k (BitString.lowBits k idx)))) p =
      T (slotTweak _ k p) := by
  obtain ⟨⟨g, ρ⟩, a⟩ := p
  have hg : g.val < f.1.q := size_toCircuit f ▸ g.isLt
  have hρ := rowIndex_lt_four (arity_topology_toCircuit f g) ρ
  have ha : a.val < 2 := by
    have := a.isLt
    simp only [arity_topology_toCircuit] at this
    exact this
  have hlt : 8 * g + 2 * rowIndex ρ + a < 8 * f.1.q := by omega
  simp only [replyOracle, slotTweak, tweak, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hlt, Option.map_some, Option.getD_some]
  apply ((labelCodec k).encodeReply 0).injective
  change labelBits _ = labelBits _
  rw [labelBits_labelOfWord (length_labelBits _)]

/-- The distinguisher of the typed reduction for `B` after its choice: `B`'s guess from `state` on
the words of a typed view. -/
@[expose] noncomputable def viewGuess {σ : Type} (B : PrvSimAdversary ValidCircuit σ) (k : ℕ)
    (state : σ) {n m s : ℕ} (τ : Circuit.Topology n m s) (V : View τ (BitString (k + 1))) :
    ProbComp Bool :=
  B.guess state (some (viewWord k τ V))

/-- **The word reduction runs the typed reductions.** Against every label table `T`, the reduction
for `B` at label parameter `k` runs `B`'s choice of `(f, x)` and, when `x` has `f.n` bits, the
typed reduction for a uniform step `j` below `Probability.dyadicSize (P k)` on `toCircuit f` with `B`'s guess
on the words of the view; otherwise `B`'s guess on `⊥`. -/
theorem eval_run_prvSimReduction {σ : Type} (B : ℕ → PrvSimAdversary ValidCircuit σ) (P : ℕ → ℕ)
    (k : ℕ) (T : BitString k → BitString (k + 1) × Bool) :
    ProbComp.eval (((labelCodec k).adapt (prvSimReduction family B P k [])).run
        fun t => pure (T t)) =
      (ProbComp.eval ((B k).choose ())).bind fun (query, state) =>
        if query.input.length = query.fn.1.n then
          (PMF.uniformOfFintype (Fin (Probability.dyadicSize (P k)))).bind fun j =>
            ProbComp.eval ((reduction (toCircuit query.fn) fullInterpretation
              (PRF.label (PRF.atLevel family (k + 1))) (slotTweak _ k)
              (BitString.ofList query.fn.1.n query.input) (viewGuess (B k) k state _) j).run
                fun t => pure (T t))
        else ProbComp.eval ((B k).guess state none) := by
  have hmap : ∀ {α β : Type} (p : PMF α) (g : α → β), p.bind (fun a => PMF.pure (g a)) = p.map g :=
    fun p g => PMF.bind_pure_comp g p
  simp only [prvSimReduction, OracleCodec.run_adapt, ProbOracleComp.run_bind,
    ProbOracleComp.run_sample, ProbComp.eval_bind]
  refine congrArg _ (funext fun ⟨query, state⟩ => ?_)
  dsimp only
  split_ifs with hx
  swap
  · simp only [ProbOracleComp.run_sample]
  set f := query.fn
  set x := query.input
  have hq : f.1.n + (toCircuit f).size = f.1.n + f.1.q := by rw [size_toCircuit]
  have hrs : ∀ w ∈ (List.range (8 * f.1.q)).map (fun idx =>
      labelBits (T (BitString.ofList k (BitString.lowBits k idx)))), w.length = k + 2 := by
    intro w hw
    obtain ⟨_, -, rfl⟩ := List.mem_map.mp hw
    exact length_labelBits _
  have hlen : 8 * f.1.q ≤ ((List.range (8 * f.1.q)).map (fun idx =>
      labelBits (T (BitString.ofList k (BitString.lowBits k idx))))).length := by simp
  have hfill : (BitString.uniformList (simCoinLen k f.1.n (toCircuit f).size)).map
      (simFillerRows k (toCircuit f).topology) =
        PMF.uniformOfFintype (Row (toCircuit f).topology → BitString (k + 1) × Bool) := by
    rw [← Cslib.Probability.PMF.uniformOfFintype_prod_map_snd (α := Wire f.1.n (toCircuit f).size →
      BitString (k + 1) × Bool), ← uniformList_map_simCoins k _ (arity_topology_toCircuit f),
      PMF.map_comp]
    rfl
  simp only [ProbOracleComp.run_bind, ProbOracleComp.run_sample, run_iterate_replyStep,
    ProbComp.eval_bind, ProbComp.eval_pure, pure_bind, ProbComp.eval_sampleDyadicIndex,
    BitString.eval_sampleList, PMF.bind_map, Function.comp_def,
    hybViewWord_eq family k f hx _ _ _ hrs hlen, eval_run_reduction]
  refine congrArg _ (funext fun j => ?_)
  simp only [viewGuess]
  rw [show simCoinLen k f.1.n f.1.q = simCoinLen k f.1.n (toCircuit f).size by rw [size_toCircuit],
    show (f.1.n + f.1.q) * (2 * (k + 1) + 1) = (f.1.n + (toCircuit f).size) * (2 * (k + 1) + 1) by
      rw [size_toCircuit]]
  have hreply : (replyOracle k ((List.range (8 * f.1.q)).map fun idx =>
      labelBits (T (BitString.ofList k (BitString.lowBits k idx)))) :
        Slot (toCircuit f).topology → BitString (k + 1) × Bool) =
      fun p => T (slotTweak _ k p) :=
    funext (replyOracle_table k f T)
  rw [hreply]
  set G : (Wire f.1.n (toCircuit f).size × Bool → BitString (k + 1)) →
      (Wire f.1.n (toCircuit f).size → Bool) →
        (Row (toCircuit f).topology → BitString (k + 1) × Bool) → PMF Bool :=
    fun key perm R => ProbComp.eval ((B k).guess state (some (viewWord k _
      (hybridView (toCircuit f) fullInterpretation (PRF.label (PRF.atLevel family (k + 1)))
        (slotTweak _ k) (BitString.ofList f.1.n x) j key perm R
          fun p => T (slotTweak _ k p))))) with hG
  have hinner : ∀ key perm, (BitString.uniformList (simCoinLen k f.1.n (toCircuit f).size)).bind
      (fun sc => G key perm (simFillerRows k _ sc)) =
        (PMF.uniformOfFintype (Row (toCircuit f).topology → BitString (k + 1) × Bool)).bind
          (G key perm) := by
    intro key perm
    rw [← hfill, PMF.bind_map]
    rfl
  calc _ = (BitString.uniformList ((f.1.n + (toCircuit f).size) * (2 * (k + 1) + 1))).bind
          (fun kc => (BitString.uniformList (simCoinLen k f.1.n (toCircuit f).size)).bind
            fun sc => G (keyFn k kc) (permFn kc) (simFillerRows k _ sc)) := rfl
    _ = (BitString.uniformList ((f.1.n + (toCircuit f).size) * (2 * (k + 1) + 1))).bind
          (fun kc => (PMF.uniformOfFintype (Row (toCircuit f).topology →
            BitString (k + 1) × Bool)).bind (G (keyFn k kc) (permFn kc))) := by
        simp only [hinner]
    _ = ((BitString.uniformList ((f.1.n + (toCircuit f).size) * (2 * (k + 1) + 1))).map
          (fun kc => ((keyFn k kc : Wire f.1.n (toCircuit f).size × Bool → _),
            (permFn kc : Wire f.1.n (toCircuit f).size → Bool)))).bind
          (fun p => (PMF.uniformOfFintype (Row (toCircuit f).topology →
            BitString (k + 1) × Bool)).bind (G p.1 p.2)) := by
        rw [PMF.bind_map]
        rfl
    _ = _ := by
        rw [uniformList_map_keyFn_permFn, ← Cslib.Probability.PMF.uniformOfFintype_prod]
        simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def]
        rfl

/-! ### The exact bound -/

/-- Global hybrid `i` for `B` at parameter `k`: `B`'s choice of `(f, x)`, then, when `x` has `f.n`
bits, hybrid experiment `i` of `toCircuit f` with `B`'s guess on the words of the view; otherwise
`B`'s guess on `⊥`. -/
private noncomputable def prvSimHybrid {σ : Type} (B : ℕ → PrvSimAdversary ValidCircuit σ)
    (k i : ℕ) : Game :=
  (ProbComp.eval ((B k).choose ())).bind fun (query, state) =>
    if query.input.length = query.fn.1.n then
      hybridGame (toCircuit query.fn) fullInterpretation (PRF.label (PRF.atLevel family (k + 1)))
        (slotTweak _ k) (BitString.ofList query.fn.1.n query.input)
        (viewGuess (B k) k state _) i
    else ProbComp.eval ((B k).guess state none)

/-- The real `prv.sim` experiment is global hybrid `0`. -/
private theorem eval_prvSimExperiment_true {σ : Type} (B : ℕ → PrvSimAdversary ValidCircuit σ)
    (k : ℕ) (S : PrvSimulator ValidTopo) :
    ProbComp.eval (prvSimExperiment (scheme family) phiTopo k S (B k) true) =
      prvSimHybrid family B k 0 := by
  simp only [prvSimExperiment, prvSimHybrid, ProbComp.eval_bind]
  refine congrArg _ (funext fun ⟨query, state⟩ => ?_)
  have hin : (scheme family).inLen query.fn = query.fn.1.n := rfl
  dsimp only
  rw [hin]
  split_ifs with hx
  · rw [hybridGame_zero]
    simp only [if_true, ProbComp.eval_bind, realGame]
    rw [eval_prvView family k query.fn hx, PMF.bind_map]
    rfl
  · rfl

/-- The simulated `prv.sim` experiment is every global hybrid from the largest number of wires
on. -/
private theorem eval_prvSimExperiment_false {σ : Type} (B : ℕ → PrvSimAdversary ValidCircuit σ)
    (k c : ℕ)
    (hc : ∀ query state, (query, state) ∈ (ProbComp.eval ((B k).choose ())).support →
      query.input.length = query.fn.1.n → query.fn.1.n + query.fn.1.q ≤ c) :
    ProbComp.eval (prvSimExperiment (scheme family) phiTopo k (simWord family k) (B k) false) =
      prvSimHybrid family B k c := by
  simp only [prvSimExperiment, prvSimHybrid, ProbComp.eval_bind]
  refine Probability.PMF.bind_congr_on_support _ _ _ fun ⟨query, state⟩ hmem => ?_
  have hin : (scheme family).inLen query.fn = query.fn.1.n := rfl
  have hev : (scheme family).ev query.fn query.input = query.fn.1.evalCirc query.input := rfl
  dsimp only
  simp only [hin, hev, Bool.false_eq_true, ↓reduceIte]
  split_ifs with hx
  · rw [hybridGame_of_le _ _ _ _ _ _ (by rw [size_toCircuit]; exact hc query state hmem hx)]
    simp only [ProbComp.eval_bind, simGame]
    have hy : BitString.ofList query.fn.1.m (query.fn.1.evalCirc query.input) =
        (toCircuit query.fn).eval fullInterpretation (BitString.ofList query.fn.1.n query.input) := by
      have h := eval_toCircuit query.fn (BitString.ofList query.fn.1.n query.input)
      rw [BitString.ofFn_ofList hx] at h
      rw [← h, BitString.ofList_ofFn]
    rw [eval_simWord, hy, PMF.bind_map]
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
    refine congrArg _ (funext fun j => ?_)
    rw [← eval_realExperiment_reduction]
    simp only [PRF.realExperiment, ProbComp.eval_bind, ProbComp.eval_uniform]
  · rw [PMF.bind_const, PMF.bind_const]

/-- Against a uniform random function, the reduction plays the next global hybrid, when every
valid query `B k` can choose has at most `P k` wires and `8 P k ≤ 2 ^ k`. -/
private theorem eval_idealExperiment_prvSimReduction {σ : Type}
    (B : ℕ → PrvSimAdversary ValidCircuit σ) (P : ℕ → ℕ) (k : ℕ)
    (hP : ∀ query state, (query, state) ∈ (ProbComp.eval ((B k).choose ())).support →
      query.input.length = query.fn.1.n → query.fn.1.n + query.fn.1.q ≤ P k)
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
    refine congrArg _ (funext fun j => ?_)
    rw [← eval_idealExperiment_reduction _ _ _ _ htw]
    simp only [PRF.idealExperiment, ProbComp.eval_bind, ProbComp.eval_uniform]
  · rw [PMF.bind_const, PMF.bind_const]

/-- **The `prv.sim` advantage against the simulator is the reduction's label advantage, times the
step range.** At parameter `k`, if every valid query `B k` can choose has at most `P k` wires and
`8 P k ≤ 2 ^ k`, the `prv.sim` advantage of `B k` against `simWord` is `dyadicSize (P k)` times
the finite PRF advantage of `prvSimReduction family B P` at label parameter `k`, read through
`labelCodec k`, against the label function of `family` at parameter `k + 1`. -/
theorem prvSimAdvantage_simWord_eq {σ : Type} (B : ℕ → PrvSimAdversary ValidCircuit σ)
    (P : ℕ → ℕ) (k : ℕ)
    (hP : ∀ query state, (query, state) ∈ (ProbComp.eval ((B k).choose ())).support →
      query.input.length = query.fn.1.n → query.fn.1.n + query.fn.1.q ≤ P k)
    (hk : 8 * P k ≤ 2 ^ k) :
    prvSimAdvantage (scheme family) phiTopo k (simWord family k) (B k) =
      Probability.dyadicSize (P k) * PRF.advantage (PRF.label (PRF.atLevel family (k + 1)))
        ((labelCodec k).adapt (prvSimReduction family B P k [])) := by
  haveI : NeZero (Probability.dyadicSize (P k)) := ⟨(Probability.dyadicSize_pos _).ne'⟩
  have hc : ∀ query state, (query, state) ∈ (ProbComp.eval ((B k).choose ())).support →
      query.input.length = query.fn.1.n →
        query.fn.1.n + query.fn.1.q ≤ Probability.dyadicSize (P k) :=
    fun query state hmem hx => (hP query state hmem hx).trans (Probability.lt_dyadicSize _).le
  rw [prvSimAdvantage, Experiment.advantage, eval_prvSimExperiment_false family B k _ hc,
    eval_prvSimExperiment_true, Game.advantage_comm,
    Game.advantage_hybrid_average (prvSimHybrid family B k) _ _ le_rfl, PRF.advantage,
    eval_realExperiment_prvSimReduction, eval_idealExperiment_prvSimReduction family B P k hP hk]
  simp only [Fin.is_lt, ↓reduceIte]

end Cslib.Crypto.Garbling.PointPermute
