/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Computability.Circuit.Boolean.Complexity
public import Cslib.Computability.Circuit.Simulation
public import CslibFrontier.Computability.Circuit.Boolean.Zhegalkin.Basis
public import CslibFrontier.Computability.Circuit.Boolean.Zhegalkin.Synthesis
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Ring.BooleanRing
import CslibFrontier.Computability.Circuit.Simulation
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

/-!
# Internal affine decomposition of `{⊕, ∧, 1}`-programs

Internal constant synthesis (`constOne`, `constZero`, `synth_consts`) and causal affine program
decomposition (`linForm`, `PaddedDecomp`, `exists_paddedDecomp`) consumed privately by
`Complexity`, `StageParts`, `StageStep`, and `UpperBound`; never re-exported through `Zhegalkin`.

## Main definitions

* `Cslib.Circuits.Boolean.Zhegalkin.constOne`, `constZero`, `linForm`, `PaddedDecomp`, `padBool`,
  `padFn`: constant functions and padded causal affine decompositions.

## Main results

* `Cslib.Circuits.Boolean.Zhegalkin.synth_consts`, `exists_paddedDecomp`:
  constant synthesis and existence of padded causal decompositions.
-/

public section

open Finset

namespace Cslib.Circuits.Boolean.Zhegalkin

/-- Constant-`true` `n`-variable Boolean function. -/
@[expose] def constOne (n : ℕ) : BooleanFunction n := fun _ => true
/-- Constant-`false` `n`-variable Boolean function. -/
@[expose] def constZero (n : ℕ) : BooleanFunction n := fun _ => false

theorem synth_consts (n : ℕ) :
    CostSynthesis interpretation andCost (inputs n) {constZero n, constOne n} 2 0 := by
  have h1 : CostSynthesis interpretation andCost (inputs n) {constOne n} 1 0 :=
    (CostSynthesis.gate (I := interpretation) (w := andCost) (s := inputs n)
      Op.one Fin.elim0 fun i => i.elim0).mono Set.Subset.rfl (by rintro _ rfl; rfl) le_rfl le_rfl
  have h0 : CostSynthesis interpretation andCost (inputs n ∪ {constOne n}) {constZero n} 1 0 := by
    have h := add_two_of_mem (G := Bool) (I := interpretation) (w := andCost) (addOp := Op.xor)
      rfl (fun _ => rfl) rfl (s := inputs n ∪ {constOne n}) (Or.inr rfl) (Or.inr rfl)
    refine h.mono Set.Subset.rfl ?_ le_rfl le_rfl
    rintro _ rfl
    exact rfl
  have h10 := h1.comp h0
  refine h10.mono Set.Subset.rfl ?_ le_rfl le_rfl
  intro f hf
  rcases hf with rfl | h1'
  · exact Or.inr rfl
  · exact Or.inl h1'


section Decomposition

/-- Affine combination over `GF(2)` of inputs `x` and conjunction outputs `gFn`. -/
@[expose] def linForm {n k : ℕ} (c₀ : Bool) (cX : Fin n → Bool) (cG : Fin k → Bool)
    (gFn : Fin k → BooleanFunction n) (x : Fin n → Bool) : Bool :=
  (if c₀ then true else (0 : Bool)) +
    (∑ j : Fin n, if cX j then x j else 0) +
    (∑ ℓ : Fin k, if cG ℓ then gFn ℓ x else 0)

private theorem bool_ite_add (a b z : Bool) :
    (if a + b then z else (0 : Bool)) = (if a then z else 0) + (if b then z else 0) := by
  cases a <;> cases b <;> cases z <;> rfl

private theorem linForm_add {n k : ℕ} (c₀ d₀ : Bool) (cX dX : Fin n → Bool)
    (cG dG : Fin k → Bool) (gFn : Fin k → BooleanFunction n) (x : Fin n → Bool) :
    linForm (c₀ + d₀) (fun j => cX j + dX j) (fun ℓ => cG ℓ + dG ℓ) gFn x =
      linForm c₀ cX cG gFn x + linForm d₀ dX dG gFn x := by
  unfold linForm
  simp only [bool_ite_add, sum_add_distrib]
  abel

private theorem linForm_snoc_false {n k : ℕ} (c₀ : Bool) (cX : Fin n → Bool) (cG : Fin k → Bool)
    (gFn : Fin k → BooleanFunction n) (gLast : BooleanFunction n) (x : Fin n → Bool) :
    linForm c₀ cX (Fin.snoc cG false) (Fin.snoc gFn gLast) x = linForm c₀ cX cG gFn x := by
  unfold linForm
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, Bool.false_eq_true, ↓reduceIte, add_zero]

/-- Causal affine decomposition of wires in a `{⊕, ∧, 1}`-program with `k` `∧`-gates. -/
private structure ProgDecomp {n g : ℕ} (p : Program signature n g) (k : ℕ) where
  /-- Boolean function computed by each conjunction gate wire. -/
  gFn : Fin k → BooleanFunction n
  /-- Constant bits of the linear forms fed into the `2 * k` conjunction inputs. -/
  cH : Fin (2 * k) → Bool
  /-- Input-variable coefficients of the `2 * k` conjunction input linear forms. -/
  aX : Fin (2 * k) → Fin n → Bool
  /-- Prior conjunction-gate coefficients of the `2 * k` conjunction input linear forms. -/
  aG : Fin (2 * k) → Fin k → Bool
  /-- Constant bits of the affine representation of each program wire. -/
  cW : Wire n g → Bool
  /-- Input-variable coefficients of the affine representation of each program wire. -/
  wX : Wire n g → Fin n → Bool
  /-- Conjunction-gate coefficients of the affine representation of each program wire. -/
  wG : Wire n g → Fin k → Bool
  causal : ∀ (r : Fin (2 * k)) (ℓ : Fin k), r.1 / 2 ≤ ℓ.1 → aG r ℓ = false
  gFn_eq : ∀ (i : Fin k) (x : Fin n → Bool),
    gFn i x =
      (linForm (cH ⟨2 * i.1, by omega⟩) (aX ⟨2 * i.1, by omega⟩)
          (aG ⟨2 * i.1, by omega⟩) gFn x &&
        linForm (cH ⟨2 * i.1 + 1, by omega⟩) (aX ⟨2 * i.1 + 1, by omega⟩)
          (aG ⟨2 * i.1 + 1, by omega⟩) gFn x)
  trace_eq : ∀ (w : Wire n g) (x : Fin n → Bool),
    p.trace interpretation x w = linForm (cW w) (wX w) (wG w) gFn x

private theorem progDecomp_empty (n : ℕ) :
    Nonempty (ProgDecomp (Program.empty : Program signature n 0) 0) := by
  refine ⟨{
    gFn := Fin.elim0
    cH := Fin.elim0
    aX := Fin.elim0
    aG := Fin.elim0
    cW := fun _ => false
    wX := Wire.elim (fun i j => decide (j = i)) Fin.elim0
    wG := fun _ => Fin.elim0
    causal := fun r => r.elim0
    gFn_eq := fun i => i.elim0
    trace_eq := fun w x => ?_ }⟩
  cases w with
  | gate j => exact j.elim0
  | input i =>
    unfold linForm
    simp only [Program.trace_input, Wire.elim_input, Bool.false_eq_true, ↓reduceIte, zero_add,
      decide_eq_true_eq]
    rw [sum_ite_eq', Fintype.sum_empty, add_zero]
    simp

private theorem progDecomp_one {n g k : ℕ} {q : Program signature n g}
    (ih : ProgDecomp q k) (wires : Fin (signature.Arity Op.one) → Wire n g) :
    Nonempty (ProgDecomp (q.gate ⟨Op.one, wires⟩) k) := by
  refine ⟨{
    gFn := ih.gFn
    cH := ih.cH
    aX := ih.aX
    aG := ih.aG
    cW := Wire.lastCases true ih.cW
    wX := Wire.lastCases (fun _ => false) ih.wX
    wG := Wire.lastCases (fun _ => false) ih.wG
    causal := ih.causal
    gFn_eq := ih.gFn_eq
    trace_eq := fun w x => ?_ }⟩
  refine Wire.lastCases ?_ (fun w₀ => ?_) w
  · change (q.gate ⟨Op.one, wires⟩).eval interpretation x (Fin.last g) = _
    rw [Program.eval_gate_last]
    unfold linForm
    simp [Line.eval, Wire.lastCases]
  · rw [Program.trace_gate_castSucc, ih.trace_eq w₀ x]
    cases w₀ <;> simp [Wire.lastCases]

private theorem progDecomp_xor {n g k : ℕ} {q : Program signature n g}
    (ih : ProgDecomp q k) (wires : Fin (signature.Arity Op.xor) → Wire n g) :
    Nonempty (ProgDecomp (q.gate ⟨Op.xor, wires⟩) k) := by
  let u₀ := wires 0
  let u₁ := wires 1
  refine ⟨{
    gFn := ih.gFn
    cH := ih.cH
    aX := ih.aX
    aG := ih.aG
    cW := Wire.lastCases (ih.cW u₀ + ih.cW u₁) ih.cW
    wX := Wire.lastCases (fun j => ih.wX u₀ j + ih.wX u₁ j) ih.wX
    wG := Wire.lastCases (fun ℓ => ih.wG u₀ ℓ + ih.wG u₁ ℓ) ih.wG
    causal := ih.causal
    gFn_eq := ih.gFn_eq
    trace_eq := fun w x => ?_ }⟩
  refine Wire.lastCases ?_ (fun w₀ => ?_) w
  · change (q.gate ⟨Op.xor, wires⟩).eval interpretation x (Fin.last g) = _
    rw [Program.eval_gate_last]
    change (q.trace interpretation x u₀ + q.trace interpretation x u₁) = _
    rw [ih.trace_eq u₀ x, ih.trace_eq u₁ x, ← linForm_add]
    simp [Wire.lastCases]
  · rw [Program.trace_gate_castSucc, ih.trace_eq w₀ x]
    cases w₀ <;> simp [Wire.lastCases]

private theorem progDecomp_and {n g k : ℕ} {q : Program signature n g}
    (ih : ProgDecomp q k) (wires : Fin (signature.Arity Op.and) → Wire n g) :
    Nonempty (ProgDecomp (q.gate ⟨Op.and, wires⟩) (k + 1)) := by
  let u₀ := wires 0
  let u₁ := wires 1
  let gLast : BooleanFunction n := fun x =>
    q.trace interpretation x u₀ && q.trace interpretation x u₁
  let gFn' : Fin (k + 1) → BooleanFunction n := Fin.snoc ih.gFn gLast
  let cH' : Fin (2 * (k + 1)) → Bool := fun r =>
    if hr : r.1 < 2 * k then ih.cH ⟨r.1, hr⟩
    else if r.1 = 2 * k then ih.cW u₀ else ih.cW u₁
  let aX' : Fin (2 * (k + 1)) → Fin n → Bool := fun r =>
    if hr : r.1 < 2 * k then ih.aX ⟨r.1, hr⟩
    else if r.1 = 2 * k then ih.wX u₀ else ih.wX u₁
  let aG' : Fin (2 * (k + 1)) → Fin (k + 1) → Bool := fun r =>
    if hr : r.1 < 2 * k then Fin.snoc (ih.aG ⟨r.1, hr⟩) false
    else if r.1 = 2 * k then Fin.snoc (ih.wG u₀) false
    else Fin.snoc (ih.wG u₁) false
  refine ⟨{
    gFn := gFn'
    cH := cH'
    aX := aX'
    aG := aG'
    cW := Wire.lastCases false ih.cW
    wX := Wire.lastCases (fun _ => false) ih.wX
    wG := Wire.lastCases (fun ℓ => decide (ℓ = Fin.last k))
      (fun w₀ => Fin.snoc (ih.wG w₀) false)
    causal := fun r => Fin.lastCases
      (fun _ => by
        dsimp only [aG']
        split_ifs <;> exact Fin.snoc_last _ _)
      (fun j hle => by
        simp only [Fin.val_castSucc] at hle
        have hr : r.1 < 2 * k := by have := j.isLt; omega
        dsimp only [aG']
        simp only [hr, ↓reduceDIte, Fin.snoc_castSucc]
        exact ih.causal ⟨r.1, hr⟩ j hle)
    gFn_eq := fun i x => ?_
    trace_eq := fun w x => ?_ }⟩
  · refine Fin.lastCases ?_ (fun j => ?_) i
    · have h1_not : ¬ (2 * k + 1 < 2 * k) := by omega
      have h1_ne : 2 * k + 1 ≠ 2 * k := by omega
      dsimp only [gFn', cH', aX', aG']
      simp only [Fin.snoc_last, Fin.val_last, lt_irrefl, h1_not, h1_ne, ↓reduceDIte, ↓reduceIte,
        linForm_snoc_false, ← ih.trace_eq u₀ x, ← ih.trace_eq u₁ x]
      rfl
    · have hj : j.castSucc.1 < k := j.isLt
      have hj0 : 2 * j.castSucc.1 < 2 * k := by omega
      have hj1 : 2 * j.castSucc.1 + 1 < 2 * k := by omega
      dsimp only [gFn', cH', aX', aG']
      simp only [Fin.snoc_castSucc, hj0, hj1, ↓reduceDIte, linForm_snoc_false]
      exact ih.gFn_eq j x
  · refine Wire.lastCases ?_ (fun w₀ => ?_) w
    · change (q.gate ⟨Op.and, wires⟩).eval interpretation x (Fin.last g) = _
      rw [Program.eval_gate_last]
      change gLast x = _
      unfold linForm
      simp only [Wire.lastCases, Fin.lastCases_last, Bool.false_eq_true, ↓reduceIte, zero_add,
        sum_const_zero, decide_eq_true_eq]
      rw [sum_ite_eq']
      simp [gFn']
    · rw [Program.trace_gate_castSucc, ih.trace_eq w₀ x]
      have hw :
          Wire.lastCases false ih.cW w₀.castSucc = ih.cW w₀ ∧
            Wire.lastCases (fun _ => false) ih.wX w₀.castSucc = ih.wX w₀ ∧
            Wire.lastCases (fun ℓ => decide (ℓ = Fin.last k))
              (fun v => Fin.snoc (ih.wG v) false) w₀.castSucc = Fin.snoc (ih.wG w₀) false := by
        cases w₀ <;> simp [Wire.lastCases]
      rw [hw.1, hw.2.1, hw.2.2, linForm_snoc_false]

private theorem exists_progDecomp {n g : ℕ} (p : Program signature n g) :
    Nonempty (ProgDecomp p (p.cost andCost)) := by
  induction p with
  | empty => exact progDecomp_empty n
  | gate q line ih =>
    obtain ⟨d⟩ := ih
    rcases line with ⟨op, wires⟩
    cases op with
    | one =>
      have hk : (q.gate ⟨Op.one, wires⟩).cost andCost = q.cost andCost := by simp
      exact hk ▸ progDecomp_one d wires
    | xor =>
      have hk : (q.gate ⟨Op.xor, wires⟩).cost andCost = q.cost andCost := by simp
      exact hk ▸ progDecomp_xor d wires
    | and =>
      have hk : (q.gate ⟨Op.and, wires⟩).cost andCost = q.cost andCost + 1 := by simp
      exact hk ▸ progDecomp_and d wires

/-- `M`-padded causal affine decomposition of a `{⊕, ∧, 1}`-circuit computing `f`. -/
structure PaddedDecomp {n : ℕ} (f : BooleanFunction n) (M k : ℕ) where
  /-- Padded Boolean functions computed by conjunction gates `0 .. M - 1`. -/
  gFn : Fin M → BooleanFunction n
  /-- Constant bits of the `2 * M` padded conjunction input linear forms. -/
  cH : Fin (2 * M) → Bool
  /-- Input-variable coefficients of the `2 * M` padded conjunction input linear forms. -/
  aX : Fin (2 * M) → Fin n → Bool
  /-- Prior conjunction-gate coefficients of the `2 * M` padded input linear forms. -/
  aG : Fin (2 * M) → Fin M → Bool
  /-- Constant bit of the output linear form computing `f`. -/
  outC : Bool
  /-- Input-variable coefficients of the output linear form computing `f`. -/
  outX : Fin n → Bool
  /-- Conjunction-gate coefficients of the output linear form computing `f`. -/
  outG : Fin M → Bool
  causal : ∀ (r : Fin (2 * M)) (ℓ : Fin M), r.1 / 2 ≤ ℓ.1 → aG r ℓ = false
  gFn_lt : ∀ (i : Fin M), i.1 < k → ∀ x : Fin n → Bool,
    gFn i x =
      (linForm (cH ⟨2 * i.1, by omega⟩) (aX ⟨2 * i.1, by omega⟩)
          (aG ⟨2 * i.1, by omega⟩) gFn x &&
        linForm (cH ⟨2 * i.1 + 1, by omega⟩) (aX ⟨2 * i.1 + 1, by omega⟩)
          (aG ⟨2 * i.1 + 1, by omega⟩) gFn x)
  gFn_ge : ∀ (i : Fin M), k ≤ i.1 → gFn i = constZero n
  out_eq : ∀ x : Fin n → Bool, f x = linForm outC outX outG gFn x

/-- Zero-pads a length-`k` Boolean vector to length `M`. -/
@[expose] def padBool {k M : ℕ} (v : Fin k → Bool) (ℓ : Fin M) : Bool :=
  if h : ℓ.1 < k then v ⟨ℓ.1, h⟩ else false

/-- Zero-pads a length-`k` family of `n`-ary Boolean functions to length `M`. -/
@[expose] def padFn {n k M : ℕ} (gFn : Fin k → BooleanFunction n) (ℓ : Fin M) : BooleanFunction n :=
  if h : ℓ.1 < k then gFn ⟨ℓ.1, h⟩ else constZero n

theorem linForm_pad {n k M : ℕ} (hkM : k ≤ M) (c₀ : Bool) (cX : Fin n → Bool)
    (cG : Fin k → Bool) (gFn : Fin k → BooleanFunction n) (x : Fin n → Bool) :
    linForm c₀ cX (padBool (M := M) cG) (padFn (M := M) gFn) x = linForm c₀ cX cG gFn x := by
  unfold linForm
  congr 1
  have hsub : (univ.map (Fin.castLEEmb hkM)) ⊆ (univ : Finset (Fin M)) := subset_univ _
  rw [← sum_subset hsub]
  · rw [sum_map]
    refine sum_congr rfl fun i _ => ?_
    simp [padBool, padFn, i.isLt]
  · intro ℓ _ hnot
    have hge : ¬ (ℓ.1 < k) := by
      intro hlt
      exact hnot (mem_map.mpr ⟨⟨ℓ.1, hlt⟩, mem_univ _, Fin.ext rfl⟩)
    simp [padBool, hge]

theorem exists_paddedDecomp {n M : ℕ} {f : BooleanFunction n} (c : Circuit signature n 1)
    (hc : c.Computes interpretation (single f)) (hkM : c.program.cost andCost ≤ M) :
    Nonempty (PaddedDecomp f M (c.program.cost andCost)) := by
  let k := c.program.cost andCost
  obtain ⟨pd⟩ := exists_progDecomp c.program
  let outW := c.outputs 0
  refine ⟨{
    gFn := padFn (M := M) pd.gFn
    cH := fun r => if hr : r.1 < 2 * k then pd.cH ⟨r.1, hr⟩ else false
    aX := fun r => if hr : r.1 < 2 * k then pd.aX ⟨r.1, hr⟩ else fun _ => false
    aG := fun r =>
      if hr : r.1 < 2 * k then padBool (M := M) (pd.aG ⟨r.1, hr⟩) else fun _ => false
    outC := pd.cW outW
    outX := pd.wX outW
    outG := padBool (M := M) (pd.wG outW)
    causal := fun r ℓ hle => ?_
    gFn_lt := fun i hi x => ?_
    gFn_ge := fun i hi => ?_
    out_eq := fun x => ?_ }⟩
  · split_ifs with hr
    · unfold padBool
      split_ifs with hℓ
      · exact pd.causal ⟨r.1, hr⟩ ⟨ℓ.1, hℓ⟩ hle
      · rfl
    · rfl
  · have hr0 : 2 * i.1 < 2 * k := by omega
    have hr1 : 2 * i.1 + 1 < 2 * k := by omega
    dsimp only [padFn]
    simp only [hi, hr0, hr1, ↓reduceDIte, linForm_pad hkM]
    exact pd.gFn_eq ⟨i.1, hi⟩ x
  · have hnot : ¬ (i.1 < c.program.cost andCost) := Nat.not_lt.mpr hi
    simp only [padFn, hnot, ↓reduceDIte]
  · have heval : c.eval interpretation x 0 = f x := congrFun (hc x) 0
    rw [← heval]
    change c.program.trace interpretation x outW = _
    rw [pd.trace_eq outW x, linForm_pad hkM]

end Decomposition

end Cslib.Circuits.Boolean.Zhegalkin
