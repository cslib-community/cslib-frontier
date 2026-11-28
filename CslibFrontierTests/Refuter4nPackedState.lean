/-
Copyright (c) 2026 Christian Reitwiessner, Ryan Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Ryan Anderson
-/

module
-- upstream: local-only (test)

public import CslibFrontier.Algorithms.WordRAM.Refuter4n.PackedState
public meta import CslibFrontier.Algorithms.WordRAM.Refuter4n.PackedState
public import CslibFrontier.Computability.Circuit.Boolean.AffineDisperser4n

/-!
# Tests for the packed state of the `4n - 9d` refuter
-/

set_option linter.hashCommand false

public section

namespace CslibFrontierTests.Refuter4nPackedState

open Cslib Cslib.BitString Cslib.Circuits Cslib.Circuits.Boolean
open Cslib.Circuits.Boolean.AffineDisperser4n Cslib.Circuits.Boolean.SemiCircuit
open Cslib.Algorithms.WordRAM.Refuter4n

/-- A `0`-gate circuit on `2` bits: the output is `x₀`. -/
def projCircuit : Circuit (fullSignature 2 Bool) 2 1 :=
  ⟨Program.empty, fun _ => Wire.input ⟨0, by decide⟩⟩

/-- One XOR gate on `3` bits (gate name `3`). -/
def xor3Circuit : Circuit (fullSignature 2 Bool) 3 1 :=
  ⟨Program.gate Program.empty
    ⟨FullOp.fn fun xs => xs 0 ^^ xs 1,
      fun i => if _ : i.val = 0 then Wire.input ⟨0, by decide⟩ else Wire.input ⟨1, by decide⟩⟩,
    fun _ => Wire.gate ⟨0, by decide⟩⟩

/-- Two gates on `2` bits: `g₀ = x₀ ∧ x₁` (name `2`) and the degenerate `g₁ = g₀ ∨ g₀`
(name `3`). -/
def degCircuit : Circuit (fullSignature 2 Bool) 2 1 :=
  let p1 := (Program.empty : Program (fullSignature 2 Bool) 2 0).gate ⟨FullOp.fn fun xs =>
    xs 0 && xs 1,
    fun i => if _ : i.val = 0 then Wire.input ⟨0, by decide⟩ else Wire.input ⟨1, by decide⟩⟩
  let p2 := p1.gate ⟨FullOp.fn fun xs => xs 0 || xs 1, fun _ => Wire.gate ⟨0, by decide⟩⟩
  ⟨p2, fun _ => Wire.gate ⟨1, by decide⟩⟩

/-! Table sizes of the layout: `N = n + C.size` and `E = 5 n + 7 C.size`. -/

#guard nameBound projCircuit == 2 && eqnBound projCircuit == 10
#guard nameBound xor3Circuit == 4 && eqnBound xor3Circuit == 22
#guard nameBound degCircuit == 4 && eqnBound degCircuit == 24

/-! Encodings: masks, gate rows (`xor` has truth table `0110₂ = 6`), the output literal
`2 · (3 + 2) + 0 = 10`, and the identity rows `2 ^ i` of the parameter map. -/

#guard maskOf {0, 2, 5} == 37
#guard ttOf (· ^^ ·) == 6
#guard ttOf (· && ·) == 8
#guard (initialPacked xor3Circuit).params == 7
#guard (initialPacked xor3Circuit).gates == 8
#guard (initialPacked xor3Circuit).gateRows.length == 4
#guard (initialPacked xor3Circuit).gateRows.getD 3 ⟨0, 0, 0⟩ == ⟨6, 2, 3⟩
#guard (initialPacked xor3Circuit).out == 10
#guard (initialPacked xor3Circuit).phiRows == [1, 2, 4]
#guard (initialPacked xor3Circuit).eqnRows.length == 22
#guard (initialPacked xor3Circuit).pairs.isEmpty

/-! The equation word: terms `{0, 2}`, right-hand side `true`, alive, at `N = 4`:
`0b1_1_0101 = 53`; masking off the alive bit gives the dense row word. -/

#guard eqnWord 4 ⟨{0, 2}, true⟩ true == 53
#guard eqnWord 4 ⟨{0, 2}, true⟩ true % 2 ^ 5 ==
  Cslib.Algorithms.WordRAM.XORSATDense.rowWord (toDenseRow 4 {0, 2} true)

/-! Sorted searches as mask scans: an empty set (no hit) and `{1, 3}` (first name above `2`). -/

#guard ((∅ : Finset ℕ).sort (· ≤ ·)).findSome? (fun i => if 2 < i then some i else none) == none
#guard (List.range 4).findSome?
  (fun i => if (maskOf ∅).testBit i then (if 2 < i then some i else none) else none) == none
#guard (({1, 3} : Finset ℕ).sort (· ≤ ·)).findSome? (fun i => if 2 < i then some i else none) ==
  some 3
#guard (List.range 4).findSome?
  (fun i => if (maskOf {1, 3}).testBit i then (if 2 < i then some i else none) else none) ==
  some 3

/-- `findSome?` over the sorted set `{1, 3}` is the scan of its mask below `4` (module client of
`findSome?_sort_eq_findSome?_range`). -/
example (g : ℕ → Option ℕ) :
    (({1, 3} : Finset ℕ).sort (· ≤ ·)).findSome? g =
      (List.range 4).findSome? fun i => if (maskOf {1, 3}).testBit i then g i else none :=
  findSome?_sort_eq_findSome?_range (N := 4)
    (fun i hi => by simp only [Finset.mem_insert, Finset.mem_singleton] at hi; omega) g

/-! Explicit rows: substituting `x₁ := x₀ + 1` in the row `x₁ + x₂` gives `x₀ + x₂ + 1`. -/

#guard substWord 1 (litWord 3 ⟨.node 0, true⟩) 6 == 13
#guard (List.range 8).all fun v =>
  let val := fun j => v.testBit j
  rowEval 3 (substWord 1 (litWord 3 ⟨.node 0, true⟩) 6) val ==
    rowEval 3 6 (Function.update val 1 (val 0 ^^ true))

/-! Explicit rows of the parameter map after a restriction `x₁ := ¬x₀` and a reparameterisation
`x₀ := x₂ + x₁ + 1` of the initial state of `xor3Circuit`: on all `8` assignments of the
parameters, every output bit of `phi` is the value of its updated row. -/

#guard (List.range 8).all fun v =>
  let val := fun j => v.testBit j
  (List.finRange 3).all fun i =>
    ((initialState xor3Circuit).restrict 1 ⟨.node 0, true⟩ ∅).phi val i ==
      rowEval 4 (((initialPacked xor3Circuit).phiRows.map
        (substWord 1 (litWord 4 ⟨.node 0, true⟩))).getD i 0) val
#guard (List.range 8).all fun v =>
  let val := fun j => v.testBit j
  (List.finRange 3).all fun i =>
    ((initialState xor3Circuit).swap 0 2 true {0, 1}).phi val i ==
      rowEval 4 (((initialPacked xor3Circuit).phiRows.map
        (substWord 0 (Cslib.Algorithms.WordRAM.XORSATDense.rowWord
          (toDenseRow 4 (symmDiff (({0, 1} : Finset ℕ).erase 0) {2}) true)))).getD i 0) val

/-- Restriction updates the rows of the packed initial state (module client of
`PhiWords.restrict`). -/
example : PhiWords 4 ((initialPacked xor3Circuit).phiRows.map
      (substWord 1 (litWord 4 ⟨.node 0, true⟩)))
    ((initialState xor3Circuit).restrict 1 ⟨.node 0, true⟩ ∅) :=
  (rep_initialPacked xor3Circuit).phi.restrict (by decide)
    (fun y hy => by simp only [Lit.Reads, Arg.node.injEq] at hy; subst hy; decide) ∅

/-- Reparameterisation updates the rows of the packed initial state (module client of
`PhiWords.swap`). -/
example : PhiWords 4 ((initialPacked xor3Circuit).phiRows.map
      (substWord 0 (Cslib.Algorithms.WordRAM.XORSATDense.rowWord
        (toDenseRow 4 (symmDiff (({0, 1} : Finset ℕ).erase 0) {2}) true))))
    ((initialState xor3Circuit).swap 0 2 true {0, 1}) :=
  (rep_initialPacked xor3Circuit).phi.swap (by decide) (by decide)
    (fun j hj => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      rcases hj with rfl | rfl <;> decide) true

/-! The `(D1)` client: no degenerate gate in the initial states of `projCircuit` (no gates) and
`xor3Circuit`, and the degenerate gate `3` in `degCircuit`, matching `findD1`. -/

#guard pFindD1 (initialPacked projCircuit) == findD1 (initialState projCircuit)
#guard pFindD1 (initialPacked xor3Circuit) == findD1 (initialState xor3Circuit)
#guard pFindD1 (initialPacked degCircuit) == findD1 (initialState degCircuit)
#guard (pFindD1 (initialPacked projCircuit)).isNone
#guard (pFindD1 (initialPacked xor3Circuit)).isNone
#guard pFindD1 (initialPacked degCircuit) == some 3

/-- The function computed by `xor3Circuit`. -/
private def xor3Fn : BooleanFunction 3 := fun x => x 0 ^^ x 1

/-- The initial state of `xor3Circuit` is valid for `xor3Fn`. -/
private theorem xor3_valid : (initialState xor3Circuit).Valid xor3Fn :=
  initialState_valid (by intro x; ext i; rw [Fin.eq_zero i]; rfl)

/-- The packed initial state represents the initial state (module client of
`rep_initialPacked`). -/
example : Rep 4 22 (initialPacked xor3Circuit) (initialState xor3Circuit) :=
  rep_initialPacked xor3Circuit

/-- Every word of the packed initial state fits at width `6 = N + 2`. -/
example : (initialPacked xor3Circuit).Fits 6 :=
  (rep_initialPacked xor3Circuit).fits xor3_valid (by decide) (by decide)

/-- The packed initial state has at most `N = 4` pair records. -/
example : (initialPacked xor3Circuit).pairs.length ≤ 4 :=
  (rep_initialPacked xor3Circuit).length_pairs_le xor3_valid

/-- The packed `(D1)` search agrees with `findD1` on every represented state. -/
example {n N E : ℕ} {P : PackedState} {S : State n} (h : Rep N E P S) :
    pFindD1 P = findD1 S :=
  h.pFindD1_eq

end CslibFrontierTests.Refuter4nPackedState
