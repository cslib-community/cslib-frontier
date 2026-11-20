/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.Garbling.Conventional
public import CslibFrontier.Crypto.Primitives.Garbling.FreeXOR
public import CslibFrontier.Crypto.Primitives.Garbling.PointPermute
public import CslibFrontier.Crypto.Primitives.Garbling.PointPermute.Simulator
import CslibFrontier.Crypto.Primitives.Garbling.HalfGates.Scheme

/-!
# Shared zero-label and active-label propagation on words

The topology-and-flag propagation traversal `simPropWords` shared between the Free-XOR garbler
(`CslibFrontier.Crypto.Primitives.Garbling.FreeXOR.Scheme`) and simulator
(`CslibFrontier.Crypto.Primitives.Garbling.FreeXOR.Simulator`), together with its word-length bounds
and word-to-typed correctness lemma (`simPropWords_eq_propagate`).

The garbler supplies the coin tape after the `k + 1` offset bits and the XOR flags computed from its
gates (`List.ofFn (isXorGate f)`), while the simulator supplies its raw coin tape and the XOR flags
from side information.

## Main definitions

* `Cslib.Crypto.Garbling.FreeXOR.isXorGate`: whether a gate of a conventional circuit computes XOR.
* `Cslib.Crypto.Garbling.FreeXOR.freeCircuit`: whether each gate of `toCircuit f` is free.
* `Cslib.Crypto.Garbling.FreeXOR.simPropWords`: propagate `(k + 2)`-bit wire labels over a topology
  and gate flag list from a coin tape.
* `Cslib.Crypto.Garbling.FreeXOR.simBaseLabels`: typed base labels read from a coin tape.

## Main results

* `Cslib.Crypto.Garbling.FreeXOR.length_simPropWords`: after `s ≤ t.q` gates, `simPropWords` holds
  `t.n + s` words.
* `Cslib.Crypto.Garbling.FreeXOR.length_le_of_mem_simPropWords`: every word in `simPropWords` has
  at most `k + 2` bits.
* `Cslib.Crypto.Garbling.FreeXOR.simPropWords_eq_propagate`: `simPropWords` matches the typed
  `propagate` labelling on `toCircuit f` whenever the flag list agrees with `isXorGate` on `Fin q`.
-/

public section

namespace Cslib.Crypto.Garbling.FreeXOR

open Cslib.Circuits ConventionalCircuit

/-- Whether gate `g` of `f` computes XOR. -/
@[expose] def isXorGate (f : ConventionalCircuit) (g : Fin f.q) : Bool :=
  decide (f.G g = xor)

/-- Whether each gate of `toCircuit f` is free (computes XOR). -/
@[expose] noncomputable def freeCircuit (f : ValidCircuit) : Fin (toCircuit f).size → Bool :=
  fun g => isXorGate f.1 (g.cast (size_toCircuit f))

/-- The wire label words of the first `n + s` wires read/propagated from `coins` over topology `t`
and XOR flags `free`: inputs and non-XOR gates read `PointPermute.simLabel k coins`, and XOR gates
add their arguments' labels. -/
@[expose] def simPropWords (k : ℕ) (t : Topo) (free : List Bool) (coins : List Bool) :
    ℕ → List (List Bool)
  | 0 => List.ofFn fun i : Fin t.n => PointPermute.simLabel k coins i
  | s + 1 =>
    if h : s < t.q then
      let ws := simPropWords k t free coins s
      ws ++ [if free.getD s false then
        List.zipWith xor (ws.getD (t.A ⟨s, h⟩ - 1) []) (ws.getD (t.B ⟨s, h⟩ - 1) [])
      else PointPermute.simLabel k coins (t.n + s)]
    else simPropWords k t free coins s

/-- A base label read from `coins` at wire `w`. -/
@[expose] def simBaseLabels {n s : ℕ} (k : ℕ) (coins : List Bool) (w : Wire n s) :
    BitString (k + 1) × Bool :=
  labelOfWord k (PointPermute.simLabel k coins w.toNat)

/-- After `s ≤ t.q` gates, `simPropWords` holds `t.n + s` label words. -/
theorem length_simPropWords (k : ℕ) (t : Topo) (free : List Bool) (coins : List Bool)
    {s : ℕ} (hs : s ≤ t.q) : (simPropWords k t free coins s).length = t.n + s := by
  induction s with
  | zero => simp [simPropWords]
  | succ s ih =>
    rw [simPropWords, dite_eq_left (show s < t.q by omega), List.length_append, ih (by omega)]
    rfl

/-- Every word in `simPropWords k t free coins s` has length at most `k + 2`. -/
theorem length_le_of_mem_simPropWords (k : ℕ) (t : Topo) (free : List Bool)
    (coins : List Bool) (s : ℕ) :
    ∀ w ∈ simPropWords k t free coins s, w.length ≤ k + 2 := by
  induction s with
  | zero =>
    intro w hw
    simp only [simPropWords, List.mem_ofFn] at hw
    obtain ⟨i, rfl⟩ := hw
    simp [PointPermute.length_simLabel]
  | succ s ih =>
    rw [simPropWords]
    by_cases hsq : s < t.q
    · rw [dite_eq_left hsq]
      intro w hw
      rcases List.mem_append.mp hw with hw | hw
      · exact ih w hw
      · rw [List.mem_singleton.mp hw]
        split
        · have ha :
              ((simPropWords k t free coins s).getD (t.A ⟨s, hsq⟩ - 1) []).length ≤ k + 2 := by
            rw [List.getD_eq_getElem?_getD]
            cases h : (simPropWords k t free coins s)[t.A ⟨s, hsq⟩ - 1]? with
            | none => simp
            | some v => exact ih v (List.mem_of_getElem? h)
          rw [List.length_zipWith]
          omega
        · simp [PointPermute.length_simLabel]
    · rw [dite_eq_right hsq]
      exact ih

/-- On a valid circuit `f` and any flag list `free` agreeing with `isXorGate f.1` on `Fin f.1.q`,
the first `n + s` words of `simPropWords` are the typed propagated `simBaseLabels`. -/
theorem simPropWords_eq_propagate (k : ℕ) (f : ValidCircuit) (free : List Bool)
    (coins : List Bool) (hfree : ∀ g : Fin f.1.q, free.getD g false = isXorGate f.1 g)
    {s : ℕ} (hs : s ≤ f.1.q) :
    simPropWords k f.1.topo free coins s =
      (List.ofFn fun v : Fin (f.1.n + (toCircuit f).size) =>
        labelBits (propagate (toCircuit f).topology (freeCircuit f)
          (simBaseLabels k coins) (Wire.ofNat v v.isLt))).take (f.1.n + s) := by
  have hτ := (toCircuit f).isOrdered_topology
  induction s with
  | zero =>
    simp only [ConventionalCircuit.topo]
    apply List.ext_getElem (by simp [simPropWords])
    intro i h₁ h₂
    simp only [simPropWords, List.length_ofFn] at h₁
    have hin : (Wire.ofNat i (by omega) : Wire f.1.n (toCircuit f).size) = .input ⟨i, h₁⟩ :=
      Wire.toNat_injective (by simp)
    simp only [simPropWords, List.getElem_ofFn, List.getElem_take, hin,
      propagate_input hτ, simBaseLabels, Wire.toNat_input,
      labelBits_labelOfWord (PointPermute.length_simLabel k coins _)]
  | succ s ih =>
    have hsq : s < f.1.q := hs
    have hsize := size_toCircuit f
    set g : Fin (toCircuit f).size := ⟨s, by omega⟩ with hg
    have hgcast : g.cast (size_toCircuit f) = ⟨s, hsq⟩ := Fin.ext rfl
    have hA₁ := f.2.one_le_A ⟨s, hsq⟩
    have hAB := f.2.A_lt_B ⟨s, hsq⟩
    have hBg := f.2.B_lt_gate ⟨s, hsq⟩
    simp only [ConventionalCircuit.topo] at hA₁ hAB hBg ih ⊢
    rw [simPropWords, dite_eq_left hsq]
    dsimp only
    rw [ih hsq.le, ← Nat.add_assoc, List.take_add_one, List.getElem?_ofFn]
    have hgate : (Wire.ofNat (f.1.n + s) (by omega) : Wire f.1.n (toCircuit f).size) =
        .gate g := Wire.toNat_injective (by simp [hg])
    simp only [show f.1.n + s < f.1.n + (toCircuit f).size by omega, dite_true,
      Option.toList_some, hgate]
    congr 1
    have hfree_eq : free.getD s false = freeCircuit f g := by
      simpa [freeCircuit, hgcast] using hfree ⟨s, hsq⟩
    rw [hfree_eq]
    by_cases hfr : freeCircuit f g = true
    · rw [ite_eq_left hfr, propagate_gate_of_free hτ (simBaseLabels k coins) hfr,
        ← Fin.sum_congr' _ (arity_topology_toCircuit f g).symm, Fin.sum_univ_two, labelBits_add]
      have hl := wires_toCircuit_zero f g (by rw [hgcast]; omega)
      have hr := wires_toCircuit_one f g (by rw [hgcast]; omega)
      simp only [hgcast] at hl hr
      rw [hl, hr,
        HalfGates.getD_take_labels (propagate (toCircuit f).topology (freeCircuit f)
          (simBaseLabels k coins)) (by omega) (by omega),
        HalfGates.getD_take_labels (propagate (toCircuit f).topology (freeCircuit f)
          (simBaseLabels k coins)) (by omega) (by omega)]
    · have hfr' : freeCircuit f g = false := Bool.eq_false_iff.mpr hfr
      rw [ite_eq_right hfr, propagate_gate_of_not_free hτ (simBaseLabels k coins) hfr',
        simBaseLabels, Wire.toNat_gate, hg,
        labelBits_labelOfWord (PointPermute.length_simLabel k coins _)]

end Cslib.Crypto.Garbling.FreeXOR
