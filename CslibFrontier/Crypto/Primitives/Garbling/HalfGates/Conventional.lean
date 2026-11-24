/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.Garbling.Conventional
public import CslibFrontier.Crypto.Primitives.Garbling.Efficient
public import CslibFrontier.Crypto.Primitives.Garbling.HalfGates
public import CslibFrontier.Computability.Circuit.MapOp
import CslibFrontier.Computability.Circuit.Encoding.MapOp

/-!
# XOR–AND conventional circuits as half-gates circuits

Half-gates garbling [ZahurRosulekEvans2015] garbles circuits whose gates all compute XOR or AND
(Figure 2, p. 9, which assumes "all gates are either AND or XOR"). `XorAndCircuit` is the type of
valid conventional circuits of Bellare, Hoang and Rogaway [BellareHoangRogaway2012] whose truth
tables are all XOR or AND (`ConventionalCircuit.IsXorAnd`). It is a decidable subtype of
`ValidCircuit`, encoded by `encValidCircuit` (`encXorAndCircuit`).

`HalfGates.toCircuit f : Circuit HalfGates.signature n m` is such a circuit over the XOR–AND basis:
gate `g` applies AND when `G g` is the AND table and XOR otherwise, to the 0-indexed wires
`A g - 1` and `B g - 1`, and output `o` is wire `n + q - m + o`. Translating it back to the full
binary basis along the meaning-preserving map `HalfGates.toFull` gives
`ConventionalCircuit.toCircuit f` (`HalfGates.mapOp_toCircuit`), so its gates, wires and outputs
are those of the conventional circuit, and it computes `ConventionalCircuit.evalCirc`
(`HalfGates.eval_toCircuit`).

## Main definitions

* `Cslib.Crypto.Garbling.ConventionalCircuit.IsXorAnd`, `Cslib.Crypto.Garbling.XorAndCircuit`,
  `Cslib.Crypto.Garbling.encXorAndCircuit`: XOR–AND conventional circuits and their words.
* `Cslib.Crypto.Garbling.HalfGates.toFull`: the XOR–AND basis inside the full binary basis.
* `Cslib.Crypto.Garbling.HalfGates.toCircuit`: an XOR–AND conventional circuit as a half-gates
  circuit.

## Main results

* `Cslib.Crypto.Garbling.HalfGates.mapOp_toCircuit`: translated to the full binary basis it is
  `ConventionalCircuit.toCircuit`.
* `Cslib.Crypto.Garbling.HalfGates.eval_toCircuit`: it computes `evalCirc`.

## References

* [S. Zahur, M. Rosulek, D. Evans, *Two Halves Make a Whole: Reducing Data Transfer in Garbled
  Circuits using Half Gates*][ZahurRosulekEvans2015]
* [M. Bellare, V. T. Hoang, P. Rogaway, *Foundations of Garbled Circuits*][BellareHoangRogaway2012]
-/

public section

namespace Cslib.Crypto.Garbling

open Cslib.Circuits

namespace ConventionalCircuit

/-- Every gate of `f` computes XOR or AND. -/
@[expose] def IsXorAnd (f : ConventionalCircuit) : Prop :=
  ∀ g, f.G g = xor ∨ f.G g = and

instance (f : ConventionalCircuit) : Decidable f.IsXorAnd := by
  unfold IsXorAnd
  infer_instance

end ConventionalCircuit

/-- Valid conventional circuits whose gates all compute XOR or AND: the circuits that half-gates
garbling garbles. -/
abbrev XorAndCircuit : Type := {f : ValidCircuit // f.val.IsXorAnd}

/-- The conventional circuit of an XOR–AND circuit. -/
abbrev XorAndCircuit.circuit (f : XorAndCircuit) : ConventionalCircuit := f.val.val

/-- The conventional circuit of an XOR–AND circuit is valid. -/
theorem XorAndCircuit.isValid (f : XorAndCircuit) : f.circuit.IsValid := f.val.property

/-- Every gate of an XOR–AND circuit computes XOR or AND. -/
theorem XorAndCircuit.isXorAnd (f : XorAndCircuit) : f.circuit.IsXorAnd := f.property

/-- XOR–AND circuits as words, by `encValidCircuit`. -/
def encXorAndCircuit : XorAndCircuit ↪ List Bool :=
  (Function.Embedding.subtype _).trans encValidCircuit

/-- An XOR–AND circuit is written as its valid circuit. -/
theorem encXorAndCircuit_apply (f : XorAndCircuit) :
    encXorAndCircuit f = encValidCircuit f.val := by
  simp only [encXorAndCircuit, Function.Embedding.trans_apply, Function.Embedding.coe_subtype]

/-- An XOR–AND circuit is written as its valid circuit, so reading the valid circuit costs
nothing. -/
theorem XorAndCircuit.val_polyTime :
    Turing.MultiTapeTM.ComputableInPolyTime (fun f : XorAndCircuit => f.val) encXorAndCircuit
      encValidCircuit :=
  .of_eq fun _ => rfl

namespace HalfGates

/-- The XOR–AND basis inside the full binary basis: XOR and AND as their truth tables. -/
@[expose] def toFull : signature.Hom (fullSignature 2 Bool) where
  toFun
    | .xor => .fn fun a => xor (a 0) (a 1)
    | .and => .fn fun a => and (a 0) (a 1)
  arity_eq op := by cases op <;> rfl

instance : toFull.Preserves interpretation fullInterpretation :=
  ⟨by rintro (_ | _) x <;> rfl⟩

/-- The half-gates operation of a truth table `G` of XOR or AND: AND when `G 1 1` is set, XOR
otherwise. -/
@[expose] def opOf (G : Bool → Bool → Bool) : Op := if G true true then .and else .xor

/-- The gates of a conventional circuit as circuit code over the XOR–AND basis: gate `i` applies
`opOf (G i)` to the 0-indexed wires `A i - 1` and `B i - 1`. -/
@[expose] def gateCode (f : ConventionalCircuit) : List (Op × List ℕ) :=
  List.ofFn fun i => (opOf (f.G i), [f.A i - 1, f.B i - 1])

/-- On an XOR–AND circuit, `toFull` sends the half-gates code to the full-basis code. -/
private theorem map_gateCode (f : XorAndCircuit) :
    (gateCode f.circuit).map (fun g => (toFull g.1, g.2)) =
      ConventionalCircuit.gateCode f.circuit := by
  simp only [gateCode, ConventionalCircuit.gateCode, List.map_ofFn]
  congr 1
  funext i
  simp only [Function.comp_apply]
  rcases f.isXorAnd i with h | h <;> rw [h] <;> rfl

/-- The code of an XOR–AND circuit decodes over the XOR–AND basis. -/
private theorem isSome_ofCode (f : XorAndCircuit) :
    (Circuit.ofCode f.circuit.n f.circuit.m
      (gateCode f.circuit, ConventionalCircuit.outputCode f.circuit) :
      Option (Circuit signature f.circuit.n f.circuit.m)).isSome := by
  have h := Circuit.isSome_ofCode_iff.mp (by
    rw [← ConventionalCircuit.code_toCircuit f.val, Circuit.ofCode_code]; rfl :
    (Circuit.ofCode f.circuit.n f.circuit.m
      (ConventionalCircuit.gateCode f.circuit, ConventionalCircuit.outputCode f.circuit) :
      Option (Circuit (fullSignature 2 Bool) f.circuit.n f.circuit.m)).isSome)
  obtain ⟨hcode, hlen, hout⟩ := h
  dsimp only at hcode hlen hout
  rw [← map_gateCode, List.length_map] at hout
  rw [← map_gateCode] at hcode
  exact Circuit.isSome_ofCode_iff.mpr ⟨(Program.isCodeFrom_map_iff toFull).mp hcode, hlen, hout⟩

/-- An XOR–AND conventional circuit as a circuit over the XOR–AND basis, decoded from its gate
list. -/
noncomputable def toCircuit (f : XorAndCircuit) : Circuit signature f.circuit.n f.circuit.m :=
  (Circuit.ofCode f.circuit.n f.circuit.m
    (gateCode f.circuit, ConventionalCircuit.outputCode f.circuit)).get
    (isSome_ofCode f)

/-- The code of `toCircuit f` is the half-gates gate list of `f` with its last `m` wires as
outputs. -/
theorem code_toCircuit (f : XorAndCircuit) :
    (toCircuit f).code = (gateCode f.circuit, ConventionalCircuit.outputCode f.circuit) :=
  Circuit.code_of_ofCode_eq_some (Option.some_get _).symm

/-- **Back in the full binary basis.** Translating `toCircuit f` along `toFull` gives the
conventional circuit's own translation `ConventionalCircuit.toCircuit f`. -/
theorem mapOp_toCircuit (f : XorAndCircuit) :
    (toCircuit f).mapOp toFull = ConventionalCircuit.toCircuit f.val :=
  Circuit.code_injective (by
    rw [Circuit.code_mapOp, code_toCircuit, ConventionalCircuit.code_toCircuit, map_gateCode])

/-- `toCircuit f` has the `q` gates of `f`. -/
theorem size_toCircuit (f : XorAndCircuit) : (toCircuit f).size = f.circuit.q := by
  rw [← Circuit.size_mapOp (φ := toFull), mapOp_toCircuit, ConventionalCircuit.size_toCircuit]

/-- Line `g` of `toCircuit f`, translated along `toFull`, has the code of line `g` of
`ConventionalCircuit.toCircuit f`. -/
private theorem code_lines_toCircuit (f : XorAndCircuit) (g : Fin (toCircuit f).size) :
    (toFull (op (toCircuit f) g), ((toCircuit f).program.lines g).code.2) =
      ((ConventionalCircuit.toCircuit f.val).program.lines (g.cast
        ((size_toCircuit f).trans (ConventionalCircuit.size_toCircuit f.val).symm))).code := by
  have h := congrArg Prod.fst ((Circuit.code_mapOp toFull (toCircuit f)).symm.trans
    (congrArg Circuit.code (mapOp_toCircuit f)))
  simp only [Circuit.code] at h
  rw [← Program.getD_code _ _ ((fun line : Op × List ℕ => (toFull line.1, line.2)) (.xor, [])),
    Fin.val_cast, ← h, List.getD_eq_getElem?_getD, List.getElem?_map, Option.getD_map,
    ← List.getD_eq_getElem?_getD, Program.getD_code]
  rfl

/-- Gate `g` of `toCircuit f` is an AND gate exactly when `G g` is the AND table. -/
theorem op_toCircuit (f : XorAndCircuit) (g : Fin (toCircuit f).size) :
    op (toCircuit f) g = opOf (f.circuit.G (g.cast (size_toCircuit f))) := by
  have h := (congrArg Prod.fst (code_lines_toCircuit f g)).trans
    (congrArg Line.op (ConventionalCircuit.lines_toCircuit f.val _))
  cases hop : op (toCircuit f) g <;> rw [hop] at h <;>
    have h11 := congrFun (FullOp.fn.inj h) fun _ => true <;>
    simp_all [opOf, Fin.cast_cast]

/-- The first argument of gate `g` of `toCircuit f` is the 0-indexed wire `A g - 1`. -/
theorem toNat_left_toCircuit (f : XorAndCircuit) (g : Fin (toCircuit f).size) :
    (left (toCircuit f) g).toNat = f.circuit.A (g.cast (size_toCircuit f)) - 1 := by
  have h := congrArg (fun code => code.getD 0 0)
    ((congrArg Prod.snd (code_lines_toCircuit f g)).trans
      (ConventionalCircuit.ofFn_toNat_wires_toCircuit f.val _))
  simpa [Line.code, left, List.getD_eq_getElem?_getD, Fin.cast_cast] using h

/-- The second argument of gate `g` of `toCircuit f` is the 0-indexed wire `B g - 1`. -/
theorem toNat_right_toCircuit (f : XorAndCircuit) (g : Fin (toCircuit f).size) :
    (right (toCircuit f) g).toNat = f.circuit.B (g.cast (size_toCircuit f)) - 1 := by
  have h := congrArg (fun code => code.getD 1 0)
    ((congrArg Prod.snd (code_lines_toCircuit f g)).trans
      (ConventionalCircuit.ofFn_toNat_wires_toCircuit f.val _))
  simpa [Line.code, right, List.getD_eq_getElem?_getD, Fin.cast_cast] using h

/-- Output `o` of `toCircuit f` is the 0-indexed wire `n + q - m + o`. -/
theorem toNat_outputs_toCircuit (f : XorAndCircuit) (o : Fin f.circuit.m) :
    ((toCircuit f).outputs o).toNat = f.circuit.n + f.circuit.q - f.circuit.m + o := by
  rw [← ConventionalCircuit.toNat_outputs_toCircuit f.val, ← mapOp_toCircuit]
  rfl

/-- The value of wire `w` of `toCircuit f` on an `n`-bit input is wire `w` of the conventional
evaluation, numbered from `0`. -/
theorem trace_toCircuit (f : XorAndCircuit) (x : Fin f.circuit.n → Bool)
    (w : Wire f.circuit.n (toCircuit f).size) :
    (toCircuit f).program.trace interpretation x w =
      (f.circuit.wires (List.ofFn x) f.circuit.q).getD w.toNat false := by
  have h : ∀ (c : Circuit (fullSignature 2 Bool) f.circuit.n f.circuit.m),
      c = ConventionalCircuit.toCircuit f.val → ∀ w : Wire f.circuit.n c.size,
        c.program.trace fullInterpretation x w =
          (f.circuit.wires (List.ofFn x) f.circuit.q).getD w.toNat false := by
    rintro c rfl w
    exact ConventionalCircuit.trace_toCircuit f.val x w
  refine Eq.trans ?_ (h _ (mapOp_toCircuit f) w)
  exact congrFun (congrArg (Wire.elim x) (Program.eval_mapOp (I := interpretation)
    (J := fullInterpretation) (toCircuit f).program x).symm) w

/-- **The translation computes the conventional semantics.** On every `n`-bit input, the outputs
of `toCircuit f` are `evalCirc f`. -/
theorem eval_toCircuit (f : XorAndCircuit) (x : Fin f.circuit.n → Bool) :
    List.ofFn ((toCircuit f).eval interpretation x) = f.circuit.evalCirc (List.ofFn x) := by
  rw [← Circuit.eval_mapOp (φ := toFull) (J := fullInterpretation), mapOp_toCircuit,
    ConventionalCircuit.eval_toCircuit]

end HalfGates

end Cslib.Crypto.Garbling
