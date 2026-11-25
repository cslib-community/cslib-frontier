/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.CarrySave
public import CslibFrontier.Computability.Circuit.Boolean.CodeTemplate
public import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Native generation of carry-save circuits

Fixed three-input formula templates generate each sum and carry bit. The lowest carry bit is a
constant, so the carry blocks have different gate counts. `appendCodes` assembles their actual
codes without padding. Composition then generates the existing four-to-two reducer.

The width is unary, and all emitted gate and output references are binary. These certificates
charge the full code and hold uniformly at every width, including zero.

## Main definitions

* `Cslib.Circuits.Boolean.csaSumCode`, `Cslib.Circuits.Boolean.csaCarryCode`: raw code templates
  for sum and carry bits.
* `Cslib.Circuits.Boolean.csa3to2Code`: raw code generation for the three-to-two reducer.
* `Cslib.Circuits.Boolean.csa4to2Code`: raw code generation for the four-to-two reducer.

## Main results

* `Cslib.Circuits.Boolean.csa3to2Code_eq_code`,
  `Cslib.Circuits.Boolean.csa4to2Code_eq_code`: exact agreement with the existing circuits.
* `Cslib.Circuits.Boolean.computableInPolyTime_csa3to2`,
  `Cslib.Circuits.Boolean.computableInPolyTime_csa4to2`: uniform native constructors.

## References

The underlying carry-save circuits are formalized in `Boolean.CarrySave`, following
[Chandra, Stockmeyer and Vishkin][ChandraStockmeyerVishkin1984] and
[Vollmer, Chapter 1][Vollmer1999].
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

open Turing.MultiTapeTM ComputableInPolyTime

private def sumTemplate : Formula signature 3 :=
  ((Formula.input 0).xor (.input 1)).xor (.input 2)

/-- The sum-bit formula instantiated at three raw input references. -/
def csaSumCode (w i : ℕ) : List (Op × List ℕ) × List ℕ :=
  formulaCode (w + (w + w)) (((Formula.input (n := 3) 0).xor (.input 1)).xor (.input 2))
    ![i, w + i, w + (w + i)]

/-- A carry-bit formula, including the constant lowest carry and total raw-index behavior. -/
def csaCarryCode (w i : ℕ) : List (Op × List ℕ) × List ℕ :=
  if 0 < i then
    formulaCode (w + (w + w)) (maj3Formula (0 : Fin 3) 1 2)
      ![i - 1, w + (i - 1), w + (w + (i - 1))]
  else ([(.const false, [])], [w + (w + w)])

private theorem csa_formulaCode_eq (f : Formula signature 3) (w : ℕ) (j : Fin w) :
    formulaCode (w + (w + w)) f ![j.val, w + j.val, w + (w + j.val)] =
      (f.rename ![Fin.castAdd (w + w) j, Fin.natAdd w (Fin.castAdd w j),
        Fin.natAdd w (Fin.natAdd w j)]).toCircuit.code := by
  let wires : Fin 3 → Fin (w + (w + w)) :=
    ![Fin.castAdd (w + w) j, Fin.natAdd w (Fin.castAdd w j), Fin.natAdd w (Fin.natAdd w j)]
  have hw : (fun k => (wires k).val) = ![j.val, w + j.val, w + (w + j.val)] := by
    funext k; fin_cases k <;> simp [wires, Nat.add_comm]
  exact hw ▸ formulaCode_eq_code f wires

private theorem csaSumCode_eq (w : ℕ) (i : Fin w) :
    csaSumCode w i.val = (csaSumFormula w i).toCircuit.code :=
  csa_formulaCode_eq sumTemplate w i

private theorem csaCarryCode_eq (w : ℕ) (i : Fin w) :
    csaCarryCode w i.val = (csaCarryFormula w i).toCircuit.code := by
  by_cases hi : 0 < i.val
  · simp only [csaCarryCode, csaCarryFormula, hi, ↓reduceIte, ↓reduceDIte]
    exact csa_formulaCode_eq (maj3Formula (0 : Fin 3) 1 2) w ⟨i.val - 1, by omega⟩
  · simp only [csaCarryCode, csaCarryFormula, hi, ↓reduceIte, ↓reduceDIte]
    rfl

/-- Generate the full three-to-two carry-save circuit code from its width. -/
def csa3to2Code (w : ℕ) : List (Op × List ℕ) × List ℕ :=
  appendCode (w + (w + w))
    (appendCodes (w + (w + w)) ((List.range w).map (csaSumCode w)))
    (appendCodes (w + (w + w)) ((List.range w).map (csaCarryCode w)))

/-- Generation preserves the exact existing circuit, including its unequal carry-bit blocks. -/
theorem csa3to2Code_eq_code (w : ℕ) : csa3to2Code w = (csa3to2 w).code := by
  have hmap {α : Type} (f : ℕ → α) (g : Fin w → α) (h : ∀ i, f i.val = g i) :
      (List.range w).map f = List.ofFn g :=
    List.ext_getElem (by simp) fun i hi _ => by
      simpa only [List.getElem_map, List.getElem_range, List.getElem_ofFn] using
        h ⟨i, by simpa using hi⟩
  rw [csa3to2Code, hmap _ _ (csaSumCode_eq w), hmap _ _ (csaCarryCode_eq w),
    appendCodes_code, appendCodes_code, appendCode_code]
  rfl

/-- The actual three-to-two reducer has a uniform native generator on unary widths. -/
@[fun_prop] theorem computableInPolyTime_csa3to2 :
    ComputableInPolyTime (fun w => (csa3to2 w).code) encUnary encCode := by
  have hw : ComputableInPolyTime (fun p : ℕ × ℕ => p.1)
      (encPair encUnary encUnary) encNat := unary_to_binary.comp (fst _ _)
  have hi : ComputableInPolyTime (fun p : ℕ × ℕ => p.2)
      (encPair encUnary encUnary) encNat := unary_to_binary.comp (snd _ _)
  have htmpl (F : Formula signature 3) {f : ℕ × ℕ → ℕ}
      (hf : ComputableInPolyTime f (encPair encUnary encUnary) encNat) :
      ComputableInPolyTime
        (fun p : ℕ × ℕ => formulaCode (p.1 + (p.1 + p.1)) F ![f p, p.1 + f p, p.1 + (p.1 + f p)])
        (encPair encUnary encUnary) encCode := by
    apply computableInPolyTime_formulaCode _ (by fun_prop)
    intro j
    fin_cases j
    · exact hf
    · change ComputableInPolyTime (fun p : ℕ × ℕ => p.1 + f p) _ encNat; fun_prop
    · change ComputableInPolyTime (fun p : ℕ × ℕ => p.1 + (p.1 + f p)) _ encNat; fun_prop
  have hs : ComputableInPolyTime (fun p : ℕ × ℕ => csaSumCode p.1 p.2)
      (encPair encUnary encUnary) encCode := htmpl sumTemplate hi
  have hm := htmpl (maj3Formula (0 : Fin 3) 1 2)
    (show ComputableInPolyTime (fun p : ℕ × ℕ => p.2 - 1) _ encNat from by fun_prop)
  have hc : ComputableInPolyTime (fun p : ℕ × ℕ => csaCarryCode p.1 p.2)
      (encPair encUnary encUnary) encCode := by
    unfold csaCarryCode
    fun_prop
  have hw' := unary_to_binary
  have hn : ComputableInPolyTime (fun w : ℕ => w + (w + w)) encUnary encNat := by fun_prop
  have h := computableInPolyTime_appendCode hn
    (computableInPolyTime_appendCodes hn (mapWithInput range hs))
    (computableInPolyTime_appendCodes hn (mapWithInput range hc))
  simpa only [← csa3to2Code_eq_code, csa3to2Code] using h

private theorem csa4to2FirstIn_val (w : ℕ) (i : Fin (w + (w + w))) :
    (csa4to2FirstIn w i).val = i.val := by
  induction i using Fin.addCases with
  | left i => simp [csa4to2FirstIn]
  | right i =>
    induction i using Fin.addCases with
    | left i => simp [csa4to2FirstIn, Nat.add_comm]
    | right i => simp [csa4to2FirstIn, -Fin.natAdd_eq_addNat, Nat.add_assoc]

private theorem code_csa4to2FirstIn (w : ℕ) :
    (Circuit.wiring signature (csa4to2FirstIn w)).code = ([], List.range (w + (w + w))) := by
  simpa using Circuit.code_wiring_eq_map (σ := signature) (g := id) (csa4to2FirstIn_val w)

private theorem code_csa4to2LastIn (w : ℕ) :
    (Circuit.wiring signature
      (Fin.natAdd (w + w) ∘ Fin.natAdd w : Fin w → Fin ((w + w) + (w + w)))).code =
      ([], (List.range w).map (fun i => (w + w) + (w + i))) :=
  Circuit.code_wiring_eq_map fun i => by simp [Nat.add_comm]

/-- Generate the existing two-layer carry-save reducer, including all input wiring. -/
def csa4to2Code (w : ℕ) : List (Op × List ℕ) × List ℕ :=
  compCode ((w + w) + (w + w)) (csa3to2Code w)
    (appendCode ((w + w) + (w + w))
      ([], (List.range w).map (fun i => (w + w) + (w + i)))
      (compCode ((w + w) + (w + w)) (csa3to2Code w) ([], List.range (w + (w + w)))))

/-- The generated code is exactly the existing four-to-two circuit's code. -/
theorem csa4to2Code_eq_code (w : ℕ) : csa4to2Code w = (csa4to2 w).code := by
  rw [csa4to2Code, csa3to2Code_eq_code, ← code_csa4to2FirstIn, ← code_csa4to2LastIn,
    compCode_code, appendCode_code, compCode_code]
  rfl

/-- The actual four-to-two reducer has a uniform native generator on unary widths. -/
@[fun_prop] theorem computableInPolyTime_csa4to2 :
    ComputableInPolyTime (fun w => (csa4to2 w).code) encUnary encCode := by
  have hw := unary_to_binary
  have hn : ComputableInPolyTime
      (fun w : ℕ => (w + w) + (w + w)) encUnary encNat := by fun_prop
  have hfirst : ComputableInPolyTime
      (fun w : ℕ => ([], List.range (w + (w + w)))) encUnary encCode := by
    have hr := unary_to_binary.map.comp
      (range.comp (show ComputableInPolyTime (fun w : ℕ => w + (w + w))
        encUnary encUnary from by fun_prop))
    simpa only [Function.comp_def, List.map_id_fun', id_eq] using (const []).prod hr
  have hlast : ComputableInPolyTime
      (fun w : ℕ => ([], (List.range w).map (fun i => (w + w) + (w + i))))
      encUnary encCode := by
    have hw' := unary_to_binary.comp (fst encUnary encUnary)
    have hi := unary_to_binary.comp (snd encUnary encUnary)
    exact (const []).prod (mapWithInput range (show ComputableInPolyTime
      (fun p : ℕ × ℕ => (p.1 + p.1) + (p.1 + p.2)) (encPair encUnary encUnary) encNat
      from by fun_prop))
  have h3 : ComputableInPolyTime csa3to2Code encUnary encCode := by
    simpa only [← csa3to2Code_eq_code] using computableInPolyTime_csa3to2
  have h := computableInPolyTime_compCode hn h3
    (computableInPolyTime_appendCode hn hlast
      (computableInPolyTime_compCode hn h3 hfirst))
  simpa only [← csa4to2Code_eq_code, csa4to2Code] using h

end Cslib.Circuits.Boolean
