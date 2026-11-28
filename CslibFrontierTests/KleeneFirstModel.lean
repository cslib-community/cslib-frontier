/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module

public import CslibFrontier.Languages.CombinatoryLogic.KleeneFirstModel

/-! Clients of the pca API and Kleene's first model `K₁` under module encapsulation. Application
in `K₁` runs codes: the successor code sends `4` to `5`, and a code searching for a zero of the
successor diverges. The combinators act on concrete indices: `k ⬝ 7` is an index of the constant
function `7`, `s ⬝ k ⬝ k` acts as the identity, and `s ⬝ (k ⬝ succ) ⬝ i` applies the successor.
Partiality reaches the combinators: `s ⬝ loop ⬝ k` is defined, but applying it diverges. A bracket
abstraction is evaluated on a concrete argument. -/

public section

namespace CslibFrontierTests.KleeneFirstModel

open Encodable Denumerable Nat.Partrec Cslib Cslib.PartialCombinatoryAlgebra

/-- The successor code sends `4` to `5` in `K₁`. -/
theorem app_succ : kleeneOne.app (encode Code.succ) 4 = Part.some 5 := by
  simp [Code.eval]

/-- An index whose function diverges everywhere: unbounded search for a zero of the successor. -/
def loop : ℕ := encode (Code.rfind' Code.succ)

/-- Applying `loop` diverges. -/
theorem app_loop (n : ℕ) : kleeneOne.app loop n = Part.none := by
  refine Part.eq_none_iff.2 fun x hx => ?_
  simp only [loop, kleeneOne_app, ofNat_encode, Code.eval, Nat.unpaired, Part.mem_map_iff] at hx
  obtain ⟨m, hm, -⟩ := hx
  have := Nat.rfind_spec hm
  simp at this

/-- `k ⬝ 7` is defined, and its value is an index of the constant function `7`. -/
example (n : ℕ) :
    kleeneOne.app ((kleeneOne.app kleeneOne.k 7).get (kleeneOne.dom_app_k 7)) n = Part.some 7 := by
  rw [app_get_eq_ap kleeneOne.app, kleeneOne.ap_ap_k]

/-- `s ⬝ k ⬝ k` acts as the identity: it sends `42` to `42`. -/
example :
    ap kleeneOne.app (ap kleeneOne.app (kleeneOne.app kleeneOne.s kleeneOne.k)
      (Part.some kleeneOne.k)) (Part.some 42) = Part.some 42 := by
  rw [kleeneOne.ap_ap_ap_s, ← Part.some_get (kleeneOne.dom_app_k 42), ap_some_some,
    app_get_eq_ap kleeneOne.app, kleeneOne.ap_ap_k]

/-- `s ⬝ (k ⬝ succ) ⬝ i ⬝ 4 = (k ⬝ succ ⬝ 4) ⬝ (i ⬝ 4) = succ ⬝ 4 = 5`. -/
example :
    ap kleeneOne.app (ap kleeneOne.app (kleeneOne.app kleeneOne.s
      ((kleeneOne.app kleeneOne.k (encode Code.succ)).get (kleeneOne.dom_app_k _)))
      (Part.some kleeneOne.i)) (Part.some 4) = Part.some 5 := by
  rw [kleeneOne.ap_ap_ap_s, app_get_eq_ap kleeneOne.app, kleeneOne.ap_ap_k, app_i,
    ap_some_some, app_succ]

/-- `s ⬝ loop ⬝ k` is defined, but applying it to `0` diverges, since `loop ⬝ 0` does. -/
example :
    (ap kleeneOne.app (kleeneOne.app kleeneOne.s loop) (Part.some kleeneOne.k)).Dom ∧
      ap kleeneOne.app (ap kleeneOne.app (kleeneOne.app kleeneOne.s loop)
        (Part.some kleeneOne.k)) (Part.some 0) = Part.none := by
  refine ⟨kleeneOne.dom_ap_s _ _, ?_⟩
  rw [kleeneOne.ap_ap_ap_s, app_loop]
  simp [ap]

/-- Combinatory completeness on a concrete term: the abstraction of `x₀ ⬝ 4` over `x₀`, applied to
the successor code, gives `5`. -/
example :
    ap kleeneOne.app
      (kleeneOne.eval (kleeneOne.abs (.app (.var 0) (.const 4))) Fin.elim0)
      (Part.some (encode Code.succ)) = Part.some 5 := by
  rw [ap_eval_abs]
  simp [eval, Fin.snoc, Code.eval]

end CslibFrontierTests.KleeneFirstModel
