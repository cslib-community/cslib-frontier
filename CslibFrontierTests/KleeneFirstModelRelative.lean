/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module

public import CslibFrontier.Languages.CombinatoryLogic.KleeneFirstModelRelative

/-! Clients of Kleene's first model relative to an oracle, `K₁ᶠ`, under module encapsulation. The
atomic oracle code answers with the oracle, so application depends on `f`: the index of `oracle`
sends `3` to `6` under doubling and to `9` under squaring. The universal oracle code evaluates a
code that queries the oracle. The combinators are oracle-independent numbers, and the realizer
`s ⬝ (k ⬝ oracle) ⬝ i`, written with the combinators of `K₁ᶠ` for one oracle, computes the
oracle in `K₁ᶠ` for another. An embedded ordinary code that searches forever diverges. -/

public section

namespace CslibFrontierTests.KleeneFirstModelRelative

open Encodable Denumerable Nat.RecursiveIn Nat.RecursiveIn.Code Cslib
  Cslib.PartialCombinatoryAlgebra

/-- The index of the atomic oracle code applies the oracle. -/
theorem app_oracle (f : ℕ → ℕ) (n : ℕ) :
    (kleeneOneRel f).app (encode Code.oracle) n = Part.some (f n) := by
  simp [Code.eval]

example : (kleeneOneRel (· * 2)).app (encode Code.oracle) 3 = Part.some 6 := app_oracle _ 3

example : (kleeneOneRel (fun n => n * n)).app (encode Code.oracle) 3 = Part.some 9 :=
  app_oracle _ 3

/-- The universal oracle code runs the oracle code with index `encode oracle` on `5`, under the
squaring oracle. -/
example : ∃ u : Code, eval (fun n => n * n : ℕ → ℕ) u (Nat.pair (encode Code.oracle) 5) =
    Part.some 25 := by
  obtain ⟨u, hu⟩ := exists_universal
  exact ⟨u, by rw [hu]; simp [Code.eval]⟩

/-- The realizer `s ⬝ (k ⬝ oracle) ⬝ i` is built from the combinators of `K₁ᶠ` for the identity
oracle, but they are also those of `K₁ᶠ` for every `f`, where it computes `f`. -/
theorem ap_s_k_oracle_i (f : ℕ → ℕ) (n : ℕ) :
    ap (kleeneOneRel f).app (ap (kleeneOneRel f).app ((kleeneOneRel f).app (kleeneOneRel id).s
      (((kleeneOneRel f).app (kleeneOneRel id).k (encode Code.oracle)).get
        (by rw [kleeneOneRel_k id f]; exact (kleeneOneRel f).dom_app_k _)))
      (Part.some (kleeneOneRel f).i)) (Part.some n) = Part.some (f n) := by
  rw [kleeneOneRel_s id f, (kleeneOneRel f).ap_ap_ap_s, app_get_eq_ap (kleeneOneRel f).app]
  simp only [kleeneOneRel_k id f, (kleeneOneRel f).ap_ap_k, app_i, ap_some_some, app_oracle]

example : ap (kleeneOneRel (· + 10)).app (ap (kleeneOneRel (· + 10)).app
    ((kleeneOneRel (· + 10)).app (kleeneOneRel id).s
      (((kleeneOneRel (· + 10)).app (kleeneOneRel id).k (encode Code.oracle)).get
        (by rw [kleeneOneRel_k id]; exact (kleeneOneRel _).dom_app_k _)))
      (Part.some (kleeneOneRel (· + 10)).i)) (Part.some 1) = Part.some 11 :=
  ap_s_k_oracle_i _ 1

/-- An embedded ordinary code that searches for a zero of the successor diverges, for every
oracle. -/
example (f : ℕ → ℕ) (n : ℕ) :
    (kleeneOneRel f).app (encode (ofPartrec (.rfind' .succ))) n = Part.none := by
  refine Part.eq_none_iff.2 fun x hx => ?_
  simp only [kleeneOneRel_app, ofNat_encode, eval_ofPartrec, Nat.Partrec.Code.eval,
    Nat.unpaired, Part.mem_map_iff] at hx
  obtain ⟨m, hm, -⟩ := hx
  have := Nat.rfind_spec hm
  simp at this

end CslibFrontierTests.KleeneFirstModelRelative
