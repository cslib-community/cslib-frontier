/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.EvaluationTime
public import CslibFrontier.Computability.Circuit.Encoding.Combinators

/-!
# Combining De Morgan circuit codes on shared inputs and in sequence

Specializes the signature-polymorphic raw circuit-code combinators of
`CslibFrontier.Computability.Circuit.Encoding.Combinators` to `Cslib.Circuits.Boolean.Op` and
`Cslib.Circuits.Boolean.encCode`.

## Main definitions

* `Cslib.Circuits.Boolean.appendCode`, `Cslib.Circuits.Boolean.appendCodes`,
  `Cslib.Circuits.Boolean.bundleCode`: combine De Morgan raw codes on shared inputs.
* `Cslib.Circuits.Boolean.compCode`: compose De Morgan raw circuit codes sequentially.

## Main results

* `Cslib.Circuits.Boolean.appendCode_code`, `Cslib.Circuits.Boolean.appendCodes_code`,
  `Cslib.Circuits.Boolean.bundleCode_code`, `Cslib.Circuits.Boolean.compCode_code`: agreement with
  typed circuit combinators.
* `Cslib.Circuits.Boolean.computableInPolyTime_appendCode`,
  `Cslib.Circuits.Boolean.computableInPolyTime_appendCodes`,
  `Cslib.Circuits.Boolean.computableInPolyTime_bundleCode`,
  `Cslib.Circuits.Boolean.computableInPolyTime_compCode`: polynomial-time constructors.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 6.1][AroraBarak09]
-/

public section

namespace Cslib.Circuits.Boolean

open Turing.MultiTapeTM

/-- Run two raw De Morgan codes on shared inputs, listing the first code's outputs before the
second's. -/
abbrev appendCode (n : ℕ) (c d : List (Op × List ℕ) × List ℕ) :
    List (Op × List ℕ) × List ℕ :=
  Circuit.appendCode n c d

/-- Appending two raw codes sums their gate counts. -/
theorem length_appendCode (n : ℕ) (c d : List (Op × List ℕ) × List ℕ) :
    (appendCode n c d).1.length = c.1.length + d.1.length :=
  Circuit.length_appendCode n c d

/-- Appending two raw codes sums their output counts. -/
theorem length_appendCode_outputs (n : ℕ) (c d : List (Op × List ℕ) × List ℕ) :
    (appendCode n c d).2.length = c.2.length + d.2.length :=
  Circuit.length_appendCode_outputs n c d

/-- Raw shared-input composition agrees with ordinary typed circuit append. -/
theorem appendCode_code {n m p : ℕ} (c : Circuit signature n m) (d : Circuit signature n p) :
    appendCode n c.code d.code = (c.append d).code :=
  (c.code_append d).symm

/-- The outputs of combined codes are the two output lists in order, on every input. -/
theorem evalOutput_appendCode_code {n m p : ℕ} (c : Circuit signature n m)
    (d : Circuit signature n p) (x : Fin n → Bool) :
    (appendCode n c.code d.code).2.map
      (evalOutput (List.ofFn x) (appendCode n c.code d.code).1) =
        List.ofFn (c.eval interpretation x) ++ List.ofFn (d.eval interpretation x) := by
  rw [appendCode_code]
  simp only [Circuit.code, List.map_ofFn]
  calc
    _ = List.ofFn ((c.append d).eval interpretation x) := by
      apply congrArg List.ofFn
      funext j
      exact ((c.append d).eval_eq_evalOutput x j).symm
    _ = _ := by rw [Circuit.eval_append, List.ofFn_fin_append]

/-- Combining circuit codes is polynomial-time, including binary input and wire counts. -/
@[fun_prop]
theorem computableInPolyTime_appendCode {α : Type} {enc : α ↪ List Bool}
    {n : α → ℕ} {c d : α → List (Op × List ℕ) × List ℕ}
    (hn : ComputableInPolyTime n enc encNat)
    (hc : ComputableInPolyTime c enc encCode)
    (hd : ComputableInPolyTime d enc encCode) :
    ComputableInPolyTime (fun a => appendCode (n a) (c a) (d a)) enc encCode :=
  Circuit.computableInPolyTime_appendCode hn hc hd

/-- Combine a list of raw De Morgan codes on shared inputs, preserving block and output order. -/
abbrev appendCodes (n : ℕ) (codes : List (List (Op × List ℕ) × List ℕ)) :
    List (Op × List ℕ) × List ℕ :=
  Circuit.appendCodes n codes

/-- Combining an empty list of raw codes yields the empty code. -/
@[simp] theorem appendCodes_nil (n : ℕ) : appendCodes n [] = ([], []) := rfl

/-- Adding a final block is ordinary shared-input append. -/
theorem appendCodes_append_singleton (n : ℕ)
    (codes : List (List (Op × List ℕ) × List ℕ)) (code : List (Op × List ℕ) × List ℕ) :
    appendCodes n (codes ++ [code]) = appendCode n (appendCodes n codes) code :=
  Circuit.appendCodes_append_singleton n codes code

/-- The combined code retains every gate, without padding the individual blocks. -/
theorem length_appendCodes (n : ℕ) (codes : List (List (Op × List ℕ) × List ℕ)) :
    (appendCodes n codes).1.length = (codes.flatMap Prod.fst).length :=
  Circuit.length_appendCodes n codes

/-- The combined code retains all outputs, including repeated outputs and zero-gate blocks. -/
theorem length_appendCodes_outputs (n : ℕ)
    (codes : List (List (Op × List ℕ) × List ℕ)) :
    (appendCodes n codes).2.length = (codes.flatMap Prod.snd).length :=
  Circuit.length_appendCodes_outputs n codes

/-- Combining arbitrary raw blocks is polynomial-time in their complete encodings. -/
@[fun_prop]
theorem computableInPolyTime_appendCodes {α : Type} {enc : α ↪ List Bool}
    {n : α → ℕ} {codes : α → List (List (Op × List ℕ) × List ℕ)}
    (hn : ComputableInPolyTime n enc encNat)
    (hcodes : ComputableInPolyTime codes enc (encList encCode)) :
    ComputableInPolyTime (fun a => appendCodes (n a) (codes a)) enc encCode :=
  Circuit.computableInPolyTime_appendCodes hn hcodes

/-- Combining single-output circuit codes agrees with `Circuit.pi`. -/
theorem appendCodes_code {k n : ℕ} (cs : Fin k → Circuit signature n 1) :
    appendCodes n (List.ofFn (fun j => (cs j).code)) = (Circuit.pi cs).code :=
  (Circuit.code_pi cs).symm

/-- Combine equal-sized De Morgan gate blocks on shared inputs. -/
abbrev bundleCode (n blockSize : ℕ) (codes : List (List (Op × List ℕ) × List ℕ)) :
    List (Op × List ℕ) × List ℕ :=
  Circuit.bundleCode n blockSize codes

/-- Bundling raw blocks is polynomial-time in their encodings and binary layout parameters. -/
@[fun_prop]
theorem computableInPolyTime_bundleCode {α : Type} {enc : α ↪ List Bool}
    {n blockSize : α → ℕ} {codes : α → List (List (Op × List ℕ) × List ℕ)}
    (hn : ComputableInPolyTime n enc encNat)
    (hblock : ComputableInPolyTime blockSize enc encNat)
    (hcodes : ComputableInPolyTime codes enc (encList encCode)) :
    ComputableInPolyTime (fun a => bundleCode (n a) (blockSize a) (codes a)) enc encCode :=
  Circuit.computableInPolyTime_bundleCode hn hblock hcodes

/-- Equal-sized blocks occupy their number times their common gate count. -/
theorem length_bundleCode (n blockSize : ℕ) (codes : List (List (Op × List ℕ) × List ℕ))
    (hlen : ∀ c ∈ codes, c.1.length = blockSize) :
    (bundleCode n blockSize codes).1.length = codes.length * blockSize :=
  Circuit.length_bundleCode n blockSize codes hlen

/-- Adding the next equal-sized block is shared-input append. -/
theorem bundleCode_append_singleton (n blockSize : ℕ)
    (codes : List (List (Op × List ℕ) × List ℕ)) (code : List (Op × List ℕ) × List ℕ)
    (hlen : ∀ c ∈ codes, c.1.length = blockSize) :
    bundleCode n blockSize (codes ++ [code]) =
      appendCode n (bundleCode n blockSize codes) code :=
  Circuit.bundleCode_append_singleton n blockSize codes code hlen

/-- For equal-sized blocks, direct relocation agrees with repeated shared-input append. -/
theorem bundleCode_eq_foldl_appendCode (n blockSize : ℕ)
    (codes : List (List (Op × List ℕ) × List ℕ))
    (hlen : ∀ c ∈ codes, c.1.length = blockSize) :
    bundleCode n blockSize codes = codes.foldl (appendCode n) ([], []) :=
  Circuit.bundleCode_eq_foldl_appendCode n blockSize codes hlen

/-- Fixed-size bundling is a specialization of the varying-size constructor. -/
theorem bundleCode_eq_appendCodes (n blockSize : ℕ)
    (codes : List (List (Op × List ℕ) × List ℕ))
    (hlen : ∀ c ∈ codes, c.1.length = blockSize) :
    bundleCode n blockSize codes = appendCodes n codes :=
  Circuit.bundleCode_eq_appendCodes n blockSize codes hlen

/-- The typed and raw bundles have the same code when component sizes agree. -/
theorem bundleCode_code {k n : ℕ} (cs : Fin k → Circuit signature n 1) (blockSize : ℕ)
    (hs : ∀ j, (cs j).size = blockSize) :
    bundleCode n blockSize (List.ofFn (fun j => (cs j).code)) = (Circuit.pi cs).code :=
  (Circuit.code_pi_bundle cs blockSize hs).symm

/-- Equal-sized single-output codes form one typed circuit with the corresponding output order. -/
theorem exists_circuit_bundleCode {k n : ℕ} (cs : Fin k → Circuit signature n 1)
    (blockSize : ℕ) (hs : ∀ j, (cs j).size = blockSize) :
    ∃ c : Circuit signature n k,
      bundleCode n blockSize (List.ofFn (fun j => (cs j).code)) = c.code ∧
        ∀ x j, c.eval interpretation x j = (cs j).eval interpretation x 0 :=
  ⟨Circuit.pi cs, bundleCode_code cs blockSize hs, fun x j => congrFun (Circuit.eval_pi cs x) j⟩

/-- Feed the outputs of `c` to the inputs of `d`, matching the argument order of `Circuit.comp`. -/
abbrev compCode (n : ℕ) (d c : List (Op × List ℕ) × List ℕ) :
    List (Op × List ℕ) × List ℕ :=
  Circuit.compCode n d c

/-- Raw sequential composition is the code of typed circuit composition. -/
theorem compCode_code {n m p : ℕ} (d : Circuit signature m p)
    (c : Circuit signature n m) : compCode n d.code c.code = (d.comp c).code :=
  (d.code_comp c).symm

/-- Sequential composition retains both gate lists. -/
theorem length_compCode (n : ℕ) (d c : List (Op × List ℕ) × List ℕ) :
    (compCode n d c).1.length = c.1.length + d.1.length :=
  Circuit.length_compCode n d c

/-- Sequential composition retains the later circuit's number of outputs. -/
theorem length_compCode_outputs (n : ℕ) (d c : List (Op × List ℕ) × List ℕ) :
    (compCode n d c).2.length = d.2.length :=
  Circuit.length_compCode_outputs n d c

/-- Construct sequential circuit codes in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_compCode {α : Type} {enc : α ↪ List Bool}
    {n : α → ℕ} {d c : α → List (Op × List ℕ) × List ℕ}
    (hn : ComputableInPolyTime n enc encNat)
    (hd : ComputableInPolyTime d enc encCode)
    (hc : ComputableInPolyTime c enc encCode) :
    ComputableInPolyTime (fun a => compCode (n a) (d a) (c a)) enc encCode :=
  Circuit.computableInPolyTime_compCode hn hd hc

end Cslib.Circuits.Boolean
