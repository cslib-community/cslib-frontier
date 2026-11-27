/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Languages.Electrical.NetlistCertificate
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! # Tests for netlist text and the end-to-end circuit checker

Every certificate below was produced by an untrusted exact generator and is checked by the
kernel (`decide +kernel`), together with the reading of the text.

* **RC low-pass filter** (`rcText`): the text, in the form of a schematic editor's SPICE export,
  is read as the explicit netlist `rcParsed`; the certificate is accepted end to end, so every
  trajectory of the circuit described by the text converges exponentially to its operating
  point, and its zero-state response at the probe `v(/out)` to the input port of `V1` is
  `∫₀ᵗ 1000 e^{-1000 (t - s)} u s ds`: the impulse response `h t = 1000 e^{-1000 t}` of
  `R = 1 kΩ`, `C = 1 µF`, with no direct feedthrough.
* **RLC low-pass filter** (`lpText`): `R = 1 kΩ`, `L = 10 mH`, `C = 100 nF`, with node names as
  such an export writes them and two probes (the capacitor voltage and the inductor current),
  accepted end to end.
* **Rejections**: altered netlists (another resistance, another node, a removed line) and a
  corrupted certificate are not accepted, and unsupported constructs are rejected by the reader
  with a message: other elements (a diode, a subcircuit), directives (`.include`, `.model`),
  continuation lines, ground written as `gnd`, names that differ only in case, a unit after a
  value, a non-constant source and an input port of gain other than `1`.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.NetlistText

open Set Matrix Mathlib.Tactic.Matrix Cslib.LinearAlgebra Cslib.Electrical Cslib.Electrical.Text

/-- The netlist read from a text, if it is accepted (kernel-decidable, unlike equality in
`Except`). -/
def okOf : Except String ParsedNetlist → Option ParsedNetlist
  | .ok P => some P
  | .error _ => none

/-- The message of a rejected text. -/
def errorOf : Except String ParsedNetlist → Option String
  | .ok _ => none
  | .error e => some e

theorem eq_ok_of_okOf {e : Except String ParsedNetlist} {P : ParsedNetlist}
    (h : okOf e = some P) : e = .ok P := by
  cases e <;> simp_all [okOf]

/-! ### RC low-pass filter -/

/-- An RC low-pass filter, as a schematic editor's SPICE export writes it. -/
def rcText : String := ".title RC low-pass filter
* exported from a schematic
V1 /in 0 dc 0 ac 1
R1 /in /out 1k
C1 /out 0 1u
.probe v /out
.end
"

/-- The netlist that `rcText` describes. -/
abbrev rcParsed : ParsedNetlist where
  netlist := { nodes := 2, inputs := 1
               branches := [⟨1, 0, .voltageSource 0 (some 0)⟩, ⟨1, 2, .resistor 1000⟩,
                 ⟨2, 0, .capacitor (1/1000000)⟩] }
  probes := [.voltage 2 0]
  nodeNames := ["/in".toList, "/out".toList]
  branchNames := ["V1".toList, "R1".toList, "C1".toList]

/-- **The reading of the text.** -/
theorem rcText_parse : parse rcText = .ok rcParsed :=
  eq_ok_of_okOf (by decide +kernel)

/-- The certificate of `rcText`. -/
def rcCert : NetlistCert where
  dec := {
    k := 1
    r := 4
    T := [[(4, 1)], [(0, 1)], [(1, 1)], [(3, 1)], [(2, 1)]]
    Tᵢ := [[(1, 1)], [(2, 1)], [(4, 1)], [(3, 1)], [(0, 1)]]
    U := [[(4, 1)], [(0, 1)], [(1, 1)], [(3, 1)], [(2, 1)]]
    Uᵢ := [[(1, 1)], [(2, 1)], [(4, 1)], [(3, 1)], [(0, 1)]]
    LE := [[(0, 1)]]
    UE := [[(0, (1/1000000 : ℚ))]]
    LF := [[(0, 1)], [(1, 1)], [(2, 1)], [(3, 1)]]
    UF := [[(0, (-1)), (2, (-1))], [(1, (-1)), (2, 1)], [(2, (-1000)), (3, 1)], [(3, (-1))]]
    K := [[(0, (-1/1000 : ℚ))], [(0, (1/1000 : ℚ))], [(0, (1/1000 : ℚ))], []]
    A := [[-1000]] }
  real := { W := [[(0, (1/1000 : ℚ))], [(0, (-1/1000 : ℚ))], [(0, (-1/1000 : ℚ))], [(0, (-1))]]
            B := [[(0, 1000)]] }
  z₀ := [0, 0, 0, 0, 0]
  P := [[(1/2000 : ℚ)]]
  lyap := ⟨⟨[[1]], [(1/2000 : ℚ)]⟩, ⟨[[1]], [1]⟩⟩

/-- **The certificate is accepted against the text.** -/
theorem rcText_check : checkText rcText rcCert = true := by decide +kernel

/-- The end-to-end guarantee for the circuit described by `rcText`. -/
example := exists_parse_of_checkText rcText_check

/-! ### The impulse response of the RC filter described by the text -/

/-- The computed output rows of the realization of `rcText`: `C = 1`, `D = 0`. -/
theorem rc_outputRows :
    eqSparse (SparseRealizationCert.outputRows rcCert.dec
        (rcParsed.netlist.probeSparse rcParsed.probes)) [[(0, 1)]] = true ∧
      eqSparse (rcCert.real.feedthroughRows rcCert.dec
        (rcParsed.netlist.probeSparse rcParsed.probes)) [] = true := by
  decide +kernel

/-- **The checked realization of the RC filter** described by `rcText`: `A = -1000`,
`B = 1000`, `C = 1`, `D = 0`. -/
theorem rc_realization :
    rcParsed.netlist.sparseRealization rcCert.dec rcCert.real rcParsed.probes =
      ⟨of fun _ _ => -1000, of fun _ _ => 1000, of fun _ _ => 1, 0⟩ := by
  have hk : rcCert.dec.k = 1 := rfl
  have h0 : ∀ j : Fin rcCert.dec.k, j.val = 0 := fun j => by have := j.is_lt; omega
  simp only [Netlist.sparseRealization, realOfSparse_eq_of_eqSparse rc_outputRows.1,
    realOfSparse_eq_of_eqSparse rc_outputRows.2]
  congr 1 <;> ext i j
  · simp only [realOfRows, map_apply, of_apply, ofLists_apply, ofList_apply, h0]
    norm_num [rcCert]
  · simp only [realOfSparse, map_apply, ofSparse_apply, of_apply, h0]
    simp [rcCert, sparseGet_cons]
  · simp [ofSparse_apply, sparseGet_cons, h0]
  · simp [ofSparse_apply]

/-- **The impulse response of the RC filter** described by `rcText`:
`h t = 1000 e^{-1000 t}` for `t ≥ 0`, with no direct feedthrough. -/
theorem rc_responseKernel {t : ℝ} (ht : 0 ≤ t) :
    (rcParsed.netlist.sparseRealization rcCert.dec rcCert.real rcParsed.probes).responseKernel t
      = of fun _ _ => 1000 * Real.exp (-1000 * t) := by
  have hk : Fintype.card (Fin rcCert.dec.k) = 1 := rfl
  rw [rc_realization, LTISystem.responseKernel_eq_of_hasDerivWithinAt
    (X := fun τ => of fun _ _ => 1000 * Real.exp (-1000 * τ)) _ _ ht]
  · ext o j
    simp [Matrix.mul_apply, hk]
  · intro j τ _
    refine (hasDerivAt_pi.2 fun l => ?_).hasDerivWithinAt
    have h := ((hasDerivAt_id τ).const_mul (-1000)).exp.const_mul 1000
    simp only [id, mul_one] at h
    convert h using 1
    · funext y
      simp
    · rw [show ∀ v : Fin rcCert.dec.k → ℝ, ((of fun _ _ => (-1000 : ℝ)) *ᵥ v) l =
        ∑ x, -1000 * v x from fun v => rfl]
      simp only [of_apply, transpose_apply, Finset.sum_const, Finset.card_univ, hk, one_smul]
      ring
  · ext i j
    simp

/-- **The zero-state response of the circuit described by `rcText`**, from the acceptance of
its certificate against the text: for every input `u` continuous on `[0, ∞)` and every
trajectory whose capacitor starts uncharged, the output voltage `v(/out)` is
`∫₀ᵗ 1000 e^{-1000 (t - s)} u s ds`. -/
example {u : ℝ → Fin rcParsed.netlist.inputs → ℝ} (hu : ContinuousOn u (Ici 0))
    {φ : ℝ → Fin rcParsed.netlist.nodes → ℝ} {i : ℝ → Fin rcParsed.netlist.branches.length → ℝ}
    (h : rcParsed.netlist.IsTrajectoryOn u φ i (Ici 0)) (h₀ : φ 0 1 = 0) {t : ℝ}
    (ht : 0 ≤ t) :
    (fun o => (rcParsed.probes.get o).eval (φ t) (i t)) =
      ∫ s in 0..t, (of fun _ _ => 1000 * Real.exp (-1000 * (t - s)) :
        Matrix (Fin 1) (Fin 1) ℝ) *ᵥ u s := by
  obtain ⟨P, hP, g⟩ := exists_parse_of_checkText rcText_check
  rw [rcText_parse] at hP
  cases hP
  have hx : realOfSparse rcCert.dec.k rcParsed.netlist.size rcCert.dec.Uᵢ *ᵥ
      (Fin.append (φ 0) (i 0) - realOfList rcParsed.netlist.size rcCert.z₀) = 0 := by
    funext l
    have hl : l.val = 0 := by have := l.is_lt; change _ < 1 at this; omega
    simp only [mulVec, dotProduct, realOfSparse, map_apply, ofSparse_apply, Pi.zero_apply]
    rw [Finset.sum_eq_single (⟨1, by decide⟩ : Fin rcParsed.netlist.size)]
    · simp [rcCert, hl, sparseGet_cons, Fin.append, Fin.addCases, h₀, realOfList,
        ofList_apply, Netlist.size]
    · intro j _ hj
      have hj' : j.val ≠ 1 := fun h => hj (Fin.ext h)
      simp [rcCert, hl, sparseGet_cons, Ne.symm hj']
    · simp
  have := g.2.2.2 u hu φ i h hx t ht
  have hz : (fun o => (rcParsed.probes.get o).eval
      (fun j => realOfList rcParsed.netlist.size rcCert.z₀ (Fin.castAdd _ j))
      (fun b => realOfList rcParsed.netlist.size rcCert.z₀ (Fin.natAdd _ b))) = 0 := by
    funext o
    fin_cases o
    simp [rcCert, Probe.eval, potential, realOfList, ofList_apply, Netlist.size]
  rw [hz, sub_zero, rc_realization, zero_mulVec, zero_add] at this
  rw [this]
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [Set.uIcc_of_le ht] at hs
  rw [← rc_realization, rc_responseKernel (sub_nonneg.2 hs.2)]
  rfl

/-! ### RLC low-pass filter -/

/-- An RLC low-pass filter with the node names of a schematic editor's SPICE export. -/
def lpText : String := ".title RLC low-pass filter
V1 /in 0 dc 0 ac 1
R1 /in Net-_R1-Pad2_ 1k
L1 Net-_R1-Pad2_ /out 10m
C1 /out 0 100n
.probe v /out 0
.probe i L1
.end
"

/-- The certificate of `lpText`. -/
def lpCert : NetlistCert where
  dec := {
    k := 2
    r := 5
    T := [[(5, 1)], [(6, 1)], [(0, 1)], [(1, 1)], [(2, 1)], [(3, 1)], [(4, 1)]]
    Tᵢ := [[(2, 1)], [(3, 1)], [(4, 1)], [(5, 1)], [(6, 1)], [(0, 1)], [(1, 1)]]
    U := [[(5, 1)], [(6, 1)], [(1, 1)], [(2, 1)], [(3, 1)], [(0, 1)], [(4, 1)]]
    Uᵢ := [[(5, 1)], [(2, 1)], [(3, 1)], [(4, 1)], [(6, 1)], [(0, 1)], [(1, 1)]]
    LE := [[(0, 1)], [(1, 1)]]
    UE := [[(0, (1/100 : ℚ))], [(1, (1/10000000 : ℚ))]]
    LF := [[(0, 1)], [(1, 1)], [(2, 1)], [(3, 1)], [(1, (-1000)), (3, (-1)), (4, 1)]]
    UF := [[(0, (-1)), (1, (-1))], [(1, 1)], [(2, (-1))], [(3, (-1))], [(4, (-1))]]
    K := [[(0, 1)], [(0, (-1))], [(0, (-1))], [], [(0, 1000)]]
    A := [[-100000, -100], [10000000, 0]] }
  real := { W := [[], [], [], [(0, (-1))], [(0, (-1))]], B := [[(0, 100)], []] }
  z₀ := [0, 0, 0, 0, 0, 0, 0]
  P := [[(1/2 : ℚ), (2621/524288 : ℚ)], [(2621/524288 : ℚ),
    (3691/67108864 : ℚ)]]
  lyap := ⟨⟨[[1], [(2621/262144 : ℚ), 1]], [(1/2 : ℚ),
    (689527/137438953472 : ℚ)]⟩,
  ⟨[[1], [(-1799/352000 : ℚ), 1]], [(34375/2048 : ℚ), (7377499599/7381975040 : ℚ)]⟩⟩

/-- **The certificate is accepted against the text.** -/
theorem lpText_check : checkText lpText lpCert = true := by decide +kernel

/-- The end-to-end guarantee for the circuit described by `lpText`. -/
example := exists_parse_of_checkText lpText_check

/-! ### Rejections -/

/-- Another resistance: the certificate is not accepted. -/
example : checkText ".title RC low-pass filter
V1 /in 0 dc 0 ac 1
R1 /in /out 2k
C1 /out 0 1u
.probe v /out
.end
" rcCert = false := by decide +kernel

/-- Another node for the capacitor: the certificate is not accepted. -/
example : checkText ".title RC low-pass filter
V1 /in 0 dc 0 ac 1
R1 /in /out 1k
C1 /in 0 1u
.probe v /out
.end
" rcCert = false := by decide +kernel

/-- A removed line: the certificate is not accepted. -/
example : checkText ".title RC low-pass filter
V1 /in 0 dc 0 ac 1
C1 /out 0 1u
.probe v /out
.end
" rcCert = false := by decide +kernel

/-- A corrupted certificate: another reduced state matrix. -/
example : checkText rcText { rcCert with dec := { rcCert.dec with A := [[-999]] } } = false := by
  decide +kernel

/-- A corrupted certificate: another input matrix. -/
example : checkText rcText { rcCert with real := { rcCert.real with B := [[(0, 999)]] } } =
    false := by
  decide +kernel

/-- Unsupported elements, directives and syntax are rejected by the reader. -/
example : errorOf (parse "t\nD1 a 0 dmod\n") = some "unsupported element: D1" := by decide +kernel
example : errorOf (parse "t\nX1 a 0 opamp\n") = some "unsupported element: X1" := by decide +kernel
example : errorOf (parse "t\n.include models.lib\n") = some "unsupported directive: .include" := by
  decide +kernel
example : errorOf (parse "t\n.model dmod D\n") = some "unsupported directive: .model" := by
  decide +kernel
example : errorOf (parse "t\nR1 a 0 1k\n+ 2k\n") = some "unsupported element: +" := by
  decide +kernel
example : errorOf (parse "t\nR1 a GND 1k\n") = some "malformed nodes" := by decide +kernel
example : errorOf (parse "t\nR1 a 0 1k\nR2 A 0 1k\n")
    = some "node names that differ only in case" := by
  decide +kernel
example : errorOf (parse "t\nR1 a 0 1k\nr1 a 0 1k\n") = some "duplicate element names" := by
  decide +kernel
example : errorOf (parse "t\nR1 a 0 1kOhm\n") = some "malformed value: 1kOhm" := by decide +kernel
example : errorOf (parse "t\nV1 a 0 sin(0 1 1k)\n") = some "malformed source" := by decide +kernel
example : errorOf (parse "t\nV1 a 0 ac 2\n")
    = some "unsupported source: only `ac 1` input ports" := by
  decide +kernel
example : errorOf (parse "t\n.probe v b\nR1 a 0 1k\n") = some "probe of an unknown node" := by
  decide +kernel

/-- Values: suffixes, exponents and fractions are exact; `1F` is `10⁻¹⁵`, as in SPICE. -/
example : (["4.7k", "2.5e-3meg", "100n", "1F", "-3"].map fun s => value? s.toList) =
    [some 4700, some 2500, some (1/10000000), some (1/1000000000000000), some (-3)] := by
  decide +kernel

end CslibFrontierTests.NetlistText
