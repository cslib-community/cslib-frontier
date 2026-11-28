/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Electrical.NetlistText
public import CslibFrontier.Languages.Electrical.SparseDecoupling
public import CslibFrontier.Algorithms.LinearAlgebra.LyapunovCertificate

/-!
# Certified stability and responses of a circuit from its netlist text

The end-to-end checker of the circuit pipeline: `Cslib.Electrical.Text.checkText s cert` reads
the netlist text `s` (`Cslib.Electrical.Text.parse`) and checks the certificate `cert` against
the circuit it describes. The certificate (`Cslib.Electrical.Text.NetlistCert`) is untrusted
data from a numerical tool: a structured index-one decoupling of the modified nodal equations
and the input data of its realization (`Cslib.LinearAlgebra.SparseDecouplingCert`,
`Cslib.LinearAlgebra.SparseRealizationCert`), an operating point, and a Lyapunov matrix with
`LDLᵀ` witnesses (`Cslib.LinearAlgebra.LyapunovCert`). Every check is an exact rational
computation that the kernel evaluates.

`Cslib.Electrical.Text.exists_parse_of_checkText` is the end-to-end theorem. If
`checkText s cert` holds, then `s` parses to a netlist `P`, and the guarantee
`Cslib.Electrical.Text.NetlistCert.Guarantee` holds for the circuit `P.netlist` with Kirchhoff
semantics (`Cslib.Electrical.Netlist.IsTrajectoryOn`), with the operating point `z₀ = cert.z₀`:

1. `z₀` is a constant trajectory with the sources at their constant values (the DC operating
   point), and every differential state starts a trajectory: the guarantee is not vacuous;
2. every trajectory with zero input converges to `z₀` exponentially, in all node potentials
   and branch currents;
3. for the probes of the text (`.probe` lines) and its input ports (`ac` sources), every
   trajectory driven by an input continuous on `[0, ∞)` from the operating-point state has the
   output `y t - y₀ = D u t + ∫₀ᵗ h (t - s) u s ds`, where `h t = C exp (t A) B` and `D` are the
   response kernel and the direct feedthrough of the checked realization
   `Cslib.Electrical.Netlist.sparseRealization`.

The trust boundary is the text and the semantics of `parse` (documented in
`CslibFrontier.Languages.Electrical.NetlistText`): the exporter that wrote the text, the
physical components and parasitics are outside it. Failure of the check is inconclusive; it is
not an instability proof.

## Main definitions

* `Cslib.Electrical.Text.NetlistCert`, `Cslib.Electrical.Text.NetlistCert.check`.
* `Cslib.Electrical.Text.NetlistCert.Guarantee`: the guarantee.
* `Cslib.Electrical.Text.checkText`.

## Main results

* `Cslib.Electrical.Text.NetlistCert.guarantee_of_check`.
* `Cslib.Electrical.Text.exists_parse_of_checkText`.
-/

public section

open Set Matrix Cslib.LinearAlgebra

namespace Cslib.Electrical.Text

/-- An untrusted certificate of stability and of the realization of a circuit. -/
structure NetlistCert where
  /-- The structured index-one decoupling of the modified nodal equations. -/
  dec : SparseDecouplingCert
  /-- The input data of the realization. -/
  real : SparseRealizationCert
  /-- The operating point: all node potentials, then all branch currents. -/
  z₀ : List ℚ
  /-- The Lyapunov matrix of the reduced state matrix `dec.A`. -/
  P : List (List ℚ)
  /-- The `LDLᵀ` witnesses for `P` and for `-(Aᵀ P + P A)`. -/
  lyap : LyapunovCert

/-- Whether `cert` is accepted for the circuit `c`: the netlist is well formed, the
decoupling, the realization data, the operating point and the Lyapunov certificate are
accepted. -/
@[expose] def NetlistCert.check (cert : NetlistCert) (c : Netlist) : Bool :=
  c.check && cert.dec.check c.size c.eSparse c.fSparse &&
    cert.real.check cert.dec c.size c.eSparse c.fSparse c.gSparse &&
    isEquilibriumSparse c.size c.fSparse c.bList cert.z₀ &&
    cert.lyap.check cert.dec.k cert.dec.A cert.P

/-- **The end-to-end checker**: whether the text `s` parses and `cert` is accepted for the
circuit it describes. -/
@[expose] def checkText (s : String) (cert : NetlistCert) : Bool :=
  match parse s with
  | .ok P => cert.check P.netlist
  | .error _ => false

/-- **The guarantee of an accepted certificate** for a netlist `P`, with the operating point
`z₀ = cert.z₀`, the differential coordinates given by the first `cert.dec.k` rows of
`cert.dec.Uᵢ`, and the checked realization `P.netlist.sparseRealization cert.dec cert.real
P.probes` from the input ports to the probes:

1. `z₀` is a constant trajectory with zero input (the DC operating point);
2. every differential state starts a trajectory on `[0, ∞)`;
3. every trajectory with zero input converges to `z₀` exponentially, in the Euclidean norm of
   all node potentials and branch currents;
4. every trajectory driven by an input continuous on `[0, ∞)` whose differential state starts at
   that of `z₀` has the probed outputs `y t - y₀ = D u t + ∫₀ᵗ h (t - s) u s ds` for `t ≥ 0`,
   with the response kernel `h` and the direct feedthrough `D` of the realization. -/
@[expose] def NetlistCert.Guarantee (cert : NetlistCert) (P : ParsedNetlist) : Prop :=
  P.netlist.IsTrajectoryOn 0 (fun _ j => realOfList P.netlist.size cert.z₀ (Fin.castAdd _ j))
      (fun _ b => realOfList P.netlist.size cert.z₀ (Fin.natAdd _ b)) (Ici 0) ∧
    (∀ x₀ : Fin cert.dec.k → ℝ, ∃ φ i, P.netlist.IsTrajectoryOn 0 φ i (Ici 0) ∧
      realOfSparse cert.dec.k P.netlist.size cert.dec.Uᵢ *ᵥ Fin.append (φ 0) (i 0) = x₀) ∧
    (∃ M α : ℝ, 0 < α ∧ ∀ φ i, P.netlist.IsTrajectoryOn 0 φ i (Ici 0) → ∀ t ≥ 0,
      ‖WithLp.toLp 2 (Fin.append (φ t) (i t) - realOfList P.netlist.size cert.z₀)‖ ≤
        M * Real.exp (-(α * t)) *
          ‖WithLp.toLp 2 (Fin.append (φ 0) (i 0) - realOfList P.netlist.size cert.z₀)‖) ∧
    ∀ (u : ℝ → Fin P.netlist.inputs → ℝ), ContinuousOn u (Ici 0) →
      ∀ φ i, P.netlist.IsTrajectoryOn u φ i (Ici 0) →
      realOfSparse cert.dec.k P.netlist.size cert.dec.Uᵢ *ᵥ
          (Fin.append (φ 0) (i 0) - realOfList P.netlist.size cert.z₀) = 0 →
      ∀ t ≥ 0, (fun o => (P.probes.get o).eval (φ t) (i t)) -
          (fun o => (P.probes.get o).eval
            (fun j => realOfList P.netlist.size cert.z₀ (Fin.castAdd _ j))
            (fun b => realOfList P.netlist.size cert.z₀ (Fin.natAdd _ b))) =
        (P.netlist.sparseRealization cert.dec cert.real P.probes).D *ᵥ u t +
          ∫ τ in 0..t, (P.netlist.sparseRealization cert.dec cert.real P.probes).responseKernel
            (t - τ) *ᵥ u τ

/-- **The guarantee holds when the certificate is accepted for the netlist.** -/
theorem NetlistCert.guarantee_of_check {cert : NetlistCert} {P : ParsedNetlist}
    (h : cert.check P.netlist = true) : cert.Guarantee P := by
  simp only [NetlistCert.check, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hc, hd⟩, he⟩, hz⟩, hl⟩ := h
  obtain ⟨h₁, h₂, h₃⟩ := Netlist.isExponentiallyStable_of_sparseChecks hc hd hz
    (LyapunovCert.isExponentiallyStable_of_check hl)
  exact ⟨h₁, h₂, h₃, fun u hu φ i hφ hx t ht =>
    hφ.probe_sub_eq_integral_sparse hc hd he hz P.probes hu hx ht⟩

/-- **Certified stability and input/output behaviour of the circuit described by a text.** If
`checkText s cert` holds, then `s` parses to a netlist `P`, and the circuit `P.netlist` has the
guarantee `cert.Guarantee P`: its operating point `cert.z₀` is exponentially stable, and its
zero-state response from the input ports to the probes of the text is that of the checked
realization. -/
theorem exists_parse_of_checkText {s : String} {cert : NetlistCert}
    (h : checkText s cert = true) : ∃ P, parse s = .ok P ∧ cert.Guarantee P := by
  unfold checkText at h
  split at h
  · rename_i P hP
    exact ⟨P, hP, NetlistCert.guarantee_of_check h⟩
  · exact absurd h Bool.false_ne_true

end Cslib.Electrical.Text
