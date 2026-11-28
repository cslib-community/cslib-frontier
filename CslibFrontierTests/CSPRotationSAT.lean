/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module

public import CslibFrontier.Computability.Complexity.Problems.CSP.RotationSAT

/-!
# Supplied-rotation CSP clients

Ordinary module imports exercise the named fields, generated encoding rules and acceptance
conditions. Large binary names, cyclic order, malformed inputs and nullary truth are observable.
-/

open Cslib.Logic.PL Cslib.Complexity Cslib.Complexity.CSP Turing.MultiTapeTM

public section

namespace CSPRotationSATTests

private abbrev ternary : RotationInstance Unit :=
  ⟨[⟨(), [2 ^ 100, 9, 7]⟩], ⟨[0, 3, 2, 5, 4, 1]⟩⟩

example : encRotationInstance encUnit ternary =
    encCSPRotationCertificate encUnit encNat (ternary.constraints, ternary.rotation) := rfl

/-- Generated projection and construction certificates compose across an ordinary import. -/
theorem polyTime_eraseRotation : ComputableInPolyTime
    (fun I : RotationInstance Unit => RotationInstance.mk I.constraints ⟨[]⟩)
    (encRotationInstance encUnit) (encRotationInstance encUnit) := by fun_prop

example : ComputableInPolyTime (RotationInstance.rotation : RotationInstance Unit → _)
    (encRotationInstance encUnit) Graph.encRotationCertificate := by fun_prop

example : ternary ∈ RotationCSPSAT (fun _ => 3) (fun _ _ => true) :=
  ⟨by decide, by decide, fun _ => false, by decide⟩

-- NP membership supplies an actual accepted polynomial-length witness for this raw record.
example : ∃ (p : Polynomial ℕ) (V : RotationInstance Unit × List Bool → Bool),
    ComputableInPolyTime V (encPair (encRotationInstance encUnit) encBits) encBool ∧
      ∃ w : List Bool, w.length = p.eval (encRotationInstance encUnit ternary).length ∧
        V (ternary, w) = true := by
  obtain ⟨p, V, hV, hcorrect⟩ := RotationCSPSAT.mem_NP encUnit (fun _ => 3) (fun _ _ => true)
  exact ⟨p, V, hV, (hcorrect ternary).mp
    ⟨by decide, by decide, fun _ => false, by decide⟩⟩

-- Mirroring a ternary order fails even though its underlying rotation has numerical genus zero.
example : (⟨ternary.constraints, ⟨[0, 5, 2, 1, 4, 3]⟩⟩ : RotationInstance Unit) ∉
    RotationCSPSAT (fun _ => 3) (fun _ _ => true) := by
  intro h
  have hbad : verifyRotationCertificate ternary.constraints ⟨[0, 5, 2, 1, 4, 3]⟩ = false :=
    by decide
  exact Bool.false_ne_true (hbad.symm.trans h.2.1)

example : (⟨ternary.constraints, ⟨[0, 3, 2, 5, 4, 2 ^ 100]⟩⟩ : RotationInstance Unit) ∉
    RotationCSPSAT (fun _ => 3) (fun _ _ => true) := by
  intro h
  have hbad : verifyRotationCertificate ternary.constraints ⟨[0, 3, 2, 5, 4, 2 ^ 100]⟩ = false :=
    by decide
  exact Bool.false_ne_true (hbad.symm.trans h.2.1)

example : ternary ∉ RotationCSPSAT (fun _ => 2) (fun _ _ => true) := by
  intro h
  have hw := h.1 ⟨(), [2 ^ 100, 9, 7]⟩ (by simp)
  contradiction

example : (⟨[⟨true, []⟩], ⟨[]⟩⟩ : RotationInstance Bool) ∈
    RotationCSPSAT (fun _ => 0) (fun b _ => b) :=
  ⟨by decide, by decide, fun _ => false, by decide⟩

example : (⟨[⟨false, []⟩], ⟨[]⟩⟩ : RotationInstance Bool) ∉
    RotationCSPSAT (fun _ => 0) (fun b _ => b) := by
  rintro ⟨_, _, σ, hσ⟩
  simp [CSP.eval, Constraint.eval] at hσ

example : (⟨[], ⟨[]⟩⟩ : RotationInstance Empty) ∈
    RotationCSPSAT (fun e => nomatch e) (fun e _ => nomatch e) :=
  ⟨by decide, by decide, fun _ => false, by decide⟩

end CSPRotationSATTests
