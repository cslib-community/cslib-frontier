/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (explicit realization-certificate regression tests)

public import CslibFrontier.Computability.WordRAM.Realization.BoundedTactic
public import CslibFrontierTests.WordRAMRealizeGraded
public import CslibFrontierTests.WordRAMGlueNamed

/-!
# Supplying certificates to `realize`

Opaque methods force use of the supplied proof applications: the hypotheses producing them
are functions, rather than certificates already visible to local lookup. The examples retain
genuine domains and computed-argument fit conditions, and pin ordinary local-certificate
priority, list order and boundedness. Scalar certificates additionally reuse the `fun_prop`
registry, without unfolding their functions or forgetting their domains and value envelopes.
-/

public section

namespace CslibFrontierTests.WordRAMRealizeCertificates

open Cslib.DataStructure Cslib.WordRAM Cslib.WordRAM.Realization

private abbrev word : ℕ ↪ (Fin 1 → ℕ) := WordEncoding.encode
private abbrev pairWords : ℕ × ℕ ↪ (Fin 2 → ℕ) := WordEncoding.encode

/-- Its exposed arithmetic has a larger intermediate than its certified implementation. -/
private def cancelAddress (n : ℕ) : ℕ := (100 + n) - (100 + n)

private theorem cancelAddress_glue : GlueComputable .exact
    (fun v : Fin 1 → ℕ => cancelAddress (v 0)) (fun _ => True) (fun _ => 0) := by
  simp only [cancelAddress, Nat.sub_self]
  exact GlueComputable.const 0 (fun _ _ => le_rfl)

-- Interpreting a query preserves the named scalar certificate before normalizing its address.
-- Unfolding the helper instead would unnecessarily demand that `100 + n` fit.
example : Realizes .exact (fun n : ℕ =>
    PFunctor.FreeM.liftM (P := ⟨ℕ, fun _ => ℕ⟩)
      (fun a => Memory.read (cancelAddress a)) (PFunctor.FreeM.lift n))
    word word (fun _ _ _ => True) (fun _ _ => 0) := by
  realize [cancelAddress_glue] <;> exact fits_zero _

-- An imported scalar body is unavailable until its certificate is supplied. Its two arguments
-- are computed from the same live word, then used as a genuine memory address.
example : Realizes .exact
    (fun n : ℕ => Memory.read (WordRAMGlueNamed.weighted ![n + 1, n + n])) word word
    (fun w n _ => 5 * n + 1 ≤ 100 ∧ Fits w 100) (fun _ _ => 0) := by
  fail_if_success realize
  realize [WordRAMGlueNamed.weighted_glue] <;> dsimp [Fits] at * <;> omega

-- Neither the opaque helper's domain nor its internal envelope follows from result fitting.
example : True := by
  fail_if_success
    have _ : Realizes .exact (fun n : ℕ => pure (WordRAMGlueNamed.twice n)) word word
        (fun w _ _ => Fits w 100) (fun _ _ => 0) := by
      realize [WordRAMGlueNamed.twice_glue] <;> omega
  fail_if_success
    have _ : Realizes .exact (fun n : ℕ => pure (WordRAMGlueNamed.twice n)) word word
        (fun w n _ => 2 * n ≤ 100 ∧ Fits w (WordRAMGlueNamed.twice n)) (fun _ _ => 0) := by
      realize [WordRAMGlueNamed.twice_glue] <;> dsimp [Fits] at * <;> omega
  trivial

-- A pointwise family of constant emitters must not turn a runtime argument into a fixed
-- program parameter. There is no uniform certificate for the arbitrary function `f`.
example (f : ℕ → ℕ)
    (_hc : ∀ c, GlueComputable .exact (fun v : Fin 1 → ℕ => f c + v 0)
      (fun _ => True) (fun v => f c + v 0)) : True := by
  fail_if_success
    have _ : Realizes .exact (fun d : ℕ × ℕ => pure (f d.1 + d.2)) pairWords word
        (fun w d _ => Fits w (f d.1 + d.2)) (fun _ _ => 0) := by
      realize <;> exact h
  trivial

section

attribute [local fun_prop] WordRAMGlueNamed.twice_glue

-- Registered scalar facts are found with no list or local copy, including under arithmetic.
example : Realizes .exact (fun n : ℕ => pure (WordRAMGlueNamed.twice (n + 1) + n)) word word
    (fun w n _ => 2 * (n + 1) ≤ 100 ∧ Fits w 100 ∧
      Fits w (WordRAMGlueNamed.twice (n + 1) + n)) (fun _ _ => 0) := by
  realize <;> dsimp [Fits] at * <;> omega

end

/-- An empty certificate list retains the ordinary realization rules. -/
theorem read_with_empty_certificates : Realizes .exact (fun n : ℕ => Memory.read n)
    (WordEncoding.encode (α := ℕ)) (WordEncoding.encode (α := ℕ))
    (fun _ _ _ => True) (fun _ _ => 0) := by
  realize []

-- A supplied theorem application is available for static wiring of an opaque method.
example (m : ℕ → Memory.Prog ℕ) (P : ℕ → ℕ → Memory.State → Prop)
    (hm : True → Realizes .exact m word word P (fun _ _ => 0)) :
    Realizes .exact (fun d : ℕ × ℕ => m d.2) pairWords word
      (fun w d s => P w d.2 s) (fun _ _ => 0) := by
  realize [hm trivial]
  exact h

-- Supplying a certificate leaves the actual fit and callee-domain conditions visible.
example (m : ℕ → Memory.Prog ℕ) (P : ℕ → ℕ → Memory.State → Prop)
    (hm : True → Realizes .exact m word word P (fun _ _ => 0)) :
    Realizes .exact (fun n : ℕ => m (n + 1)) word word
      (fun w n s => Fits w (n + 1) ∧ P w (n + 1) s) (fun _ _ => 0) := by
  realize [hm trivial]
  · exact h.1
  · exact h.2

-- Standard-basis subtraction can stage the argument without an exact-underflow premise.
example (m : ℕ → Memory.Prog ℕ) (P : ℕ → ℕ → Memory.State → Prop)
    (hm : True → Realizes .standard m word word P (fun _ _ => 0)) :
    Realizes .standard (fun d : ℕ × ℕ => m (d.1 - d.2)) pairWords word
      (fun w d s => P w (d.1 - d.2) s) (fun _ _ => 0) := by
  realize [hm trivial]
  exact h

-- Both applications refer to the caller's `hcert`, despite the macro's generated local facts.
-- The first method's reply becomes a live argument of the independently supplied second method.
example (first : ℕ → Memory.Prog ℕ) (next : ℕ × ℕ → Memory.Prog ℕ) (hcert : True)
    (hFirst : True → Realizes .exact first word word (fun _ _ _ => True) (fun _ _ => 0))
    (hNext : True → Realizes .exact next pairWords word (fun _ _ _ => True) (fun _ _ => 0)) :
    Realizes .exact (fun n : ℕ => do
      let a ← first n
      next (n, a)) word word (fun _ _ _ => True) (fun _ _ => 0) := by
  realize [hFirst hcert, hNext hcert]

-- The first matching supplied certificate has priority, including its genuine domain.
example (m : ℕ → Memory.Prog ℕ) (P : ℕ → ℕ → Memory.State → Prop)
    (hRestricted : True → Realizes .exact m word word P (fun _ _ => 0))
    (hTotal : True → Realizes .exact m word word (fun _ _ _ => True) (fun _ _ => 0)) :
    Realizes .exact m word word P (fun _ _ => 0) := by
  realize [hRestricted trivial, hTotal trivial]
  exact h

-- Reversing the list selects the total certificate, rather than the later restricted one.
example (m : ℕ → Memory.Prog ℕ) (P : ℕ → ℕ → Memory.State → Prop)
    (hRestricted : True → Realizes .exact m word word P (fun _ _ => 0))
    (hTotal : True → Realizes .exact m word word (fun _ _ _ => True) (fun _ _ => 0)) :
    Realizes .exact m word word (fun _ _ _ => True) (fun _ _ => 0) := by
  realize [hTotal trivial, hRestricted trivial]

-- A certificate already in the local context retains priority over a supplied alternative.
example (m : ℕ → Memory.Prog ℕ) (P : ℕ → ℕ → Memory.State → Prop)
    (hLocal : Realizes .exact m word word P (fun _ _ => 0))
    (hTotal : True → Realizes .exact m word word (fun _ _ _ => True) (fun _ _ => 0)) :
    Realizes .exact m word word P (fun _ _ => 0) := by
  realize [hTotal trivial]
  exact h

-- Supplied frontier-bounded certificates use the existing bounded frontend and static wiring.
example (m : ℕ → Memory.Prog ℕ) (P : ℕ → ℕ → Memory.State → Prop)
    (hm : True → RealizesBounded .exact m word word P (fun _ _ => 0)) :
    RealizesBounded .exact (fun d : ℕ × ℕ => m d.1) pairWords word
      (fun w d s => P w d.1 s) (fun _ _ => 0) := by
  realize [hm trivial]
  exact h

-- Neither a callee domain nor a computed-argument fit can be discharged by listing a certificate.
example (m : ℕ → Memory.Prog ℕ)
    (_hm : True → Realizes .exact m word word (fun _ n _ => 0 < n) (fun _ _ => 0)) :
    True := by
  fail_if_success
    have _ : Realizes .exact m word word (fun _ _ _ => True) (fun _ _ => 0) := by
      realize [_hm trivial]
  trivial

example (m : ℕ → Memory.Prog ℕ)
    (_hm : True → Realizes .exact m word word (fun _ _ _ => True) (fun _ _ => 0)) :
    True := by
  fail_if_success
    have _ : Realizes .exact (fun n : ℕ => m (n + 1)) word word
        (fun _ _ _ => True) (fun _ _ => 0) := by
      realize [_hm trivial]
  trivial

-- A concrete query-free method pays for every iteration and requires exact subtraction.
private def paidMethod (n : ℕ) : Memory.Prog ℕ :=
  iterate Cslib.WordRAM.Realization.Tests.identityBody () n (n - 1)

private theorem paidMethod_realizes : Realizes .exact paidMethod word word
    (fun _ n _ => 0 < n) (fun n _ => n) := by
  unfold paidMethod
  realize [CslibFrontierTests.WordRAMRealizeGraded.counted_bound_realizes]
  exact h

-- Generalization makes the method opaque; its supplied certificate is proved, not assumed.
-- The caller retains the staged argument's fit, genuine callee domain and paid work comparison.
example : Realizes .exact (fun d : ℕ × ℕ => paidMethod (d.1 + d.1)) pairWords word
    (fun w d _ => Fits w (d.1 + d.1) ∧ 0 < d.1 + d.1 ∧ d.1 + d.1 ≤ d.2)
    (fun d _ => d.2) := by
  generalize heq : paidMethod = m
  have hPaid : True → Realizes .exact m word word
      (fun _ n _ => 0 < n) (fun n _ => n) := by
    intro _
    rw [← heq]
    exact paidMethod_realizes
  fail_if_success realize
  realize [hPaid trivial]
  · exact h.1
  · exact h.2.1
  · exact h.2.2

-- At width two the caller domain is inhabited, and its positive-work method returns one.
example : Fits 2 (1 + 1) ∧ 0 < 1 + 1 ∧ 1 + 1 ≤ 2 ∧ paidMethod (1 + 1) = pure 1 := by
  exact ⟨by decide, by decide, by decide,
    Cslib.WordRAM.Realization.Tests.identity_iterate 2 1⟩

-- Listing a certificate with unpaid local work cannot establish a zero-work contract.
example (m : ℕ → Memory.Prog ℕ)
    (_hm : True → Realizes .exact m word word (fun _ _ _ => True) (fun n _ => n)) :
    True := by
  fail_if_success
    have _ : Realizes .exact m word word (fun _ _ _ => True) (fun _ _ => 0) := by
      realize [_hm trivial]
  trivial

-- An ordinary certificate supplies no frontier-bounded witness for an opaque method.
example (m : ℕ → Memory.Prog ℕ)
    (_hm : True → Realizes .exact m word word (fun _ _ _ => True) (fun _ _ => 0)) :
    True := by
  fail_if_success
    have _ : RealizesBounded .exact m word word (fun _ _ _ => True) (fun _ _ => 0) := by
      realize [_hm trivial]
  trivial

end CslibFrontierTests.WordRAMRealizeCertificates
