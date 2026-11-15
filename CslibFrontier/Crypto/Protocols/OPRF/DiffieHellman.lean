/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.PMF
public import Mathlib.Algebra.Module.ZMod
import CslibFrontier.Crypto.Computational.DiffieHellman.Finite
import CslibFrontier.Probability.PMF.Uniform
import Mathlib.Algebra.Field.ZMod

/-!
# Diffie–Hellman oblivious pseudorandom functions (Boneh–Shoup §11.6.3)

[BonehShoup2023], Section 11.6.3 (pp. 454–456), defines the function
`F′(k, x) = H′(x, H(x)^k)` of equation (11.21) over a cyclic group `G` of prime order `q` with
generator `g`, and gives two protocols, `OPRF1` and `OPRF2`, by which a sender holding the key `k`
and a receiver holding the input `x` evaluate `F′(k, x)`. Here `G` is written additively as a
`ZMod q`-module, so `H(x)^k` is `k • H x`, `g^k` is `k • g`, and the hashed input `H(x)` is an
element `h : G`:

* In `OPRF1` (pp. 454–455), the receiver draws a uniform nonzero exponent `ρ : (ZMod q)ˣ` and
  sends `v = blind ρ h = (ρ : ZMod q) • h`; the sender returns `w = respond k v = k • v`; the
  receiver unblinds `unblind ρ w = ((ρ⁻¹ : (ZMod q)ˣ) : ZMod q) • w` and applies `H' x`.
* In `OPRF2` (p. 456), the sender publishes `u = k • g`; the receiver draws `ρ : (ZMod q)ˣ` and
  `τ : ZMod q`, sends `v = maskedBlind g ρ τ h = blind ρ h + τ • g`, and unblinds the sender's
  reply `w` as `maskedUnblind u ρ τ w = unblind ρ (w - τ • u)`.

This module formalizes the steps of both protocols as functions on group elements, their
correctness, the exact distribution of the receiver's message in each protocol, and the joint
distribution of the receiver's message and unblinded group element against a deviating `OPRF2`
sender that adds an error `d v` to its response. The six protocol-step definitions are exposed so
that tests and downstream protocols (such as the adaptive oblivious transfer of Section 11.6.4) can
unfold them directly.

## Deviations from [BonehShoup2023]

* **Group elements only.** The protocols are expressed as operations on `G` and exact `PMF` laws of
  uniform exponents, through an arbitrary continuation `f` as in
  `Cslib.Crypto.uniformOfFintype_bind_smul_add`. Interactive protocol executions, random-oracle
  games for `H` and `H'`, that `F′` is a PRF under CDH (Exercise 11.3, p. 458), that a wrong output
  in `OPRF2` is uniform in `Y` when `H'` is a random oracle, and receiver security under one-more
  Diffie–Hellman (pp. 455–456) are not formalized here.
* **Invertible blinding exponents without primality.** Because `ρ` is typed in `(ZMod q)ˣ`,
  correctness (`unblind_respond_blind`, `maskedUnblind_respond_maskedBlind`), the general
  invariance `uniformOfFintype_bind_blind_units_smul`, the `OPRF2` message law
  `uniformOfFintype_bind_maskedBlind`, and the general deviating-sender identity
  `uniformOfFintype_bind_maskedUnblind_add` need no primality of `q`. For prime `q`, `(ZMod q)ˣ` is
  the book's `ℤ_q \ {0}`.
* **Two printed independence/uniformity statements in §11.6.3 are false as stated, by `1 / q` at
  the identity element `0`:**
  1. For `OPRF1` (p. 455), the book states that with `ρ` uniform in `ℤ_q \ {0}`, the receiver's
     message `v = H(x)^ρ` is "a random group element, statistically independent of `x`". Because
     `ρ` is nonzero, `blind ρ 0 = 0` always, whereas for `h ≠ 0` in a prime-order group generated
     by `g`, `blind ρ h` is uniform on `G \ {0}` (it has the law of `blind ρ g` for uniform
     `ρ : (ZMod q)ˣ`, at statistical distance `1 / q` from the uniform distribution on `G`). Thus
     `v` is independent of `x` only among inputs with `H(x) ≠ 0`, as stated in
     `uniformOfFintype_bind_blind_of_ne_zero`.
  2. For `OPRF2` (p. 456), the book states that when a deviating sender replies to `v` with
     `w = v^k · d` for `d ≠ 1` (additively `respond k v + d v` with `d v ≠ 0`), the receiver
     computes `k • h + unblind ρ (d v)` where the error term `unblind ρ (d v)` "is just a random
     group element (uniformly distributed over `G`)". Because both `ρ` and `d v` are nonzero,
     `unblind ρ (d v)` is never `0`: for prime `q` and generator `g`, it has the law of `blind ρ g`
     for uniform `ρ : (ZMod q)ˣ` (uniform on `G \ {0}`, off by `1 / q` from uniform on `G`),
     independent of the message `τ • g`, as stated in
     `uniformOfFintype_bind_maskedUnblind_add_of_ne_zero`.

## Main definitions

* `Cslib.Crypto.Protocols.OPRF.eval`: the function `F′(k, x) = H′(x, k • H x)` of (11.21).
* `Cslib.Crypto.Protocols.OPRF.respond`: the sender's step `v ↦ k • v` in both protocols.
* `Cslib.Crypto.Protocols.OPRF.blind`, `Cslib.Crypto.Protocols.OPRF.unblind`: the receiver's
  blinding and unblinding steps in `OPRF1`.
* `Cslib.Crypto.Protocols.OPRF.maskedBlind`, `Cslib.Crypto.Protocols.OPRF.maskedUnblind`: the
  receiver's masked blinding and unblinding steps in `OPRF2`.

## Main results

* `Cslib.Crypto.Protocols.OPRF.unblind_respond_blind`,
  `Cslib.Crypto.Protocols.OPRF.apply_unblind_respond_blind`: correctness of `OPRF1`.
* `Cslib.Crypto.Protocols.OPRF.maskedUnblind_respond_add`: in `OPRF2`, if the sender adds `d` to
  its honest response, the receiver computes `k • h + unblind ρ d`.
* `Cslib.Crypto.Protocols.OPRF.maskedUnblind_respond_maskedBlind`,
  `Cslib.Crypto.Protocols.OPRF.apply_maskedUnblind_respond_maskedBlind`: correctness of `OPRF2`.
* `Cslib.Crypto.Protocols.OPRF.uniformOfFintype_bind_blind_units_smul`,
  `Cslib.Crypto.Protocols.OPRF.uniformOfFintype_bind_blind_of_ne_zero`: the law of the receiver's
  message in `OPRF1` for nonzero hashed inputs.
* `Cslib.Crypto.Protocols.OPRF.uniformOfFintype_bind_maskedBlind`: the law of the receiver's
  message in `OPRF2`.
* `Cslib.Crypto.Protocols.OPRF.uniformOfFintype_bind_maskedUnblind_add`,
  `Cslib.Crypto.Protocols.OPRF.uniformOfFintype_bind_maskedUnblind_add_of_ne_zero`: the joint law
  of the receiver's message and unblinded group element against a deviating `OPRF2` sender.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 11.6.3, equation (11.21) and Protocols `OPRF1` and `OPRF2`,
  pp. 454–456.
-/

public section

open Cslib Cslib.Probability

namespace Cslib.Crypto.Protocols.OPRF

/-! ## The function and the two protocols -/

section Protocol

variable {G : Type} [AddCommGroup G] {q : ℕ} [Module (ZMod q) G] {X Y : Type}

/-- The function `F′(k, x) = H′(x, H(x)^k)` of [BonehShoup2023], Section 11.6.3, equation (11.21)
(p. 454), written additively as `H' x (k • H x)`. -/
@[expose] def eval (H : X → G) (H' : X → G → Y) (k : ZMod q) (x : X) : Y :=
  H' x (k • H x)

/-- The sender's step in Protocols `OPRF1` and `OPRF2` ([BonehShoup2023], Section 11.6.3,
pp. 454–456): multiply the received group element `v` by the key `k`. -/
@[expose] def respond (k : ZMod q) (v : G) : G :=
  k • v

/-- The receiver's blinding step in Protocol `OPRF1` ([BonehShoup2023], Section 11.6.3,
pp. 454–455): multiply the hashed input `h` by an invertible exponent `ρ : (ZMod q)ˣ`. -/
@[expose] def blind (ρ : (ZMod q)ˣ) (h : G) : G :=
  (ρ : ZMod q) • h

/-- The receiver's unblinding step in Protocol `OPRF1` ([BonehShoup2023], Section 11.6.3,
pp. 454–455): multiply the sender's response `w` by `ρ⁻¹`. -/
@[expose] def unblind (ρ : (ZMod q)ˣ) (w : G) : G :=
  ((ρ⁻¹ : (ZMod q)ˣ) : ZMod q) • w

/-- The receiver's blinding step in Protocol `OPRF2` ([BonehShoup2023], Section 11.6.3, p. 456):
the `OPRF1` message `blind ρ h` masked by `τ • g`. -/
@[expose] def maskedBlind (g : G) (ρ : (ZMod q)ˣ) (τ : ZMod q) (h : G) : G :=
  blind ρ h + τ • g

/-- The receiver's unblinding step in Protocol `OPRF2` ([BonehShoup2023], Section 11.6.3, p. 456),
given the sender's public key `u = k • g`: subtract `τ • u` from `w` and apply `unblind ρ`. -/
@[expose] def maskedUnblind (u : G) (ρ : (ZMod q)ˣ) (τ : ZMod q) (w : G) : G :=
  unblind ρ (w - τ • u)

/-- Unblinding by `ρ` is blinding by `ρ⁻¹`. -/
theorem unblind_eq_blind_inv (ρ : (ZMod q)ˣ) (w : G) : unblind ρ w = blind ρ⁻¹ w := rfl

/-- Unblinding cancels blinding by the same unit `ρ`. -/
@[simp] theorem unblind_blind (ρ : (ZMod q)ˣ) (h : G) : unblind ρ (blind ρ h) = h := by
  rw [unblind, blind, smul_smul, Units.inv_mul, one_smul]

/-- Correctness of Protocol `OPRF1` ([BonehShoup2023], Section 11.6.3, p. 455) at the level of
group elements: unblinding the sender's response to `blind ρ h` yields `k • h`. -/
theorem unblind_respond_blind (ρ : (ZMod q)ˣ) (k : ZMod q) (h : G) :
    unblind ρ (respond k (blind ρ h)) = k • h := by
  rw [respond, blind, smul_comm k, ← blind, unblind_blind]

/-- Correctness of Protocol `OPRF1` ([BonehShoup2023], Section 11.6.3, p. 455): applying `H' x` to
the unblinded response on `H x` gives `eval H H' k x`. -/
theorem apply_unblind_respond_blind (H : X → G) (H' : X → G → Y) (ρ : (ZMod q)ˣ) (k : ZMod q)
    (x : X) : H' x (unblind ρ (respond k (blind ρ (H x)))) = eval H H' k x := by
  rw [unblind_respond_blind, eval]

/-- In Protocol `OPRF2` ([BonehShoup2023], Section 11.6.3, p. 456), if the sender answers
`v = maskedBlind g ρ τ h` with `respond k v + d`, the receiver's unblinded group element is
`k • h + unblind ρ d`. -/
theorem maskedUnblind_respond_add (g : G) (ρ : (ZMod q)ˣ) (τ k : ZMod q) (h d : G) :
    maskedUnblind (k • g) ρ τ (respond k (maskedBlind g ρ τ h) + d) = k • h + unblind ρ d := by
  have h1 : respond k (maskedBlind g ρ τ h) + d - τ • k • g = respond k (blind ρ h) + d := by
    rw [respond, maskedBlind, smul_add, smul_comm k τ g, respond]
    abel
  rw [maskedUnblind, h1, unblind, smul_add, ← unblind, ← unblind, unblind_respond_blind]

/-- Correctness of Protocol `OPRF2` ([BonehShoup2023], Section 11.6.3, p. 456) at the level of
group elements: when the sender responds honestly under public key `k • g`, `maskedUnblind`
recovers `k • h`. -/
theorem maskedUnblind_respond_maskedBlind (g : G) (ρ : (ZMod q)ˣ) (τ k : ZMod q) (h : G) :
    maskedUnblind (k • g) ρ τ (respond k (maskedBlind g ρ τ h)) = k • h := by
  simpa only [add_zero, unblind, smul_zero] using maskedUnblind_respond_add g ρ τ k h 0

/-- Correctness of Protocol `OPRF2` ([BonehShoup2023], Section 11.6.3, p. 456): applying `H' x` to
the unblinded response on `H x` gives `eval H H' k x`. -/
theorem apply_maskedUnblind_respond_maskedBlind (H : X → G) (H' : X → G → Y) (g : G)
    (ρ : (ZMod q)ˣ) (τ k : ZMod q) (x : X) :
    H' x (maskedUnblind (k • g) ρ τ (respond k (maskedBlind g ρ τ (H x)))) = eval H H' k x := by
  rw [maskedUnblind_respond_maskedBlind, eval]

end Protocol

/-! ## What the sender sees -/

section Laws

variable {G : Type} [AddCommGroup G] {q : ℕ} [NeZero q] [Module (ZMod q) G] {α : Type*}

/-- Without primality of `q`, hashed inputs that differ by an invertible factor `a : (ZMod q)ˣ`
induce the same `OPRF1` message distribution under a uniform `ρ : (ZMod q)ˣ`. -/
theorem uniformOfFintype_bind_blind_units_smul (a : (ZMod q)ˣ) (h : G) (f : G → PMF α) :
    ((PMF.uniformOfFintype (ZMod q)ˣ).bind fun ρ => f (blind ρ ((a : ZMod q) • h))) =
      (PMF.uniformOfFintype (ZMod q)ˣ).bind fun ρ => f (blind ρ h) := by
  have hmul : ∀ ρ : (ZMod q)ˣ, blind ρ ((a : ZMod q) • h) = blind (ρ * a) h := fun ρ => by
    rw [blind, blind, smul_smul, Units.val_mul]
  simp only [hmul]
  exact PMF.uniformOfFintype_bind_equiv (Equiv.mulRight a) fun ρ => f (blind ρ h)

/-- The receiver's message law in Protocol `OPRF1` ([BonehShoup2023], Section 11.6.3, p. 455): in a
group of prime order `q` generated by `g`, for every nonzero hashed input `h ≠ 0`, `blind ρ h`
under uniform `ρ : (ZMod q)ˣ` has the same distribution as `blind ρ g` (uniform on the nonzero
elements `G \ {0}`).

The book's statement that "the sender just sees a random group element, statistically independent
of `x`" is off by `1 / q` at the identity element: because `ρ` is drawn from `(ZMod q)ˣ`, if
`h = 0` then `blind ρ 0 = 0` always, whereas if `h ≠ 0` then `blind ρ h` is uniform on `G \ {0}`
and never `0`. Thus the message distribution is independent of `x` only among inputs with
`H x ≠ 0`. -/
theorem uniformOfFintype_bind_blind_of_ne_zero [Fact q.Prime] {g h : G}
    (hg : Function.Surjective fun c : ZMod q => c • g) (hh : h ≠ 0) (f : G → PMF α) :
    ((PMF.uniformOfFintype (ZMod q)ˣ).bind fun ρ => f (blind ρ h)) =
      (PMF.uniformOfFintype (ZMod q)ˣ).bind fun ρ => f (blind ρ g) := by
  obtain ⟨a, rfl⟩ := hg h
  have ha : a ≠ 0 := by
    rintro rfl
    exact hh (zero_smul _ _)
  exact uniformOfFintype_bind_blind_units_smul (Units.mk0 a ha) g f

/-- The receiver's message law in Protocol `OPRF2` ([BonehShoup2023], Section 11.6.3, p. 456): when
`g` generates `G`, for every hashed input `h` and every `ρ : (ZMod q)ˣ`, `maskedBlind g ρ τ h`
under uniform `τ : ZMod q` has the distribution of `τ • g`, so the message leaks nothing about `h`
or `ρ`. -/
theorem uniformOfFintype_bind_maskedBlind {g : G}
    (hg : Function.Surjective fun c : ZMod q => c • g) (ρ : (ZMod q)ˣ) (h : G) (f : G → PMF α) :
    ((PMF.uniformOfFintype (ZMod q)).bind fun τ => f (maskedBlind g ρ τ h)) =
      (PMF.uniformOfFintype (ZMod q)).bind fun τ => f (τ • g) := by
  simpa only [maskedBlind, add_comm] using Crypto.uniformOfFintype_bind_smul_add hg (blind ρ h) f

/-- Joint law of the receiver's message and unblinded group element against a deviating `OPRF2`
sender ([BonehShoup2023], Section 11.6.3, p. 456), without primality of `q`: when `g` generates `G`
and the sender adds `d v` to its honest response on message `v`, the message `v` and the element
computed by the receiver have the joint distribution of `(τ • g, k • h + blind ρ (d (τ • g)))` for
independent uniform `τ : ZMod q` and `ρ : (ZMod q)ˣ`. -/
theorem uniformOfFintype_bind_maskedUnblind_add {g : G}
    (hg : Function.Surjective fun c : ZMod q => c • g) (k : ZMod q) (h : G) (d : G → G)
    (f : G → G → PMF α) :
    ((PMF.uniformOfFintype (ZMod q)ˣ).bind fun ρ => (PMF.uniformOfFintype (ZMod q)).bind fun τ =>
        f (maskedBlind g ρ τ h)
          (maskedUnblind (k • g) ρ τ
            (respond k (maskedBlind g ρ τ h) + d (maskedBlind g ρ τ h)))) =
      (PMF.uniformOfFintype (ZMod q)).bind fun τ => (PMF.uniformOfFintype (ZMod q)ˣ).bind fun ρ =>
        f (τ • g) (k • h + blind ρ (d (τ • g))) := by
  simp only [maskedUnblind_respond_add]
  have hρ : ∀ ρ : (ZMod q)ˣ,
      ((PMF.uniformOfFintype (ZMod q)).bind fun τ =>
        f (maskedBlind g ρ τ h) (k • h + unblind ρ (d (maskedBlind g ρ τ h)))) =
      (PMF.uniformOfFintype (ZMod q)).bind fun τ => f (τ • g) (k • h + unblind ρ (d (τ • g))) :=
    fun ρ => uniformOfFintype_bind_maskedBlind hg ρ h fun v => f v (k • h + unblind ρ (d v))
  simp only [hρ]
  rw [PMF.bind_comm]
  refine congrArg _ (funext fun τ => ?_)
  simp only [unblind_eq_blind_inv]
  exact PMF.uniformOfFintype_bind_equiv (Equiv.inv (ZMod q)ˣ)
    fun ρ => f (τ • g) (k • h + blind ρ (d (τ • g)))

/-- Joint law of the receiver's message and unblinded group element against a deviating `OPRF2`
sender in a prime-order group ([BonehShoup2023], Section 11.6.3, p. 456): when `q` is prime, `g`
generates `G`, and the sender's deviation `d v` on every message `v` is nonzero, the message and
the element computed by the receiver are jointly distributed as `(τ • g, k • h + blind ρ g)` for
independent uniform `τ : ZMod q` and `ρ : (ZMod q)ˣ`.

The book's statement that for a wrong answer (`d ≠ 0`), the error term `unblind ρ d` (printed
`d^(1/ρ)`) "is just a random group element (uniformly distributed over `G`)" is off by `1 / q` at
the identity element: because `ρ` is a unit and `d v ≠ 0`, `unblind ρ (d v)` is never `0`, and is
instead distributed as `blind ρ g` for uniform `ρ : (ZMod q)ˣ` (uniform on `G \ {0}`). -/
theorem uniformOfFintype_bind_maskedUnblind_add_of_ne_zero [Fact q.Prime] {g : G}
    (hg : Function.Surjective fun c : ZMod q => c • g) (k : ZMod q) (h : G) (d : G → G)
    (hd : ∀ v, d v ≠ 0) (f : G → G → PMF α) :
    ((PMF.uniformOfFintype (ZMod q)ˣ).bind fun ρ => (PMF.uniformOfFintype (ZMod q)).bind fun τ =>
        f (maskedBlind g ρ τ h)
          (maskedUnblind (k • g) ρ τ
            (respond k (maskedBlind g ρ τ h) + d (maskedBlind g ρ τ h)))) =
      (PMF.uniformOfFintype (ZMod q)).bind fun τ => (PMF.uniformOfFintype (ZMod q)ˣ).bind fun ρ =>
        f (τ • g) (k • h + blind ρ g) := by
  rw [uniformOfFintype_bind_maskedUnblind_add hg]
  refine congrArg _ (funext fun τ => ?_)
  exact uniformOfFintype_bind_blind_of_ne_zero hg (hd _) fun x => f (τ • g) (k • h + x)

end Laws

end Cslib.Crypto.Protocols.OPRF
