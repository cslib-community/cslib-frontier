/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Automation
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Computability.WordRAM.Time
import CslibFrontier.Computability.GenericRAM.Native.Certificate
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolySpace.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace

/-! Ordinary-import regression tests for polynomial resource-growth automation. -/

set_option linter.privateModule false

open Turing.MultiTapeTM

section

variable {α : Type*} {size u v : α → ℕ}

example (hu : PolyBounded size u) (hv : PolyBounded size v) :
    PolyBounded size (fun a => 7 * (u a + 1) ^ 3 + v a * (2 * size a + 5)) := by
  growth_poly

example (hu : PolyBounded size u) :
    PolyBounded size (fun a => Nat.log 2 (u a + 1) + Nat.sqrt (size a * u a)) := by
  growth_poly

example (hu : PolyBounded size u) (hv : PolyBounded size v) :
    PolyBounded size (fun a => max (u a) (v a) + (u a - v a) + u a / (v a + 1)) := by
  growth_poly

-- Ceiling logarithms (including degenerate bases) and remainders against arbitrary divisors.
example (hu : PolyBounded size u) :
    PolyBounded size (fun a =>
      Nat.clog 2 (u a + 1) + Nat.clog 1 (u a) + Nat.clog 0 (u a) + u a % (2 ^ size a)) := by
  growth_poly

-- One-sided minimum in both argument orders, clamping an exponential expression.
example (hu : PolyBounded size u) :
    PolyBounded size (fun a => min (u a) (2 ^ size a) + min (2 ^ size a) (u a + 1)) := by
  growth_poly

-- Conditionals: `ite`, non-dependent `dite`, and `cond`.
example {c : α → Prop} [DecidablePred c] {b : α → Bool}
    (hu : PolyBounded size u) (hv : PolyBounded size v) :
    PolyBounded size (fun a =>
      (if c a then u a else v a + 1) +
      (if _h : c a then 2 * u a else v a) +
      cond (b a) (u a ^ 2) (size a)) := by
  growth_poly

-- Structural `List.length` normalization across constructors and length-preserving/shrinking ops.
example {β γ : Type*} {xs ys : α → List β} {f : β → γ} {x : α → β}
    (hxs : PolyBounded size (fun a => (xs a).length))
    (hys : PolyBounded size (fun a => (ys a).length))
    (hu : PolyBounded size u) :
    PolyBounded size (fun a =>
      ((x a :: xs a ++ ys a).map f).length +
      (List.replicate (u a) (x a)).length +
      (xs a).reverse.length +
      ((xs a).take (2 ^ size a)).length +
      ((List.replicate (2 ^ size a) (x a)).take (u a)).length +
      ((ys a).drop (2 ^ size a)).length +
      (List.append (xs a) (ys a)).length +
      ([] : List β).length) := by
  growth_poly

-- Substitution through a bound at another size, found in the context.
example {β : Type*} {size' v : β → ℕ} {g : α → β}
    (hv : PolyBounded size' v) (hg : PolyBounded size (fun a => size' (g a))) :
    PolyBounded size (fun a => v (g a) + size a) := by
  growth_poly

-- Substitution into a polynomially bounded function of one natural number.
example {F : ℕ → ℕ} (hF : Cslib.PolynomiallyBounded F) (hu : PolyBounded size u) :
    PolyBounded size (fun a => F (2 * u a + size a + 1)) := by
  growth_poly

-- A function of one natural number that `fun_prop` bounds, and an arithmetic definition.
example (hu : PolyBounded size u) :
    PolyBounded size (fun a => (fun n => 3 * n ^ 2 + 1) (u a) + Nat.succ (u a)) := by
  growth_poly

-- Leaves inside conjunctions; `IsPolynomial` below unfolds to one.
example (h : PolyBounded size u ∧ PolyBounded size v) :
    PolyBounded size (fun a => u a * v a + 1) := by
  growth_poly

-- A local `let` and an extra fact passed at the call.
example (h : PolyBounded size u ∧ True) : PolyBounded size (fun a => u a ^ 2) := by
  let B := fun a => u a * u a
  have : PolyBounded size B := by growth_poly
  growth_poly [h.1]

-- A variable exponent, variable logarithm base, unbounded dividend, and unknown function are
-- deliberately unsupported.
example (_hu : PolyBounded size u) : True := by
  fail_if_success have : PolyBounded id (fun n : ℕ => 2 ^ n) := by growth_poly
  fail_if_success have : PolyBounded size (fun a => u a ^ size a) := by growth_poly
  fail_if_success have : PolyBounded size (fun a => Nat.clog (size a) (u a)) := by growth_poly
  fail_if_success have : PolyBounded size (fun a => 2 ^ size a % u a) := by growth_poly
  fail_if_success have : PolyBounded id (fun n : ℕ =>
      if h : n < [2 ^ n].length then [2 ^ n][n] else 0) := by growth_poly
  fail_if_success have : PolyBounded size (fun a => Nat.factorial (u a)) := by growth_poly
  trivial

/--
error: growth_poly: no rule or local fact bounds
  (u a).factorial
by a polynomial in
  size a
Add a `PolyBounded` fact or a certificate for it to the context, or pass one as `growth_poly [h]`.
-/
#guard_msgs in
example (hu : PolyBounded size u) (hv : PolyBounded size v) :
    PolyBounded size (fun a => u a + v a * Nat.factorial (u a)) := by
  growth_poly

-- Failure is decided by bounded syntax-directed decomposition, within a small budget.
/--
error: growth_poly: no rule or local fact bounds
  (size a).factorial
by a polynomial in
  size a
Add a `PolyBounded` fact or a certificate for it to the context, or pass one as `growth_poly [h]`.
-/
#guard_msgs in
set_option maxHeartbeats 2000 in
-- A small budget: the unbounded factorial must be rejected with `growth_poly`'s diagnostic.
example (hu : PolyBounded size u) :
    let w := fun a => (u a + 1) ^ 4 * (2 * u a + 3) + (u a + size a) * (u a + 7)
    PolyBounded size (fun a => w a + Nat.factorial (size a)) := by
  intro w
  growth_poly

/--
error: growth_poly: no rule or local fact bounds
  a.factorial
by a polynomial in
  id a
Add a `PolyBounded` fact or a certificate for it to the context, or pass one as `growth_poly [h]`.
-/
#guard_msgs in
set_option maxHeartbeats 2000 in
-- A small budget: an unbounded `min` must try both sides once and report `growth_poly`'s error.
example : PolyBounded id (fun n : ℕ => min (2 ^ n) n.factorial) := by
  growth_poly

end

-- Leaves from polynomial-time certificates: the encoded output length, and a unary value.
example {α β : Type} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool} {f : α → β} {g : α → ℕ}
    (hf : ComputableInPolyTime f encIn encOut) (hg : ComputableInPolyTime g encIn encUnary) :
    PolyBounded (fun a => (encIn a).length)
      (fun a => 2 * (encOut (f a)).length + g a ^ 2 + (encIn a).length) := by
  growth_poly

-- A bit-string certificate bounds the word's length, and a composed unary one its value.
example {α : Type} {encIn : α ↪ List Bool} {g : α → List Bool} {h : α → List ℕ}
    (hg : ComputableInPolyTime g encIn encBits)
    (hh : ComputableInPolyTime (List.length ∘ h) encIn encUnary) :
    PolyBounded (fun a => (encIn a).length) (fun a => (g a).length * (h a).length) := by
  growth_poly

-- A certificate composed after another one, through its output-length bound.
example {α β γ : Type} {encIn : α ↪ List Bool} {encMid : β ↪ List Bool}
    {encOut : γ ↪ List Bool} {f : β → γ} {g : α → β}
    (hf : ComputableInPolyTime f encMid encOut) (hg : ComputableInPolyTime g encIn encMid) :
    PolyBounded (fun a => (encIn a).length) (fun a => (encOut (f (g a))).length + 1) := by
  growth_poly

-- A polynomial native certificate: its time bound from the definition of `IsPolynomial`, its
-- output length through the polynomial-time certificate it yields.
example {α β : Type} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool} {f : α → β}
    (c : Cslib.GenericRAM.NativeCertificate f encIn encOut) (hc : c.IsPolynomial) :
    PolyBounded (fun a => (encIn a).length) (fun a => c.time a * (encOut (f a)).length) := by
  growth_poly

-- Polynomial-space and logspace certificates through their output lengths, and a degree bound.
example {α β γ : Type} {encIn : α ↪ List Bool} {encMid : β ↪ List Bool}
    {encOut : γ ↪ List Bool} {f : α → β} {g : α → γ} {u : α → ℕ}
    (hf : ComputableInPolySpace f encIn encMid) (hg : ComputableInLogSpace g encIn encOut)
    (hu : DegreeBounded (fun a => (encIn a).length) u 3) :
    PolyBounded (fun a => (encIn a).length)
      (fun a => (encMid (f a)).length * (encOut (g a)).length + u a) := by
  growth_poly

-- Each certificate lemma of `growth_poly` is proved in the module its failure message names;
-- `CslibFrontierTests/PolynomialGrowthImports.lean` checks the messages without them.
open Lean in
run_meta do
  let env ← getEnv
  for l in Cslib.Tactic.GrowthPoly.certificateLemmas ++ [Cslib.Tactic.GrowthPoly.encListLemma] do
    let some i := env.getModuleIdxFor? l.name | throwError "{l.name} is not imported"
    let home := env.header.moduleNames[i.toNat]!
    unless home == l.module do throwError "{l.name} is proved in {home}, not {l.module}"

/-! ### Multi-step unfolding, structure projections, `encList` element counts, and `encPair` -/

private def innerStepCost (x y : ℕ) : ℕ :=
  let s := x + y
  Nat.succ (2 * s ^ 2)

private def branchStepCost (ok : Bool) (x y : ℕ) : ℕ :=
  if ok then innerStepCost x y else cond ok x (y + 3)

private def outerWrapperCost (ok : Bool) (x y : ℕ) : ℕ :=
  branchStepCost ok x y

private structure CostBundle (α : Type*) where
  time : α → ℕ
  space : α → ℕ

private def mkBranchBundle {α : Type*} (ok : α → Bool) (b₁ b₂ : CostBundle α) : CostBundle α where
  time a := if ok a then b₁.time a else b₂.time a
  space a := b₁.space a + (if _h : ok a = true then b₁.space a else b₂.space a)

private def wrapBundle {α : Type*} (b : CostBundle α) : CostBundle α :=
  { time := b.time, space := b.space }

-- Multi-step unfolding across nested helper definitions, `let` bindings, `ite`, `cond`, and `succ`.
example {α : Type*} {size u v : α → ℕ} {ok : α → Bool}
    (hu : PolyBounded size u) (hv : PolyBounded size v) :
    PolyBounded size (fun a => outerWrapperCost (ok a) (u a) (v a)) := by
  growth_poly

-- Non-class structure projections through multi-step combinators (`ite` and non-dependent `dite`).
example {α : Type*} {size : α → ℕ} {ok : α → Bool} {b₁ b₂ : CostBundle α}
    (h₁ : PolyBounded size b₁.space) (h₂ : PolyBounded size b₂.space) :
    PolyBounded size (wrapBundle (mkBranchBundle ok b₁ b₂)).space := by
  growth_poly

-- Element-count leaf `(fl a).length` derived from `ComputableInPolyTime fl encIn (encList enc)`,
-- including reducible encoding abbreviations (`abbrev`).
private abbrev encNestedNat : List (List ℕ) ↪ List Bool := encList (encList encNat)

example {α : Type} {encIn : α ↪ List Bool} {fl : α → List ℕ} {rows : α → List (List ℕ)}
    {p : α → ℕ}
    (hp : ComputableInPolyTime p encIn encUnary)
    (hfl : ComputableInPolyTime fl encIn (encList encNat))
    (hrows : ComputableInPolyTime rows encIn encNestedNat) :
    PolyBounded (fun a => (encIn a).length)
      (fun a => ((rows a).length + 1) * (2 * ((fl a).length * (2 * (p a + 1) + 1)) + 1)) := by
  growth_poly

-- `encPair` length expansion (including nested pairs) and direct `PolynomiallyBounded` leaf
-- matching at `size = id`.
example {α β γ : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool} {encC : γ ↪ List Bool}
    {f : ℕ → α} {g : ℕ → β} {h : ℕ → γ}
    (hf : Cslib.PolynomiallyBounded fun n => (encA (f n)).length)
    (hg : Cslib.PolynomiallyBounded fun n => (encB (g n)).length)
    (hh : Cslib.PolynomiallyBounded fun n => (encC (h n)).length) :
    PolyBounded id
      (fun n => (encPair (encPair encA encB) encC ((f n, g n), h n)).length) := by
  growth_poly

-- Soundness: element-count derivation bounds `(fl a).length`, NOT individual element values
-- `(fl a).headD 0` when elements are binary-encoded.
example {α : Type} {encIn : α ↪ List Bool} {fl : α → List ℕ}
    (_hfl : ComputableInPolyTime fl encIn (encList encNat)) : True := by
  fail_if_success
    have : PolyBounded (fun a => (encIn a).length) (fun a => (fl a).headD 0) := by growth_poly
  trivial

example {F : ℕ → ℕ} (hF : Cslib.PolynomiallyBounded F) :
    Cslib.PolynomiallyBounded (fun n => 3 * F n ^ 2 + Nat.log 2 (n + 1)) := by
  growth_poly

-- Polynomial growth does not establish an exact word-width admission condition.
example : PolyBounded id (fun n : ℕ => n + 1) ∧ Cslib.WordRAM.Fits 3 7 ∧
    ¬Cslib.WordRAM.Fits 3 8 := by
  refine ⟨?_, by decide, by decide⟩
  growth_poly

example : True := by
  fail_if_success have : Cslib.WordRAM.Fits 3 8 := by growth_poly
  trivial

/-! ### Extensible `@[growth_poly]`, powers of logs, local bounds, and input decomposition -/

private def customMetric (n : ℕ) : ℕ := 3 * n + 2

@[growth_poly]
private theorem customMetric_le (n : ℕ) : customMetric n ≤ 3 * n + 2 := le_rfl

private def customMix (m n : ℕ) : ℕ := m + 2 * n

@[growth_poly]
private theorem polyBounded_customMix {α : Type*} {size u v : α → ℕ}
    (hu : PolyBounded size u) (hv : PolyBounded size v) :
    PolyBounded size (fun a => customMix (u a) (v a)) :=
  hu.add ((PolyBounded.const 2).mul hv)

-- Custom `@[growth_poly]` pointwise bound and closure rules work without unfolding.
example {α : Type*} {size u v : α → ℕ} (hu : PolyBounded size u) (hv : PolyBounded size v) :
    PolyBounded size (fun a => customMetric (u a) + customMix (u a) (v a)) := by
  growth_poly

-- Invalid `@[growth_poly]` targets are rejected at registration time.
/--
error: `growth_poly` requires a non-variable head on the left-hand side, got
  ?n
-/
#guard_msgs in
@[growth_poly]
private theorem badGrowthPolyWildcard (n : ℕ) : n ≤ n := le_rfl

/--
error: `growth_poly` expects a theorem concluding `lhs ≤ rhs`, `lhs = rhs` in `ℕ`, or `Turing.MultiTapeTM.PolyBounded size (fun a => op …)`, got
  True
-/
#guard_msgs in
@[growth_poly]
private theorem badGrowthPolyConcl : True := trivial

-- `Nat.log2`, `b ^ Nat.log b _`, exponent splitting (`+`, `*`, `min`, local bound),
-- and expanded `@[growth_poly]` `List.length` rules.
example {α β : Type*} {size u v : α → ℕ} {xs : α → List β} {ys : α → List ℕ}
    {p : β → Bool} {c k : ℕ}
    (hu : PolyBounded size u)
    (hxs : PolyBounded size (fun a => (xs a).length))
    (hlogb : ∀ a, v a ≤ c * (Nat.log 2 (u a) + 1)) :
    PolyBounded size (fun a =>
      Nat.log2 (u a) + 2 ^ (c * (Nat.log 2 (u a) + 1) + k) +
      2 ^ min (size a) (Nat.log 2 (u a)) + 2 ^ (v a) +
      ((xs a).filter p).length + (List.range (u a)).length +
      (List.finRange (u a)).length + ((xs a).zip (ys a)).length +
      (xs a).zipIdx.length + (xs a).tail.length + ((xs a).eraseIdx (v a)).length) := by
  growth_poly

-- Local pointwise `fvar` bounds.
example {α : Type*} {size f : α → ℕ} {d : ℕ}
    (hf : ∀ a, f a ≤ size a + 3) :
    PolyBounded size (fun a => f a + 2 * (f a + 1) ^ d) := by
  growth_poly

-- Non-reducible `PolyBounded` wrapper + nested-`Prod` `abbrev` projection in `PolyBounded.comp`.
private abbrev NestedProdCtx : Type := (ℕ × ℕ) × (List Bool × ℕ)

private def WrappedPolyBounded {α : Type*} (size cost : α → ℕ) : Prop :=
  PolyBounded size cost

example {β γ : Type*} {size : (ℕ × β) × (NestedProdCtx × γ) → ℕ}
    {size' cost : β × NestedProdCtx → ℕ}
    (hcost : WrappedPolyBounded size' cost)
    (hsize' : PolyBounded size (fun a => size' (a.1.2, a.2.1))) :
    PolyBounded size (fun a => cost (a.1.2, a.2.1) + 1) := by
  growth_poly

-- Automatic decomposition of `enc_structure` + `encPair` + `encList` + `encUnary` + `encBits`
-- input components, and goal-side `encNat` / `encBool` / `enc_structure` lengths.
private structure GrowthSample where
  items : List ℕ
  tag : Bool
  width : ℕ
  bits : List Bool

private enc_structure encGrowthSample : GrowthSample where
  items : (encList encNat), tag : encBool, width : encUnary, bits : encBits

example :
    PolyBounded (fun x : GrowthSample => (encGrowthSample x).length)
      (fun x => x.items.length * x.width + x.bits.length +
        (encNat x.items.length).length + (encBool x.tag).length +
        (encGrowthSample x).length) := by
  growth_poly

-- Soundness: global `Nat.log2_le_self` is not applied inside exponents, and a linear local bound
-- on an exponent does not make `2 ^ f a` polynomial.
example {α : Type*} {size f : α → ℕ} (_hf : ∀ a, f a ≤ size a) : True := by
  fail_if_success have : PolyBounded size (fun a => 2 ^ Nat.log2 (size a)) := by growth_poly
  fail_if_success have : PolyBounded size (fun a => 2 ^ f a) := by growth_poly
  trivial
