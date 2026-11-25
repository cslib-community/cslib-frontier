/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Recursion.StackScheme
public import CslibFrontier.Computability.GenericRAM.Native.Combinators
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListLookup
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListPrimitives
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeOptionPrimitives
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Envelope
import CslibFrontier.Tactic.OptionMatch
import CslibFrontier.Tactic.EncLen

/-!
# Native Turing-machine certificates for explicit-stack recursion

The pure explicit-stack depth-first recursion scheme (`Cslib.Algorithms.StackRecursion.Scheme`,
`Invariant`, `State`, `Scheme.Loop`, `Scheme.Eval`, `Scheme.step`, `Scheme.run`) is defined
without any machine model in `CslibFrontier.Algorithms.Recursion.StackScheme`.

**The native certificate** (`Scheme.certificate`). The leaf step is an arbitrary native
certificate; the other components are polynomial-time (`Scheme.PolyTime`). One fixed machine runs
the stack machine for a natively computed number `fuel a` of steps (`NativeCertificate.iterate`)
and returns the register. When `2 * n - 1 ≤ fuel a` the result is `y` (`Scheme.run_eq_some`). If
every node, frame and value on the derivation has encoded length at most `F` and every leaf is
evaluated within time `TL` and space `SL`, the time is at most `fuel a + 1` times
`K ((h + 1) (F + 1)) ^ K + TL` and the workspace at most `K ((h + 1) (F + 1)) ^ K + SL`, up to
the cost of computing the fuel and the root and of the binary clock, for one constant `K` of the
scheme (`Scheme.certificate_le`). Only the stack is kept, so the workspace grows with the depth,
not with the number of nodes. The number of nodes of a recursion tree is bounded in
`CslibFrontier/Foundations/Data/Nat/RecursionTree.lean`.

This is the depth-first evaluation of the recursion in the proof of Theorem D.1 of
[OpenAI2026ETH] (Appendix D.4.7, p. 64), which keeps one sum over mode tuples and one product
over groups per stack level. The scheme is generic: the recursion of Appendix D.4 is one
instance, with its leaves evaluated by direct summation.

## Main definitions

* `Cslib.Algorithms.StackRecursion.Scheme.encState`: list-and-option encoding of stack states.
* `Cslib.Algorithms.StackRecursion.Scheme.PolyTime`: polynomial-time non-leaf components.
* `Cslib.Algorithms.StackRecursion.Scheme.stepCertificate`,
  `Cslib.Algorithms.StackRecursion.Scheme.leafCost`: one-step native certificate and pending-leaf
  cost.
* `Cslib.Algorithms.StackRecursion.Scheme.certificate`: one native machine for the clocked run.

## Main results

* `Cslib.Algorithms.StackRecursion.Scheme.exists_stepCertificate_le`: one step costs a polynomial
  in the state length plus the leaf certificate at a pending leaf.
* `Cslib.Algorithms.StackRecursion.Scheme.length_encState_le`: encoded length bound on good states.
* `Cslib.Algorithms.StackRecursion.Scheme.certificate_le`: time `fuel + 1` times a polynomial in
  `(h + 1) * (F + 1)` plus the leaf time, and workspace a polynomial plus the leaf space.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Appendix D.4.7 (p. 64).
-/

public section

namespace Cslib.Algorithms.StackRecursion.Scheme

open Cslib.GenericRAM Turing.MultiTapeTM

variable {X A Y : Type}

/-! ### The native machine -/

section Native

variable (R : Scheme X A Y) {encX : X ↪ List Bool} {encA : A ↪ List Bool} {encY : Y ↪ List Bool}

/-- The encoding of a machine state: the list of open frames, each a pair, then the optional
pending node and the optional returned value. -/
abbrev encState (encX : X ↪ List Bool) (encA : A ↪ List Bool) (encY : Y ↪ List Bool) :
    State X A Y ↪ List Bool :=
  encPair (encList (encPair encX encA)) (encPair (encOption encX) (encOption encY))

/-- **The polynomial-time components** of a scheme: everything but the leaf step. -/
structure PolyTime (encX : X ↪ List Bool) (encA : A ↪ List Bool) (encY : Y ↪ List Bool) :
    Prop where
  /-- The leaf test. -/
  isLeaf : ComputableInPolyTime R.isLeaf encX encBool
  /-- The initial accumulator. -/
  start : ComputableInPolyTime R.start encX encA
  /-- Child generation. -/
  next : ComputableInPolyTime (fun p : X × A => R.next p.1 p.2) (encPair encX encA)
    (encOption encX)
  /-- Absorbing a child's value. -/
  absorb : ComputableInPolyTime (fun p : (X × A) × Y => R.absorb p.1.1 p.1.2 p.2)
    (encPair (encPair encX encA) encY) encA
  /-- The value of a call. -/
  finish : ComputableInPolyTime (fun p : X × A => R.finish p.1 p.2) (encPair encX encA) encY

/-- Whether the register holds a pending leaf. -/
private def isLeafCall (σ : State X A Y) : Bool := σ.2.1.elim false R.isLeaf

/-- Evaluate a pending node as a leaf, keeping the stack. -/
private def leafStep (σ : State X A Y) : State X A Y :=
  (σ.1, none, σ.2.1.elim none fun x => some (R.leaf x))

/-- Every step but the evaluation of a leaf. -/
private def polyStep (σ : State X A Y) : State X A Y :=
  σ.2.1.elim
    (σ.2.2.elim σ fun y => σ.1.head?.elim σ fun f => R.resume f.1 (R.absorb f.1 f.2 y) σ.1.tail)
    (fun x => R.resume x (R.start x) σ.1)

/-- A step evaluates a leaf, or takes a polynomial-time step. -/
private theorem step_eq_ite (σ : State X A Y) :
    R.step σ = if isLeafCall R σ then leafStep R σ else polyStep R σ := by
  rcases σ with ⟨_ | ⟨⟨x, a⟩, st⟩, _ | c, _ | y⟩ <;>
    simp only [step, isLeafCall, leafStep, polyStep, Option.elim, List.head?, List.tail,
      Bool.false_eq_true, ite_false] <;> rfl

variable {R}

/-- Continuing a call is polynomial-time. -/
private theorem resume_polyTime (h : R.PolyTime encX encA encY) :
    ComputableInPolyTime (fun q : (X × A) × List (X × A) => R.resume q.1.1 q.1.2 q.2)
      (encPair (encPair encX encA) (encList (encPair encX encA))) (encState encX encA encY) := by
  have hnext := h.next
  have hfinish := h.finish
  unfold resume
  option_match_to_elim
  fun_prop

/-- The leaf test on the register is polynomial-time. -/
private theorem isLeafCall_polyTime (h : R.PolyTime encX encA encY) :
    ComputableInPolyTime (isLeafCall R) (encState encX encA encY) encBool := by
  have hreg := (ComputableInPolyTime.fst (encOption encX) (encOption encY)).comp
    (ComputableInPolyTime.snd (encList (encPair encX encA))
      (encPair (encOption encX) (encOption encY)))
  exact ComputableInPolyTime.optionElimWithInput (body := fun _ x => R.isLeaf x) hreg
    (ComputableInPolyTime.const false)
    (h.isLeaf.comp (ComputableInPolyTime.snd (encState encX encA encY) encX))

/-- Every step but the evaluation of a leaf is polynomial-time. -/
private theorem polyStep_polyTime (h : R.PolyTime encX encA encY) :
    ComputableInPolyTime (polyStep R) (encState encX encA encY) (encState encX encA encY) := by
  have hstack : ComputableInPolyTime (fun σ : State X A Y => σ.1) (encState encX encA encY)
      (encList (encPair encX encA)) :=
    ComputableInPolyTime.fst (encList (encPair encX encA))
      (encPair (encOption encX) (encOption encY))
  have hreg : ComputableInPolyTime (fun σ : State X A Y => σ.2) (encState encX encA encY)
      (encPair (encOption encX) (encOption encY)) :=
    ComputableInPolyTime.snd (encList (encPair encX encA))
      (encPair (encOption encX) (encOption encY))
  have hpend : ComputableInPolyTime (fun σ : State X A Y => σ.2.1) (encState encX encA encY)
      (encOption encX) := (ComputableInPolyTime.fst (encOption encX) (encOption encY)).comp hreg
  have hret : ComputableInPolyTime (fun σ : State X A Y => σ.2.2) (encState encX encA encY)
      (encOption encY) := (ComputableInPolyTime.snd (encOption encX) (encOption encY)).comp hreg
  -- A returned value is absorbed by the innermost open frame.
  have hframe : ComputableInPolyTime
      (fun q : (State X A Y × Y) × (X × A) =>
        R.resume q.2.1 (R.absorb q.2.1 q.2.2 q.1.2) q.1.1.1.tail)
      (encPair (encPair (encState encX encA encY) encY) (encPair encX encA))
      (encState encX encA encY) := by
    have hq := ComputableInPolyTime.fst (encPair (encState encX encA encY) encY)
      (encPair encX encA)
    have hf := ComputableInPolyTime.snd (encPair (encState encX encA encY) encY)
      (encPair encX encA)
    have hy := (ComputableInPolyTime.snd (encState encX encA encY) encY).comp hq
    have hσ := (ComputableInPolyTime.fst (encState encX encA encY) encY).comp hq
    have habs := h.absorb.comp (hf.prod hy)
    exact (resume_polyTime h).comp
      ((((ComputableInPolyTime.fst encX encA).comp hf).prod habs).prod
        ((ComputableInPolyTime.tail (encA := encPair encX encA)).comp (hstack.comp hσ)))
  have hreturn : ComputableInPolyTime
      (fun p : State X A Y × Y =>
        p.1.1.head?.elim p.1 fun f => R.resume f.1 (R.absorb f.1 f.2 p.2) p.1.1.tail)
      (encPair (encState encX encA encY) encY) (encState encX encA encY) := by
    have hσ := ComputableInPolyTime.fst (encState encX encA encY) encY
    have hhead : ComputableInPolyTime (fun p : State X A Y × Y => p.1.1.head?)
        (encPair (encState encX encA encY) encY) (encOption (encPair encX encA)) :=
      (ComputableInPolyTime.head? (encPair encX encA) (encL := encList (encPair encX encA))).comp
        (hstack.comp hσ)
    exact ComputableInPolyTime.optionElimWithInput
      (value := fun p : State X A Y × Y => p.1.1.head?) (fallback := fun p => p.1)
      (body := fun p f => R.resume f.1 (R.absorb f.1 f.2 p.2) p.1.1.tail) hhead hσ hframe
  have hnoCall : ComputableInPolyTime
      (fun σ : State X A Y =>
        σ.2.2.elim σ fun y => σ.1.head?.elim σ fun f => R.resume f.1 (R.absorb f.1 f.2 y) σ.1.tail)
      (encState encX encA encY) (encState encX encA encY) :=
    ComputableInPolyTime.optionElimWithInput (value := fun σ : State X A Y => σ.2.2)
      (fallback := fun σ => σ)
      (body := fun σ y => σ.1.head?.elim σ fun f => R.resume f.1 (R.absorb f.1 f.2 y) σ.1.tail)
      hret ComputableInPolyTime.id' hreturn
  have hcall : ComputableInPolyTime
      (fun p : State X A Y × X => R.resume p.2 (R.start p.2) p.1.1)
      (encPair (encState encX encA encY) encX) (encState encX encA encY) := by
    have hx : ComputableInPolyTime (fun p : State X A Y × X => p.2)
        (encPair (encState encX encA encY) encX) encX :=
      ComputableInPolyTime.snd (encState encX encA encY) encX
    have hst : ComputableInPolyTime (fun p : State X A Y × X => p.1.1)
        (encPair (encState encX encA encY) encX) (encList (encPair encX encA)) :=
      hstack.comp (ComputableInPolyTime.fst (encState encX encA encY) encX)
    exact (resume_polyTime h).comp ((hx.prod (h.start.comp hx)).prod hst)
  exact ComputableInPolyTime.optionElimWithInput (value := fun σ : State X A Y => σ.2.1)
    (fallback := fun σ => σ.2.2.elim σ fun y =>
      σ.1.head?.elim σ fun f => R.resume f.1 (R.absorb f.1 f.2 y) σ.1.tail)
    (body := fun σ x => R.resume x (R.start x) σ.1) hpend hnoCall hcall

end Native

section Certificate

variable {R : Scheme X A Y} {encX : X ↪ List Bool} {encA : A ↪ List Bool} {encY : Y ↪ List Bool}

private theorem stack_polyTime :
    ComputableInPolyTime (fun σ : State X A Y => σ.1) (encState encX encA encY)
      (encList (encPair encX encA)) :=
  ComputableInPolyTime.fst _ _

private theorem pending_polyTime :
    ComputableInPolyTime (fun σ : State X A Y => σ.2.1) (encState encX encA encY)
      (encOption encX) :=
  (ComputableInPolyTime.fst (encOption encX) (encOption encY)).comp (ComputableInPolyTime.snd _ _)

variable (R) in
/-- **The leaf step**: the leaf certificate on the pending node, keeping the stack. -/
private noncomputable def leafStepCertificate (leaf : NativeCertificate R.leaf encX encY) :
    NativeCertificate (leafStep R) (encState encX encA encY) (encState encX encA encY) :=
  (NativeCertificate.ofPolyTime stack_polyTime).prod ((NativeCertificate.const none).prod
    (NativeCertificate.option (value := fun σ : State X A Y => σ.2.1) (fallback := fun _ => none)
      (body := fun p : State X A Y × X => some (R.leaf p.2))
      (NativeCertificate.ofPolyTime pending_polyTime) (NativeCertificate.const none)
      (NativeCertificate.some (leaf.comp (NativeCertificate.payload _ encX)))))

/-- **One step of the machine**: the leaf certificate on a pending leaf, and a polynomial-time
step otherwise. -/
noncomputable def stepCertificate (h : R.PolyTime encX encA encY)
    (leaf : NativeCertificate R.leaf encX encY) :
    NativeCertificate R.step (encState encX encA encY) (encState encX encA encY) :=
  (NativeCertificate.branch (NativeCertificate.ofPolyTime (isLeafCall_polyTime h))
    (leafStepCertificate R leaf) (NativeCertificate.ofPolyTime (polyStep_polyTime h))).congr
    fun σ => (step_eq_ite R σ).symm

private theorem stepCertificate_time (h : R.PolyTime encX encA encY)
    (leaf : NativeCertificate R.leaf encX encY) (σ : State X A Y) :
    (stepCertificate h leaf).time σ =
      (NativeCertificate.ofPolyTime (isLeafCall_polyTime h)).time σ +
      if isLeafCall R σ then (leafStepCertificate R (encA := encA) leaf).time σ
      else (NativeCertificate.ofPolyTime (polyStep_polyTime h)).time σ := by rfl

private theorem stepCertificate_space (h : R.PolyTime encX encA encY)
    (leaf : NativeCertificate R.leaf encX encY) (σ : State X A Y) :
    (stepCertificate h leaf).space σ =
      (NativeCertificate.ofPolyTime (isLeafCall_polyTime h)).space σ +
      if isLeafCall R σ then (leafStepCertificate R (encA := encA) leaf).space σ
      else (NativeCertificate.ofPolyTime (polyStep_polyTime h)).space σ := by rfl

private theorem leafStepCertificate_time (leaf : NativeCertificate R.leaf encX encY)
    (st : List (X × A)) (x : X) (v : Option Y) :
    (leafStepCertificate R (encA := encA) leaf).time (st, some x, v) =
      (NativeCertificate.ofPolyTime (stack_polyTime (encX := encX) (encA := encA)
        (encY := encY))).time (st, some x, v) +
        ((encState encX encA encY (st, some x, v)).length +
          (2 * (NativeCertificate.ofPolyTime (pending_polyTime (encX := encX) (encA := encA)
            (encY := encY))).time (st, some x, v) +
            (encState encX encA encY (st, some x, v)).length +
            ((encPair (encState encX encA encY) encX ((st, some x, v), x)).length +
              leaf.time x))) := by rfl

private theorem leafStepCertificate_space (leaf : NativeCertificate R.leaf encX encY)
    (st : List (X × A)) (x : X) (v : Option Y) :
    (leafStepCertificate R (encA := encA) leaf).space (st, some x, v) =
      (NativeCertificate.ofPolyTime (stack_polyTime (encX := encX) (encA := encA)
        (encY := encY))).space (st, some x, v) +
        ((encState encX encA encY (st, some x, v)).length +
          (2 * (NativeCertificate.ofPolyTime (pending_polyTime (encX := encX) (encA := encA)
            (encY := encY))).space (st, some x, v) +
            (encState encX encA encY (st, some x, v)).length +
            ((encPair (encState encX encA encY) encX ((st, some x, v), x)).length +
              leaf.space x))) := by rfl

variable (R) in
/-- The leaf cost of a state: the leaf certificate's bound at a pending leaf, and zero
otherwise. -/
def leafCost (cost : X → ℕ) (σ : State X A Y) : ℕ :=
  σ.2.1.elim 0 fun x => if R.isLeaf x then cost x else 0

private theorem length_pending_le {σ : State X A Y} {x : X} (hx : σ.2.1 = some x) :
    (encX x).length ≤ (encState encX encA encY σ).length := by
  rcases σ with ⟨st, r, v⟩
  simp only at hx
  subst hx
  enc_len

/-- **The cost of one step**: a polynomial in the state length, plus the leaf certificate at a
pending leaf. -/
theorem exists_stepCertificate_le (h : R.PolyTime encX encA encY)
    (leaf : NativeCertificate R.leaf encX encY) :
    ∃ K : ℕ, ∀ σ : State X A Y,
      (stepCertificate h leaf).time σ ≤
          K * ((encState encX encA encY σ).length + 1) ^ K + R.leafCost leaf.time σ ∧
        (stepCertificate h leaf).space σ ≤
          K * ((encState encX encA encY σ).length + 1) ^ K + R.leafCost leaf.space σ := by
  have ht := NativeCertificate.ofPolyTime_isPolynomial (isLeafCall_polyTime h)
  have hp := NativeCertificate.ofPolyTime_isPolynomial (polyStep_polyTime h)
  have hs := NativeCertificate.ofPolyTime_isPolynomial (stack_polyTime (encX := encX)
    (encA := encA) (encY := encY))
  have hc := NativeCertificate.ofPolyTime_isPolynomial (pending_polyTime (encX := encX)
    (encA := encA) (encY := encY))
  -- Everything but the leaf certificate is polynomial in the state length.
  have hT := ((((ht.1.add hp.1).add hs.1).add ((PolyBounded.const 2).mul hc.1)).add
    ((PolyBounded.const 6).mul PolyBounded.self)).add (PolyBounded.const 1)
  have hS := ((((ht.2.add hp.2).add hs.2).add ((PolyBounded.const 2).mul hc.2)).add
    ((PolyBounded.const 6).mul PolyBounded.self)).add (PolyBounded.const 1)
  obtain ⟨KT, hKT⟩ := hT.exists_le_succ_pow
  obtain ⟨KS, hKS⟩ := hS.exists_le_succ_pow
  refine ⟨KT + KS, fun σ => ?_⟩
  have hT' := hKT (KT + KS) (Nat.le_add_right KT KS) σ
  have hS' := hKS (KT + KS) (Nat.le_add_left KS KT) σ
  rcases σ with ⟨st, _ | x, v⟩
  · rw [stepCertificate_time, stepCertificate_space]
    simp only [leafCost, isLeafCall, Option.elim, Bool.false_eq_true, ite_false, Nat.add_zero]
    constructor <;> omega
  · have hx := length_pending_le (encX := encX) (encA := encA) (encY := encY)
      (σ := (st, some x, v)) rfl
    rw [stepCertificate_time, stepCertificate_space]
    by_cases hl : R.isLeaf x = true
    · simp only [leafCost, isLeafCall, Option.elim, hl, ite_true]
      have hpair := length_encPair (enc₁ := encState encX encA encY) (enc₂ := encX)
        ((st, some x, v), x)
      dsimp only at hpair
      rw [leafStepCertificate_time, leafStepCertificate_space]
      constructor <;> omega
    · simp only [Bool.not_eq_true] at hl
      simp only [leafCost, isLeafCall, Option.elim, hl, Bool.false_eq_true, ite_false,
        Nat.add_zero]
      constructor <;> omega

/-- **The native machine** for the clocked run: one fixed machine, from native certificates for
the fuel and the root. -/
noncomputable def certificate (h : R.PolyTime encX encA encY)
    (leaf : NativeCertificate R.leaf encX encY) {I : Type} {encIn : I ↪ List Bool}
    {fuel : I → ℕ} {root : I → X} (cn : NativeCertificate fuel encIn encNat)
    (croot : NativeCertificate root encIn encX) :
    NativeCertificate (R.run fuel root) encIn (encOption encY) :=
  NativeCertificate.snd (NativeCertificate.snd (NativeCertificate.iterate cn
    ((NativeCertificate.const ([] : List (X × A))).prod
      ((NativeCertificate.some croot).prod (NativeCertificate.const (none : Option Y))))
    (stepCertificate h leaf)))

/-- A good state is at most `5 (H + 1) (F + 1)` long when the nodes, frames and values it holds
are at most `F` long. -/
theorem length_encState_le {Inv : Invariant X A Y} {H F : ℕ} {σ : State X A Y}
    (hσ : Good Inv H σ) (hnode : ∀ x, Inv.node x → (encX x).length ≤ F)
    (hframe : ∀ x a, Inv.frame x a → (encPair encX encA (x, a)).length ≤ F)
    (hvalue : ∀ y, Inv.value y → (encY y).length ≤ F) :
    (encState encX encA encY σ).length ≤ 5 * (H + 1) * (F + 1) := by
  obtain ⟨hlen, hfr, hreg⟩ := hσ
  have hstack : (encList (encPair encX encA) σ.1).length ≤ H * (2 * F + 1) := by
    rw [length_encList]
    calc (σ.1.map fun f => 2 * (encPair encX encA f).length + 1).sum
        ≤ (σ.1.map fun f => 2 * (encPair encX encA f).length + 1).length • (2 * F + 1) :=
          List.sum_le_length_nsmul _ _ fun n hn => by
            obtain ⟨⟨x, a⟩, hf, rfl⟩ := List.mem_map.mp hn
            have := hframe x a (hfr _ hf)
            omega
      _ ≤ H * (2 * F + 1) := by
          rw [List.length_map, smul_eq_mul]
          exact Nat.mul_le_mul_right _ hlen
  have hHF : H * (2 * F + 1) ≤ 2 * H * F + H := by rw [Nat.mul_add, Nat.mul_one]; ring_nf; omega
  rcases σ with ⟨st, r, v⟩
  rcases hreg with ⟨x, hr, hx⟩ | ⟨y, hr, hy⟩ <;> simp only [Prod.mk.injEq] at hr <;>
    obtain ⟨rfl, rfl⟩ := hr <;>
    simp only [length_encPair, encOption_some, encOption_none, List.length_cons,
      List.length_nil] at hstack ⊢
  · nlinarith [hnode x hx]
  · nlinarith [hvalue y hy]

private theorem pow_absorb (K₀ z : ℕ) (hz : 1 ≤ z) :
    K₀ * (5 * z + 1) ^ K₀ + 5 * z ≤ (K₀ * 6 ^ K₀ + K₀ + 6) * z ^ (K₀ * 6 ^ K₀ + K₀ + 6) := by
  set K := K₀ * 6 ^ K₀ + K₀ + 6
  have h6 : (5 * z + 1) ^ K₀ ≤ 6 ^ K₀ * z ^ K := by
    calc (5 * z + 1) ^ K₀ ≤ (6 * z) ^ K₀ := Nat.pow_le_pow_left (by omega) _
      _ = 6 ^ K₀ * z ^ K₀ := Nat.mul_pow _ _ _
      _ ≤ 6 ^ K₀ * z ^ K := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hz (by omega))
  have hz' : z ≤ z ^ K := Nat.le_self_pow (by omega) z
  calc K₀ * (5 * z + 1) ^ K₀ + 5 * z ≤ K₀ * (6 ^ K₀ * z ^ K) + 5 * z ^ K := by gcongr
    _ = (K₀ * 6 ^ K₀ + 5) * z ^ K := by ring
    _ ≤ K * z ^ K := Nat.mul_le_mul_right _ (by omega)

/-- **The resources of the native machine.** There is one constant `K` such that, for any fuel
and root certificates, if the root has a derivation with `N` nodes and at most `H` open calls
whose nodes, frames and values are at most `F` long, and whose leaves are evaluated by the leaf
certificate within time `TL` and space `SL`, then the time is at most the cost of the fuel and the
root plus `fuel + 1` times `K ((H + 1) (F + 1)) ^ K + TL` (and the cost of the binary clock), and
the workspace is at most the cost of the fuel and the root plus `K ((H + 1) (F + 1)) ^ K + SL`.
The bounds hold for any fuel; with `2 * N - 1 ≤ fuel` the result is the value
(`run_eq_some`). -/
theorem certificate_le (h : R.PolyTime encX encA encY)
    (leaf : NativeCertificate R.leaf encX encY) :
    ∃ K : ℕ, ∀ {I : Type} {encIn : I ↪ List Bool} {fuel : I → ℕ} {root : I → X}
      (cn : NativeCertificate fuel encIn encNat) (croot : NativeCertificate root encIn encX)
      (Inv : Invariant X A Y) (F TL SL : ℕ),
      (∀ x, Inv.node x → (encX x).length ≤ F ∧
        (R.isLeaf x = true → leaf.time x ≤ TL ∧ leaf.space x ≤ SL)) →
      (∀ x a, Inv.frame x a → (encPair encX encA (x, a)).length ≤ F) →
      (∀ y, Inv.value y → (encY y).length ≤ F) →
      ∀ (a : I) (y : Y) (N H : ℕ), R.Eval Inv (root a) y N H →
        (certificate h leaf cn croot).time a ≤ cn.time a + croot.time a + 2 * (encIn a).length +
            (fuel a + 1) * (K * ((H + 1) * (F + 1)) ^ K + TL +
              ((encNat (fuel a)).length + 1) ^ 2) ∧
          (certificate h leaf cn croot).space a ≤ cn.space a + croot.space a +
            2 * (encIn a).length + K * ((H + 1) * (F + 1)) ^ K + SL +
              (encNat (fuel a)).length := by
  obtain ⟨K₀, hK₀⟩ := exists_stepCertificate_le h leaf
  refine ⟨K₀ * 6 ^ K₀ + K₀ + 6, ?_⟩
  intro I encIn fuel root cn croot Inv F TL SL hnode hframe hvalue a y N H he
  set z := (H + 1) * (F + 1)
  have hz : 1 ≤ z := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have habsorb := pow_absorb K₀ z hz
  -- Every state of the run is good, hence short, and pays the leaf bound only at a leaf.
  have hgood := he.good_iterate
  have hlen (j : ℕ) : (encState encX encA encY (R.step^[j] ([], some (root a), none))).length ≤
      5 * z := by
    have := length_encState_le (hgood j) (fun x hx => (hnode x hx).1) hframe hvalue
    rwa [Nat.mul_assoc] at this
  clear_value z
  have hcost (cost : X → ℕ) (B : ℕ)
      (hB : ∀ x, Inv.node x → R.isLeaf x = true → cost x ≤ B) (j : ℕ) :
      R.leafCost cost (R.step^[j] ([], some (root a), none)) ≤ B := by
    obtain ⟨-, -, ⟨x, hr, hx⟩ | ⟨y', hr, -⟩⟩ := hgood j <;> simp only [leafCost, hr, Option.elim]
    · split_ifs with hl
      · exact hB x hx hl
      · exact Nat.zero_le _
    · exact Nat.zero_le _
  have hround (j : ℕ) :
      (stepCertificate h leaf).time (R.step^[j] ([], some (root a), none)) ≤
          K₀ * (5 * z + 1) ^ K₀ + TL ∧
        (stepCertificate h leaf).space (R.step^[j] ([], some (root a), none)) ≤
          K₀ * (5 * z + 1) ^ K₀ + SL := by
    obtain ⟨ht, hs⟩ := hK₀ (R.step^[j] ([], some (root a), none))
    have hp : K₀ * ((encState encX encA encY (R.step^[j] ([], some (root a), none))).length + 1) ^
        K₀ ≤ K₀ * (5 * z + 1) ^ K₀ :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by have := hlen j; omega) _)
    have hct := hcost leaf.time TL (fun x hx hl => ((hnode x hx).2 hl).1) j
    have hcs := hcost leaf.space SL (fun x hx hl => ((hnode x hx).2 hl).2) j
    constructor <;> omega
  have hmaxT := NativeCertificate.maxRoundTime_le (stepCertificate h leaf) (fuel a)
    ([], some (root a), none) (R := K₀ * (5 * z + 1) ^ K₀ + TL) fun j _ => (hround j).1
  have hmaxS := NativeCertificate.maxRoundSpace_le (stepCertificate h leaf) (fuel a)
    ([], some (root a), none) (Q := K₀ * (5 * z + 1) ^ K₀ + SL) fun j _ => (hround j).2
  have hmaxL := NativeCertificate.maxStateLength_le
    (encPair (encList (encPair encX encA)) (encPair (encOption encX) (encOption encY))) R.step
    (fuel a) ([], some (root a), none) (B := 5 * z) fun j _ => hlen j
  simp only [certificate, NativeCertificate.snd_time, NativeCertificate.snd_space,
    NativeCertificate.iterate_time, NativeCertificate.iterate_space,
    NativeCertificate.prod_time, NativeCertificate.prod_space, NativeCertificate.const_time,
    NativeCertificate.const_space, NativeCertificate.some_time, NativeCertificate.some_space]
  constructor
  · have hstep : NativeCertificate.maxRoundTime (stepCertificate h leaf) (fuel a)
        ([], some (root a), none) +
        NativeCertificate.maxStateLength
          (encPair (encList (encPair encX encA)) (encPair (encOption encX) (encOption encY)))
          R.step (fuel a) ([], some (root a), none) + ((encNat (fuel a)).length + 1) ^ 2 ≤
        (K₀ * 6 ^ K₀ + K₀ + 6) * z ^ (K₀ * 6 ^ K₀ + K₀ + 6) + TL +
          ((encNat (fuel a)).length + 1) ^ 2 := by omega
    have := Nat.mul_le_mul_left (fuel a + 1) hstep
    omega
  · omega

end Certificate

end Cslib.Algorithms.StackRecursion.Scheme
