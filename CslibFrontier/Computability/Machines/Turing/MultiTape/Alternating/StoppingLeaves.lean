/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.StoppingProduct
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.StoppingLeafRequest
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.GuardedLeaf
public import
  CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.FastContraction.StoppingQuery.WordSum

/-!
# Native product calls from the stopping sum

The physical carry-save leaf is serialized once. Its raw assignment path is retained while
short metadata prepares the product root. The concrete product compiler handles every local
gate and product level, and invokes the supplied entry terminal at most once per branch.

`exists_leaves` supplies both physical leaf contracts required by `CarrySaveWordSum`. The
long path and raw counters contribute linearly. The only remaining semantic premise is the
behavior of the supplied native terminal on entry and constant gates of the actual product.
-/

noncomputable section

public section

namespace Turing.MultiTapeATM.StoppingLeaves

open MultiTapeTM Cslib Cslib.BitString Cslib.Circuits.Boolean
open Cslib.Circuits.Frontier.FastContraction StoppingQuery.ProductRouting
open StoppingLeafRequest

private theorem input_length (x : Input) :
    (encInput x).length =
      2 * ((encContext x.context).length + x.count.length + x.width.length + x.path.length) +
        x.bit.length + 7 := by
  rw [encInput_eq, CountingLeaf.length_encRawInput]

private theorem setup_le (x : Input) (w A l load d D : ℕ) (hd : d ≤ D)
    (hw : w ≤ l * ((encInput x).length + ((encContext x.context).length + 1) ^ d + 1)) :
    x.path.length + 3 + (2 * (encInput x).length + 5) +
        (A * ((encInput x).length + ((encContext x.context).length + 1) ^ d + 1) +
          (2 * w + 16)) + (load * (w + 1) + 8) ≤
      (A + 2 * l + load * (l + 1) + 35) *
        ((encInput x).length + ((encContext x.context).length + 1) ^ D + 1) := by
  let N := (encInput x).length + ((encContext x.context).length + 1) ^ D + 1
  have hN : 1 ≤ N := Nat.succ_pos _
  have hp := Nat.pow_le_pow_right (Nat.succ_pos (encContext x.context).length) hd
  change ((encContext x.context).length + 1) ^ d ≤
    ((encContext x.context).length + 1) ^ D at hp
  have hm : (encInput x).length + ((encContext x.context).length + 1) ^ d + 1 ≤ N := by
    dsimp only [N]
    omega
  have hword : w ≤ l * N := hw.trans (Nat.mul_le_mul_left l hm)
  have hword' : w + 1 ≤ (l + 1) * N := by
    rw [Nat.add_mul, Nat.one_mul]
    omega
  have hl : (encInput x).length ≤ N := by dsimp [N]; omega
  have hpath : x.path.length ≤ N := by have := input_length x; omega
  have hA := Nat.mul_le_mul_left A hm
  have hload := Nat.mul_le_mul_left load hword'
  have hw₂ := Nat.mul_le_mul_left 2 hword
  have hl₂ := Nat.mul_le_mul_left 2 hl
  calc
    _ ≤ N + 3 + (2 * N + 5) + (A * N + (2 * (l * N) + 16)) +
        (load * ((l + 1) * N) + 8) := by omega
    _ = (A + 2 * l + load * (l + 1) + 3) * N + 32 := by ring
    _ ≤ (A + 2 * l + load * (l + 1) + 35) * N := by nlinarith

private theorem physical_size_le (context : Context) (count width path bits : List Bool)
    (carry : Bool) (B D : ℕ) (hD : 1 ≤ D) (hb : path.length + bits.length ≤ B) :
    let x : Input := ⟨context, count, width, path, carry, bits⟩
    (encInput x).length + ((encContext context).length + 1) ^ D + 1 ≤
      10 * (B + count.length + width.length + ((encContext context).length + 1) ^ D + 1) := by
  intro x
  have hp : (encContext context).length + 1 ≤ ((encContext context).length + 1) ^ D := by
    simpa only [pow_one] using
      Nat.pow_le_pow_right (Nat.succ_pos (encContext context).length) hD
  rw [input_length]
  dsimp only [x]
  omega

/-- Construct the actual word-valued product leaves of the stopping sum. All routing is native;
the supplied terminal answers product terminals satisfying the stated storage invariant.
Both leaf contracts use one clock, linear in the physical traversal budget and raw counters,
plus polynomial short-context preparation and one product/entry clock. -/
theorem exists_leaves {N : ℕ} {S : Type} [Finite S]
    (assignment query : Fin N) (hne : assignment ≠ query) (terminal : MultiTapeATM N Bool S) :
    ∃ (a : ℕ) (Q : Type) (_ : Finite Q)
      (leaf : Bool → Bool → MultiTapeATM (a + 12) Bool Q) (C D P E : ℕ),
      ∀ (input : List Bool) (ctx : Context) (count width : List Bool) (B terminalTime : ℕ)
        (entry : ℕ → ℕ → GaloisRingArith.Ring ctx.parameters.precision
          (modulus ctx.parameters.scale)),
        ctx.coefficient < (modulus ctx.parameters.scale).length →
        (∀ (path : List Bool), path.length ≤ B → ∀ p,
          Valid ctx.parameters (2 ^ Nat.clog 2 ctx.parameters.vertices)
            (Nat.clog 2 ctx.parameters.vertices) p → player p = none →
          let start := (TwoWordInput.ready assignment query input path (encPosition p)).withState
            (some terminal.toPTM.initial)
          terminal.HaltsWithin terminalTime start ∧
            (terminal.AcceptsWithin terminalTime start ↔
              StoppingQuery.value ctx.parameters.scale ctx.parameters.precision 0
                ctx.parameters.vertices (fun _ v => entry (binaryValue path) v)
                (address p) = p.claim)) →
        let time := C * (B + count.length + width.length +
          ((encContext ctx).length + 1) ^ D + 1) +
            StoppingProduct.clock P E ctx.parameters terminalTime
        let scratch := CarrySaveLeaf.scratch a (encContext ctx) count width
        CarrySaveStream.LeafBound leaf time B input scratch ∧
          CarrySaveStream.LeafCorrect
            (StoppingQuery.WordSum.leaves ctx.parameters.scale ctx.parameters.precision
              ctx.parameters.vertices entry ctx.coefficient) leaf time B input scratch := by
  classical
  obtain ⟨K, ass, src, QP, hQP, product, P, E, hne', hproduct⟩ :=
    StoppingProduct.exists_evaluator assignment query hne terminal
  let := hQP
  obtain ⟨U, selected, QL, hQL, loaded, load, hload⟩ :=
    TwoWordLoad.exists_load_from
      encPrepared_assignment_deg.inO_one encPrepared_position_deg.inO_one ass src hne' product
  let := hQL
  choose d hd using exists_instruction_inO
  choose l hl using fun b => (hd b).length_le_time
  let raw (x : Input) : CountingLeaf.RawInput :=
    ⟨encContext x.context, x.count, x.width, x.path, x.carry, x.bit⟩
  let cost (b : Bool) (x : Input) :=
    (encInput x).length + ((encContext x.context).length + 1) ^ d b
  obtain ⟨a, Q, hQ, leaf, A, hleaf⟩ := GuardedLeaf.exists_runner selected loaded raw
    (fun x => (encInput_eq x).symm) (fun _ => active) (fun b _ => !b)
    (fun b x => encPrepared (prepare b x)) cost hd
  let D := max 1 (max (d false) (d true))
  let coeff (b : Bool) := A b + 2 * l b + load * (l b + 1) + 35
  let C := max (coeff false) (coeff true)
  refine ⟨a, Q, hQ, leaf, C * 10, D, P, E, ?_⟩
  intro input ctx count width B terminalTime entry hcoefficient hterminal time scratch
  let productTime := StoppingProduct.clock P E ctx.parameters terminalTime
  have hphysical (height bits path unary : List Bool) (frontier : ℤ)
      (status carry claim : Bool) (hb : path.length + bits.length ≤ B) :
      let x : Input := ⟨ctx, count, width, path, carry, bits⟩
      let cfg := (CarrySaveLeaf.initial a input (encContext ctx) count width
        height bits path unary frontier status).withState (some (leaf carry claim).toPTM.initial)
      (leaf carry claim).HaltsWithin time cfg ∧ ((leaf carry claim).AcceptsWithin time cfg ↔
        if active x then
          ((representative ctx.parameters.scale ctx.parameters.precision
            (∏ v ∈ Finset.range ctx.parameters.vertices, entry (binaryValue path) v)).coeff
              ctx.coefficient).val.testBit (cappedBit x) = claim
        else (!claim) = true) := by
    intro x cfg
    let w := encPrepared (prepare claim x)
    let t := load * (w.length + 1) + 8 + productTime
    let target := SharedWordFork.start selected loaded input w 0
    have hchild (ha : active x = true) : loaded.HaltsWithin t target ∧
        (loaded.AcceptsWithin t target ↔
          ((representative ctx.parameters.scale ctx.parameters.precision
            (∏ v ∈ Finset.range ctx.parameters.vertices, entry (binaryValue path) v)).coeff
              ctx.coefficient).val.testBit (cappedBit x) = claim) := by
      have hbit : cappedBit x < ctx.parameters.precision := by
        have h := ha
        simp only [StoppingLeafRequest.active, Bool.and_eq_true, decide_eq_true_eq] at h
        exact h.2
      have hp := hproduct input path ctx.parameters (fun _ v => entry (binaryValue path) v)
        terminalTime (hterminal path (by omega)) ⟨ctx.coefficient, hcoefficient⟩
          ⟨cappedBit x, hbit⟩ claim
      have hh := hload input (prepare claim x) 0 (Nat.zero_le _) productTime hp.1
      simpa only [t, target, w, SharedWordFork.start, Nat.zero_add] using
        And.intro hh.1 (hh.2.trans hp.2)
    have hs := hleaf input x height unary frontier status claim t (fun ha => (hchild ha).1)
    have hlen := hl claim x
    simp only [encBits_apply, instruction, List.length_append] at hlen
    have hw : w.length ≤ l claim * ((encInput x).length +
        ((encContext x.context).length + 1) ^ d claim + 1) := by
      change 3 + w.length ≤ _ at hlen
      omega
    have hD : d claim ≤ D := by
      refine le_trans ?_ (Nat.le_max_right 1 _)
      cases claim <;> first | exact Nat.le_max_left .. | exact Nat.le_max_right ..
    have hC : coeff claim ≤ C := by
      cases claim <;> first | exact Nat.le_max_left .. | exact Nat.le_max_right ..
    have hsetup := setup_le x w.length (A claim) (l claim) load (d claim) D hD hw
    have hsize := physical_size_le ctx count width path bits carry B D (Nat.le_max_left ..) hb
    have hbound := Nat.mul_le_mul hC hsize
    have hclock : x.path.length + 3 + (2 * (encInput x).length + 5) +
        (A claim * (cost claim x + 1) + (2 * w.length + 16)) + t ≤ time := by
      dsimp only [time, cost, t, productTime, coeff, x] at *
      rw [← Nat.mul_assoc] at hbound
      omega
    have hacc : (leaf carry claim).AcceptsWithin time cfg ↔
        if active x then loaded.AcceptsWithin t target else (!claim) = true :=
      ⟨fun h => hs.2.mp (h.of_halted_stepCoins hs.1), fun h => (hs.2.mpr h).mono hclock⟩
    refine ⟨hs.1.mono hclock, hacc.trans ?_⟩
    cases ha : active x with
    | false => simp only [Bool.false_eq_true, ↓reduceIte]
    | true => simpa only [ha, ↓reduceIte] using (hchild ha).2
  constructor
  · intro height bits path unary frontier status carry claim _ hb
    exact (hphysical height bits path unary frontier status carry claim (by omega)).1
  · intro height bits path unary frontier status carry claim _ hb hbit
    have hs := (hphysical height bits path unary frontier status carry claim (by omega)).2
    let x : Input := ⟨ctx, count, width, path, carry, bits⟩
    have he := prepare_of_bit_lt claim x hbit
    have hi := cappedBit_eq x hbit
    rw [he.2, hi] at hs
    rw [CarrySaveQuery.value, dite_eq_left hbit, CarrySaveQuery.tree,
      StoppingQuery.WordSum.component_leaves]
    cases carry <;> cases claim <;>
      simpa only [x, CarrySaveLeaf.initial, scratch, Bool.not_false, Bool.not_true,
        Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte, MultiTapePTM.toNTM,
        MultiTapeMachine.toNTM, MultiTapePTM.branches] using hs

end Turing.MultiTapeATM.StoppingLeaves
