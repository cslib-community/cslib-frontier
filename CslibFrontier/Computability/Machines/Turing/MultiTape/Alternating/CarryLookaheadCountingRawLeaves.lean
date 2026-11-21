/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.CarryLookaheadCountingFromLeaves

/-!
# Counting with a recursive continuation on the six physical query fields

The carry-save traversal stores a path with its head at the right and its component selector
in finite control. Before handing over to an alternating raw leaf, the machine rewinds the
path and installs that selector on a fresh tape. The persistent predicate context is already
at its origin. It need not be copied during the handover.
-/

public section

namespace Turing.MultiTapeATM.CarryLookaheadCountingRawLeaves

open MultiTapeTM Cslib.CountingLeaf Cslib.Circuits.Boolean.CarryLookahead.Query

variable {k : ℕ} {S : Type} (next : Bool → MultiTapeATM (6 + (k + 2)) Bool S)

/-- Physical preparation followed by the alternating verifier selected by the claim. -/
noncomputable def machine (carry claim : Bool) :=
  prependTM (CarrySaveLeaf.machine k carry) ((next claim).extendTapes (CarrySaveLeaf.nativeTapes k))

/-- Both signs of an alternating leaf query are checked from its six original tapes. -/
def RawSpec (predicate : List Bool × ℕ → Bool) (input context count width : List Bool)
    (budget baseTime : ℕ) : Prop :=
  ∀ (path bits : List Bool) (carry claim : Bool), bits.length + path.length ≤ budget →
    let q := CarrySaveLeaf.query context count width path bits carry
    let cfg := (Native.initial k input q).withState (some (next claim).toPTM.initial)
    (next claim).HaltsWithin baseTime cfg ∧
      ((next claim).AcceptsWithin baseTime cfg ↔ runRaw predicate q = claim)

private theorem run_leaf (predicate : List Bool × ℕ → Bool) (input context count width : List Bool)
    (budget baseTime : ℕ) (h : RawSpec next predicate input context count width budget baseTime)
    (height bits path unary : List Bool) (frontier : ℤ) (status carry claim : Bool)
    (hb : height.length + bits.length + path.length ≤ budget) :
    let cfg := CarrySaveLeaf.initial k input context count width height bits path unary
      frontier status
    let start := cfg.withState (some (machine next carry claim).toPTM.initial)
    let time := budget + 3 + baseTime
    (machine next carry claim).HaltsWithin time start ∧
      ((machine next carry claim).AcceptsWithin time start ↔
        runRaw predicate (CarrySaveLeaf.query context count width path bits carry) = claim) := by
  let cfg := CarrySaveLeaf.initial k input context count width height bits path unary
    frontier status
  let mid := CarrySaveLeaf.prepared cfg carry
  let leaf := (next claim).extendTapes (CarrySaveLeaf.nativeTapes k)
  obtain ⟨hp, _⟩ := CarrySaveLeaf.runsBetween k input context count width height bits path
    unary frontier status carry
  have hv : viewCfg (CarrySaveLeaf.nativeTapes k) (mid.withState (some leaf.toPTM.toNTM.q₀)) =
      (Native.initial k input (CarrySaveLeaf.query context count width path bits carry)).withState
        (some (next claim).toPTM.initial) := by
    change (viewCfg (CarrySaveLeaf.nativeTapes k) mid).withState _ = _
    rw [show viewCfg (CarrySaveLeaf.nativeTapes k) mid = _ from CarrySaveLeaf.view_prepared k input
      context count width height bits path unary frontier status carry]
    rfl
  obtain ⟨hh, ha⟩ := h path bits carry claim (by omega)
  have hh' : leaf.HaltsWithin baseTime (mid.withState (some leaf.toPTM.toNTM.q₀)) := by
    rw [MultiTapeATM.haltsWithin_extendTapes_iff, hv]
    exact hh
  obtain ⟨ht, hs⟩ := prependTM_spec (CarrySaveLeaf.machine k carry) leaf cfg mid
    (path.length + 3) baseTime hp hh'
  have hle : path.length + 3 + baseTime ≤ budget + 3 + baseTime := by omega
  rw [MultiTapeATM.acceptsWithin_extendTapes_iff, hv] at hs
  refine ⟨ht.mono hle, ⟨fun hacc => ha.mp (hs.mp (hacc.of_halted_stepCoins ht)),
    fun hc => (hs.mpr (ha.mpr hc)).mono hle⟩⟩

/-- The counting evaluator descends to one supplied alternating continuation on each branch.
The preparation of its six fields and the traversal overhead are independent of the length of
the predicate context. The continuation's running time occurs once. -/
theorem exists_evaluator [Finite S] (predicate : List Bool × ℕ → Bool) :
    ∃ (scratch r t : ℕ) (Q : Type) (_ : Finite Q)
      (atm : MultiTapeATM (CarryLookaheadCountingPrepare.size scratch k r t) Bool Q) (A D : ℕ),
      ∀ (input context : List Bool) (n w : ℕ) (bit : Fin w) (claim : Bool) (baseTime : ℕ),
        let budget := CarrySaveCountingRoot.sizeBudget n w
        RawSpec next predicate input context (encNat n) (encNat w) budget baseTime →
        let a : CountingInput.Input := ⟨n, ⟨w, bit.val, claim⟩⟩
        let start := (CarryLookaheadCountingPrepare.initial scratch k r t input context a).withState
          (some atm.toPTM.initial)
        let time := A * (n.size + w.size + 1) ^ D + (budget + 3) + baseTime
        atm.HaltsWithin time start ∧ (atm.AcceptsWithin time start ↔
          (∑ j ∈ Finset.range n, (predicate (context, j)).toNat).testBit bit.val = claim) := by
  obtain ⟨s, r, t, Q, hQ, atm, A, D, h⟩ :=
    CarryLookaheadCountingFromLeaves.exists_evaluator predicate (machine next)
  refine ⟨s, r, t, Q, hQ, atm, A, D, ?_⟩
  intro input context n w bit claim baseTime budget hraw
  have run := run_leaf next predicate input context (encNat n) (encNat w) budget baseTime hraw
  have hrun := h input context n w bit claim (budget + 3 + baseTime)
    (fun height bits path unary frontier status carry claim _ hb =>
      (run height bits path unary frontier status carry claim hb).1)
    (fun height bits path unary frontier status carry claim _ hb _ => by
      have ha := (run height bits path unary frontier status carry claim hb).2
      rw [runRaw_eq_value] at ha
      change (_ ↔ Cslib.Circuits.Boolean.CarrySaveQuery.value
        (CarrySaveCounting.leaves predicate context (encNat n) (encNat w))
        ⟨path, 0, carry, ofBits bits⟩ = claim) at ha
      rwa [ofBits_eq_lsbValue bits] at ha)
  simpa only [Nat.add_assoc] using hrun

end Turing.MultiTapeATM.CarryLookaheadCountingRawLeaves
