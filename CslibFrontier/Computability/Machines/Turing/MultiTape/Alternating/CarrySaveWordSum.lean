/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import
  CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.CarryLookaheadCountingPrepare
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.SharedWordFork
import
 CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.TwoWordLoad
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Envelope
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Quantitative

/-!
# A native outer sum with word-valued leaves

The binary path is delivered by the physical carry-save traversal. The machine can use an
alternating continuation to answer operand bits. Its root storage contains the depth in unary
and binary, the precision, and the claim. Each branch calls at most one leaf and pays its clock
at most once.

`exists_evaluator` starts with one encoded request containing only the context, binary height,
precision, queried bit and claim. It prepares the count word and unary frontier natively, then
runs the existing finisher. Context length and runtime height contribute linearly; the remaining
preparation and routing cost is polynomial in the short binary parameter word. The fixed leaf
machine and its supplied clock remain explicit, and the leaf clock is added with coefficient one.
-/

public section

namespace Turing.MultiTapeATM.CarrySaveWordSum

open MultiTapeTM Cslib.BitString Cslib.Circuits.Boolean CarrySaveQuery CarryLookahead.Query

/-- The raw word-sum request, with no precomputed count, unary frontier or routing fields. -/
structure Request where
  /-- Opaque data retained for the fixed leaf machine. -/
  context : List Bool
  /-- The binary height of the complete carry-save tree. -/
  height : ℕ
  /-- Binary precision, queried bit, and the claimed output. -/
  query : Initial.Input
  deriving DecidableEq

/-- A framed context, a framed binary height, and the complete encoded bit query. -/
enc_structure encRequest : Request where
  context : encBits, height : encNat, query : Initial.encInput

private def parameters (a : Request) : CountingInput.Input := ⟨a.height, a.query⟩

private theorem parameters_deg : ComputableInDegree parameters encRequest CountingInput.encInput
    1 1 :=
  CountingInput.encInput_mk_deg.comp (encRequest_height_deg.prod encRequest_query_deg)

private theorem length_encRequest (a : Request) :
    (encRequest a).length = 2 * a.context.length +
      (CountingInput.encInput (parameters a)).length + 1 := by
  simp only [encRequest_apply, encRequestFields, CountingInput.encInput_apply,
    CountingInput.encInputFields, length_encPair, encBits_apply, parameters]
  omega

private theorem component_spec {k w : ℕ} {S : Type}
    (leaf : Bool → Bool → MultiTapeATM (k + 12) Bool S)
    (leaves : List Bool → Cslib.BitString (w + w)) (input context : List Bool) (n time : ℕ)
    (ht : CarrySaveStream.LeafBound leaf time (CarrySaveCountingRoot.sizeBudget n w) input
      (CarrySaveLeaf.scratch k context (encNat n) (encNat w)))
    (ha : CarrySaveStream.LeafCorrect leaves leaf time (CarrySaveCountingRoot.sizeBudget n w)
      input (CarrySaveLeaf.scratch k context (encNat n) (encNat w)))
    (bit : Fin w) (carry claim : Bool) :
    let atm := CarrySaveStream.machine leaf carry claim
    let cfg := (CarrySaveCountingRoot.initial k input context n w bit.val).withState
      (some atm.toPTM.initial)
    let totalTime := CarrySaveCountingRoot.clockOfLeaf time n w
    atm.HaltsWithin totalTime cfg ∧ (atm.AcceptsWithin totalTime cfg ↔
      component (tree leaves (Nat.clog 2 n) []) carry bit = claim) := by
  let L := Nat.clog 2 n
  let atm := CarrySaveStream.machine leaf carry claim
  let cfg := (CarrySaveCountingRoot.initial k input context n w bit.val).withState
    (some atm.toPTM.initial)
  let localTime := CarrySaveStream.budget time L (encNat L) (encNat bit.val)
  have hinit : (CarrySaveStream.machine leaf carry claim).toPTM.initial =
      CarrySaveStream.State.header carry claim := CarrySaveStream.machine_q₀ ..
  have hh : atm.HaltsWithin localTime cfg := by
    simpa only [cfg, atm, localTime, L, CarrySaveCountingRoot.initial, CarrySaveLeaf.initial,
      hinit]
      using CarrySaveStream.haltsWithin_budget leaf time _ ht L (encNat L) (encNat bit.val) []
        (encUnary L) 0 false carry claim (CarrySaveCountingRoot.initial_frontier n)
        (CarrySaveCountingRoot.initial_size_le n w bit)
  have hab := CarrySaveStream.acceptsWithin_budget leaves leaf time _ ht ha L
    (encNat L) (encNat bit.val) [] (encUnary L) 0 false carry claim
    (CarrySaveCountingRoot.initial_frontier n) (CarrySaveCountingRoot.initial_size_le n w bit)
    (lsbValue_bits _) (by simpa only [encNat_apply, lsbValue_bits] using bit.isLt)
  have hl : atm.AcceptsWithin localTime cfg ↔
      component (tree leaves L []) carry bit = claim := by
    simpa only [cfg, atm, localTime, L, CarrySaveCountingRoot.initial, CarrySaveLeaf.initial,
      hinit,
      encNat_apply, lsbValue_bits, CarrySaveQuery.value, bit.isLt, ↓reduceDIte] using hab
  have hb := CarrySaveCountingRoot.budget_le_clockOfLeaf time n w bit
  exact ⟨hh.mono hb,
    ⟨fun h => hl.mp (h.of_halted_stepCoins hh), fun h => (hl.mpr h).mono hb⟩⟩

/-- A single finite machine finishes arbitrary word-valued leaves on prepared tapes. At depth
`L`, its carry-save clock is linear in `L`, plus binary counter sizes and one leaf time. The
finishing adder adds a polynomial in the binary size of the precision. -/
theorem exists_finisher {k : ℕ} {S : Type} [Finite S]
    (leaf : Bool → Bool → MultiTapeATM (k + 12) Bool S) :
    ∃ (r q : ℕ) (Q : Type) (_ : Finite Q)
      (atm : MultiTapeATM (CarryLookaheadCountingLayout.size k r q) Bool Q) (c d : ℕ),
      ∀ (input context : List Bool) (L w time : ℕ)
        (leaves : List Bool → Cslib.BitString (w + w)),
        let n := 2 ^ L
        let budget := CarrySaveCountingRoot.sizeBudget n w
        let scratch := CarrySaveLeaf.scratch k context (encNat n) (encNat w)
        CarrySaveStream.LeafBound leaf time budget input scratch →
        CarrySaveStream.LeafCorrect leaves leaf time budget input scratch →
        ∀ (bit : Fin w) (claim : Bool),
          let cfg := CarryLookaheadCounting.initial k r q input context n w bit.val claim
          let start := cfg.withState (some atm.toPTM.initial)
          let clock := CarryLookaheadCounting.clockOfRoot c d w
            (40 * L + 2 * L.size + 2 * w.size + time + 1)
          atm.HaltsWithin clock start ∧ (atm.AcceptsWithin clock start ↔
            (carryLookaheadAdd w).eval interpretation (tree leaves L []) bit = claim) := by
  let := Fintype.ofFinite S
  obtain ⟨r, SR, hSR, terminal, cP, dP, hterm⟩ :=
    CountingTerminal.exists_terminal_for_pair (CarrySaveStream.machine leaf)
  let := hSR
  obtain ⟨q, Q, hQ, atm, c, d, h⟩ :=
    CarryLookaheadCounting.exists_finisher_for_pair terminal cP dP
  refine ⟨r, q, Q, hQ, atm, c, d, ?_⟩
  intro input context L w time leaves n budget scratch ht ha bit claim
  have hc := Nat.clog_pow 2 L one_lt_two
  have root := hterm input context n w (CarrySaveCountingRoot.clockOfLeaf time n w)
    (tree leaves (Nat.clog 2 n) []) (component_spec leaf leaves input context n time ht ha)
  have finish := h input context n w (CarrySaveCountingRoot.clockOfLeaf time n w)
    (tree leaves (Nat.clog 2 n) []) root bit claim
  simpa only [n, CarrySaveCountingRoot.clockOfLeaf, hc] using finish

private theorem clock_bound (A ci di c d : ℕ) :
    ∃ C D, ∀ a : Request,
      A * ((encRequest a).length + 1) + 8 +
        ci * (a.height + ((CountingInput.encInput (parameters a)).length + 1) ^ di + 1) +
        CarryLookaheadCounting.clockOfRoot c d a.query.width
          (40 * a.height + 2 * a.height.size + 2 * a.query.width.size + 1) ≤
        C * (a.context.length + a.height +
          ((CountingInput.encInput (parameters a)).length + 1) ^ D + 1) := by
  let size := fun a : Request => (CountingInput.encInput (parameters a)).length + 1
  have hh : PolyBounded size (fun a : Request => a.height.size) := PolyBounded.self.mono
    (fun a => by simp only [size, CountingInput.length_encInput, parameters]; omega)
  have hw : PolyBounded size (fun a : Request => a.query.width.size) := PolyBounded.self.mono
    (fun a => by simp only [size, CountingInput.length_encInput, parameters]; omega)
  have hr : PolyBounded size (fun a : Request => Nat.clog 2 (a.query.width + 1)) :=
    hw.mono fun a => Nat.clog_le_of_le_pow (by
      have := Nat.lt_size_self a.query.width
      omega)
  have hm := (((PolyBounded.const 4).mul hw).add ((PolyBounded.const 6).mul hr)).add
    (PolyBounded.const 27)
  have ho := (PolyBounded.const c).mul (hm.pow d)
  have hf : PolyBounded size (fun a : Request => CarryLookaheadCounting.clockOfRoot c d
      a.query.width (2 * a.height.size + 2 * a.query.width.size + 1)) := by
    simpa only [CarryLookaheadCounting.clockOfRoot, CarryLookaheadCounting.overhead,
      CarryLookaheadCounting.metadataBound, Nat.add_assoc] using
      (((((PolyBounded.const 2).mul hr).add (.const 6)).mul (ho.add (.const 2))).add ho).add
        (((((PolyBounded.const 2).mul hh).add ((PolyBounded.const 2).mul hw)).add
          (.const 1)).add (.const 1))
  let extra := fun a : Request => A * (size a + 1) + 8 + ci * (size a ^ di + 1) +
    CarryLookaheadCounting.clockOfRoot c d a.query.width
      (2 * a.height.size + 2 * a.query.width.size + 1)
  have he : PolyBounded size extra :=
    ((((PolyBounded.const A).mul (PolyBounded.self.add (.const 1))).add (.const 8)).add
      ((PolyBounded.const ci).mul ((PolyBounded.self.pow di).add (.const 1)))).add hf
  obtain ⟨C, D, hc⟩ := he.exists_le_linear_add_pow
    (fun a => a.context.length + a.height) (2 * A + ci + 40)
    (fun a => by dsimp only [size]; omega)
  refine ⟨C, D, fun a => ?_⟩
  have h := hc a
  rw [length_encRequest]
  dsimp only [size, extra] at h ⊢
  simp only [CarryLookaheadCounting.clockOfRoot] at h ⊢
  nlinarith

/-- Compile one fixed finite leaf machine into a sum-bit machine starting from a single raw
request. Native loading and depth preparation charge context length and height linearly, with
polynomial overhead only in the complete short parameter word. Each branch adds one leaf clock. -/
theorem exists_evaluator {k : ℕ} {S : Type} [Finite S]
    (leaf : Bool → Bool → MultiTapeATM (k + 12) Bool S) :
    ∃ (K : ℕ) (source : Fin K) (Q : Type) (_ : Finite Q)
      (atm : MultiTapeATM K Bool Q) (C D : ℕ),
      ∀ (input context : List Bool) (L w leafTime : ℕ)
        (leaves : List Bool → Cslib.BitString (w + w)),
        let n := 2 ^ L
        let budget := CarrySaveCountingRoot.sizeBudget n w
        let scratch := CarrySaveLeaf.scratch k context (encNat n) (encNat w)
        CarrySaveStream.LeafBound leaf leafTime budget input scratch →
        CarrySaveStream.LeafCorrect leaves leaf leafTime budget input scratch →
        ∀ (bit : Fin w) (claim : Bool),
          let request : Request := ⟨context, L, ⟨w, bit.val, claim⟩⟩
          let start := SharedWordFork.start source atm input (encRequest request) 0
          let time := C * (context.length + L +
            ((CountingInput.encInput ⟨L, request.query⟩).length + 1) ^ D + 1) + leafTime
          atm.HaltsWithin time start ∧ (atm.AcceptsWithin time start ↔
            (carryLookaheadAdd w).eval interpretation (tree leaves L []) bit = claim) := by
  obtain ⟨r, q, SF, hSF, finish, c, d, hfinish⟩ := exists_finisher leaf
  let : Finite SF := hSF
  obtain ⟨scratch, SP, hSP, prepare, ci, di, hprepare⟩ :=
    CarryLookaheadCountingPrepare.exists_prepare_height k r q
  let : Finite SP := hSP
  let e := CarryLookaheadCountingPrepare.evaluatorTapes scratch k r q
  let continuation := finish.extendTapes e
  let prepared := prependTM prepare continuation
  obtain ⟨K, source, Q, hQ, atm, A, hload⟩ :=
    TwoWordLoad.exists_load_from encRequest_context_deg.inO_one
      parameters_deg.inO_one _ _
      (CarryLookaheadCountingPrepare.context_ne_request scratch k r q) prepared
  obtain ⟨C, D, hclock⟩ := clock_bound A ci di c d
  refine ⟨K, source, Q, hQ, atm, C, D, ?_⟩
  intro input context L w leafTime leaves n budget leafScratch ht ha bit claim request start time
  let a : CountingInput.Input := ⟨L, request.query⟩
  let rootTime := 40 * L + 2 * L.size + 2 * w.size + leafTime + 1
  let finishTime := CarryLookaheadCounting.clockOfRoot c d w rootTime
  let prepTime := ci * (L + ((CountingInput.encInput a).length + 1) ^ di + 1)
  let storage := CarryLookaheadCountingPrepare.initial scratch k r q input context a
  let completed := CarryLookaheadCountingPrepare.config scratch k r q input context a
    (CarryLookaheadCountingInitialLayout.canonical ⟨2 ^ L, a.query⟩)
  have hview : viewCfg e completed =
      CarryLookaheadCounting.initial k r q input context n w bit.val claim := by
    rw [CarryLookaheadCountingPrepare.view_prepared_of_retained]
  have hf := hfinish input context L w leafTime leaves ht ha bit claim
  have hh : continuation.HaltsWithin finishTime
      (completed.withState (some continuation.toPTM.initial)) := by
    rw [haltsWithin_extendTapes_iff]
    change finish.HaltsWithin finishTime
      ((viewCfg e completed).withState (some finish.toPTM.initial))
    rw [hview]
    exact hf.1
  have hp := prependTM_spec prepare continuation storage completed prepTime finishTime
    (hprepare input context a) hh
  have hpMeaning : prepared.AcceptsWithin (prepTime + finishTime)
      (storage.withState (some prepared.toPTM.initial)) ↔
        (carryLookaheadAdd w).eval interpretation (tree leaves L []) bit = claim := by
    refine hp.2.trans ?_
    rw [acceptsWithin_extendTapes_iff]
    change finish.AcceptsWithin finishTime
      ((viewCfg e completed).withState (some finish.toPTM.initial)) ↔ _
    rw [hview]
    exact hf.2
  obtain ⟨hl, hlMeaning⟩ := hload input request 0 (Nat.zero_le _)
    (prepTime + finishTime) (by
      rw [CarryLookaheadCountingPrepare.ready_eq_initial]
      exact hp.1)
  have hb : 0 + A * ((encRequest request).length + 1) + 8 +
      (prepTime + finishTime) ≤ time := by
    have h := hclock request
    dsimp only [parameters, request] at h
    dsimp only [prepTime, finishTime, rootTime, a, time, request]
    simp only [CarryLookaheadCounting.clockOfRoot] at h ⊢
    omega
  have hm : atm.AcceptsWithin
      (0 + A * ((encRequest request).length + 1) + 8 + (prepTime + finishTime)) start ↔
      (carryLookaheadAdd w).eval interpretation (tree leaves L []) bit = claim := by
    refine hlMeaning.trans ?_
    rw [CarryLookaheadCountingPrepare.ready_eq_initial]
    exact hpMeaning
  exact ⟨hl.mono hb, ⟨fun h => hm.mp (h.of_halted_stepCoins hl),
    fun h => (hm.mpr h).mono hb⟩⟩

end Turing.MultiTapeATM.CarrySaveWordSum
