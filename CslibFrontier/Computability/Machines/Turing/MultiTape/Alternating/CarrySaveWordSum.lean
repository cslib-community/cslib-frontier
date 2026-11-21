/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.CarryLookaheadCounting

/-!
# A native outer sum with word-valued leaves

The binary path is delivered by the physical carry-save traversal. The machine can use an
alternating continuation to answer operand bits. Its root storage contains the depth in unary
and binary, the precision, and the claim. Each branch calls one leaf and pays its clock once.
-/

public section

namespace Turing.MultiTapeATM.CarrySaveWordSum

open MultiTapeTM Cslib.BitString Cslib.Circuits.Boolean CarrySaveQuery

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
      encNat_apply, lsbValue_bits, value, bit.isLt, ↓reduceDIte] using hab
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

end Turing.MultiTapeATM.CarrySaveWordSum
