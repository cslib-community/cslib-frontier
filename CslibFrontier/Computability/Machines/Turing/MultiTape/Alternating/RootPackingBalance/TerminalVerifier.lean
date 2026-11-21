/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.RootPackingBalance.TerminalGraph
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.RootPackingBalance.TerminalClock
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.RootPackingBalance.Initialize

/-!
# A clocked alternating balance verifier from an ordinary external input

For a fixed source tape count, one finite machine checks a proposed seed against the actual
copied and subdivided root graph. Its input supplies the raw movement schedule, seed, label
length and public graph parameters. Every path pays a constant number of linear schedule scans
and polynomial time on the short metadata, including all moves and the native rank test.
-/

public section
namespace Turing.MultiTapeATM.RootPackingBalance

open MultiTapeTM MultiTapePTM Cslib QuantifiedWord
open RootBalanceRequest (Public encPublic)
open RootPredecessorGraph (edgeCount vertexCount)

private theorem exists_game (k : ℕ) :
    ∃ (U : ℕ) (src : Fin U) (Q : Type) (_ : Finite Q) (atm : MultiTapeATM U Bool Q) (C E : ℕ),
      ∀ (input : List Bool) (p : Public),
        let pre := frame (encPublic p)
        let flags := rankFlags (Nat.clog 2 p.2)
        let time := C * (p.1.raw.length + Initialize.shortSize p ^ E + 1) + 2 * flags.length + 1
        let start := WordGameLeaf.config src (some atm.toPTM.initial) (pre ++ flags) pre.length
          (TerminalLayout.blank U input)
        atm.HaltsWithin time start ∧ (atm.AcceptsWithin time start ↔
          plays (fun word => terminalValue k (p, word)) [] flags) := by
  obtain ⟨U, src, Q, hQ, leaf, c, d, A, D, h⟩ := exists_terminal k
  obtain ⟨C, E, hbound⟩ := terminal_clock c d A D
  refine ⟨U, src, _, inferInstance, machine leaf src, C, E, ?_⟩
  intro input p
  let pre := frame (encPublic p)
  let flags := rankFlags (Nat.clog 2 p.2)
  let value := fun word : List Bool => terminalValue k (p, word.drop pre.length)
  let t := C * (p.1.raw.length + Initialize.shortSize p ^ E + 1)
  have hh (suffix : List Bool) (hlen : suffix.length = flags.length) := hbound p suffix hlen
  obtain ⟨halt, acc⟩ := spec leaf src t (TerminalLayout.blank U input) value pre flags (by
    intro suffix hlen
    let x : RootBalanceRequest.Input := (p, suffix)
    obtain ⟨ht, ha⟩ := h input x
    have he : RootBalanceRequest.encInput x = pre ++ suffix := rfl
    have hb := hh suffix hlen
    have hv : value (pre ++ suffix) = terminalValue k x := by simp [value, x]
    dsimp only
    rw [hv, ← he]
    exact ⟨ht.mono hb, ⟨fun hacc => ha.mp (hacc.of_halted_stepCoins ht),
      fun hx => (ha.mpr hx).mono hb⟩⟩)
  dsimp only
  rw [QuantifiedWord.machine_initial]
  refine ⟨halt, acc.trans ?_⟩
  have hp := plays_append_prefix value pre [] flags
  simpa [value] using hp

private theorem join_clock (A d B e : ℕ) : ∃ C E, ∀ p : Public,
    A * (p.1.raw.length + Initialize.shortSize p ^ d + 1) +
        (B * (p.1.raw.length + Initialize.shortSize p ^ e + 1) +
          2 * (rankFlags (Nat.clog 2 p.2)).length + 1) ≤
      C * (p.1.raw.length + Initialize.shortSize p ^ E + 1) := by
  let E := max 1 (max d e)
  refine ⟨A + B + 7, E, fun p => ?_⟩
  let S := Initialize.shortSize p
  let R := p.1.raw.length
  let Z := R + S ^ E + 1
  have hS : 1 ≤ S := by simp [S, Initialize.shortSize]
  have hd := Nat.pow_le_pow_right hS ((Nat.le_max_left d e).trans (Nat.le_max_right 1 _))
  have he := Nat.pow_le_pow_right hS ((Nat.le_max_right d e).trans (Nat.le_max_right 1 _))
  have hz : S ≤ S ^ E := by simpa only [pow_one] using Nat.pow_le_pow_right hS (Nat.le_max_left 1 _)
  have hA := Nat.mul_le_mul_left A (show R + S ^ d + 1 ≤ Z from by dsimp [Z, E]; omega)
  have hB := Nat.mul_le_mul_left B (show R + S ^ e + 1 ≤ Z from by dsimp [Z, E]; omega)
  have hn : Nat.clog 2 p.2 ≤ p.2.size := Nat.clog_le_of_le_pow (Nat.lt_size_self _).le
  have hw : Nat.clog 2 (Nat.clog 2 p.2) ≤ Nat.clog 2 p.2 :=
    (Nat.clog_le_of_le_pow (Nat.lt_size_self _).le).trans (Nat.size_le_self _)
  have hsz : p.2.size ≤ S := by dsimp [S, Initialize.shortSize]; omega
  change A * (R + S ^ d + 1) + (B * (R + S ^ e + 1) + _ + 1) ≤ (A + B + 7) * Z
  rw [length_rankFlags, Nat.add_mul, Nat.add_mul]
  have : S ≤ Z := by dsimp [Z]; omega
  have : 0 < Z := Nat.zero_lt_succ _
  omega

/-- A finite alternating machine starts with blank work tapes on the encoded public request
and accepts exactly the balanced seeds of the represented root graph. The same clock bounds
all computation paths, including malformed guesses and padded challenges. -/
theorem exists_balance_verifier (k : ℕ) :
    ∃ (U : ℕ) (Q : Type) (_ : Finite Q) (atm : MultiTapeATM U Bool Q) (C E : ℕ),
      ∀ {q copies : ℕ} {S : Type} (M : MultiTapePTM k Bool S) (input : List Bool)
        (b σ : ℕ) (code : BlockLetter k S b → Fin copies → Bool) (a : ℕ)
        (seed : BalancedSchedules.SeededLabels.Seed (vertexCount k q copies) (6 * a)),
        let p := graphPublic k q copies σ a seed
        let start := atm.toPTM.toNTM.initCfg (encPublic p)
        let time := C * (p.1.raw.length + Initialize.shortSize p ^ E + 1)
        atm.HaltsWithin time start ∧ (atm.AcceptsWithin time start ↔
          PacketPacking.Seeded.Balanced (vertexCount k q copies) a
            (explicitVertexEquiv k q copies).toEmbedding
            (RootPredecessorGraph.rowOf M input b σ code) (RootPredecessorGraph.colOf k q copies)
            seed) := by
  obtain ⟨U, src, Q, hQ, game, B, e, hg⟩ := exists_game k
  obtain ⟨K, S', hS', atm, A, d, hi⟩ := Initialize.exists_prepend src game
  obtain ⟨C, E, hbound⟩ := join_clock A d B e
  refine ⟨K, S', hS', atm, C, E, ?_⟩
  intro q copies S M input b σ code a seed
  let p := graphPublic k q copies σ a seed
  obtain ⟨hh, ha⟩ := hg (encPublic p) p
  obtain ⟨hh', ha'⟩ := hi p _ hh
  have hiff := ha'.trans (ha.trans (plays_iff_balanced M input b σ code a seed))
  exact ⟨hh'.mono (hbound p), ⟨fun hacc => hiff.mp (hacc.of_halted_stepCoins hh'),
    fun hx => (hiff.mpr hx).mono (hbound p)⟩⟩

end Turing.MultiTapeATM.RootPackingBalance
