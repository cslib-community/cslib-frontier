/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.RootSeedChoice.Verifier
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.RootSeedChoice.Tagged
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.SharedWordFork

/-!
# Checking balance and a contraction continuation on one seed

The root machine chooses one seed, plays the rank challenge, and takes a native universal step.
One child checks the rank terminal. The other gets the same seed, the requested output bit index,
and its claimed value. Loading this seeded public data costs linear raw length plus polynomial
short work. The continuation's clock contributes additively to the whole branch bound.
-/

public section

namespace Turing.MultiTapeATM.RootSeedChoice

open Cslib MultiTapeTM MultiTapePTM QuantifiedWord RootPackingBalance
open RootBalanceRequest (Public encPublic)
open RootPredecessorGraph (vertexCount)

/-- The contraction continuation receives the original public request with its seed installed.
Its selected tape head is at the origin, with the other work tapes blank. -/
@[expose] def continuationStart {K : ℕ} {R : Type} (i j : Fin K) (r : MultiTapeATM K Bool R)
    (input : List Bool) (p : Public) :=
  (TwoWordInput.ready i j input (encPublic p) []).withState (some r.toPTM.initial)

private theorem exists_continuation {K : ℕ} {R : Type} [Finite R] (i j : Fin K) (hij : i ≠ j)
    (right : MultiTapeATM K Bool R) :
    ∃ (J : ℕ) (src : Fin J) (Q : Type) (_ : Finite Q) (atm : MultiTapeATM J Bool Q) (F f : ℕ),
      ∀ (input : List Bool) (x : RootBalanceRequest.Input) (t : ℕ),
        let cfg := continuationStart i j right input (RootSeedInstall.install x).1
        let word := RootBalanceRequest.encInput x
        let start := SharedWordFork.start src atm input word word.length
        let time := terminalTime F f 0 0 x + t
        right.HaltsWithin t cfg → atm.HaltsWithin time start ∧
          (atm.AcceptsWithin time start ↔ right.AcceptsWithin t cfg) := by
  obtain ⟨f, hs⟩ := RootSeedInstall.exists_computableInO
  have hpub := (ComputableInDegree.fst encPublic encBits).inO_one.comp_linear hs
  have hnil := (ComputableInDegree.const (encIn := RootBalanceRequest.encInput)
    (encMid := encBits) ([] : List Bool)).inO_one.comp_linear hs
  obtain ⟨J, src, Q, hQ, atm, F, h⟩ := TerminalLayout.exists_load hpub hnil i j hij right
  refine ⟨J, src, Q, hQ, atm, F, f, ?_⟩
  intro input x t
  simpa only [terminalTime, zero_mul, Nat.add_zero, SharedWordFork.start, continuationStart,
    Function.comp_apply, encBits_apply] using h input x t

/-- From the prepared choice tape, the fork preserves an arbitrary ambient read-only input.
The contraction machine can therefore query the original source input's tensor entries. -/
theorem exists_coupled_game (k : ℕ) {K : ℕ} {R : Type} [Finite R]
    (i j : Fin K) (hij : i ≠ j) (right : MultiTapeATM K Bool R) :
    ∃ (W : ℕ) (src : Fin W) (Q : Type) (_ : Finite Q) (atm : MultiTapeATM W Bool Q) (C D : ℕ),
      ∀ {q copies : ℕ} {S : Type} (M : MultiTapePTM k Bool S) (input host : List Bool)
        (b σ : ℕ) (code : BlockLetter k S b → Fin copies → Bool) (a bit : ℕ) (claim : Bool)
        (t : ℕ) (post : Public → Prop),
        let U := vertexCount k q copies
        let p := queryPublic k q copies σ a (zeroSeed U a) bit claim
        let pre := frame (encPublic p)
        (∀ seed, let seeded := queryPublic k q copies σ a seed bit claim
          let cfg := continuationStart i j right host seeded
          right.HaltsWithin t cfg ∧ (right.AcceptsWithin t cfg ↔ post seeded)) →
        let cfg := WordGameLeaf.config src (some atm.toPTM.initial) (pre ++ flags p) pre.length
          (TerminalLayout.blank W host)
        let time := C * (p.1.raw.length + Initialize.shortSize p ^ D + 1) + t
        atm.HaltsWithin time cfg ∧ (atm.AcceptsWithin time cfg ↔
          ∃ seed, PacketPacking.Seeded.Balanced U a (explicitVertexEquiv k q copies).toEmbedding
            (RootPredecessorGraph.rowOf M input b σ code) (RootPredecessorGraph.colOf k q copies)
            seed ∧ post (queryPublic k q copies σ a seed bit claim)) := by
  obtain ⟨d, hd⟩ := RootSeedInstall.exists_prepare_inO
  obtain ⟨I, isrc, L, hL, left, c, A, g, hleft⟩ :=
    exists_terminal_of_prepare k RootSeedInstall.install hd
  obtain ⟨J, jsrc, S', hS', cont, F, f, hcont⟩ := exists_continuation i j hij right
  obtain ⟨H, src, T, hT, fork, hfork⟩ := SharedWordFork.exists_both isrc left jsrc cont
  obtain ⟨l, e, hl⟩ := terminal_clock c d A g
  obtain ⟨r, v, hr⟩ := terminal_clock F f 0 0
  obtain ⟨B, g', hwork⟩ := game_clock l e r v
  refine ⟨H, src, _, inferInstance, machine fork src, B + 1, g', ?_⟩
  intro q copies S M input host b σ code a bit claim t post
  dsimp only
  intro hright
  let p := queryPublic k q copies σ a (zeroSeed _ _) bit claim
  let pre := frame (encPublic p)
  let val (x : RootBalanceRequest.Input) := terminalValue k (RootSeedInstall.install x) ∧
    post (RootSeedInstall.install x).1
  let part (m exp : ℕ) := m * (p.1.raw.length + Initialize.shortSize p ^ exp + 1)
  let τ := part l e + part r v + t
  have hgame := spec fork src (τ + 1) (TerminalLayout.blank H host)
    (fun word => val (p, word.drop pre.length)) pre (flags p) (by
      intro choices hlen
      let x : RootBalanceRequest.Input := (p, choices)
      let w := RootBalanceRequest.encInput x
      have he : w = pre ++ choices := rfl
      obtain ⟨s, hs⟩ := exists_installed_query k q copies σ a bit claim choices
      change (RootSeedInstall.install x).1 = _ at hs
      obtain ⟨hh, ha⟩ := hright s
      rw [← hs] at hh ha
      obtain ⟨hh₁, ha₁⟩ := hleft host x
      obtain ⟨hh₂, ha₂⟩ := hcont host x t hh
      have h₁ : terminalTime c d A g x ≤ τ := by
        have hx := hl p choices hlen
        change terminalTime c d A g x ≤ part l e at hx
        dsimp only [τ]
        omega
      have h₂ : terminalTime F f 0 0 x + t ≤ τ := by
        have hx := hr p choices hlen
        change terminalTime F f 0 0 x ≤ part r v at hx
        dsimp only [τ]
        omega
      obtain ⟨halt, acc⟩ := hfork host w w.length τ (hh₁.mono h₁) (hh₂.mono h₂)
      dsimp only
      rw [List.drop_left, ← he]
      refine ⟨halt, acc.trans (and_congr ?_ ?_)⟩
      · exact ⟨fun h => ha₁.mp (h.of_halted_stepCoins hh₁), fun z => (ha₁.mpr z).mono h₁⟩
      · exact ⟨fun h => ha.mp (ha₂.mp (h.of_halted_stepCoins hh₂)),
          fun z => (ha₂.mpr (ha.mpr z)).mono h₂⟩)
  obtain ⟨hh, ha⟩ := hgame
  rw [← machine_initial fork src] at hh ha
  have hplay := plays_append_prefix (fun word => val (p, word.drop pre.length)) pre [] (flags p)
  simp only [List.append_nil, List.drop_left] at hplay
  have hiff := ha.trans (hplay.trans (plays_iff_balanced_and M input b σ code a bit claim post))
  have hu := hwork p
  have hclock : τ + 1 + 2 * (flags p).length + 1 ≤ part (B + 1) g' + t := by
    change part l e + (part r v + 2 * (flags p).length + 1) ≤ part B g' at hu
    dsimp only [τ, part] at hu ⊢
    rw [Nat.add_mul, one_mul]
    omega
  exact ⟨hh.mono hclock, ⟨fun acc => hiff.mp (acc.of_halted_stepCoins hh),
    fun z => (hiff.mpr z).mono hclock⟩⟩

/-- A root seed is accepted exactly when it is balanced and the supplied contraction machine
certifies the same bit claim on that same seed. The single resulting machine handles both claims. -/
theorem exists_coupled (k : ℕ) {K : ℕ} {R : Type} [Finite R]
    (i j : Fin K) (hij : i ≠ j) (right : MultiTapeATM K Bool R) :
    ∃ (W : ℕ) (Q : Type) (_ : Finite Q) (atm : MultiTapeATM W Bool Q) (C D : ℕ),
      ∀ {q copies : ℕ} {S : Type} (M : MultiTapePTM k Bool S) (input : List Bool)
        (b σ : ℕ) (code : BlockLetter k S b → Fin copies → Bool) (a bit : ℕ) (claim : Bool)
        (t : ℕ) (post : Public → Prop),
        let U := vertexCount k q copies
        let p := queryPublic k q copies σ a (zeroSeed U a) bit claim
        let raw := encPublic p
        (∀ seed, let seeded := queryPublic k q copies σ a seed bit claim
          let cfg := continuationStart i j right raw seeded
          right.HaltsWithin t cfg ∧ (right.AcceptsWithin t cfg ↔ post seeded)) →
        let cfg := atm.toPTM.toNTM.initCfg raw
        let time := C * (p.1.raw.length + Initialize.shortSize p ^ D + 1) + t
        atm.HaltsWithin time cfg ∧ (atm.AcceptsWithin time cfg ↔
          ∃ seed, PacketPacking.Seeded.Balanced U a (explicitVertexEquiv k q copies).toEmbedding
            (RootPredecessorGraph.rowOf M input b σ code) (RootPredecessorGraph.colOf k q copies)
            seed ∧ post (queryPublic k q copies σ a seed bit claim)) := by
  obtain ⟨H, src, T, hT, game, B, g, hg⟩ := exists_coupled_game k i j hij right
  obtain ⟨d₀, hi⟩ := exists_flags_inO
  obtain ⟨W, Q, hQ, atm, F, hinit⟩ := Initialize.exists_prepend_of_flags hi src game
  obtain ⟨C, D, hbound⟩ := game_clock F d₀ B g
  refine ⟨W, Q, hQ, atm, C, D, ?_⟩
  intro q copies S M input b σ code a bit claim t post
  dsimp only
  intro hright
  let p := queryPublic k q copies σ a (zeroSeed _ _) bit claim
  obtain ⟨hh, ha⟩ := hg M input (encPublic p) b σ code a bit claim t post hright
  obtain ⟨hh', ha'⟩ := hinit p _ hh
  have hv := hbound p
  have hclock : F * (p.1.raw.length + Initialize.shortSize p ^ d₀ + 1) +
      (B * (p.1.raw.length + Initialize.shortSize p ^ g + 1) + t) ≤
      C * (p.1.raw.length + Initialize.shortSize p ^ D + 1) + t := by omega
  exact ⟨hh'.mono hclock, ⟨fun acc => ha.mp (ha'.mp (acc.of_halted_stepCoins hh')),
    fun z => (ha'.mpr (ha.mpr z)).mono hclock⟩⟩

end Turing.MultiTapeATM.RootSeedChoice
