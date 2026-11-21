/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.RootSeedChoice.Clock
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.RootPackingBalance.Game

/-!
# Guessing and validating a common seed from an ordinary root request

One machine starts with blank work tapes. It selects four fixed-width coefficients and checks
their balance against the represented root graph. All edge and rank challenges share those four
digits. Its time bound charges the underlying schedule linearly.
-/

public section

namespace Turing.MultiTapeATM.RootSeedChoice

open Cslib MultiTapeTM MultiTapePTM QuantifiedWord RootPackingBalance
open RootBalanceRequest (Public encPublic)
open RootPredecessorGraph (vertexCount)

/-- Ordinary-input alternating machine for existence of a balanced root seed. All later
universal moves challenge the same previously selected seed. -/
theorem exists_verifier (k : ℕ) :
    ∃ (K : ℕ) (Q : Type) (_ : Finite Q) (atm : MultiTapeATM K Bool Q) (C E : ℕ),
      ∀ {q copies : ℕ} {S : Type} (M : MultiTapePTM k Bool S) (input : List Bool)
        (b σ : ℕ) (code : BlockLetter k S b → Fin copies → Bool) (a : ℕ),
        let U := vertexCount k q copies
        let p := graphPublic k q copies σ a (zeroSeed U a)
        let start := atm.toPTM.toNTM.initCfg (encPublic p)
        let time := C * (p.1.raw.length + Initialize.shortSize p ^ E + 1)
        atm.HaltsWithin time start ∧ (atm.AcceptsWithin time start ↔
          ∃ seed, PacketPacking.Seeded.Balanced U a (explicitVertexEquiv k q copies).toEmbedding
            (RootPredecessorGraph.rowOf M input b σ code) (RootPredecessorGraph.colOf k q copies)
            seed) := by
  obtain ⟨d, hd⟩ := RootSeedInstall.exists_prepare_inO
  obtain ⟨U, src, L, hL, leaf, c, A, D, hterm⟩ :=
    exists_terminal_of_prepare k RootSeedInstall.install hd
  obtain ⟨B, e, hb⟩ := terminal_clock c d A D
  have hg := Game.compile leaf src (fun x => terminalValue k (RootSeedInstall.install x)) flags
    (terminalTime c d A D) _ hterm hb
  obtain ⟨i, hi⟩ := exists_flags_inO
  obtain ⟨K, Q, hQ, atm, F, h⟩ :=
    Initialize.exists_prepend_of_flags hi src (machine leaf src)
  obtain ⟨C, E, hbound⟩ := game_clock F i B e
  refine ⟨K, Q, hQ, atm, C, E, ?_⟩
  intro q copies S M input b σ code a
  let p := graphPublic k q copies σ a (zeroSeed (vertexCount k q copies) a)
  obtain ⟨ht, ha⟩ := hg (encPublic p) p
  obtain ⟨hh, hhacc⟩ := h p _ ht
  have hiff := hhacc.trans (ha.trans (plays_iff_exists_balanced M input b σ code a))
  exact ⟨hh.mono (hbound p), ⟨fun acc => hiff.mp (acc.of_halted_stepCoins hh),
    fun hx => (hiff.mpr hx).mono (hbound p)⟩⟩

end Turing.MultiTapeATM.RootSeedChoice
