/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.RootPackingBalance.Initialize
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.SharedWordFork
import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.SkipFrame
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Envelope

/-!
# Initializing a quantified root request stored on a work tape

The root schedule may have been guessed by preceding stages. Its work word is rewound, copied
and framed together with the computed flags. The ambient read-only input and its left-blank
position survive, so tensor continuations can read the original source input directly.
-/

public section

namespace Turing.MultiTapeATM.RootPackingBalance.Initialize

open MultiTapeTM
open RootBalanceRequest (Public encPublic)

private theorem rewind_clock (c d : ℕ) : ∃ C E, ∀ p : Public,
    (encPublic p).length + c * (p.1.raw.length + shortSize p ^ d + 1) + 8 +
        (frame (encPublic p)).length ≤ C * (p.1.raw.length + shortSize p ^ E + 1) := by
  let small (p : Public) := 18 * (shortSize p + 2) + c * (shortSize p ^ d + 1) + 9
  have h : PolyBounded shortSize small := (((PolyBounded.const 18).mul
    (PolyBounded.self.add (.const 2))).add ((PolyBounded.const c).mul
      ((PolyBounded.self.pow d).add (.const 1)))).add (.const 9)
  obtain ⟨C, E, hc⟩ := h.exists_le_linear_add_pow (fun p => p.1.raw.length) (12 + c)
    (fun p => by simp [shortSize])
  refine ⟨C, E, fun p => le_trans ?_ (hc p)⟩
  have hp : (encPublic p).length ≤ 4 * p.1.raw.length + 6 * (shortSize p + 2) := by
    simp only [encPublic, length_encPair, RootPredecessorQuery.length_encInput,
      encNat_apply, Nat.size_eq_bits_len, shortSize, RootPredecessorQuery.shortSize]
    omega
  simp only [length_frame, small, Nat.add_mul, Nat.mul_add, Nat.mul_one]
  omega

/-- Run the flag initializer from a public word on a work tape, preserving the host input. -/
theorem exists_prepend_work {flags : Public → List Bool} {d : ℕ}
    (hd : ComputableInO (fun p : Public => (p, flags p)) encPublic RootBalanceRequest.encInput
      (fun p => p.1.raw.length + shortSize p ^ d) (fun p => p.1.raw.length + shortSize p ^ d))
    {K : ℕ} {L : Type} [Finite L] (tape : Fin K) (leaf : MultiTapeATM K Bool L) :
    ∃ (U : ℕ) (src : Fin U) (Q : Type) (_ : Finite Q) (atm : MultiTapeATM U Bool Q) (C E : ℕ),
      ∀ (host : List Bool) (p : Public) (t : ℕ),
        let w := encPublic p
        let pre := frame w
        let target := WordGameLeaf.config tape (some leaf.toPTM.initial) (pre ++ flags p) pre.length
          (TerminalLayout.blank K host)
        let start := SharedWordFork.start src atm host w w.length
        leaf.HaltsWithin t target →
          let time := C * (p.1.raw.length + shortSize p ^ E + 1) + t
          atm.HaltsWithin time start ∧
            (atm.AcceptsWithin time start ↔ leaf.AcceptsWithin t target) := by
  let emb : Fin K ↪ Fin (K + 1) := Fin.castSuccEmb
  let i := emb tape
  let j := Fin.last K
  have hij : i ≠ j := Fin.castSucc_ne_last _
  let skip := SkipFrame.machine i
  let child := leaf.extendTapes emb
  let stage := prependTM skip child
  have hnil := (ComputableInDegree.const (encIn := RootBalanceRequest.encInput)
    (encMid := encBits) ([] : List Bool)).inO_one.comp_linear hd
  obtain ⟨U, src, Q, hQ, atm, c, h⟩ := TerminalLayout.exists_load hd hnil i j hij stage
  obtain ⟨C, E, hc⟩ := rewind_clock c d
  refine ⟨U, src, Q, hQ, atm, C, E, ?_⟩
  intro host p t
  dsimp only
  intro hh
  let pre := frame (encPublic p)
  let word := pre ++ flags p
  let start := TwoWordInput.ready i j host word []
  let finish : Cfg (K + 1) Bool Unit host := {start with
    workTapePos := Function.update start.workTapePos i (pre.length : ℤ)}
  have hs : skip.runFrom (start.withState (some skip.q₀)) pre.length = finish.withState none :=
    SkipFrame.runFrom i (encPublic p) (flags p) start
      (by simp [start, TwoWordInput.ready, TwoWordInput.words, wordsCfg, word, pre]) rfl
  have hv : viewCfg emb (finish.withState (some child.toPTM.initial)) =
      WordGameLeaf.config tape (some leaf.toPTM.initial) word pre.length
        (TerminalLayout.blank K host) := by
    apply Cfg.ext <;> try rfl
    · funext l z
      by_cases hl : l = tape
      · subst l
        simp [finish, start, TwoWordInput.ready, TwoWordInput.words, wordsCfg, viewCfg,
          Cfg.withState, WordGameLeaf.config, i]
      · simp [finish, start, TwoWordInput.ready, TwoWordInput.words, wordsCfg, viewCfg,
          Cfg.withState, WordGameLeaf.config, i, hl, TerminalLayout.blank,
          tapesCfg]
    · funext l
      by_cases hl : l = tape <;>
        simp [finish, start, TwoWordInput.ready, wordsCfg, viewCfg, Cfg.withState,
          WordGameLeaf.config, i, hl, TerminalLayout.blank, tapesCfg]
  have ht : child.HaltsWithin t (finish.withState (some child.toPTM.initial)) :=
    (leaf.haltsWithin_extendTapes_iff emb t _).2 (hv ▸ hh)
  obtain ⟨hs', ha⟩ := prependTM_spec skip child start finish pre.length t hs ht
  obtain ⟨hh', hacc⟩ := h host p _ hs'
  have hb := Nat.add_le_add_right (hc p) t
  rw [Nat.add_assoc _ pre.length t] at hb
  have hac : child.AcceptsWithin t (finish.withState (some child.toPTM.initial)) ↔
      leaf.AcceptsWithin t (WordGameLeaf.config tape (some leaf.toPTM.initial)
        word pre.length (TerminalLayout.blank K host)) := by
    exact (leaf.acceptsWithin_extendTapes_iff emb t _).trans (by rw [hv])
  have hiff := hacc.trans (ha.trans hac)
  exact ⟨hh'.mono hb, ⟨fun hx => hiff.mp (hx.of_halted_stepCoins hh'),
    fun hx => (hiff.mpr hx).mono hb⟩⟩

end Turing.MultiTapeATM.RootPackingBalance.Initialize
