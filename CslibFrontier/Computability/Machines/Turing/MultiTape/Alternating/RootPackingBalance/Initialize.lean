/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.FramedPrefixInput
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.QuantifiedWord.Fields
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.RootPackingBalance.TerminalLayout
public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.RootBalanceRequest
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Envelope

/-!
# Initializing a root-seed balance check from its ordinary input

The public word contains the raw root schedule, its shared seed and a binary edge count. The
machine copies that word into a frame, computes the three blocks of quantifier flags from the
short count, and starts the game on its first flag. Its input head is on the left blank and
all continuation tapes except the designated flag tape are blank.
-/

public section

namespace Turing.MultiTapeATM.RootPackingBalance.Initialize

open MultiTapeTM
open RootBalanceRequest (Public encPublic)
open QuantifiedWord (rankFlags)

/-- The arithmetic parameters of the external public word, excluding the raw schedule. -/
@[expose] def shortSize (p : Public) : ℕ := RootPredecessorQuery.shortSize p.1 + p.2.size + 1

private theorem prepare_inO : ∃ d, ComputableInO
    (fun p : Public => (p, rankFlags (Nat.clog 2 p.2))) encPublic RootBalanceRequest.encInput
    (fun p => p.1.raw.length + shortSize p ^ d)
    (fun p => p.1.raw.length + shortSize p ^ d) := by
  obtain ⟨T, S, hT, hS, hflags⟩ :=
    QuantifiedWord.computableInPolyTime_rankFlags.exists_computableInO
  have hid : ComputableInDegree (fun p : Public => p) encPublic encPublic 1 1 := .id'
  have h := hid.inO_one.prod (hflags.comp (ComputableInDegree.snd
    RootPredecessorQuery.encInput encNat).inO_one)
  have hn : PolyBounded shortSize (fun p : Public => (encNat p.2).length) :=
    PolyBounded.self.mono fun p => by
      simp only [shortSize, encNat_apply, Nat.size_eq_bits_len]
      omega
  let u (p : Public) := 12 * (shortSize p + 2) + T p.2 + S p.2
  have hu : PolyBounded shortSize u :=
    ((((PolyBounded.const 12).mul (PolyBounded.self.add (.const 2))).add
      (hT.comp (g := Prod.snd) hn)).add (hS.comp (g := Prod.snd) hn))
  obtain ⟨c, d, hc⟩ := hu.exists_le_linear_add_pow (fun p => p.1.raw.length) 8
    (fun p => by simp [shortSize])
  have he (p : Public) : (encPublic p).length ≤ 4 * p.1.raw.length + 6 * (shortSize p + 2) := by
    simp only [encPublic, length_encPair, RootPredecessorQuery.length_encInput,
      encNat_apply, Nat.size_eq_bits_len, shortSize, RootPredecessorQuery.shortSize]
    omega
  refine ⟨d, h.mono c (fun p => ?_) (fun p => ?_)⟩ <;>
    refine le_trans ?_ (hc p) <;> have hp := he p <;>
    change (encPublic p).length + ((encPublic p).length + _) ≤ 8 * p.1.raw.length + u p <;>
    dsimp only [u] <;> omega

/-- A uniform finite machine starts from the public word on its read-only input tape. It pays
linear raw length plus polynomial short overhead before the continuation's clock starts. -/
theorem exists_prepend {K : ℕ} {L : Type} [Finite L] (tape : Fin K) (leaf : MultiTapeATM K Bool L) :
    ∃ (u : ℕ) (Q : Type) (_ : Finite Q) (atm : MultiTapeATM u Bool Q) (C d : ℕ),
      ∀ (p : Public) (t : ℕ),
        let input := encPublic p
        let header := frame input
        let cfg := WordGameLeaf.config tape (some leaf.toPTM.initial)
          (header ++ rankFlags (Nat.clog 2 p.2)) header.length (TerminalLayout.blank K input)
        leaf.HaltsWithin t cfg →
          let time := C * (p.1.raw.length + shortSize p ^ d + 1) + t
          atm.HaltsWithin time (atm.toPTM.toNTM.initCfg input) ∧
            (atm.AcceptsWithin time (atm.toPTM.toNTM.initCfg input) ↔
              leaf.AcceptsWithin t cfg) := by
  obtain ⟨d, hd⟩ := prepare_inO
  obtain ⟨u, Q, hQ, atm, C, h⟩ := FramedPrefixInput.exists_prepend hd tape leaf
  refine ⟨u, Q, hQ, atm, C, d, ?_⟩
  intro p t
  have hz : (tapesCfg (encPublic p) (fun _ : Fin K => []) 0 0 []) =
      wordsCfg (encPublic p) (none : Option Unit) (fun _ : Fin K => []) [] :=
    tapesCfg_zero_withState _ _ _
  simpa only [FramedPrefixInput.ready, TerminalLayout.blank, hz, Cfg.withState,
    WordGameLeaf.config] using h p t

end Turing.MultiTapeATM.RootPackingBalance.Initialize
