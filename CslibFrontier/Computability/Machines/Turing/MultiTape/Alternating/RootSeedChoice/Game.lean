/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.RootSeedChoice.Fields
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.RootPackingBalance.Initialize
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.RootPackingBalance.TerminalGraph
public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.RootSeedInstall
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-!
# A common seed for every root balance challenge

The root schedule supplies the hash universe, label length and edge count. The game selects all
four coefficients before any edge, rank, or bit is challenged. The terminal reads that same choice
with the short-field decoder, which retains the underlying root schedule.
-/

public section

namespace Turing.MultiTapeATM.RootSeedChoice

open Cslib MultiTapeTM MultiTapePTM QuantifiedWord RootPackingBalance
open RootBalanceRequest (Public encPublic)

/-- The seed choices precede the edge, rank, and bit challenges. -/
@[expose] def flags (p : Public) : List Bool :=
  seedFlags p.1.context.universeSize p.1.context.labelLength ++ rankFlags (Nat.clog 2 p.2)

private def key (p : Public) := (p.1.context, p.2)

private abbrev encKey := encPair SeededPredecessor.encContext encNat

private theorem key_deg : ComputableInDegree key encPublic encKey 1 1 :=
  (RootPredecessorQuery.encInput_context_deg.comp (ComputableInDegree.fst _ _)).prod
    (ComputableInDegree.snd _ _)

private theorem key_size : PolyBounded Initialize.shortSize (fun p => (encKey (key p)).length) := by
  apply PolyBounded.of_forall_le 2 1
  intro p
  simp only [key, length_encPair, encNat_apply, ← Nat.size_eq_bits_len, Initialize.shortSize,
    RootPredecessorQuery.shortSize, pow_one]
  omega

private theorem flags_poly : ComputableInPolyTime (fun v : SeededPredecessor.Context × ℕ =>
    seedFlags v.1.universeSize v.1.labelLength ++ rankFlags (Nat.clog 2 v.2)) encKey encBits :=
  (computableInPolyTime_seedFlags.comp (ComputableInPolyTime.fst _ _)).bitsAppend
    (computableInPolyTime_rankFlags.comp (ComputableInPolyTime.snd _ _))

/-- All physically played fields fit in polynomial space on the short graph parameters. -/
theorem flags_size : PolyBounded Initialize.shortSize (fun p => (flags p).length) :=
  flags_poly.polyBounded_length.comp (g := key) key_size

/-- A native initializer copies the schedule and prepares all seed and balance flags. -/
theorem exists_flags_inO : ∃ d, ComputableInO (fun p : Public => (p, flags p))
    encPublic RootBalanceRequest.encInput (fun p => p.1.raw.length + Initialize.shortSize p ^ d)
    (fun p => p.1.raw.length + Initialize.shortSize p ^ d) :=
  Initialize.prepare_inO_of_meta key_deg key_size flags_poly

/-- A canonical public template gives no information about the seed to select. -/
@[expose] def zeroSeed (U a : ℕ) : BalancedSchedules.SeededLabels.Seed U (6 * a) := fun _ => 0

/-- Every continuation receives the public request with precisely the one chosen seed installed.
This equality also holds for suffix games with additional existential or universal moves. -/
theorem plays_installed (k q copies σ a : ℕ) (value : RootBalanceRequest.Input → Prop)
    (rest : List Bool) :
    let U := RootPredecessorGraph.vertexCount k q copies
    let p := graphPublic k q copies σ a (zeroSeed U a)
    plays (fun choices => value (RootSeedInstall.install (p, choices))) []
        (seedFlags U a ++ rest) ↔
      ∃ seed, plays (fun tail => value (graphPublic k q copies σ a seed, tail)) [] rest := by
  let U := RootPredecessorGraph.vertexCount k q copies
  let p := graphPublic k q copies σ a (zeroSeed U a)
  change plays _ [] (seedFlags U a ++ rest) ↔ _
  rw [plays_seedFlags]
  apply exists_congr
  intro seed
  let w := SeedChoice.word seed
  let v := fun choices => value (RootSeedInstall.install (p, choices))
  have hw (tail : List Bool) : RootSeedInstall.install (p, w ++ tail) =
      (graphPublic k q copies σ a seed, tail) := RootSeedInstall.install_word p seed tail
  simpa only [v, List.append_nil, List.nil_append, hw] using plays_append_prefix v w [] rest

/-- The same guessed coefficients are installed before checking any branch of balance. -/
theorem plays_iff_exists_balanced {k q copies : ℕ} {S : Type} (M : MultiTapePTM k Bool S)
    (input : List Bool) (b σ : ℕ) (code : BlockLetter k S b → Fin copies → Bool) (a : ℕ) :
    let U := RootPredecessorGraph.vertexCount k q copies
    let p := graphPublic k q copies σ a (zeroSeed U a)
    plays (fun choices => terminalValue k (RootSeedInstall.install (p, choices))) [] (flags p) ↔
      ∃ seed, PacketPacking.Seeded.Balanced U a (explicitVertexEquiv k q copies).toEmbedding
        (RootPredecessorGraph.rowOf M input b σ code) (RootPredecessorGraph.colOf k q copies)
        seed := by
  let U := RootPredecessorGraph.vertexCount k q copies
  let p := graphPublic k q copies σ a (zeroSeed U a)
  exact (plays_installed k q copies σ a (terminalValue k) (rankFlags (Nat.clog 2 p.2))).trans
    (exists_congr fun seed => plays_iff_balanced M input b σ code a seed)

end Turing.MultiTapeATM.RootSeedChoice
