/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.STCON.SeedSearchSetup
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatLength
import CslibFrontier.Tactic.EncLen

/-!
# Binary seed scheduler for subdivided STCON

The scheduler retains the initialized setup, binary seed and source counters, and the
designated answer while calling a scanner on the original read-only input. It enumerates only
original roots, while the scanner can visit any subdivision vertex. The scanner returns a
controller verdict on a successful branch and fails on a rejected branch. A bad verdict advances
the seed counter and a passing negative verdict can terminate the search.

The clock bounds scanner calls in the rejecting state monad. The workspace lemmas bound the
encoded scheduler frame and its product with a scanner state. These are callback-boundary
certificates for subsequent native loop compilation.

## Main definitions

* `SeedScanRequest`: fixed setup, binary seed rank and subdivision source ID.
* `runSeedSchedulerFor`: scheduler using the STCON source numbering.

## Main results

* `seedScanRequest_inSpace`: native linear-space request construction.
* `runSeedSchedulerFor_eq`: agreement with the indexed search, including list multiplicity.
* `length_seedSchedulerCall_le`: additive scheduler and scanner state bound.
* `runSeedSchedulerFor_clock`: product bound for the spent callback clock.

## References

* [Hoza2026NLUL], Section 1.2.
-/

public section

namespace Cslib.Complexity.STCON

open DoubleCounting Reachability.Hoza
open _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.MultiTapeTM.ComputableInSpace
open _root_.Turing.QueryMachine.Subdivision

/-- The data needed by a same-input source scanner. -/
structure SeedScanRequest where
  /-- Retained dimensions and fixed endpoints. -/
  setup : SeedSearchSetup
  /-- Binary seed rank, read least significant bit first. -/
  seed : ℕ
  /-- Subdivision ID at which to start the scan. -/
  sourceID : ℕ

/-- Encode the scanner request with binary scalar fields. -/
enc_structure encSeedScanRequest : SeedScanRequest where
  setup : encSeedSearchSetup, seed : encNat, sourceID : encNat

/-- Scheduler state retained across a scan. The cursor is zero on the designated call. -/
structure SeedSchedulerFrame where
  /-- The pending scan. -/
  request : SeedScanRequest
  /-- Position in the original-source enumeration. -/
  cursor : ℕ
  /-- The designated answer, absent until the designated scan has decided. -/
  answer : Option Bool

/-- Encode the retained scheduler state using a binary cursor and constant-size answer. -/
enc_structure encSeedSchedulerFrame : SeedSchedulerFrame where
  request : encSeedScanRequest, cursor : encNat, answer : (encOption encBool)

/-- Build the retained frame for a scanner call from the binary counters. -/
@[expose] def seedSchedulerFrame (setup : SeedSearchSetup) (seed : ℕ) (phase : Option (ℕ × Bool))
    (sourceID : ℕ) : SeedSchedulerFrame :=
  ⟨⟨setup, seed, sourceID⟩, (phase.map Prod.fst).getD 0, phase.map Prod.snd⟩

/-- Compute a scanner request from the retained setup, seed, and optional original-source
position. An absent position requests the designated scan. -/
def seedScanRequest (p : SeedSearchSetup × ℕ × Option ℕ) : SeedScanRequest :=
  let (setup, seed, position) := p
  ⟨setup, seed, position.elim setup.sourceID setup.originalSourceID⟩

/-- The designated callback frame carries the request for the retained source. -/
theorem seedSchedulerFrame_designated_request (s : SeedSearchSetup) (seed : ℕ) :
    (seedSchedulerFrame s seed none s.sourceID).request = seedScanRequest (s, seed, none) := by
  unfold seedScanRequest
  rfl

/-- An indexed callback frame carries the request for that original source position. -/
theorem seedSchedulerFrame_indexed_request (s : SeedSearchSetup) (seed position : ℕ)
    (answer : Bool) :
    (seedSchedulerFrame s seed (some (position, answer))
      (s.originalSourceID position)).request = seedScanRequest (s, seed, some position) := by
  unfold seedScanRequest
  rfl

/-- Preparing a request uses linear native workspace in its encoded arguments. -/
theorem seedScanRequest_inSpace :
    ComputableInSpace seedScanRequest
      (encPair encSeedSearchSetup (encPair encNat (encOption encNat))) encSeedScanRequest
      (fun p => (encPair encSeedSearchSetup (encPair encNat (encOption encNat)) p).length) := by
  let e := encPair encNat (encOption encNat)
  have hs := fst encSeedSearchSetup e
  have ht := snd encSeedSearchSetup e
  have hi := budget_comp_linear (fst encNat (encOption encNat)) ht
  have hp := budget_comp_linear (snd encNat (encOption encNat)) ht
  have hsrc := optionElimSnd
    (encSeedSearchSetup_sourceID_budget
      (budget_id (.refl _) :
        ComputableInSpace id encSeedSearchSetup encSeedSearchSetup
          (fun s => (encSeedSearchSetup s).length)))
    originalSourceID_inSpace
  exact (encSeedScanRequest_mk_budget hs hi (budget_comp_linear hsrc (budget_prod hs hp))).of_enc_eq
    (fun (_ : SeedSearchSetup × ℕ × Option ℕ) => rfl)

/-- Run the binary scheduler on the initialized carrier. The frame exposes the retained
registers for resource accounting. A scanner can use just its request field. -/
def runSeedSchedulerFor {m : Type → Type} [AlternativeMonad m] (s : SeedSearchSetup)
    (hsource : s.sourceID < s.parameters.search.subdivision.vertexCount)
    (hroot : ∀ position < s.parameters.search.subdivision.originalCount,
      s.originalSourceID position < s.parameters.search.subdivision.vertexCount)
    (scan : SeedSchedulerFrame → m (Option ControllerVerdict)) :
    m (Option (SeedAnswer s.parameters.search.seedWidth)) :=
  runSeedScheduler
    (fun i phase u => scan (seedSchedulerFrame s i.val (phase.map fun (j, b) => (j.val, b)) u.val))
    (fun j => ⟨s.originalSourceID j.val, hroot _ j.isLt⟩) ⟨s.sourceID, hsource⟩

/-- Ignoring scheduler bookkeeping gives exactly the indexed controller semantics. -/
theorem runSeedSchedulerFor_eq {m : Type → Type} [AlternativeMonad m] (s : SeedSearchSetup)
    (hsource : s.sourceID < s.parameters.search.subdivision.vertexCount)
    (hroot : ∀ position < s.parameters.search.subdivision.originalCount,
      s.originalSourceID position < s.parameters.search.subdivision.vertexCount)
    (scan : SeedScanRequest → m (Option ControllerVerdict)) :
    runSeedSchedulerFor s hsource hroot (fun f => scan f.request) =
      runSeedSearchIndexed
        (fun bits u => scan ⟨s, (BitString.equivFin _ bits).val, u.val⟩)
        (fun j => ⟨s.originalSourceID j.val, hroot _ j.isLt⟩) ⟨s.sourceID, hsource⟩ := by
  unfold runSeedSchedulerFor
  exact runSeedScheduler_eq (length := s.parameters.search.seedWidth)
    (fun i u => scan ⟨s, i.val, u.val⟩) _ _

/-- Retained scheduler bits are linear in the setup size, even when a scanner rejects.
The bound covers all pending scans, including the designated scan with cursor zero. -/
theorem length_encSeedSchedulerFrame_le (s : SeedSearchSetup) (i cursor u : ℕ)
    (answer : Option Bool) (hi : i ≤ s.parameters.search.seedLimit)
    (hc : cursor ≤ s.parameters.search.subdivision.originalCount)
    (hu : u ≤ s.parameters.search.subdivision.vertexCount) :
    (encSeedSchedulerFrame ⟨⟨s, i, u⟩, cursor, answer⟩).length ≤
      12 * (encSeedSearchSetup s).length + 9 := by
  have hsearch := (encSeedSearchParameters_search_length_le s.parameters).trans
    (encSeedSearchSetup_parameters_length_le s)
  have hsub := (encSeedSearchSize_subdivision_length_le s.parameters.search).trans hsearch
  have hseed := (length_encNat_mono hi).trans
    ((encSeedSearchSize_seedLimit_length_le s.parameters.search).trans hsearch)
  have hcursor := (length_encNat_mono hc).trans
    ((encSubdivisionSize_originalCount_length_le s.parameters.search.subdivision).trans hsub)
  have hsource := (length_encNat_mono hu).trans
    ((encSubdivisionSize_vertexCount_length_le s.parameters.search.subdivision).trans hsub)
  cases answer <;> enc_len [encSeedSchedulerFrame_apply, encSeedScanRequest_apply]

private theorem scanFrame_bounds (s : SeedSearchSetup)
    (hlimit : s.parameters.search.seedLimit = 2 ^ s.parameters.search.seedWidth)
    (i : Fin (2 ^ s.parameters.search.seedWidth))
    (phase : Option (Fin s.parameters.search.subdivision.originalCount × Bool))
    (u : Fin s.parameters.search.subdivision.vertexCount) :
    let f := seedSchedulerFrame s i.val (phase.map fun (j, b) => (j.val, b)) u.val
    f.request.seed < s.parameters.search.seedLimit ∧
      f.cursor ≤ s.parameters.search.subdivision.originalCount ∧
      f.request.sourceID < s.parameters.search.subdivision.vertexCount := by
  refine ⟨hlimit.symm ▸ i.isLt, ?_, u.isLt⟩
  cases phase with
  | none => exact Nat.zero_le _
  | some p => exact p.1.isLt.le

/-- Each callback frame and scanner-state pair uses linear space in the setup and the
scanner state's own charged encoding. This applies to every scanner prefix, independently
of how that scan halts, by taking its state at that prefix for `state`. -/
theorem length_seedSchedulerCall_le {σ : Type} (enc : σ ↪ List Bool) (s : SeedSearchSetup)
    (hlimit : s.parameters.search.seedLimit = 2 ^ s.parameters.search.seedWidth)
    (i : Fin (2 ^ s.parameters.search.seedWidth))
    (phase : Option (Fin s.parameters.search.subdivision.originalCount × Bool))
    (u : Fin s.parameters.search.subdivision.vertexCount) (state : σ) :
    let f := seedSchedulerFrame s i.val (phase.map fun (j, b) => (j.val, b)) u.val
    (encPair encSeedSchedulerFrame enc (f, state)).length ≤
      24 * (encSeedSearchSetup s).length + (enc state).length + 19 := by
  obtain ⟨hi, hc, hu⟩ := scanFrame_bounds s hlimit i phase u
  let f := seedSchedulerFrame s i.val (phase.map fun (j, b) => (j.val, b)) u.val
  have hf : (encSeedSchedulerFrame f).length ≤ 12 * (encSeedSearchSetup s).length + 9 :=
    length_encSeedSchedulerFrame_le s i.val f.cursor u.val f.answer hi.le hc hu.le
  change (encPair encSeedSchedulerFrame enc (f, state)).length ≤ _
  simp only [length_encPair]
  omega

/-- A scanner charged at a common cost per call yields the product clock, including on
branches that fail before exhausting the candidate seeds. -/
theorem runSeedSchedulerFor_clock {σ : Type} (clock : σ → ℕ) (cost : ℕ) (s : SeedSearchSetup)
    (hsource : s.sourceID < s.parameters.search.subdivision.vertexCount)
    (hroot : ∀ position < s.parameters.search.subdivision.originalCount,
      s.originalSourceID position < s.parameters.search.subdivision.vertexCount)
    (hlimit : s.parameters.search.seedLimit = 2 ^ s.parameters.search.seedWidth)
    (scan : SeedSchedulerFrame → OptionT (StateM σ) (Option ControllerVerdict))
    (hc : ∀ f t, f.request.setup = s → f.request.seed < s.parameters.search.seedLimit →
      f.cursor ≤ s.parameters.search.subdivision.originalCount →
      f.request.sourceID < s.parameters.search.subdivision.vertexCount →
      clock ((scan f).run t).2 ≤ clock t + cost) (t : σ) :
    clock ((runSeedSchedulerFor s hsource hroot scan).run t).2 ≤
      clock t + s.parameters.search.seedLimit *
        ((1 + s.parameters.search.subdivision.originalCount) * cost) := by
  have h := runSeedScheduler_clock clock cost
    (fun i phase u => scan (seedSchedulerFrame s i.val (phase.map fun (j, b) => (j.val, b)) u.val))
    (fun j => ⟨s.originalSourceID j.val, hroot _ j.isLt⟩) ⟨s.sourceID, hsource⟩
    (fun i phase u t => by
      obtain ⟨hi, hj, hu⟩ := scanFrame_bounds s hlimit i phase u
      exact hc _ t rfl hi hj hu) t
  simpa only [hlimit, runSeedSchedulerFor] using h

/-- The native initializer sets the exclusive limit to the number of binary seeds. -/
theorem configurationSeedScheduler_seedLimit {k : ℕ} {State : Type} [Fintype State]
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) (input : List Bool) :
    let size := (configurationSeedSearchSetup ntm c input).parameters.search
    size.seedLimit = 2 ^ size.seedWidth := by
  dsimp only
  rw [(configurationSeedSearchSetup_endpoints ntm c input).1]
  rfl

/-- A polynomial bound on each callback gives a polynomial spent clock on the original
input, using the initialized seed limit and original-source count. -/
theorem configurationSeedScheduler_clock_polyBounded {k : ℕ} {State : Type} [Fintype State]
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) {cost : List Bool → ℕ}
    (hcost : PolyBounded List.length cost) :
    PolyBounded List.length (fun input =>
      let size := (configurationSeedSearchSetup ntm c input).parameters.search
      size.seedLimit * ((1 + size.subdivision.originalCount) * cost input)) := by
  obtain ⟨hseed, hsource, _⟩ := configurationSeedSearchParameters_polyBounded ntm c
  refine (hseed.mul (((PolyBounded.const 1).add hsource).mul hcost)).mono fun input => ?_
  dsimp only
  rw [(configurationSeedSearchSetup_endpoints ntm c input).1]

end Cslib.Complexity.STCON
