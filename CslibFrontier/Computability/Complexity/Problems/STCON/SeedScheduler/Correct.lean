/-
Copyright (c) 2026 Christian Reitwiessner, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.STCON.SeedScheduler

/-!
# Correctness of the initialized seed scheduler

The binary request frames of the initialized scheduler use the same seed numbers,
designated endpoints, and row-major original roots as the indexed isolation search.
With exact scanner outcomes, the scheduler selects the least min-isolating seed and
returns the reachability answer for the configuration instance.

## Main results

* `configurationSeedScheduler_correct` transports the indexed search correctness theorem
  to the initialized scheduler and its scanner requests.
-/

public section

namespace Cslib.Complexity.STCON

open Code.JustesenFamily DoubleCounting LayeredDigraph.Subdivision Reachability.Hoza
open _root_.Turing _root_.Turing.MultiTapeNTM

/-- The initialized scheduler finds the least min-isolating seed and decides the configuration
instance, given a scanner with exactly one effect-free verdict for each valid request.
The requested source and the retained target are subdivision IDs. With the list monad the
outcome equation is a singleton, so it includes multiplicity. -/
theorem configurationSeedScheduler_correct {m : Type → Type} [AlternativeMonad m] [LawfulMonad m]
    {k : ℕ} {State : Type} [Fintype State]
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) (input : List Bool)
    (scan : SeedScanRequest → m (Option ControllerVerdict)) :
    let I := configurationInstance ntm c input
    let setup := configurationSeedSearchSetup ntm c input
    let size := setup.parameters.search
    let index := configurationSubdivisionIndex ntm c input
    let hs := (configurationSeedSearchSetup_endpoints_lt_vertexCount ntm c input).1
    let ht := (configurationSeedSearchSetup_endpoints_lt_vertexCount ntm c input).2
    let hr := fun _ hp =>
      configurationSeedSearchSetup_originalSourceID_lt_vertexCount ntm c input hp
    (∀ (seed : Fin (2 ^ size.seedWidth)) (source : Fin size.subdivision.vertexCount),
      let seedBits := fun j : Fin (codeLength I.n (I.n - 1)) => seed.val.testBit j.val
      let adj := generatedSubdivisionAdj (layeredDigraph I) index seedBits
      ∃ verdict, scan ⟨setup, seed.val, source.val⟩ = pure (some verdict) ∧
        match verdict with
        | .bad j => ¬ ∃! p, Passes adj source j p
        | .decided hit => (∀ j, ∃! p, Passes adj source j p) ∧
            (hit = true ↔ Relation.ReflTransGen adj source ⟨setup.targetID, ht⟩)) →
    ∃ result, runSeedSchedulerFor setup hs hr (fun frame => scan frame.request) =
        pure (some result) ∧
      (layeredDigraph I).IsMinIsolating (generatedWeight (fun j => result.seed.val.testBit j.val)) ∧
      (∀ i : Fin (2 ^ size.seedWidth), i < result.seed →
        ¬ (layeredDigraph I).IsMinIsolating (generatedWeight (fun j => i.val.testBit j.val))) ∧
      (result.reachable = true ↔ I ∈ STCON) := by
  intro I setup size index hs ht hr hscan
  let source := layeredCoordinates I (layeredStart I)
  let target := layeredCoordinates I (layeredTarget I)
  obtain ⟨hparams, hids⟩ := configurationSeedSearchSetup_endpoints ntm c input
  have hwidth : size.seedWidth = codeLength I.n (I.n - 1) :=
    congrArg (fun p : SeedSearchParameters => p.search.seedWidth) hparams
  have hbound : size.subdivision.chainBound = generatedWeightBound I.n (I.n - 1) :=
    congrArg (fun p : SeedSearchParameters => p.search.subdivision.chainBound) hparams
  let bound := (configurationSeedSearchParameters ntm c input).search.subdivision.chainBound
  have hchain : size.subdivision.chainBound = bound :=
    congrArg (fun p : SeedSearchParameters => p.search.subdivision.chainBound) hparams
  have endpointVal (v : Fin ((I.n - 1) + 1) × Fin I.n) :
      (index (root size.subdivision.chainBound v)).val =
        (subdivisionIndex I bound (root bound v)).val := by
    rw [configurationSubdivisionIndex_val]
    simp only [subdivisionIndex_root_val]
    rw [hchain]
  have hsource : (⟨setup.sourceID, hs⟩ : Fin size.subdivision.vertexCount) =
      index (root size.subdivision.chainBound source) :=
    Fin.ext ((Prod.mk.inj hids).1.trans (endpointVal source).symm)
  have htarget : (⟨setup.targetID, ht⟩ : Fin size.subdivision.vertexCount) =
      index (root size.subdivision.chainBound target) :=
    Fin.ext ((Prod.mk.inj hids).2.trans (endpointVal target).symm)
  have hroots :
      List.ofFn (fun j : Fin size.subdivision.originalCount =>
        (⟨setup.originalSourceID j.val, hr _ j.isLt⟩ : Fin size.subdivision.vertexCount)) =
        List.ofFn (originalRootID index) := by
    apply List.ext_getElem
    · simpa only [List.length_ofFn] using configurationSeedSearchSetup_originalCount ntm c input
    · intro i _ hi
      simp only [List.getElem_ofFn]
      apply Fin.ext
      rw [originalRootID, configurationSubdivisionIndex_val]
      exact configurationSeedSearchSetup_originalSourceID_eq ntm c input
        ⟨i, by simpa only [List.length_ofFn] using hi⟩
  let controller (bits : Fin (codeLength I.n (I.n - 1)) → Bool)
      (u : Fin size.subdivision.vertexCount) :=
    scan ⟨setup, (BitString.equivFin _ bits).val, u.val⟩
  have hc (bits : Fin (codeLength I.n (I.n - 1)) → Bool) (u : Fin size.subdivision.vertexCount) :
      ∃ verdict, controller bits u = pure (some verdict) ∧
        match verdict with
        | .bad j => ¬ ∃! p, Passes (generatedSubdivisionAdj (layeredDigraph I) index bits) u j p
        | .decided hit =>
          (∀ j, ∃! p, Passes (generatedSubdivisionAdj (layeredDigraph I) index bits) u j p) ∧
            (hit = true ↔ Relation.ReflTransGen
              (generatedSubdivisionAdj (layeredDigraph I) index bits) u
              (index (root size.subdivision.chainBound target))) := by
    let seed := (BitString.equivFin _ bits).cast (congrArg (2 ^ ·) hwidth.symm)
    have hbits : (fun j : Fin (codeLength I.n (I.n - 1)) => seed.val.testBit j.val) = bits := by
      funext j
      exact BitString.testBit_equivFin ..
    obtain ⟨verdict, hreturn, hspec⟩ := hscan seed u
    rw [hbits, htarget] at hspec
    exact ⟨verdict, hreturn, hspec⟩
  have hb (bits : Fin (codeLength I.n (I.n - 1)) → Bool) (v : Fin ((I.n - 1) + 1) × Fin I.n) :
      generatedWeight bits v ≤ size.subdivision.chainBound :=
    hbound ▸ (generatedWeight_lt_bound bits v).le
  obtain ⟨result, hrun, hmin, hleast, hreach⟩ :=
    runGeneratedSeedSearch_correct (layeredDigraph I) (fun _ => rfl) index hb
      source target controller hc
  rw [runSeedSearchIndexed_eq] at hrun
  rw [runSeedSchedulerFor_eq, runSeedSearchIndexed_eq, hroots, hsource, hwidth]
  have bitsOfRank (i : Fin (2 ^ codeLength I.n (I.n - 1))) :
      (BitString.equivFin _).symm i = fun j : Fin (codeLength I.n (I.n - 1)) =>
        i.val.testBit j.val := by
    funext j
    exact BitString.equivFin_symm_apply ..
  refine ⟨result, hrun, ?_, ?_, hreach.trans (layeredDigraph_reachable_iff I)⟩
  · rw [← bitsOfRank]
    exact hmin
  · intro i hi
    rw [← bitsOfRank]
    exact hleast i hi

end Cslib.Complexity.STCON
