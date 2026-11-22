/-
Copyright (c) 2026 Christian Reitwiessner, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Reachability.DoubleCounting.Scan.BoundedWalk.Runtime
public import CslibFrontier.Computability.Complexity.Problems.STCON.JustesenWeightedSubdivision
import CslibFrontier.Foundations.Data.Nat.BinarySize

/-!
# Bounded walks for Justesen-weighted STCON

The native component certificates bound the workspace for one transition and for reading
the query position, halt flag, and optional unused fuel.

The retained-dimension walk calls the initialized Justesen subdivision adjacency on the
original input. Successful first halts correspond to canonical selector lists for typed
walks on the generated subdivision. For fuel at most the subdivision vertex count, the
common walk clock bounds all branches and every encoded prefix has logarithmic length
in the original input. The native entry certificate computes the initialized context and
reader width using that logarithmic budget.
-/

public section

namespace Cslib.Complexity.STCON

open Cslib.Code.JustesenFamily Cslib.DoubleCounting.Scan
open Cslib.LayeredDigraph.Subdivision Cslib.Reachability.Hoza
open _root_.Turing _root_.Turing.MultiTapeTM
open _root_.Turing.DoubleCounting.BoundedWalk _root_.Turing.QueryMachine.Subdivision

variable {k : ℕ} {State : Type} [Fintype State]

/-- Enter the retained-dimension walk from the initialized Justesen context and valid
subdivision registers. Every adjacency call uses the common clock three. -/
noncomputable def configurationJustesenBoundedWalk (ntm : MultiTapeNTM k Bool State)
    (c : ℕ) (w : List Bool) (rank : ℕ)
    (r : Registers
      (configurationSeedSearchSetup ntm c w).parameters.search.subdivision.vertexCount) :
    NondeterministicQueryMachine
      (Runtime.State JustesenSubdivisionContext JustesenSubdivisionState) :=
  let edge := justesenWeightedSubdivisionCallback ntm
  let start := fun ctx u v => justesenSubdivisionEdgeStart (ctx, u, v)
  let ctx := configurationJustesenSubdivisionContext ntm c w rank
  Runtime.machine edge start callbackVerdict 3 (Runtime.entry edge start callbackVerdict 3 ctx r)

/-- The initial state is computed from the original encoded word and a valid seed rank.
The binary endpoint and fuel producers use the same logarithmic workspace budget. -/
theorem configurationJustesenBoundedWalk_init_inSpace (ntm : MultiTapeNTM k Bool State) (c : ℕ)
    {α : Type} {encIn : α ↪ List Bool} {rank : α → ℕ}
    {r : (a : α) → Registers
      (configurationSeedSearchSetup ntm c (encIn a)).parameters.search.subdivision.vertexCount}
    (hrank : ComputableInLogSpace rank encIn encNat)
    (hrank_lt : ∀ a, rank a <
      (configurationSeedSearchParameters ntm c (encIn a)).search.seedLimit)
    (hcurrent : ComputableInSpace (fun a => (r a).current.val) encIn encNat
      (fun a => Nat.log2 (encIn a).length))
    (htarget : ComputableInSpace (fun a => (r a).target.val) encIn encNat
      (fun a => Nat.log2 (encIn a).length))
    (hfuel : ComputableInSpace (fun a => (r a).fuel) encIn encNat
      (fun a => Nat.log2 (encIn a).length)) :
    ComputableInSpace
      (fun a => (configurationJustesenBoundedWalk ntm c (encIn a) (rank a) (r a)).init)
      encIn (Runtime.encState encJustesenSubdivisionContext encJustesenSubdivisionState)
      (fun a => Nat.log2 (encIn a).length) := by
  let ctx (a : α) := configurationJustesenSubdivisionContext ntm c (encIn a) (rank a)
  let budget (a : α) := Nat.log2 (encIn a).length
  have hctx : ComputableInSpace ctx encIn encJustesenSubdivisionContext budget :=
    configurationJustesenSubdivisionContext_inSpace ntm c hrank hrank_lt
  have hsize := encJustesenSubdivisionContext_subdivision_budget hctx
  have hdim : ComputableInSpace
      (fun a =>
        (configurationSeedSearchSetup ntm c (encIn a)).parameters.search.subdivision.vertexCount)
      encIn encNat budget :=
    (encSubdivisionSize_vertexCount_budget hsize).of_enc_eq fun a => by
      simp only [(configurationSeedSearchSetup_endpoints ntm c (encIn a)).1,
        ctx, configurationJustesenSubdivisionContext]
  have hentry := Runtime.entry_budget (justesenWeightedSubdivisionCallback ntm)
    (fun ctx u v => justesenSubdivisionEdgeStart (ctx, u, v)) callbackVerdict 3
    encJustesenSubdivisionContext encJustesenSubdivisionState hctx hdim hcurrent htarget hfuel
  exact hentry.of_enc_eq fun _ => by
    simp only [configurationJustesenBoundedWalk, Runtime.machine_init, ctx]

/-- A successful first halt uses exactly the canonical selectors of a typed walk on the
Justesen-weighted subdivision, and returns the same unused fuel. -/
theorem configurationJustesenBoundedWalk_firstHalting_iff (ntm : MultiTapeNTM k Bool State)
    (c : ℕ) (w : List Bool) :
    let I := configurationInstance ntm c w
    let size := (configurationSeedSearchSetup ntm c w).parameters.search.subdivision
    ∀ (seed : Fin (2 ^ codeLength I.n (I.n - 1))) (r : Registers size.vertexCount)
      (bits : List Bool) (left : ℕ),
      let M := configurationJustesenBoundedWalk ntm c w seed.val r
      let adjacent := configurationJustesenSubdivisionAdjacent ntm c w seed
      M.FirstHalting w bits M.init ∧ Runtime.remainingFuel (M.run w bits) = some left ↔
        ∃ tail, bits = selectors 3 tail ∧
          (walkM readNext (fun u v => pure (adjacent u v)) r.target r.fuel r.current tail).1 =
            some left := by
  intro I size seed r bits left M adjacent
  let edge := justesenWeightedSubdivisionCallback ntm
  let start := fun ctx u v => justesenSubdivisionEdgeStart (ctx, u, v)
  let ctx := configurationJustesenSubdivisionContext ntm c w seed.val
  have hcall := configurationJustesenSubdivisionEdge_halts_and_agrees ntm c w seed
  let initial := Runtime.entry edge start callbackVerdict 3 ctx r
  let walk := Runtime.machine edge start callbackVerdict 3 initial
  have hinit : walk.init = initial := Runtime.machine_init edge start callbackVerdict 3 initial
  change walk.FirstHalting w bits walk.init ∧
    Runtime.remainingFuel (walk.run w bits) = some left ↔ _
  rw [NondeterministicQueryMachine.run, hinit]
  exact Runtime.firstHalting_remainingFuel_iff edge start callbackVerdict 3 initial ctx r w adjacent
    (fun u v => (hcall u v).1) (fun u v => (hcall u v).2) bits left

/-- The initialized Justesen walk's transition and state observers use workspace linear in
their encoded operation requests. The certificates apply to every runtime state. -/
theorem configurationJustesenBoundedWalk_parts_inSpace (ntm : MultiTapeNTM k Bool State)
    (c : ℕ) (w : List Bool) (rank : ℕ)
    (r : Registers
      (configurationSeedSearchSetup ntm c w).parameters.search.subdivision.vertexCount) :
    let M := configurationJustesenBoundedWalk ntm c w rank r
    let enc := Runtime.encState encJustesenSubdivisionContext encJustesenSubdivisionState
    let encNext := Runtime.encStep encJustesenSubdivisionContext encJustesenSubdivisionState
    ComputableInSpace M.query enc encNat (fun s => (enc s).length) ∧
    ComputableInSpace M.next encNext enc (fun p => (encNext p).length) ∧
    ComputableInSpace M.halted enc encBool (fun s => (enc s).length) ∧
    ComputableInSpace Runtime.remainingFuel enc (encOption encNat) (fun s => (enc s).length) := by
  obtain ⟨hq, hn, hh, _, _⟩ := justesenWeightedSubdivisionCallback_parts_inSpace ntm
  exact ⟨Runtime.query_inSpace _ _ _ _ _ _ _ hq,
    Runtime.next_inSpace _ _ _ _ _ _ _ justesenSubdivisionEdgeStart_inSpace hn hh
      (callbackVerdict_inSpace _ _),
    Runtime.halted_inSpace _ _ _ _ _ _ _, Runtime.remainingFuel_inSpace _ _⟩

/-- The initialized walk's state envelope is logarithmic apart from the charged adjacency state. -/
theorem configurationJustesenBoundedWalk_stateBound_le_log (ntm : MultiTapeNTM k Bool State)
    (c : ℕ) :
    ∃ C, ∀ w : List Bool,
      let I := configurationInstance ntm c w
      let size := (configurationSeedSearchSetup ntm c w).parameters.search.subdivision
      ∀ (seed : Fin (2 ^ codeLength I.n (I.n - 1))) (fuel calleeBound : ℕ),
        fuel ≤ size.vertexCount →
        Runtime.stateBound size.vertexCount fuel 3
          (encJustesenSubdivisionContext
            (configurationJustesenSubdivisionContext ntm c w seed.val)).length calleeBound ≤
          C * (Nat.log2 w.length + 1) + calleeBound := by
  obtain ⟨D, hcontext⟩ := length_configurationJustesenSubdivisionContext_le_log ntm c
  obtain ⟨P, hvertices⟩ := length_configurationSubdivisionVertexCount_le_log ntm c
  refine ⟨2 * D + 22 * P + 31, fun w => ?_⟩
  intro I size seed fuel calleeBound hfuel
  have hctx := hcontext w seed.val seed.isLt
  have hvertices := hvertices w
  have hwidth : Nat.log2 size.vertexCount.size ≤ (encNat size.vertexCount).length := by
    rw [length_encNat_eq_size]
    exact Nat.log2_le_self _
  have hf := length_encNat_mono hfuel
  have hclock : (encNat 3).length = 2 := rfl
  have hlog : 1 ≤ Nat.log2 w.length + 1 := Nat.succ_le_succ (Nat.zero_le _)
  change (encNat size.vertexCount).length ≤ _ at hvertices
  simp only [Runtime.stateBound, hclock, Nat.add_mul, Nat.mul_assoc]
  omega

/-- At each valid seed, the common clock and logarithmic state bound cover all selector
lists, including rejection and suspended adjacency calls. -/
theorem configurationJustesenBoundedWalk_bounds (ntm : MultiTapeNTM k Bool State) (c : ℕ) :
    ∃ C, ∀ w : List Bool,
      let I := configurationInstance ntm c w
      let size := (configurationSeedSearchSetup ntm c w).parameters.search.subdivision
      ∀ (seed : Fin (2 ^ codeLength I.n (I.n - 1))) (r : Registers size.vertexCount),
        r.fuel ≤ size.vertexCount →
        let M := configurationJustesenBoundedWalk ntm c w seed.val r
        M.HaltsWithin w (r.fuel * (size.vertexCount.size + 6) + (size.vertexCount.size + 2)) ∧
          ∀ bits, (Runtime.encState encJustesenSubdivisionContext encJustesenSubdivisionState
            (M.run w bits)).length ≤ C * (Nat.log2 w.length + 1) := by
  obtain ⟨A, hcall⟩ := configurationJustesenSubdivisionEdge_contract ntm c
  obtain ⟨C, hbound⟩ := configurationJustesenBoundedWalk_stateBound_le_log ntm c
  refine ⟨C + A, fun w => ?_⟩
  intro I size seed r hfuel M
  let edge := justesenWeightedSubdivisionCallback ntm
  let start := fun ctx u v => justesenSubdivisionEdgeStart (ctx, u, v)
  let ctx := configurationJustesenSubdivisionContext ntm c w seed.val
  let b := Nat.log2 w.length + 1
  refine ⟨Runtime.haltsWithin edge start callbackVerdict 3 ctx r w, fun bits => ?_⟩
  have hcallee (u v : Fin size.vertexCount) (t : ℕ) (ht : t ≤ 3) :
      (encJustesenSubdivisionState (edge.runFrom w (start ctx u.val v.val) t)).length ≤ A * b :=
    (hcall w seed u v).2.2.2 t ht
  have hrun := Runtime.length_run_le edge start callbackVerdict 3 ctx r w bits
    encJustesenSubdivisionContext encJustesenSubdivisionState (A * b) hcallee
  exact hrun.trans (by simpa only [b, Nat.add_mul] using hbound w seed r.fuel (A * b) hfuel)

/-- A common selector clock for fuel at most the initialized subdivision vertex count. -/
@[expose] noncomputable def configurationJustesenBoundedWalkClock (ntm : MultiTapeNTM k Bool State)
    (c : ℕ) (w : List Bool) : ℕ :=
  let n := (configurationSeedSearchSetup ntm c w).parameters.search.subdivision.vertexCount
  n * (n.size + 6) + (n.size + 2)

/-- The common selector clock is polynomial in the length of the original input. -/
theorem configurationJustesenBoundedWalkClock_polyBounded
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) :
    PolyBounded List.length (configurationJustesenBoundedWalkClock ntm c) := by
  let count (w : List Bool) :=
    (configurationSeedSearchSetup ntm c w).parameters.search.subdivision.vertexCount
  have hcount : PolyBounded List.length count :=
    configurationSubdivisionVertexCount_polyBounded ntm c
  have hwidth : PolyBounded List.length (fun w => (count w).size) :=
    hcount.mono fun w => Nat.size_le_self (count w)
  exact (hcount.mul (hwidth.add (.const 6))).add (hwidth.add (.const 2))

/-- The common clock bounds every selector branch, uniformly in the rank and endpoints. -/
theorem configurationJustesenBoundedWalk_haltsWithin_clock
    (ntm : MultiTapeNTM k Bool State) (c : ℕ) (w : List Bool) (rank : ℕ)
    (r : Registers
      (configurationSeedSearchSetup ntm c w).parameters.search.subdivision.vertexCount)
    (hfuel : r.fuel ≤
      (configurationSeedSearchSetup ntm c w).parameters.search.subdivision.vertexCount) :
    (configurationJustesenBoundedWalk ntm c w rank r).HaltsWithin w
      (configurationJustesenBoundedWalkClock ntm c w) := by
  have h := Runtime.haltsWithin (justesenWeightedSubdivisionCallback ntm)
    (fun ctx u v => justesenSubdivisionEdgeStart (ctx, u, v)) callbackVerdict 3
    (configurationJustesenSubdivisionContext ntm c w rank) r w
  unfold configurationJustesenBoundedWalk configurationJustesenBoundedWalkClock
  exact NondeterministicQueryMachine.HaltsWithin.mono _ _ h
    (Nat.add_le_add_right (Nat.mul_le_mul_right _ hfuel) _)

end Cslib.Complexity.STCON
