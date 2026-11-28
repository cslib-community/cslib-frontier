/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.HopcroftKarp.Internal
import CslibFrontier.Computability.WordRAM.CountingLoop
import CslibFrontier.Computability.WordRAM.Notation
import CslibFrontier.Computability.WordRAM.SymbolicExec
import Mathlib.Algebra.BigOperators.Fin

/-!
# Hopcroft–Karp iterative DFS frame and single-step transitions

Pure accumulator/potential lemmas for `hkDfs` and `hkDfsRoots`, augmenting-path copy helper
`copyAugCode`, stack-frame invariant `DfsFrame`, and single-step symbolic-execution theorems
(`exec_dfsStep_pop`, `exec_dfsStep_skip`, `exec_dfsStep_accept`, `exec_dfsStep_push`) for the
explicit-stack depth-first search loop `dfsLoop` ([HopcroftKarp1973]; [CLRS2009], Problem 26-6).

## Main definitions

* `Cslib.Algorithms.WordRAM.HopcroftKarp.Internal.VisCovers`,
  `Cslib.Algorithms.WordRAM.HopcroftKarp.Internal.dfsPot`: pure visited-coverage and DFS potential.
* `Cslib.Algorithms.WordRAM.HopcroftKarp.Internal.dfsStepBody`,
  `Cslib.Algorithms.WordRAM.HopcroftKarp.Internal.dfsLoop`,
  `Cslib.Algorithms.WordRAM.HopcroftKarp.Internal.DfsFrame`: explicit-stack DFS loop and frame.

## Main results

* `Cslib.Algorithms.WordRAM.HopcroftKarp.Internal.hkDfs_pure_props`,
  `Cslib.Algorithms.WordRAM.HopcroftKarp.Internal.hkDfsRoots_nodup_snd`: pure invariants of `hkDfs`.
* `Cslib.Algorithms.WordRAM.HopcroftKarp.Internal.exec_dfsStep_pop`,
  `Cslib.Algorithms.WordRAM.HopcroftKarp.Internal.exec_dfsStep_skip`,
  `Cslib.Algorithms.WordRAM.HopcroftKarp.Internal.exec_dfsStep_accept`,
  `Cslib.Algorithms.WordRAM.HopcroftKarp.Internal.exec_dfsStep_push`: single-step transitions of
  `dfsStepBody`.

## References

* [J. E. Hopcroft and R. M. Karp, *An n^{5/2} Algorithm for Maximum Matchings in Bipartite
  Graphs*][HopcroftKarp1973]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest, and C. Stein,
  *Introduction to Algorithms*][CLRS2009]
-/

public section

namespace Cslib.Algorithms.WordRAM.HopcroftKarp.Internal

open Cslib.WordRAM
open Cslib.Algorithms.Lean
open Cslib.Algorithms.Lean.MaxFlow
open Cslib.Algorithms.WordRAM.HopcroftKarp.Reg

/-! ## Pure DFS accumulator, coverage, and potential lemmas -/

private theorem hkDfsLevel_acc {m r : ℕ} (G : Fin m × Fin r → Bool)
    (mate : Vector (Option (Fin m)) r) (dist : Vector (Option ℕ) m)
    (accept : Bool) (i : ℕ)
    (next : Fin m → Vector Bool r → List (Fin m × Fin r) →
      Vector Bool r × Option (List (Fin m × Fin r)))
    (hnext : ∀ w₀ vis₀ acc₀, next w₀ vis₀ acc₀ =
      ((next w₀ vis₀ []).1, (next w₀ vis₀ []).2.map (· ++ acc₀)))
    (u : Fin m) (vs : List (Fin r)) (vis : Vector Bool r) (acc₀ : List (Fin m × Fin r)) :
    hkDfsLevel G mate dist accept i next u vs vis acc₀ =
      ((hkDfsLevel G mate dist accept i next u vs vis []).1,
        (hkDfsLevel G mate dist accept i next u vs vis []).2.map (· ++ acc₀)) := by
  induction vs generalizing vis with
  | nil => rfl
  | cons v vs ih =>
    dsimp only [hkDfsLevel]
    split
    · cases hm : vget mate v with
      | none =>
        dsimp only
        split
        · simp
        · exact ih vis
      | some w₀ =>
        dsimp only
        split
        · rw [hnext w₀ (vset vis v true) acc₀]
          cases (next w₀ (vset vis v true) []).2 <;> simp [ih]
        · exact ih vis
    · exact ih vis

theorem hkDfs_acc {m r : ℕ} (G : Fin m × Fin r → Bool) (adj : Fin m → List (Fin r))
    (mate : Vector (Option (Fin m)) r) (dist : Vector (Option ℕ) m) :
    ∀ (f i : ℕ) (u : Fin m) (vis : Vector Bool r) (acc₀ : List (Fin m × Fin r)),
      hkDfs G adj mate dist f i u vis acc₀ =
        ((hkDfs G adj mate dist f i u vis []).1,
          (hkDfs G adj mate dist f i u vis []).2.map (· ++ acc₀))
  | 0, i, u, vis, acc₀ =>
    hkDfsLevel_acc G mate dist true i (fun _ vis _ => (vis, none)) (fun _ _ _ => rfl)
      u (adj u) vis acc₀
  | f + 1, i, u, vis, acc₀ =>
    hkDfsLevel_acc G mate dist false i (hkDfs G adj mate dist f (i + 1))
      (hkDfs_acc G adj mate dist f (i + 1)) u (adj u) vis acc₀

/-- Remaining-depth continuation supplied to `hkDfsLevel` for the recursive `hkDfs` call. -/
@[expose] def dfsNext {m r : ℕ} (G : Fin m × Fin r → Bool) (adj : Fin m → List (Fin r))
    (mate : Vector (Option (Fin m)) r) (dist : Vector (Option ℕ) m) :
    ℕ → ℕ → Fin m → Vector Bool r → List (Fin m × Fin r) →
      Vector Bool r × Option (List (Fin m × Fin r))
  | 0, _, _, vis, _ => (vis, none)
  | f + 1, i, w₀, vis, acc₀ => hkDfs G adj mate dist f (i + 1) w₀ vis acc₀

theorem hkDfs_eq_dfsLevel {m r : ℕ} (G : Fin m × Fin r → Bool)
    (adj : Fin m → List (Fin r)) (mate : Vector (Option (Fin m)) r)
    (dist : Vector (Option ℕ) m) (f i : ℕ) (u : Fin m) (vis : Vector Bool r)
    (acc₀ : List (Fin m × Fin r)) :
    hkDfs G adj mate dist f i u vis acc₀ =
      hkDfsLevel G mate dist (decide (f = 0)) i
        (dfsNext G adj mate dist f i) u (adj u) vis acc₀ := by
  cases f <;> rfl

/-- `ps` has pairwise distinct right endpoints, each marked `true` in `vis`. -/
@[expose] def VisCovers {m r : ℕ} (vis : Vector Bool r) (ps : List (Fin m × Fin r)) : Prop :=
  (ps.map Prod.snd).Nodup ∧ ∀ e ∈ ps, vget vis e.2 = true

theorem VisCovers.mono {m r : ℕ} {vis vis' : Vector Bool r} {ps : List (Fin m × Fin r)}
    (h : VisCovers vis ps) (hle : ∀ x, vget vis x = true → vget vis' x = true) :
    VisCovers vis' ps :=
  ⟨h.1, fun e he => hle e.2 (h.2 e he)⟩

theorem VisCovers.snoc {m r : ℕ} {vis : Vector Bool r} {ps : List (Fin m × Fin r)}
    (h : VisCovers vis ps) (u : Fin m) {v : Fin r} (hv : vget vis v = false) :
    VisCovers (vset vis v true) (ps ++ [(u, v)]) := by
  have hv_not : v ∉ ps.map Prod.snd := by
    rw [List.mem_map]
    rintro ⟨e, he, rfl⟩
    exact Bool.false_ne_true (hv.symm.trans (h.2 e he))
  refine ⟨?_, fun e he => ?_⟩
  · rw [List.map_append, List.map_singleton, ← List.concat_eq_append]
    exact h.1.concat hv_not
  · rcases List.mem_append.mp he with he | he
    · have hne : e.2 ≠ v := fun heq => hv_not (heq ▸ List.mem_map_of_mem he)
      rw [vget_vset_ne _ _ hne.symm]
      exact h.2 e he
    · obtain rfl := List.mem_singleton.mp he
      exact vget_vset_self vis v true

theorem VisCovers.length_le {m r : ℕ} {vis : Vector Bool r} {ps : List (Fin m × Fin r)}
    (h : VisCovers vis ps) : ps.length ≤ r := by
  simpa using h.1.length_le_card

/-- Per-vertex instruction-potential weight assigned to an unvisited right vertex `v`. -/
@[expose] def dfsVertWeight (inst : SparseInstance) (mate : Vector (Option (Fin inst.m)) inst.r)
    (v : Fin inst.r) : ℕ :=
  38 * hkDfsCost inst.adj mate v + 14

/-- Remaining DFS work potential summed over unvisited (`false`) entries of `vis`. -/
@[expose] def dfsPot (inst : SparseInstance) (mate : Vector (Option (Fin inst.m)) inst.r)
    (vis : Vector Bool inst.r) : ℕ :=
  vecPotential (fun b : Bool => b = false) (dfsVertWeight inst mate) vis

theorem dfsPot_vset_true {inst : SparseInstance}
    {mate : Vector (Option (Fin inst.m)) inst.r} {vis : Vector Bool inst.r} {v : Fin inst.r}
    (hv : vget vis v = false) :
    dfsPot inst mate (vset vis v true) + dfsVertWeight inst mate v = dfsPot inst mate vis :=
  vecPotential_vset_add hv (by simp)

theorem dfsPot_replicate_le {inst : SparseInstance}
    {mate : Vector (Option (Fin inst.m)) inst.r}
    (hM : IsMatching inst.graph (mateMatching mate)) :
    dfsPot inst mate (Vector.replicate inst.r false) ≤ 38 * inst.numEdges + 14 * inst.r := by
  have hcost := vecPotential_replicate_le (adj := inst.adj) hM
  have h14 : (∑ _ ∈ Finset.univ.filter
      (fun v : Fin inst.r => vget (Vector.replicate inst.r false) v = false), 14) ≤
      14 * inst.r :=
    (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)).trans (by simp [Nat.mul_comm])
  simp only [vecPotential] at hcost
  simp only [dfsPot, vecPotential, dfsVertWeight, Finset.sum_add_distrib, ← Finset.mul_sum]
  change _ ≤ 38 * bipAdjSteps inst.adj + 14 * inst.r
  omega

theorem hkDfsLevel_pure_props {inst : SparseInstance}
    {mate : Vector (Option (Fin inst.m)) inst.r} {dist : Vector (Option ℕ) inst.m}
    (f d : ℕ)
    (hnext : ∀ (w₀ : Fin inst.m) (vis₀ : Vector Bool inst.r)
        (ps : List (Fin inst.m × Fin inst.r)),
      VisCovers vis₀ ps →
      (∀ x, vget vis₀ x = true →
        vget (dfsNext inst.graph inst.adj mate dist f d w₀ vis₀ []).1 x = true) ∧
      dfsPot inst mate (dfsNext inst.graph inst.adj mate dist f d w₀ vis₀ []).1 ≤
        dfsPot inst mate vis₀ ∧
      match (dfsNext inst.graph inst.adj mate dist f d w₀ vis₀ []).2 with
      | some qw =>
        VisCovers (dfsNext inst.graph inst.adj mate dist f d w₀ vis₀ []).1 (ps ++ qw) ∧
          qw.length = f
      | none =>
        VisCovers (dfsNext inst.graph inst.adj mate dist f d w₀ vis₀ []).1 ps)
    (u : Fin inst.m) (vs : List (Fin inst.r)) (vis : Vector Bool inst.r)
    (ps : List (Fin inst.m × Fin inst.r)) (hcovers : VisCovers vis ps) :
    (∀ x, vget vis x = true →
      vget (hkDfsLevel inst.graph mate dist (decide (f = 0)) d
        (dfsNext inst.graph inst.adj mate dist f d) u vs vis []).1 x = true) ∧
      dfsPot inst mate (hkDfsLevel inst.graph mate dist (decide (f = 0)) d
        (dfsNext inst.graph inst.adj mate dist f d) u vs vis []).1 ≤ dfsPot inst mate vis ∧
      match (hkDfsLevel inst.graph mate dist (decide (f = 0)) d
          (dfsNext inst.graph inst.adj mate dist f d) u vs vis []).2 with
      | some q =>
        VisCovers (hkDfsLevel inst.graph mate dist (decide (f = 0)) d
          (dfsNext inst.graph inst.adj mate dist f d) u vs vis []).1 (ps ++ q) ∧
          q.length = f + 1
      | none =>
        VisCovers (hkDfsLevel inst.graph mate dist (decide (f = 0)) d
          (dfsNext inst.graph inst.adj mate dist f d) u vs vis []).1 ps := by
  induction vs generalizing vis ps with
  | nil =>
    exact ⟨fun _ h => h, le_refl _, hcovers⟩
  | cons v vs ih =>
    dsimp only [hkDfsLevel]
    split
    · next hc =>
      have hpot_v := dfsPot_vset_true (inst := inst) (mate := mate) hc.2
      have hvset (x : Fin inst.r) (hx : vget vis x = true) : vget (vset vis v true) x = true := by
        rcases eq_or_ne x v with rfl | hne
        · exact vget_vset_self vis x true
        · rwa [vget_vset_ne _ _ hne.symm]
      cases hm : vget mate v with
      | none =>
        dsimp only
        split
        · next ha =>
          obtain rfl : f = 0 := of_decide_eq_true ha
          dsimp only
          exact ⟨hvset, by omega, hcovers.snoc u hc.2, rfl⟩
        · exact ih vis ps hcovers
      | some w₀ =>
        dsimp only
        split
        · next hb =>
          obtain ⟨hmono_w, hpot_w, hres_w⟩ :=
            hnext w₀ (vset vis v true) (ps ++ [(u, v)]) (hcovers.snoc u hc.2)
          have hmono_step (x : Fin inst.r) (hx : vget vis x = true) := hmono_w x (hvset x hx)
          cases hrw : (dfsNext inst.graph inst.adj mate dist f d w₀ (vset vis v true) []).2 with
          | some qw =>
            simp only [hrw] at hres_w ⊢
            exact ⟨hmono_step, by omega,
              by simpa [List.append_assoc] using hres_w.1,
              by simp only [List.length_cons, hres_w.2]⟩
          | none =>
            simp only [hrw] at hres_w ⊢
            obtain ⟨hm2, hp2, hr2⟩ := ih _ ps (hcovers.mono hmono_step)
            exact ⟨fun x hx => hm2 x (hmono_step x hx), by omega, hr2⟩
        · exact ih vis ps hcovers
    · exact ih vis ps hcovers

theorem hkDfs_pure_props {inst : SparseInstance}
    {mate : Vector (Option (Fin inst.m)) inst.r} {dist : Vector (Option ℕ) inst.m} :
    ∀ (f d : ℕ) (u : Fin inst.m) (vis : Vector Bool inst.r)
      (ps : List (Fin inst.m × Fin inst.r)),
      VisCovers vis ps →
      (∀ x, vget vis x = true →
        vget (hkDfs inst.graph inst.adj mate dist f d u vis []).1 x = true) ∧
        dfsPot inst mate (hkDfs inst.graph inst.adj mate dist f d u vis []).1 ≤
          dfsPot inst mate vis ∧
        match (hkDfs inst.graph inst.adj mate dist f d u vis []).2 with
        | some q =>
          VisCovers (hkDfs inst.graph inst.adj mate dist f d u vis []).1 (ps ++ q) ∧
            q.length = f + 1
        | none =>
          VisCovers (hkDfs inst.graph inst.adj mate dist f d u vis []).1 ps
  | 0, d, u, vis, ps, hcovers => by
    rw [hkDfs_eq_dfsLevel]
    exact hkDfsLevel_pure_props 0 d (fun _ vis₀ ps₀ hc => ⟨fun _ h => h, le_refl _, hc⟩)
      u (inst.adj u) vis ps hcovers
  | f + 1, d, u, vis, ps, hcovers => by
    rw [hkDfs_eq_dfsLevel]
    exact hkDfsLevel_pure_props (f + 1) d (hkDfs_pure_props f (d + 1)) u (inst.adj u) vis ps hcovers

theorem hkDfsRoots_nodup_snd {inst : SparseInstance}
    (mate : Vector (Option (Fin inst.m)) inst.r) (dist : Vector (Option ℕ) inst.m) (k : ℕ) :
    ∀ (us : List (Fin inst.m)) (vis : Vector Bool inst.r)
      (acc₀ : List (Fin inst.m × Fin inst.r)),
      VisCovers vis acc₀ →
      ((hkDfsRoots inst.graph inst.adj mate dist k us vis acc₀).map Prod.snd).Nodup := by
  intro us vis acc₀ hc
  induction us generalizing vis acc₀ with
  | nil => exact hc.1
  | cons u us ih =>
    simp only [hkDfsRoots]
    split_ifs with hd
    · rw [hkDfs_acc]
      obtain ⟨_, _, hres⟩ := hkDfs_pure_props (inst := inst) (mate := mate) (dist := dist)
        k 0 u vis acc₀ hc
      cases hr : (hkDfs inst.graph inst.adj mate dist k 0 u vis []).2 with
      | none => exact ih _ acc₀ (by simpa only [hr] using hres)
      | some q =>
        rw [hr] at hres
        have hperm : (q ++ acc₀).Perm (acc₀ ++ q) := List.perm_append_comm
        exact ih _ (q ++ acc₀)
          ⟨(hperm.map Prod.snd).nodup_iff.mpr hres.1.1, fun e he => hres.1.2 e (hperm.subset he)⟩
    · exact ih vis acc₀ hc

/-! ## DFS memory predicates and `copyAugCode` -/

/-- In-memory DFS visited-flag table `vis[0..r)` starting at `bVis`. -/
@[expose] def VisMem (inst : SparseInstance) (bOff : ℕ) (vis : Vector Bool inst.r)
    (mem : ℕ → ℕ) : Prop :=
  ∀ v : Fin inst.r,
    mem (bOff + inst.m + 1 + inst.numEdges + inst.r + 3 * inst.m + v.val) =
      if vget vis v = true then 1 else 0

theorem VisMem.of_outside {inst : SparseInstance} {bOff : ℕ}
    {vis : Vector Bool inst.r} {mem mem' : ℕ → ℕ}
    (h : VisMem inst bOff vis mem)
    (hf : ∀ a, bOff + inst.m + 1 + inst.numEdges + inst.r + 3 * inst.m ≤ a ∧
        a < bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 3 * inst.m → mem' a = mem a) :
    VisMem inst bOff vis mem' :=
  fun v => (hf _ ⟨by omega, by have := v.isLt; omega⟩).trans (h v)

theorem VisMem.vset_true {inst : SparseInstance} {bOff : ℕ}
    {vis : Vector Bool inst.r} {mem mem' : ℕ → ℕ}
    (h : VisMem inst bOff vis mem) (v : Fin inst.r)
    (hself : mem' (bOff + inst.m + 1 + inst.numEdges + inst.r + 3 * inst.m + v.val) = 1)
    (hother : ∀ v₀ : Fin inst.r, v₀ ≠ v →
      mem' (bOff + inst.m + 1 + inst.numEdges + inst.r + 3 * inst.m + v₀.val) =
        mem (bOff + inst.m + 1 + inst.numEdges + inst.r + 3 * inst.m + v₀.val)) :
    VisMem inst bOff (vset vis v true) mem' := by
  intro v₀
  rcases eq_or_ne v₀ v with rfl | hne
  · simpa using hself
  · rw [hother v₀ hne, vget_vset_ne _ _ hne.symm]
    exact h v₀

private theorem VisMem.mem_eq_zero {inst : SparseInstance} {bOff : ℕ}
    {vis : Vector Bool inst.r} {mem : ℕ → ℕ} (h : VisMem inst bOff vis mem) {v : Fin inst.r}
    (hvv : vget vis v = false) :
    mem (bOff + inst.m + 1 + inst.numEdges + inst.r + 3 * inst.m + v.val) = 0 := by
  rw [h v, ite_eq_right (by simp [hvv])]

/-- In-memory phase rematch pairs `augU[0..ps.length)` and `augV[0..ps.length)`. -/
@[expose] def AugMem (inst : SparseInstance) (bOff : ℕ) (ps : List (Fin inst.m × Fin inst.r))
    (mem : ℕ → ℕ) : Prop :=
  ∀ i : ℕ, (hi : i < ps.length) →
    mem (bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 6 * inst.m + 6 + i) = (ps[i]'hi).1.val ∧
    mem (bOff + inst.m + 1 + inst.numEdges + 3 * inst.r + 6 * inst.m + 6 + i) = (ps[i]'hi).2.val

theorem AugMem.of_outside {inst : SparseInstance} {bOff : ℕ}
    {ps : List (Fin inst.m × Fin inst.r)} {mem mem' : ℕ → ℕ}
    (h : AugMem inst bOff ps mem) (hlen : ps.length ≤ inst.r)
    (hf : ∀ a, bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 6 * inst.m + 6 ≤ a ∧
        a < bOff + inst.m + 1 + inst.numEdges + 4 * inst.r + 6 * inst.m + 6 → mem' a = mem a) :
    AugMem inst bOff ps mem' :=
  fun i hi =>
    ⟨(hf _ ⟨by omega, by omega⟩).trans (h i hi).1, (hf _ ⟨by omega, by omega⟩).trans (h i hi).2⟩

private def copyAugBody : Code .standard 34 := ram[
  addr ← bStackUReg + idx; val ← *addr;
  addr ← bAugUReg + augLen; *addr ← val;
  addr ← bStackVReg + idx; val ← *addr;
  addr ← bAugVReg + augLen; *addr ← val;
  augLen ← augLen + one;
  idx ← idx + one ]

private def copyAugCode : Code .standard 34 :=
  .seq (ram[ limit ← rk + one; idx ← #0 ])
    (.loop (.lt idx limit) copyAugBody)

private theorem exec_copyAugCode {w bOff k : ℕ} {inst : SparseInstance}
    (augPairs stackPairs : List (Fin inst.m × Fin inst.r))
    (x : Data 34) (hb : BaseRegs inst bOff x)
    (hrk : x.regs rk = k)
    (haugLen : x.regs augLen = augPairs.length)
    (hact : x.regs active = 1)
    (hlen_st : stackPairs.length = k + 1)
    (hk_le : k ≤ inst.m + 1)
    (haug_fit : augPairs.length + (k + 1) ≤ inst.r)
    (haugM : AugMem inst bOff augPairs x.mem)
    (hstackM : ∀ i : ℕ, (hi : i < k + 1) →
      x.mem (bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 3 * inst.m + i) =
        (stackPairs[i]'(by omega)).1.val ∧
      x.mem (bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 4 * inst.m + 2 + i) =
        (stackPairs[i]'(by omega)).2.val)
    (hfit : Fits w (bOff + 7 * inst.m + 5 * inst.r + inst.numEdges + 8)) :
    ∃ y, ExecWithin w copyAugCode x y (12 * (k + 1) + 4) ∧
      (∀ i : Fin 34, i.val < 26 → y.regs i = x.regs i) ∧
      y.regs active = 1 ∧
      y.regs augLen = (augPairs ++ stackPairs).length ∧
      AugMem inst bOff (augPairs ++ stackPairs) y.mem ∧
      (∀ a, ¬(bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 6 * inst.m + 6 ≤ a ∧
          a < bOff + inst.m + 1 + inst.numEdges + 4 * inst.r + 6 * inst.m + 6) →
        y.mem a = x.mem a) := by
  obtain ⟨s₀, he₀, rfl⟩ : ∃ s₀, ExecWithin w
      (ram[ limit ← rk + one; idx ← #0 ] : Code .standard 34) x s₀ 2 ∧
      s₀ = (x.set limit (k + 1)).set idx 0 := by
    refine WP.exists_execWithin ?_
    wram_exec [hrk, hb.hone]
    rfl
  let P (t : ℕ) (y : Data 34) : Prop :=
    t ≤ k + 1 ∧
      (∀ i : Fin 34, i.val < 26 → y.regs i = x.regs i) ∧
      y.regs active = 1 ∧
      y.regs limit = k + 1 ∧
      y.regs augLen = augPairs.length + t ∧
      AugMem inst bOff (augPairs ++ stackPairs.take t) y.mem ∧
      (∀ a, ¬(bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 6 * inst.m + 6 ≤ a ∧
          a < bOff + inst.m + 1 + inst.numEdges + 4 * inst.r + 6 * inst.m + 6) →
        y.mem a = x.mem a)
  have hP₀ : P 0 ((x.set limit (k + 1)).set idx 0) := by
    refine ⟨Nat.zero_le _, fun i hi => by wram_simp, by wram_simp [hact], by wram_simp,
      by wram_simp [haugLen], ?_, fun _ _ => rfl⟩
    simpa using haugM
  have hbody (y : Data 34) (hy : P (y.regs idx) y) (hlt : y.regs idx < k + 1) :
      ∃ z, ExecWithin w copyAugBody y z 10 ∧ P (y.regs idx + 1) z ∧
        z.regs idx = y.regs idx + 1 := by
    obtain ⟨_, hr, hact_y, hlim_y, hal_y, haug_y, hf_y⟩ := hy
    have hby : BaseRegs inst bOff y := hb.of_eq fun i hi => hr i (by omega)
    have hlt_st : y.regs idx < stackPairs.length := by omega
    have hsu : y.mem (bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 3 * inst.m + y.regs idx) =
        (stackPairs[y.regs idx]'hlt_st).1.val :=
      (hf_y _ (by omega)).trans (hstackM (y.regs idx) hlt).1
    have hsv :
        y.mem (bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 4 * inst.m + 2 + y.regs idx) =
          (stackPairs[y.regs idx]'hlt_st).2.val :=
      (hf_y _ (by omega)).trans (hstackM (y.regs idx) hlt).2
    refine WP.exists_execWithin ?_
    wram_exec [copyAugBody,
      hby.hbStackU, hby.hbAugU, hby.hbStackV, hby.hbAugV, hby.hone, hal_y, hsu, hsv]
    have htake_eq : augPairs ++ stackPairs.take (y.regs idx + 1) =
        (augPairs ++ stackPairs.take (y.regs idx)) ++ [stackPairs[y.regs idx]'hlt_st] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hlt_st, Option.toList_some,
        ← List.append_assoc]
    refine ⟨⟨by omega,
      fun i hi => by wram_simp [hr i hi],
      by wram_simp [hact_y],
      by wram_simp [hlim_y],
      by wram_simp [hal_y, Nat.add_assoc],
      ?_,
      fun a ha => by wram_simp [hf_y a ha]⟩,
      by wram_simp⟩
    intro i hi
    have hlen_old : (augPairs ++ stackPairs.take (y.regs idx)).length =
        augPairs.length + y.regs idx := by
      rw [List.length_append, List.length_take_of_le (by omega)]
    by_cases hlt_i : i < augPairs.length + y.regs idx
    · simp only [htake_eq, List.getElem_append_left (hlen_old.symm ▸ hlt_i)]
      wram_simp
      exact haug_y i (hlen_old.symm ▸ hlt_i)
    · have hi_lt : i < augPairs.length + y.regs idx + 1 := by
        rwa [htake_eq, List.length_append, List.length_singleton, hlen_old] at hi
      obtain rfl : i = augPairs.length + y.regs idx := by omega
      simp only [htake_eq, List.getElem_append_right (le_of_eq hlen_old), hlen_old, Nat.sub_self,
        List.getElem_singleton]
      wram_simp
  obtain ⟨y, hl, hPend, _⟩ := ExecWithin.loop_count P (fun y hy => hy.2.2.2.1) hbody
    (x := (x.set limit (k + 1)).set idx 0) (by simp) (by simpa using hP₀)
  obtain ⟨_, hr, hact', _, hal', haug', hf'⟩ := hPend
  rw [List.take_of_length_le (by omega)] at haug'
  refine ⟨y, (he₀.seq hl).mono (by simp; omega), hr, hact',
    by rw [List.length_append, hlen_st]; exact hal', haug', hf'⟩

/-! ## Explicit-stack DFS step and frame invariant -/

/-- Single explicit-stack DFS loop body advancing or backtracking one stack frame. -/
def dfsStepBody : Code .standard 34 := ram[
  addr ← bStackUReg + rd; idx ← *addr;
  addr ← bOffReg + idx; addr ← addr + one; limit ← *addr;
  addr ← bStackPosReg + rd; val2 ← *addr;
  if val2 < limit then [
    tmp ← val2 + one;
    addr ← bStackPosReg + rd; *addr ← tmp;
    addr ← bEdgesReg + val2; val ← *addr;
    addr ← bVisReg + val; tmp ← *addr;
    if tmp = zero then [
      addr ← bColMateReg + val; val2 ← *addr;
      if val2 = rm then [
        if rd = rk then [
          addr ← bVisReg + val; *addr ← one;
          addr ← bStackVReg + rd; *addr ← val;
          ⟪copyAugCode⟫;
          active ← zero
        ] else [ tmp ← zero ]
      ] else [
        if rd < rk then [
          addr ← bDistReg + val2; tmp ← *addr;
          idx ← rd + two;
          if tmp = idx then [
            addr ← bVisReg + val; *addr ← one;
            addr ← bStackVReg + rd; *addr ← val;
            rd ← rd + one;
            addr ← bStackUReg + rd; *addr ← val2;
            addr ← bOffReg + val2; tmp ← *addr;
            addr ← bStackPosReg + rd; *addr ← tmp
          ] else [ tmp ← zero ]
        ] else [ tmp ← zero ]
      ]
    ] else [ tmp ← zero ]
  ] else [
    if rd = zero then [ active ← zero ] else [ rd ← rd - one ]
  ] ]

/-- Explicit-stack DFS iteration loop running `dfsStepBody` while `active = 1`. -/
@[expose] def dfsLoop : Code .standard 34 :=
  .loop (.eq active one) dfsStepBody

/-- Bundled state invariant at stack depth `d` during `dfsLoop`. -/
structure DfsFrame (inst : SparseInstance) (bOff k : ℕ)
    (mate : Vector (Option (Fin inst.m)) inst.r) (dist : Vector (Option ℕ) inst.m)
    (augPairs : List (Fin inst.m × Fin inst.r)) (d : ℕ)
    (path : List (Fin inst.m × Fin inst.r)) (u : Fin inst.m) (pre : List (Fin inst.r))
    (vis : Vector Bool inst.r) (x : Data 34) : Prop where
  hplen : path.length = d
  hcovers : VisCovers vis (augPairs ++ path)
  hb : BaseRegs inst bOff x
  hcsr : CSRMem inst bOff x.mem
  hmate : MateMem inst bOff mate x.mem
  hdM : DistMem inst bOff dist x.mem
  hvisM : VisMem inst bOff vis x.mem
  haugM : AugMem inst bOff augPairs x.mem
  hstack : ∀ i : ℕ, (hi : i < d) →
    x.mem (bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 3 * inst.m + i) =
      (path[i]'(by omega)).1.val ∧
    x.mem (bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 4 * inst.m + 2 + i) =
      (path[i]'(by omega)).2.val
  hsu : x.mem (bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 3 * inst.m + d) = u.val
  hsp : x.mem (bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 5 * inst.m + 4 + d) =
    inst.offset u.val + pre.length
  hrk : x.regs rk = k
  hrd : x.regs rd = d
  hal : x.regs augLen = augPairs.length
  hact : x.regs active = 1

/-- Address `a` lies outside `vis` and the active DFS stack frames above depth `d`. -/
@[expose] def DfsSubtreeOutside (inst : SparseInstance) (bOff d a : ℕ) : Prop :=
  ¬(bOff + inst.m + 1 + inst.numEdges + inst.r + 3 * inst.m ≤ a ∧
      a < bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 3 * inst.m) ∧
    ¬(bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 3 * inst.m + (d + 1) ≤ a ∧
      a < bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 4 * inst.m + 2) ∧
    ¬(bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 4 * inst.m + 2 + d ≤ a ∧
      a < bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 5 * inst.m + 4) ∧
    ¬(bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 5 * inst.m + 4 + d ≤ a ∧
      a < bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 6 * inst.m + 6)

private theorem stack_snoc {inst : SparseInstance} {bOff d : ℕ}
    {path : List (Fin inst.m × Fin inst.r)} {u : Fin inst.m} {v : Fin inst.r}
    {mem mem' : ℕ → ℕ} (hplen : path.length = d)
    (hstack : ∀ i : ℕ, (hi : i < d) →
      mem (bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 3 * inst.m + i) =
        (path[i]'(by omega)).1.val ∧
      mem (bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 4 * inst.m + 2 + i) =
        (path[i]'(by omega)).2.val)
    (hsu : mem (bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 3 * inst.m + d) = u.val)
    (hkeep_u : ∀ i ≤ d,
      mem' (bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 3 * inst.m + i) =
        mem (bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 3 * inst.m + i))
    (hkeep_v : ∀ i < d,
      mem' (bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 4 * inst.m + 2 + i) =
        mem (bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 4 * inst.m + 2 + i))
    (hset_v :
      mem' (bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 4 * inst.m + 2 + d) = v.val) :
    ∀ i : ℕ, (hi : i < d + 1) →
      mem' (bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 3 * inst.m + i) =
        ((path ++ [(u, v)])[i]'(by simp [hplen]; omega)).1.val ∧
      mem' (bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 4 * inst.m + 2 + i) =
        ((path ++ [(u, v)])[i]'(by simp [hplen]; omega)).2.val := by
  intro i hi
  by_cases hlt : i < d
  · rw [List.getElem_append_left (by omega), hkeep_u i hlt.le, hkeep_v i hlt]
    exact hstack i hlt
  · obtain rfl : i = d := by omega
    rw [List.getElem_append_right (by omega), hkeep_u _ le_rfl, hsu, hset_v]
    simp [hplen]

theorem exec_dfsStep_pop {w bOff k d : ℕ} {inst : SparseInstance}
    {mate : Vector (Option (Fin inst.m)) inst.r} {dist : Vector (Option ℕ) inst.m}
    {augPairs path : List (Fin inst.m × Fin inst.r)} {u : Fin inst.m} {pre : List (Fin inst.r)}
    {vis : Vector Bool inst.r} {x : Data 34}
    (hd_le : d ≤ k) (hk_le : k ≤ inst.m + 1)
    (hsplit : inst.adj u = pre)
    (hfr : DfsFrame inst bOff k mate dist augPairs d path u pre vis x)
    (hfit : Fits w (bOff + 7 * inst.m + 5 * inst.r + inst.numEdges + 8)) :
    ∃ y, ExecWithin w dfsStepBody x y 12 ∧
      (∀ i : Fin 34, i.val < 25 → y.regs i = x.regs i) ∧
      y.regs augLen = augPairs.length ∧
      (if d = 0 then y.regs active = 0 else y.regs active = 1 ∧ y.regs rd = d - 1) ∧
      y.mem = x.mem := by
  have hu_lt := u.isLt
  have hoff_succ : inst.offset (u.val + 1) = inst.offset u.val + (inst.adj u).length :=
    inst.offset_succ hu_lt
  have hpre_len : pre.length = (inst.adj u).length := by rw [hsplit]
  have hoff_u1 : x.mem (bOff + u.val + 1) = inst.offset (u.val + 1) := by
    simpa [Nat.add_assoc] using hfr.hcsr.hoff hu_lt
  have hnl : ¬inst.offset u.val + pre.length < inst.offset (u.val + 1) := by omega
  refine WP.exists_execWithin ?_
  unfold dfsStepBody
  by_cases hd0 : d = 0
  · subst hd0
    have hsu0 : x.mem (bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 3 * inst.m) = u.val := by
      simpa using hfr.hsu
    have hsp0 : x.mem (bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 5 * inst.m + 4) =
        inst.offset u.val + pre.length := by
      simpa using hfr.hsp
    wram_exec [hfr.hb.hbStackU, hfr.hb.hbOff, hfr.hb.hbStackPos, hfr.hb.hone, hfr.hb.hzero,
      hfr.hrd, hsu0, hoff_u1, hsp0, hnl]
    exact ⟨fun i hi => by wram_simp, by wram_simp [hfr.hal], by wram_simp, rfl⟩
  · wram_exec [hfr.hb.hbStackU, hfr.hb.hbOff, hfr.hb.hbStackPos, hfr.hb.hone, hfr.hb.hzero,
      hfr.hrd, hfr.hsu, hoff_u1, hfr.hsp, hnl, hd0]
    exact ⟨fun i hi => by wram_simp, by wram_simp [hfr.hal],
      by rw [ite_eq_right hd0]; exact ⟨by wram_simp [hfr.hact], by wram_simp⟩, rfl⟩

private theorem DfsFrame.edge_facts {bOff k d : ℕ} {inst : SparseInstance}
    {mate : Vector (Option (Fin inst.m)) inst.r} {dist : Vector (Option ℕ) inst.m}
    {augPairs path : List (Fin inst.m × Fin inst.r)} {u : Fin inst.m}
    {pre vs : List (Fin inst.r)} {v : Fin inst.r} {vis : Vector Bool inst.r} {x : Data 34}
    (hsplit : inst.adj u = pre ++ v :: vs)
    (hfr : DfsFrame inst bOff k mate dist augPairs d path u pre vis x) :
    inst.offset (u.val + 1) = inst.offset u.val + (inst.adj u).length ∧
      inst.offset u.val + pre.length < inst.numEdges ∧
      inst.offset u.val + pre.length < inst.offset (u.val + 1) ∧
      x.mem (bOff + inst.m + 1 + (inst.offset u.val + pre.length)) = v.val ∧
      x.mem (bOff + u.val + 1) = inst.offset (u.val + 1) := by
  have hoff_succ : inst.offset (u.val + 1) = inst.offset u.val + (inst.adj u).length := by
    simpa using inst.offset_succ u.isLt
  have hpre_lt : pre.length < (inst.adj u).length := by
    rw [hsplit, List.length_append, List.length_cons]; omega
  have hadj_get : (inst.adj u)[pre.length]'hpre_lt = v := by simp [hsplit]
  exact ⟨hoff_succ, inst.offset_add_lt_numEdges u hpre_lt, by omega,
    by rw [hfr.hcsr.hedge u hpre_lt, hadj_get],
    by simpa [Nat.add_assoc] using hfr.hcsr.hoff u.isLt⟩

theorem exec_dfsStep_skip {w bOff k d : ℕ} {inst : SparseInstance}
    {mate : Vector (Option (Fin inst.m)) inst.r} {dist : Vector (Option ℕ) inst.m}
    {augPairs path : List (Fin inst.m × Fin inst.r)} {u : Fin inst.m}
    {pre vs : List (Fin inst.r)} {v : Fin inst.r}
    {vis : Vector Bool inst.r} {x : Data 34}
    (hd_le : d ≤ k) (hk_le : k ≤ inst.m + 1)
    (hsplit : inst.adj u = pre ++ v :: vs)
    (hfr : DfsFrame inst bOff k mate dist augPairs d path u pre vis x)
    (hcond : vget vis v = true ∨
      (vget vis v = false ∧ vget mate v = none ∧ d ≠ k) ∨
      (vget vis v = false ∧ ∃ w₀, vget mate v = some w₀ ∧
        ¬(d < k ∧ vget dist w₀ = some (d + 1))))
    (hfit : Fits w (bOff + 7 * inst.m + 5 * inst.r + inst.numEdges + 8)) :
    ∃ x₁, ExecWithin w dfsStepBody x x₁ 27 ∧
      (∀ i : Fin 34, i.val < 25 → x₁.regs i = x.regs i) ∧
      DfsFrame inst bOff k mate dist augPairs d path u (pre ++ [v]) vis x₁ ∧
      (∀ a, DfsSubtreeOutside inst bOff d a → x₁.mem a = x.mem a) ∧
      (∀ a, ¬(bOff + inst.m + 1 + inst.numEdges + inst.r + 3 * inst.m ≤ a ∧
          a < bOff + inst.m + 1 + inst.numEdges + 4 * inst.r + 6 * inst.m + 6) →
        x₁.mem a = x.mem a) := by
  have hu_lt := u.isLt
  have hv_lt := v.isLt
  obtain ⟨hoff_succ, hed_lt, hlt_lim, hedge_v, hoff_u1⟩ := hfr.edge_facts hsplit
  have hraw : ∃ x₁, ExecWithin w dfsStepBody x x₁ 27 ∧
      (∀ i : Fin 34, i.val < 25 → x₁.regs i = x.regs i) ∧
      x₁.regs rd = d ∧ x₁.regs augLen = augPairs.length ∧ x₁.regs active = 1 ∧
      x₁.mem = Function.update x.mem
        (bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 5 * inst.m + 4 + d)
        (inst.offset u.val + pre.length + 1) := by
    refine WP.exists_execWithin ?_
    unfold dfsStepBody
    by_cases hvv_t : vget vis v = true
    · have hvis_v :
          x.mem (bOff + inst.m + 1 + inst.numEdges + inst.r + 3 * inst.m + v.val) = 1 := by
        rw [hfr.hvisM v, ite_eq_left hvv_t]
      wram_exec [hfr.hb.hbStackU, hfr.hb.hbOff, hfr.hb.hbStackPos, hfr.hb.hbEdges,
        hfr.hb.hbVis, hfr.hb.hone, hfr.hb.hzero, hfr.hrd, hfr.hsu, hoff_u1, hfr.hsp,
        hlt_lim, hedge_v, hvis_v]
      exact ⟨fun i hi => by wram_simp, by wram_simp [hfr.hrd], by wram_simp [hfr.hal],
        by wram_simp [hfr.hact], rfl⟩
    · have hvv_f : vget vis v = false := Bool.eq_false_iff.mpr hvv_t
      have hvis_v := hfr.hvisM.mem_eq_zero hvv_f
      have hmate_v := hfr.hmate v
      rcases hcond with h | ⟨_, hmv, hd_ne⟩ | ⟨_, w₀, hmv, hnot⟩
      · exact absurd h hvv_t
      · have henc_m : encodeOptFin (vget mate v) = inst.m := by simp [hmv, encodeOptFin]
        wram_exec [hfr.hb.hbStackU, hfr.hb.hbOff, hfr.hb.hbStackPos, hfr.hb.hbEdges,
          hfr.hb.hbVis, hfr.hb.hbColMate, hfr.hb.hrm, hfr.hb.hone, hfr.hb.hzero,
          hfr.hrd, hfr.hrk, hd_ne, hfr.hsu, hoff_u1, hfr.hsp, hlt_lim, hedge_v, hvis_v,
          hmate_v, henc_m]
        exact ⟨fun i hi => by wram_simp, by wram_simp [hfr.hrd], by wram_simp [hfr.hal],
          by wram_simp [hfr.hact], rfl⟩
      · have hw_lt := w₀.isLt
        have henc_m : encodeOptFin (vget mate v) = w₀.val := by simp [hmv, encodeOptFin]
        have hw_ne : w₀.val ≠ inst.m := ne_of_lt hw_lt
        by_cases hd_lt : d < k
        · have hdw : vget dist w₀ ≠ some (d + 1) := fun h => hnot ⟨hd_lt, h⟩
          have hdist_w := hfr.hdM w₀
          have henc_ne : encodeDist (vget dist w₀) ≠ d + 2 := by
            cases h : vget dist w₀ with
            | none => simp [encodeDist]
            | some j =>
              simp only [encodeDist]
              intro heq
              exact hdw (by rw [h]; congr 1; omega)
          wram_exec [hfr.hb.hbStackU, hfr.hb.hbOff, hfr.hb.hbStackPos, hfr.hb.hbEdges,
            hfr.hb.hbVis, hfr.hb.hbColMate, hfr.hb.hbDist, hfr.hb.hrm, hfr.hb.hone,
            hfr.hb.hzero, hfr.hb.htwo, hfr.hrd, hfr.hrk, hd_lt, hfr.hsu, hoff_u1, hfr.hsp,
            hlt_lim, hedge_v, hvis_v, hmate_v, henc_m, hw_ne, hdist_w, henc_ne]
          exact ⟨fun i hi => by wram_simp, by wram_simp [hfr.hrd], by wram_simp [hfr.hal],
            by wram_simp [hfr.hact], rfl⟩
        · wram_exec [hfr.hb.hbStackU, hfr.hb.hbOff, hfr.hb.hbStackPos, hfr.hb.hbEdges,
            hfr.hb.hbVis, hfr.hb.hbColMate, hfr.hb.hrm, hfr.hb.hone, hfr.hb.hzero,
            hfr.hrd, hfr.hrk, hd_lt, hfr.hsu, hoff_u1, hfr.hsp, hlt_lim, hedge_v, hvis_v,
            hmate_v, henc_m, hw_ne]
          exact ⟨fun i hi => by wram_simp, by wram_simp [hfr.hrd], by wram_simp [hfr.hal],
            by wram_simp [hfr.hact], rfl⟩
  obtain ⟨x₁, he_skip, hr₁, hrd₁, hal₁, hact₁, hmem₁⟩ := hraw
  have haug_le : augPairs.length ≤ inst.r :=
    (List.sublist_append_left augPairs path).length_le.trans hfr.hcovers.length_le
  have hout (a : ℕ)
      (hne : a ≠ bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 5 * inst.m + 4 + d) :
      x₁.mem a = x.mem a := by rw [hmem₁, Function.update_of_ne hne]
  refine ⟨x₁, he_skip, hr₁,
    { hplen := hfr.hplen
      hcovers := hfr.hcovers
      hb := hfr.hb.of_eq fun i hi => hr₁ i (by omega)
      hcsr := hfr.hcsr.of_outside fun _ _ => hout _ (by omega)
      hmate := hfr.hmate.of_outside fun _ _ => hout _ (by omega)
      hdM := hfr.hdM.of_outside fun _ _ => hout _ (by omega)
      hvisM := hfr.hvisM.of_outside fun _ _ => hout _ (by omega)
      haugM := hfr.haugM.of_outside haug_le fun _ _ => hout _ (by omega)
      hstack := fun i hi => by
        rw [hout _ (by omega), hout _ (by omega)]
        exact hfr.hstack i hi
      hsu := (hout _ (by omega)).trans hfr.hsu
      hsp := by rw [hmem₁, Function.update_self]; simp [Nat.add_assoc]
      hrk := (hr₁ rk (by decide)).trans hfr.hrk
      hrd := hrd₁
      hal := hal₁
      hact := hact₁ },
    fun a ha => hout a (by simp only [DfsSubtreeOutside] at ha; omega),
    fun a _ => hout a (by omega)⟩

theorem exec_dfsStep_accept {w bOff k : ℕ} {inst : SparseInstance}
    {mate : Vector (Option (Fin inst.m)) inst.r} {dist : Vector (Option ℕ) inst.m}
    {augPairs path : List (Fin inst.m × Fin inst.r)} {u : Fin inst.m}
    {pre vs : List (Fin inst.r)} {v : Fin inst.r}
    {vis : Vector Bool inst.r} {x : Data 34}
    (hk_le : k ≤ inst.m + 1)
    (hsplit : inst.adj u = pre ++ v :: vs)
    (hfr : DfsFrame inst bOff k mate dist augPairs k path u pre vis x)
    (hvv : vget vis v = false) (hmv : vget mate v = none)
    (hfit : Fits w (bOff + 7 * inst.m + 5 * inst.r + inst.numEdges + 8)) :
    ∃ z, ExecWithin w dfsLoop x z (12 * (k + 1) + 33) ∧
      (∀ i : Fin 34, i.val < 25 → z.regs i = x.regs i) ∧
      z.regs augLen = (augPairs ++ (path ++ [(u, v)])).length ∧
      VisMem inst bOff (vset vis v true) z.mem ∧
      AugMem inst bOff (augPairs ++ (path ++ [(u, v)])) z.mem ∧
      (∀ a, ¬(bOff + inst.m + 1 + inst.numEdges + inst.r + 3 * inst.m ≤ a ∧
          a < bOff + inst.m + 1 + inst.numEdges + 4 * inst.r + 6 * inst.m + 6) →
        z.mem a = x.mem a) := by
  have hu_lt := u.isLt
  have hv_lt := v.isLt
  obtain ⟨hoff_succ, hed_lt, hlt_lim, hedge_v, hoff_u1⟩ := hfr.edge_facts hsplit
  have hc_loop : (Cond.eq active one).Holds x := by
    rw [Cond.holds_eq, hfr.hact, hfr.hb.hone]
  have hvis_v := hfr.hvisM.mem_eq_zero hvv
  have hmate_v := hfr.hmate v
  have henc_m : encodeOptFin (vget mate v) = inst.m := by simp [hmv, encodeOptFin]
  have hplen := hfr.hplen
  have hcov_acc : VisCovers (vset vis v true) ((augPairs ++ path) ++ [(u, v)]) :=
    hfr.hcovers.snoc u hvv
  have haug_fit : augPairs.length + (k + 1) ≤ inst.r := by
    have := hcov_acc.length_le
    simp only [List.length_append, List.length_singleton, hplen] at this
    omega
  have hstep : ∃ z, ExecWithin w dfsStepBody x z (12 * (k + 1) + 29) ∧
      (∀ i : Fin 34, i.val < 25 → z.regs i = x.regs i) ∧
      z.regs active = 0 ∧
      z.regs augLen = (augPairs ++ (path ++ [(u, v)])).length ∧
      VisMem inst bOff (vset vis v true) z.mem ∧
      AugMem inst bOff (augPairs ++ (path ++ [(u, v)])) z.mem ∧
      (∀ a, ¬(bOff + inst.m + 1 + inst.numEdges + inst.r + 3 * inst.m ≤ a ∧
          a < bOff + inst.m + 1 + inst.numEdges + 4 * inst.r + 6 * inst.m + 6) →
        z.mem a = x.mem a) := by
    refine WP.exists_execWithin ?_
    wram_exec [dfsStepBody, hfr.hb.hbStackU, hfr.hb.hbOff, hfr.hb.hbStackPos, hfr.hb.hbEdges,
      hfr.hb.hbVis, hfr.hb.hbColMate, hfr.hb.hbStackV, hfr.hb.hrm, hfr.hb.hone, hfr.hb.hzero,
      hfr.hrd, hfr.hrk, hfr.hsu, hoff_u1, hfr.hsp, hlt_lim, hedge_v, hvis_v, hmate_v, henc_m]
    refine WP.name fun x_mid hx_mid => ?_
    have hb_mid : BaseRegs inst bOff x_mid :=
      hfr.hb.of_eq fun i hi => by subst hx_mid; wram_simp
    have hrk_mid : x_mid.regs rk = k := by subst hx_mid; wram_simp [hfr.hrk]
    have hal_mid : x_mid.regs augLen = augPairs.length := by subst hx_mid; wram_simp [hfr.hal]
    have hact_mid : x_mid.regs active = 1 := by subst hx_mid; wram_simp [hfr.hact]
    have haug_mid : AugMem inst bOff augPairs x_mid.mem :=
      hfr.haugM.of_outside (by omega) fun a ha => by subst hx_mid; wram_simp
    have hstack_mid := stack_snoc (inst := inst) (bOff := bOff) (d := k) (u := u) (v := v)
      (mem' := x_mid.mem) hplen hfr.hstack hfr.hsu
      (fun i hi => by subst hx_mid; wram_simp)
      (fun i hi => by subst hx_mid; wram_simp)
      (by subst hx_mid; wram_simp)
    obtain ⟨y_cp, he_cp, hr_cp, hact_cp, hal_cp, haug_cp, hf_cp⟩ :=
      exec_copyAugCode augPairs (path ++ [(u, v)]) x_mid hb_mid hrk_mid hal_mid
        hact_mid (by simp [hplen]) hk_le haug_fit haug_mid hstack_mid hfit
    refine WP.of_execWithin he_cp ?_
    have hz_mid : y_cp.regs zero = 0 := (hr_cp zero (by decide)).trans hb_mid.hzero
    wram_exec [hz_mid]
    subst hx_mid
    refine ⟨fun i hi => ?_, by wram_simp, by wram_simp [hal_cp], ?_, haug_cp, fun a ha => ?_⟩
    · have hrcp := hr_cp i (by omega)
      wram_simp [hrcp]
    · refine hfr.hvisM.vset_true v ?_ fun v₀ hne => ?_
      · rw [Data.set_mem, hf_cp _ (by omega)]
        wram_simp
      · have := v₀.isLt
        have hne_val : v₀.val ≠ v.val := fun h => hne (Fin.ext h)
        rw [Data.set_mem, hf_cp _ (by omega)]
        wram_simp
    · rw [Data.set_mem, hf_cp a (by omega)]
      wram_simp
  obtain ⟨z, he_step, hr_z, hact_z, hal_z, hvis_z, haug_z, hf_z⟩ := hstep
  have hc_exit : ¬(Cond.eq active one).Holds z := by
    rw [Cond.holds_eq, hact_z, (hr_z one (by decide)).trans hfr.hb.hone]
    simp
  have he_exit := ExecWithin.loop_exit (body := dfsStepBody) (w := w) hc_exit
  exact ⟨z, (ExecWithin.loop_iter hc_loop he_step he_exit).mono (by omega),
    hr_z, hal_z, hvis_z, haug_z, hf_z⟩

theorem exec_dfsStep_push {w bOff k d : ℕ} {inst : SparseInstance}
    {mate : Vector (Option (Fin inst.m)) inst.r} {dist : Vector (Option ℕ) inst.m}
    {augPairs path : List (Fin inst.m × Fin inst.r)} {u w₀ : Fin inst.m}
    {pre vs : List (Fin inst.r)} {v : Fin inst.r}
    {vis : Vector Bool inst.r} {x : Data 34}
    (hd_lt_k : d < k) (hk_le : k ≤ inst.m + 1)
    (hsplit : inst.adj u = pre ++ v :: vs)
    (hfr : DfsFrame inst bOff k mate dist augPairs d path u pre vis x)
    (hvv : vget vis v = false) (hmv : vget mate v = some w₀)
    (hdw : vget dist w₀ = some (d + 1))
    (hfit : Fits w (bOff + 7 * inst.m + 5 * inst.r + inst.numEdges + 8)) :
    ∃ x_push, ExecWithin w dfsStepBody x x_push 36 ∧
      (∀ i : Fin 34, i.val < 25 → x_push.regs i = x.regs i) ∧
      DfsFrame inst bOff k mate dist augPairs (d + 1) (path ++ [(u, v)]) w₀ []
        (vset vis v true) x_push ∧
      x_push.mem (bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 5 * inst.m + 4 + d) =
        inst.offset u.val + (pre ++ [v]).length ∧
      (∀ a, DfsSubtreeOutside inst bOff d a → x_push.mem a = x.mem a) ∧
      (∀ a, ¬(bOff + inst.m + 1 + inst.numEdges + inst.r + 3 * inst.m ≤ a ∧
          a < bOff + inst.m + 1 + inst.numEdges + 4 * inst.r + 6 * inst.m + 6) →
        x_push.mem a = x.mem a) := by
  have hu_lt := u.isLt
  have hv_lt := v.isLt
  have hw_lt := w₀.isLt
  obtain ⟨hoff_succ, hed_lt, hlt_lim, hedge_v, hoff_u1⟩ := hfr.edge_facts hsplit
  have hvis_v := hfr.hvisM.mem_eq_zero hvv
  have hmate_v := hfr.hmate v
  have henc_m : encodeOptFin (vget mate v) = w₀.val := by simp [hmv, encodeOptFin]
  have hw_ne : w₀.val ≠ inst.m := ne_of_lt hw_lt
  have hdist_w := hfr.hdM w₀
  have henc_dw : encodeDist (vget dist w₀) = d + 2 := by simp [hdw, encodeDist]
  have hoff_w : x.mem (bOff + w₀.val) = inst.offset w₀.val := hfr.hcsr.hoff (le_of_lt hw_lt)
  have hplen := hfr.hplen
  have hraw : ∃ x_push, ExecWithin w dfsStepBody x x_push 36 ∧
      (∀ i : Fin 34, i.val < 25 → x_push.regs i = x.regs i) ∧
      x_push.regs rd = d + 1 ∧
      x_push.regs augLen = augPairs.length ∧
      x_push.regs active = 1 ∧
      VisMem inst bOff (vset vis v true) x_push.mem ∧
      (∀ i : ℕ, (hi : i < d + 1) →
        x_push.mem (bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 3 * inst.m + i) =
          ((path ++ [(u, v)])[i]'(by simp [hplen]; omega)).1.val ∧
        x_push.mem (bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 4 * inst.m + 2 + i) =
          ((path ++ [(u, v)])[i]'(by simp [hplen]; omega)).2.val) ∧
      x_push.mem (bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 3 * inst.m + (d + 1)) =
        w₀.val ∧
      x_push.mem (bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 5 * inst.m + 4 + d) =
        inst.offset u.val + (pre ++ [v]).length ∧
      x_push.mem (bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 5 * inst.m + 4 + (d + 1)) =
        inst.offset w₀.val ∧
      (∀ a, DfsSubtreeOutside inst bOff d a → x_push.mem a = x.mem a) := by
    refine WP.exists_execWithin ?_
    wram_exec [dfsStepBody,
      hfr.hb.hbStackU, hfr.hb.hbOff, hfr.hb.hbStackPos, hfr.hb.hbEdges, hfr.hb.hbVis,
      hfr.hb.hbColMate, hfr.hb.hbDist, hfr.hb.hbStackV, hfr.hb.hrm, hfr.hb.hone, hfr.hb.hzero,
      hfr.hb.htwo, hfr.hrd, hfr.hrk, hd_lt_k, hfr.hsu, hoff_u1, hfr.hsp, hlt_lim, hedge_v,
      hvis_v, hmate_v, henc_m, hw_ne, hdist_w, henc_dw, hoff_w]
    refine ⟨fun i hi => by wram_simp, by wram_simp, by wram_simp [hfr.hal],
      by wram_simp [hfr.hact], ?_, ?_, by wram_simp, by wram_simp; simp [Nat.add_assoc],
      by wram_simp, fun a ha => by simp only [DfsSubtreeOutside] at ha; wram_simp⟩
    · exact hfr.hvisM.vset_true v (by wram_simp) fun v₀ hne => by
        have := v₀.isLt
        have hne_val : v₀.val ≠ v.val := fun h => hne (Fin.ext h)
        wram_simp
    · exact stack_snoc (inst := inst) (bOff := bOff) (d := d) (u := u) (v := v)
        hplen hfr.hstack hfr.hsu
        (fun i hi => by wram_simp) (fun i hi => by wram_simp) (by wram_simp)
  obtain ⟨x_push, he_push, hr_p, hrd_p, hal_p, hact_p, hvis_p, hstack_p,
    hsu1_p, hspd_p, hsp1_p, hf_p⟩ := hraw
  have haug_le : augPairs.length ≤ inst.r :=
    (List.sublist_append_left augPairs path).length_le.trans hfr.hcovers.length_le
  have hout (a : ℕ) (ha : ¬(bOff + inst.m + 1 + inst.numEdges + inst.r + 3 * inst.m ≤ a ∧
      a < bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 6 * inst.m + 6)) :
      x_push.mem a = x.mem a :=
    hf_p a (by simp only [DfsSubtreeOutside]; omega)
  refine ⟨x_push, he_push, hr_p,
    { hplen := by simp [hplen]
      hcovers := by simpa [List.append_assoc] using hfr.hcovers.snoc u hvv
      hb := hfr.hb.of_eq fun i hi => hr_p i (by omega)
      hcsr := hfr.hcsr.of_outside fun a _ => hout a (by omega)
      hmate := hfr.hmate.of_outside fun a _ => hout a (by omega)
      hdM := hfr.hdM.of_outside fun a _ => hout a (by omega)
      hvisM := hvis_p
      haugM := hfr.haugM.of_outside haug_le fun a _ => hout a (by omega)
      hstack := hstack_p
      hsu := hsu1_p
      hsp := by simpa using hsp1_p
      hrk := (hr_p rk (by decide)).trans hfr.hrk
      hrd := hrd_p
      hal := hal_p
      hact := hact_p },
    hspd_p, hf_p, fun a _ => hout a (by omega)⟩

end Cslib.Algorithms.WordRAM.HopcroftKarp.Internal
