/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Distributed.SetAgreement.ImmediateSnapshot
public import Mathlib.Algebra.Ring.Parity
import CslibFrontier.Foundations.Combinatorics.Sperner.Kuhn
import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.ZMod.Basic

/-!
# Combinatorial Sperner Parity and Wait-Free `k`-Set Agreement Impossibility in `IIS`

As an `R`-round Iterated Immediate Snapshot (`IIS`) step toward `#7504` (leaving the general
asynchronous read/write shared-memory to `IIS` simulation open in `#7504`), this module proves the
impossibility of wait-free `k`-set agreement for `R`-round deterministic `IIS` protocols
(after [HerlihyShavit1999], §3.3, Lemma 3.2 and Theorem 3.3, pp. 880–881; [BorowskyGafni1993];
[SaksZaharoglou2000]; [BorowskyGafni1997], §3.5), via a purely combinatorial interior-facet
involution paired with `Cslib.Sperner.odd_card_doors_iff_surjective`.

* **One-shot `IS` split/merge involution (`flipBlocks`, `ISSchedule.flip`):** for an active
  process `q ∈ U`, an ordered partition `π : ISSchedule U` lies on the `q`-boundary
  (`π.IsBoundaryAt q`) precisely when `{q}` is the unique final block (`π.blocks = init ++ [{q}]`),
  so no other process observes `q`. Dropping `{q}` establishes a snapshot-preserving bijection
  `ISSchedule.boundaryEquiv` with `ISSchedule (U.erase q)`. On all non-boundary schedules, either
  `q` belongs to a block `B` with `B ≠ {q}` (split `{q}` immediately before `B.erase q`) or `{q}`
  is a singleton block followed by `C` (merge `{q}` into `insert q C`). This defines an explicit
  fixed-point-free involution `ISSchedule.flip` preserving `.snapshot p` for every `p ≠ q`.
* **`R`-round `IIS` execution involution (`flipIISExec`):** scanning backwards from the final
  round `R` to find the last round `r` in which `E r` is not `q`-boundary, and applying the
  one-shot `ISSchedule.flip` in round `r`, yields an involution on `Fin R → ISSchedule U` whose
  fixed points are exactly the `q`-boundary executions (`IsBoundaryExecAt q E`) and which preserves
  the `R`-round full-information view `iisRun inp E p` for every `p ≠ q`
  (`iisRun_flipIISExec_of_ne`), because in all later rounds `r' > r`, `{q}` runs last alone so no
  `p ≠ q` observes `q`'s changed round-`r` view.
* **Odd Panchromatic `IIS` Execution Parity (`odd_card_panchromatic_iis`):** by induction on `#U`,
  combining `Cslib.Sperner.odd_card_doors_iff_surjective` with `flipIISExec` on interior doors and
  `boundaryExecEquiv` on boundary doors, every carrier-valid coloring `c : IISView V Input R → V`
  (`∀ v, c v ∈ v.carrier`) admits an **odd** number (hence at least one) of panchromatic `R`-round
  `IIS` executions hitting all `#U` colors.
* **Wait-Free `k`-Set Agreement Impossibility & Quorum Sharpness (`#7504` steps):**
  - `not_solvesSetAgreement_iis`: when `k + 1 ≤ Fintype.card V` and `k + 1 ≤ Fintype.card Val`, no
    `R`-round `IIS` protocol solves `k`-set agreement (`IISProtocol.SolvesSetAgreement`).
  - `exists_iis_setAgreement_iff`: `k`-set agreement is solvable in `IIS` if and only if
    `Fintype.card V ≤ k ∨ Fintype.card Val ≤ k`.
  - `exists_quorumSetAgreement_of_lt`: in contrast, in the one-round `(n - t)`-quorum model where
    at most `t < k` processes are missed, the `(t + 1)`-leader protocol solves `k`-set agreement.

## Model scope

The impossibility theorem `not_solvesSetAgreement_iis` applies to deterministic full-information
protocols in the `R`-round Iterated Immediate Snapshot (`IIS`) model (`IISProtocol V Val R`) as a
step toward `#7504`. The asynchronous read/write shared-memory to `IIS` simulation
([BorowskyGafni1993]; [BorowskyGafni1997]; [HerlihyShavit1999]) is tracked separately in #7504.

## Main definitions

* `Cslib.Distributed.SetAgreement.ISSchedule.IsBoundaryAt`,
  `Cslib.Distributed.SetAgreement.ISSchedule.flip`,
  `Cslib.Distributed.SetAgreement.ISSchedule.boundaryEquiv`: one-shot `q`-boundary predicate,
  split/merge involution, and boundary schedule equivalence.
* `Cslib.Distributed.SetAgreement.IsBoundaryExecAt`,
  `Cslib.Distributed.SetAgreement.flipIISExec`,
  `Cslib.Distributed.SetAgreement.boundaryExecEquiv`: `R`-round `q`-boundary predicate,
  backwards-from-`R` execution involution, and boundary execution equivalence.
* `Cslib.Distributed.SetAgreement.IsCarrierColoring`,
  `Cslib.Distributed.SetAgreement.IsPanchromaticIIS`: carrier-valid `IIS` view colorings and
  panchromatic `IIS` executions.
* `Cslib.Distributed.SetAgreement.IISProtocol.SolvesSetAgreement`: wait-free `k`-set agreement
  specification for `R`-round `IIS` protocols.
* `Cslib.Distributed.SetAgreement.IsQuorumSchedule`,
  `Cslib.Distributed.SetAgreement.QuorumProtocol`,
  `Cslib.Distributed.SetAgreement.QuorumProtocol.SolvesSetAgreement`: one-round `(n - t)`-quorum
  `k`-set agreement model and specification.

## Main results

* `Cslib.Distributed.SetAgreement.ISSchedule.flip_flip`,
  `Cslib.Distributed.SetAgreement.ISSchedule.flip_eq_self_iff`,
  `Cslib.Distributed.SetAgreement.ISSchedule.snapshot_flip_of_ne`: one-shot split/merge involution
  laws.
* `Cslib.Distributed.SetAgreement.flipIISExec_flipIISExec`,
  `Cslib.Distributed.SetAgreement.flipIISExec_eq_self_iff`,
  `Cslib.Distributed.SetAgreement.iisRun_flipIISExec_of_ne`: `R`-round `IIS` interior-facet
  involution laws.
* `Cslib.Distributed.SetAgreement.odd_card_panchromatic_iis`,
  `Cslib.Distributed.SetAgreement.exists_panchromatic_iis`: odd parity and existence of
  panchromatic `R`-round `IIS` executions.
* `Cslib.Distributed.SetAgreement.not_solvesSetAgreement_iis`,
  `Cslib.Distributed.SetAgreement.exists_iis_setAgreement_iff`: wait-free `k`-set agreement
  impossibility step and sharp solvability criterion in `IIS`.
* `Cslib.Distributed.SetAgreement.exists_quorumSetAgreement_of_lt`: positive one-round
  `(n - t)`-quorum `k`-set agreement protocol whenever `t < k`.

## References

* [E. Borowsky, E. Gafni, *Generalized FLP Impossibility Result for t-Resilient Asynchronous
  Computations*][BorowskyGafni1993]
* [E. Borowsky, E. Gafni, *A Simple Algorithmically Reasoned Characterization of Wait-Free
  Computations*][BorowskyGafni1997]
* [M. Herlihy, N. Shavit, *The Topological Structure of Asynchronous
  Computability*][HerlihyShavit1999]
* [M. Saks, F. Zaharoglou, *Wait-Free k-Set Agreement Is Impossible: The Topology of Public
  Knowledge*][SaksZaharoglou2000]
-/

public section

namespace Cslib.Distributed.SetAgreement

open Finset

/-! ### Part 1: One-shot `IS` split/merge involution and boundary equivalence -/

section OneShotInvolution

variable {V : Type*} [DecidableEq V]

/-- Block-level split/merge involution at process `q`:
* `[B]`: fixed if `B = {q}`, else split into `[{q}, B.erase q]`;
* `B :: C :: rest` with `q ∈ B`: if `B = {q}` merge into `insert q C :: rest`, else split into
  `{q} :: B.erase q :: C :: rest`;
* `B :: C :: rest` with `q ∉ B`: recurse on `C :: rest`. -/
@[expose]
def flipBlocks (q : V) : List (Finset V) → List (Finset V)
  | [] => []
  | [B] => if B = {q} then [B] else [{q}, B.erase q]
  | B :: C :: rest =>
    if q ∈ B then
      if B = {q} then insert q C :: rest
      else {q} :: B.erase q :: C :: rest
    else
      B :: flipBlocks q (C :: rest)

omit [DecidableEq V] in
private theorem not_exists_append_singleton_of_head_mem {B C : Finset V} {rest : List (Finset V)}
    {q : V} (hqB : q ∈ B) (hdisj : (B :: C :: rest).Pairwise Disjoint) :
    ¬ ∃ init, B :: C :: rest = init ++ [{q}] := by
  rintro ⟨init, heq⟩
  cases init with
  | nil => simp at heq
  | cons D tl =>
    simp only [List.cons_append, List.cons.injEq] at heq
    obtain ⟨rfl, htl⟩ := heq
    rw [List.pairwise_cons] at hdisj
    have hq_mem : {q} ∈ C :: rest := htl ▸ List.mem_append_right tl (List.mem_singleton.mpr rfl)
    exact Finset.disjoint_left.mp (hdisj.1 {q} hq_mem) hqB (mem_singleton_self q)

/-- Merging the first two blocks does not change the snapshot of a process outside the first. -/
private theorem blocksSnapshot_cons_cons_of_notMem {A C : Finset V} {rest : List (Finset V)}
    {p : V} (hpA : p ∉ A) :
    blocksSnapshot (A :: C :: rest) p = blocksSnapshot ((A ∪ C) :: rest) p := by
  simp only [blocksSnapshot, unionBlocks_cons, mem_union, hpA, false_or]
  by_cases hC : p ∈ C <;> by_cases hr : p ∈ unionBlocks rest <;> simp [hC, hr, union_assoc]

/-- Splitting `B ∋ q` (`B ≠ {q}`) into `{q} :: B.erase q` in front of `tail` keeps the blocks
nonempty and pairwise disjoint and preserves the union and every snapshot but `q`'s. -/
private theorem split_spec {B : Finset V} {q : V} (tail : List (Finset V)) (hqB : q ∈ B)
    (hBs : B ≠ {q}) (hne : ∀ X ∈ B :: tail, X.Nonempty) (hdisj : (B :: tail).Pairwise Disjoint) :
    (∀ X ∈ {q} :: B.erase q :: tail, X.Nonempty) ∧
      ({q} :: B.erase q :: tail).Pairwise Disjoint ∧
      unionBlocks ({q} :: B.erase q :: tail) = unionBlocks (B :: tail) ∧
      ∀ p, p ≠ q → blocksSnapshot ({q} :: B.erase q :: tail) p = blocksSnapshot (B :: tail) p := by
  have hu : ({q} : Finset V) ∪ B.erase q = B := by rw [singleton_union, insert_erase hqB]
  have hBq : (B.erase q).Nonempty := by
    rw [← ne_empty_iff_nonempty, Ne, erase_eq_empty_iff, not_or]
    exact ⟨(hne B List.mem_cons_self).ne_empty, hBs⟩
  simp only [List.pairwise_cons, List.forall_mem_cons] at hne hdisj ⊢
  refine ⟨⟨singleton_nonempty q, hBq, hne.2⟩,
    ⟨⟨disjoint_singleton_left.mpr (notMem_erase q B), fun D hD =>
        (hdisj.1 D hD).mono_left (singleton_subset_iff.mpr hqB)⟩,
      fun D hD => (hdisj.1 D hD).mono_left (erase_subset q B), hdisj.2⟩,
    by rw [unionBlocks_cons, unionBlocks_cons, ← union_assoc, hu, unionBlocks_cons],
    fun p hpq => ?_⟩
  cases tail <;> rw [blocksSnapshot_cons_cons_of_notMem (by simpa using hpq), hu]

/-- Complete structural specification of `flipBlocks q bs` for valid block lists containing `q`. -/
private theorem flipBlocks_spec (q : V) :
    ∀ (bs : List (Finset V)),
      (∀ B ∈ bs, B.Nonempty) → bs.Pairwise Disjoint → q ∈ unionBlocks bs →
      (∀ B ∈ flipBlocks q bs, B.Nonempty) ∧
        (flipBlocks q bs).Pairwise Disjoint ∧
        unionBlocks (flipBlocks q bs) = unionBlocks bs ∧
        flipBlocks q (flipBlocks q bs) = bs ∧
        (flipBlocks q bs = bs ↔ ∃ init, bs = init ++ [{q}]) ∧
        (∀ p, p ≠ q → blocksSnapshot (flipBlocks q bs) p = blocksSnapshot bs p)
  | [], _, _, hq => nomatch notMem_empty q hq
  | [B], hne, hdisj, hq => by
    have hqB : q ∈ B := by simpa only [unionBlocks_cons, unionBlocks_nil, union_empty] using hq
    by_cases hBs : B = {q}
    · subst hBs
      have hfl : flipBlocks q [{q}] = [{q}] := by simp [flipBlocks]
      rw [hfl]
      exact ⟨hne, hdisj, rfl, hfl, ⟨fun _ => ⟨[], rfl⟩, fun _ => rfl⟩, fun _ _ => rfl⟩
    · obtain ⟨h1, h2, h3, h4⟩ := split_spec [] hqB hBs hne hdisj
      simp only [flipBlocks, hBs, ↓reduceIte]
      refine ⟨h1, h2, h3, by simp [insert_erase hqB], ?_, h4⟩
      simp [List.append_eq_singleton_iff, eq_comm (a := [B]), Ne.symm hBs]
  | B :: C :: rest, hne, hdisj, hq => by
    have hfix {bs'} (hlen : bs'.length ≠ (B :: C :: rest).length) (hqB : q ∈ B) :
        (bs' = B :: C :: rest ↔ ∃ init, B :: C :: rest = init ++ [{q}]) :=
      iff_of_false (fun h => hlen (congrArg List.length h))
        (not_exists_append_singleton_of_head_mem hqB hdisj)
    by_cases hqB : q ∈ B
    · by_cases hBs : B = {q}
      · -- Merge `{q}` into `C`: `insert q C :: rest`
        subst hBs
        simp only [List.pairwise_cons, List.forall_mem_cons] at hne hdisj
        have hqC : q ∉ C := disjoint_left.mp hdisj.1.1 (mem_singleton_self q)
        have hins : insert q C ≠ {q} := fun h => hqC (by
          obtain ⟨c, hc⟩ := hne.2.1
          simpa [mem_singleton.mp (h ▸ mem_insert_of_mem hc)] using hc)
        simp only [flipBlocks, mem_singleton, ↓reduceIte]
        refine ⟨?_, ?_, by
          rw [unionBlocks_cons, unionBlocks_cons, unionBlocks_cons, insert_eq, union_assoc], ?_,
          hfix (by simp) hqB, fun p hpq => ?_⟩
        · simpa using hne.2.2
        · simp only [List.pairwise_cons]
          exact ⟨fun D hD => disjoint_insert_left.mpr
            ⟨disjoint_left.mp (hdisj.1.2 D hD) (mem_singleton_self q), hdisj.2.1 D hD⟩,
            hdisj.2.2⟩
        · cases rest <;> simp [flipBlocks, hins, erase_insert hqC]
        · rw [blocksSnapshot_cons_cons_of_notMem (by simpa using hpq), singleton_union]
      · -- Split `B` into `{q} :: B.erase q :: C :: rest`
        obtain ⟨h1, h2, h3, h4⟩ := split_spec (C :: rest) hqB hBs hne hdisj
        simp only [flipBlocks, hqB, hBs, ↓reduceIte]
        exact ⟨h1, h2, h3, by simp [insert_erase hqB], hfix (by simp) hqB, h4⟩
    · -- `q ∉ B`: recurse on `C :: rest`
      rw [List.pairwise_cons] at hdisj
      have hq_tl : q ∈ unionBlocks (C :: rest) := (mem_union.mp hq).resolve_left hqB
      obtain ⟨hne', hdisj', hu', hinv', hfix', hsnap'⟩ :=
        flipBlocks_spec q (C :: rest) (fun X hX => hne X (List.mem_cons_of_mem B hX))
          hdisj.2 hq_tl
      obtain ⟨D, tl', hfl⟩ : ∃ D tl', flipBlocks q (C :: rest) = D :: tl' := by
        cases h : flipBlocks q (C :: rest) with
        | nil => rw [h, unionBlocks_nil] at hu'; exact absurd (hu' ▸ hq_tl) (notMem_empty q)
        | cons D tl' => exact ⟨D, tl', rfl⟩
      simp only [flipBlocks, hqB, ↓reduceIte]
      refine ⟨?_, List.pairwise_cons.mpr ⟨disjoint_unionBlocks_right.mp
          (hu' ▸ disjoint_unionBlocks_right.mpr hdisj.1), hdisj'⟩,
        by simp only [unionBlocks_cons, hu'], ?_, ?_, fun p hpq => ?_⟩
      · simpa [List.forall_mem_cons, hne B List.mem_cons_self] using hne'
      · rw [hfl]; simp only [flipBlocks, hqB, ↓reduceIte]; rw [← hfl, hinv']
      · simp [hfix', List.cons_eq_append_iff]
      · simp only [blocksSnapshot, hu', hsnap' p hpq]

/-- A one-shot `IS` schedule `π : ISSchedule U` lies on the `q`-boundary when `{q}` is the unique
final block of `π.blocks` (so no process `p ≠ q` observes `q`). -/
@[expose]
def ISSchedule.IsBoundaryAt {U : Finset V} (π : ISSchedule U) (q : V) : Prop :=
  π.blocks.getLast? = some {q}

instance instDecidableIsBoundaryAt {U : Finset V} (π : ISSchedule U) (q : V) :
    Decidable (π.IsBoundaryAt q) :=
  inferInstanceAs (Decidable (π.blocks.getLast? = some {q}))

theorem ISSchedule.isBoundaryAt_iff_exists_append {U : Finset V} (π : ISSchedule U) (q : V) :
    π.IsBoundaryAt q ↔ ∃ init, π.blocks = init ++ [{q}] := by
  unfold ISSchedule.IsBoundaryAt
  constructor
  · intro h
    have hne : π.blocks ≠ [] := by
      intro hnil
      simp only [hnil, List.getLast?_nil] at h
      nomatch h
    rw [List.getLast?_eq_some_getLast hne, Option.some.injEq] at h
    exact ⟨π.blocks.dropLast, (List.dropLast_append_getLast hne).symm.trans (by rw [h])⟩
  · rintro ⟨init, heq⟩
    rw [heq, List.getLast?_concat]

/-- One-shot split/merge involution on `ISSchedule U` at `q ∈ U`. -/
def ISSchedule.flip {U : Finset V} {q : V} (hq : q ∈ U) (π : ISSchedule U) : ISSchedule U where
  blocks := flipBlocks q π.blocks
  blocks_nonempty := by
    obtain ⟨hne, -, -, -⟩ := flipBlocks_spec q π.blocks π.blocks_nonempty
      π.blocks_pairwise_disjoint (π.union_blocks.symm ▸ hq)
    exact hne
  blocks_pairwise_disjoint := by
    obtain ⟨-, hdisj, -, -⟩ := flipBlocks_spec q π.blocks π.blocks_nonempty
      π.blocks_pairwise_disjoint (π.union_blocks.symm ▸ hq)
    exact hdisj
  union_blocks := by
    obtain ⟨-, -, hu, -⟩ := flipBlocks_spec q π.blocks π.blocks_nonempty
      π.blocks_pairwise_disjoint (π.union_blocks.symm ▸ hq)
    exact hu.trans π.union_blocks

@[simp]
theorem ISSchedule.blocks_flip {U : Finset V} {q : V} (hq : q ∈ U) (π : ISSchedule U) :
    (π.flip hq).blocks = flipBlocks q π.blocks := by
  rfl

@[simp]
theorem ISSchedule.flip_flip {U : Finset V} {q : V} (hq : q ∈ U) (π : ISSchedule U) :
    (π.flip hq).flip hq = π := by
  ext1
  unfold ISSchedule.flip
  dsimp only
  exact (flipBlocks_spec q π.blocks π.blocks_nonempty π.blocks_pairwise_disjoint
    (π.union_blocks.symm ▸ hq)).2.2.2.1

theorem ISSchedule.flip_eq_self_iff {U : Finset V} {q : V} (hq : q ∈ U) (π : ISSchedule U) :
    π.flip hq = π ↔ π.IsBoundaryAt q := by
  rw [ISSchedule.ext_iff, isBoundaryAt_iff_exists_append]
  unfold ISSchedule.flip
  dsimp only
  exact (flipBlocks_spec q π.blocks π.blocks_nonempty π.blocks_pairwise_disjoint
    (π.union_blocks.symm ▸ hq)).2.2.2.2.1

theorem ISSchedule.isBoundaryAt_flip_iff {U : Finset V} {q : V} (hq : q ∈ U) (π : ISSchedule U) :
    (π.flip hq).IsBoundaryAt q ↔ π.IsBoundaryAt q := by
  rw [← flip_eq_self_iff hq, flip_flip, ← flip_eq_self_iff hq, eq_comm]

theorem ISSchedule.snapshot_flip_of_ne {U : Finset V} {q : V} (hq : q ∈ U) (π : ISSchedule U)
    {p : V} (hpq : p ≠ q) :
    (π.flip hq).snapshot p = π.snapshot p := by
  unfold ISSchedule.snapshot ISSchedule.flip
  dsimp only
  exact (flipBlocks_spec q π.blocks π.blocks_nonempty π.blocks_pairwise_disjoint
    (π.union_blocks.symm ▸ hq)).2.2.2.2.2 p hpq

/-- Drop the trailing singleton `{q}` from a `q`-boundary schedule on `U`, producing a schedule on
`U.erase q`. -/
@[expose]
def ISSchedule.dropBoundary {U : Finset V} {q : V} (π : ISSchedule U)
    (hb : π.IsBoundaryAt q) : ISSchedule (U.erase q) where
  blocks := π.blocks.dropLast
  blocks_nonempty B hB := π.blocks_nonempty B (List.dropLast_subset _ hB)
  blocks_pairwise_disjoint := by
    obtain ⟨init, heq⟩ := (π.isBoundaryAt_iff_exists_append q).mp hb
    rw [heq, List.dropLast_concat]
    exact (List.pairwise_append.mp (heq ▸ π.blocks_pairwise_disjoint)).1
  union_blocks := by
    obtain ⟨init, heq⟩ := (π.isBoundaryAt_iff_exists_append q).mp hb
    rw [heq, List.dropLast_concat]
    have hpw := List.pairwise_append.mp (heq ▸ π.blocks_pairwise_disjoint)
    have hq_not : q ∉ unionBlocks init := by
      intro hq_in
      obtain ⟨B, hB, hqB⟩ := mem_unionBlocks.mp hq_in
      exact Finset.disjoint_left.mp (hpw.2.2 B hB {q} List.mem_cons_self) hqB
        (mem_singleton_self q)
    have hu : unionBlocks init ∪ {q} = U := by
      have h := π.union_blocks
      rwa [heq, unionBlocks_append, unionBlocks_cons, unionBlocks_nil, union_empty] at h
    ext x
    simp only [mem_erase]
    constructor
    · intro hx
      exact ⟨fun hxq => hq_not (hxq ▸ hx), hu ▸ mem_union_left _ hx⟩
    · rintro ⟨hxq, hxU⟩
      rcases mem_union.mp (hu.symm ▸ hxU) with hx | hx
      · exact hx
      · exact absurd (mem_singleton.mp hx) hxq

/-- Append trailing singleton `{q}` to a schedule on `U.erase q` (`q ∈ U`), producing a
`q`-boundary schedule on `U`. -/
@[expose]
def ISSchedule.snocSingleton {U : Finset V} {q : V} (hq : q ∈ U)
    (π₀ : ISSchedule (U.erase q)) : ISSchedule U where
  blocks := π₀.blocks ++ [{q}]
  blocks_nonempty B hB := by
    rcases List.mem_append.mp hB with hB | hB
    · exact π₀.blocks_nonempty B hB
    · rw [List.mem_singleton.mp hB]
      exact singleton_nonempty q
  blocks_pairwise_disjoint := by
    rw [List.pairwise_append]
    refine ⟨π₀.blocks_pairwise_disjoint, List.pairwise_singleton _ _, fun B hB C hC => ?_⟩
    rw [List.mem_singleton.mp hC]
    refine Finset.disjoint_right.mpr fun x hx hB_in => ?_
    rw [mem_singleton.mp hx] at hB_in
    have hq_er : q ∈ U.erase q := π₀.union_blocks ▸ mem_unionBlocks.mpr ⟨B, hB, hB_in⟩
    exact notMem_erase q U hq_er
  union_blocks := by
    rw [unionBlocks_append, π₀.union_blocks, unionBlocks_cons, unionBlocks_nil, union_empty,
      union_comm, ← insert_eq, insert_erase hq]

theorem ISSchedule.isBoundaryAt_snocSingleton {U : Finset V} {q : V} (hq : q ∈ U)
    (π₀ : ISSchedule (U.erase q)) :
    (π₀.snocSingleton hq).IsBoundaryAt q := by
  simp only [IsBoundaryAt, snocSingleton, List.getLast?_concat]

theorem ISSchedule.snapshot_dropBoundary_of_ne {U : Finset V} {q : V} (π : ISSchedule U)
    (hb : π.IsBoundaryAt q) {p : V} (hpq : p ≠ q) :
    (π.dropBoundary hb).snapshot p = π.snapshot p := by
  obtain ⟨init, heq⟩ := (π.isBoundaryAt_iff_exists_append q).mp hb
  unfold ISSchedule.snapshot ISSchedule.dropBoundary
  dsimp only
  rw [heq, List.dropLast_concat]
  by_cases hp_init : p ∈ unionBlocks init
  · exact (blocksSnapshot_append_of_mem_left hp_init).symm
  · have hp_not_all : p ∉ unionBlocks (init ++ [{q}]) := by
      simp only [unionBlocks_append, unionBlocks_cons, unionBlocks_nil, union_empty, mem_union,
        mem_singleton, hp_init, hpq, or_self, not_false_eq_true]
    rw [blocksSnapshot_of_notMem hp_init, blocksSnapshot_of_notMem hp_not_all]

theorem ISSchedule.notMem_snapshot_of_isBoundaryAt {U : Finset V} {q : V} (π : ISSchedule U)
    (hb : π.IsBoundaryAt q) {p : V} (hpq : p ≠ q) :
    q ∉ π.snapshot p := by
  rw [← π.snapshot_dropBoundary_of_ne hb hpq]
  exact fun hq_in => notMem_erase q U ((π.dropBoundary hb).snapshot_subset p hq_in)

/-- Exact equivalence between `q`-boundary schedules on `U` (`q ∈ U`) and all schedules on
`U.erase q`. -/
def ISSchedule.boundaryEquiv {U : Finset V} {q : V} (hq : q ∈ U) :
    {π : ISSchedule U // π.IsBoundaryAt q} ≃ ISSchedule (U.erase q) where
  toFun π := π.val.dropBoundary π.property
  invFun π₀ := ⟨π₀.snocSingleton hq, π₀.isBoundaryAt_snocSingleton hq⟩
  left_inv π := by
    ext1
    ext1
    obtain ⟨init, heq⟩ := (π.val.isBoundaryAt_iff_exists_append q).mp π.property
    simp only [dropBoundary, snocSingleton]
    rw [heq, List.dropLast_concat]
  right_inv π₀ := by
    ext1
    simp only [dropBoundary, snocSingleton, List.dropLast_concat]

end OneShotInvolution

/-! ### Part 2: `R`-round `IIS` backwards-from-`R` interior-facet involution -/

section IISInvolution

variable {V : Type*} [DecidableEq V]

/-- An `R`-round `IIS` execution `E` lies on the `q`-boundary when `{q}` runs last alone in every
round `r : Fin R`. -/
@[expose]
def IsBoundaryExecAt {U : Finset V} (q : V) {R : ℕ} (E : Fin R → ISSchedule U) : Prop :=
  ∀ r : Fin R, (E r).IsBoundaryAt q

instance instDecidableIsBoundaryExecAt {U : Finset V} (q : V) {R : ℕ}
    (E : Fin R → ISSchedule U) : Decidable (IsBoundaryExecAt q E) :=
  inferInstanceAs (Decidable (∀ r : Fin R, (E r).IsBoundaryAt q))

theorem isBoundaryExecAt_succ_iff {U : Finset V} (q : V) {R : ℕ}
    (E : Fin (R + 1) → ISSchedule U) :
    IsBoundaryExecAt q E ↔ IsBoundaryExecAt q (Fin.init E) ∧ (E (Fin.last R)).IsBoundaryAt q := by
  constructor
  · intro h
    exact ⟨fun r => h r.castSucc, h (Fin.last R)⟩
  · rintro ⟨hinit, hlast⟩ r
    exact Fin.lastCases hlast hinit r

/-- Backwards-from-`R` interior-facet involution on `R`-round `IIS` executions:
scan from the final round `Fin.last (R - 1)` down to `0`, and apply the one-shot split/merge
involution `ISSchedule.flip` at the **largest** round `r` where `E r` is not `q`-boundary. -/
@[expose]
def flipIISExec {U : Finset V} {q : V} (hq : q ∈ U) :
    {R : ℕ} → (Fin R → ISSchedule U) → (Fin R → ISSchedule U)
  | 0, E => E
  | R + 1, E =>
    if (E (Fin.last R)).IsBoundaryAt q then
      Fin.snoc (flipIISExec hq (Fin.init E)) (E (Fin.last R))
    else
      Fin.snoc (Fin.init E) ((E (Fin.last R)).flip hq)

theorem flipIISExec_succ_of_isBoundaryAt {U : Finset V} {q : V} (hq : q ∈ U) {R : ℕ}
    {E : Fin (R + 1) → ISSchedule U} (hb : (E (Fin.last R)).IsBoundaryAt q) :
    flipIISExec hq E = Fin.snoc (flipIISExec hq (Fin.init E)) (E (Fin.last R)) := by
  simp only [flipIISExec, hb, ↓reduceIte]

theorem flipIISExec_succ_of_not_isBoundaryAt {U : Finset V} {q : V} (hq : q ∈ U) {R : ℕ}
    {E : Fin (R + 1) → ISSchedule U} (hb : ¬ (E (Fin.last R)).IsBoundaryAt q) :
    flipIISExec hq E = Fin.snoc (Fin.init E) ((E (Fin.last R)).flip hq) := by
  simp only [flipIISExec, hb, ↓reduceIte]

@[simp]
theorem flipIISExec_flipIISExec {U : Finset V} {q : V} (hq : q ∈ U) :
    ∀ {R : ℕ} (E : Fin R → ISSchedule U), flipIISExec hq (flipIISExec hq E) = E
  | 0, E => rfl
  | R + 1, E => by
    by_cases hb : (E (Fin.last R)).IsBoundaryAt q
    · rw [flipIISExec_succ_of_isBoundaryAt hq hb,
        flipIISExec_succ_of_isBoundaryAt hq (by rw [Fin.snoc_last]; exact hb)]
      simp only [Fin.snoc_last, Fin.init_snoc, flipIISExec_flipIISExec hq, Fin.snoc_init_self]
    · have hb_flip : ¬ ((E (Fin.last R)).flip hq).IsBoundaryAt q := by
        rwa [ISSchedule.isBoundaryAt_flip_iff hq]
      rw [flipIISExec_succ_of_not_isBoundaryAt hq hb,
        flipIISExec_succ_of_not_isBoundaryAt hq (by rw [Fin.snoc_last]; exact hb_flip)]
      simp only [Fin.snoc_last, Fin.init_snoc, ISSchedule.flip_flip, Fin.snoc_init_self]

theorem flipIISExec_eq_self_iff {U : Finset V} {q : V} (hq : q ∈ U) :
    ∀ {R : ℕ} (E : Fin R → ISSchedule U), flipIISExec hq E = E ↔ IsBoundaryExecAt q E
  | 0, E => ⟨fun _ r => Fin.elim0 r, fun _ => Subsingleton.elim _ _⟩
  | R + 1, E => by
    rw [isBoundaryExecAt_succ_iff]
    unfold flipIISExec
    by_cases hb : (E (Fin.last R)).IsBoundaryAt q
    · simp only [hb, ↓reduceIte, and_true, ← flipIISExec_eq_self_iff hq (Fin.init E)]
      constructor
      · intro heq
        have := congrArg Fin.init heq
        rwa [Fin.init_snoc] at this
      · intro heq
        rw [heq, Fin.snoc_init_self]
    · simp only [hb, ↓reduceIte, and_false, iff_false]
      intro heq
      have hlast := congrFun heq (Fin.last R)
      rw [Fin.snoc_last] at hlast
      exact hb ((ISSchedule.flip_eq_self_iff hq _).mp hlast)

theorem isBoundaryExecAt_flipIISExec_iff {U : Finset V} {q : V} (hq : q ∈ U) {R : ℕ}
    (E : Fin R → ISSchedule U) :
    IsBoundaryExecAt q (flipIISExec hq E) ↔ IsBoundaryExecAt q E := by
  rw [← flipIISExec_eq_self_iff hq, flipIISExec_flipIISExec, ← flipIISExec_eq_self_iff hq, eq_comm]

/-- View invariance under `flipIISExec`: flipping at `q` preserves the `R`-round `IIS` view of
every process `p ≠ q`. -/
theorem iisRun_flipIISExec_of_ne {Input : Type*} [DecidableEq Input] {U : Finset V} {q : V}
    (hq : q ∈ U) (inp : V → Input) :
    ∀ {R : ℕ} (E : Fin R → ISSchedule U) {p : V}, p ≠ q →
      iisRun inp (flipIISExec hq E) p = iisRun inp E p
  | 0, _, _, _ => rfl
  | R + 1, E, p, hpq => by
    rw [iisRun_succ, iisRun_succ]
    congr 1
    unfold flipIISExec
    by_cases hb : (E (Fin.last R)).IsBoundaryAt q
    · simp only [hb, ↓reduceIte, Fin.snoc_last, Fin.init_snoc]
      refine image_congr fun r hr => iisRun_flipIISExec_of_ne hq inp (Fin.init E) ?_
      intro hrq
      subst hrq
      exact (E (Fin.last R)).notMem_snapshot_of_isBoundaryAt hb hpq hr
    · simp only [hb, ↓reduceIte, Fin.snoc_last, Fin.init_snoc,
        ISSchedule.snapshot_flip_of_ne hq (E (Fin.last R)) hpq]

/-- Equivalence between `q`-boundary `R`-round `IIS` executions on `U` (`q ∈ U`) and all `R`-round
`IIS` executions on `U.erase q`. -/
def boundaryExecEquiv {U : Finset V} {q : V} (hq : q ∈ U) (R : ℕ) :
    {E : Fin R → ISSchedule U // IsBoundaryExecAt q E} ≃ (Fin R → ISSchedule (U.erase q)) where
  toFun E r := (E.val r).dropBoundary (E.property r)
  invFun E₀ := ⟨fun r => (E₀ r).snocSingleton hq, fun r => (E₀ r).isBoundaryAt_snocSingleton hq⟩
  left_inv E := by
    ext1
    funext r
    exact congrArg Subtype.val ((ISSchedule.boundaryEquiv hq).left_inv ⟨E.val r, E.property r⟩)
  right_inv E₀ := by
    funext r
    exact (ISSchedule.boundaryEquiv hq).right_inv (E₀ r)

theorem iisRun_dropBoundary_of_ne {Input : Type*} [DecidableEq Input] {U : Finset V} {q : V}
    (inp : V → Input) :
    ∀ {R : ℕ} (E : Fin R → ISSchedule U) (hb : IsBoundaryExecAt q E) {p : V}, p ≠ q →
      iisRun inp (fun r => (E r).dropBoundary (hb r)) p = iisRun inp E p
  | 0, _, _, _, _ => rfl
  | R + 1, E, hb, p, hpq => by
    rw [iisRun_succ, iisRun_succ]
    congr 1
    have hsnap : ((E (Fin.last R)).dropBoundary (hb (Fin.last R))).snapshot p =
        (E (Fin.last R)).snapshot p :=
      (E (Fin.last R)).snapshot_dropBoundary_of_ne (hb (Fin.last R)) hpq
    change (((E (Fin.last R)).dropBoundary (hb (Fin.last R))).snapshot p).image
        (iisRun inp (fun r : Fin R => (E r.castSucc).dropBoundary (hb r.castSucc))) =
      ((E (Fin.last R)).snapshot p).image (iisRun inp (Fin.init E))
    rw [hsnap]
    refine image_congr fun r hr => ?_
    have hrq : r ≠ q := fun heq =>
      (E (Fin.last R)).notMem_snapshot_of_isBoundaryAt (hb (Fin.last R)) hpq (heq ▸ hr)
    exact iisRun_dropBoundary_of_ne inp (Fin.init E) (fun s => hb s.castSucc) hrq

end IISInvolution

/-! ### Part 3: Combinatorial Sperner Parity for `R`-Round `IIS` Executions -/

section SpernerParity

variable {V Input : Type*} [DecidableEq V] [DecidableEq Input]

/-- Global carrier-validity of an `R`-round `IIS` view coloring (`Sperner` condition on the
iterated chromatic subdivision): every view `v` is colored by a process in `v.carrier`. -/
@[expose]
def IsCarrierColoring {R : ℕ} (c : IISView V Input R → V) : Prop :=
  ∀ v : IISView V Input R, c v ∈ v.carrier

/-- Subface-relativized carrier-validity on `U : Finset V` at input `inp`: for every active subset
`U' ⊆ U` and every `R`-round `IIS` execution on `U'`, each process `p ∈ U'` is colored by a member
of `(iisRun inp E p).carrier`. -/
private def IsCarrierColoringOn (U : Finset V) (inp : V → Input) {R : ℕ}
    (c : IISView V Input R → V) : Prop :=
  ∀ U' ⊆ U, ∀ (E : Fin R → ISSchedule U') (p : V),
    p ∈ U' → c (iisRun inp E p) ∈ (iisRun inp E p).carrier

private theorem IsCarrierColoring.on {R : ℕ} {c : IISView V Input R → V} (hc : IsCarrierColoring c)
    (U : Finset V) (inp : V → Input) : IsCarrierColoringOn U inp c :=
  fun _ _ E p _ => hc (iisRun inp E p)

/-- An `R`-round `IIS` execution `E` on `U` is *panchromatic* under coloring `c` at input `inp`
when every process color `b ∈ U` is decided by some active process `p ∈ U`. -/
@[expose]
def IsPanchromaticIIS (U : Finset V) (inp : V → Input) {R : ℕ}
    (c : IISView V Input R → V) (E : Fin R → ISSchedule U) : Prop :=
  ∀ b ∈ U, ∃ p ∈ U, c (iisRun inp E p) = b

instance instDecidableIsPanchromaticIIS (U : Finset V) (inp : V → Input) {R : ℕ}
    (c : IISView V Input R → V) (E : Fin R → ISSchedule U) :
    Decidable (IsPanchromaticIIS U inp c E) :=
  inferInstanceAs (Decidable (∀ b ∈ U, ∃ p ∈ U, c (iisRun inp E p) = b))

/-- Door predicate for `E : Fin R → ISSchedule U` at facet `k ∈ U` avoiding color `q₀`: every
color `b ∈ U \ {q₀}` appears at some vertex `j ∈ U \ {k}`. -/
private def IsIISDoor (U : Finset V) (inp : V → Input) {R : ℕ}
    (c : IISView V Input R → V) (q₀ : V) (E : Fin R → ISSchedule U) (k : V) : Prop :=
  ∀ b ∈ U, b ≠ q₀ → ∃ j ∈ U, j ≠ k ∧ c (iisRun inp E j) = b

private instance instDecidableIsIISDoor (U : Finset V) (inp : V → Input) {R : ℕ}
    (c : IISView V Input R → V) (q₀ : V) (E : Fin R → ISSchedule U) (k : V) :
    Decidable (IsIISDoor U inp c q₀ E k) :=
  inferInstanceAs (Decidable (∀ b ∈ U, b ≠ q₀ → ∃ j ∈ U, j ≠ k ∧ c (iisRun inp E j) = b))

/-- Single-execution door parity from `Cslib.Sperner.odd_card_doors_iff_surjective`. -/
private theorem odd_card_iisDoors_iff_panchromatic {U : Finset V} {inp : V → Input} {R : ℕ}
    {c : IISView V Input R → V} (hc : IsCarrierColoringOn U inp c) {q₀ : V} (hq₀ : q₀ ∈ U)
    (E : Fin R → ISSchedule U) :
    Odd #{k ∈ U | IsIISDoor U inp c q₀ E k} ↔ IsPanchromaticIIS U inp c E := by
  let f : U → U := fun x =>
    ⟨c (iisRun inp E x.val),
      carrier_iisRun_subset inp E x.property (hc U Subset.rfl E x.val x.property)⟩
  let b₀ : U := ⟨q₀, hq₀⟩
  have hsperner := Cslib.Sperner.odd_card_doors_iff_surjective f b₀ rfl
  have hcard_eq : #{k : U | ∀ b ≠ b₀, ∃ j ≠ k, f j = b} =
      #{k ∈ U | IsIISDoor U inp c q₀ E k} := by
    refine card_nbij' (fun x => x.val)
      (fun k => if hk : k ∈ U then ⟨k, hk⟩ else b₀) ?_ ?_ ?_ ?_
    · rintro ⟨k, hk⟩ hx
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hx ⊢
      refine ⟨hk, fun b hbU hbq₀ => ?_⟩
      obtain ⟨⟨j, hjU⟩, hjk, hfj⟩ := hx ⟨b, hbU⟩ (fun h => hbq₀ (congrArg Subtype.val h))
      exact ⟨j, hjU, fun h => hjk (Subtype.ext h), congrArg Subtype.val hfj⟩
    · intro k hk_in
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hk_in ⊢
      obtain ⟨hkU, hdoor⟩ := hk_in
      simp only [hkU, ↓reduceDIte]
      rintro ⟨b, hbU⟩ hbb₀
      obtain ⟨j, hjU, hjk, hcj⟩ := hdoor b hbU (fun h => hbb₀ (Subtype.ext h))
      exact ⟨⟨j, hjU⟩, fun h => hjk (congrArg Subtype.val h), Subtype.ext hcj⟩
    · rintro ⟨k, hk⟩ _
      simp only [hk, ↓reduceDIte]
    · intro k hk_in
      simp only [coe_filter, Set.mem_ofPred_eq] at hk_in
      simp only [hk_in.1, ↓reduceDIte]
  have hsurj_iff : Function.Surjective f ↔ IsPanchromaticIIS U inp c E := by
    constructor
    · intro hsurj b hbU
      obtain ⟨⟨p, hpU⟩, hp⟩ := hsurj ⟨b, hbU⟩
      exact ⟨p, hpU, congrArg Subtype.val hp⟩
    · intro hpanch ⟨b, hbU⟩
      obtain ⟨p, hpU, hp⟩ := hpanch b hbU
      exact ⟨⟨p, hpU⟩, Subtype.ext hp⟩
  rw [← hcard_eq, hsperner, hsurj_iff]

/-- Subface-relativized induction helper proving odd panchromatic execution parity on `U` under
`IsCarrierColoringOn U inp c`. -/
private theorem odd_card_panchromatic_iis_of_on (U : Finset V) (inp : V → Input) {R : ℕ}
    {c : IISView V Input R → V} (hc : IsCarrierColoringOn U inp c) :
    Odd #{E : Fin R → ISSchedule U | IsPanchromaticIIS U inp c E} := by
  induction hn : #U generalizing U with
  | zero =>
    rw [card_eq_zero] at hn
    subst hn
    have huniv : (univ : Finset (Fin R → ISSchedule (∅ : Finset V))) =
        {fun _ => ISSchedule.empty} := by
      ext E
      simp only [mem_univ, mem_singleton, true_iff]
      funext r
      ext1
      exact (E r).blocks_eq_nil_of_empty
    have hall : ∀ E : Fin R → ISSchedule (∅ : Finset V), IsPanchromaticIIS ∅ inp c E :=
      fun _ _ hb => absurd hb (notMem_empty _)
    rw [filter_true_of_mem fun E _ => hall E, huniv, card_singleton]
    exact odd_one
  | succ n ih =>
    obtain ⟨q₀, hq₀⟩ := card_pos.mp (by omega : 0 < #U)
    set S := (univ : Finset (Fin R → ISSchedule U))
    set D := (S ×ˢ U).filter fun p => IsIISDoor U inp c q₀ p.1 p.2
    -- Double-count doors across all executions `E ∈ S`
    have hD_parity : Odd #{E ∈ S | IsPanchromaticIIS U inp c E} ↔ Odd #D := by
      have hsum : #D = ∑ E ∈ S, #{k ∈ U | IsIISDoor U inp c q₀ E k} := by
        rw [card_filter, sum_product]
        simp only [card_filter]
      rw [hsum, odd_sum_iff_odd_card_odd]
      simp only [odd_card_iisDoors_iff_panchromatic hc hq₀]
    rw [hD_parity, ← card_filter_add_card_filter_not fun p => ¬ IsBoundaryExecAt p.2 p.1]
    refine Even.add_odd ?_ ?_
    · -- 1. Interior doors (`¬ IsBoundaryExecAt k E`) pair up without fixed points under
      --    `flipIISExec`!
      let g : (Fin R → ISSchedule U) × V → (Fin R → ISSchedule U) × V :=
        fun p => if hk : p.2 ∈ U then (flipIISExec hk p.1, p.2) else p
      have hg : ∀ (E : Fin R → ISSchedule U) {k : V} (hk : k ∈ U),
          g (E, k) = (flipIISExec hk E, k) := by
        intro E k hk
        dsimp only [g]
        simp only [hk, ↓reduceDIte]
      refine Cslib.Sperner.even_card_of_involution g ?_ ?_ ?_
      · rintro ⟨E, k⟩ hp
        simp only [D, mem_filter, mem_product, S, mem_univ, true_and] at hp ⊢
        obtain ⟨⟨hkU, hdoor⟩, hint⟩ := hp
        rw [hg E hkU]
        refine ⟨⟨hkU, fun b hbU hbq₀ => ?_⟩, ?_⟩
        · obtain ⟨j, hjU, hjk, hcj⟩ := hdoor b hbU hbq₀
          exact ⟨j, hjU, hjk, (congrArg c (iisRun_flipIISExec_of_ne hkU inp E hjk)).trans hcj⟩
        · rwa [isBoundaryExecAt_flipIISExec_iff hkU]
      · rintro ⟨E, k⟩ hp
        simp only [D, mem_filter, mem_product, S, mem_univ, true_and] at hp
        have hkU := hp.1.1
        rw [hg E hkU, hg _ hkU, flipIISExec_flipIISExec]
      · rintro ⟨E, k⟩ hp
        simp only [D, mem_filter, mem_product, S, mem_univ, true_and] at hp
        obtain ⟨⟨hkU, -⟩, hint⟩ := hp
        rw [hg E hkU]
        intro hcon
        exact hint ((flipIISExec_eq_self_iff hkU E).mp (congrArg Prod.fst hcon))
    · -- 2. Boundary doors (`IsBoundaryExecAt k E`) force `k = q₀` and biject with panchromatic
      --    executions on `U.erase q₀`!
      simp only [Classical.not_not]
      have hU₀_card : #(U.erase q₀) = n := by
        rw [card_erase_of_mem hq₀, hn, Nat.add_sub_cancel]
      have hc₀ : IsCarrierColoringOn (U.erase q₀) inp c :=
        fun U' hU' => hc U' (Subset.trans hU' (erase_subset q₀ U))
      -- Every boundary door `(E, k)` must have `k = q₀`!
      have hforce_q₀ : ∀ {E : Fin R → ISSchedule U} {k : V},
          k ∈ U → IsIISDoor U inp c q₀ E k → IsBoundaryExecAt k E → k = q₀ := by
        intro E k hkU hdoor hbound
        by_contra hkq₀
        obtain ⟨j, hjU, hjk, hcj⟩ := hdoor k hkU hkq₀
        let E₀ : Fin R → ISSchedule (U.erase k) := fun r => (E r).dropBoundary (hbound r)
        have hj_er : j ∈ U.erase k := mem_erase.mpr ⟨hjk, hjU⟩
        have hview := iisRun_dropBoundary_of_ne inp E hbound hjk
        have hmem_er : c (iisRun inp E j) ∈ U.erase k := by
          rw [← hview]
          exact carrier_iisRun_subset inp E₀ hj_er (hc (U.erase k) (erase_subset k U) E₀ j hj_er)
        exact notMem_erase k U (hcj ▸ hmem_er)
      convert ih (U.erase q₀) hc₀ hU₀_card using 1
      refine card_nbij'
        (fun p => if hb : IsBoundaryExecAt q₀ p.1 then (boundaryExecEquiv hq₀ R) ⟨p.1, hb⟩
                  else fun _ => ISSchedule.ofImmediateSnapshotOn
                    (fun x => if x ∈ U.erase q₀ then U.erase q₀ else ∅)
                    ⟨fun _ hx => by simp only [hx, ↓reduceIte],
                     fun _ hx => by simp only [hx, ↓reduceIte, Subset.rfl],
                     fun _ hx => by simp only [hx, ↓reduceIte],
                     fun _ hx _ hy => by simp only [hx, hy, ↓reduceIte, Subset.rfl, or_self],
                     fun _ hx _ hy _ => by simp only [hx, hy, ↓reduceIte, Subset.rfl]⟩)
        (fun E₀ => ((boundaryExecEquiv hq₀ R).symm E₀ |>.val, q₀)) ?_ ?_ ?_ ?_
      · rintro ⟨E, k⟩ hp
        simp only [D, coe_filter, mem_filter, mem_product, S, mem_univ, true_and,
          Set.mem_ofPred_eq] at hp ⊢
        obtain ⟨⟨hkU, hdoor⟩, hbound⟩ := hp
        have hkeq : k = q₀ := hforce_q₀ hkU hdoor hbound
        subst hkeq
        simp only [hbound, ↓reduceDIte]
        intro b hb_er
        obtain ⟨hbq₀, hbU⟩ := mem_erase.mp hb_er
        obtain ⟨j, hjU, hjq₀, hcj⟩ := hdoor b hbU hbq₀
        refine ⟨j, mem_erase.mpr ⟨hjq₀, hjU⟩, ?_⟩
        change c (iisRun inp (fun r => (E r).dropBoundary (hbound r)) j) = b
        rw [iisRun_dropBoundary_of_ne inp E hbound hjq₀]
        exact hcj
      · intro E₀ hE₀
        simp only [D, coe_filter, mem_filter, mem_product, S, mem_univ, true_and,
          Set.mem_ofPred_eq] at hE₀ ⊢
        set E := ((boundaryExecEquiv hq₀ R).symm E₀).val
        have hbound : IsBoundaryExecAt q₀ E := ((boundaryExecEquiv hq₀ R).symm E₀).property
        have hdrop : (fun r => (E r).dropBoundary (hbound r)) = E₀ :=
          (boundaryExecEquiv hq₀ R).right_inv E₀
        refine ⟨⟨hq₀, fun b hbU hbq₀ => ?_⟩, hbound⟩
        obtain ⟨j, hj_er, hcj⟩ := hE₀ b (mem_erase.mpr ⟨hbq₀, hbU⟩)
        obtain ⟨hjq₀, hjU⟩ := mem_erase.mp hj_er
        refine ⟨j, hjU, hjq₀, ?_⟩
        rw [← iisRun_dropBoundary_of_ne inp E hbound hjq₀, hdrop]
        exact hcj
      · rintro ⟨E, k⟩ hp
        simp only [D, coe_filter, mem_filter, mem_product, S, mem_univ, true_and,
          Set.mem_ofPred_eq] at hp
        obtain ⟨⟨hkU, hdoor⟩, hbound⟩ := hp
        have hkeq : k = q₀ := hforce_q₀ hkU hdoor hbound
        subst hkeq
        simp only [hbound, ↓reduceDIte, Equiv.symm_apply_apply]
      · intro E₀ _
        have hbound : IsBoundaryExecAt q₀ ((boundaryExecEquiv hq₀ R).symm E₀).val :=
          ((boundaryExecEquiv hq₀ R).symm E₀).property
        dsimp only
        simp only [hbound, ↓reduceDIte]
        exact (boundaryExecEquiv hq₀ R).apply_symm_apply E₀

/-- Iterated immediate snapshot (`IIS`) chromatic-subdivision Sperner parity step for #7504 (after
[Herlihy and Shavit, Lemma 3.2, p. 880, and §5.2, Definitions 5.3–5.4,
pp. 897–898][HerlihyShavit1999]): for every carrier-valid coloring `c : IISView V Input R → V`
(`∀ v, c v ∈ v.carrier`), finite process set `U : Finset V`, and input `inp : V → Input`, the
number of `R`-round `IIS` executions on `U` hitting all `#U` colors is odd. -/
theorem odd_card_panchromatic_iis {R : ℕ} {c : IISView V Input R → V} (hc : IsCarrierColoring c)
    (U : Finset V) (inp : V → Input) :
    Odd #{E : Fin R → ISSchedule U | IsPanchromaticIIS U inp c E} :=
  odd_card_panchromatic_iis_of_on U inp (hc.on U inp)

/-- Iterated immediate snapshot (`IIS`) panchromatic existence step for #7504 (after
[Herlihy and Shavit, Lemma 3.2, p. 880][HerlihyShavit1999]): every carrier-valid coloring admits at
least one panchromatic `R`-round `IIS` execution on `U`. -/
theorem exists_panchromatic_iis {R : ℕ} {c : IISView V Input R → V} (hc : IsCarrierColoring c)
    (U : Finset V) (inp : V → Input) :
    ∃ E : Fin R → ISSchedule U, IsPanchromaticIIS U inp c E := by
  obtain ⟨E, hE⟩ := card_pos.mp (odd_card_panchromatic_iis hc U inp).pos
  exact ⟨E, (mem_filter.mp hE).2⟩

end SpernerParity

/-! ### Part 4: Wait-free `k`-set agreement impossibility in `IIS` and `t < k` quorum contrast -/

section SetAgreementImpossibility

/-- An `R`-round `IIS` protocol `P : IISProtocol V Val R` solves wait-free `k`-set agreement
([HerlihyShavit1999], §3.3, p. 879; [BorowskyGafni1993]; [SaksZaharoglou2000]) when:
1. **Validity (`P.IsValid`):** every decided value is the initial input of some process, and
2. **`k`-Agreement:** in every execution, at most `k` distinct values are decided across all
   processes. -/
@[expose]
def IISProtocol.SolvesSetAgreement {V Val : Type*} [Fintype V] [DecidableEq V] [DecidableEq Val]
    {R : ℕ} (P : IISProtocol V Val R) (k : ℕ) : Prop :=
  P.IsValid ∧
    ∀ (inp : V → Val) (E : Fin R → ISSchedule (univ : Finset V)),
      #((univ : Finset V).image fun p => P.decide p (iisRun inp E p)) ≤ k

/-- Iterated immediate snapshot (`IIS`) impossibility step for #7504 (after
[Herlihy and Shavit, §3.3, Theorem 3.3, p. 881][HerlihyShavit1999]; see also [BorowskyGafni1993]
and [SaksZaharoglou2000]): on `Fintype.card V ≥ k + 1` processes with `Fintype.card Val ≥ k + 1`
possible input values, no `R`-round deterministic `IIS` protocol solves wait-free `k`-set agreement
(the general asynchronous read/write shared-memory to `IIS` reduction remains open in #7504). -/
theorem not_solvesSetAgreement_iis {V Val : Type*} [Fintype V] [DecidableEq V] [Fintype Val]
    [DecidableEq Val] {k R : ℕ} (hV : k + 1 ≤ Fintype.card V) (hVal : k + 1 ≤ Fintype.card Val)
    (P : IISProtocol V Val R) :
    ¬ P.SolvesSetAgreement k := by
  classical
  rintro ⟨hvalid, hagree⟩
  have hcarrier := P.isCarrierValid_of_isValid hvalid
  -- Choose `k + 1` active processes `U` and `k + 1` distinct input values `W`
  obtain ⟨U, -, hU_card⟩ := exists_subset_card_eq (s := (univ : Finset V)) hV
  obtain ⟨W, -, hW_card⟩ := exists_subset_card_eq (s := (univ : Finset Val)) hVal
  obtain ⟨p₀, hp₀⟩ := card_pos.mp (by omega : 0 < #U)
  let e : U ≃ W := Finset.equivOfCardEq (hU_card.trans hW_card.symm)
  let inp : V → Val := fun p => if hp : p ∈ U then (e ⟨p, hp⟩).val else (e ⟨p₀, hp₀⟩).val
  have hinj_U : ∀ {p₁ p₂ : V}, p₁ ∈ U → p₂ ∈ U → inp p₁ = inp p₂ → p₁ = p₂ := by
    intro p₁ p₂ hp₁ hp₂ heq
    dsimp only [inp] at heq
    simp only [hp₁, hp₂, ↓reduceDIte] at heq
    exact congrArg Subtype.val (e.injective (Subtype.ext heq))
  -- Pull back decisions along `inp` on `U` to obtain a carrier-valid coloring `c : IISView → V`
  let invInp : Val → V := fun val =>
    if h : ∃ q ∈ U, inp q = val then Classical.choose h else p₀
  let c : IISView V Val R → V := fun v => invInp (P.decide v.proc v)
  have hc_spec : ∀ U' ⊆ U, ∀ (E' : Fin R → ISSchedule U') {p : V} (hp : p ∈ U'),
      c (iisRun inp E' p) ∈ (iisRun inp E' p).carrier ∧
        inp (c (iisRun inp E' p)) = P.decide p (iisRun inp E' p) := by
    intro U' hU' E' p hp
    let E_ext : Fin R → ISSchedule (univ : Finset V) := fun r => (E' r).extendToUniv
    have hpU : p ∈ U := hU' hp
    have hview := iisRun_extendToUniv_of_mem inp E' hp
    have hmem_img := hcarrier inp E_ext p
    rw [hview] at hmem_img
    obtain ⟨q, hq_car, hq_inp⟩ := mem_image.mp hmem_img
    have hqU : q ∈ U := hU' (carrier_iisRun_subset inp E' hp hq_car)
    have hex : ∃ r ∈ U, inp r = P.decide p (iisRun inp E' p) := ⟨q, hqU, hq_inp⟩
    have hproc_eq : P.decide (iisRun inp E' p).proc (iisRun inp E' p) =
        P.decide p (iisRun inp E' p) := by
      rw [iisRun_proc]
    have hc_eq : c (iisRun inp E' p) = Classical.choose hex := by
      dsimp only [c, invInp]
      rw [hproc_eq]
      simp only [hex, ↓reduceDIte]
    obtain ⟨hrU, hr_inp⟩ := Classical.choose_spec hex
    have hr_eq_q : Classical.choose hex = q := hinj_U hrU hqU (hr_inp.trans hq_inp.symm)
    exact ⟨hc_eq.trans hr_eq_q ▸ hq_car, hc_eq ▸ hr_inp⟩
  have hc_on : IsCarrierColoringOn U inp c :=
    fun U' hU' E' p hp => (hc_spec U' hU' E' hp).1
  -- Apply Odd Panchromatic `IIS` Execution Parity!
  obtain ⟨E, hpanch⟩ := card_pos.mp (odd_card_panchromatic_iis_of_on U inp hc_on).pos
  have hpanch' : IsPanchromaticIIS U inp c E := (mem_filter.mp hpanch).2
  let E_ext : Fin R → ISSchedule (univ : Finset V) := fun r => (E r).extendToUniv
  -- Every value in `U.image inp` is decided in `E_ext`!
  have hsub : U.image inp ⊆ (univ : Finset V).image (fun p => P.decide p (iisRun inp E_ext p)) := by
    intro val hval
    obtain ⟨q, hqU, rfl⟩ := mem_image.mp hval
    obtain ⟨p, hpU, hcp⟩ := hpanch' q hqU
    have hdec : P.decide p (iisRun inp E_ext p) = inp q := by
      rw [iisRun_extendToUniv_of_mem inp E hpU, ← (hc_spec U Subset.rfl E hpU).2, hcp]
    exact mem_image.mpr ⟨p, mem_univ p, hdec⟩
  have hcard_img : #(U.image inp) = k + 1 := by
    rw [card_image_of_injOn (fun x hx y hy hxy => hinj_U hx hy hxy), hU_card]
  have hle : k + 1 ≤ k := by
    rw [← hcard_img]
    exact le_trans (card_le_card hsub) (hagree inp E_ext)
  omega

/-- Iterated immediate snapshot (`IIS`) solvability threshold step for #7504: for every `k : ℕ`
and finite types `V` and `Val`, there exists an `R`-round `IIS` protocol solving wait-free `k`-set
agreement if and only if `Fintype.card V ≤ k ∨ Fintype.card Val ≤ k`. -/
theorem exists_iis_setAgreement_iff (V Val : Type*) [Fintype V] [DecidableEq V]
    [Fintype Val] [DecidableEq Val] (k : ℕ) :
    (∃ (R : ℕ) (P : IISProtocol V Val R), P.SolvesSetAgreement k) ↔
      Fintype.card V ≤ k ∨ Fintype.card Val ≤ k := by
  constructor
  · rintro ⟨R, P, hsol⟩
    by_contra hnot
    push Not at hnot
    exact not_solvesSetAgreement_iis hnot.1 hnot.2 P hsol
  · intro hbound
    -- `0`-round protocol: every process immediately decides its own initial input!
    refine ⟨0, ⟨fun _ v => InitView.input v⟩, ?_, ?_⟩
    · intro inp E p
      exact mem_image_of_mem inp (mem_univ p)
    · intro inp E
      rcases hbound with hV | hVal
      · exact le_trans card_image_le (by simpa only [card_univ] using hV)
      · exact le_trans (card_le_univ _) hVal

/-! ### Contrast: positive one-round `(n - t)`-quorum `k`-set agreement when `t < k` -/

/-- A one-round `(n - t)`-quorum schedule over `V`: at most `t` processes are missed, so every
deciding process `p` hears from a quorum `Q p : Finset V` containing `p` of cardinality at least
`Fintype.card V - t`. -/
@[expose]
def IsQuorumSchedule {V : Type*} [Fintype V] (t : ℕ) (Q : V → Finset V) : Prop :=
  (∀ p : V, p ∈ Q p) ∧ ∀ p : V, Fintype.card V - t ≤ #(Q p)

/-- Local quorum view observed by `p` in a one-round `(n - t)`-quorum exchange: the set of
`(process, input)` pairs from `Q p`. -/
@[expose]
def quorumRun {V Val : Type*} [DecidableEq V] [DecidableEq Val] (inp : V → Val)
    (Q : V → Finset V) (p : V) : Finset (V × Val) :=
  (Q p).image fun q => (q, inp q)

/-- One-round deterministic quorum decision protocol. -/
structure QuorumProtocol (V Val : Type*) where
  /-- Per-process decision rule applied to the received `(process, input)` set. -/
  decide : V → Finset (V × Val) → Val

/-- A `QuorumProtocol` solves `(n - t)`-quorum `k`-set agreement when in every
`IsQuorumSchedule t Q` schedule, every process decides an observed input from `Q p` and at most `k`
distinct values are decided globally. -/
@[expose]
def QuorumProtocol.SolvesSetAgreement {V Val : Type*} [Fintype V] [DecidableEq V]
    [DecidableEq Val] (P : QuorumProtocol V Val) (t k : ℕ) : Prop :=
  (∀ (inp : V → Val) (Q : V → Finset V), IsQuorumSchedule t Q →
      ∀ p : V, P.decide p (quorumRun inp Q p) ∈ (Q p).image inp) ∧
    (∀ (inp : V → Val) (Q : V → Finset V), IsQuorumSchedule t Q →
      #((univ : Finset V).image fun p => P.decide p (quorumRun inp Q p)) ≤ k)

/-- Original one-round `(n - t)`-quorum contrast step for #7504: whenever `t < k`, a fixed leader
set `L` of size `min (t + 1) |V|` intersects every quorum `Q p` of size `≥ |V| - t`, so adopting
any heard leader's input solves `(n - t)`-quorum `k`-set agreement in one round. -/
theorem exists_quorumSetAgreement_of_lt (V Val : Type*) [Fintype V] [DecidableEq V]
    [DecidableEq Val] [Nonempty Val] {t k : ℕ} (htk : t < k) :
    ∃ P : QuorumProtocol V Val, P.SolvesSetAgreement t k := by
  classical
  have hmin_le : min (t + 1) (Fintype.card V) ≤ #(univ : Finset V) := by
    rw [card_univ]
    exact Nat.min_le_right _ _
  obtain ⟨L, -, hL_card⟩ := exists_subset_card_eq hmin_le
  let dflt : Val := Classical.arbitrary Val
  let P : QuorumProtocol V Val :=
    { decide := fun _ view =>
        if h : ∃ qv ∈ view, qv.1 ∈ L then (Classical.choose h).2 else dflt }
  -- Key pigeonhole intersection: every quorum `Q p` of size `≥ |V| - t` meets `L`!
  have hmeet : ∀ {Q : V → Finset V}, IsQuorumSchedule t Q → ∀ p : V, (Q p ∩ L).Nonempty := by
    intro Q hQ p
    by_cases hle : Fintype.card V ≤ t + 1
    · have hL_univ : L = univ := eq_univ_of_card L (hL_card.trans (Nat.min_eq_right hle))
      rw [hL_univ, inter_univ]
      exact ⟨p, hQ.1 p⟩
    · have hL_eq : #L = t + 1 := hL_card.trans (Nat.min_eq_left (by omega))
      by_contra hemp
      rw [not_nonempty_iff_eq_empty, ← disjoint_iff_inter_eq_empty] at hemp
      have hcard_u : #(Q p ∪ L) ≤ Fintype.card V := card_le_univ _
      rw [card_union_of_disjoint hemp, hL_eq] at hcard_u
      have hQp := hQ.2 p
      omega
  have hdec : ∀ {inp : V → Val} {Q : V → Finset V}, IsQuorumSchedule t Q → ∀ p : V,
      ∃ q ∈ Q p, q ∈ L ∧ P.decide p (quorumRun inp Q p) = inp q := by
    intro inp Q hQ p
    obtain ⟨q₀, hq₀⟩ := hmeet hQ p
    have hex : ∃ qv ∈ quorumRun inp Q p, qv.1 ∈ L :=
      ⟨(q₀, inp q₀), mem_image_of_mem _ (mem_inter.mp hq₀).1, (mem_inter.mp hq₀).2⟩
    obtain ⟨hqv_in, hqvL⟩ := Classical.choose_spec hex
    obtain ⟨q, hqQ, hq_eq⟩ := mem_image.mp hqv_in
    rw [← hq_eq] at hqvL
    refine ⟨q, hqQ, hqvL, ?_⟩
    dsimp only [P]
    simp only [hex, ↓reduceDIte, ← hq_eq]
  refine ⟨P, fun inp Q hQ p => ?_, fun inp Q hQ => ?_⟩
  · obtain ⟨q, hqQ, -, hq⟩ := hdec hQ p
    exact hq ▸ mem_image_of_mem inp hqQ
  · have hsub : ((univ : Finset V).image fun p => P.decide p (quorumRun inp Q p)) ⊆
        L.image inp := by
      intro val hval
      obtain ⟨p, -, rfl⟩ := mem_image.mp hval
      obtain ⟨q, -, hqL, hq⟩ := hdec hQ p
      exact hq ▸ mem_image_of_mem inp hqL
    calc #((univ : Finset V).image fun p => P.decide p (quorumRun inp Q p))
        ≤ #(L.image inp) := card_le_card hsub
      _ ≤ #L := card_image_le
      _ = min (t + 1) (Fintype.card V) := hL_card
      _ ≤ t + 1 := Nat.min_le_left _ _
      _ ≤ k := htk

end SetAgreementImpossibility

end Cslib.Distributed.SetAgreement
