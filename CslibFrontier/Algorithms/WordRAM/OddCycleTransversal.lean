/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.OddCycleTransversal.Layout
public import CslibFrontier.Computability.WordRAM.Time
import CslibFrontier.Algorithms.WordRAM.OddCycleTransversal.Outer
import CslibFrontier.Algorithms.WordRAM.OddCycleTransversal.Validity
import CslibFrontier.Computability.WordRAM.Realization.Program.Standard
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Odd cycle transversal by iterative compression on the Word-RAM

Implements the iterative-compression odd-cycle-transversal algorithm of Reed, Smith and Vetta
`[ReedSmithVetta2004]` with Hüffner's three-way compression branching `[Hueffner2009]` and
`[CyganEtAl2015, Section 4.4]` as a single uniform flat program over `Cslib.WordRAM.Basis.exact`.
`Basis.exact` supplies unit-cost multiplication for the `n × n` adjacency matrix and
`(2n + 2) × (2n + 2)` split-network flow matrix index arithmetic.

## Overview

Given an `n`-vertex simple graph `G` serialized in `State.init (encodeInput G k)` (`n :: k ::
encodeAdjMatrix G`), the program allocates workspace up to `octWorkspace n = 5 * n ^ 2 + 21 * n +
11` and maintains a `0`/`1` indicator of an odd cycle transversal `S` of `prefixGraph G m` (`|S| ≤
k`) at `sepAddr n 0 .. sepAddr n (n - 1)` together with a proper Boolean colouring off `S` at
`colAddr n 0 .. colAddr n (n - 1)`:

1. **Outer vertex-addition loop (`octStep`, `m = 0 .. n - 1`):** forms `W = S ∪ {m}` and compacts
   `W` into `wListBase`. When `|W| ≤ k`, `W` is accepted directly; otherwise `|W| = k + 1` and
   `compressProg` enumerates all `3 ^ |W|` three-way guesses on `W` via a base-3 odometer.
2. **Compression leaf (`leafProg`) and unit-capacity vertex-split max-flow (`minSepProg`):** checks
   properness on the kept part of `W`, marks keep and flip terminals outside `W`, runs `n` rounds of
   layered BFS + unit augmentation on the `(2n + 2)`-vertex split network, extracts the minimum
   vertex separator from the final residual reachable cut, and commits `D ∪ X` and the updated
   colouring when `|D| + |X| ≤ k`.

The implementation is factored under `CslibFrontier.Algorithms.WordRAM.OddCycleTransversal`
into `Layout` (pure input encoding and workspace offsets; publicly re-exported here), `Range`,
`NetworkProg`, `CompressProg`, parallel verification modules `MinSep`, `Validity`, `Cost`, and
`LeafSubroutines`, `CompressSpec`, and `Outer` (all imported privately here so downstream callers
load only the slim public API).

## Main definitions

* `Cslib.Algorithms.WordRAM.OddCycleTransversal.encodeAdjMatrix`,
  `Cslib.Algorithms.WordRAM.OddCycleTransversal.encodeInput`: row-major `0`/`1` adjacency matrix and
  prefixed input word list `n :: k :: encodeAdjMatrix G`, with the layout lemmas
  `length_encodeAdjMatrix`, `length_encodeInput` and `getElem_encodeAdjMatrix`.
* `Cslib.Algorithms.WordRAM.OddCycleTransversal.sepAddr`,
  `Cslib.Algorithms.WordRAM.OddCycleTransversal.colAddr`,
  `Cslib.Algorithms.WordRAM.OddCycleTransversal.octWorkspace`: output transversal/colouring cell
  addresses and total memory frontier `5 * n ^ 2 + 21 * n + 11`.
* `Cslib.Algorithms.WordRAM.OddCycleTransversal.OctInstance`,
  `Cslib.Algorithms.WordRAM.OddCycleTransversal.OctInstance.encode`,
  `Cslib.Algorithms.WordRAM.OddCycleTransversal.OctInstance.Yes`: packaged decision instances,
  encoding, and yes-set for `UniformDecidableInTime`.

## Main results

* `Cslib.Algorithms.WordRAM.OddCycleTransversal.exists_oct_program`: a single uniform flat program
  over `Basis.exact` decides whether `G` has an odd cycle transversal of size at most `k` within
  `C * 3 ^ k * (n + 1) ^ 5` instructions whenever `Fits w (octWorkspace n)` and `Fits w k`, and on
  yes-instances materializes a valid transversal of size `≤ k` and a proper `2`-colouring off it in
  final machine memory.
* `Cslib.Algorithms.WordRAM.OddCycleTransversal.uniformDecidableInTime_oct`,
  `Cslib.Algorithms.WordRAM.OddCycleTransversal.uniformDecidableInTimeLogWord_oct`: uniform FPT
  `O(3 ^ k · n ^ 5)` decision certificates under explicit workspace fit and under the
  transdichotomous logarithmic word-size convention.

## References

* [B. Reed, K. Smith, A. Vetta, *Finding odd cycle transversals*][ReedSmithVetta2004]
* [F. Hüffner, *Algorithm engineering for optimal graph bipartization*][Hueffner2009]
* [M. Cygan, F. V. Fomin, Ł. Kowalik, D. Lokshtanov, D. Marx, M. Pilipczuk, M. Pilipczuk,
  S. Saurabh, *Parameterized Algorithms*][CyganEtAl2015]
-/

public section

namespace Cslib.Algorithms.WordRAM.OddCycleTransversal

open SimpleGraph SimpleGraph.OddCycleTransversal
open Cslib.Algorithms.Lean.IterativeCompression
open Cslib.DataStructure Cslib.WordRAM Cslib.WordRAM.Realization

/-- **Word-RAM odd cycle transversal by iterative compression**: a single uniform flat program over
`Basis.exact` decides whether an `n`-vertex simple graph `G` has an odd cycle transversal of size at
most `k` within `C * 3 ^ k * (n + 1) ^ 5` instructions whenever `Fits w (octWorkspace n)` and
`Fits w k`, agreeing with `Cslib.Algorithms.Lean.IterativeCompression.oct` and materializing a
valid transversal at `sepAddr n` and a proper Boolean colouring off it at `colAddr n` on
yes-instances. -/
theorem exists_oct_program :
    ∃ r C pc : ℕ, 0 < C ∧ ∃ prog : Program .exact r,
      ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k w : ℕ),
        Fits w (octWorkspace n) → Fits w k →
        ∃ (y : Data r) (steps res : ℕ),
          Runs w prog (State.init (encodeInput G k)) ⟨pc, y⟩ steps ∧
          step w prog ⟨pc, y⟩ = .halt res ∧
          steps + 1 ≤ C * 3 ^ k * (n + 1) ^ 5 ∧
          res ≤ 1 ∧
          (res = 1 ↔ (oct G k).isSome) ∧
          (res = 1 ↔
            ∃ T : Finset (Fin n), G.IsOddCycleTransversal (T : Set (Fin n)) ∧ T.card ≤ k) ∧
          (res = 1 →
            (∀ v : Fin n, y.mem (sepAddr n v.1) ≤ 1 ∧ y.mem (colAddr n v.1) ≤ 1) ∧
            let S : Finset (Fin n) := Finset.univ.filter fun v => y.mem (sepAddr n v.1) = 1
            G.IsOddCycleTransversal (S : Set (Fin n)) ∧ S.card ≤ k ∧
              ∀ u v : Fin n, G.Adj u v → u ∉ S → v ∉ S →
                (y.mem (colAddr n u.1) == 1) ≠ (y.mem (colAddr n v.1) == 1)) := by
  obtain ⟨r, C₀, pc, prog, frontier, _, hprog⟩ :=
    octProg_realizes.exists_standard_init_program_state_from_words 0
  refine ⟨r, 681 * C₀ + 2, pc, by omega, prog, ?_⟩
  intro n G _ k w hw hk
  let words := encodeInput G k
  have hlen_fit : Fits w (words.length + 1) := by
    rw [length_encodeInput]
    exact hw.of_le (by dsimp only [octWorkspace]; omega)
  have hin_fit : InputFits w words := inputFits_encodeInput G hw hk
  have hs₀_1 : (Memory.State.init words).mem 1 = n := rfl
  have hsafe : (Memory.State.init words).frontier =
      3 + (Memory.State.init words).mem 1 * (Memory.State.init words).mem 1 ∧
      Fits w (octWorkspace ((Memory.State.init words).mem 1)) := by
    rw [hs₀_1]
    exact ⟨by simp [Memory.State.init, words, length_encodeInput]; omega, hw⟩
  have hv := validHistory_octProg (G := G) hw hk
  obtain ⟨y, steps, hruns, hhalt, hmem, _, hbound⟩ :=
    hprog w () words (fun j => Fin.elim0 j) (Nat.zero_le _) hlen_fit hin_fit hsafe hv
  rw [clientResult_width w (octProg ())] at hhalt
  rw [clientState_width w (octProg ())] at hmem
  obtain ⟨hmc, hres_le, hres_iff, hres_oct⟩ := octProg_spec_and_cost G k
  set res := (Memory.spec 0).clientResult (Memory.State.init words) (octProg ())
  have hout_eq : WordEncoding.encode (α := ℕ) res 0 = res := rfl
  rw [hout_eq] at hhalt
  have hymem : y.mem = ((Memory.spec 0).clientState (Memory.State.init words) (octProg ())).mem :=
    congrArg Memory.State.mem hmem
  have hpow3 : 1 ≤ 3 ^ k := Nat.one_le_pow k 3 (by decide)
  have hp5 : 1 ≤ (n + 1) ^ 5 := Nat.one_le_pow 5 (n + 1) (Nat.succ_pos n)
  have h1_le : 1 ≤ 3 ^ k * (n + 1) ^ 5 := Nat.mul_le_mul hpow3 hp5
  have hsteps_le : steps + 1 ≤ (681 * C₀ + 2) * 3 ^ k * (n + 1) ^ 5 := by
    dsimp only [words] at hbound
    calc steps + 1
        ≤ C₀ * (memoryCost (octProg ()) (Memory.State.init (encodeInput G k)) + 0 + 1) + 1 := hbound
      _ ≤ C₀ * (680 * 3 ^ k * (n + 1) ^ 5 + 1) + 1 :=
          Nat.add_le_add_right (Nat.mul_le_mul_left C₀ (by omega)) 1
      _ ≤ C₀ * (681 * 3 ^ k * (n + 1) ^ 5) + 2 * (3 ^ k * (n + 1) ^ 5) := by nlinarith
      _ = (681 * C₀ + 2) * 3 ^ k * (n + 1) ^ 5 := by ring
  refine ⟨y, steps, res, hruns, hhalt, hsteps_le, hres_le,
    hres_iff.trans oct_isSome_iff.symm, hres_iff, fun h1 => ?_⟩
  obtain ⟨h01, hcard, hprop⟩ := hres_oct h1
  have hsep_addr : ∀ v : Fin n, y.mem (sepAddr n v.1) =
      ((Memory.spec 0).clientState (Memory.State.init words) (octProg ())).mem
        (sepBase n + v.1) := fun v => by rw [hymem]; rfl
  have hcol_addr : ∀ v : Fin n, y.mem (colAddr n v.1) =
      ((Memory.spec 0).clientState (Memory.State.init words) (octProg ())).mem
        (colBase n + v.1) := fun v => by rw [hymem]; rfl
  refine ⟨fun v => ⟨(hsep_addr v).trans_le (h01 v).1, (hcol_addr v).trans_le (h01 v).2⟩, ?_⟩
  dsimp only
  have hS_eq : (Finset.univ.filter fun v : Fin n => y.mem (sepAddr n v.1) = 1) =
      (Finset.univ.filter fun v : Fin n =>
        ((Memory.spec 0).clientState (Memory.State.init words) (octProg ())).mem
          (sepBase n + v.1) = 1) := by
    ext v; simp [hsep_addr v]
  rw [hS_eq]
  have hpropG : ∀ u v : Fin n, G.Adj u v →
      u ∉ (Finset.univ.filter fun v : Fin n =>
        ((Memory.spec 0).clientState (Memory.State.init words) (octProg ())).mem
          (sepBase n + v.1) = 1) →
      v ∉ (Finset.univ.filter fun v : Fin n =>
        ((Memory.spec 0).clientState (Memory.State.init words) (octProg ())).mem
          (sepBase n + v.1) = 1) →
      (y.mem (colAddr n u.1) == 1) ≠ (y.mem (colAddr n v.1) == 1) := by
    intro u v hadj hu hv
    rw [hcol_addr u, hcol_addr v]
    rw [← prefixGraph_of_le G (le_refl n)] at hadj
    exact hprop u v hadj hu hv
  exact ⟨isOddCycleTransversal_iff_exists_bool.mpr
      ⟨fun v => y.mem (colAddr n v.1) == 1, fun u v hadj hu hv => hpropG u v hadj hu hv⟩,
    hcard, hpropG⟩

/-! ### Packaged decision problem and `UniformDecidableInTime` certificates -/

/-- Packaged instance of the parameterized odd-cycle-transversal decision problem: a simple graph
`G` on `Fin n` with decidable adjacency together with parameter `k`. -/
structure OctInstance where
  /-- Number of vertices. -/
  n : ℕ
  /-- Solution-size bound. -/
  k : ℕ
  /-- Input simple graph on `Fin n`. -/
  G : SimpleGraph (Fin n)
  /-- Decidable adjacency relation on `G`. -/
  [decAdj : DecidableRel G.Adj]

attribute [instance] OctInstance.decAdj

/-- Word-RAM encoding of an `OctInstance` as `encodeInput x.G x.k`. -/
@[expose] def OctInstance.encode (x : OctInstance) : List ℕ :=
  encodeInput x.G x.k

/-- The yes-instances of `OctInstance`: graphs admitting an odd cycle transversal of size `≤ k`. -/
@[expose] def OctInstance.Yes : Set OctInstance :=
  {x | ∃ T : Finset (Fin x.n), x.G.IsOddCycleTransversal (T : Set (Fin x.n)) ∧ T.card ≤ x.k}

/-- **Uniform FPT Word-RAM decision for odd cycle transversal** at every word width fitting
`octWorkspace x.n`. -/
theorem uniformDecidableInTime_oct :
    ∃ C : ℕ, 0 < C ∧
      UniformDecidableInTime .exact OctInstance.Yes
        (fun _ => OctInstance.encode)
        (fun x _ => C * 3 ^ x.k * (x.n + 1) ^ 5)
        (fun x w => Fits w (octWorkspace x.n)) := by
  obtain ⟨r, C, pc, hC_pos, prog, hprog⟩ := exists_oct_program
  refine ⟨C, hC_pos, r, prog, ?_, ?_⟩
  · intro x w hw hin
    have hk : Fits w x.k :=
      hin.2 x.k (by simp [OctInstance.encode, encodeInput])
    obtain ⟨y, steps, res, hruns, hhalt, htime, hres_le, _, hres_iff, _⟩ :=
      hprog x.G x.k w hw hk
    exact ⟨res, steps + 1, ⟨⟨pc, y⟩, steps, hruns, hhalt, rfl⟩, htime, hres_le, hres_iff⟩
  · intro x
    obtain ⟨w, hlow, hin⟩ :=
      InputFits.exists_width x.encode (Nat.log 2 (octWorkspace x.n) + 1)
    have hw_fit : Fits w (octWorkspace x.n) := by
      have hlt : octWorkspace x.n < 2 ^ (Nat.log 2 (octWorkspace x.n) + 1) :=
        Nat.lt_pow_succ_log_self Nat.one_lt_two _
      exact Fits.mono hlt hlow
    exact ⟨w, hw_fit, hin⟩

/-- **Uniform FPT Word-RAM decision for odd cycle transversal** under the transdichotomous
logarithmic word-size convention (`size x = x.encode.length`). -/
theorem uniformDecidableInTimeLogWord_oct :
    ∃ C : ℕ, 0 < C ∧
      UniformDecidableInTimeLogWord .exact OctInstance.Yes
        (fun _ => OctInstance.encode)
        (fun x => x.encode.length)
        (fun x _ => C * 3 ^ x.k * (x.n + 1) ^ 5) := by
  obtain ⟨C, hC_pos, hdec⟩ := uniformDecidableInTime_oct
  refine ⟨C, hC_pos, 4, by decide, hdec.mono (fun _ _ => le_rfl) ?_
    (inputAdmissible_of_widthIndependent OctInstance.encode _)⟩
  intro x w hw
  have hlt : octWorkspace x.n < (x.encode.length + 1) ^ 4 := by
    simp only [OctInstance.encode, length_encodeInput, octWorkspace]
    let M := x.n * x.n + 3
    have hM : 3 ≤ M := Nat.le_add_left 3 (x.n * x.n)
    have hM2 : 9 ≤ M * M := by nlinarith
    have h3M : 3 * M ≤ M * M := by nlinarith
    have hn_le : x.n ≤ x.n * x.n + 1 := by nlinarith
    calc 5 * (x.n * x.n) + 21 * x.n + 11
        < 9 * (3 * M) := by dsimp only [M]; nlinarith
      _ ≤ (M * M) * (M * M) := Nat.mul_le_mul hM2 h3M
      _ = (2 + x.n * x.n + 1) ^ 4 := by dsimp only [M]; ring
  exact (fits_of_lt_pow hlt).mono hw

end Cslib.Algorithms.WordRAM.OddCycleTransversal
