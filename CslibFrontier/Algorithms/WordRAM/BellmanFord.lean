/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.BellmanFord.Basic
public import CslibFrontier.Algorithms.WordRAM.CSR
public import CslibFrontier.Computability.WordRAM.ListOutput
public import CslibFrontier.Computability.WordRAM.Notation
public import CslibFrontier.Computability.WordRAM.Signed.Comparison
import CslibFrontier.Computability.GenericRAM.Signed.Fits
import CslibFrontier.Computability.WordRAM.CountingLoop
import CslibFrontier.Computability.WordRAM.SymbolicExec
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The Bellman–Ford algorithm on the word RAM

Single-source shortest paths with possibly negative integer edge weights, and detection of
reachable negative cycles, implemented on the standard-basis word RAM
(`Cslib.WordRAM.Basis.standard`) in `O(|V|(|V| + |E|))` instructions
[Bellman][Bellman1958] [Cormen et al., Section 24.1][CLRS2009].

## Representation

An instance (`Cslib.Algorithms.WordRAM.BellmanFord.Instance`) is a directed multigraph on `Fin n`
with adjacency lists `adj : Fin n → List (Fin n × ℤ)` and source `source : Fin n`. Its input word
list (`Instance.encode`) mirrors `Cslib.Algorithms.Dijkstra.ListInstance.encode`: `n`, `source`,
the `n + 1` cumulative edge offsets `offset 0, …, offset n`, and the `m` edges in vertex order as
pairs `(target, Signed.encode weight)` using the width-independent sign-and-magnitude code
`Cslib.WordRAM.Signed.encode`.

Because `Signed.encode z` is never `1` (`encode_ne_one`), tentative distances in `WithTop ℤ` are
stored in one word each (`encodeDist`): `1` for `⊤` and `Signed.encode z` for a finite weight
`z : ℤ`. Signed addition and comparison are executed by `Cslib.WordRAM.Signed.add` and
`Cslib.WordRAM.Signed.less` using ordinary unsigned word instructions.

The program (`Cslib.Algorithms.WordRAM.BellmanFord.program`) writes the tentative distance array at
addresses `[outBase + 1, outBase + 1 + n)` just past the input, runs `n - 1` edge-relaxation
rounds followed by the negative-cycle check pass, writes the output header (`n` if no reachable
negative cycle exists, `0` otherwise) at `outBase`, and halts returning `outBase`. Under the list
output convention `Cslib.WordRAM.ExecutesList`, the output list (`answerWords G`) is `[]` when a
negative cycle is reachable from `source` and `[encodeDist (d 0), …, encodeDist (d (n - 1))]` for
the shortest-path distances `d` otherwise.

## Word-size condition

Across `n - 1` sequential rounds of `m` edge relaxations with edge magnitudes at most
`M = G.maxAbsWeight`, every finite intermediate distance has magnitude at most `(n - 1) m M`, and
every candidate sum `a + c` has magnitude at most `(n m + 1) M`. The envelope
`G.wordBound = 8 * (n + 1) * (m + 2) * (M + 2)` covers input length and words, memory addresses,
and the two extra sign/overflow bits required by `Cslib.WordRAM.Signed.exec_add`.

## Main definitions

* `Cslib.Algorithms.WordRAM.BellmanFord.Instance`: weighted digraph on `Fin n` with integer edge
  weights and source vertex.
* `Cslib.Algorithms.WordRAM.BellmanFord.Instance.encode`,
  `Cslib.Algorithms.WordRAM.BellmanFord.Instance.wordBound`: input word list and word-size envelope.
* `Cslib.Algorithms.WordRAM.BellmanFord.encodeDist`,
  `Cslib.Algorithms.WordRAM.BellmanFord.decodeDist`: single-word encoding of `WithTop ℤ`.
* `Cslib.Algorithms.WordRAM.BellmanFord.answerWords`,
  `Cslib.Algorithms.WordRAM.BellmanFord.decodeAnswer`: output word list and decoder back to
  `Option (Fin G.n → WithTop ℤ)`.
* `Cslib.Algorithms.WordRAM.BellmanFord.Reg.outBase`: output-list header register.
* `Cslib.Algorithms.WordRAM.BellmanFord.solver`,
  `Cslib.Algorithms.WordRAM.BellmanFord.program`: structured and flat word-RAM programs.

## Main results

* `Cslib.Algorithms.WordRAM.BellmanFord.decodeDist_encodeDist`,
  `Cslib.Algorithms.WordRAM.BellmanFord.decodeAnswer_answerWords`: lossless decoding of distances
  and outputs.
* `Cslib.Algorithms.WordRAM.BellmanFord.answerWords_eq_nil_iff`,
  `Cslib.Algorithms.WordRAM.BellmanFord.isShortestDist_of_answerWords_ne_nil`: negative-cycle
  characterization and shortest-path correctness of `answerWords`.
* `Cslib.Algorithms.WordRAM.BellmanFord.solver_spec`,
  `Cslib.Algorithms.WordRAM.BellmanFord.program_spec`,
  `Cslib.Algorithms.WordRAM.BellmanFord.computesListInTime_program`: execution within
  `64 * n * (n + m)` instructions at every word width `w` with `Fits w G.wordBound`.
* `Cslib.Algorithms.WordRAM.BellmanFord.not_readsWidth_program`,
  `Cslib.Algorithms.WordRAM.BellmanFord.isRandFree_program`: width-independence and determinism
  certificates for `program`.

## References

* [R. Bellman, *On a routing problem*][Bellman1958]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to
  Algorithms*][CLRS2009]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.BellmanFord

open Cslib.WordRAM Cslib.WordRAM.Signed
open Cslib.Algorithms.Lean.BellmanFord

/-! ### Single-word encoding of `WithTop ℤ` -/

/-- No integer has sign-and-magnitude code `1`: nonnegative integers have even codes and negative
integers have codes at least `3`. -/
theorem encode_ne_one (z : ℤ) : Signed.encode z ≠ 1 := by
  unfold Signed.encode
  split_ifs with h
  · have : 1 ≤ z.natAbs := Int.natAbs_pos.2 (by omega)
    omega
  · omega

/-- Single-word encoding of `WithTop ℤ`: `1` for `⊤` and `Signed.encode z` for `(z : ℤ)`. -/
def encodeDist : WithTop ℤ → ℕ
  | ⊤ => 1
  | (z : ℤ) => Signed.encode z

/-- Decode a word produced by `encodeDist` back to `WithTop ℤ`. -/
def decodeDist (x : ℕ) : WithTop ℤ :=
  if x = 1 then ⊤ else (Signed.decode x : WithTop ℤ)

@[simp]
theorem encodeDist_top : encodeDist ⊤ = 1 := rfl

@[simp]
theorem encodeDist_coe (z : ℤ) : encodeDist (z : WithTop ℤ) = Signed.encode z := rfl

@[simp]
theorem encodeDist_eq_one_iff (d : WithTop ℤ) : encodeDist d = 1 ↔ d = ⊤ := by
  cases d with
  | top => simp
  | coe z => simp [encode_ne_one z]

@[simp]
theorem decodeDist_encodeDist (d : WithTop ℤ) : decodeDist (encodeDist d) = d := by
  cases d with
  | top => simp [decodeDist]
  | coe z => simp [decodeDist, encode_ne_one z]

theorem encodeDist_injective : Function.Injective encodeDist :=
  Function.LeftInverse.injective decodeDist_encodeDist

/-! ### Problem instances and word encoding -/

/-- A single-source shortest-path instance on `Fin n` with signed integer edge weights. Parallel
edges and self-loops are permitted. -/
structure Instance where
  /-- Number of vertices. -/
  n : ℕ
  /-- Adjacency lists of `(target, weight)` pairs. -/
  adj : Fin n → List (Fin n × ℤ)
  /-- Source vertex. -/
  source : Fin n

namespace Instance

variable (G : Instance)

theorem n_pos : 0 < G.n := Fin.pos G.source

/-- Total number of directed edge entries across all adjacency lists. -/
def m : ℕ := CSR.m G.n G.adj

/-- Maximum absolute edge weight across all edges (`0` when `m = 0`). -/
def maxAbsWeight : ℕ :=
  Finset.univ.sup fun u => ((G.adj u).map (Int.natAbs ∘ Prod.snd)).foldr max 0

theorem natAbs_le_maxAbsWeight {u : Fin G.n} {e : Fin G.n × ℤ} (he : e ∈ G.adj u) :
    e.2.natAbs ≤ G.maxAbsWeight := by
  have hmem : e.2.natAbs ∈ (G.adj u).map (Int.natAbs ∘ Prod.snd) :=
    List.mem_map.2 ⟨e, he, rfl⟩
  have h1 : e.2.natAbs ≤ ((G.adj u).map (Int.natAbs ∘ Prod.snd)).foldr max 0 :=
    List.le_max_of_le hmem le_rfl
  exact h1.trans (Finset.le_sup
    (f := fun u => ((G.adj u).map (Int.natAbs ∘ Prod.snd)).foldr max 0) (Finset.mem_univ u))

/-- Cumulative number of edges leaving vertices `< u`. -/
def offset (u : ℕ) : ℕ :=
  CSR.offset G.n G.adj u

/-- Word-list encoding of `G`: `n`, `source`, the `n + 1` offsets `offset 0, …, offset n`, and
then all edges in vertex order as two words `(target, Signed.encode weight)`. -/
def encode : List ℕ :=
  CSR.encode G.n G.source G.adj Signed.encode

/-- First memory address past the input in `State.init G.encode`, used as the output-list header. -/
def outAddrBase : ℕ := G.n + 2 * G.m + 4

/-- Base address of the `n`-word tentative distance table (`outAddrBase + 1`). -/
private def distAddrBase : ℕ := G.n + 2 * G.m + 5

/-- Word-size envelope covering input length and words, memory addresses, and intermediate signed
path weights of magnitude at most `(n * m + 1) * maxAbsWeight`. -/
def wordBound : ℕ := 8 * (G.n + 1) * (G.m + 2) * (G.maxAbsWeight + 2)

private theorem offset_add_lt_m (u : Fin G.n) {i : ℕ} (hi : i < (G.adj u).length) :
    G.offset u + i < G.m :=
  CSR.offset_add_lt_m G.n G.adj u hi

/-- The encoded input has `n + 2 * m + 3` words. -/
theorem encode_length : G.encode.length = G.n + 2 * G.m + 3 :=
  CSR.encode_length G.n G.source G.adj Signed.encode

theorem offset_succ {u : ℕ} (hu : u < G.n) :
    G.offset (u + 1) = G.offset u + (G.adj ⟨u, hu⟩).length :=
  CSR.offset_succ G.n G.adj hu

theorem offset_n : G.offset G.n = G.m :=
  CSR.offset_n G.n G.adj

theorem offset_mono {u v : ℕ} (h : u ≤ v) : G.offset u ≤ G.offset v :=
  CSR.offset_mono G.n G.adj h

theorem init_len {r : ℕ} : (Data.init G.encode : Data r).mem 0 = G.n + 2 * G.m + 3 :=
  CSR.init_len G.n G.source G.adj Signed.encode

theorem init_n {r : ℕ} : (Data.init G.encode : Data r).mem 1 = G.n :=
  CSR.init_n G.n G.source G.adj Signed.encode

theorem init_source {r : ℕ} : (Data.init G.encode : Data r).mem 2 = G.source :=
  CSR.init_source G.n G.source G.adj Signed.encode

theorem init_offset {r : ℕ} {u : ℕ} (hu : u ≤ G.n) :
    (Data.init G.encode : Data r).mem (3 + u) = G.offset u := by
  rw [Nat.add_comm 3 u]
  exact CSR.init_offset G.n G.source G.adj Signed.encode hu

private theorem le_wordBound_linear {x : ℕ} (hx : x ≤ 2 * G.n + 2 * G.m + 32) :
    x ≤ G.wordBound := by
  have h1 : 2 * G.n + 2 * G.m + 32 ≤ 16 * (G.n + 1) * (G.m + 2) := by nlinarith
  have h2 : 16 * (G.n + 1) * (G.m + 2) = 8 * (G.n + 1) * (G.m + 2) * 2 := by ring
  have h3 : 8 * (G.n + 1) * (G.m + 2) * 2 ≤ G.wordBound := by
    unfold wordBound
    exact Nat.mul_le_mul_left _ (by omega)
  omega

private theorem fits_of_linear {w x : ℕ} (hfit : Fits w G.wordBound)
    (hx : x ≤ 2 * G.n + 2 * G.m + 32) : Fits w x :=
  hfit.of_le (G.le_wordBound_linear hx)

theorem init_target {r : ℕ} (u : Fin G.n) {i : ℕ} (hi : i < (G.adj u).length) :
    (Data.init G.encode : Data r).mem ((G.n + 4) + 2 * (G.offset u + i)) =
      ((G.adj u)[i].1 : ℕ) := by
  rw [show (G.n + 4) + 2 * (G.offset u + i) = 2 * (G.offset u + i) + G.n + 4 by ring]
  exact CSR.init_target G.n G.source G.adj Signed.encode u hi

theorem init_weight {r : ℕ} (u : Fin G.n) {i : ℕ} (hi : i < (G.adj u).length) :
    (Data.init G.encode : Data r).mem ((G.n + 4) + 2 * (G.offset u + i) + 1) =
      Signed.encode (G.adj u)[i].2 := by
  rw [show (G.n + 4) + 2 * (G.offset u + i) + 1 = 2 * (G.offset u + i) + G.n + 5 by ring]
  exact CSR.init_weight G.n G.source G.adj Signed.encode u hi

/-- Whenever `G.wordBound` fits in `w` bits, the encoded input words fit in `w` bits. -/
theorem inputFits_encode {w : ℕ} (hfit : Fits w G.wordBound) : InputFits w G.encode := by
  refine CSR.inputFits_encode G.n G.source G.adj Signed.encode
    (G.le_wordBound_linear (by change G.n + 2 * G.m + 3 ≤ _; omega)) (fun u e he => ?_) hfit
  have hc := G.natAbs_le_maxAbsWeight he
  have henc : Signed.encode e.2 ≤ 2 * G.maxAbsWeight + 1 := by
    unfold Signed.encode; split_ifs <;> omega
  have h2 : 8 * 1 * (G.maxAbsWeight + 2) ≤ G.wordBound := by
    unfold wordBound
    have : 8 * 1 ≤ 8 * (G.n + 1) * (G.m + 2) := by nlinarith
    exact Nat.mul_le_mul_right _ this
  omega

end Instance

/-! ### Output specification -/

/-- Output word list of Bellman–Ford on `G`: `[]` when a negative cycle is reachable from
`G.source`, and `[encodeDist (d 0), …, encodeDist (d (n - 1))]` otherwise. -/
def answerWords (G : Instance) : List ℕ :=
  match bellmanFord G.adj (List.finRange G.n) G.source with
  | none => []
  | some d => (List.finRange G.n).map fun v => encodeDist (d v)

/-- Decode the output word list of `program` back to `Option (Fin G.n → WithTop ℤ)`. -/
def decodeAnswer (G : Instance) (ws : List ℕ) : Option (Fin G.n → WithTop ℤ) :=
  if ws.isEmpty then none
  else some fun v => decodeDist (ws.getD v.val 1)

theorem length_answerWords_le (G : Instance) : (answerWords G).length ≤ G.n := by
  unfold answerWords
  split <;> simp

/-- Decoding `answerWords G` recovers `bellmanFord G.adj (List.finRange G.n) G.source` exactly. -/
@[simp]
theorem decodeAnswer_answerWords (G : Instance) :
    decodeAnswer G (answerWords G) = bellmanFord G.adj (List.finRange G.n) G.source := by
  unfold decodeAnswer answerWords
  cases hbf : bellmanFord G.adj (List.finRange G.n) G.source with
  | none => rfl
  | some d =>
    have hne : ((List.finRange G.n).map fun v => encodeDist (d v)) ≠ [] :=
      List.ne_nil_of_length_pos (by simp [G.n_pos])
    simp only [Bool.eq_false_iff.mpr (mt List.isEmpty_iff.mp hne), Bool.false_eq_true, ↓reduceIte,
      Option.some.injEq]
    funext v
    rw [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem (by simp : v.val < (List.finRange G.n).length),
      List.getElem_finRange]
    simp

/-- `answerWords G` is empty if and only if a negative cycle is reachable from `G.source`. -/
theorem answerWords_eq_nil_iff (G : Instance) :
    answerWords G = [] ↔ NegCycleReachable G.adj G.source := by
  rw [← bellmanFord_eq_none_iff (vs := List.finRange G.n) List.mem_finRange]
  unfold answerWords
  cases bellmanFord G.adj (List.finRange G.n) G.source with
  | none => simp
  | some d => exact iff_of_false (List.ne_nil_of_length_pos (by simp [G.n_pos])) (by simp)

/-- When `answerWords G ≠ []`, entry `v` decodes to the shortest-path weight from `G.source` to
`v`. -/
theorem isShortestDist_of_answerWords_ne_nil {G : Instance} (h : answerWords G ≠ [])
    (v : Fin G.n) :
    IsShortestDist G.adj G.source v (decodeDist ((answerWords G).getD v.val 1)) := by
  unfold answerWords at h ⊢
  cases hbf : bellmanFord G.adj (List.finRange G.n) G.source with
  | none => exact absurd (by simp [hbf]) h
  | some d =>
    have hv : v.val < (List.finRange G.n).length := by simp
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hv,
      List.getElem_finRange]
    simpa using isShortestDist_of_bellmanFord_eq_some List.mem_finRange hbf v

end Cslib.Algorithms.WordRAM.BellmanFord

end

public section

namespace Cslib.Algorithms.WordRAM.BellmanFord

open Cslib.WordRAM Cslib.WordRAM.Signed
open Cslib.Algorithms.Lean.BellmanFord

/-! ### Magnitude envelope of intermediate Bellman–Ford estimates -/

/-- Every finite estimate in `d` has absolute value at most `B`. -/
private def MagBounded {V : Type*} (B : ℕ) (d : V → WithTop ℤ) : Prop :=
  ∀ v (z : ℤ), d v = z → z.natAbs ≤ B

private theorem magBounded_init {V : Type*} [DecidableEq V] (s : V) :
    MagBounded 0 (init (W := ℤ) s) := by
  intro v z hv
  by_cases hvs : v = s
  · subst hvs
    simp only [init, Function.update_self, WithTop.zero_eq_coe] at hv
    subst hv
    simp
  · simp [init, hvs] at hv

private theorem magBounded_relax {V : Type*} [DecidableEq V] {B M : ℕ} {d : V → WithTop ℤ}
    (hd : MagBounded B d) (u v : V) {c : ℤ} (hc : c.natAbs ≤ M) :
    MagBounded (B + M) (relax d u v c) := by
  intro x z hx
  unfold relax at hx
  split_ifs at hx with hlt
  · by_cases hxv : x = v
    · subst hxv
      rw [Function.update_self] at hx
      cases hdu : d u with
      | top =>
        rw [hdu, WithTop.top_add] at hx
        exact absurd hx WithTop.top_ne_coe
      | coe a =>
        rw [hdu, ← WithTop.coe_add, WithTop.coe_eq_coe] at hx
        subst hx
        have ha := hd u a hdu
        have htri := Int.natAbs_add_le a c
        omega
    · rw [Function.update_of_ne hxv] at hx
      have hz := hd x z hx
      omega
  · have hz := hd x z hx
    omega

private theorem magBounded_scan {V : Type*} [DecidableEq V] {M : ℕ} (u : V) :
    ∀ (es : List (V × ℤ)) {B : ℕ} {d : V → WithTop ℤ},
      (∀ e ∈ es, e.2.natAbs ≤ M) → MagBounded B d →
      MagBounded (B + es.length * M) (es.foldl (fun d e => relax d u e.1 e.2) d)
  | [], B, d, _, hd => by simpa using hd
  | e :: es, B, d, hes, hd => by
    rw [List.foldl_cons, List.length_cons, Nat.succ_mul, ← Nat.add_assoc, Nat.add_right_comm]
    exact magBounded_scan u es (fun e' he' => hes e' (List.mem_cons_of_mem e he'))
      (magBounded_relax hd u e.1 (hes e List.mem_cons_self))

private theorem magBounded_round_list (G : Instance) :
    ∀ (us : List (Fin G.n)) {B : ℕ} {d : Fin G.n → WithTop ℤ},
      MagBounded B d →
      MagBounded (B + (us.map fun u => (G.adj u).length).sum * G.maxAbsWeight)
        (us.foldl (fun d u => (G.adj u).foldl (fun d e => relax d u e.1 e.2) d) d)
  | [], B, d, hd => by simpa using hd
  | u :: us, B, d, hd => by
    simp only [List.foldl_cons, List.map_cons, List.sum_cons, Nat.add_mul, ← Nat.add_assoc]
    exact magBounded_round_list G us
      (magBounded_scan u (G.adj u) (fun _ he => G.natAbs_le_maxAbsWeight he) hd)

private theorem magBounded_round (G : Instance) {B : ℕ} {d : Fin G.n → WithTop ℤ}
    (hd : MagBounded B d) :
    MagBounded (B + G.m * G.maxAbsWeight)
      (Lean.BellmanFord.round G.adj (List.finRange G.n) d) := by
  have hsum : ((List.finRange G.n).map fun u => (G.adj u).length).sum = G.m := by
    rw [← Fin.sum_univ_def]
    rfl
  simpa only [Lean.BellmanFord.round, hsum] using magBounded_round_list G (List.finRange G.n) hd

private theorem magBounded_iterate_round (G : Instance) :
    ∀ (k : ℕ) {B : ℕ} {d : Fin G.n → WithTop ℤ},
      MagBounded B d →
      MagBounded (B + k * (G.m * G.maxAbsWeight))
        ((Lean.BellmanFord.round G.adj (List.finRange G.n))^[k] d)
  | 0, B, d, hd => by simpa using hd
  | k + 1, B, d, hd => by
    rw [Function.iterate_succ_apply, Nat.succ_mul, Nat.add_comm (k * _), ← Nat.add_assoc]
    exact magBounded_iterate_round G k (magBounded_round G hd)

private theorem signed_fits_of_wordBound {G : Instance} {w : ℕ} (hfit : Fits w G.wordBound) :
    2 ≤ w ∧ Fits w 3 ∧
      GenericRAM.Signed.Fits (w - 2) (((G.n * G.m + 1) * G.maxAbsWeight : ℕ) : ℤ) := by
  have h32 : 32 ≤ G.wordBound := G.le_wordBound_linear (by omega)
  have hw32 : 32 < 2 ^ w := hfit.of_le h32
  have hw5 : 5 < w := by
    by_contra hle
    have hpow : 2 ^ w ≤ 2 ^ 5 := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have h3 : Fits w 3 := hfit.of_le (by omega)
  refine ⟨by omega, h3, ⟨by omega, ?_, ?_⟩⟩
  · have : (0 : ℤ) ≤ 2 ^ (w - 2 - 1) := by positivity
    omega
  · set B : ℕ := (G.n * G.m + 1) * G.maxAbsWeight
    have hnm : G.n * G.m + 1 ≤ (G.n + 1) * (G.m + 2) := by nlinarith
    have hB1 : B + 1 ≤ (G.n + 1) * (G.m + 2) * (G.maxAbsWeight + 2) := by
      calc B + 1 = (G.n * G.m + 1) * G.maxAbsWeight + 1 := rfl
        _ ≤ (G.n + 1) * (G.m + 2) * G.maxAbsWeight + (G.n + 1) * (G.m + 2) * 2 :=
          Nat.add_le_add (Nat.mul_le_mul_right _ hnm) (by nlinarith)
        _ = (G.n + 1) * (G.m + 2) * (G.maxAbsWeight + 2) := by ring
    have hB : 8 * (B + 1) ≤ G.wordBound := by
      unfold Instance.wordBound
      calc 8 * (B + 1) ≤ 8 * ((G.n + 1) * (G.m + 2) * (G.maxAbsWeight + 2)) :=
            Nat.mul_le_mul_left 8 hB1
        _ = 8 * (G.n + 1) * (G.m + 2) * (G.maxAbsWeight + 2) := by ring
    have hlt8 : 8 * (B + 1) < 2 ^ w := hfit.of_le hB
    have hpow : 2 ^ w = 8 * 2 ^ (w - 2 - 1) := by
      have hw_eq : w = (w - 2 - 1) + 3 := by omega
      conv_lhs => rw [hw_eq, pow_add]
      ring
    have hBlt : B < 2 ^ (w - 2 - 1) := by omega
    exact_mod_cast hBlt

/-! ### Registers and structured Word-RAM program -/

namespace Reg

/-- Constant `0` (`= encodeDist (0 : WithTop ℤ)`). -/
private abbrev cZero : Fin (21 + 9) := ⟨9, by decide⟩
/-- Constant `1` (`= encodeDist ⊤`). -/
private abbrev cOne : Fin (21 + 9) := ⟨10, by decide⟩
/-- Constant `2`. -/
private abbrev cTwo : Fin (21 + 9) := ⟨11, by decide⟩
/-- Constant `3` (base of the offset array). -/
private abbrev cThree : Fin (21 + 9) := ⟨12, by decide⟩
/-- Vertex count `n`. -/
private abbrev nv : Fin (21 + 9) := ⟨13, by decide⟩
/-- Source vertex `source`. -/
private abbrev src : Fin (21 + 9) := ⟨14, by decide⟩
/-- Base address `n + 4` of the edge array. -/
private abbrev ebase : Fin (21 + 9) := ⟨15, by decide⟩
/-- Output-list header address `outAddrBase`. -/
abbrev outBase : Fin (21 + 9) := ⟨16, by decide⟩
/-- Distance-table base address `distAddrBase = outAddrBase + 1`. -/
private abbrev dbase : Fin (21 + 9) := ⟨17, by decide⟩
/-- Round index `0 .. n - 1`. -/
private abbrev rnd : Fin (21 + 9) := ⟨18, by decide⟩
/-- Round limit `n - 1`. -/
private abbrev rndLim : Fin (21 + 9) := ⟨19, by decide⟩
/-- Current vertex `u`. -/
private abbrev u : Fin (21 + 9) := ⟨20, by decide⟩
/-- Current edge cursor `j`. -/
private abbrev j : Fin (21 + 9) := ⟨21, by decide⟩
/-- End of `u`'s edges `offset (u + 1)`. -/
private abbrev jEnd : Fin (21 + 9) := ⟨22, by decide⟩
/-- Encoded tentative distance `encodeDist (d u)`. -/
private abbrev du : Fin (21 + 9) := ⟨23, by decide⟩
/-- Current edge target `v`. -/
private abbrev vReg : Fin (21 + 9) := ⟨24, by decide⟩
/-- Encoded edge weight `Signed.encode c`. -/
private abbrev wc : Fin (21 + 9) := ⟨25, by decide⟩
/-- Encoded tentative distance `encodeDist (d v)`. -/
private abbrev dv : Fin (21 + 9) := ⟨26, by decide⟩
/-- Encoded candidate weight `Signed.encode (a + c)`. -/
private abbrev sumReg : Fin (21 + 9) := ⟨27, by decide⟩
/-- Scratch memory address. -/
private abbrev addr : Fin (21 + 9) := ⟨28, by decide⟩
/-- Check-pass accumulator (`1` if all edges so far satisfy `d v ≤ d u + c`, `0` otherwise). -/
private abbrev ok : Fin (21 + 9) := ⟨29, by decide⟩

end Reg

open Reg

/-- Initialize constants, dimensions, and base addresses from `State.init G.encode`. -/
private def setupCode : Code .standard (21 + 9) := ram[
  cZero ← #0; cOne ← #1; cTwo ← #2; cThree ← #3;
  outBase ← *cZero; outBase ← outBase + cOne; dbase ← outBase + cOne;
  nv ← *cOne; src ← *cTwo;
  ebase ← nv + cThree; ebase ← ebase + cOne ]

/-- Body setting `mem[dbase + u] := 1` (`⊤`). -/
private def initBody : Code .standard (21 + 9) := ram[
  addr ← dbase + u; *addr ← cOne; u ← u + cOne ]

/-- Initialize `d` to `0` at `src` and `⊤` elsewhere. -/
private def initCode : Code .standard (21 + 9) := ram[
  u ← cZero;
  ⟪.loop (.lt u nv) initBody⟫;
  addr ← dbase + src; *addr ← cZero ]

/-- Test whether edge `j` out of `u` strictly improves `d v`, setting `Signed.result` to
`(decide (d u + c < d v)).toNat`, `vReg` to `v`, and (when improving) `sumReg` to
`encodeDist (d u + c)` without modifying memory. -/
private def testImproveCode : Code .standard (21 + 9) := ram[
  addr ← dbase + u; du ← *addr;
  addr ← cTwo * j; addr ← ebase + addr; vReg ← *addr;
  addr ← addr + cOne; wc ← *addr;
  if du = cOne then [ result ← cZero ]
  else [
    left ← du; right ← wc; ⟪Signed.add⟫; sumReg ← result;
    addr ← dbase + vReg; dv ← *addr;
    if dv = cOne then [ result ← cOne ]
    else [
      left ← sumReg; right ← dv; ⟪Signed.less⟫ ] ] ]

/-- Relax edge `j` out of `u`. -/
private def relaxEdgeCode : Code .standard (21 + 9) :=
  testImproveCode.seq (ram[
    if result = cOne then [ addr ← dbase + vReg; *addr ← sumReg ] else [ dv ← dv ] ])

/-- Loop over edges `j ∈ [offset u, offset (u + 1))` relaxing out-edges of `u`. -/
private def relaxEdgeLoop : Code .standard (21 + 9) :=
  .loop (.lt j jEnd) (ram[ ⟪relaxEdgeCode⟫; j ← j + cOne ])

/-- Load `[offset u, offset (u + 1))` into `[j, jEnd)`. -/
private def scanVertexPrep : Code .standard (21 + 9) := ram[
  addr ← cThree + u; j ← *addr; addr ← addr + cOne; jEnd ← *addr ]

/-- Scan all out-edges of vertex `u` in a relaxation round. -/
private def scanVertexCode : Code .standard (21 + 9) :=
  scanVertexPrep.seq relaxEdgeLoop

/-- One full Bellman–Ford relaxation round over `u = 0, …, n - 1`. -/
private def roundCode : Code .standard (21 + 9) :=
  (ram[ u ← cZero ]).seq (.loop (.lt u nv) (scanVertexCode.seq (ram[ u ← u + cOne ])))

/-- Execute `n - 1` relaxation rounds. -/
private def roundsCode : Code .standard (21 + 9) :=
  (ram[ rndLim ← nv - cOne; rnd ← cZero ]).seq
    (.loop (.lt rnd rndLim) (roundCode.seq (ram[ rnd ← rnd + cOne ])))

/-- Check whether edge `j` out of `u` can still be relaxed, clearing `ok` if `d u + c < d v`. -/
private def checkEdgeCode : Code .standard (21 + 9) :=
  testImproveCode.seq (ram[ if result = cOne then [ ok ← cZero ] else [ dv ← dv ] ])

/-- Loop checking edges `j ∈ [offset u, offset (u + 1))` out of `u`. -/
private def checkEdgeLoop : Code .standard (21 + 9) :=
  .loop (.lt j jEnd) (ram[ ⟪checkEdgeCode⟫; j ← j + cOne ])

/-- Scan all out-edges of `u` during the negative-cycle check. -/
private def checkVertexCode : Code .standard (21 + 9) :=
  scanVertexPrep.seq checkEdgeLoop

/-- Negative-cycle check pass over all vertices and edges. -/
private def checkCode : Code .standard (21 + 9) :=
  (ram[ ok ← cOne; u ← cZero ]).seq
    (.loop (.lt u nv) (checkVertexCode.seq (ram[ u ← u + cOne ])))

/-- Write output length header (`nv` on `ok = 1`, `0` on `ok = 0`) at `outBase`. -/
private def finishCode : Code .standard (21 + 9) := ram[
  if ok = cOne then [ *outBase ← nv ] else [ *outBase ← cZero ] ]

/-- Complete structured Bellman–Ford solver leaving output header address in `outBase`. -/
def solver : Code .standard (21 + 9) := ram[
  ⟪setupCode⟫; ⟪initCode⟫; ⟪roundsCode⟫; ⟪checkCode⟫; ⟪finishCode⟫ ]

/-- Flat Word-RAM Bellman–Ford program returning `answerWords G` via `ExecutesList`. -/
def program : Program .standard (21 + 9) := solver.program outBase

/-! ### Machine state invariants and step specifications -/

/-- Fixed registers and untouched input memory `[0, G.outAddrBase)` maintained throughout execution
after `setupCode`. -/
private structure CtxInv (G : Instance) (x : Data (21 + 9)) : Prop where
  czero : x.regs cZero = 0
  cone : x.regs cOne = 1
  ctwo : x.regs cTwo = 2
  cthree : x.regs cThree = 3
  hnv : x.regs nv = G.n
  hsrc : x.regs src = G.source
  hebase : x.regs ebase = G.n + 4
  houtBase : x.regs outBase = G.outAddrBase
  hdbase : x.regs dbase = G.distAddrBase
  mem_input : ∀ a < G.outAddrBase, x.mem a = (Data.init G.encode : Data (21 + 9)).mem a

/-- Memory cells `[G.distAddrBase, G.distAddrBase + G.n)` represent `d : Fin G.n → WithTop ℤ`. -/
private def DistRep (G : Instance) (d : Fin G.n → WithTop ℤ) (mem : ℕ → ℕ) : Prop :=
  ∀ v : Fin G.n, mem (G.distAddrBase + v.val) = encodeDist (d v)

private theorem CtxInv.of_regs_mem_eq {G : Instance} {x y : Data (21 + 9)} (hx : CtxInv G x)
    (hm : ∀ a < G.outAddrBase, y.mem a = x.mem a)
    (hr : ∀ q : Fin (21 + 9), 9 ≤ q.val → q.val < 18 → y.regs q = x.regs q) : CtxInv G y where
  czero := (hr cZero (by decide) (by decide)).trans hx.czero
  cone := (hr cOne (by decide) (by decide)).trans hx.cone
  ctwo := (hr cTwo (by decide) (by decide)).trans hx.ctwo
  cthree := (hr cThree (by decide) (by decide)).trans hx.cthree
  hnv := (hr nv (by decide) (by decide)).trans hx.hnv
  hsrc := (hr src (by decide) (by decide)).trans hx.hsrc
  hebase := (hr ebase (by decide) (by decide)).trans hx.hebase
  houtBase := (hr outBase (by decide) (by decide)).trans hx.houtBase
  hdbase := (hr dbase (by decide) (by decide)).trans hx.hdbase
  mem_input a ha := (hm a ha).trans (hx.mem_input a ha)

private theorem CtxInv.of_frame {G : Instance} {x y : Data (21 + 9)} (hx : CtxInv G x)
    (hf : Signed.Frame x y) : CtxInv G y :=
  hx.of_regs_mem_eq (fun a _ => congrFun hf.1 a) fun q h9 _ => hf.2 q (Or.inr h9)

private theorem CtxInv.set {G : Instance} {x : Data (21 + 9)} (hx : CtxInv G x)
    {r : Fin (21 + 9)} (hr : r.val < 9 ∨ 18 ≤ r.val) {val : ℕ} :
    CtxInv G (x.set r val) :=
  hx.of_regs_mem_eq (fun _ _ => rfl) fun _ h9 h18 =>
    Data.set_regs_of_ne (Fin.ne_of_val_ne (by omega)) val

private theorem CtxInv.write_ge {G : Instance} {x : Data (21 + 9)} (hx : CtxInv G x)
    {a : ℕ} (ha : G.outAddrBase ≤ a) {val : ℕ} :
    CtxInv G (x.write a val) :=
  hx.of_regs_mem_eq (fun _ hq => Data.write_mem_of_ne (by omega) val) fun _ _ _ => rfl

private theorem CtxInv.offset_eq {G : Instance} {x : Data (21 + 9)} (hx : CtxInv G x)
    {u₀ : ℕ} (hu₀ : u₀ ≤ G.n) : x.mem (3 + u₀) = G.offset u₀ := by
  rw [hx.mem_input (3 + u₀) (by unfold Instance.outAddrBase; omega)]
  exact G.init_offset hu₀

private theorem CtxInv.target_eq {G : Instance} {x : Data (21 + 9)} (hx : CtxInv G x)
    (u₀ : Fin G.n) {i : ℕ} (hi : i < (G.adj u₀).length) :
    x.mem ((G.n + 4) + 2 * (G.offset u₀ + i)) = ((G.adj u₀)[i].1 : ℕ) := by
  have hlt := G.offset_add_lt_m u₀ hi
  rw [hx.mem_input _ (by unfold Instance.outAddrBase; omega)]
  exact G.init_target u₀ hi

private theorem CtxInv.weight_eq {G : Instance} {x : Data (21 + 9)} (hx : CtxInv G x)
    (u₀ : Fin G.n) {i : ℕ} (hi : i < (G.adj u₀).length) :
    x.mem ((G.n + 4) + 2 * (G.offset u₀ + i) + 1) = Signed.encode (G.adj u₀)[i].2 := by
  have hlt := G.offset_add_lt_m u₀ hi
  rw [hx.mem_input _ (by unfold Instance.outAddrBase; omega)]
  exact G.init_weight u₀ hi

private theorem distRep_update {G : Instance} {d : Fin G.n → WithTop ℤ} {mem : ℕ → ℕ}
    (hd : DistRep G d mem) (v : Fin G.n) (val : WithTop ℤ) :
    DistRep G (Function.update d v val)
      (Function.update mem (G.distAddrBase + v.val) (encodeDist val)) := by
  intro x
  by_cases hxv : x = v
  · subst hxv
    simp
  · have hne : G.distAddrBase + x.val ≠ G.distAddrBase + v.val := by
      intro heq
      exact hxv (Fin.ext (by omega))
    rw [Function.update_of_ne hne, Function.update_of_ne hxv]
    exact hd x

/-- `setupCode` establishes `CtxInv G` in `11` instructions without modifying memory. -/
private theorem setupCode_spec (G : Instance) {w : ℕ} (hfit : Fits w G.wordBound) :
    ∃ y, ExecWithin w setupCode (Data.init G.encode) y 11 ∧ CtxInv G y := by
  obtain ⟨_, h3, _⟩ := signed_fits_of_wordBound hfit
  have h1 : Fits w 1 := h3.of_le (by decide)
  have h2 : Fits w 2 := h3.of_le (by decide)
  have hf_out : Fits w (G.n + 2 * G.m + 3 + 1) := G.fits_of_linear hfit (by omega)
  have hf_db : Fits w (G.n + 2 * G.m + 3 + 1 + 1) := G.fits_of_linear hfit (by omega)
  have hf_eb1 : Fits w (G.n + 3) := G.fits_of_linear hfit (by omega)
  have hf_eb2 : Fits w (G.n + 3 + 1) := G.fits_of_linear hfit (by omega)
  have hm0 := G.init_len (r := 21 + 9)
  have hm1 := G.init_n (r := 21 + 9)
  have hm2 := G.init_source (r := 21 + 9)
  unfold setupCode
  wram_exec [Data.init_regs, hm0, hm1, hm2, h1, h2, h3, hf_out, hf_db, hf_eb1, hf_eb2]
  refine ⟨by wram_simp, by wram_simp, by wram_simp, by wram_simp, by wram_simp, by wram_simp,
    ?_, ?_, ?_, fun _ _ => rfl⟩
  · wram_simp
  · wram_simp; unfold Instance.outAddrBase; omega
  · wram_simp; unfold Instance.distAddrBase; omega

/-- `initCode` initializes `DistRep G (init G.source)` in at most `5 * G.n + 5` instructions. -/
private theorem initCode_spec (G : Instance) {w : ℕ} (hfit : Fits w G.wordBound)
    {x : Data (21 + 9)} (hx : CtxInv G x) :
    ∃ y, ExecWithin w initCode x y (5 * G.n + 5) ∧ CtxInv G y ∧
      DistRep G (init G.source) y.mem := by
  let P (k : ℕ) (y : Data (21 + 9)) : Prop :=
    CtxInv G y ∧ ∀ i < k, y.mem (G.distAddrBase + i) = 1
  have hbody (y : Data (21 + 9)) (hy : P (y.regs u) y) (hlt : y.regs u < G.n) :
      ∃ z, ExecWithin w initBody y z 3 ∧ P (y.regs u + 1) z ∧ z.regs u = y.regs u + 1 := by
    obtain ⟨hyc, hym⟩ := hy
    have hf_addr : Fits w (G.distAddrBase + y.regs u) :=
      G.fits_of_linear hfit (by unfold Instance.distAddrBase; omega)
    have hf_inc : Fits w (y.regs u + 1) := G.fits_of_linear hfit (by omega)
    unfold initBody
    wram_exec [hyc.hdbase, hyc.cone, hf_addr, hf_inc]
    refine ⟨⟨((hyc.set (by decide)).write_ge
        (by unfold Instance.outAddrBase Instance.distAddrBase; omega)).set (by decide), ?_⟩,
      by wram_simp⟩
    intro i hi
    change (((y.set addr (G.distAddrBase + y.regs u)).write
        (G.distAddrBase + y.regs u) 1).mem (G.distAddrBase + i)) = 1
    by_cases hik : i = y.regs u
    · subst hik
      exact Data.write_mem_self _ _ _
    · rw [Data.write_mem_of_ne (by omega)]
      exact hym i (by omega)
  have hf_src : Fits w (G.distAddrBase + G.source.val) := by
    have := G.source.isLt
    exact G.fits_of_linear hfit (by unfold Instance.distAddrBase; omega)
  have hu0 : ExecWithin (B := .standard) w (ram[ u ← cZero ]) x (x.set u 0) 1 := by
    ram_eval [hx.czero]
  have hx0_P : P ((x.set u 0).regs u) (x.set u 0) := by
    rw [Data.set_regs_self]
    exact ⟨hx.set (by decide), fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  have hx0_le : (x.set u 0).regs u ≤ G.n := by
    rw [Data.set_regs_self]; exact Nat.zero_le _
  obtain ⟨y, hy_loop, ⟨hyc, hym⟩, _⟩ :=
    ExecWithin.loop_count P (fun y hy => hy.1.hnv) hbody hx0_le hx0_P
  rw [Data.set_regs_self, Nat.sub_zero] at hy_loop
  have hfin : ∃ z, ExecWithin w (ram[ addr ← dbase + src; *addr ← cZero ]) y z 2 ∧
      CtxInv G z ∧ DistRep G (init G.source) z.mem := by
    wram_exec [hyc.hdbase, hyc.hsrc, hyc.czero, hf_src]
    refine ⟨(hyc.set (by decide)).write_ge
        (by unfold Instance.outAddrBase Instance.distAddrBase; omega), ?_⟩
    intro v
    by_cases hvs : v = G.source
    · subst hvs
      rw [Data.write_mem_self]
      simp only [init, Function.update_self]
      rfl
    · have hne : G.distAddrBase + v.val ≠ G.distAddrBase + G.source.val := by
        intro heq
        exact hvs (Fin.ext (by omega))
      rw [Data.write_mem_of_ne hne]
      change y.mem (G.distAddrBase + v.val) = encodeDist (init G.source v)
      rw [hym v.val v.isLt]
      simp [init, hvs]
  obtain ⟨z, hz_ex, hz_ctx, hz_d⟩ := hfin
  exact ⟨z, (hu0.seq (hy_loop.seq hz_ex)).mono (by omega), hz_ctx, hz_d⟩

/-- `testImproveCode` decides `d u₀ + c₀ < d v₀` in at most `44` instructions without modifying
memory. -/
private theorem testImproveCode_spec (G : Instance) {w B : ℕ} (hfit : Fits w G.wordBound)
    (hB : B ≤ G.n * G.m * G.maxAbsWeight) (u₀ : Fin G.n) {i : ℕ} (hi : i < (G.adj u₀).length)
    {d : Fin G.n → WithTop ℤ} (hd_mag : MagBounded B d) {x : Data (21 + 9)} (hx : CtxInv G x)
    (hd : DistRep G d x.mem) (hu : x.regs u = u₀.val) (hj : x.regs j = G.offset u₀ + i) :
    ∃ y, ExecWithin w testImproveCode x y 44 ∧ CtxInv G y ∧ y.mem = x.mem ∧
      y.regs Signed.result =
        (decide (d u₀ + (G.adj u₀)[i].2 < d (G.adj u₀)[i].1)).toNat ∧
      y.regs vReg = (G.adj u₀)[i].1.val ∧
      (d u₀ + (G.adj u₀)[i].2 < d (G.adj u₀)[i].1 →
        y.regs sumReg = encodeDist (d u₀ + (G.adj u₀)[i].2)) ∧
      y.regs u = u₀.val ∧ y.regs j = G.offset u₀ + i ∧ y.regs jEnd = x.regs jEnd ∧
      y.regs rnd = x.regs rnd ∧ y.regs rndLim = x.regs rndLim ∧ y.regs ok = x.regs ok := by
  obtain ⟨hw2, h3, hSfit⟩ := signed_fits_of_wordBound hfit
  have h2 : Fits w 2 := h3.of_le (by decide)
  have hw_eq : (w - 2) + 2 = w := by omega
  set v₀ := (G.adj u₀)[i].1
  set c₀ := (G.adj u₀)[i].2
  have hj_lt := G.offset_add_lt_m u₀ hi
  have hdu_mem : x.mem (G.distAddrBase + u₀.val) = encodeDist (d u₀) := hd u₀
  have htarget_mem : x.mem ((G.n + 4) + 2 * (G.offset u₀ + i)) = v₀.val := hx.target_eq u₀ hi
  have hweight_mem : x.mem ((G.n + 4) + 2 * (G.offset u₀ + i) + 1) = Signed.encode c₀ :=
    hx.weight_eq u₀ hi
  have hf_du : Fits w (G.distAddrBase + u₀.val) := by
    have := u₀.isLt
    exact G.fits_of_linear hfit (by unfold Instance.distAddrBase; omega)
  have hf_2j : Fits w (2 * (G.offset u₀ + i)) := G.fits_of_linear hfit (by omega)
  have hf_et : Fits w ((G.n + 4) + 2 * (G.offset u₀ + i)) := G.fits_of_linear hfit (by omega)
  have hf_ew : Fits w ((G.n + 4) + 2 * (G.offset u₀ + i) + 1) := G.fits_of_linear hfit (by omega)
  have hf_dv : Fits w (G.distAddrBase + v₀.val) := by
    have := v₀.isLt
    exact G.fits_of_linear hfit (by unfold Instance.distAddrBase; omega)
  cases hdu : d u₀ with
  | top =>
    have hlt_false : decide ((⊤ : WithTop ℤ) + c₀ < d v₀) = false :=
      decide_eq_false (by rw [WithTop.top_add]; exact not_top_lt)
    unfold testImproveCode
    wram_exec [hx.hdbase, hu, hdu_mem, hdu, encodeDist_top, hx.ctwo, hj, hx.hebase, hx.cone,
      hx.czero, htarget_mem, hweight_mem, hf_du, hf_2j, hf_et, hf_ew]
    rw [hlt_false]
    exact ⟨((((((((hx.set (by decide)).set (by decide)).set (by decide)).set (by decide)).set
        (by decide)).set (by decide)).set (by decide)).set (by decide)),
      rfl, by wram_simp; rfl, by wram_simp,
      fun h => absurd h (by rw [WithTop.top_add]; exact not_top_lt),
      by wram_simp [hu], by wram_simp [hj], by wram_simp, by wram_simp, by wram_simp,
      by wram_simp⟩
  | coe a =>
    have hne1 : Signed.encode a ≠ 1 := encode_ne_one a
    have ha_abs : a.natAbs ≤ (G.n * G.m + 1) * G.maxAbsWeight :=
      calc a.natAbs ≤ G.n * G.m * G.maxAbsWeight := (hd_mag u₀ a hdu).trans hB
        _ ≤ (G.n * G.m + 1) * G.maxAbsWeight := Nat.mul_le_mul_right _ (Nat.le_succ _)
    have hc_abs : c₀.natAbs ≤ (G.n * G.m + 1) * G.maxAbsWeight :=
      calc c₀.natAbs ≤ 1 * G.maxAbsWeight := by
            simpa using G.natAbs_le_maxAbsWeight (List.getElem_mem hi)
        _ ≤ (G.n * G.m + 1) * G.maxAbsWeight := Nat.mul_le_mul_right _ (by omega)
    have ha_sfit : GenericRAM.Signed.Fits (w - 2) a := hSfit.of_natAbs_le ha_abs
    have hc_sfit : GenericRAM.Signed.Fits (w - 2) c₀ := hSfit.of_natAbs_le hc_abs
    unfold testImproveCode
    wram_exec [hx.hdbase, hu, hdu_mem, hdu, encodeDist_coe, hx.ctwo, hj, hx.hebase, hx.cone,
      htarget_mem, hweight_mem, hf_du, hf_2j, hf_et, hf_ew, hne1]
    refine WP.name fun x₁ hx₁ => ?_
    have hx₁_l : x₁.regs Signed.left = Signed.encode a := by
      rw [hx₁]
      wram_simp
    have hx₁_r : x₁.regs Signed.right = Signed.encode c₀ := by
      rw [hx₁]
      wram_simp
    obtain ⟨y₁, hy₁_ex, hy₁_res, hy₁_fr⟩ := Signed.exec_add ha_sfit hc_sfit x₁ hx₁_l hx₁_r
    rw [hw_eq] at hy₁_ex
    dsimp only [GenericRAM.Signed.Arithmetic.eval] at hy₁_res
    have hx₁_ctx : CtxInv G x₁ := by
      rw [hx₁]
      exact (((((((((hx.set (by decide)).set (by decide)).set (by decide)).set (by decide)).set
        (by decide)).set (by decide)).set (by decide)).set (by decide)).set (by decide))
    have hy₁_ctx : CtxInv G y₁ := hx₁_ctx.of_frame hy₁_fr
    have hy₁_v : y₁.regs vReg = v₀.val :=
      (hy₁_fr.2 vReg (Or.inr (by decide))).trans (by rw [hx₁]; wram_simp)
    have hy₁_u : y₁.regs u = u₀.val :=
      (hy₁_fr.2 u (Or.inr (by decide))).trans (by rw [hx₁]; wram_simp [hu])
    have hy₁_j : y₁.regs j = G.offset u₀ + i :=
      (hy₁_fr.2 j (Or.inr (by decide))).trans (by rw [hx₁]; wram_simp [hj])
    have hy₁_jEnd : y₁.regs jEnd = x.regs jEnd :=
      (hy₁_fr.2 jEnd (Or.inr (by decide))).trans (by rw [hx₁]; wram_simp)
    have hy₁_rnd : y₁.regs rnd = x.regs rnd :=
      (hy₁_fr.2 rnd (Or.inr (by decide))).trans (by rw [hx₁]; wram_simp)
    have hy₁_rndLim : y₁.regs rndLim = x.regs rndLim :=
      (hy₁_fr.2 rndLim (Or.inr (by decide))).trans (by rw [hx₁]; wram_simp)
    have hy₁_ok : y₁.regs ok = x.regs ok :=
      (hy₁_fr.2 ok (Or.inr (by decide))).trans (by rw [hx₁]; wram_simp)
    have hy₁_mem : y₁.mem = x.mem := hy₁_fr.1.trans (by rw [hx₁]; rfl)
    have hdv_mem : y₁.mem (G.distAddrBase + v₀.val) = encodeDist (d v₀) := by
      rw [hy₁_mem]; exact hd v₀
    refine WP.of_execWithin hy₁_ex ?_
    cases hdv : d v₀ with
    | top =>
      have hlt_true : decide ((a : WithTop ℤ) + c₀ < ⊤) = true :=
        decide_eq_true (by rw [← WithTop.coe_add]; exact WithTop.coe_lt_top _)
      wram_exec [hy₁_res, hy₁_ctx.hdbase, hy₁_v, hdv_mem, hdv, encodeDist_top, hy₁_ctx.cone, hf_dv]
      rw [hlt_true]
      refine ⟨(((hy₁_ctx.set (by decide)).set (by decide)).set (by decide)).set (by decide),
        hy₁_mem, by wram_simp; rfl, by wram_simp [hy₁_v], ?_,
        by wram_simp [hy₁_u], by wram_simp [hy₁_j], by wram_simp [hy₁_jEnd],
        by wram_simp [hy₁_rnd], by wram_simp [hy₁_rndLim], by wram_simp [hy₁_ok]⟩
      intro _
      wram_simp
      rw [← WithTop.coe_add, encodeDist_coe]
    | coe b =>
      have hne1_b : Signed.encode b ≠ 1 := encode_ne_one b
      wram_exec [hy₁_res, hy₁_ctx.hdbase, hy₁_v, hdv_mem, hdv, encodeDist_coe, hy₁_ctx.cone, hf_dv,
        hne1_b]
      refine WP.name fun x₂ hx₂ => ?_
      have hx₂_l : x₂.regs Signed.left = Signed.encode (a + c₀) := by rw [hx₂]; wram_simp
      have hx₂_r : x₂.regs Signed.right = Signed.encode b := by rw [hx₂]; wram_simp
      obtain ⟨y₂, hy₂_ex, hy₂_res, hy₂_fr⟩ := Signed.exec_less h2 x₂ hx₂_l hx₂_r
      have hx₂_ctx : CtxInv G x₂ := by
        rw [hx₂]
        exact ((((hy₁_ctx.set (by decide)).set (by decide)).set (by decide)).set
          (by decide)).set (by decide)
      have hy₂_ctx : CtxInv G y₂ := hx₂_ctx.of_frame hy₂_fr
      refine WP.of_execWithin hy₂_ex ⟨by omega, hy₂_ctx,
        hy₂_fr.1.trans (by rw [hx₂]; exact hy₁_mem), ?_,
        (hy₂_fr.2 vReg (Or.inr (by decide))).trans (by rw [hx₂]; wram_simp [hy₁_v]), ?_,
        (hy₂_fr.2 u (Or.inr (by decide))).trans (by rw [hx₂]; wram_simp [hy₁_u]),
        (hy₂_fr.2 j (Or.inr (by decide))).trans (by rw [hx₂]; wram_simp [hy₁_j]),
        (hy₂_fr.2 jEnd (Or.inr (by decide))).trans (by rw [hx₂]; wram_simp [hy₁_jEnd]),
        (hy₂_fr.2 rnd (Or.inr (by decide))).trans (by rw [hx₂]; wram_simp [hy₁_rnd]),
        (hy₂_fr.2 rndLim (Or.inr (by decide))).trans (by rw [hx₂]; wram_simp [hy₁_rndLim]),
        (hy₂_fr.2 ok (Or.inr (by decide))).trans (by rw [hx₂]; wram_simp [hy₁_ok])⟩
      · rw [hy₂_res]
        by_cases hlt : a + c₀ < b <;> simp [hlt, ← WithTop.coe_add]
      · intro _
        have hy₂_sum : y₂.regs sumReg = Signed.encode (a + c₀) :=
          (hy₂_fr.2 sumReg (Or.inr (by decide))).trans (by rw [hx₂]; wram_simp)
        rw [hy₂_sum, ← WithTop.coe_add, encodeDist_coe]

/-- `relaxEdgeCode` executes a single `relax` step in at most `47` instructions while preserving
`CtxInv`, `u`, `j`, `jEnd`, `rnd`, and `rndLim`. -/
private theorem relaxEdgeCode_spec (G : Instance) {w B : ℕ} (hfit : Fits w G.wordBound)
    (hB : B ≤ G.n * G.m * G.maxAbsWeight) (u₀ : Fin G.n) {i : ℕ} (hi : i < (G.adj u₀).length)
    {d : Fin G.n → WithTop ℤ} (hd_mag : MagBounded B d) {x : Data (21 + 9)} (hx : CtxInv G x)
    (hd : DistRep G d x.mem) (hu : x.regs u = u₀.val) (hj : x.regs j = G.offset u₀ + i) :
    ∃ y, ExecWithin w relaxEdgeCode x y 47 ∧ CtxInv G y ∧
      DistRep G (relax d u₀ (G.adj u₀)[i].1 (G.adj u₀)[i].2) y.mem ∧
      y.regs u = u₀.val ∧ y.regs j = G.offset u₀ + i ∧ y.regs jEnd = x.regs jEnd ∧
      y.regs rnd = x.regs rnd ∧ y.regs rndLim = x.regs rndLim := by
  obtain ⟨y₁, hy₁_ex, hy₁_ctx, hy₁_mem, hy₁_res, hy₁_v, hy₁_sum, hy₁_u, hy₁_j, hy₁_jEnd, hy₁_rnd,
    hy₁_rndLim, _⟩ := testImproveCode_spec G hfit hB u₀ hi hd_mag hx hd hu hj
  set v₀ := (G.adj u₀)[i].1
  set c₀ := (G.adj u₀)[i].2
  have hf_dv : Fits w (G.distAddrBase + v₀.val) := by
    have := v₀.isLt
    exact G.fits_of_linear hfit (by unfold Instance.distAddrBase; omega)
  unfold relaxEdgeCode
  suffices ∃ y, ExecWithin w _ y₁ y 3 ∧ CtxInv G y ∧ DistRep G (relax d u₀ v₀ c₀) y.mem ∧
      y.regs u = u₀.val ∧ y.regs j = G.offset u₀ + i ∧ y.regs jEnd = x.regs jEnd ∧
      y.regs rnd = x.regs rnd ∧ y.regs rndLim = x.regs rndLim by
    obtain ⟨y, hy_ex, hy_post⟩ := this
    exact ⟨y, (hy₁_ex.seq hy_ex).mono (by omega), hy_post⟩
  by_cases himp : d u₀ + c₀ < d v₀
  · have hres1 : y₁.regs Signed.result = 1 := by simp [hy₁_res, himp]
    have hsum := hy₁_sum himp
    wram_exec [hres1, hy₁_ctx.cone, hy₁_ctx.hdbase, hy₁_v, hsum, hf_dv]
    refine ⟨(hy₁_ctx.set (by decide)).write_ge
        (by simp only [Instance.outAddrBase, Instance.distAddrBase]; omega),
      ?_, by wram_simp [hy₁_u], by wram_simp [hy₁_j], by wram_simp [hy₁_jEnd],
      by wram_simp [hy₁_rnd], by wram_simp [hy₁_rndLim]⟩
    change DistRep G (relax d u₀ v₀ c₀)
      (Function.update y₁.mem (G.distAddrBase + v₀.val) (encodeDist (d u₀ + c₀)))
    rw [hy₁_mem, show relax d u₀ v₀ c₀ = Function.update d v₀ (d u₀ + c₀) by simp [relax, himp]]
    exact distRep_update hd v₀ (d u₀ + c₀)
  · have hres0 : y₁.regs Signed.result = 0 := by simp [hy₁_res, himp]
    wram_exec [hres0, hy₁_ctx.cone]
    refine ⟨hy₁_ctx.set (by decide), ?_, by wram_simp [hy₁_u], by wram_simp [hy₁_j],
      by wram_simp [hy₁_jEnd], by wram_simp [hy₁_rnd], by wram_simp [hy₁_rndLim]⟩
    change DistRep G (relax d u₀ v₀ c₀) y₁.mem
    rwa [hy₁_mem, show relax d u₀ v₀ c₀ = d by simp [relax, himp]]

/-- `relaxEdgeLoop` scans a suffix `es` of `G.adj u₀`. -/
private theorem relaxEdgeLoop_spec (G : Instance) {w : ℕ} (hfit : Fits w G.wordBound)
    (u₀ : Fin G.n) :
    ∀ (es : List (Fin G.n × ℤ)) (i B : ℕ) (d : Fin G.n → WithTop ℤ) (x : Data (21 + 9))
      (_ : i + es.length = (G.adj u₀).length),
      (∀ k (hk : k < es.length),
        (G.adj u₀)[i + k]'(by omega) = es[k]) →
      B + es.length * G.maxAbsWeight ≤ G.n * G.m * G.maxAbsWeight →
      MagBounded B d → CtxInv G x → DistRep G d x.mem →
      x.regs u = u₀.val → x.regs j = G.offset u₀ + i →
      x.regs jEnd = G.offset u₀ + (G.adj u₀).length →
      ∃ y, ExecWithin w relaxEdgeLoop x y (50 * es.length + 2) ∧ CtxInv G y ∧
        DistRep G (es.foldl (fun d e => relax d u₀ e.1 e.2) d) y.mem ∧
        y.regs u = u₀.val ∧ y.regs rnd = x.regs rnd ∧ y.regs rndLim = x.regs rndLim
  | [], i, _, d, x, hlen, _, _, _, hx, hd, hu, hj, hjEnd => by
    have hexit : ¬(Cond.lt j jEnd).Holds x := by
      simp [Cond.holds_lt, hj, hjEnd, ← hlen]
    exact ⟨x, (Exec.loop_exit hexit).within.mono (by omega), hx, hd, hu, rfl, rfl⟩
  | e :: es, i, B, d, x, hlen, hget, hB, hd_mag, hx, hd, hu, hj, hjEnd => by
    have hlen' : i + (es.length + 1) = (G.adj u₀).length := by
      simpa only [List.length_cons] using hlen
    have hi_lt : i < (G.adj u₀).length := by omega
    have he0 : (G.adj u₀)[i]'hi_lt = e := hget 0 (Nat.zero_lt_succ _)
    have hcond : (Cond.lt j jEnd).Holds x := by
      simp only [Cond.holds_lt, hj, hjEnd]
      omega
    obtain ⟨y₁, hy₁_ex, hy₁_ctx, hy₁_d, hy₁_u, hy₁_j, hy₁_jEnd, hy₁_rnd, hy₁_rndLim⟩ :=
      relaxEdgeCode_spec G hfit (by simp only [List.length_cons, Nat.succ_mul] at hB; omega)
        u₀ hi_lt hd_mag hx hd hu hj
    rw [he0] at hy₁_d
    have hj_lt_m := G.offset_add_lt_m u₀ hi_lt
    have hf_j1 : Fits w (G.offset u₀ + i + 1) := G.fits_of_linear hfit (by omega)
    have hinc : ExecWithin w (ram[ j ← j + cOne ]) y₁ (y₁.set j (G.offset u₀ + i + 1)) 1 := by
      ram_eval [hy₁_j, hy₁_ctx.cone, hf_j1]
    set y₂ := y₁.set j (G.offset u₀ + i + 1)
    have hy₂_ctx : CtxInv G y₂ := hy₁_ctx.set (by decide)
    have hc_abs : e.2.natAbs ≤ G.maxAbsWeight := by
      rw [← he0]
      exact G.natAbs_le_maxAbsWeight (List.getElem_mem hi_lt)
    have hd_mag' : MagBounded (B + G.maxAbsWeight) (relax d u₀ e.1 e.2) :=
      magBounded_relax hd_mag u₀ e.1 hc_abs
    obtain ⟨z, hz_ex, hz_ctx, hz_d, hz_u, hz_rnd, hz_rndLim⟩ :=
      relaxEdgeLoop_spec G hfit u₀ es (i + 1) (B + G.maxAbsWeight) (relax d u₀ e.1 e.2) y₂
        (by omega)
        (fun k hk => by
          simpa [Nat.add_assoc, Nat.add_comm 1 k] using hget (k + 1) (Nat.succ_lt_succ hk))
        (by simp only [List.length_cons, Nat.succ_mul] at hB; omega)
        hd_mag' hy₂_ctx hy₁_d
        (by simpa [y₂] using hy₁_u)
        (by simp [y₂, Nat.add_assoc])
        (by simpa [y₂, hjEnd] using hy₁_jEnd)
    refine ⟨z, (ExecWithin.loop_iter hcond (hy₁_ex.seq hinc) hz_ex).mono ?_, hz_ctx, hz_d, hz_u,
      hz_rnd.trans (by simpa [y₂] using hy₁_rnd),
      hz_rndLim.trans (by simpa [y₂] using hy₁_rndLim)⟩
    simp only [List.length_cons]
    omega

/-- `scanVertexPrep` loads `[offset u₀, offset u₀ + |adj u₀|)` into `[j, jEnd)` in `4`
instructions. -/
private theorem scanVertexPrep_spec (G : Instance) {w : ℕ} (hfit : Fits w G.wordBound)
    (u₀ : Fin G.n) {s : Data (21 + 9)} (hs : CtxInv G s) (hu_eq : s.regs u = u₀.val) :
    ∃ s₁, ExecWithin w scanVertexPrep s s₁ 4 ∧ CtxInv G s₁ ∧ s₁.mem = s.mem ∧
      s₁.regs u = u₀.val ∧ s₁.regs j = G.offset u₀ ∧
      s₁.regs jEnd = G.offset u₀ + (G.adj u₀).length ∧
      s₁.regs rnd = s.regs rnd ∧ s₁.regs rndLim = s.regs rndLim ∧ s₁.regs ok = s.regs ok := by
  have hk_lt := u₀.isLt
  have hf_3k : Fits w (3 + u₀.val) := G.fits_of_linear hfit (by omega)
  have hf_3k1 : Fits w (3 + u₀.val + 1) := G.fits_of_linear hfit (by omega)
  have hoff0 := hs.offset_eq hk_lt.le
  have hoff1 : s.mem (3 + u₀.val + 1) = G.offset u₀ + (G.adj u₀).length := by
    rw [show 3 + u₀.val + 1 = 3 + (u₀.val + 1) by omega,
      hs.offset_eq (Nat.succ_le_of_lt hk_lt), G.offset_succ hk_lt]
  unfold scanVertexPrep
  wram_exec [hs.cthree, hu_eq, hs.cone, hoff0, hoff1, hf_3k, hf_3k1]
  exact ⟨(((hs.set (by decide)).set (by decide)).set (by decide)).set (by decide),
    rfl, by wram_simp [hu_eq], by wram_simp, by wram_simp, by wram_simp, by wram_simp, by wram_simp⟩

/-- `roundCode` executes one complete `round` in at most `9 * G.n + 50 * G.m + 3` instructions. -/
private theorem roundCode_spec (G : Instance) {w B : ℕ} (hfit : Fits w G.wordBound)
    (hB : B + G.m * G.maxAbsWeight ≤ G.n * G.m * G.maxAbsWeight)
    {d : Fin G.n → WithTop ℤ} (hd_mag : MagBounded B d)
    {x : Data (21 + 9)} (hx : CtxInv G x) (hd : DistRep G d x.mem) :
    ∃ y, ExecWithin w roundCode x y (9 * G.n + 50 * G.m + 3) ∧ CtxInv G y ∧
      DistRep G (Lean.BellmanFord.round G.adj (List.finRange G.n) d) y.mem ∧
      y.regs rnd = x.regs rnd ∧ y.regs rndLim = x.regs rndLim := by
  have hvloop : ∀ (us : List (Fin G.n)) (k B₀ : ℕ) (d₀ : Fin G.n → WithTop ℤ) (s : Data (21 + 9)),
      k + us.length = G.n →
      (∀ idx (hidx : idx < us.length), (us[idx]).val = k + idx) →
      B₀ + (us.map fun w => (G.adj w).length).sum * G.maxAbsWeight ≤
        G.n * G.m * G.maxAbsWeight →
      MagBounded B₀ d₀ → CtxInv G s → DistRep G d₀ s.mem → s.regs u = k →
      ∃ z, ExecWithin w (.loop (.lt u nv) (scanVertexCode.seq (ram[ u ← u + cOne ]))) s z
          (9 * us.length + 50 * (us.map fun w => (G.adj w).length).sum + 2) ∧
        CtxInv G z ∧
        DistRep G (us.foldl (fun d u => (G.adj u).foldl (fun d e => relax d u e.1 e.2) d) d₀)
          z.mem ∧
        z.regs rnd = s.regs rnd ∧ z.regs rndLim = s.regs rndLim := by
    intro us
    induction us with
    | nil =>
      intro k _ d₀ s hlen _ _ _ hs hd₀ hu_eq
      have hexit : ¬(Cond.lt u nv).Holds s := by
        simp [Cond.holds_lt, hu_eq, hs.hnv, ← hlen]
      exact ⟨s, (Exec.loop_exit hexit).within.mono (by simp), hs, hd₀, rfl, rfl⟩
    | cons u₀ us ih =>
      intro k B₀ d₀ s hlen hval hB₀ hd₀_mag hs hd₀ hu_eq
      have hk_lt : k < G.n := by simp only [List.length_cons] at hlen; omega
      have hu₀_val : u₀.val = k := by
        have h0 := hval 0 (by simp)
        rwa [List.getElem_cons_zero, Nat.add_zero] at h0
      have hcond : (Cond.lt u nv).Holds s := by
        simp only [Cond.holds_lt, hu_eq, hs.hnv]; omega
      obtain ⟨s₁, hs₁_ex, hs₁_ctx, hs₁_mem, hs₁_u, hs₁_j, hs₁_jEnd, hs₁_rnd, hs₁_rndLim, _⟩ :=
        scanVertexPrep_spec G hfit u₀ hs (hu_eq.trans hu₀_val.symm)
      have hB_u₀ : B₀ + (G.adj u₀).length * G.maxAbsWeight ≤ G.n * G.m * G.maxAbsWeight := by
        simp only [List.map_cons, List.sum_cons, Nat.add_mul] at hB₀
        omega
      obtain ⟨s₂, hs₂_ex, hs₂_ctx, hs₂_d, hs₂_u, hs₂_rnd, hs₂_rndLim⟩ :=
        relaxEdgeLoop_spec G hfit u₀ (G.adj u₀) 0 B₀ d₀ s₁ (by simp)
          (fun idx _ => by simp) hB_u₀ hd₀_mag hs₁_ctx (hs₁_mem ▸ hd₀)
          hs₁_u (by simpa using hs₁_j) hs₁_jEnd
      have hf_k1 : Fits w (u₀.val + 1) := by
        have := u₀.isLt
        exact G.fits_of_linear hfit (by omega)
      have hinc : ExecWithin w (ram[ u ← u + cOne ]) s₂ (s₂.set u (k + 1)) 1 := by
        rw [← hu₀_val]
        ram_eval [hs₂_u, hs₂_ctx.cone, hf_k1]
      set s₃ := s₂.set u (k + 1)
      have hs₃_ctx : CtxInv G s₃ := hs₂_ctx.set (by decide)
      have hd₁_mag : MagBounded (B₀ + (G.adj u₀).length * G.maxAbsWeight)
          ((G.adj u₀).foldl (fun d e => relax d u₀ e.1 e.2) d₀) :=
        magBounded_scan u₀ (G.adj u₀) (fun _ he => G.natAbs_le_maxAbsWeight he) hd₀_mag
      obtain ⟨z, hz_ex, hz_ctx, hz_d, hz_rnd, hz_rndLim⟩ :=
        ih (k + 1) (B₀ + (G.adj u₀).length * G.maxAbsWeight) _ s₃
          (by simp only [List.length_cons] at hlen; omega)
          (fun idx hidx => by
            simpa [Nat.add_assoc, Nat.add_comm 1 idx] using
              hval (idx + 1) (Nat.succ_lt_succ hidx))
          (by
            simp only [List.map_cons, List.sum_cons, Nat.add_mul, ← Nat.add_assoc] at hB₀
            exact hB₀)
          hd₁_mag hs₃_ctx hs₂_d (by simp [s₃])
      have hstep : ExecWithin w (scanVertexCode.seq (ram[ u ← u + cOne ])) s s₃
          (4 + (50 * (G.adj u₀).length + 2) + 1) :=
        (hs₁_ex.seq hs₂_ex).seq hinc
      refine ⟨z, (ExecWithin.loop_iter hcond hstep hz_ex).mono ?_, hz_ctx, hz_d,
        hz_rnd.trans (by simpa [s₃, hs₁_rnd] using hs₂_rnd),
        hz_rndLim.trans (by simpa [s₃, hs₁_rndLim] using hs₂_rndLim)⟩
      simp only [List.length_cons, List.map_cons, List.sum_cons]
      omega
  have hinit_u : ExecWithin (B := .standard) w (ram[ u ← cZero ]) x (x.set u 0) 1 := by
    ram_eval [hx.czero]
  set x₀ := x.set u 0
  have hx₀_ctx : CtxInv G x₀ := hx.set (by decide)
  have hsum : ((List.finRange G.n).map fun w => (G.adj w).length).sum = G.m := by
    rw [← Fin.sum_univ_def]; rfl
  obtain ⟨y, hy_ex, hy_ctx, hy_d, hy_rnd, hy_rndLim⟩ :=
    hvloop (List.finRange G.n) 0 B d x₀ (by simp) (fun idx _ => by simp)
      (by rwa [hsum]) hd_mag hx₀_ctx hd (by simp [x₀])
  refine ⟨y, (hinit_u.seq hy_ex).mono ?_, hy_ctx, hy_d,
    hy_rnd.trans (by simp [x₀]), hy_rndLim.trans (by simp [x₀])⟩
  rw [List.length_finRange, hsum]
  omega

/-- `roundsCode` executes `G.n - 1` relaxation rounds, computing `distances`. -/
private theorem roundsCode_spec (G : Instance) {w : ℕ} (hfit : Fits w G.wordBound)
    {x : Data (21 + 9)} (hx : CtxInv G x) (hd : DistRep G (init G.source) x.mem) :
    ∃ y, ExecWithin w roundsCode x y ((G.n - 1) * (9 * G.n + 50 * G.m + 6) + 4) ∧
      CtxInv G y ∧ DistRep G (distances G.adj (List.finRange G.n) G.source) y.mem := by
  have hrloop : ∀ (rem k : ℕ) (d₀ : Fin G.n → WithTop ℤ) (s : Data (21 + 9)),
      k + rem = G.n - 1 →
      MagBounded (k * (G.m * G.maxAbsWeight)) d₀ →
      CtxInv G s → DistRep G d₀ s.mem →
      s.regs rnd = k → s.regs rndLim = G.n - 1 →
      ∃ z, ExecWithin w (.loop (.lt rnd rndLim) (roundCode.seq (ram[ rnd ← rnd + cOne ]))) s z
          (rem * (9 * G.n + 50 * G.m + 6) + 2) ∧
        CtxInv G z ∧
        DistRep G ((Lean.BellmanFord.round G.adj (List.finRange G.n))^[rem] d₀) z.mem := by
    intro rem
    induction rem with
    | zero =>
      intro k d₀ s hrem _ hs hd₀ hrnd hrndLim
      have hexit : ¬(Cond.lt rnd rndLim).Holds s := by
        simp [Cond.holds_lt, hrnd, hrndLim, ← hrem]
      exact ⟨s, (Exec.loop_exit hexit).within.mono (by simp), hs, hd₀⟩
    | succ rem ih =>
      intro k d₀ s hrem hd₀_mag hs hd₀ hrnd hrndLim
      have hcond : (Cond.lt rnd rndLim).Holds s := by
        simp only [Cond.holds_lt, hrnd, hrndLim]; omega
      have hBk : k * (G.m * G.maxAbsWeight) + G.m * G.maxAbsWeight ≤
          G.n * G.m * G.maxAbsWeight := by
        have hk1 : k + 1 ≤ G.n := by omega
        calc k * (G.m * G.maxAbsWeight) + G.m * G.maxAbsWeight
            = (k + 1) * (G.m * G.maxAbsWeight) := by ring
          _ ≤ G.n * (G.m * G.maxAbsWeight) := Nat.mul_le_mul_right _ hk1
          _ = G.n * G.m * G.maxAbsWeight := by ring
      obtain ⟨s₁, hs₁_ex, hs₁_ctx, hs₁_d, hs₁_rnd, hs₁_rndLim⟩ :=
        roundCode_spec G hfit hBk hd₀_mag hs hd₀
      have hf_k1 : Fits w (k + 1) := G.fits_of_linear hfit (by omega)
      have hinc : ExecWithin w (ram[ rnd ← rnd + cOne ]) s₁ (s₁.set rnd (k + 1)) 1 := by
        ram_eval [hs₁_rnd, hrnd, hs₁_ctx.cone, hf_k1]
      set s₂ := s₁.set rnd (k + 1)
      have hs₂_ctx : CtxInv G s₂ := hs₁_ctx.set (by decide)
      have hd₁_mag : MagBounded ((k + 1) * (G.m * G.maxAbsWeight))
          (Lean.BellmanFord.round G.adj (List.finRange G.n) d₀) := by
        rw [Nat.add_one_mul]
        exact magBounded_round G hd₀_mag
      obtain ⟨z, hz_ex, hz_ctx, hz_d⟩ :=
        ih (k + 1) _ s₂ (by omega) hd₁_mag hs₂_ctx hs₁_d (by simp [s₂])
          (by simpa [s₂, hrndLim] using hs₁_rndLim)
      rw [← Function.iterate_succ_apply] at hz_d
      refine ⟨z, (ExecWithin.loop_iter hcond (hs₁_ex.seq hinc) hz_ex).mono ?_, hz_ctx, hz_d⟩
      have hstep_mul := Nat.add_one_mul rem (9 * G.n + 50 * G.m + 6)
      omega
  have hf_lim : Fits w (G.n - 1) := G.fits_of_linear hfit (by omega)
  have hprep : ExecWithin w (ram[ rndLim ← nv - cOne; rnd ← cZero ]) x
      ((x.set rndLim (G.n - 1)).set rnd 0) 2 := by
    ram_eval [hx.hnv, hx.cone, hx.czero, hf_lim]
  set x₀ := (x.set rndLim (G.n - 1)).set rnd 0
  have hx₀_ctx : CtxInv G x₀ := (hx.set (by decide)).set (by decide)
  obtain ⟨y, hy_ex, hy_ctx, hy_d⟩ :=
    hrloop (G.n - 1) 0 (init G.source) x₀ (by simp)
      (by simpa using magBounded_init G.source) hx₀_ctx hd (by simp [x₀]) (by simp [x₀])
  refine ⟨y, (hprep.seq hy_ex).mono (by omega), hy_ctx, ?_⟩
  simpa only [distances, List.length_finRange] using hy_d

/-- `checkEdgeCode` tests `d v ≤ d u + c` without writing memory. -/
private theorem checkEdgeCode_spec (G : Instance) {w B : ℕ} (hfit : Fits w G.wordBound)
    (hB : B ≤ G.n * G.m * G.maxAbsWeight) (u₀ : Fin G.n) {i : ℕ} (hi : i < (G.adj u₀).length)
    {d : Fin G.n → WithTop ℤ} (hd_mag : MagBounded B d) (b₀ : Bool)
    {x : Data (21 + 9)} (hx : CtxInv G x) (hd : DistRep G d x.mem)
    (hu : x.regs u = u₀.val) (hj : x.regs j = G.offset u₀ + i) (hok : x.regs ok = b₀.toNat) :
    ∃ y, ExecWithin w checkEdgeCode x y 47 ∧ CtxInv G y ∧ y.mem = x.mem ∧
      y.regs ok = (b₀ && decide (d (G.adj u₀)[i].1 ≤ d u₀ + (G.adj u₀)[i].2)).toNat ∧
      y.regs u = u₀.val ∧ y.regs j = G.offset u₀ + i ∧ y.regs jEnd = x.regs jEnd := by
  obtain ⟨y₁, hy₁_ex, hy₁_ctx, hy₁_mem, hy₁_res, _, _, hy₁_u, hy₁_j, hy₁_jEnd, _, _, hy₁_ok⟩ :=
    testImproveCode_spec G hfit hB u₀ hi hd_mag hx hd hu hj
  have hy₁_ok' : y₁.regs ok = b₀.toNat := hy₁_ok.trans hok
  set v₀ := (G.adj u₀)[i].1
  set c₀ := (G.adj u₀)[i].2
  suffices ∃ y, ExecWithin (B := .standard) w
      (ram[ if result = cOne then [ ok ← cZero ] else [ dv ← dv ] ])
      y₁ y 3 ∧ CtxInv G y ∧ y.mem = x.mem ∧
      y.regs ok = (b₀ && decide (d v₀ ≤ d u₀ + c₀)).toNat ∧
      y.regs u = u₀.val ∧ y.regs j = G.offset u₀ + i ∧ y.regs jEnd = x.regs jEnd by
    obtain ⟨y, hy_ex, hy_post⟩ := this
    exact ⟨y, (hy₁_ex.seq hy_ex).mono (by omega), hy_post⟩
  by_cases himp : d u₀ + c₀ < d v₀
  · have hres1 : y₁.regs Signed.result = 1 := by simp [hy₁_res, himp]
    have hle_false : decide (d v₀ ≤ d u₀ + c₀) = false := decide_eq_false (not_le.2 himp)
    wram_exec [hres1, hy₁_ctx.cone, hy₁_ctx.czero]
    rw [hle_false, Bool.and_false]
    exact ⟨hy₁_ctx.set (by decide), hy₁_mem, Data.set_regs_self _ _ _,
      by wram_simp [hy₁_u], by wram_simp [hy₁_j], by wram_simp [hy₁_jEnd]⟩
  · have hres0 : y₁.regs Signed.result = 0 := by simp [hy₁_res, himp]
    have hle_true : decide (d v₀ ≤ d u₀ + c₀) = true := decide_eq_true (not_lt.1 himp)
    wram_exec [hres0, hy₁_ctx.cone]
    rw [hle_true, Bool.and_true]
    exact ⟨hy₁_ctx.set (by decide), hy₁_mem, by wram_simp [hy₁_ok'],
      by wram_simp [hy₁_u], by wram_simp [hy₁_j], by wram_simp [hy₁_jEnd]⟩

/-- `checkEdgeLoop` tests a suffix `es` of `G.adj u₀` without writing memory. -/
private theorem checkEdgeLoop_spec (G : Instance) {w B : ℕ} (hfit : Fits w G.wordBound)
    (hB : B ≤ G.n * G.m * G.maxAbsWeight) (u₀ : Fin G.n) {d : Fin G.n → WithTop ℤ}
    (hd_mag : MagBounded B d) :
    ∀ (es : List (Fin G.n × ℤ)) (i : ℕ) (b₀ : Bool) (x : Data (21 + 9))
      (_ : i + es.length = (G.adj u₀).length),
      (∀ k (hk : k < es.length), (G.adj u₀)[i + k]'(by omega) = es[k]) →
      CtxInv G x → DistRep G d x.mem →
      x.regs u = u₀.val → x.regs j = G.offset u₀ + i →
      x.regs jEnd = G.offset u₀ + (G.adj u₀).length → x.regs ok = b₀.toNat →
      ∃ y, ExecWithin w checkEdgeLoop x y (50 * es.length + 2) ∧ CtxInv G y ∧ y.mem = x.mem ∧
        y.regs ok = (b₀ && es.all fun e => decide (d e.1 ≤ d u₀ + e.2)).toNat ∧
        y.regs u = u₀.val
  | [], i, b₀, x, hlen, _, hx, _, hu, hj, hjEnd, hok => by
    have hexit : ¬(Cond.lt j jEnd).Holds x := by
      simp [Cond.holds_lt, hj, hjEnd, ← hlen]
    exact ⟨x, (Exec.loop_exit hexit).within.mono (by simp), hx, rfl, by simpa using hok, hu⟩
  | e :: es, i, b₀, x, hlen, hget, hx, hd, hu, hj, hjEnd, hok => by
    have hlen' : i + (es.length + 1) = (G.adj u₀).length := by
      simpa only [List.length_cons] using hlen
    have hi_lt : i < (G.adj u₀).length := by omega
    have he0 : (G.adj u₀)[i]'hi_lt = e := hget 0 (Nat.zero_lt_succ _)
    have hcond : (Cond.lt j jEnd).Holds x := by
      simp only [Cond.holds_lt, hj, hjEnd]; omega
    obtain ⟨y₁, hy₁_ex, hy₁_ctx, hy₁_mem, hy₁_ok, hy₁_u, hy₁_j, hy₁_jEnd⟩ :=
      checkEdgeCode_spec G hfit hB u₀ hi_lt hd_mag b₀ hx hd hu hj hok
    rw [he0] at hy₁_ok
    have hj_lt_m := G.offset_add_lt_m u₀ hi_lt
    have hf_j1 : Fits w (G.offset u₀ + i + 1) := G.fits_of_linear hfit (by omega)
    have hinc : ExecWithin w (ram[ j ← j + cOne ]) y₁ (y₁.set j (G.offset u₀ + i + 1)) 1 := by
      ram_eval [hy₁_j, hy₁_ctx.cone, hf_j1]
    set y₂ := y₁.set j (G.offset u₀ + i + 1)
    have hy₂_ctx : CtxInv G y₂ := hy₁_ctx.set (by decide)
    obtain ⟨z, hz_ex, hz_ctx, hz_mem, hz_ok, hz_u⟩ :=
      checkEdgeLoop_spec G hfit hB u₀ hd_mag es (i + 1)
        (b₀ && decide (d e.1 ≤ d u₀ + e.2)) y₂
        (by omega)
        (fun k hk => by
          simpa [Nat.add_assoc, Nat.add_comm 1 k] using hget (k + 1) (Nat.succ_lt_succ hk))
        hy₂_ctx (hy₁_mem ▸ hd)
        (by simpa [y₂] using hy₁_u)
        (by simp [y₂, Nat.add_assoc])
        (by simpa [y₂, hjEnd] using hy₁_jEnd)
        (by simpa [y₂] using hy₁_ok)
    refine ⟨z, (ExecWithin.loop_iter hcond (hy₁_ex.seq hinc) hz_ex).mono ?_, hz_ctx,
      hz_mem.trans hy₁_mem, ?_, hz_u⟩
    · simp only [List.length_cons]; omega
    · simpa only [List.all_cons, Bool.and_assoc] using hz_ok

/-- `checkCode` computes `check G.adj (List.finRange G.n) d` in `ok` without writing memory. -/
private theorem checkCode_spec (G : Instance) {w B : ℕ} (hfit : Fits w G.wordBound)
    (hB : B ≤ G.n * G.m * G.maxAbsWeight) {d : Fin G.n → WithTop ℤ} (hd_mag : MagBounded B d)
    {x : Data (21 + 9)} (hx : CtxInv G x) (hd : DistRep G d x.mem) :
    ∃ y, ExecWithin w checkCode x y (9 * G.n + 50 * G.m + 4) ∧ CtxInv G y ∧ y.mem = x.mem ∧
      y.regs ok = (check G.adj (List.finRange G.n) d).toNat := by
  have hvloop : ∀ (us : List (Fin G.n)) (k : ℕ) (b₀ : Bool) (s : Data (21 + 9)),
      k + us.length = G.n →
      (∀ idx (hidx : idx < us.length), (us[idx]).val = k + idx) →
      CtxInv G s → DistRep G d s.mem → s.regs u = k → s.regs ok = b₀.toNat →
      ∃ z, ExecWithin w (.loop (.lt u nv) (checkVertexCode.seq (ram[ u ← u + cOne ]))) s z
          (9 * us.length + 50 * (us.map fun w => (G.adj w).length).sum + 2) ∧
        CtxInv G z ∧ z.mem = s.mem ∧
        z.regs ok =
          (b₀ && us.all fun u₀ => (G.adj u₀).all fun e => decide (d e.1 ≤ d u₀ + e.2)).toNat := by
    intro us
    induction us with
    | nil =>
      intro k b₀ s hlen _ hs _ hu_eq hok
      have hexit : ¬(Cond.lt u nv).Holds s := by
        simp [Cond.holds_lt, hu_eq, hs.hnv, ← hlen]
      exact ⟨s, (Exec.loop_exit hexit).within.mono (by simp), hs, rfl, by simpa using hok⟩
    | cons u₀ us ih =>
      intro k b₀ s hlen hval hs hd₀ hu_eq hok
      have hk_lt : k < G.n := by simp only [List.length_cons] at hlen; omega
      have hu₀_val : u₀.val = k := by
        have h0 := hval 0 (by simp)
        rwa [List.getElem_cons_zero, Nat.add_zero] at h0
      have hcond : (Cond.lt u nv).Holds s := by
        simp only [Cond.holds_lt, hu_eq, hs.hnv]; omega
      obtain ⟨s₁, hs₁_ex, hs₁_ctx, hs₁_mem, hs₁_u, hs₁_j, hs₁_jEnd, _, _, hs₁_ok⟩ :=
        scanVertexPrep_spec G hfit u₀ hs (hu_eq.trans hu₀_val.symm)
      obtain ⟨s₂, hs₂_ex, hs₂_ctx, hs₂_mem, hs₂_ok, hs₂_u⟩ :=
        checkEdgeLoop_spec G hfit hB u₀ hd_mag (G.adj u₀) 0 b₀ s₁ (by simp)
          (fun idx _ => by simp) hs₁_ctx (hs₁_mem ▸ hd₀) hs₁_u (by simpa using hs₁_j)
          hs₁_jEnd (hs₁_ok.trans hok)
      have hf_k1 : Fits w (u₀.val + 1) := by
        have := u₀.isLt
        exact G.fits_of_linear hfit (by omega)
      have hinc : ExecWithin w (ram[ u ← u + cOne ]) s₂ (s₂.set u (k + 1)) 1 := by
        rw [← hu₀_val]
        ram_eval [hs₂_u, hs₂_ctx.cone, hf_k1]
      set s₃ := s₂.set u (k + 1)
      have hs₃_ctx : CtxInv G s₃ := hs₂_ctx.set (by decide)
      obtain ⟨z, hz_ex, hz_ctx, hz_mem, hz_ok⟩ :=
        ih (k + 1) (b₀ && (G.adj u₀).all fun e => decide (d e.1 ≤ d u₀ + e.2)) s₃
          (by simp only [List.length_cons] at hlen; omega)
          (fun idx hidx => by
            simpa [Nat.add_assoc, Nat.add_comm 1 idx] using hval (idx + 1) (Nat.succ_lt_succ hidx))
          hs₃_ctx ((hs₂_mem.trans hs₁_mem) ▸ hd₀) (by simp [s₃]) (by simpa [s₃] using hs₂_ok)
      have hstep : ExecWithin w (checkVertexCode.seq (ram[ u ← u + cOne ])) s s₃
          (4 + (50 * (G.adj u₀).length + 2) + 1) :=
        (hs₁_ex.seq hs₂_ex).seq hinc
      refine ⟨z, (ExecWithin.loop_iter hcond hstep hz_ex).mono ?_, hz_ctx,
        hz_mem.trans (hs₂_mem.trans hs₁_mem), ?_⟩
      · simp only [List.length_cons, List.map_cons, List.sum_cons]; omega
      · simpa only [List.all_cons, Bool.and_assoc] using hz_ok
  have hprep : ExecWithin (B := .standard) w (ram[ ok ← cOne; u ← cZero ]) x
      ((x.set ok 1).set u 0) 2 := by
    ram_eval [hx.cone, hx.czero]
  set x₀ := (x.set ok 1).set u 0
  have hx₀_ctx : CtxInv G x₀ := (hx.set (by decide)).set (by decide)
  have hsum : ((List.finRange G.n).map fun w => (G.adj w).length).sum = G.m := by
    rw [← Fin.sum_univ_def]; rfl
  obtain ⟨y, hy_ex, hy_ctx, hy_mem, hy_ok⟩ :=
    hvloop (List.finRange G.n) 0 true x₀ (by simp) (fun idx _ => by simp)
      hx₀_ctx hd (by simp [x₀]) (by simp [x₀])
  refine ⟨y, (hprep.seq hy_ex).mono ?_, hy_ctx, hy_mem, ?_⟩
  · rw [List.length_finRange, hsum]; omega
  · simpa only [Bool.true_and, check] using hy_ok

/-! ### Main Word-RAM theorems -/

/-- Structured execution of `solver` leaves `outAddrBase` in `outBase` and `answerWords G` in
`outputList y.mem outAddrBase` within `64 * G.n * (G.n + G.m) - 1` instructions. -/
theorem solver_spec (G : Instance) {w : ℕ} (hfit : Fits w G.wordBound) :
    ∃ y, ExecWithin w solver (Data.init G.encode) y (64 * G.n * (G.n + G.m) - 1) ∧
      y.regs outBase = G.outAddrBase ∧ outputList y.mem (y.regs outBase) = answerWords G := by
  obtain ⟨y₁, hy₁_ex, hy₁_ctx⟩ := setupCode_spec G hfit
  obtain ⟨y₂, hy₂_ex, hy₂_ctx, hy₂_d⟩ := initCode_spec G hfit hy₁_ctx
  obtain ⟨y₃, hy₃_ex, hy₃_ctx, hy₃_d⟩ := roundsCode_spec G hfit hy₂_ctx hy₂_d
  set dStar := distances G.adj (List.finRange G.n) G.source
  have hdStar_mag : MagBounded ((G.n - 1) * (G.m * G.maxAbsWeight)) dStar := by
    simpa only [dStar, distances, List.length_finRange, Nat.zero_add] using
      magBounded_iterate_round G (G.n - 1) (magBounded_init G.source)
  have hBStar : (G.n - 1) * (G.m * G.maxAbsWeight) ≤ G.n * G.m * G.maxAbsWeight :=
    calc (G.n - 1) * (G.m * G.maxAbsWeight)
        ≤ G.n * (G.m * G.maxAbsWeight) := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
      _ = G.n * G.m * G.maxAbsWeight := by ring
  obtain ⟨y₄, hy₄_ex, hy₄_ctx, hy₄_mem, hy₄_ok⟩ :=
    checkCode_spec G hfit hBStar hdStar_mag hy₃_ctx hy₃_d
  have hy₄_d : DistRep G dStar y₄.mem := hy₄_mem ▸ hy₃_d
  have hfinish : ∃ y₅, ExecWithin w finishCode y₄ y₅ 3 ∧
      y₅.regs outBase = G.outAddrBase ∧ outputList y₅.mem G.outAddrBase = answerWords G := by
    cases hchk : check G.adj (List.finRange G.n) dStar
    · have hok0 : y₄.regs ok = 0 := by simp [hy₄_ok, hchk]
      unfold finishCode
      wram_exec [hok0, hy₄_ctx.cone, hy₄_ctx.houtBase, hy₄_ctx.czero]
      refine ⟨by wram_simp [hy₄_ctx.houtBase], ?_⟩
      rw [outputList_eq_iff]
      refine ⟨?_, ?_⟩
      · rw [Data.write_mem_self]
        simp [answerWords, bellmanFord, dStar, hchk]
      · simpa [answerWords, bellmanFord, dStar, hchk] using Block.holdsList_nil _ _
    · have hok1 : y₄.regs ok = 1 := by simp [hy₄_ok, hchk]
      unfold finishCode
      wram_exec [hok1, hy₄_ctx.cone, hy₄_ctx.houtBase, hy₄_ctx.hnv]
      refine ⟨by wram_simp [hy₄_ctx.houtBase], ?_⟩
      rw [outputList_eq_iff]
      have hans : answerWords G = (List.finRange G.n).map fun v => encodeDist (dStar v) := by
        simp [answerWords, bellmanFord, dStar, hchk]
      rw [hans]
      refine ⟨?_, fun i => ?_⟩
      · rw [Data.write_mem_self]
        simp
      · have hi_lt : i.val < G.n := by simpa using i.isLt
        dsimp only [Block.read]
        rw [Data.write_mem_of_ne (by omega),
          show G.outAddrBase + 1 + i.val = G.distAddrBase + i.val by
            unfold Instance.outAddrBase Instance.distAddrBase; omega,
          hy₄_d ⟨i.val, hi_lt⟩]
        simp
  obtain ⟨y₅, hy₅_ex, hy₅_out, hy₅_list⟩ := hfinish
  refine ⟨y₅, (hy₁_ex.seq (hy₂_ex.seq (hy₃_ex.seq (hy₄_ex.seq hy₅_ex)))).mono ?_,
    hy₅_out, by rwa [hy₅_out]⟩
  have hn1 : 1 ≤ G.n := G.n_pos
  have hsub : G.n - 1 + 1 = G.n := by omega
  have hmul : (G.n - 1) * (9 * G.n + 50 * G.m + 6) + (9 * G.n + 50 * G.m + 6) =
      G.n * (9 * G.n + 50 * G.m + 6) := by
    rw [← Nat.succ_mul, ← Nat.add_one, hsub]
  have hquad : 11 + ((5 * G.n + 5) + (((G.n - 1) * (9 * G.n + 50 * G.m + 6) + 4) +
      ((9 * G.n + 50 * G.m + 4) + 3))) + 1 ≤ 64 * G.n * (G.n + G.m) := by
    nlinarith
  omega

/-- **Bellman–Ford on the word RAM (`O(|V|(|V| + |E|))`).** At every word width `w` with
`Fits w G.wordBound`, `program` halts within `64 * G.n * (G.n + G.m)` instructions (including the
final `halt`) and outputs `answerWords G`: `[]` if and only if a negative cycle is reachable from
`G.source`, and the encoded shortest-path distances `[encodeDist (d 0), …, encodeDist (d (n - 1))]`
otherwise. -/
theorem program_spec (G : Instance) {w : ℕ} (hfit : Fits w G.wordBound) :
    ∃ steps ≤ 64 * G.n * (G.n + G.m),
      ExecutesList w program (State.init G.encode) (answerWords G) steps := by
  obtain ⟨y, ⟨steps, hsteps, hexec⟩, hyout, hylist⟩ := solver_spec G hfit
  have hlen := length_answerWords_le G
  have hpos : 1 ≤ 64 * G.n * (G.n + G.m) := by
    have := G.n_pos
    nlinarith
  have hfit_out : Fits w (y.regs outBase + (outputList y.mem (y.regs outBase)).length) := by
    rw [hylist, hyout]
    exact G.fits_of_linear hfit (by unfold Instance.outAddrBase; omega)
  refine ⟨steps + 1, by omega, ?_⟩
  have hex := hexec.executesList outBase hfit_out
  rwa [hylist] at hex

/-- Fixed-program `Program.ComputesListInTime` certificate for Word-RAM Bellman–Ford. -/
theorem computesListInTime_program :
    program.ComputesListInTime (fun _ G => G.encode)
      (fun G _ => 64 * G.n * (G.n + G.m))
      (fun G w => Fits w G.wordBound)
      answerWords := by
  intro G w hfit _
  obtain ⟨steps, hle, hex⟩ := program_spec G hfit
  exact ⟨steps, hex, hle⟩

/-- `program` does not read the word width (`width%`). -/
theorem not_readsWidth_program : ¬ program.ReadsWidth := by
  apply Code.not_readsWidth_program
  decide +kernel

/-- `program` is deterministic (`rand`-free). -/
theorem isRandFree_program : program.IsRandFree := by
  rw [program, Code.isRandFree_program]
  decide +kernel

end Cslib.Algorithms.WordRAM.BellmanFord
