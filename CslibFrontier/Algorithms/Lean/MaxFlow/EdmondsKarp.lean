/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.MaxFlow.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card

/-!
# Edmonds–Karp Shortest-Augmenting-Path Algorithm

Formalizes the **Edmonds–Karp algorithm** ([EdmondsKarp1972], Section 1, Theorem 1, pp. 249–253;
[CLRS2009], Section 26.2, Lemma 26.7 and Theorem 26.8, pp. 727–730): augmenting an integral network
flow along breadth-first (fewest-arc) residual `s`-`t` paths guarantees monotonic residual
shortest-path distances and terminates in strongly polynomial augmentation count independent of arc
capacities.

## Mathematical and algorithmic overview

1. **Residual shortest-path distance (`Flow.resDist`):** for any finite vertex type `V`,
   `f.resDist v : ℕ` is the minimum arc length `< |V|` of a positive-residual-capacity walk from
   `N.s` to `v`, or `|V|` when `v` is unreachable.
2. **Distance monotonicity (`Flow.resDist_le_augmentByBottleneck`):** augmenting `f` along any
   shortest augmenting path `p` (`IsShortestAugmentingPath`) never decreases `resDist v` for any
   vertex `v` ([EdmondsKarp1972], p. 251; [CLRS2009], Lemma 26.7, pp. 727–728).
3. **Critical-arc bound (`Network.shortestAugmentingSeq_length_le`):** each directed residual pair
   `(u, v) ∈ N.symArcs` becomes a bottleneck critical arc at most `|V| / 2` times because
   `resDist u` increases by at least `2` between critical occurrences, bounding any sequence of
   shortest-path augmentations by `N.symArcs.card * (|V| / 2) ≤ |V| * N.posArcs.card`
   ([CLRS2009], Theorem 26.8, p. 729; compare [EdmondsKarp1972], Theorem 1, p. 251, which obtains
   `(|V|^3 - |V|) / 4` by combining source- and sink-distance monotonicity).
4. **Pure executable solver (`edmondsKarp`, `edmondsKarpDense`):** over `Network (Fin n)` with
   candidate neighbor lists `adj : Fin n → List (Fin n)`, maintains an explicit `n × n` `Vector`
   matrix (`FlowMatrix N`) and performs breadth-first shortest-path augmentations (`bfs`), returning
   an integral maximum flow, its minimum `s`-`t` cut, and the number of augmentations performed
   (`edmondsKarp_correct`, `edmondsKarpDense_correct`). For the checked machine running-time bound
   (`O(n ^ 5)` dense Word-RAM instructions), see `CslibFrontier.Algorithms.WordRAM.EdmondsKarp`.

## Main definitions

* `Cslib.Algorithms.Lean.MaxFlow.Network.Flow.HasResWalkOfLen`, `Flow.resDist`,
  `Flow.IsShortestAugmentingPath`: residual walk lengths, capped shortest-path distances, and
  fewest-arc augmenting paths.
* `Cslib.Algorithms.Lean.MaxFlow.Network.symArcs`, `Network.posArcs`,
  `Network.IsShortestAugmentingSeq`: active directed residual pairs and shortest-augmentation
  traces.
* `Cslib.Algorithms.Lean.MaxFlow.AdjValid`, `adjSteps`, `defaultAdj`, `FlowMatrix`, `bfs`,
  `Output`, `edmondsKarp`, `edmondsKarpDense`: pure executable BFS and Edmonds–Karp solver over
  `Fin n`.

## Main results

* `Cslib.Algorithms.Lean.MaxFlow.Network.Flow.resDist_le_augmentByBottleneck`: shortest-path
  distance monotonicity.
* `Cslib.Algorithms.Lean.MaxFlow.Network.shortestAugmentingSeq_length_le` and
  `shortestAugmentingSeq_length_le_card_mul_posArcs`: polynomial augmentation bounds.
* `Cslib.Algorithms.Lean.MaxFlow.edmondsKarp_correct` and `edmondsKarpDense_correct`: max-flow /
  min-cut certification and augmentation-count bounds.

## References

* [J. Edmonds and R. M. Karp, *Theoretical Improvements in Algorithmic Efficiency for Network Flow
  Problems*][EdmondsKarp1972]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest, and C. Stein,
  *Introduction to Algorithms*][CLRS2009]
-/

public section

namespace Cslib.Algorithms.Lean.MaxFlow

namespace Network

section DistanceAndCriticalArcs

variable {V : Type*} [Fintype V] (N : Network V)

/-- Active directed pairs `(u, v)` with `u ≠ v` that can ever carry positive residual capacity in
`N` (either `N.cap u v > 0` or `N.cap v u > 0`). -/
@[expose] def symArcs [DecidableEq V] : Finset (V × V) :=
  Finset.univ.filter fun e => e.1 ≠ e.2 ∧ 0 < N.cap e.1 e.2 + N.cap e.2 e.1

/-- Non-loop directed arcs `(u, v)` with positive capacity `N.cap u v > 0` in `N`. -/
@[expose] def posArcs [DecidableEq V] : Finset (V × V) :=
  Finset.univ.filter fun e => e.1 ≠ e.2 ∧ 0 < N.cap e.1 e.2

theorem card_symArcs_le_two_mul_posArcs [DecidableEq V] :
    N.symArcs.card ≤ 2 * N.posArcs.card := by
  have hsub : N.symArcs ⊆ N.posArcs ∪ N.posArcs.image Prod.swap := by
    rintro ⟨u, v⟩ he
    simp only [symArcs, Finset.mem_filter, Finset.mem_univ, true_and] at he
    by_cases huv : 0 < N.cap u v
    · exact Finset.mem_union_left _ (by simp [posArcs, he.1, huv])
    · exact Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨(v, u), by simp [posArcs, he.1.symm]; omega, rfl⟩)
  have := (Finset.card_le_card hsub).trans
    ((Finset.card_union_le _ _).trans (Nat.add_le_add_left Finset.card_image_le _))
  omega

private theorem card_symArcs_mul_half_le [DecidableEq V] (m : ℕ) :
    N.symArcs.card * (m / 2) ≤ m * N.posArcs.card :=
  calc N.symArcs.card * (m / 2)
      ≤ 2 * N.posArcs.card * (m / 2) := Nat.mul_le_mul_right _ N.card_symArcs_le_two_mul_posArcs
    _ = N.posArcs.card * (2 * (m / 2)) := by rw [Nat.mul_comm 2, Nat.mul_assoc]
    _ ≤ N.posArcs.card * m := Nat.mul_le_mul_left _ (Nat.mul_div_le m 2)
    _ = m * N.posArcs.card := Nat.mul_comm _ _

theorem card_symArcs_le_card_sq [DecidableEq V] :
    N.symArcs.card ≤ Fintype.card V * Fintype.card V :=
  (Finset.card_le_univ _).trans_eq (Fintype.card_prod V V)

theorem card_symArcs_le_mul_pred [DecidableEq V] :
    N.symArcs.card ≤ Fintype.card V * (Fintype.card V - 1) := by
  have hsub : N.symArcs ⊆ Finset.univ.offDiag := fun e he => by
    simp only [symArcs, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_offDiag] at he ⊢
    exact he.1
  exact (Finset.card_le_card hsub).trans_eq <| by
    rw [Finset.offDiag_card, Finset.card_univ, ← Nat.mul_sub_one]

namespace Flow

variable {N}

/-- Existence of a positive-residual-capacity walk of exact arc length `k` from `N.s` to `v`. -/
inductive HasResWalkOfLen (f : N.Flow) : V → ℕ → Prop
  | zero : HasResWalkOfLen f N.s 0
  | succ {u v : V} {k : ℕ} : HasResWalkOfLen f u k → 0 < f.resCap u v → HasResWalkOfLen f v (k + 1)

theorem HasResWalkOfLen.resReachable {f : N.Flow} {v : V} {k : ℕ}
    (h : f.HasResWalkOfLen v k) : f.ResReachable N.s v := by
  induction h with
  | zero => exact .refl
  | succ _ hstep ih => exact ih.tail hstep

private theorem hasResWalkOfLen_add (f : N.Flow) (q : List V) {u w : V} {k : ℕ}
    (hwalk : f.HasResWalkOfLen u k) (hu : q.head? = some u) (hw : q.getLast? = some w)
    (hq : ∀ e ∈ pathArcs q, 0 < f.resCap e.1 e.2) :
    f.HasResWalkOfLen w (k + (pathArcs q).length) := by
  induction q generalizing u k with
  | nil => simp at hu
  | cons x rest ih =>
    simp only [List.head?_cons, Option.some.injEq] at hu
    subst hu
    rcases rest with _ | ⟨y, rest'⟩
    · simp only [List.getLast?_singleton, Option.some.injEq] at hw
      subst hw
      simpa using hwalk
    · have hrec := ih (hwalk.succ (hq (x, y) List.mem_cons_self)) rfl (by simpa using hw)
        fun e he => hq e (List.mem_cons_of_mem _ he)
      simpa [Nat.add_assoc, Nat.add_comm] using hrec

theorem hasResWalkOfLen_of_walk (f : N.Flow) {p : List V} {v : V}
    (hs : p.head? = some N.s) (ht : p.getLast? = some v)
    (harcs : ∀ e ∈ pathArcs p, 0 < f.resCap e.1 e.2) :
    f.HasResWalkOfLen v (pathArcs p).length := by
  simpa using hasResWalkOfLen_add f p .zero hs ht harcs

theorem exists_hasResWalkOfLen_lt_card_of_resReachable (f : N.Flow) {v : V}
    (h : f.ResReachable N.s v) : ∃ k < Fintype.card V, f.HasResWalkOfLen v k := by
  obtain ⟨q, hnodup, hqs, hqt, hqarcs⟩ := exists_nodup_list_of_reflTransGen h
  have hq_ne : q ≠ [] := by rintro rfl; simp at hqs
  have := hnodup.length_le_card
  have := length_pathArcs_add_one hq_ne
  exact ⟨(pathArcs q).length, by omega, f.hasResWalkOfLen_of_walk hqs hqt hqarcs⟩

/-- Residual shortest-path distance from `N.s` to `v`, capped at `Fintype.card V` when `v` is
unreachable. -/
noncomputable def resDist (f : N.Flow) (v : V) : ℕ :=
  open scoped Classical in
  if h : ∃ k, k < Fintype.card V ∧ f.HasResWalkOfLen v k then Nat.find h else Fintype.card V

theorem resDist_le_card (f : N.Flow) (v : V) : f.resDist v ≤ Fintype.card V := by
  classical
  unfold resDist
  split_ifs with h
  · exact (Nat.find_spec h).1.le
  · exact le_rfl

theorem resDist_lt_card_iff_resReachable (f : N.Flow) (v : V) :
    f.resDist v < Fintype.card V ↔ f.ResReachable N.s v := by
  classical
  unfold resDist
  split_ifs with h
  · exact ⟨fun _ => (Nat.find_spec h).2.resReachable, fun _ => (Nat.find_spec h).1⟩
  · exact ⟨fun hlt => absurd hlt (Nat.lt_irrefl _), fun hreach =>
      False.elim (h (f.exists_hasResWalkOfLen_lt_card_of_resReachable hreach))⟩

theorem hasResWalkOfLen_resDist (f : N.Flow) {v : V} (hlt : f.resDist v < Fintype.card V) :
    f.HasResWalkOfLen v (f.resDist v) := by
  classical
  unfold resDist at hlt ⊢
  split_ifs at hlt ⊢ with h
  · exact (Nat.find_spec h).2
  · omega

theorem resDist_le_of_hasResWalkOfLen (f : N.Flow) {v : V} {k : ℕ}
    (hwalk : f.HasResWalkOfLen v k) : f.resDist v ≤ k := by
  classical
  by_cases hk : k < Fintype.card V
  · simpa [resDist, show ∃ m, m < Fintype.card V ∧ f.HasResWalkOfLen v m from ⟨k, hk, hwalk⟩]
      using Nat.find_min' (⟨k, hk, hwalk⟩ : ∃ m, m < Fintype.card V ∧ f.HasResWalkOfLen v m)
        ⟨hk, hwalk⟩
  · exact (f.resDist_le_card v).trans (Nat.le_of_not_lt hk)

@[simp]
theorem resDist_source (f : N.Flow) : f.resDist N.s = 0 :=
  Nat.eq_zero_of_le_zero (f.resDist_le_of_hasResWalkOfLen .zero)

theorem eq_source_of_resDist_eq_zero (f : N.Flow) {v : V} (hv : f.resDist v = 0) : v = N.s := by
  have : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨N.s⟩
  have hwalk := f.hasResWalkOfLen_resDist (v := v) (by omega)
  cases hv ▸ hwalk; rfl

/-- Residual shortest-path triangle inequality: positive residual capacity on `(u, v)` gives
`f.resDist v ≤ f.resDist u + 1` unconditionally (including when `u` is unreachable). -/
theorem resDist_le_add_one_of_pos_resCap (f : N.Flow) {u v : V} (hpos : 0 < f.resCap u v) :
    f.resDist v ≤ f.resDist u + 1 := by
  by_cases hlt : f.resDist u < Fintype.card V
  · exact f.resDist_le_of_hasResWalkOfLen ((f.hasResWalkOfLen_resDist hlt).succ hpos)
  · exact (f.resDist_le_card v).trans (by omega)

theorem exists_pred_of_resDist_eq_succ (f : N.Flow) {v : V} {k : ℕ}
    (hk : k + 1 < Fintype.card V) (hv : f.resDist v = k + 1) :
    ∃ u : V, f.resDist u = k ∧ 0 < f.resCap u v := by
  have hwalk := hv ▸ f.hasResWalkOfLen_resDist (v := v) (by omega)
  cases hwalk with
  | succ hprev hpos =>
    have := f.resDist_le_of_hasResWalkOfLen hprev
    have := f.resDist_le_add_one_of_pos_resCap hpos
    exact ⟨_, by omega, hpos⟩

theorem resDist_le_add_length_pathArcs (f : N.Flow) {q : List V} {u w : V}
    (hu : q.head? = some u) (hw : q.getLast? = some w)
    (hq : ∀ e ∈ pathArcs q, 0 < f.resCap e.1 e.2) :
    f.resDist w ≤ f.resDist u + (pathArcs q).length := by
  by_cases hlt : f.resDist u < Fintype.card V
  · exact f.resDist_le_of_hasResWalkOfLen
      (hasResWalkOfLen_add f q (f.hasResWalkOfLen_resDist hlt) hu hw hq)
  · have := f.resDist_le_card w; omega

/-- Every vertex on a positive-residual-capacity walk starting at `N.s` has `resDist` bounded by
the walk's arc length. -/
theorem resDist_mem_le_length_pathArcs (f : N.Flow) {p : List V}
    (hs : p.head? = some N.s) (harcs : ∀ e ∈ pathArcs p, 0 < f.resCap e.1 e.2)
    {x : V} (hx : x ∈ p) : f.resDist x ≤ (pathArcs p).length := by
  have hgen (q : List V) (u : V) (hu : q.head? = some u)
      (hq : ∀ e ∈ pathArcs q, 0 < f.resCap e.1 e.2) (hx : x ∈ q) :
      f.resDist x ≤ f.resDist u + (pathArcs q).length := by
    induction q generalizing u with
    | nil => simp at hx
    | cons a rest ih =>
      obtain rfl : a = u := by simpa using hu
      rcases List.mem_cons.mp hx with rfl | hmem'
      · exact Nat.le_add_right _ _
      · rcases rest with _ | ⟨b, rest'⟩
        · simp at hmem'
        · have hstep : f.resDist b ≤ f.resDist a + 1 :=
            f.resDist_le_add_one_of_pos_resCap (hq (a, b) List.mem_cons_self)
          have hrec := ih b rfl (fun e he => hq e (List.mem_cons_of_mem _ he)) hmem'
          simp only [pathArcs_cons_cons, List.length_cons]; omega
  simpa using hgen p N.s hs harcs hx

/-- A shortest augmenting path: a simple `s`-`t` augmenting path of minimum residual arc length
`f.resDist N.t`. -/
@[expose] def IsShortestAugmentingPath (f : N.Flow) (p : List V) : Prop :=
  f.IsAugmentingPath p ∧ (pathArcs p).length = f.resDist N.t

theorem IsShortestAugmentingPath.isAugmentingPath {f : N.Flow} {p : List V}
    (hp : f.IsShortestAugmentingPath p) : f.IsAugmentingPath p := hp.1

theorem IsShortestAugmentingPath.length_eq {f : N.Flow} {p : List V}
    (hp : f.IsShortestAugmentingPath p) : (pathArcs p).length = f.resDist N.t := hp.2

/-- Every consecutive arc `(u, v)` along a shortest augmenting path advances `f.resDist` by `1` and
satisfies `f.resDist v ≤ f.resDist N.t`. -/
theorem resDist_arc_of_isShortestAugmentingPath (f : N.Flow) {p : List V}
    (hp : f.IsShortestAugmentingPath p) {u v : V} (he : (u, v) ∈ pathArcs p) :
    f.resDist v = f.resDist u + 1 ∧ f.resDist v ≤ f.resDist N.t := by
  have hgen (q : List V) (x : V) (hx : q.head? = some x) (hqt : q.getLast? = some N.t)
      (hq : ∀ a ∈ pathArcs q, 0 < f.resCap a.1 a.2)
      (hdists : f.resDist N.t = f.resDist x + (pathArcs q).length)
      (hmem : (u, v) ∈ pathArcs q) :
      f.resDist v = f.resDist u + 1 ∧ f.resDist v ≤ f.resDist N.t := by
    induction q generalizing x with
    | nil => simp at hmem
    | cons a rest ih =>
      obtain rfl : a = x := by simpa using hx
      rcases rest with _ | ⟨b, rest'⟩
      · simp at hmem
      · have htail := fun e he => hq e (List.mem_cons_of_mem _ he)
        have hstep : f.resDist b ≤ f.resDist a + 1 :=
          f.resDist_le_add_one_of_pos_resCap (hq (a, b) List.mem_cons_self)
        have := f.resDist_le_add_length_pathArcs rfl (by simpa using hqt) htail
        simp only [pathArcs_cons_cons, List.length_cons] at hdists
        rcases List.mem_cons.mp (show (u, v) ∈ (a, b) :: pathArcs (b :: rest') from hmem)
          with hEq | hmem'
        · rcases Prod.mk.inj hEq with ⟨rfl, rfl⟩; exact ⟨by omega, by omega⟩
        · exact ih b rfl (by simpa using hqt) htail (by omega) hmem'
  have haug := hp.isAugmentingPath
  exact hgen p N.s haug.head? haug.getLast? (fun _ h => haug.pos_resCap h)
    (by simp [hp.length_eq]) he

/-- **Edmonds–Karp shortest-path distance monotonicity** ([EdmondsKarp1972], Section 1, p. 251;
[CLRS2009], Lemma 26.7, pp. 727–728): augmenting `f` along a shortest augmenting path `p` never
decreases `resDist v` for any vertex `v`. -/
private theorem resCap_augmentByBottleneck [DecidableEq V] (f : N.Flow) {p : List V}
    (hp : f.IsAugmentingPath p) (u w : V) :
    (f.augmentByBottleneck p hp).resCap u w =
      if (u, w) ∈ pathArcs p then f.resCap u w - f.bottleneck p
      else if (w, u) ∈ pathArcs p then f.resCap u w + f.bottleneck p
      else f.resCap u w :=
  f.resCap_augment hp.nodup hp.head? hp.getLast? (f.bottleneck p)
    (fun _ he => f.bottleneck_le_resCap he) u w

theorem resDist_le_augmentByBottleneck [DecidableEq V] (f : N.Flow) {p : List V}
    (hp : f.IsShortestAugmentingPath p) (v : V) :
    f.resDist v ≤ (f.augmentByBottleneck p hp.isAugmentingPath).resDist v := by
  let f' := f.augmentByBottleneck p hp.isAugmentingPath
  by_cases hlt : f'.resDist v < Fintype.card V
  · have hind (k : ℕ) : k < Fintype.card V → ∀ w : V, f'.resDist w = k → f.resDist w ≤ k := by
      induction k with
      | zero => intro _ w hw; rw [f'.eq_source_of_resDist_eq_zero hw]; simp
      | succ k ih =>
        intro hk1 w hw
        obtain ⟨u, hu_dist, hpos'⟩ := f'.exists_pred_of_resDist_eq_succ hk1 hw
        have := ih (by omega) u hu_dist
        by_cases hpos : 0 < f.resCap u w
        · have := f.resDist_le_add_one_of_pos_resCap hpos; omega
        · have hres' : f'.resCap u w = _ := f.resCap_augmentByBottleneck hp.isAugmentingPath u w
          have hwu : (w, u) ∈ pathArcs p := by
            by_contra h; split_ifs at hres' <;> omega
          have := (f.resDist_arc_of_isShortestAugmentingPath hp hwu).1; omega
    exact hind (f'.resDist v) hlt v rfl
  · exact (f.resDist_le_card v).trans (Nat.le_of_not_lt hlt)

end Flow

/-- A shortest-augmenting-path trace of length `T` on `N`: `flows 0, …, flows T` linked by shortest
augmenting paths `paths 0, …, paths (T - 1)`. -/
@[expose] def IsShortestAugmentingSeq [DecidableEq V] (T : ℕ) (flows : ℕ → N.Flow)
    (paths : ℕ → List V) : Prop :=
  ∀ t < T, ∃ hp : (flows t).IsShortestAugmentingPath (paths t),
    flows (t + 1) = (flows t).augmentByBottleneck (paths t) hp.isAugmentingPath

private theorem resDist_mono_of_seq [DecidableEq V] {T : ℕ} {flows : ℕ → N.Flow}
    {paths : ℕ → List V} (hseq : N.IsShortestAugmentingSeq T flows paths)
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ T) (v : V) :
    (flows i).resDist v ≤ (flows j).resDist v := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ k _ ih =>
    obtain ⟨hp, hnext⟩ := hseq k (by omega)
    exact (ih (by omega)).trans (hnext ▸ (flows k).resDist_le_augmentByBottleneck hp v)

private theorem exists_zero_to_pos_step {g : ℕ → ℕ} {a b : ℕ} (hab : a ≤ b)
    (ha : g a = 0) (hb : 0 < g b) :
    ∃ r, a ≤ r ∧ r < b ∧ g r < g (r + 1) := by
  induction b, hab using Nat.le_induction with
  | base => omega
  | succ k hle ih =>
    by_cases hpos : 0 < g k
    · obtain ⟨r, hr₁, hr₂, hlt⟩ := ih hpos; exact ⟨r, hr₁, by omega, hlt⟩
    · exact ⟨k, hle, Nat.lt_succ_self k, by omega⟩

/-- **Edmonds–Karp polynomial augmentation bound** ([EdmondsKarp1972], Section 1, Theorem 1,
p. 251; [CLRS2009], Theorem 26.8, p. 729): when `N.s ≠ N.t`, every sequence of shortest-path
augmentations has length at most `N.symArcs.card * (Fintype.card V / 2)`. -/
theorem shortestAugmentingSeq_length_le [DecidableEq V] (hst : N.s ≠ N.t) {T : ℕ}
    {flows : ℕ → N.Flow} {paths : ℕ → List V}
    (hseq : N.IsShortestAugmentingSeq T flows paths) :
    T ≤ N.symArcs.card * (Fintype.card V / 2) := by
  let isCrit (e : V × V) : Finset (Fin T) :=
    Finset.univ.filter fun t =>
      e ∈ pathArcs (paths t.1) ∧ (flows t.1).resCap e.1 e.2 = (flows t.1).bottleneck (paths t.1)
  have hcrit_card : ∀ e ∈ N.symArcs, (isCrit e).card ≤ Fintype.card V / 2 := by
    rintro ⟨u, v⟩ _
    have hmaps : ∀ t ∈ isCrit (u, v),
        (flows t.1).resDist u / 2 ∈ Finset.range (Fintype.card V / 2) := fun t ht => by
      obtain ⟨hp, _⟩ := hseq t.1 t.2
      have := (flows t.1).resDist_arc_of_isShortestAugmentingPath hp (Finset.mem_filter.mp ht).2.1
      have := ((flows t.1).resDist_lt_card_iff_resReachable N.t).mpr
        ((flows t.1).exists_augmentingPath_iff_resReachable.mp ⟨paths t.1, hp.isAugmentingPath⟩)
      rw [Finset.mem_range]; omega
    have hgap {t₁ t₂ : Fin T} (ht₁ : t₁ ∈ isCrit (u, v)) (ht₂ : t₂ ∈ isCrit (u, v))
        (hlt : t₁.1 < t₂.1) : (flows t₁.1).resDist u + 2 ≤ (flows t₂.1).resDist u := by
      obtain ⟨he₁, hbot₁⟩ := (Finset.mem_filter.mp ht₁).2
      obtain ⟨he₂, _⟩ := (Finset.mem_filter.mp ht₂).2
      obtain ⟨hp₁, hnext₁⟩ := hseq t₁.1 t₁.2
      obtain ⟨hp₂, _⟩ := hseq t₂.1 t₂.2
      have hzero₁ : (flows (t₁.1 + 1)).resCap u v = 0 := by
        rw [hnext₁, Flow.resCap_augmentByBottleneck]; simp [he₁, hbot₁]
      obtain ⟨r, hr₁, hr₂, hinc⟩ := exists_zero_to_pos_step (g := fun k => (flows k).resCap u v)
        (by omega) hzero₁ (hp₂.isAugmentingPath.pos_resCap he₂)
      obtain ⟨hpr, hnextr⟩ := hseq r (by omega)
      have hvu_r : (v, u) ∈ pathArcs (paths r) := by
        rw [hnextr, Flow.resCap_augmentByBottleneck] at hinc
        by_contra h; split_ifs at hinc <;> omega
      have := ((flows t₁.1).resDist_arc_of_isShortestAugmentingPath hp₁ he₁).1
      have := ((flows r).resDist_arc_of_isShortestAugmentingPath hpr hvu_r).1
      have := N.resDist_mono_of_seq hseq (i := t₁.1) (j := r) (by omega) (by omega) v
      have := N.resDist_mono_of_seq hseq (i := r) (j := t₂.1) (by omega) (by omega) u
      omega
    have hinj : Set.InjOn (fun t : Fin T => (flows t.1).resDist u / 2) (isCrit (u, v)) :=
      fun t₁ ht₁ t₂ ht₂ heq => by
        dsimp only at heq
        rcases lt_trichotomy t₁.1 t₂.1 with hlt | heq' | hgt
        · have := hgap ht₁ ht₂ hlt; omega
        · exact Fin.ext heq'
        · have := hgap ht₂ ht₁ hgt; omega
    exact (Finset.card_le_card_of_injOn _ hmaps hinj).trans_eq (Finset.card_range _)
  have hcover : (Finset.univ : Finset (Fin T)) ⊆ N.symArcs.biUnion isCrit := fun t _ => by
    obtain ⟨hp, _⟩ := hseq t.1 t.2
    have haug := hp.isAugmentingPath
    obtain ⟨e, he, hbot⟩ := (flows t.1).exists_mem_pathArcs_resCap_eq_bottleneck
      (pathArcs_ne_nil_of_head?_ne_getLast? hst haug.head? haug.getLast?)
    have := haug.pos_resCap he
    have := (flows t.1).resCap_le_cap_add_cap e.1 e.2
    exact Finset.mem_biUnion.mpr ⟨e,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, ne_of_mem_pathArcs haug.nodup he, by omega⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, he, hbot⟩⟩
  simpa [Fintype.card_fin] using (Finset.card_le_card hcover).trans
    (Finset.card_biUnion_le.trans (Finset.sum_le_sum hcrit_card))

/-- Sparse `|V| * |E|` corollary of `shortestAugmentingSeq_length_le` ([CLRS2009], Theorem 26.8,
p. 729): every shortest-path augmentation sequence has length at most
`Fintype.card V * N.posArcs.card`. -/
theorem shortestAugmentingSeq_length_le_card_mul_posArcs [DecidableEq V] (hst : N.s ≠ N.t)
    {T : ℕ} {flows : ℕ → N.Flow} {paths : ℕ → List V}
    (hseq : N.IsShortestAugmentingSeq T flows paths) :
    T ≤ Fintype.card V * N.posArcs.card :=
  (N.shortestAugmentingSeq_length_le hst hseq).trans (N.card_symArcs_mul_half_le (Fintype.card V))

end DistanceAndCriticalArcs

end Network


/-! ### Executable BFS and Edmonds–Karp solver over `Fin n` -/

section ExecutableFin

/-- Total `Fin n`-indexed lookup on `Vector α n`. -/
@[expose] def vget {α : Type*} {n : ℕ} (tbl : Vector α n) (v : Fin n) : α := tbl[v.1]

/-- Total `Fin n`-indexed update on `Vector α n`. -/
@[expose] def vset {α : Type*} {n : ℕ} (tbl : Vector α n) (v : Fin n) (x : α) : Vector α n :=
  tbl.set v.1 x v.2

@[simp]
theorem vget_replicate {α : Type*} {n : ℕ} (a : α) (v : Fin n) :
    vget (Vector.replicate n a) v = a := by
  simp [vget]

@[simp]
theorem vget_vset_self {α : Type*} {n : ℕ} (tbl : Vector α n) (v : Fin n) (x : α) :
    vget (vset tbl v x) v = x := by
  simp [vget, vset]

theorem vget_vset_ne {α : Type*} {n : ℕ} (tbl : Vector α n) {u v : Fin n} (x : α) (h : u ≠ v) :
    vget (vset tbl u x) v = vget tbl v := by
  have hne : u.1 ≠ v.1 := Fin.val_ne_of_ne h
  simp [vget, vset, hne]

/-- Lookup entry `(u, v)` in an `n × n` `Vector` matrix. -/
@[expose] def fget {α : Type*} {n : ℕ} (mat : Vector (Vector α n) n) (u v : Fin n) : α :=
  vget (vget mat u) v

/-- Update entry `(u, v)` in an `n × n` `Vector` matrix. -/
@[expose] def fset {α : Type*} {n : ℕ} (mat : Vector (Vector α n) n) (u v : Fin n) (x : α) :
    Vector (Vector α n) n :=
  vset mat u (vset (vget mat u) v x)

@[simp]
theorem fget_fset_self {α : Type*} {n : ℕ} (mat : Vector (Vector α n) n) (u v : Fin n) (x : α) :
    fget (fset mat u v x) u v = x := by
  simp [fget, fset]

theorem fget_fset_ne {α : Type*} {n : ℕ} (mat : Vector (Vector α n) n) {a b u v : Fin n} (x : α)
    (hne : (a, b) ≠ (u, v)) :
    fget (fset mat a b x) u v = fget mat u v := by
  by_cases hau : a = u
  · subst hau
    have hbv : b ≠ v := fun h => hne (congrArg (Prod.mk a) h)
    simp [fget, fset, vget_vset_ne _ _ hbv]
  · simp [fget, fset, vget_vset_ne _ _ hau]

/-- Candidate neighbor lists `adj` cover `N` when every non-loop pair `(u, v)` with positive
capacity in either direction appears in `adj u`. -/
@[expose] def AdjValid {n : ℕ} (N : Network (Fin n)) (adj : Fin n → List (Fin n)) : Prop :=
  ∀ u v, u ≠ v → 0 < N.cap u v + N.cap v u → v ∈ adj u

instance instDecidableAdjValid {n : ℕ} (N : Network (Fin n))
    (adj : Fin n → List (Fin n)) : Decidable (AdjValid N adj) := by
  unfold AdjValid
  infer_instance

/-- Total length of all candidate neighbor lists (`2 * |E|` on sparse symmetric adjacency lists,
`n^2` on `defaultAdj n`). -/
@[expose] def adjSteps {n : ℕ} (adj : Fin n → List (Fin n)) : ℕ :=
  ∑ u : Fin n, (adj u).length

/-- Dense candidate neighbor list enumerating `List.finRange n` at every vertex. -/
@[expose] def defaultAdj (n : ℕ) : Fin n → List (Fin n) :=
  fun _ => List.finRange n

theorem adjValid_defaultAdj {n : ℕ} (N : Network (Fin n)) : AdjValid N (defaultAdj n) :=
  fun _ v _ _ => List.mem_finRange v

@[simp]
theorem adjSteps_defaultAdj (n : ℕ) : adjSteps (defaultAdj n) = n * n := by
  simp [adjSteps, defaultAdj, Fintype.card_fin]

/-- Under `AdjValid N adj`, every active residual pair `(u, v) ∈ N.symArcs` appears in `adj u`, so
`N.symArcs.card ≤ adjSteps adj`. -/
theorem card_symArcs_le_adjSteps {n : ℕ} {N : Network (Fin n)} {adj : Fin n → List (Fin n)}
    (hadj : AdjValid N adj) : N.symArcs.card ≤ adjSteps adj := by
  have hsub : N.symArcs ⊆ Finset.univ.biUnion fun u : Fin n =>
      (adj u).toFinset.image (Prod.mk u) := fun ⟨u, v⟩ he => by
    simp only [Network.symArcs, Finset.mem_filter, Finset.mem_univ, true_and] at he
    exact Finset.mem_biUnion.mpr ⟨u, Finset.mem_univ _,
      Finset.mem_image.mpr ⟨v, List.mem_toFinset.mpr (hadj u v he.1 he.2), rfl⟩⟩
  exact (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans
    (Finset.sum_le_sum fun u _ => Finset.card_image_le.trans (List.toFinset_card_le _)))

/-! #### Reversed-walk validity and executable BFS -/

/-- `rp` reverses to a simple positive-residual-capacity walk from `N.s` to `v`. -/
structure IsRevWalkTo {n : ℕ} {N : Network (Fin n)} (f : N.Flow)
    (v : Fin n) (rp : List (Fin n)) : Prop where
  nodup : rp.reverse.Nodup
  head? : rp.reverse.head? = some N.s
  getLast? : rp.reverse.getLast? = some v
  pos_resCap : ∀ e ∈ pathArcs rp.reverse, 0 < f.resCap e.1 e.2

theorem IsRevWalkTo.isAugmentingPath {n : ℕ} {N : Network (Fin n)} {f : N.Flow} {rp : List (Fin n)}
    (h : IsRevWalkTo f N.t rp) : f.IsAugmentingPath rp.reverse :=
  ⟨h.nodup, h.head?, h.getLast?, h.pos_resCap⟩

/-- Table-level structural invariant for `revPath`: every `some rp` entry is a valid reversed walk
whose vertices are all already marked in `revPath`. -/
structure TblValid {n : ℕ} {N : Network (Fin n)} (f : N.Flow)
    (tbl : Vector (Option (List (Fin n))) n) : Prop where
  walk : ∀ v rp, vget tbl v = some rp → IsRevWalkTo f v rp
  mem_isSome : ∀ v rp, vget tbl v = some rp → ∀ x ∈ rp.reverse, (vget tbl x).isSome = true

/-- Intermediate state of one BFS layer over `Fin n`, carrying an erased `TblValid` proof. -/
structure BfsState {n : ℕ} {N : Network (Fin n)} (f : N.Flow) where
  /-- Reversed shortest path `v :: … :: [s]` for each discovered vertex `v`, or `none`. -/
  revPath : Vector (Option (List (Fin n))) n
  /-- Newly discovered vertices in the current layer. -/
  frontier : List (Fin n)
  /-- Erased proof that every `some rp` in `revPath` reverses to a simple valid walk. -/
  tblValid : TblValid f revPath

/-- Result of a single BFS shortest-augmenting-path search for flow `f`. -/
structure BfsResult {n : ℕ} {N : Network (Fin n)} (f : N.Flow) where
  /-- Shortest residual `s`-`t` augmenting path when `t` is reachable, or `none`. -/
  augPath : Option (List (Fin n))
  /-- Erased proof that any returned `some p` is a valid augmenting path for `f`. -/
  augPath_valid : ∀ p, augPath = some p → f.IsAugmentingPath p
  /-- Residual-reachability cut (`f.reachableCut` when `augPath = none`). -/
  cut : Finset (Fin n)

theorem tblValid_init {n : ℕ} {N : Network (Fin n)} (f : N.Flow) :
    TblValid f (vset (Vector.replicate n none) N.s (some [N.s])) := by
  have hget_eq {v : Fin n} {rp : List (Fin n)}
      (h : vget (vset (Vector.replicate n none) N.s (some [N.s])) v = some rp) :
      v = N.s ∧ rp = [N.s] := by
    rcases eq_or_ne v N.s with rfl | hne
    · simp_all
    · simp [vget_vset_ne _ _ hne.symm] at h
  refine ⟨fun v rp h => ?_, fun v rp h x hx => ?_⟩
  · obtain ⟨rfl, rfl⟩ := hget_eq h; exact ⟨List.nodup_singleton _, rfl, rfl, by simp⟩
  · obtain ⟨rfl, rfl⟩ := hget_eq h; simp_all

theorem tblValid_insert {n : ℕ} {N : Network (Fin n)} {f : N.Flow}
    {tbl : Vector (Option (List (Fin n))) n} (htbl : TblValid f tbl)
    {u v : Fin n} {rp_u : List (Fin n)}
    (hu_walk : IsRevWalkTo f u rp_u)
    (hu_mem : ∀ x ∈ rp_u.reverse, (vget tbl x).isSome = true)
    (hpos : 0 < f.resCap u v) (hnone : (vget tbl v).isNone = true) :
    TblValid f (vset tbl v (some (v :: rp_u))) ∧
      (∀ x ∈ rp_u.reverse, (vget (vset tbl v (some (v :: rp_u))) x).isSome = true) := by
  have hpu_ne : rp_u.reverse ≠ [] := by intro h; simpa [h] using hu_walk.head?
  have hv_walk : IsRevWalkTo f v (v :: rp_u) := by
    have hv_notin : v ∉ rp_u.reverse := fun hv => by
      have := hu_mem v hv; rw [Option.isNone_iff_eq_none.mp hnone] at this; simp at this
    refine ⟨?_, by simpa [List.reverse_cons, List.head?_append_of_ne_nil _ hpu_ne] using
        hu_walk.head?, by simp [List.reverse_cons], fun e he => ?_⟩
    · rw [List.reverse_cons, List.nodup_append]
      exact ⟨hu_walk.nodup, List.nodup_singleton v, fun a ha b hb hab => by
        subst hab; rw [List.mem_singleton.mp hb] at ha; exact hv_notin ha⟩
    · rw [List.reverse_cons, pathArcs_append_singleton hpu_ne hu_walk.getLast?,
        List.mem_append, List.mem_singleton] at he
      rcases he with h | rfl
      · exact hu_walk.pos_resCap e h
      · exact hpos
  have hisSome_mono (x : Fin n) (hx : (vget tbl x).isSome = true) :
      (vget (vset tbl v (some (v :: rp_u))) x).isSome = true := by
    rcases eq_or_ne v x with rfl | hvx
    · simp
    · simp [vget_vset_ne _ _ hvx, hx]
  refine ⟨⟨fun w rp hget => ?_, fun w rp hget x hx => ?_⟩, fun x hx => hisSome_mono x (hu_mem x hx)⟩
  · rcases eq_or_ne v w with rfl | hvw
    · obtain rfl : v :: rp_u = rp := by simpa using hget
      exact hv_walk
    · exact htbl.walk w rp (by simpa [vget_vset_ne _ _ hvw] using hget)
  · rcases eq_or_ne v w with rfl | hvw
    · obtain rfl : v :: rp_u = rp := by simpa using hget
      rcases List.mem_append.mp (List.reverse_cons ▸ hx) with hx_u | hx_v
      · exact hisSome_mono x (hu_mem x hx_u)
      · rw [List.mem_singleton.mp hx_v]; simp
    · exact hisSome_mono x
        (htbl.mem_isSome w rp (by simpa [vget_vset_ne _ _ hvw] using hget) x hx)

/-- Scan candidate neighbors `vs` of `u`, discovering newly reachable vertices in the residual
graph of `f`. -/
@[expose] def scanNeighbors {n : ℕ} {N : Network (Fin n)} (f : N.Flow)
    (u : Fin n) (rp_u : List (Fin n)) (hu_walk : IsRevWalkTo f u rp_u) :
    List (Fin n) → (st : BfsState f) →
    (∀ x ∈ rp_u.reverse, (vget st.revPath x).isSome = true) → BfsState f
  | [], st, _ => st
  | v :: vs, st, hu_mem =>
    if hcond : (0 < f.resCap u v && (vget st.revPath v).isNone) = true then
      let hpos : 0 < f.resCap u v := of_decide_eq_true (Bool.and_eq_true_iff.mp hcond).1
      let hnone : (vget st.revPath v).isNone = true := (Bool.and_eq_true_iff.mp hcond).2
      let hins := tblValid_insert st.tblValid hu_walk hu_mem hpos hnone
      let st' : BfsState f :=
        { revPath := vset st.revPath v (some (v :: rp_u))
          frontier := v :: st.frontier
          tblValid := hins.1 }
      scanNeighbors f u rp_u hu_walk vs st' hins.2
    else
      scanNeighbors f u rp_u hu_walk vs st hu_mem

/-- Expand all vertices in `layer`. -/
@[expose] def expandLayer {n : ℕ} {N : Network (Fin n)} (f : N.Flow)
    (adj : Fin n → List (Fin n)) :
    List (Fin n) → BfsState f → BfsState f
  | [], st => st
  | u :: us, st =>
    let st' :=
      match hget : vget st.revPath u with
      | none => st
      | some rp_u =>
        scanNeighbors f u rp_u (st.tblValid.walk u rp_u hget) (adj u) st
          (st.tblValid.mem_isSome u rp_u hget)
    expandLayer f adj us st'

/-- Run `k` BFS layer expansions from `(revPath, frontier)`. -/
@[expose] def bfsLoop {n : ℕ} {N : Network (Fin n)} (f : N.Flow)
    (adj : Fin n → List (Fin n)) :
    ℕ → BfsState f → BfsState f
  | 0, st => st
  | k + 1, st =>
    let st' := expandLayer f adj st.frontier
      { revPath := st.revPath, frontier := [], tblValid := st.tblValid }
    bfsLoop f adj k st'

/-- Pure breadth-first search for a shortest residual `s`-`t` augmenting path. -/
@[expose] def bfs {n : ℕ} (N : Network (Fin n)) (adj : Fin n → List (Fin n))
    (f : N.Flow) : BfsResult f :=
  let initSt : BfsState f :=
    { revPath := vset (Vector.replicate n none) N.s (some [N.s])
      frontier := [N.s]
      tblValid := tblValid_init f }
  let finalSt := bfsLoop f adj (n - 1) initSt
  match hget : vget finalSt.revPath N.t with
  | some rp_t =>
    { augPath := some rp_t.reverse
      augPath_valid := fun q hq => by
        injection hq with hq_eq
        subst hq_eq
        exact (finalSt.tblValid.walk N.t rp_t hget).isAugmentingPath
      cut := ∅ }
  | none =>
    { augPath := none
      augPath_valid := fun _ h => nomatch h
      cut := Finset.univ.filter fun v => (vget finalSt.revPath v).isSome = true }

private structure ValidRevPath {n : ℕ} {N : Network (Fin n)} (f : N.Flow) (v : Fin n)
    (rp : List (Fin n)) : Prop extends IsRevWalkTo f v rp where
  length_eq : (pathArcs rp.reverse).length = f.resDist v

private structure LayerInv {n : ℕ} {N : Network (Fin n)} (f : N.Flow) (d : ℕ)
    (st : BfsState f) : Prop where
  frontier_nodup : st.frontier.Nodup
  mem_frontier : ∀ v, v ∈ st.frontier ↔ f.resDist v < n ∧ f.resDist v = d
  isSome_iff : ∀ v, (vget st.revPath v).isSome ↔ f.resDist v < n ∧ f.resDist v ≤ d
  valid_revPath : ∀ v rp, vget st.revPath v = some rp → ValidRevPath f v rp

private structure StepInv {n : ℕ} {N : Network (Fin n)} (f : N.Flow) (d : ℕ)
    (baseTbl : Vector (Option (List (Fin n))) n) (st : BfsState f) : Prop where
  frontier_nodup : st.frontier.Nodup
  mono_base : ∀ w rp, vget baseTbl w = some rp → vget st.revPath w = some rp
  mem_frontier : ∀ w, w ∈ st.frontier ↔ (vget baseTbl w).isNone ∧ (vget st.revPath w).isSome
  valid_entry : ∀ w rp, vget st.revPath w = some rp →
    ValidRevPath f w rp ∧ f.resDist w < n ∧ f.resDist w ≤ d + 1

private theorem scanNeighbors_preserves {n : ℕ} {N : Network (Fin n)} {f : N.Flow} {d : ℕ}
    {baseTbl : Vector (Option (List (Fin n))) n}
    (hbase : ∀ v, (vget baseTbl v).isSome ↔ f.resDist v < n ∧ f.resDist v ≤ d)
    {u : Fin n} {rp_u : List (Fin n)} (hu_walk : IsRevWalkTo f u rp_u)
    (hu_valid : ValidRevPath f u rp_u) (hu_lt : f.resDist u < n) (hu_dist : f.resDist u = d)
    (vs : List (Fin n)) {st : BfsState f}
    (hu_mem : ∀ x ∈ rp_u.reverse, (vget st.revPath x).isSome = true)
    (hst : StepInv f d baseTbl st) :
    StepInv f d baseTbl (scanNeighbors f u rp_u hu_walk vs st hu_mem) ∧
      (∀ w rp, vget st.revPath w = some rp →
        vget (scanNeighbors f u rp_u hu_walk vs st hu_mem).revPath w = some rp) ∧
      (∀ v ∈ vs, 0 < f.resCap u v →
        (vget (scanNeighbors f u rp_u hu_walk vs st hu_mem).revPath v).isSome = true) := by
  induction vs generalizing st with
  | nil => exact ⟨hst, fun _ _ h => h, by simp⟩
  | cons v vs' ih =>
    simp only [scanNeighbors]
    by_cases hcond : (0 < f.resCap u v && (vget st.revPath v).isNone) = true
    · simp only [hcond, ↓reduceDIte]
      obtain ⟨hpos', hnone⟩ := Bool.and_eq_true_iff.mp hcond
      have hpos : 0 < f.resCap u v := of_decide_eq_true hpos'
      have hnone_st : vget st.revPath v = none := Option.isNone_iff_eq_none.mp hnone
      have hnone_base : vget baseTbl v = none := by
        cases hb : vget baseTbl v with
        | none => rfl
        | some rp => exact absurd (hst.mono_base v rp hb) (by simp [hnone_st])
      have hv_lt : f.resDist v < n := by
        have hu_r := (f.resDist_lt_card_iff_resReachable u).mp (by simpa [Fintype.card_fin])
        simpa [Fintype.card_fin] using (f.resDist_lt_card_iff_resReachable v).mpr (hu_r.tail hpos)
      have hv_not_le : ¬ f.resDist v ≤ d := fun h => by
        have := (hbase v).mpr ⟨hv_lt, h⟩; simp [hnone_base] at this
      have := f.resDist_le_add_one_of_pos_resCap hpos
      let hins := tblValid_insert st.tblValid hu_walk hu_mem hpos hnone
      let st' : BfsState f := ⟨vset st.revPath v (some (v :: rp_u)), v :: st.frontier, hins.1⟩
      have hpu_ne : rp_u.reverse ≠ [] := by intro h; simpa [h] using hu_valid.head?
      have hv_valid : ValidRevPath f v (v :: rp_u) := ⟨hins.1.walk v (v :: rp_u) (by simp), by
        rw [List.reverse_cons, pathArcs_append_singleton hpu_ne hu_valid.getLast?,
          List.length_append, List.length_singleton, hu_valid.length_eq]; omega⟩
      have hst' : StepInv f d baseTbl st' :=
        ⟨List.nodup_cons.mpr ⟨fun h => by
            have := (hst.mem_frontier v).mp h; simp [hnone_st] at this,
            hst.frontier_nodup⟩,
          fun w rp hbw => by
            have hvw : v ≠ w := by rintro rfl; simp [hnone_base] at hbw
            exact (vget_vset_ne _ _ hvw).trans (hst.mono_base w rp hbw),
          fun w => by
            rcases eq_or_ne w v with rfl | hwv
            · simp [st', hnone_base]
            · simp only [st', List.mem_cons, hwv, false_or, vget_vset_ne _ _ hwv.symm]
              exact hst.mem_frontier w,
          fun w rp hw => by
            rcases eq_or_ne w v with rfl | hwv
            · simp only [st', vget_vset_self, Option.some.injEq] at hw
              exact hw ▸ ⟨hv_valid, hv_lt, by omega⟩
            · exact hst.valid_entry w rp (by simpa [st', vget_vset_ne _ _ hwv.symm] using hw)⟩
      obtain ⟨hfin, hmono', hcov'⟩ := ih hins.2 hst'
      refine ⟨hfin, fun w rp hsw => hmono' w rp ?_, fun w hw hres_w => ?_⟩
      · have hvw : v ≠ w := by rintro rfl; simp [hnone_st] at hsw
        simpa [st', vget_vset_ne _ _ hvw] using hsw
      · rcases List.mem_cons.mp hw with hEq | hw'
        · rw [hEq, hmono' v (v :: rp_u) (by simp [st'])]; rfl
        · exact hcov' w hw' hres_w
    · simp only [hcond]
      obtain ⟨hfin, hmono', hcov'⟩ := ih hu_mem hst
      refine ⟨hfin, hmono', fun w hw hres_w => ?_⟩
      rcases List.mem_cons.mp hw with rfl | hw'
      · obtain ⟨rp_w, hrp_w⟩ : ∃ rp, vget st.revPath w = some rp := by
          cases h : vget st.revPath w with
          | none =>
            exact absurd (Bool.and_eq_true_iff.mpr ⟨decide_eq_true hres_w, by simp [h]⟩) hcond
          | some rp => exact ⟨rp, rfl⟩
        simp [hmono' w rp_w hrp_w]
      · exact hcov' w hw' hres_w

private theorem expandLayer_preserves {n : ℕ} {N : Network (Fin n)} {f : N.Flow}
    {adj : Fin n → List (Fin n)} {d : ℕ}
    {baseSt : BfsState f} (hinv : LayerInv f d baseSt)
    (us : List (Fin n)) (hus : ∀ u ∈ us, u ∈ baseSt.frontier)
    {st : BfsState f} (hst : StepInv f d baseSt.revPath st) :
    StepInv f d baseSt.revPath (expandLayer f adj us st) ∧
      (∀ w rp, vget st.revPath w = some rp →
        vget (expandLayer f adj us st).revPath w = some rp) ∧
      (∀ u ∈ us, ∀ v ∈ adj u, 0 < f.resCap u v →
        (vget (expandLayer f adj us st).revPath v).isSome = true) := by
  induction us generalizing st with
  | nil => exact ⟨hst, fun _ _ h => h, by simp⟩
  | cons u us' ih =>
    obtain ⟨hu_lt, hu_dist⟩ := (hinv.mem_frontier u).mp (hus u List.mem_cons_self)
    obtain ⟨rp_u, hrp_base⟩ := Option.isSome_iff_exists.mp
      ((hinv.isSome_iff u).mpr ⟨hu_lt, hu_dist.le⟩)
    have hrp_st := hst.mono_base u rp_u hrp_base
    simp only [expandLayer]
    split
    · simp_all
    · rename_i rp_u' hget
      obtain rfl : rp_u' = rp_u := Option.some.inj (hget.symm.trans hrp_st)
      obtain ⟨hst_mid, hmono_mid, hcov_u⟩ :=
        scanNeighbors_preserves hinv.isSome_iff (st.tblValid.walk u rp_u' hget)
          (hinv.valid_revPath u rp_u' hrp_base) hu_lt hu_dist (adj u)
          (st.tblValid.mem_isSome u rp_u' hget) hst
      obtain ⟨hst_end, hmono_end, hcov_us⟩ :=
        ih (fun x hx => hus x (List.mem_cons_of_mem u hx)) hst_mid
      refine ⟨hst_end, fun w rp hw => hmono_end w rp (hmono_mid w rp hw), fun x hx v hv hpos => ?_⟩
      rcases List.mem_cons.mp hx with rfl | hx'
      · obtain ⟨rp_v, hrpv⟩ := Option.isSome_iff_exists.mp (hcov_u v hv hpos)
        simp [hmono_end v rp_v hrpv]
      · exact hcov_us x hx' v hv hpos

private theorem layerInv_step {n : ℕ} {N : Network (Fin n)} {f : N.Flow}
    {adj : Fin n → List (Fin n)} (hadj : AdjValid N adj) {d : ℕ}
    {baseSt : BfsState f} (hinv : LayerInv f d baseSt) :
    let st := expandLayer f adj baseSt.frontier
      { revPath := baseSt.revPath, frontier := [], tblValid := baseSt.tblValid }
    LayerInv f (d + 1) st := by
  let st0 : BfsState f := ⟨baseSt.revPath, [], baseSt.tblValid⟩
  have hst0 : StepInv f d baseSt.revPath st0 :=
    ⟨List.nodup_nil, fun _ _ h => h, fun w => by cases vget baseSt.revPath w <;> simp [st0],
      fun w rp hw =>
        let ⟨hlt, _⟩ := (hinv.isSome_iff w).mp (by simp [st0] at hw; simp [hw])
        ⟨hinv.valid_revPath w rp hw, hlt, by omega⟩⟩
  obtain ⟨hst, -, hcov⟩ := expandLayer_preserves hinv baseSt.frontier (fun _ h => h) hst0
  have hsome_iff (v : Fin n) :
      (vget (expandLayer f adj baseSt.frontier st0).revPath v).isSome ↔
        f.resDist v < n ∧ f.resDist v ≤ d + 1 := by
    refine ⟨fun hs => let ⟨rp, hrp⟩ := Option.isSome_iff_exists.mp hs
        let ⟨_, hlt, hle⟩ := hst.valid_entry v rp hrp; ⟨hlt, hle⟩,
      fun ⟨hlt, hle⟩ => ?_⟩
    by_cases hle_d : f.resDist v ≤ d
    · obtain ⟨rp, hrp⟩ := Option.isSome_iff_exists.mp ((hinv.isSome_iff v).mpr ⟨hlt, hle_d⟩)
      simp [hst.mono_base v rp hrp]
    · obtain ⟨u, hu_dist, hpos⟩ := f.exists_pred_of_resDist_eq_succ
        (by rw [Fintype.card_fin]; omega) (by omega : f.resDist v = d + 1)
      have := f.resCap_le_cap_add_cap u v
      exact hcov u ((hinv.mem_frontier u).mpr ⟨by omega, hu_dist⟩) v
        (hadj u v (by rintro rfl; omega) (by omega)) hpos
  refine ⟨hst.frontier_nodup, fun v => ?_, hsome_iff, fun v rp hrp => (hst.valid_entry v rp hrp).1⟩
  rw [hst.mem_frontier v, hsome_iff v]
  have : (vget baseSt.revPath v).isNone = true ↔ ¬ (f.resDist v < n ∧ f.resDist v ≤ d) := by
    rw [← hinv.isSome_iff v]; cases vget baseSt.revPath v <;> simp
  rw [this]; omega

private theorem layerInv_init {n : ℕ} {N : Network (Fin n)} (f : N.Flow) :
    LayerInv f 0
      { revPath := vset (Vector.replicate n none) N.s (some [N.s])
        frontier := [N.s]
        tblValid := tblValid_init f } := by
  have hn : 0 < n := Nat.zero_lt_of_lt N.s.isLt
  refine ⟨List.nodup_singleton N.s,
    fun v => ⟨by rintro h; rw [List.mem_singleton.mp h]; exact ⟨by simp [hn], f.resDist_source⟩,
      fun ⟨_, h0⟩ => List.mem_singleton.mpr (f.eq_source_of_resDist_eq_zero h0)⟩,
    fun v => ?_, fun v rp hget => ?_⟩
  · rcases eq_or_ne v N.s with rfl | hne
    · simp [hn]
    · simpa [vget_vset_ne _ _ hne.symm] using
        fun _ h => hne (f.eq_source_of_resDist_eq_zero (Nat.eq_zero_of_le_zero h))
  · rcases eq_or_ne v N.s with rfl | hne
    · obtain rfl : [N.s] = rp := by simpa using hget
      exact ⟨⟨List.nodup_singleton _, rfl, rfl, by simp⟩, by simp⟩
    · simp [vget_vset_ne _ _ hne.symm] at hget

private theorem bfsLoop_spec {n : ℕ} {N : Network (Fin n)} {f : N.Flow}
    {adj : Fin n → List (Fin n)} (hadj : AdjValid N adj) :
    ∀ (k d : ℕ) (st : BfsState f),
      LayerInv f d st →
      LayerInv f (d + k) (bfsLoop f adj k st)
  | 0, _, st, hinv => by simpa [bfsLoop] using hinv
  | k + 1, d, st, hinv => by
    simp only [bfsLoop]
    simpa [Nat.add_right_comm, Nat.add_assoc] using
      bfsLoop_spec hadj k (d + 1) _ (layerInv_step hadj hinv)

/-- Specification of `bfs`: when `augPath = some p`, `p` is a shortest residual `s`-`t`
augmenting path of length at most `n`; when `augPath = none`, `f` has no augmenting path and
`cut = f.reachableCut`. -/
theorem bfs_spec {n : ℕ} {N : Network (Fin n)} {adj : Fin n → List (Fin n)}
    (hadj : AdjValid N adj) (f : N.Flow) :
    (∀ p, (bfs N adj f).augPath = some p →
      f.IsShortestAugmentingPath p ∧ p.length ≤ n) ∧
    ((bfs N adj f).augPath = none →
      (¬ ∃ p, f.IsAugmentingPath p) ∧ (bfs N adj f).cut = f.reachableCut) := by
  let initSt : BfsState f :=
    { revPath := vset (Vector.replicate n none) N.s (some [N.s])
      frontier := [N.s]
      tblValid := tblValid_init f }
  have hinv : LayerInv f (n - 1) (bfsLoop f adj (n - 1) initSt) := by
    simpa using bfsLoop_spec hadj (n - 1) 0 initSt (layerInv_init f)
  dsimp only [initSt] at hinv
  unfold bfs
  dsimp only
  split
  · rename_i rp_t hget
    simp only [Option.some.injEq, reduceCtorEq, false_implies, and_true]
    rintro p rfl
    have hv := hinv.valid_revPath N.t rp_t hget
    exact ⟨⟨hv.toIsRevWalkTo.isAugmentingPath, hv.length_eq⟩,
      by simpa [Fintype.card_fin] using hv.nodup.length_le_card⟩
  · rename_i hget
    simp only [reduceCtorEq, false_implies, implies_true, true_and]
    refine fun _ => ⟨fun hex => ?_, ?_⟩
    · have hlt : f.resDist N.t < n := by
        simpa [Fintype.card_fin] using (f.resDist_lt_card_iff_resReachable N.t).mpr
          (f.exists_augmentingPath_iff_resReachable.mp hex)
      have hs := (hinv.isSome_iff N.t).mpr ⟨hlt, by omega⟩
      rw [hget] at hs; simp at hs
    · ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, f.mem_reachableCut_iff,
        ← f.resDist_lt_card_iff_resReachable, Fintype.card_fin, hinv.isSome_iff v]
      omega

/-! #### Explicit `n × n` `FlowMatrix` and arc-by-arc bottleneck augmentation -/

/-- Concrete `n × n` `Vector` matrix storing arc flows, paired with erased feasibility proofs so
`toFlow` performs `O(1)` matrix lookups with zero stacked closures. -/
structure FlowMatrix {n : ℕ} (N : Network (Fin n)) where
  /-- Concrete `n × n` matrix of arc flows. -/
  mat : Vector (Vector ℕ n) n
  /-- Capacity bound on every entry (erased `Prop`). -/
  le_cap : ∀ u v, fget mat u v ≤ N.cap u v
  /-- Flow conservation at intermediate vertices (erased `Prop`). -/
  conserve : ∀ v, v ≠ N.s → v ≠ N.t → ∑ u, fget mat u v = ∑ w, fget mat v w

/-- View a `FlowMatrix N` as an `N.Flow` whose `toFun` is `O(1)` `fget` lookup. -/
@[expose] def FlowMatrix.toFlow {n : ℕ} {N : Network (Fin n)} (M : FlowMatrix N) : N.Flow where
  toFun u v := fget M.mat u v
  le_cap := M.le_cap
  conserve := M.conserve

@[simp]
theorem FlowMatrix.toFlow_apply {n : ℕ} {N : Network (Fin n)} (M : FlowMatrix N) (u v : Fin n) :
    M.toFlow u v = fget M.mat u v := rfl

/-- The all-zero `FlowMatrix N`. -/
@[expose] def initFlowMatrix {n : ℕ} (N : Network (Fin n)) : FlowMatrix N where
  mat := Vector.replicate n (Vector.replicate n 0)
  le_cap u v := by simp [fget]
  conserve v _ _ := by simp [fget]

@[simp]
theorem initFlowMatrix_toFlow {n : ℕ} (N : Network (Fin n)) :
    (initFlowMatrix N).toFlow = Network.Flow.zero N := by
  ext u v
  simp [initFlowMatrix, fget]

/-- Push `δ` units along directed arcs `es` in `mat`. -/
@[expose] def updateArcsMat {n : ℕ} (δ : ℕ) :
    List (Fin n × Fin n) → Vector (Vector ℕ n) n → Vector (Vector ℕ n) n
  | [], mat => mat
  | (a, b) :: es, mat =>
    let cancel := min δ (fget mat b a)
    let mat₁ := fset mat b a (fget mat b a - cancel)
    let mat₂ := fset mat₁ a b (fget mat a b + (δ - cancel))
    updateArcsMat δ es mat₂

private theorem fget_updateArcsMat {n : ℕ} (δ : ℕ) {es : List (Fin n × Fin n)}
    (hnodup : es.Nodup) (hloopless : ∀ e ∈ es, e.1 ≠ e.2)
    (hnoswap : ∀ u v, (u, v) ∈ es → (v, u) ∉ es)
    (mat : Vector (Vector ℕ n) n) (u v : Fin n) :
    fget (updateArcsMat δ es mat) u v =
      if (u, v) ∈ es then fget mat u v + (δ - min δ (fget mat v u))
      else if (v, u) ∈ es then fget mat u v - min δ (fget mat u v)
      else fget mat u v := by
  induction es generalizing mat with
  | nil => simp [updateArcsMat]
  | cons e es' ih =>
    rcases e with ⟨a, b⟩
    obtain ⟨hab_not, hnodup'⟩ := List.nodup_cons.mp hnodup
    have hba_not : (b, a) ∉ es' :=
      fun h => hnoswap a b List.mem_cons_self (List.mem_cons_of_mem _ h)
    let cancel := min δ (fget mat b a)
    let mat₁ := fset mat b a (fget mat b a - cancel)
    let mat₂ := fset mat₁ a b (fget mat a b + (δ - cancel))
    have hstep (x y : Fin n) : fget mat₂ x y =
        if (x, y) = (a, b) then fget mat x y + (δ - min δ (fget mat y x))
        else if (y, x) = (a, b) then fget mat x y - min δ (fget mat x y)
        else fget mat x y := by
      rcases eq_or_ne (x, y) (a, b) with hxy | hxy
      · rcases Prod.mk.inj hxy with ⟨rfl, rfl⟩; simp [mat₂, cancel]
      · rcases eq_or_ne (y, x) (a, b) with hyx | hyx
        · rcases Prod.mk.inj hyx with ⟨rfl, rfl⟩
          simp [hxy, mat₂, mat₁, cancel, fget_fset_ne _ _ hxy.symm]
        · have hba : (b, a) ≠ (x, y) := fun h => by
            rcases Prod.mk.inj h with ⟨rfl, rfl⟩; exact hyx rfl
          simp [hxy, hyx, mat₂, mat₁, fget_fset_ne _ _ hxy.symm, fget_fset_ne _ _ hba]
    simp only [updateArcsMat]
    rw [ih hnodup' (fun _ h => hloopless _ (List.mem_cons_of_mem _ h))
      (fun x y h₁ h₂ => hnoswap x y (List.mem_cons_of_mem _ h₁) (List.mem_cons_of_mem _ h₂)) mat₂]
    by_cases huv : (u, v) ∈ es'
    · have h₁ : (u, v) ≠ (a, b) := fun h => hab_not (h ▸ huv)
      have h₂ : (v, u) ≠ (a, b) := fun h =>
        hba_not (by rcases Prod.mk.inj h with ⟨rfl, rfl⟩; exact huv)
      simp only [huv, List.mem_cons_of_mem _ huv, ↓reduceIte, hstep, h₁, h₂]
    · by_cases hvu : (v, u) ∈ es'
      · have h₁ : (v, u) ≠ (a, b) := fun h => hab_not (h ▸ hvu)
        have h₂ : (u, v) ≠ (a, b) := fun h =>
          hba_not (by rcases Prod.mk.inj h with ⟨rfl, rfl⟩; exact hvu)
        simp only [huv, hvu, List.mem_cons, h₂, false_or, List.mem_cons_of_mem _ hvu,
          ↓reduceIte, hstep, h₁]
      · simp only [huv, hvu, ↓reduceIte, hstep, List.mem_cons, or_false]

/-- Augment `M` along the augmenting path `p` by its bottleneck `M.toFlow.bottleneck p`. -/
@[expose] def augmentFlowMatrix {n : ℕ} {N : Network (Fin n)} (M : FlowMatrix N)
    (p : List (Fin n)) (hp : M.toFlow.IsAugmentingPath p) : FlowMatrix N :=
  let δ := M.toFlow.bottleneck p
  let mat' := updateArcsMat δ (pathArcs p) M.mat
  have hfun : ∀ u v, fget mat' u v = (M.toFlow.augmentByBottleneck p hp) u v := fun u v => by
    rw [fget_updateArcsMat δ (nodup_pathArcs hp.nodup)
      (fun e he => ne_of_mem_pathArcs hp.nodup he)
      (fun a b hab => not_swap_mem_pathArcs hp.nodup hab)]
    rfl
  { mat := mat'
    le_cap := fun u v => by
      rw [hfun u v]
      exact (M.toFlow.augmentByBottleneck p hp).le_cap u v
    conserve := fun v hvs hvt => by
      simp only [hfun]
      exact (M.toFlow.augmentByBottleneck p hp).conserve v hvs hvt }

@[simp]
theorem augmentFlowMatrix_toFlow {n : ℕ} {N : Network (Fin n)} (M : FlowMatrix N)
    (p : List (Fin n)) (hp : M.toFlow.IsAugmentingPath p) :
    (augmentFlowMatrix M p hp).toFlow = M.toFlow.augmentByBottleneck p hp := by
  ext u v
  simp only [augmentFlowMatrix, FlowMatrix.toFlow_apply]
  exact fget_updateArcsMat (M.toFlow.bottleneck p) (nodup_pathArcs hp.nodup)
    (fun e he => ne_of_mem_pathArcs hp.nodup he)
    (fun a b hab => not_swap_mem_pathArcs hp.nodup hab) M.mat u v

/-- Output of the Edmonds–Karp algorithm on `N : Network (Fin n)`. -/
structure Output {n : ℕ} (N : Network (Fin n)) where
  /-- Final integral flow on `N`. -/
  flow : N.Flow
  /-- Residual-reachability cut certifying optimality (`flow.reachableCut`). -/
  cut : Finset (Fin n)
  /-- Number of shortest-path augmentations performed. -/
  augmentations : ℕ

/-- Mathematical upper bound on the number of shortest-path augmentations performed by Edmonds–Karp
on `N` ([CLRS2009], Theorem 26.8, p. 729). -/
def maxAugmentations {n : ℕ} (N : Network (Fin n)) : ℕ :=
  N.symArcs.card * (n / 2)

/-- Bounded-fuel Edmonds–Karp loop over `FlowMatrix N`: runs `bfs` and augments along shortest
paths while `fuel` remains, finishing with one certifying `bfs` search when `fuel = 0` or
`augPath = none`. -/
@[expose] def edmondsKarpLoop {n : ℕ} (N : Network (Fin n)) (adj : Fin n → List (Fin n)) :
    ℕ → FlowMatrix N → ℕ → Output N
  | 0, M, k =>
    let res := bfs N adj M.toFlow
    { flow := M.toFlow, cut := res.cut, augmentations := k }
  | fuel + 1, M, k =>
    let res := bfs N adj M.toFlow
    match haug : res.augPath with
    | none => { flow := M.toFlow, cut := res.cut, augmentations := k }
    | some p =>
      let M' := augmentFlowMatrix M p (res.augPath_valid p haug)
      edmondsKarpLoop N adj fuel M' (k + 1)

/-- Execute the **Edmonds–Karp shortest-augmenting-path algorithm** on `N : Network (Fin n)` using
candidate neighbor lists `adj`. -/
@[expose] def edmondsKarp {n : ℕ} (N : Network (Fin n))
    (adj : Fin n → List (Fin n)) : Output N :=
  let M₀ := initFlowMatrix N
  if N.s = N.t then
    { flow := M₀.toFlow, cut := ∅, augmentations := 0 }
  else
    edmondsKarpLoop N adj (adjSteps adj * (n / 2)) M₀ 0

/-- Dense specialization of `edmondsKarp` using `defaultAdj n` (`List.finRange n` at every
vertex), requiring no external adjacency structure. -/
@[expose] def edmondsKarpDense {n : ℕ} (N : Network (Fin n)) : Output N :=
  edmondsKarp N (defaultAdj n)

private theorem isShortestAugmentingSeq_snoc {V : Type*} [Fintype V] [DecidableEq V] {N : Network V}
    {k : ℕ} {flows : ℕ → N.Flow} {paths : ℕ → List V}
    (hseq : N.IsShortestAugmentingSeq k flows paths)
    {p : List V} (hp : (flows k).IsShortestAugmentingPath p) :
    N.IsShortestAugmentingSeq (k + 1)
      (fun t => if t ≤ k then flows t else (flows k).augmentByBottleneck p hp.isAugmentingPath)
      (fun t => if t < k then paths t else p) := fun t ht => by
  by_cases hlt : t < k
  · simpa [hlt, hlt.le, show t + 1 ≤ k from hlt] using hseq t hlt
  · obtain rfl : t = k := by omega
    simp only [le_rfl, lt_self_iff_false, show ¬ t + 1 ≤ t by omega, ↓reduceIte]
    exact ⟨hp, trivial⟩

private theorem edmondsKarpLoop_stop {n : ℕ} {N : Network (Fin n)}
    {adj : Fin n → List (Fin n)} (hadj : AdjValid N adj) (hst : N.s ≠ N.t)
    {k : ℕ} {M : FlowMatrix N} {flows : ℕ → N.Flow} {paths : ℕ → List (Fin n)}
    (hseq : N.IsShortestAugmentingSeq k flows paths)
    (hnone : (bfs N adj M.toFlow).augPath = none) :
    (¬ ∃ p, M.toFlow.IsAugmentingPath p) ∧
      (bfs N adj M.toFlow).cut = M.toFlow.reachableCut ∧
      k ≤ maxAugmentations N ∧
      k ≤ n * N.posArcs.card := by
  obtain ⟨hno, hcut⟩ := (bfs_spec hadj M.toFlow).2 hnone
  exact ⟨hno, hcut,
    by simpa [maxAugmentations, Fintype.card_fin] using N.shortestAugmentingSeq_length_le hst hseq,
    by simpa [Fintype.card_fin] using N.shortestAugmentingSeq_length_le_card_mul_posArcs hst hseq⟩

private theorem edmondsKarpLoop_spec {n : ℕ} {N : Network (Fin n)}
    {adj : Fin n → List (Fin n)} (hadj : AdjValid N adj) (hst : N.s ≠ N.t) :
    ∀ (fuel k : ℕ) (M : FlowMatrix N) (flows : ℕ → N.Flow) (paths : ℕ → List (Fin n)),
      maxAugmentations N ≤ fuel + k →
      N.IsShortestAugmentingSeq k flows paths →
      flows k = M.toFlow →
      let call := edmondsKarpLoop N adj fuel M k
      (¬ ∃ p, call.flow.IsAugmentingPath p) ∧
        call.cut = call.flow.reachableCut ∧
        call.augmentations ≤ maxAugmentations N ∧
        call.augmentations ≤ n * N.posArcs.card
  | 0, k, M, flows, paths, hfuel, hseq, hfk => by
    simp only [edmondsKarpLoop]
    rcases haug : (bfs N adj M.toFlow).augPath with _ | p
    · exact edmondsKarpLoop_stop hadj hst hseq haug
    · have hlen' : k + 1 ≤ maxAugmentations N := by
        simpa [maxAugmentations, Fintype.card_fin] using N.shortestAugmentingSeq_length_le hst
          (isShortestAugmentingSeq_snoc hseq (hfk ▸ ((bfs_spec hadj M.toFlow).1 p haug).1))
      omega
  | fuel + 1, k, M, flows, paths, hfuel, hseq, hfk => by
    simp only [edmondsKarpLoop]
    split
    · rename_i haug
      exact edmondsKarpLoop_stop hadj hst hseq haug
    · rename_i p haug
      obtain ⟨hshort, _⟩ := (bfs_spec hadj M.toFlow).1 p haug
      have hp := (bfs N adj M.toFlow).augPath_valid p haug
      have hseq' := isShortestAugmentingSeq_snoc hseq (hfk ▸ hshort)
      have hfk' :
          (if k + 1 ≤ k then flows (k + 1)
           else (flows k).augmentByBottleneck p (hfk ▸ hshort).isAugmentingPath) =
            (augmentFlowMatrix M p hp).toFlow := by
        simp only [show ¬ k + 1 ≤ k by omega, ↓reduceIte, augmentFlowMatrix_toFlow]
        ext u v
        change (flows k).augmentFun p ((flows k).bottleneck p) u v =
          M.toFlow.augmentFun p (M.toFlow.bottleneck p) u v
        rw [hfk]
      exact edmondsKarpLoop_spec hadj hst fuel (k + 1) _ _ _ (by omega) hseq' hfk'

/-- **Edmonds–Karp correctness theorem** ([EdmondsKarp1972], Theorem 1, p. 251; [CLRS2009],
Theorems 26.6 & 26.8, pp. 723, 729): on any integral network `N : Network (Fin n)` with `N.s ≠ N.t`
and valid candidate neighbor lists `adj`, `edmondsKarp N adj` returns an integral maximum flow
`out.flow` and minimum `s`-`t` cut `out.cut = out.flow.reachableCut` with
`out.flow.value = N.cutCapacity out.cut` in at most `N.symArcs.card * (n / 2)` (and at most
`n * N.posArcs.card`) augmentations. -/
theorem edmondsKarp_correct {n : ℕ} {N : Network (Fin n)} {adj : Fin n → List (Fin n)}
    (hadj : AdjValid N adj) (hst : N.s ≠ N.t) :
    let out := edmondsKarp N adj
    out.flow.IsMaxFlow ∧
      N.IsMinCut out.cut ∧
      out.flow.value = (N.cutCapacity out.cut : ℤ) ∧
      out.cut = out.flow.reachableCut ∧
      out.augmentations ≤ N.symArcs.card * (n / 2) ∧
      out.augmentations ≤ n * N.posArcs.card := by
  simp only [edmondsKarp, hst, ↓reduceIte]
  obtain ⟨hno, hcut_eq, haug_sym, haug_pos⟩ :=
    edmondsKarpLoop_spec hadj hst (adjSteps adj * (n / 2)) 0 (initFlowMatrix N)
      (fun _ => Network.Flow.zero N) (fun _ => [])
      (by
        simp only [maxAugmentations, Nat.add_zero]
        exact Nat.mul_le_mul_right _ (card_symArcs_le_adjSteps hadj))
      (fun _ ht => absurd ht (Nat.not_lt_zero _)) (initFlowMatrix_toFlow N).symm
  have hval := Network.Flow.value_eq_cutCapacity_reachableCut _ hno
  have hmin := Network.Flow.isMinCut_of_value_eq_cutCapacity _
    (Network.Flow.reachableCut_isCut _ hno) hval
  exact ⟨(Network.Flow.isMaxFlow_iff_not_exists_augmentingPath _ hst).mpr hno,
    hcut_eq ▸ hmin, hcut_eq ▸ hval, hcut_eq, haug_sym, haug_pos⟩

/-- Correctness of `edmondsKarpDense` without external adjacency obligations. -/
theorem edmondsKarpDense_correct {n : ℕ} {N : Network (Fin n)} (hst : N.s ≠ N.t) :
    let out := edmondsKarpDense N
    out.flow.IsMaxFlow ∧
      N.IsMinCut out.cut ∧
      out.flow.value = (N.cutCapacity out.cut : ℤ) ∧
      out.cut = out.flow.reachableCut ∧
      out.augmentations ≤ N.symArcs.card * (n / 2) ∧
      out.augmentations ≤ n * N.posArcs.card :=
  edmondsKarp_correct (adjValid_defaultAdj N) hst

end ExecutableFin

end Cslib.Algorithms.Lean.MaxFlow
