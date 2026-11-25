/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.Locality.Hanf
public import CslibFrontier.Logics.FirstOrder.Locality.Reachability
import CslibFrontier.Tactic.FirstOrder.Simp
import Mathlib.Basic.Finite.Sum
import Mathlib.Tactic.FinCases

/-!
# Exact Hanf and Gaifman locality ranks of first-order logic

`CslibFrontier.Logics.FirstOrder.Locality.Hanf` proves Hanf and Gaifman locality with the radii
`(3 ^ n - 1) / 2` and `(3 ^ (n + 1) - 1) / 2` of [Libkin, Theorem 4.12 and
Corollary 4.13][Libkin2004]. This module improves both bounds to their exact values on finite
structures, solving [Libkin, Exercises 4.10 and 4.11 (pp. 63–64)][Libkin2004]:

* **Sharp Gaifman locality (`2 ^ n - 1`).** In a finite structure `M`, tuples `a₁, a₂` with
  isomorphic radius-`(2 ^ n - 1)` neighborhoods are `n`-round Ehrenfeucht–Fraïssé-equivalent
  (`NbhdIso.duplicatorWins_of_two_pow`; `NbhdIso.duplicatorWins_of_equiv_two_pow` is the
  two-structure form) and, when `L.IsRelational`, satisfy the same formulas of quantifier rank at
  most `n` (`NbhdIso.realize_iff_of_two_pow`, `NbhdIso.formula_realize_iff_of_two_pow`).
* **Sharp Hanf locality (`2 ^ (n - 1) - 1`).** Over finite nonempty structures, Hanf-equivalence at
  radius `2 ^ (n - 1) - 1` implies `n`-round Ehrenfeucht–Fraïssé-equivalence
  (`HanfEquiv.duplicatorWins_of_two_pow`), and therefore agreement on relational formulas and
  sentences of quantifier rank at most `n` (`HanfEquiv.realize_iff_of_two_pow`,
  `HanfEquiv.formula_realize_iff_of_two_pow`, `realize_sentence_iff_of_nbhdIso_two_pow`). Notice
  that in `ℕ`, `2 ^ (0 - 1) - 1 = 0` and `2 ^ (1 - 1) - 1 = 0`, so radius `0` suffices for both
  `n = 0` and `n = 1`.
* **Matching lower bounds over `FirstOrder.Language.graph`.**
  - For every `n ≥ 1` and `r < 2 ^ n - 1`, two vertices of a finite `Language.graph`-structure
    have isomorphic radius-`r` neighborhoods yet disagree on the quantifier-rank-`n` formula
    `loopReach n` (`exists_nbhdIso_realize_loopReach`), so any Gaifman locality radius `ρ n` valid
    on finite `Language.graph`-structures satisfies `2 ^ n - 1 ≤ ρ n` for all `n`
    (`two_pow_sub_one_le_of_gaifman_radius`).
  - For every `n ≥ 2` and `d < 2 ^ (n - 1) - 1`, two finite nonempty `Language.graph`-structures
    are Hanf-equivalent at radius `d` yet disagree on a `Language.graph.Sentence` of quantifier
    rank `n` (`exists_hanfEquiv_sentence_not_realize_iff`), and likewise for `1`-tuples and
    `Language.graph.Formula (Fin 1)` (`exists_hanfEquiv_formula_not_realize_iff`). Consequently any
    Hanf locality radius `ρ n` valid on finite nonempty `Language.graph`-structures satisfies
    `2 ^ (n - 1) - 1 ≤ ρ n` for all `n` (`two_pow_pred_sub_one_le_of_hanf_sentence_radius`,
    `two_pow_pred_sub_one_le_of_hanf_radius`).

**Proof ideas.** The upper bounds maintain a shrinking clustered neighborhood-isomorphism invariant
`ClusterWitness`: with `m` rounds remaining, the pebbled indices are partitioned into clusters that
are pairwise more than `2 ^ m` apart on both sides and carry radius-`(2 ^ m - 1)` neighborhood
isomorphisms. When Spoiler plays within `T = 2 ^ m'` of a cluster at `m = m' + 1`, that cluster is
unique because distinct clusters are more than `2 T` apart, and restricting its radius-`(2 T - 1)`
isomorphism extends the cluster at radius `T - 1` while keeping distance more than `T` from all
other clusters. When Spoiler plays outside every radius-`T` cluster ball, those balls are pairwise
disjoint and `exists_compl_equiv_nbhdIso` matches the move outside the balls on the other side with
the same radius-`(T - 1)` singleton neighborhood type, forming a new cluster.

For the lower bounds, `relStructure` interprets `Language.graph` as directed graphs with self-loops,
whose Gaifman graph ignores edge orientation and self-loops (`gaifmanGraph_relStructure`). Adding a
self-loop at the far end of one component of `P_{2^n} ⊕ P_{2^n}` gives the `2 ^ n - 1` Gaifman
bound via `loopReach n`. Placing two self-loops on one directed path of `P_{2^n - 1} ⊕ P_{2^n - 1}`
versus one self-loop on each component gives the `2 ^ (n - 1) - 1` Hanf bound: swapping components
on the `d`-ball around the right endpoint matches all `d`-neighborhoods whenever `2 d < 2 ^ n - 2`,
while a rank-`n` sentence detects two distinct self-loops at directed distance at most `2 ^ n - 2`
by meeting at their midpoint.

## Main definitions

* `Cslib.Logic.FO.Locality.loopReach`: the formula stating that a self-loop lies within distance
  `2 ^ n - 1` along `distLE`, of quantifier rank `n`
  (`Cslib.Logic.FO.Locality.quantifierRank_loopReach`).

## Main results

* `Cslib.Logic.FO.Locality.NbhdIso.duplicatorWins_of_equiv_two_pow`,
  `Cslib.Logic.FO.Locality.NbhdIso.duplicatorWins_of_two_pow`,
  `Cslib.Logic.FO.Locality.NbhdIso.realize_iff_of_two_pow`,
  `Cslib.Logic.FO.Locality.NbhdIso.formula_realize_iff_of_two_pow`: sharp Gaifman locality at
  radius `2 ^ n - 1` ([Libkin, Exercises 4.10 and 4.11][Libkin2004]).
* `Cslib.Logic.FO.Locality.HanfEquiv.duplicatorWins_of_two_pow`,
  `Cslib.Logic.FO.Locality.HanfEquiv.realize_iff_of_two_pow`,
  `Cslib.Logic.FO.Locality.HanfEquiv.formula_realize_iff_of_two_pow`,
  `Cslib.Logic.FO.Locality.realize_sentence_iff_of_nbhdIso_two_pow`: sharp Hanf locality at radius
  `2 ^ (n - 1) - 1` ([Libkin, Exercises 4.10 and 4.11][Libkin2004]).
* `Cslib.Logic.FO.Locality.exists_nbhdIso_realize_loopReach`,
  `Cslib.Logic.FO.Locality.two_pow_sub_one_le_of_gaifman_radius`: optimality of the `2 ^ n - 1`
  Gaifman radius ([Libkin, Exercise 4.11][Libkin2004]).
* `Cslib.Logic.FO.Locality.exists_hanfEquiv_sentence_not_realize_iff`,
  `Cslib.Logic.FO.Locality.exists_hanfEquiv_formula_not_realize_iff`,
  `Cslib.Logic.FO.Locality.two_pow_pred_sub_one_le_of_hanf_sentence_radius`,
  `Cslib.Logic.FO.Locality.two_pow_pred_sub_one_le_of_hanf_radius`: optimality of the
  `2 ^ (n - 1) - 1` Hanf radius ([Libkin, Exercise 4.11][Libkin2004]).

## References

* [L. Libkin, *Elements of Finite Model Theory*][Libkin2004], Exercises 4.10 and 4.11 (pp. 63–64).
-/

public section

open FirstOrder Language Structure

namespace Cslib.Logic.FO.Locality

universe u v w w'

section UpperBounds

variable {L : Language.{u, v}} {M : Type w} {N : Type w'} [L.Structure M] [L.Structure N]

/-! ### Shrinking clustered neighborhood-isomorphism invariant -/

/-- One cluster `p` in a clustered game position: an enumeration `idx` of the indices assigned to
`p` together with a radius-`r` neighborhood isomorphism on the corresponding subtuples. -/
private structure ClusterEntry (L : Language.{u, v}) [L.Structure M] [L.Structure N]
    (r k : ℕ) (a : Fin k → M) (b : Fin k → N) (c : ℕ) (cl : Fin k → Fin c) (p : Fin c) where
  sz : ℕ
  idx : Fin sz → Fin k
  cl_idx : ∀ u, cl (idx u) = p
  mem_idx : ∀ i, cl i = p → ∃ u, idx u = i
  isoFun : M → N
  isNbhdIso : IsNbhdIso L r (a ∘ idx) (b ∘ idx) isoFun

/-- A clustered position with `m` rounds remaining: the `k` pebble indices are partitioned into `c`
clusters, each carrying a radius-`(2 ^ m - 1)` neighborhood isomorphism, while indices in distinct
clusters lie at Gaifman distance strictly greater than `2 ^ m` in both `M` and `N`. -/
private structure ClusterWitness (L : Language.{u, v}) [L.Structure M] [L.Structure N]
    (m : ℕ) {k : ℕ} (a : Fin k → M) (b : Fin k → N) where
  c : ℕ
  cl : Fin k → Fin c
  entry : ∀ p : Fin c, ClusterEntry L (2 ^ m - 1) k a b c cl p
  nullary : ∀ R : L.Relations 0,
    RelMap R (Fin.elim0 : Fin 0 → M) ↔ RelMap R (Fin.elim0 : Fin 0 → N)
  sepM : ∀ i j : Fin k, cl i ≠ cl j →
    ((2 ^ m : ℕ) : ℕ∞) < (gaifmanGraph L M).edist (a i) (a j)
  sepN : ∀ i j : Fin k, cl i ≠ cl j →
    ((2 ^ m : ℕ) : ℕ∞) < (gaifmanGraph L N).edist (b i) (b j)

private theorem two_pow_add_pred_eq (m : ℕ) : 2 ^ m + (2 ^ m - 1) = 2 ^ (m + 1) - 1 := by
  have := @Nat.one_le_two_pow m
  rw [pow_succ]
  omega

private theorem one_le_cast_two_pow (m : ℕ) : (1 : ℕ∞) ≤ ((2 ^ m : ℕ) : ℕ∞) := by
  exact_mod_cast @Nat.one_le_two_pow m

/-- Every clustered position is a partial isomorphism: pebbles in the same cluster agree via that
cluster's neighborhood isomorphism, while pebbles in distinct clusters have Gaifman distance
greater than `1` and therefore cannot be equal or share a relation tuple. -/
private theorem ClusterWitness.partialIso {m k : ℕ} {a : Fin k → M} {b : Fin k → N}
    (W : ClusterWitness L m a b) : PartialIso L a b := by
  refine ⟨fun i j => ?_, fun {l} R f => ?_⟩
  · by_cases hij : W.cl i = W.cl j
    · set p := W.cl i
      obtain ⟨u, hu⟩ := (W.entry p).mem_idx i rfl
      obtain ⟨v, hv⟩ := (W.entry p).mem_idx j hij.symm
      simpa only [Function.comp_apply, hu, hv] using
        (W.entry p).isNbhdIso.partialIso.eq_iff u v
    · exact iff_of_false (fun h => by simpa [h] using W.sepM i j hij)
        (fun h => by simpa [h] using W.sepN i j hij)
  · rcases Nat.eq_zero_or_pos l with rfl | hl
    · rw [Subsingleton.elim (a ∘ f) Fin.elim0, Subsingleton.elim (b ∘ f) Fin.elim0]
      exact W.nullary R
    · let i₀ : Fin l := ⟨0, hl⟩
      set p := W.cl (f i₀)
      by_cases hall : ∀ q : Fin l, W.cl (f q) = p
      · choose g hg using fun q => (W.entry p).mem_idx (f q) (hall q)
        have hcomp : (W.entry p).idx ∘ g = f := funext hg
        simpa only [Function.comp_assoc, hcomp] using
          (W.entry p).isNbhdIso.partialIso.relMap_iff R g
      · obtain ⟨q, hq⟩ := not_forall.mp hall
        have farM : 1 < (gaifmanGraph L M).edist (a (f q)) (a (f i₀)) :=
          (one_le_cast_two_pow m).trans_lt (W.sepM (f q) (f i₀) hq)
        have farN : 1 < (gaifmanGraph L N).edist (b (f q)) (b (f i₀)) :=
          (one_le_cast_two_pow m).trans_lt (W.sepN (f q) (f i₀) hq)
        exact iff_of_false
          (fun hR => absurd (edist_le_one_of_relMap hR q i₀) (not_le.2 farM))
          (fun hR => absurd (edist_le_one_of_relMap hR q i₀) (not_le.2 farN))

/-- Symmetry of clustered positions when `M` is nonempty. -/
private noncomputable def ClusterWitness.symm [Nonempty M] {m k : ℕ} {a : Fin k → M}
    {b : Fin k → N} (W : ClusterWitness L m a b) : ClusterWitness L m b a where
  c := W.c
  cl := W.cl
  entry p :=
    { sz := (W.entry p).sz
      idx := (W.entry p).idx
      cl_idx := (W.entry p).cl_idx
      mem_idx := (W.entry p).mem_idx
      isoFun := Function.invFunOn (W.entry p).isoFun (ball L (a ∘ (W.entry p).idx) (2 ^ m - 1))
      isNbhdIso := (W.entry p).isNbhdIso.symm }
  nullary R := (W.nullary R).symm
  sepM := W.sepN
  sepN := W.sepM

private theorem edist_gt_of_sep {V : Type*} {G : SimpleGraph V} {T : ℕ} {u v x : V}
    (huv : ((2 * T : ℕ) : ℕ∞) < G.edist u v) (hux : G.edist u x ≤ T) :
    ((T : ℕ) : ℕ∞) < G.edist x v := lt_of_not_ge fun hxv => huv.not_ge <| calc
  G.edist u v ≤ G.edist u x + G.edist x v := SimpleGraph.edist_triangle
  _ ≤ (T : ℕ∞) + T := add_le_add hux hxv
  _ = ((2 * T : ℕ) : ℕ∞) := by rw [← Nat.cast_add, two_mul]

private theorem cast_two_pow_le_succ (m : ℕ) : ((2 ^ m : ℕ) : ℕ∞) ≤ ((2 ^ (m + 1) : ℕ) : ℕ∞) := by
  exact_mod_cast Nat.pow_le_pow_right (by decide) (Nat.le_succ m)

/-- A point within `2 ^ m` of a cluster that is `2 ^ (m + 1)`-separated from another cluster
lies more than `2 ^ m` from every pebble of that other cluster. -/
private theorem lt_edist_of_mem_ball_of_sep {V : Type*} [L.Structure V] {m k c s : ℕ}
    {a : Fin k → V} {cl : Fin k → Fin c}
    (hsep : ∀ i j : Fin k, cl i ≠ cl j →
      ((2 ^ (m + 1) : ℕ) : ℕ∞) < (gaifmanGraph L V).edist (a i) (a j))
    {idx : Fin s → Fin k} {x : V} (hx : x ∈ ball L (a ∘ idx) (2 ^ m)) {j : Fin k}
    (hj : ∀ u, cl (idx u) ≠ cl j) : ((2 ^ m : ℕ) : ℕ∞) < (gaifmanGraph L V).edist x (a j) := by
  obtain ⟨u, hu⟩ := mem_ball.1 hx
  exact edist_gt_of_sep (pow_succ' 2 m ▸ hsep (idx u) j (hj u)) hu

/-- The `2 ^ m`-balls around two `2 ^ (m + 1)`-separated clusters are disjoint. -/
private theorem not_mem_ball_of_sep {V : Type*} [L.Structure V] {m k c s t : ℕ}
    {a : Fin k → V} {cl : Fin k → Fin c}
    (hsep : ∀ i j : Fin k, cl i ≠ cl j →
      ((2 ^ (m + 1) : ℕ) : ℕ∞) < (gaifmanGraph L V).edist (a i) (a j))
    {p q : Fin c} (hpq : p ≠ q) {idxp : Fin s → Fin k} {idxq : Fin t → Fin k}
    (hp : ∀ u, cl (idxp u) = p) (hq : ∀ u, cl (idxq u) = q) {z : V}
    (hz : z ∈ ball L (a ∘ idxp) (2 ^ m)) : z ∉ ball L (a ∘ idxq) (2 ^ m) := by
  intro hzq
  obtain ⟨v, hv⟩ := mem_ball.1 hzq
  exact (lt_edist_of_mem_ball_of_sep hsep hz fun u => hp u ▸ hq v ▸ hpq).not_ge
    (SimpleGraph.edist_comm ▸ hv)

/-- A point outside the `r`-ball around a subtuple lies more than `r` from each of its pebbles. -/
private theorem lt_edist_of_not_mem_ball {V : Type*} [L.Structure V] {k s r : ℕ} {a : Fin k → V}
    {idx : Fin s → Fin k} {x : V} {j : Fin k} (hj : ∃ u, idx u = j)
    (hx : x ∉ ball L (a ∘ idx) r) : ((r : ℕ) : ℕ∞) < (gaifmanGraph L V).edist x (a j) := by
  obtain ⟨u, rfl⟩ := hj
  rw [SimpleGraph.edist_comm]
  exact lt_of_not_ge fun hle => hx (mem_ball.2 ⟨u, hle⟩)

/-- The pebble separation of a clustered position extends to a new pebble `x`, given the
separation `hnew` of `x` from the pebbles outside its cluster. -/
private theorem sep_snoc {V : Type*} [L.Structure V] {m k c c' : ℕ} {a : Fin k → V}
    {cl : Fin k → Fin c} {cl' : Fin (k + 1) → Fin c'} {x : V}
    (hsep : ∀ i j : Fin k, cl i ≠ cl j →
      ((2 ^ (m + 1) : ℕ) : ℕ∞) < (gaifmanGraph L V).edist (a i) (a j))
    (hcl : ∀ i j : Fin k, cl' i.castSucc ≠ cl' j.castSucc → cl i ≠ cl j)
    (hnew : ∀ j : Fin k, cl' (Fin.last k) ≠ cl' j.castSucc →
      ((2 ^ m : ℕ) : ℕ∞) < (gaifmanGraph L V).edist x (a j))
    (i j : Fin (k + 1)) (hij : cl' i ≠ cl' j) :
    ((2 ^ m : ℕ) : ℕ∞) <
      (gaifmanGraph L V).edist ((Fin.snoc a x : Fin (k + 1) → V) i)
        ((Fin.snoc a x : Fin (k + 1) → V) j) := by
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => exact absurd rfl hij
    | cast j =>
      simp only [Fin.snoc_last, Fin.snoc_castSucc]
      exact hnew j hij
  | cast i =>
    induction j using Fin.lastCases with
    | last =>
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      rw [SimpleGraph.edist_comm]
      exact hnew i (Ne.symm hij)
    | cast j =>
      simp only [Fin.snoc_castSucc]
      exact (cast_two_pow_le_succ m).trans_lt (hsep i j (hcl i j hij))

/-- Lift an untouched cluster `E` across `Fin.snoc a x` and `Fin.snoc b y` at radius `d ≤ r`. -/
private def ClusterEntry.snocSkip {r d k c c' : ℕ} {a : Fin k → M} {b : Fin k → N}
    {cl : Fin k → Fin c} {p : Fin c} (E : ClusterEntry L r k a b c cl p) (hd : d ≤ r)
    (x : M) (y : N) (cl' : Fin (k + 1) → Fin c') (p' : Fin c')
    (hcl_idx : ∀ u, cl' (E.idx u).castSucc = p')
    (hmem_idx : ∀ j : Fin k, cl' j.castSucc = p' → cl j = p)
    (hlast : cl' (Fin.last k) ≠ p') :
    ClusterEntry L d (k + 1) (Fin.snoc a x) (Fin.snoc b y) c' cl' p' where
  sz := E.sz
  idx := Fin.castSucc ∘ E.idx
  cl_idx := hcl_idx
  mem_idx i hi := by
    induction i using Fin.lastCases with
    | last => exact absurd hi hlast
    | cast j =>
      obtain ⟨u, hu⟩ := E.mem_idx j (hmem_idx j hi)
      exact ⟨u, congrArg Fin.castSucc hu⟩
  isoFun := E.isoFun
  isNbhdIso := by
    simpa only [← Function.comp_assoc, Fin.snoc_comp_castSucc] using E.isNbhdIso.mono hd

/-- Extend cluster `E` with `(x, E.isoFun x)` at radius `d` when `x ∈ ball L (a ∘ E.idx) l` and
`l + d ≤ r`. -/
private def ClusterEntry.snocExtend {r l d k c : ℕ} {a : Fin k → M} {b : Fin k → N}
    {cl : Fin k → Fin c} {p : Fin c} (E : ClusterEntry L r k a b c cl p) (hld : l + d ≤ r)
    {x : M} (hx : x ∈ ball L (a ∘ E.idx) l) :
    ClusterEntry L d (k + 1) (Fin.snoc a x) (Fin.snoc b (E.isoFun x)) c (Fin.snoc cl p) p where
  sz := E.sz + 1
  idx := Fin.snoc (Fin.castSucc ∘ E.idx) (Fin.last k)
  cl_idx u := by
    induction u using Fin.lastCases with
    | last => simp
    | cast u => simp [E.cl_idx u]
  mem_idx i hi := by
    induction i using Fin.lastCases with
    | last => exact ⟨Fin.last E.sz, by simp⟩
    | cast j =>
      simp only [Fin.snoc_castSucc] at hi
      obtain ⟨u, hu⟩ := E.mem_idx j hi
      exact ⟨u.castSucc, by simp [hu]⟩
  isoFun := E.isoFun
  isNbhdIso := by
    have hsub : ∀ u : Fin (E.sz + 1),
        (Fin.snoc (a ∘ E.idx) x : Fin (E.sz + 1) → M) u ∈ ball L (a ∘ E.idx) l := by
      intro u
      induction u using Fin.lastCases with
      | last => simpa using hx
      | cast u => simpa using ball_mono (Nat.zero_le l) (mem_ball_self (a ∘ E.idx) 0 u)
    have hres := E.isNbhdIso.restrict (x := Fin.snoc (a ∘ E.idx) x) (l := l) (d := d) hsub hld
    rw [Fin.comp_snoc, show E.isoFun ∘ (a ∘ E.idx) = b ∘ E.idx from
      funext E.isNbhdIso.map_tuple] at hres
    simpa only [Fin.comp_snoc, ← Function.comp_assoc, Fin.snoc_comp_castSucc, Fin.snoc_last]
      using hres

/-- Singleton cluster `{Fin.last k}` formed from a far move `(x, y)`. -/
private def ClusterEntry.snocSingleton {d k c : ℕ} (a : Fin k → M) (b : Fin k → N)
    (cl : Fin k → Fin c) {x : M} {y : N} {h : M → N}
    (H : IsNbhdIso L d (fun _ : Fin 1 => x) (fun _ : Fin 1 => y) h) :
    ClusterEntry L d (k + 1) (Fin.snoc a x) (Fin.snoc b y) (c + 1)
      (Fin.snoc (Fin.castSucc ∘ cl) (Fin.last c)) (Fin.last c) where
  sz := 1
  idx := fun _ => Fin.last k
  cl_idx _ := by simp
  mem_idx i hi := by
    induction i using Fin.lastCases with
    | last => exact ⟨0, rfl⟩
    | cast j =>
      simp only [Fin.snoc_castSucc, Function.comp_apply] at hi
      exact absurd hi (Fin.castSucc_ne_last _)
  isoFun := h
  isNbhdIso := by
    simpa only [Function.comp_def, Fin.snoc_last] using H

/-- One forth step of the clustered invariant: from stage `m + 1` and Spoiler move `x : M`,
Duplicator finds `y : N` preserving `ClusterWitness` at stage `m`. -/
private theorem ClusterWitness.forth [Finite M] {m k : ℕ} {a : Fin k → M} {b : Fin k → N}
    (W : ClusterWitness L (m + 1) a b) (e : M ≃ N)
    (he : ∀ z, NbhdIso L (2 ^ m - 1) (fun _ : Fin 1 => z) (fun _ : Fin 1 => e z)) (x : M) :
    ∃ y : N, Nonempty (ClusterWitness L m (Fin.snoc a x : Fin (k + 1) → M)
      (Fin.snoc b y : Fin (k + 1) → N)) := by
  have hr_eq := two_pow_add_pred_eq m
  have hr : 2 ^ m ≤ 2 ^ (m + 1) - 1 := by lia
  have hshrink : 2 ^ m - 1 ≤ 2 ^ (m + 1) - 1 := (Nat.sub_le _ _).trans hr
  by_cases hnear : ∃ p : Fin W.c, x ∈ ball L (a ∘ (W.entry p).idx) (2 ^ m)
  · -- Case A: `x` lies within `2 ^ m` of some cluster `p₀`; extend `p₀`.
    obtain ⟨p₀, hx⟩ := hnear
    set E₀ := W.entry p₀
    set y := E₀.isoFun x
    have hy : y ∈ ball L (b ∘ E₀.idx) (2 ^ m) :=
      E₀.isNbhdIso.mapsTo_ball hr hx
    refine ⟨y, ⟨{
      c := W.c
      cl := Fin.snoc W.cl p₀
      entry := fun p =>
        if hp : p = p₀ then hp ▸ E₀.snocExtend hr_eq.le hx
        else (W.entry p).snocSkip hshrink x y (Fin.snoc W.cl p₀) p
          (fun u => by simp [(W.entry p).cl_idx u])
          (fun _ hj => by simpa only [Fin.snoc_castSucc] using hj)
          (by simp [Ne.symm hp])
      nullary := W.nullary
      sepM := sep_snoc W.sepM (fun i j h => by simpa only [Fin.snoc_castSucc] using h)
        fun j hj => lt_edist_of_mem_ball_of_sep W.sepM hx fun u => by
          simpa only [E₀.cl_idx u, Fin.snoc_last, Fin.snoc_castSucc] using hj
      sepN := sep_snoc W.sepN (fun i j h => by simpa only [Fin.snoc_castSucc] using h)
        fun j hj => lt_edist_of_mem_ball_of_sep W.sepN hy fun u => by
          simpa only [E₀.cl_idx u, Fin.snoc_last, Fin.snoc_castSucc] using hj }⟩⟩
  · -- Case B: `x` lies outside every cluster's `2 ^ m`-ball; form a new singleton cluster.
    let BM : Fin W.c → Set M := fun p => ball L (a ∘ (W.entry p).idx) (2 ^ m)
    let BN : Fin W.c → Set N := fun p => ball L (b ∘ (W.entry p).idx) (2 ^ m)
    have disjM : Pairwise fun p q => Disjoint (BM p) (BM q) := fun p q hpq =>
      Set.disjoint_left.2 fun _ hz =>
        not_mem_ball_of_sep W.sepM hpq (W.entry p).cl_idx (W.entry q).cl_idx hz
    have disjN : Pairwise fun p q => Disjoint (BN p) (BN q) := fun p q hpq =>
      Set.disjoint_left.2 fun _ hz =>
        not_mem_ball_of_sep W.sepN hpq (W.entry p).cl_idx (W.entry q).cl_idx hz
    set SM : Set M := ⋃ p, BM p
    set SN : Set N := ⋃ p, BN p
    classical
    -- Identify each union with the dependent sum of its disjoint cluster balls.
    let ballEquiv (p : Fin W.c) : BM p ≃ BN p :=
      Set.BijOn.equiv _ ((W.entry p).isNbhdIso.mono hr).bijOn
    let EM := Set.unionEqSigmaOfDisjoint disjM
    let EN := Set.unionEqSigmaOfDisjoint disjN
    let E : SM ≃ SN := EM.trans ((Equiv.sigmaCongrRight ballEquiv).trans EN.symm)
    let H : M → N := fun z => if hz : z ∈ SM then (E ⟨z, hz⟩).val else e z
    have hH (z : SM) : H z = (E z).val := dite_eq_left z.property
    have hEq (p : Fin W.c) {z : M} (hzp : z ∈ BM p) : H z = (W.entry p).isoFun z := by
      let q : Σ p, BM p := ⟨p, ⟨z, hzp⟩⟩
      change H (EM.symm q).val = (W.entry p).isoFun z
      rw [hH (EM.symm q)]
      simp only [E, Equiv.trans_apply, Equiv.apply_symm_apply]
      rfl
    have hBij : Set.BijOn H SM SN := by
      refine ⟨fun z hz => hH ⟨z, hz⟩ ▸ (E ⟨z, hz⟩).property,
        fun z hz w hw he => ?_, fun w hw => ?_⟩
      · rw [hH ⟨z, hz⟩, hH ⟨w, hw⟩] at he
        exact congrArg Subtype.val (E.injective (Subtype.ext he))
      · obtain ⟨z, hz⟩ := E.surjective ⟨w, hw⟩
        exact ⟨z, z.property, (hH z).trans (congrArg Subtype.val hz)⟩
    have hPt : ∀ z ∈ SM, NbhdIso L (2 ^ m - 1) (fun _ : Fin 1 => z) (fun _ : Fin 1 => H z) := by
      intro z hz
      obtain ⟨p, hzp⟩ := Set.mem_iUnion.1 hz
      rw [hEq p hzp]
      exact ((W.entry p).isNbhdIso.restrict (x := fun _ : Fin 1 => z) (l := 2 ^ m)
        (d := 2 ^ m - 1) (fun _ => hzp) hr_eq.le).nbhdIso
    obtain ⟨g, hg⟩ := exists_compl_equiv_nbhdIso e he hBij hPt
    have hxSM : x ∈ SMᶜ := fun hx' => hnear (Set.mem_iUnion.1 hx')
    set y : N := (g ⟨x, hxSM⟩).val
    have hySN : y ∉ SN := (g ⟨x, hxSM⟩).property
    obtain ⟨h_xy, H_xy⟩ := nbhdIso_iff.1 (hg ⟨x, hxSM⟩)
    refine ⟨y, ⟨{
      c := W.c + 1
      cl := Fin.snoc (Fin.castSucc ∘ W.cl) (Fin.last W.c)
      entry := fun p =>
        Fin.lastCases (ClusterEntry.snocSingleton a b W.cl H_xy)
          (fun p' => (W.entry p').snocSkip hshrink x y
            (Fin.snoc (Fin.castSucc ∘ W.cl) (Fin.last W.c)) p'.castSucc
            (fun u => by simp [(W.entry p').cl_idx u])
            (fun _ hj => by
              simpa only [Fin.snoc_castSucc, Function.comp_apply, Fin.castSucc_inj] using hj)
            (by simp [(Fin.castSucc_ne_last p').symm])) p
      nullary := W.nullary
      sepM := sep_snoc W.sepM (fun i j h => by simpa only [Fin.snoc_castSucc,
          Function.comp_apply, ne_eq, Fin.castSucc_inj] using h)
        fun j _ => lt_edist_of_not_mem_ball ((W.entry (W.cl j)).mem_idx j rfl)
          fun h => hxSM (Set.mem_iUnion.2 ⟨W.cl j, h⟩)
      sepN := sep_snoc W.sepN (fun i j h => by simpa only [Fin.snoc_castSucc,
          Function.comp_apply, ne_eq, Fin.castSucc_inj] using h)
        fun j _ => lt_edist_of_not_mem_ball ((W.entry (W.cl j)).mem_idx j rfl)
          fun h => hySN (Set.mem_iUnion.2 ⟨W.cl j, h⟩) }⟩⟩

private theorem ClusterWitness.duplicatorWins [Finite M] :
    ∀ {n k : ℕ} {a : Fin k → M} {b : Fin k → N} (e : M ≃ N),
      (∀ m < n, ∀ z, NbhdIso L (2 ^ m - 1) (fun _ : Fin 1 => z) (fun _ : Fin 1 => e z)) →
      ClusterWitness L n a b → DuplicatorWins L n a b
  | 0, _, _, _, _, _, W => duplicatorWins_zero.2 W.partialIso
  | n + 1, _, _, _, e, he, W => by
    refine duplicatorWins_succ.2 ⟨W.partialIso, fun x => ?_, fun y => ?_⟩
    · obtain ⟨y, ⟨W'⟩⟩ := W.forth e (he n (Nat.lt_succ_self n)) x
      exact ⟨y, W'.duplicatorWins e (fun m hm => he m (Nat.lt_succ_of_lt hm))⟩
    · have hM : Nonempty M := ⟨e.symm y⟩
      have hN : Nonempty N := ⟨y⟩
      have : Finite N := Finite.of_equiv M e
      have he' : ∀ z, NbhdIso L (2 ^ n - 1) (fun _ : Fin 1 => z) (fun _ : Fin 1 => e.symm z) :=
        fun z => by simpa using (he n (Nat.lt_succ_self n) (e.symm z)).symm
      obtain ⟨x, ⟨W'⟩⟩ := W.symm.forth e.symm he' y
      exact ⟨x, W'.symm.duplicatorWins e (fun m hm => he m (Nat.lt_succ_of_lt hm))⟩

/-! ### Sharp Gaifman locality (`2 ^ n - 1`) -/

/-- **Sharp Gaifman locality, two-structure form**
([Libkin, Exercises 4.10 and 4.11][Libkin2004]): if a bijection `e : M ≃ N` from a finite
structure matches points with isomorphic radius-`(2 ^ (n - 1) - 1)` neighborhoods, then tuples
with isomorphic radius-`(2 ^ n - 1)` neighborhoods are `n`-round
Ehrenfeucht–Fraïssé-equivalent. -/
theorem NbhdIso.duplicatorWins_of_equiv_two_pow [Finite M] {n k : ℕ} {a : Fin k → M}
    {b : Fin k → N} (e : M ≃ N)
    (he : ∀ c, NbhdIso L (2 ^ (n - 1) - 1) (fun _ : Fin 1 => c) (fun _ : Fin 1 => e c))
    (hab : NbhdIso L (2 ^ n - 1) a b) : DuplicatorWins L n a b := by
  obtain ⟨h, Hh⟩ := nbhdIso_iff.1 hab
  let W : ClusterWitness L n a b :=
    { c := 1
      cl := fun _ => 0
      entry := fun p =>
        { sz := k
          idx := id
          cl_idx := fun _ => Subsingleton.elim 0 p
          mem_idx := fun i _ => ⟨i, rfl⟩
          isoFun := h
          isNbhdIso := Hh }
      nullary := fun R => by
        simpa only [Subsingleton.elim (a ∘ Fin.elim0) Fin.elim0,
          Subsingleton.elim (b ∘ Fin.elim0) Fin.elim0] using Hh.partialIso.relMap_iff R Fin.elim0
      sepM := fun _ _ hne => absurd (Subsingleton.elim _ _) hne
      sepN := fun _ _ hne => absurd (Subsingleton.elim _ _) hne }
  refine W.duplicatorWins e fun m hm z => (he z).mono ?_
  exact Nat.sub_le_sub_right (Nat.pow_le_pow_right (by decide) (by omega)) 1

/-- **Sharp Gaifman locality** ([Libkin, Exercises 4.10 and 4.11][Libkin2004]): in a finite
structure, tuples with isomorphic radius-`(2 ^ n - 1)` neighborhoods are `n`-round
Ehrenfeucht–Fraïssé-equivalent. -/
theorem NbhdIso.duplicatorWins_of_two_pow [Finite M] {n k : ℕ} {a₁ a₂ : Fin k → M}
    (hab : NbhdIso L (2 ^ n - 1) a₁ a₂) : DuplicatorWins L n a₁ a₂ :=
  hab.duplicatorWins_of_equiv_two_pow (Equiv.refl M) fun _ => NbhdIso.refl _ _

/-- **Sharp Gaifman locality for bounded formulas**
([Libkin, Exercises 4.10 and 4.11][Libkin2004]): in a finite structure over a relational language,
tuples with isomorphic radius-`(2 ^ n - 1)` neighborhoods satisfy the same formulas of quantifier
rank at most `n`. -/
theorem NbhdIso.realize_iff_of_two_pow [L.IsRelational] [Finite M] {n k : ℕ} {a₁ a₂ : Fin k → M}
    (h : NbhdIso L (2 ^ n - 1) a₁ a₂) {φ : L.BoundedFormula Empty k}
    (hφ : quantifierRank φ ≤ n) : φ.Realize default a₁ ↔ φ.Realize default a₂ :=
  h.duplicatorWins_of_two_pow.realize_iff hφ

/-- **Sharp Gaifman locality for formulas with free variables**
([Libkin, Exercises 4.10 and 4.11][Libkin2004]): the form of `NbhdIso.realize_iff_of_two_pow` for
`φ : L.Formula (Fin k)`. -/
theorem NbhdIso.formula_realize_iff_of_two_pow [L.IsRelational] [Finite M] {n k : ℕ}
    {a₁ a₂ : Fin k → M} (h : NbhdIso L (2 ^ n - 1) a₁ a₂) {φ : L.Formula (Fin k)}
    (hφ : quantifierRank φ ≤ n) : φ.Realize a₁ ↔ φ.Realize a₂ :=
  h.duplicatorWins_of_two_pow.formula_realize_iff hφ

/-! ### Sharp Hanf locality (`2 ^ (n - 1) - 1`) -/

/-- **Sharp Hanf locality** ([Libkin, Exercises 4.10 and 4.11][Libkin2004]): over a finite
nonempty structure, tuples that are Hanf-equivalent at radius `2 ^ (n - 1) - 1` are `n`-round
Ehrenfeucht–Fraïssé-equivalent. The language is arbitrary. -/
theorem HanfEquiv.duplicatorWins_of_two_pow [Finite M] [Nonempty M] :
    ∀ {n k : ℕ} {a : Fin k → M} {b : Fin k → N},
      HanfEquiv L (2 ^ (n - 1) - 1) a b → DuplicatorWins L n a b
  | 0, _, _, _, H => duplicatorWins_zero.2 H.nbhdIso.partialIso
  | m + 1, k, a, b, H => by
    have hP := H.nbhdIso.partialIso
    simp only [Nat.add_sub_cancel] at H
    obtain ⟨f, hf⟩ := hanfEquiv_iff.1 H
    have he : ∀ c', NbhdIso L (2 ^ (m - 1) - 1) (fun _ : Fin 1 => c')
        (fun _ : Fin 1 => f c') := fun c' => by
      obtain ⟨h, Hh⟩ := nbhdIso_iff.1 (hf c')
      have hres := Hh.restrict (x := fun _ : Fin 1 => c') (l := 0) (d := 2 ^ (m - 1) - 1)
        (fun _ => mem_ball_snoc.2 (.inr (mem_ball_self _ 0 0)))
        (by
          have : 2 ^ (m - 1) ≤ 2 ^ m := Nat.pow_le_pow_right (by decide) (Nat.sub_le m 1)
          omega)
      have hc' : h c' = f c' := by simpa using Hh.map_tuple (Fin.last k)
      exact (by simpa [Function.comp_def, hc'] using hres : IsNbhdIso L _ _ _ h).nbhdIso
    refine duplicatorWins_succ.2 ⟨hP, fun c => ⟨f c, ?_⟩, fun d => ⟨f.symm d, ?_⟩⟩
    · exact (hf c).duplicatorWins_of_equiv_two_pow f he
    · have hd := hf (f.symm d)
      rw [f.apply_symm_apply] at hd
      exact hd.duplicatorWins_of_equiv_two_pow f he

/-- **Sharp Hanf locality for bounded formulas** ([Libkin, Exercises 4.10 and 4.11][Libkin2004]):
over a finite nonempty structure and a relational language, tuples that are Hanf-equivalent at
radius `2 ^ (n - 1) - 1` satisfy the same bounded formulas of quantifier rank at most `n`. -/
theorem HanfEquiv.realize_iff_of_two_pow [L.IsRelational] [Finite M] [Nonempty M] {n k : ℕ}
    {a : Fin k → M} {b : Fin k → N} (h : HanfEquiv L (2 ^ (n - 1) - 1) a b)
    {φ : L.BoundedFormula Empty k} (hφ : quantifierRank φ ≤ n) :
    φ.Realize default a ↔ φ.Realize default b :=
  h.duplicatorWins_of_two_pow.realize_iff hφ

/-- **Sharp Hanf locality for formulas with free variables**
([Libkin, Exercises 4.10 and 4.11][Libkin2004]). -/
theorem HanfEquiv.formula_realize_iff_of_two_pow [L.IsRelational] [Finite M] [Nonempty M]
    {n k : ℕ} {a : Fin k → M} {b : Fin k → N} (h : HanfEquiv L (2 ^ (n - 1) - 1) a b)
    {φ : L.Formula (Fin k)} (hφ : quantifierRank φ ≤ n) :
    φ.Realize a ↔ φ.Realize b :=
  h.duplicatorWins_of_two_pow.formula_realize_iff hφ

/-- **Sharp Hanf locality for sentences** ([Libkin, Exercises 4.10 and 4.11][Libkin2004]): if a
bijection between a finite nonempty structure `M` and `N` matches points with isomorphic
radius-`(2 ^ (n - 1) - 1)` neighborhoods, then `M` and `N` satisfy the same sentences of
quantifier rank at most `n`. -/
theorem realize_sentence_iff_of_nbhdIso_two_pow [L.IsRelational] [Finite M] [Nonempty M] {n : ℕ}
    (e : M ≃ N)
    (he : ∀ c, NbhdIso L (2 ^ (n - 1) - 1) (fun _ : Fin 1 => c) (fun _ : Fin 1 => e c))
    {φ : L.Sentence} (hφ : quantifierRank φ ≤ n) : M ⊨ φ ↔ N ⊨ φ :=
  (hanfEquiv_zero_iff.2 ⟨e, he⟩ : HanfEquiv L _ (default : Fin 0 → M)
    (default : Fin 0 → N)).realize_iff_of_two_pow hφ

end UpperBounds

/-! ### Matching lower bounds over `FirstOrder.Language.graph` -/

section LowerBounds

/-- `loopReach n` has quantifier rank `n` (`quantifierRank_loopReach`) and asserts that a vertex
with a self-loop (`adj x x`) is reachable within `2 ^ n - 1` steps along `distLE`. -/
def loopReach : ℕ → Language.graph.Formula (Fin 1)
  | 0 => adj.formula₂ (Term.var 0) (Term.var 0)
  | k + 1 => (BoundedFormula.relabel (fun i : Fin 2 => ![Sum.inl 0, Sum.inr 0] i) (distLE k) ⊓
      BoundedFormula.relabel (fun _ : Fin 1 => Sum.inr 0) (loopReach k)).ex

@[simp] theorem quantifierRank_loopReach (n : ℕ) : quantifierRank (loopReach n) = n := by
  induction n with
  | zero =>
    simp only [loopReach, Relations.formula₂, Relations.formula,
      quantifierRank_relations_boundedFormula]
  | succ k ih =>
    simp only [loopReach, quantifierRank_ex, quantifierRank_inf, quantifierRank_relabel,
      quantifierRank_distLE, ih, max_self]

theorem realize_loopReach_zero {M : Type*} [Language.graph.Structure M] (x : M) :
    (loopReach 0).Realize ![x] ↔ RelMap adj ![x, x] := by
  fo_simp [loopReach]

private theorem boundedFormula_realize_iff_formula_realize {L : Language} {M : Type*}
    [L.Structure M] {m : ℕ} (φ : L.Formula (Fin m)) {v v' : Fin m → M} (hv : ∀ i, v i = v' i)
    (xs : Fin 0 → M) : BoundedFormula.Realize φ v xs ↔ Formula.Realize φ v' := by
  rw [Formula.Realize, funext hv, Subsingleton.elim xs default]

theorem realize_loopReach_succ {M : Type*} [Language.graph.Structure M] (k : ℕ) (x : M) :
    (loopReach (k + 1)).Realize ![x] ↔
      ∃ z, (distLE k).Realize ![x, z] ∧ (loopReach k).Realize ![z] := by
  fo_simp [loopReach]
  exact exists_congr fun z => and_congr
    (boundedFormula_realize_iff_formula_realize _ (fun i => by fin_cases i <;> rfl) _)
    (boundedFormula_realize_iff_formula_realize _ (fun i => by fin_cases i; rfl) _)

/-! #### Exactness of the Gaifman locality rank `2 ^ n - 1` -/

private theorem relMap_adj_relStructure {V : Type*} (R : V → V → Prop) (t : Fin 2 → V) :
    (letI := relStructure R; RelMap adj t) ↔ R (t 0) (t 1) := by
  let := relStructure R
  have ht : t = ![t 0, t 1] := by ext i; fin_cases i <;> rfl
  conv_lhs => rw [ht]
  rw [relMap_relStructure]

/-- Augmenting a binary relation with self-loops leaves its Gaifman graph unchanged, since Gaifman
adjacency ignores diagonal pairs. -/
private theorem gaifmanGraph_or_eq_and {V : Type*} (R : V → V → Prop) (S : V → Prop) :
    @gaifmanGraph Language.graph V (relStructure fun x y => R x y ∨ (x = y ∧ S x)) =
      SimpleGraph.fromRel R := by
  rw [gaifmanGraph_relStructure]
  ext x y
  simp only [SimpleGraph.fromRel_adj]
  grind

/-- Any bijection `φ : V ≃ V` preserving a base relation `R` globally and preserving self-loops on
the radius-`d` ball around `c` restricts to a radius-`d` neighborhood isomorphism. -/
private theorem isNbhdIso_or_eq_and {V : Type*} {d : ℕ} {R : V → V → Prop}
    {S₁ S₂ : V → Prop} (c : V) (φ : V ≃ V)
    (hR : ∀ u v, R (φ u) (φ v) ↔ R u v)
    (hloop : ∀ u ∈ @ball Language.graph V
      (relStructure fun x y => R x y ∨ (x = y ∧ S₁ x)) 1 (fun _ => c) d,
      S₂ (φ u) ↔ S₁ u) :
    @IsNbhdIso Language.graph V V
      (relStructure fun x y => R x y ∨ (x = y ∧ S₁ x))
      (relStructure fun x y => R x y ∨ (x = y ∧ S₂ x))
      1 d (fun _ => c) (fun _ => φ c) φ := by
  let I₁ := relStructure fun x y => R x y ∨ (x = y ∧ S₁ x)
  let I₂ := relStructure fun x y => R x y ∨ (x = y ∧ S₂ x)
  let eG : (@gaifmanGraph Language.graph V I₁) ≃g (@gaifmanGraph Language.graph V I₂) :=
    { toEquiv := φ
      map_rel_iff' := fun {u v} => by
        rw [gaifmanGraph_or_eq_and, gaifmanGraph_or_eq_and, SimpleGraph.fromRel_adj,
          SimpleGraph.fromRel_adj, φ.injective.ne_iff, hR u v, hR v u] }
  have hball : ∀ u : V,
      u ∈ @ball Language.graph V I₁ 1 (fun _ => c) d ↔
        φ u ∈ @ball Language.graph V I₂ 1 (fun _ => φ c) d := fun u => by
    rw [@mem_ball_const Language.graph V I₁, @mem_ball_const Language.graph V I₂]
    exact iff_of_eq (congrArg (· ≤ (d : ℕ∞)) (eG.edist_eq c u).symm)
  refine @IsNbhdIso.mk Language.graph V V I₁ I₂ 1 d (fun _ => c) (fun _ => φ c) φ
    ⟨fun u hu => (hball u).1 hu, fun _ _ _ _ h => φ.injective h,
      fun v hv => ⟨φ.symm v, (hball _).2 (by simpa only [Equiv.apply_symm_apply] using hv),
        φ.apply_symm_apply v⟩⟩
    (fun _ => rfl) fun {l} R' t ht => ?_
  cases R'
  rw [relMap_adj_relStructure _ (φ ∘ t), relMap_adj_relStructure _ t]
  dsimp only [Function.comp_apply]
  refine or_congr (hR (t 0) (t 1)) ?_
  rw [φ.injective.eq_iff]
  exact and_congr_right fun _ => hloop (t 0) (ht 0)

/-- A simple graph `G` augmented with self-loops on a vertex set `S`. Its Gaifman graph is `G`
itself, since Gaifman adjacency ignores self-loops. -/
private def loopGraphRel {V : Type*} (G : SimpleGraph V) (S : V → Prop) (x y : V) : Prop :=
  G.Adj x y ∨ (x = y ∧ S x)

private theorem gaifmanGraph_loopGraphRel {V : Type*} (G : SimpleGraph V) (S : V → Prop) :
    @gaifmanGraph Language.graph V (relStructure (loopGraphRel G S)) = G := by
  unfold loopGraphRel
  rw [gaifmanGraph_or_eq_and]
  ext x y
  simp only [SimpleGraph.fromRel_adj, G.adj_comm, or_self, and_iff_right_iff_imp]
  exact SimpleGraph.Adj.ne

private theorem realize_distLE_loopGraphRel {V : Type*} (G : SimpleGraph V) (S : V → Prop)
    (k : ℕ) (x y : V) :
    (letI := relStructure (loopGraphRel G S); (distLE k).Realize ![x, y]) ↔
      G.edist x y ≤ ((2 ^ k : ℕ) : ℕ∞) := by
  let := relStructure (loopGraphRel G S)
  induction k generalizing x y with
  | zero =>
    rw [realize_distLE_zero, relMap_relStructure, pow_zero, Nat.cast_one,
      SimpleGraph.edist_le_one_iff_adj_or_eq]
    simp only [loopGraphRel]
    tauto
  | succ k ih =>
    have h2 : ((2 ^ (k + 1) : ℕ) : ℕ∞) = ((2 ^ k : ℕ) : ℕ∞) + ((2 ^ k : ℕ) : ℕ∞) := by
      rw [pow_succ, mul_two, Nat.cast_add]
    rw [realize_distLE_succ]
    simp only [ih]
    exact ⟨fun ⟨z, h1, h2'⟩ => SimpleGraph.edist_triangle.trans (h2 ▸ add_le_add h1 h2'),
      fun h => SimpleGraph.exists_edist_le_of_edist_le_add (by rwa [Nat.cast_add, ← h2])⟩

private theorem realize_loopReach_loopGraphRel {V : Type*} (G : SimpleGraph V) (S : V → Prop)
    (n : ℕ) (x : V) :
    (letI := relStructure (loopGraphRel G S); (loopReach n).Realize ![x]) ↔
      ∃ y, S y ∧ G.edist x y ≤ ((2 ^ n - 1 : ℕ) : ℕ∞) := by
  let := relStructure (loopGraphRel G S)
  induction n generalizing x with
  | zero =>
    rw [realize_loopReach_zero, relMap_relStructure]
    simp only [loopGraphRel, G.loopless.irrefl, false_or, true_and, pow_zero, Nat.sub_self,
      Nat.cast_zero, nonpos_iff_eq_zero, SimpleGraph.edist_eq_zero_iff]
    exact ⟨fun hx => ⟨x, hx, rfl⟩, fun ⟨y, hy, hxy⟩ => hxy ▸ hy⟩
  | succ k ih =>
    rw [realize_loopReach_succ]
    simp only [realize_distLE_loopGraphRel, ih]
    have hsum : ((2 ^ (k + 1) - 1 : ℕ) : ℕ∞) = ((2 ^ k : ℕ) : ℕ∞) + ((2 ^ k - 1 : ℕ) : ℕ∞) := by
      rw [← Nat.cast_add, two_pow_add_pred_eq]
    constructor
    · rintro ⟨z, hxz, y, hy, hzy⟩
      exact ⟨y, hy, SimpleGraph.edist_triangle.trans (hsum ▸ add_le_add hxz hzy)⟩
    · rintro ⟨y, hy, hxy⟩
      obtain ⟨z, hxz, hzy⟩ := SimpleGraph.exists_edist_le_of_edist_le_add
        (by rwa [Nat.cast_add, ← hsum])
      exact ⟨z, hxz, y, hy, hzy⟩

/-- **Exactness of the Gaifman locality rank `2 ^ n - 1`** ([Libkin, Exercise 4.11][Libkin2004]):
for every `n ≥ 1` and `r < 2 ^ n - 1`, two vertices of a finite `Language.graph`-structure have
isomorphic radius-`r` neighborhoods while `loopReach n` (of quantifier rank `n`) holds of the first
and fails of the second. -/
theorem exists_nbhdIso_realize_loopReach {n r : ℕ} (hn : 1 ≤ n) (hr : r < 2 ^ n - 1) :
    ∃ (M : Type) (_ : Finite M) (_ : Language.graph.Structure M) (a b : Fin 1 → M),
      NbhdIso Language.graph r a b ∧
      (loopReach n).Realize a ∧
      ¬ (loopReach n).Realize b := by
  have hm : 2 ≤ 2 ^ n := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by decide : 0 < 2) hn
  set m := 2 ^ n
  let P := SimpleGraph.pathGraph m
  let G := P ⊕g P
  let loopPt : Fin m ⊕ Fin m := .inl ⟨m - 1, by omega⟩
  let S : Fin m ⊕ Fin m → Prop := (· = loopPt)
  let _ : Language.graph.Structure (Fin m ⊕ Fin m) := relStructure (loopGraphRel G S)
  let x₀ : Fin m := ⟨0, by omega⟩
  have hvec (z : Fin m ⊕ Fin m) : (fun _ : Fin 1 => z) = ![z] :=
    funext (Fin.forall_fin_one.mpr rfl)
  refine ⟨Fin m ⊕ Fin m, inferInstance, inferInstance, fun _ => .inl x₀, fun _ => .inr x₀,
    ?_, ?_, ?_⟩
  · refine (isNbhdIso_or_eq_and (.inl x₀) (Equiv.sumComm (Fin m) (Fin m))
      (fun u v => (SimpleGraph.Iso.sumComm (G := P) (H := P)).map_adj_iff) fun u hu => ?_).nbhdIso
    change u ∈ ball Language.graph (fun _ : Fin 1 => (.inl x₀ : Fin m ⊕ Fin m)) r at hu
    rw [mem_ball_const, gaifmanGraph_loopGraphRel] at hu
    rcases u with j | j
    · refine iff_of_false Sum.inr_ne_inl fun h => ?_
      have hj : (j : ℕ) = m - 1 := congrArg Fin.val (Sum.inl.inj h)
      rw [SimpleGraph.edist_sum_inl, SimpleGraph.edist_pathGraph, Nat.cast_le] at hu
      simp only [x₀] at hu
      omega
    · exact absurd hu (not_le.2 (by
        rw [SimpleGraph.edist_eq_top_of_not_reachable (SimpleGraph.not_reachable_sum_inl_inr _ _)]
        exact ENat.natCast_lt_top r))
  · rw [hvec, realize_loopReach_loopGraphRel]
    refine ⟨loopPt, rfl, ?_⟩
    rw [SimpleGraph.edist_sum_inl, SimpleGraph.edist_pathGraph, Nat.cast_le]
    simp only [x₀, m]
    omega
  · rw [hvec, realize_loopReach_loopGraphRel]
    rintro ⟨y, rfl, hy⟩
    rw [SimpleGraph.edist_comm, SimpleGraph.edist_eq_top_of_not_reachable
      (SimpleGraph.not_reachable_sum_inl_inr _ _)] at hy
    exact absurd hy (not_le.2 (ENat.natCast_lt_top _))

/-- **Optimality of the Gaifman locality rank `2 ^ n - 1`**
([Libkin, Exercise 4.11][Libkin2004]): any radius function `ρ` giving Gaifman locality on finite
`Language.graph`-structures for `1`-tuples and formulas of quantifier rank at most `n` satisfies
`2 ^ n - 1 ≤ ρ n` for every `n`. -/
theorem two_pow_sub_one_le_of_gaifman_radius {ρ : ℕ → ℕ}
    (hρ : ∀ (n : ℕ) (M : Type) [Finite M] [Language.graph.Structure M] (a b : Fin 1 → M)
      (φ : Language.graph.Formula (Fin 1)), quantifierRank φ ≤ n →
      NbhdIso Language.graph (ρ n) a b → (φ.Realize a ↔ φ.Realize b)) (n : ℕ) :
    2 ^ n - 1 ≤ ρ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · by_contra hlt
    obtain ⟨M, _, _, a, b, hab, ha, hb⟩ := exists_nbhdIso_realize_loopReach hn (not_le.1 hlt)
    exact hb ((hρ n M a b (loopReach n) (quantifierRank_loopReach n).le hab).1 ha)

/-! #### Exactness of the Hanf locality rank `2 ^ (n - 1) - 1` -/

/-- `strictEdge` asserts `x₀ ≠ x₁ ∧ adj x₀ x₁` (quantifier rank `0`). -/
private def strictEdge : Language.graph.Formula (Fin 2) :=
  (Term.equal (Term.var 0) (Term.var 1)).not ⊓ adj.formula₂ (Term.var 0) (Term.var 1)

private theorem quantifierRank_strictEdge : quantifierRank strictEdge = 0 := by
  simp only [strictEdge, quantifierRank_inf, quantifierRank_not, Term.equal,
    quantifierRank_bdEqual, Relations.formula₂, Relations.formula,
    quantifierRank_relations_boundedFormula, max_self]

private theorem realize_strictEdge {M : Type*} [Language.graph.Structure M] (x y : M) :
    strictEdge.Realize ![x, y] ↔ x ≠ y ∧ RelMap adj ![x, y] := by
  fo_simp [strictEdge]

/-- Existential composition `∃ u, φ(u) ∧ ψ(u, x₀)` of a unary formula `φ` and a binary formula
`ψ`. -/
private def exStep1 {L : Language} (φ : L.Formula (Fin 1)) (ψ : L.Formula (Fin 2)) :
    L.Formula (Fin 1) :=
  (BoundedFormula.relabel (fun _ : Fin 1 => Sum.inr 0) φ ⊓
    BoundedFormula.relabel (fun i : Fin 2 => ![Sum.inr 0, Sum.inl 0] i) ψ).ex

private theorem quantifierRank_exStep1 {L : Language} (φ : L.Formula (Fin 1))
    (ψ : L.Formula (Fin 2)) :
    quantifierRank (exStep1 φ ψ) = max (quantifierRank φ) (quantifierRank ψ) + 1 := by
  simp only [exStep1, quantifierRank_ex, quantifierRank_inf, quantifierRank_relabel]

private theorem realize_exStep1 {L : Language} {M : Type*} [L.Structure M]
    (φ : L.Formula (Fin 1)) (ψ : L.Formula (Fin 2)) (z : M) :
    (exStep1 φ ψ).Realize ![z] ↔ ∃ u, φ.Realize ![u] ∧ ψ.Realize ![u, z] := by
  fo_simp [exStep1]
  exact exists_congr fun u => and_congr
    (boundedFormula_realize_iff_formula_realize _ (fun i => by fin_cases i; rfl) _)
    (boundedFormula_realize_iff_formula_realize _ (fun i => by fin_cases i <;> rfl) _)

/-- `fwdStrict k` has quantifier rank `k + 1` and states on a directed path with self-loops that a
self-loop occurs strictly before `x₀` within at most `2 ^ (k + 1) - 1` forward steps. -/
private def fwdStrict : ℕ → Language.graph.Formula (Fin 1)
  | 0 => exStep1 (loopReach 0) strictEdge
  | k + 1 => exStep1 (fwdStrict k) (distLE (k + 1))

private theorem quantifierRank_fwdStrict (k : ℕ) : quantifierRank (fwdStrict k) = k + 1 := by
  induction k with
  | zero =>
    simp only [fwdStrict, quantifierRank_exStep1, quantifierRank_loopReach,
      quantifierRank_strictEdge, max_self]
  | succ k ih =>
    simp only [fwdStrict, quantifierRank_exStep1, ih, quantifierRank_distLE, max_self]

private theorem realize_fwdStrict_zero {M : Type*} [Language.graph.Structure M] (z : M) :
    (fwdStrict 0).Realize ![z] ↔ ∃ u, (loopReach 0).Realize ![u] ∧ strictEdge.Realize ![u, z] :=
  realize_exStep1 (loopReach 0) strictEdge z

private theorem realize_fwdStrict_succ {M : Type*} [Language.graph.Structure M] (k : ℕ) (z : M) :
    (fwdStrict (k + 1)).Realize ![z] ↔
      ∃ w, (fwdStrict k).Realize ![w] ∧ (distLE (k + 1)).Realize ![w, z] :=
  realize_exStep1 (fwdStrict k) (distLE (k + 1)) z

/-- `twoLoopSentence k` has quantifier rank `k + 2` and asks for a midpoint `z` satisfying both
`fwdStrict k` and `loopReach (k + 1)`: on a directed path with self-loops, two distinct self-loops
within `2 ^ (k + 2) - 2` forward steps of one another. -/
private def twoLoopSentence (k : ℕ) : Language.graph.Sentence :=
  (BoundedFormula.relabel (fun _ : Fin 1 => Sum.inr 0) (fwdStrict k) ⊓
    BoundedFormula.relabel (fun _ : Fin 1 => Sum.inr 0) (loopReach (k + 1))).ex

private theorem quantifierRank_twoLoopSentence (k : ℕ) :
    quantifierRank (twoLoopSentence k) = k + 2 := by
  simp only [twoLoopSentence, quantifierRank_ex, quantifierRank_inf, quantifierRank_relabel,
    quantifierRank_fwdStrict, quantifierRank_loopReach, max_self]

private theorem realize_twoLoopSentence {M : Type*} [Language.graph.Structure M] (k : ℕ) :
    M ⊨ twoLoopSentence k ↔ ∃ z : M, (fwdStrict k).Realize ![z] ∧
      (loopReach (k + 1)).Realize ![z] := by
  fo_simp [twoLoopSentence, Sentence.Realize, Formula.Realize]
  exact exists_congr fun z => and_congr
    (boundedFormula_realize_iff_formula_realize _ (fun i => by fin_cases i; rfl) _)
    (boundedFormula_realize_iff_formula_realize _ (fun i => by fin_cases i; rfl) _)

/-- Loopless base edge relation of two disjoint directed paths on `Fin m ⊕ Fin m`. -/
private def dirSumBase {m : ℕ} : Fin m ⊕ Fin m → Fin m ⊕ Fin m → Prop
  | .inl x, .inl y => (x : ℕ) + 1 = (y : ℕ)
  | .inr x, .inr y => (x : ℕ) + 1 = (y : ℕ)
  | _, _ => False

/-- Two disjoint directed paths on `Fin m ⊕ Fin m`, augmented with self-loops on `S`. -/
private def dirSumPathRel {m : ℕ} (S : Fin m ⊕ Fin m → Prop) (u v : Fin m ⊕ Fin m) : Prop :=
  dirSumBase u v ∨ (u = v ∧ S u)

private theorem dirSumBase_swap {m : ℕ} (u v : Fin m ⊕ Fin m) :
    dirSumBase (Sum.swap u) (Sum.swap v) ↔ dirSumBase u v := by
  cases u <;> cases v <;> rfl

private theorem dirSumPathRel_swap {m : ℕ} (S : Fin m ⊕ Fin m → Prop) (u v : Fin m ⊕ Fin m) :
    dirSumPathRel (S ∘ Sum.swap) (Sum.swap u) (Sum.swap v) ↔ dirSumPathRel S u v := by
  cases u <;> cases v <;> simp [dirSumPathRel, dirSumBase]

private def dirSumPathSwap {m : ℕ} (S : Fin m ⊕ Fin m → Prop) :
    @Language.Equiv Language.graph (Fin m ⊕ Fin m) (Fin m ⊕ Fin m)
      (relStructure (dirSumPathRel S)) (relStructure (dirSumPathRel (S ∘ Sum.swap))) :=
  @Language.Equiv.mk Language.graph (Fin m ⊕ Fin m) (Fin m ⊕ Fin m)
    (relStructure (dirSumPathRel S)) (relStructure (dirSumPathRel (S ∘ Sum.swap)))
    (Equiv.sumComm (Fin m) (Fin m)) (fun f => isEmptyElim f) fun {n} R t => by
      cases R
      rw [@relMap_adj_relStructure (Fin m ⊕ Fin m) (dirSumPathRel (S ∘ Sum.swap))
          ((Equiv.sumComm (Fin m) (Fin m)).toFun ∘ t),
        @relMap_adj_relStructure (Fin m ⊕ Fin m) (dirSumPathRel S) t]
      exact dirSumPathRel_swap S (t 0) (t 1)

private theorem realize_dirSumPathRel_swap {m k : ℕ} (S : Fin m ⊕ Fin m → Prop)
    (φ : Language.graph.Formula (Fin k)) (v : Fin k → Fin m ⊕ Fin m) :
    (letI := relStructure (dirSumPathRel S); φ.Realize v) ↔
      (letI := relStructure (dirSumPathRel (S ∘ Sum.swap)); φ.Realize (Sum.swap ∘ v)) :=
  (@StrongHomClass.realize_formula Language.graph (Fin m ⊕ Fin m) (Fin m ⊕ Fin m)
    (relStructure (dirSumPathRel S)) (relStructure (dirSumPathRel (S ∘ Sum.swap)))
    (Fin k)
    (@Language.Equiv Language.graph (Fin m ⊕ Fin m) (Fin m ⊕ Fin m)
      (relStructure (dirSumPathRel S)) (relStructure (dirSumPathRel (S ∘ Sum.swap))))
    _ _ (dirSumPathSwap S) φ v).symm

private theorem gaifmanGraph_dirSumPathRel {m : ℕ} (S : Fin m ⊕ Fin m → Prop) :
    @gaifmanGraph Language.graph (Fin m ⊕ Fin m) (relStructure (dirSumPathRel S)) =
      SimpleGraph.pathGraph m ⊕g SimpleGraph.pathGraph m := by
  unfold dirSumPathRel
  rw [gaifmanGraph_or_eq_and]
  ext u v
  rcases u with x | x <;> rcases v with y | y <;>
    simp only [SimpleGraph.fromRel_adj, dirSumBase, SimpleGraph.sum_adj_inl,
      SimpleGraph.sum_adj_inr, SimpleGraph.pathGraph_adj, ne_eq, Sum.inl.injEq, Sum.inr.injEq,
      Fin.ext_iff] <;>
    first | omega | simp

private theorem realize_distLE_dirSumPathRel_inl {m : ℕ} (S : Fin m ⊕ Fin m → Prop) (k : ℕ) :
    ∀ (x : Fin m) (v : Fin m ⊕ Fin m),
      (letI := relStructure (dirSumPathRel S); (distLE k).Realize ![.inl x, v]) ↔
        match v with
        | .inl y => (x : ℕ) ≤ (y : ℕ) ∧ (y : ℕ) ≤ (x : ℕ) + 2 ^ k
        | .inr _ => False := by
  let := relStructure (dirSumPathRel S)
  induction k with
  | zero =>
    intro x v
    rw [realize_distLE_zero, relMap_relStructure]
    cases v with
    | inl y =>
      simp only [dirSumPathRel, dirSumBase, Sum.inl.injEq, Fin.ext_iff, pow_zero]
      omega
    | inr y =>
      simp only [dirSumPathRel, dirSumBase, reduceCtorEq, false_and, or_false]
  | succ k ih =>
    intro x v
    rw [realize_distLE_succ]
    simp only [Sum.exists, ih, false_and, exists_false, or_false]
    have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [pow_succ, mul_two]
    cases v with
    | inl y =>
      refine ⟨fun ⟨z, hz⟩ => by omega,
        fun ⟨hxy, hyx⟩ => ⟨⟨min (y : ℕ) ((x : ℕ) + 2 ^ k), by omega⟩, ?_⟩⟩
      dsimp only
      omega
    | inr _ => simp

private theorem realize_distLE_dirSumPathRel {m : ℕ} (S : Fin m ⊕ Fin m → Prop) (k : ℕ) :
    ∀ u v : Fin m ⊕ Fin m,
      (letI := relStructure (dirSumPathRel S); (distLE k).Realize ![u, v]) ↔
        match u, v with
        | .inl x, .inl y => (x : ℕ) ≤ (y : ℕ) ∧ (y : ℕ) ≤ (x : ℕ) + 2 ^ k
        | .inr x, .inr y => (x : ℕ) ≤ (y : ℕ) ∧ (y : ℕ) ≤ (x : ℕ) + 2 ^ k
        | _, _ => False := by
  rintro (x | x) v
  · cases v <;> exact realize_distLE_dirSumPathRel_inl S k x _
  · rw [realize_dirSumPathRel_swap S (distLE k) ![.inr x, v] ]
    have hcomp : Sum.swap ∘ ![.inr x, v] = ![.inl x, Sum.swap v] := by
      ext i; fin_cases i <;> rfl
    rw [hcomp, realize_distLE_dirSumPathRel_inl (S ∘ Sum.swap) k x (Sum.swap v)]
    cases v <;> rfl

private theorem realize_unary_dirSumPathRel {m : ℕ} (φ : Language.graph.Formula (Fin 1))
    (P : (Fin m ⊕ Fin m → Prop) → Fin m → Prop)
    (hinl : ∀ (S : Fin m ⊕ Fin m → Prop) (x : Fin m),
      (letI := relStructure (dirSumPathRel S);
        φ.Realize ![(Sum.inl x : Fin m ⊕ Fin m)]) ↔ P S x)
    (S : Fin m ⊕ Fin m → Prop) :
    ∀ u : Fin m ⊕ Fin m,
      (letI := relStructure (dirSumPathRel S); φ.Realize ![u]) ↔
        match u with
        | .inl x => P S x
        | .inr x => P (S ∘ Sum.swap) x := by
  rintro (x | x)
  · exact hinl S x
  · rw [realize_dirSumPathRel_swap S φ ![.inr x] ]
    have hcomp : Sum.swap ∘ ![(.inr x : Fin m ⊕ Fin m)] = ![.inl x] := by
      ext i; fin_cases i; rfl
    rw [hcomp]
    exact hinl (S ∘ Sum.swap) x

private theorem realize_loopReach_dirSumPathRel_inl {m : ℕ} (S : Fin m ⊕ Fin m → Prop) (n : ℕ) :
    ∀ x : Fin m,
      (letI := relStructure (dirSumPathRel S);
        (loopReach n).Realize ![(Sum.inl x : Fin m ⊕ Fin m)]) ↔
        ∃ y : Fin m, S (.inl y) ∧ (x : ℕ) ≤ (y : ℕ) ∧ (y : ℕ) ≤ (x : ℕ) + (2 ^ n - 1) := by
  let := relStructure (dirSumPathRel S)
  induction n with
  | zero =>
    intro x
    rw [realize_loopReach_zero, relMap_relStructure]
    simp only [dirSumPathRel, dirSumBase, Nat.add_eq_left, one_ne_zero, true_and, false_or,
      pow_zero, Nat.sub_self, add_zero]
    exact ⟨fun hx => ⟨x, hx, le_rfl, le_rfl⟩,
      fun ⟨y, hy, h1, h2⟩ => Fin.ext (le_antisymm h1 h2) ▸ hy⟩
  | succ k ih =>
    intro x
    rw [realize_loopReach_succ]
    simp only [realize_distLE_dirSumPathRel]
    have hsum := two_pow_add_pred_eq k
    constructor
    · rintro ⟨z | z, hxz, hz⟩
      · obtain ⟨y, hy, hzy⟩ := (ih z).1 hz
        exact ⟨y, hy, by omega, by omega⟩
      · exact False.elim hxz
    · rintro ⟨y, hy, hxy, hyx⟩
      refine ⟨.inl ⟨min (y : ℕ) ((x : ℕ) + 2 ^ k), by omega⟩, ?_, (ih _).2 ⟨y, hy, ?_⟩⟩ <;>
        (dsimp only; omega)

private theorem realize_loopReach_dirSumPathRel {m : ℕ} (S : Fin m ⊕ Fin m → Prop) (n : ℕ) :
    ∀ u : Fin m ⊕ Fin m,
      (letI := relStructure (dirSumPathRel S); (loopReach n).Realize ![u]) ↔
        match u with
        | .inl x => ∃ y : Fin m, S (.inl y) ∧ (x : ℕ) ≤ (y : ℕ) ∧ (y : ℕ) ≤ (x : ℕ) + (2 ^ n - 1)
        | .inr x => ∃ y : Fin m, S (.inr y) ∧ (x : ℕ) ≤ (y : ℕ) ∧
            (y : ℕ) ≤ (x : ℕ) + (2 ^ n - 1) :=
  realize_unary_dirSumPathRel (loopReach n)
    (fun S x => ∃ y : Fin m, S (.inl y) ∧ (x : ℕ) ≤ (y : ℕ) ∧ (y : ℕ) ≤ (x : ℕ) + (2 ^ n - 1))
    (fun S x => realize_loopReach_dirSumPathRel_inl S n x) S

private theorem realize_fwdStrict_dirSumPathRel_inl {m : ℕ} (S : Fin m ⊕ Fin m → Prop) (k : ℕ) :
    ∀ z : Fin m,
      (letI := relStructure (dirSumPathRel S);
        (fwdStrict k).Realize ![(Sum.inl z : Fin m ⊕ Fin m)]) ↔
        ∃ u : Fin m, S (.inl u) ∧ (u : ℕ) + 1 ≤ (z : ℕ) ∧
          (z : ℕ) ≤ (u : ℕ) + (2 ^ (k + 1) - 1) := by
  let := relStructure (dirSumPathRel S)
  induction k with
  | zero =>
    intro z
    rw [realize_fwdStrict_zero]
    simp only [Sum.exists, realize_loopReach_zero, realize_strictEdge, relMap_relStructure,
      dirSumPathRel, dirSumBase, Nat.add_eq_left, one_ne_zero, ne_eq, Sum.inl.injEq, Fin.ext_iff,
      reduceCtorEq, true_and, false_and, and_false, false_or, or_false, exists_false]
    refine exists_congr fun u => ⟨fun ⟨huS, hne, hadj⟩ => ?_, fun ⟨huS, h1, h2⟩ => ?_⟩
    · have := hadj.resolve_right fun h => hne h.1
      exact ⟨huS, by omega, by omega⟩
    · exact ⟨huS, by omega, .inl (by omega)⟩
  | succ k ih =>
    intro z
    rw [realize_fwdStrict_succ]
    simp only [realize_distLE_dirSumPathRel]
    have hsum := two_pow_add_pred_eq (k + 1)
    constructor
    · rintro ⟨v | v, hvF, hvz⟩
      · obtain ⟨u, huS, h1, h2⟩ := (ih v).1 hvF
        exact ⟨u, huS, by omega, by omega⟩
      · exact False.elim hvz
    · rintro ⟨u, huS, h1, h2⟩
      refine ⟨.inl ⟨min (z : ℕ) ((u : ℕ) + (2 ^ (k + 1) - 1)), by omega⟩,
        (ih _).2 ⟨u, huS, ?_, ?_⟩, ?_⟩ <;>
      · dsimp only
        have := @Nat.one_le_two_pow k
        rw [pow_succ] at *
        omega

private theorem realize_fwdStrict_dirSumPathRel {m : ℕ} (S : Fin m ⊕ Fin m → Prop) (k : ℕ) :
    ∀ w : Fin m ⊕ Fin m,
      (letI := relStructure (dirSumPathRel S); (fwdStrict k).Realize ![w]) ↔
        match w with
        | .inl z => ∃ u : Fin m, S (.inl u) ∧ (u : ℕ) + 1 ≤ (z : ℕ) ∧
            (z : ℕ) ≤ (u : ℕ) + (2 ^ (k + 1) - 1)
        | .inr z => ∃ u : Fin m, S (.inr u) ∧ (u : ℕ) + 1 ≤ (z : ℕ) ∧
            (z : ℕ) ≤ (u : ℕ) + (2 ^ (k + 1) - 1) :=
  realize_unary_dirSumPathRel (fwdStrict k)
    (fun S z => ∃ u : Fin m, S (.inl u) ∧ (u : ℕ) + 1 ≤ (z : ℕ) ∧
      (z : ℕ) ≤ (u : ℕ) + (2 ^ (k + 1) - 1))
    (fun S z => realize_fwdStrict_dirSumPathRel_inl S k z) S

private theorem exists_dirSumPath_hanfEquiv {k d : ℕ} (hd : d < 2 ^ (k + 1) - 1) :
    ∃ (m : ℕ) (_ : 0 < m) (S₁ S₂ : Fin m ⊕ Fin m → Prop),
      @HanfEquiv Language.graph (Fin m ⊕ Fin m) (Fin m ⊕ Fin m)
        (relStructure (dirSumPathRel S₁)) (relStructure (dirSumPathRel S₂))
        0 d Fin.elim0 Fin.elim0 ∧
      (letI := relStructure (dirSumPathRel S₁); (Fin m ⊕ Fin m) ⊨ twoLoopSentence k) ∧
      ¬ (letI := relStructure (dirSumPathRel S₂); (Fin m ⊕ Fin m) ⊨ twoLoopSentence k) := by
  have hk := @Nat.one_le_two_pow k
  have hk1 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ, mul_comm]
  have hk2 : 2 ^ (k + 2) = 4 * 2 ^ k := by rw [pow_succ, pow_succ]; omega
  set D := 2 ^ (k + 2) - 2
  have hD_2d : 2 * d + 2 ≤ D := by omega
  set m := D + 1
  let S₁ : Fin m ⊕ Fin m → Prop
    | .inl x => (x : ℕ) = 0 ∨ (x : ℕ) = D
    | .inr _ => False
  let S₂ : Fin m ⊕ Fin m → Prop
    | .inl x => (x : ℕ) = 0
    | .inr x => (x : ℕ) = D
  refine ⟨m, by omega, S₁, S₂, ?_, ?_, ?_⟩
  · -- `M ⇆_d N`: swap `.inl x ↔ .inr x` when `D ≤ x + d`, and keep fixed otherwise.
    let coord : Fin m ⊕ Fin m → Fin m := Sum.elim id id
    let fFun : Fin m ⊕ Fin m → Fin m ⊕ Fin m := fun c =>
      if D ≤ (coord c : ℕ) + d then Sum.swap c else c
    have hf_inv : Function.Involutive fFun := fun c => by
      have hcoord : coord (Sum.swap c) = coord c := by cases c <;> rfl
      by_cases h : D ≤ (coord c : ℕ) + d <;> simp [fFun, h, hcoord]
    let f : Fin m ⊕ Fin m ≃ Fin m ⊕ Fin m :=
      { toFun := fFun, invFun := fFun, left_inv := hf_inv, right_inv := hf_inv }
    refine (@hanfEquiv_zero_iff Language.graph _ _ (relStructure (dirSumPathRel S₁))
      (relStructure (dirSumPathRel S₂)) d _ _).2 ⟨f, fun c => ?_⟩
    have hcoord_le :
        ∀ u ∈ @ball Language.graph _ (relStructure (dirSumPathRel S₁)) 1 (fun _ => c) d,
          (coord u : ℕ) ≤ (coord c : ℕ) + d ∧ (coord c : ℕ) ≤ (coord u : ℕ) + d := by
      intro u hu
      rw [@mem_ball_const, gaifmanGraph_dirSumPathRel] at hu
      have hle := ((SimpleGraph.Hom.sumFold (SimpleGraph.pathGraph m)).edist_le c u).trans hu
      rw [SimpleGraph.Hom.sumFold_apply, SimpleGraph.Hom.sumFold_apply,
        SimpleGraph.edist_pathGraph, Nat.cast_le] at hle
      change (coord u : ℕ) - (coord c : ℕ) + ((coord c : ℕ) - (coord u : ℕ)) ≤ d at hle
      omega
    by_cases hswap : D ≤ (coord c : ℕ) + d
    · -- Near `D`: `f c = Sum.swap c`, and `Sum.swap` is the local isomorphism.
      rw [show f c = Sum.swap c from ite_eq_left hswap]
      refine @IsNbhdIso.nbhdIso Language.graph _ _ (relStructure (dirSumPathRel S₁))
        (relStructure (dirSumPathRel S₂)) 1 d _ _ _
        (isNbhdIso_or_eq_and c (Equiv.sumComm (Fin m) (Fin m)) dirSumBase_swap fun u hu => ?_)
      have hcu := hcoord_le u hu
      rcases u with y | y <;> dsimp only [coord, Sum.elim_inl, Sum.elim_inr, id_eq] at hcu hswap
      · simp only [Equiv.sumComm_apply, Sum.swap_inl, S₁, S₂]
        exact ⟨Or.inr, fun hy => hy.resolve_left (by omega)⟩
      · simp only [Equiv.sumComm_apply, Sum.swap_inr, S₁, S₂]
        exact iff_of_false (by omega) False.elim
    · -- Away from `D`: `f c = c`, and `id` is the local isomorphism.
      rw [show f c = c from ite_eq_right hswap]
      refine @IsNbhdIso.nbhdIso Language.graph _ _ (relStructure (dirSumPathRel S₁))
        (relStructure (dirSumPathRel S₂)) 1 d _ _ _
        (isNbhdIso_or_eq_and c (Equiv.refl (Fin m ⊕ Fin m)) (fun _ _ => Iff.rfl) fun u hu => ?_)
      have hcu := hcoord_le u hu
      rcases u with y | y <;> dsimp only [coord, Sum.elim_inl, Sum.elim_inr, id_eq] at hcu hswap
      · simp only [Equiv.refl_apply, S₁, S₂]
        exact ⟨Or.inl, fun hy => hy.resolve_right (by omega)⟩
      · simp only [Equiv.refl_apply, S₁, S₂]
        exact iff_of_false (by omega) False.elim
  · -- `M ⊨ twoLoopSentence k`, witnessed at the midpoint `2 ^ (k + 1) - 1`.
    let _ := relStructure (dirSumPathRel S₁)
    rw [realize_twoLoopSentence]
    have hD_split : D = (2 ^ (k + 1) - 1) + (2 ^ (k + 1) - 1) := by omega
    refine ⟨.inl ⟨2 ^ (k + 1) - 1, by omega⟩, ?_, ?_⟩
    · rw [realize_fwdStrict_dirSumPathRel]
      exact ⟨⟨0, by omega⟩, .inl rfl, by dsimp only; omega, by simp⟩
    · rw [realize_loopReach_dirSumPathRel]
      exact ⟨⟨D, by omega⟩, .inr rfl, by dsimp only; omega, by dsimp only; omega⟩
  · -- `¬ N ⊨ twoLoopSentence k`, since each component of `N` has only one self-loop.
    let _ := relStructure (dirSumPathRel S₂)
    rw [realize_twoLoopSentence]
    rintro ⟨z, hzF, hzB⟩
    rw [realize_fwdStrict_dirSumPathRel] at hzF
    rw [realize_loopReach_dirSumPathRel] at hzB
    rcases z with z | z <;>
    · obtain ⟨u, hu, hu1, _⟩ := hzF
      obtain ⟨y, hy, hy1, _⟩ := hzB
      dsimp only [S₂] at hu hy
      omega

/-- **Exactness of the Hanf locality rank `2 ^ (n - 1) - 1` for sentences**
([Libkin, Exercise 4.11][Libkin2004]): for every `n ≥ 2` and `d < 2 ^ (n - 1) - 1`, there exist
finite nonempty `Language.graph`-structures `M` and `N` and a sentence `σ` of quantifier rank `n`
such that `M ⇆_d N` while `M ⊨ σ` and `¬ N ⊨ σ`. -/
theorem exists_hanfEquiv_sentence_not_realize_iff {n d : ℕ} (hn : 2 ≤ n)
    (hd : d < 2 ^ (n - 1) - 1) :
    ∃ (M N : Type) (_ : Finite M) (_ : Nonempty M)
      (_ : Language.graph.Structure M) (_ : Language.graph.Structure N)
      (σ : Language.graph.Sentence),
      quantifierRank σ = n ∧
      HanfEquiv Language.graph d (Fin.elim0 : Fin 0 → M) (Fin.elim0 : Fin 0 → N) ∧
      M ⊨ σ ∧ ¬ N ⊨ σ := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  obtain ⟨m, hm, S₁, S₂, hHanf, hM₁, hM₂⟩ := exists_dirSumPath_hanfEquiv hd
  exact ⟨Fin m ⊕ Fin m, Fin m ⊕ Fin m, inferInstance, ⟨.inl ⟨0, hm⟩⟩,
    relStructure (dirSumPathRel S₁), relStructure (dirSumPathRel S₂),
    twoLoopSentence k, quantifierRank_twoLoopSentence k, hHanf, hM₁, hM₂⟩

/-! #### Lifting the Hanf sentence lower bound to `1`-tuples via an isolated vertex -/

/-- Extend a binary relation on `V` to `Option V` by leaving `none` loopless and isolated. -/
private def optRel {V : Type*} (R : V → V → Prop) : Option V → Option V → Prop
  | some x, some y => R x y
  | _, _ => False

private theorem gaifmanGraph_optRel_adj {V : Type*} (R : V → V → Prop) (u v : Option V) :
    (@gaifmanGraph Language.graph (Option V) (relStructure (optRel R))).Adj u v ↔
      match u, v with
      | some x, some y => (@gaifmanGraph Language.graph V (relStructure R)).Adj x y
      | _, _ => False := by
  rw [gaifmanGraph_relStructure, gaifmanGraph_relStructure, SimpleGraph.fromRel_adj]
  rcases u with _ | x <;> rcases v with _ | y <;>
    simp [optRel, SimpleGraph.fromRel_adj]

private theorem edist_optRel_none_some {V : Type*} (R : V → V → Prop) (x : V) :
    (@gaifmanGraph Language.graph (Option V)
      (relStructure (optRel R))).edist none (some x) = ⊤ := by
  refine SimpleGraph.edist_eq_top_of_not_reachable fun ⟨p⟩ => ?_
  cases p with
  | @cons _ _ _ h _ => exact (gaifmanGraph_optRel_adj R _ _).1 h

private theorem edist_optRel_some_some {V : Type*} (R : V → V → Prop) (x y : V) :
    (@gaifmanGraph Language.graph (Option V) (relStructure (optRel R))).edist (some x) (some y) =
      (@gaifmanGraph Language.graph V (relStructure R)).edist x y := by
  let G := @gaifmanGraph Language.graph V (relStructure R)
  let GO := @gaifmanGraph Language.graph (Option V) (relStructure (optRel R))
  let emb : G →g GO :=
    { toFun := some
      map_rel' := fun {a b} h => (gaifmanGraph_optRel_adj R (some a) (some b)).2 h }
  let proj : GO →g G :=
    { toFun := fun u => u.getD x
      map_rel' := fun {u v} h => by
        rw [show GO = _ from rfl, gaifmanGraph_optRel_adj] at h
        rcases u with _ | a <;> rcases v with _ | b <;> first | exact h.elim | exact h }
  exact le_antisymm (emb.edist_le x y) (proj.edist_le (some x) (some y))

private theorem isNbhdIso_optRel_none {V₁ V₂ : Type*} (R₁ : V₁ → V₁ → Prop)
    (R₂ : V₂ → V₂ → Prop) (d : ℕ) {k : ℕ} :
    @IsNbhdIso Language.graph (Option V₁) (Option V₂) (relStructure (optRel R₁))
      (relStructure (optRel R₂)) k d (fun _ => none) (fun _ => none) (fun _ => none) := by
  have hball₁ : ∀ u : Option V₁,
      u ∈ @ball Language.graph (Option V₁) (relStructure (optRel R₁)) k (fun _ => none) d →
        u = none := by
    intro u hu
    obtain ⟨_, hx⟩ := (@mem_ball Language.graph (Option V₁) (relStructure (optRel R₁))
      k (fun _ => none) d u).1 hu
    cases u with
    | none => rfl
    | some x =>
      rw [edist_optRel_none_some] at hx
      exact absurd hx (not_le.2 (ENat.natCast_lt_top d))
  have hball₂ : ∀ v : Option V₂,
      v ∈ @ball Language.graph (Option V₂) (relStructure (optRel R₂)) k (fun _ => none) d ↔
        ∃ _ : Fin k, v = none := by
    intro v
    rw [@mem_ball Language.graph (Option V₂) (relStructure (optRel R₂))]
    refine exists_congr fun _ => ?_
    cases v with
    | none => simp
    | some y =>
      rw [edist_optRel_none_some]
      exact iff_of_false (not_le.2 (ENat.natCast_lt_top d)) (fun h => by cases h)
  refine @IsNbhdIso.mk Language.graph (Option V₁) (Option V₂) (relStructure (optRel R₁))
    (relStructure (optRel R₂)) k d (fun _ => none) (fun _ => none) (fun _ => none)
    ⟨fun u hu => ?_, fun u hu v hv _ => (hball₁ u hu).trans (hball₁ v hv).symm,
      fun v hv => ?_⟩ (fun _ => rfl) (fun {l} R t ht => ?_)
  · obtain ⟨i, _⟩ := (@mem_ball Language.graph (Option V₁) (relStructure (optRel R₁))
      k (fun _ => none) d u).1 hu
    exact (hball₂ none).2 ⟨i, rfl⟩
  · obtain ⟨i, rfl⟩ := (hball₂ v).1 hv
    exact ⟨none, @mem_ball_self Language.graph (Option V₁) (relStructure (optRel R₁))
      k (fun _ => none) d i, rfl⟩
  · cases R
    rw [relMap_adj_relStructure (optRel R₂) ((fun _ => none) ∘ t),
      relMap_adj_relStructure (optRel R₁) t]
    dsimp only [Function.comp_apply]
    rw [hball₁ (t 0) (ht 0)]
    simp [optRel]

private theorem mem_ball_optRel_some {V : Type*} (R : V → V → Prop) (d : ℕ) (c : V)
    (u : Option V) :
    u ∈ @ball Language.graph (Option V) (relStructure (optRel R)) 1 (fun _ => some c) d ↔
      ∃ x ∈ @ball Language.graph V (relStructure R) 1 (fun _ => c) d, u = some x := by
  rw [@mem_ball_const Language.graph (Option V) (relStructure (optRel R))]
  cases u with
  | none =>
    rw [SimpleGraph.edist_comm, edist_optRel_none_some]
    exact iff_of_false (not_le.2 (ENat.natCast_lt_top d)) fun ⟨_, _, heq⟩ => by cases heq
  | some x =>
    rw [edist_optRel_some_some]
    exact ⟨fun hx => ⟨x, (@mem_ball_const Language.graph V (relStructure R) d c x).2 hx, rfl⟩,
      fun ⟨x', hx', heq⟩ => Option.some.inj heq ▸
        (@mem_ball_const Language.graph V (relStructure R) d c x').1 hx'⟩

private theorem nbhdIso_optRel_some {V₁ V₂ : Type*} {R₁ : V₁ → V₁ → Prop}
    {R₂ : V₂ → V₂ → Prop} {d : ℕ} {c₁ : V₁} {c₂ : V₂}
    (hc : @NbhdIso Language.graph V₁ V₂ (relStructure R₁) (relStructure R₂) 1 d
      (fun _ => c₁) (fun _ => c₂)) :
    @NbhdIso Language.graph (Option V₁) (Option V₂) (relStructure (optRel R₁))
      (relStructure (optRel R₂)) 1 d (fun _ => some c₁) (fun _ => some c₂) := by
  obtain ⟨h, ⟨hmaps, hinj, hsurj⟩, htuple, hrel⟩ :=
    (@nbhdIso_iff Language.graph V₁ V₂ (relStructure R₁) (relStructure R₂)
      1 d (fun _ => c₁) (fun _ => c₂)).1 hc
  refine @IsNbhdIso.nbhdIso Language.graph (Option V₁) (Option V₂)
    (relStructure (optRel R₁)) (relStructure (optRel R₂)) 1 d
    (fun _ => some c₁) (fun _ => some c₂) (Option.map h)
    (@IsNbhdIso.mk Language.graph (Option V₁) (Option V₂)
      (relStructure (optRel R₁)) (relStructure (optRel R₂)) 1 d
      (fun _ => some c₁) (fun _ => some c₂) (Option.map h)
      ⟨fun u hu => ?_, fun u hu v hv huv => ?_, fun v hv => ?_⟩
      (fun i => congrArg some (htuple i)) (fun {l} R t ht => ?_))
  · obtain ⟨x, hx, rfl⟩ := (mem_ball_optRel_some R₁ d c₁ u).1 hu
    exact (mem_ball_optRel_some R₂ d c₂ (some (h x))).2 ⟨h x, hmaps hx, rfl⟩
  · obtain ⟨x₁, hx₁, rfl⟩ := (mem_ball_optRel_some R₁ d c₁ u).1 hu
    obtain ⟨x₂, hx₂, rfl⟩ := (mem_ball_optRel_some R₁ d c₁ v).1 hv
    exact congrArg some (hinj hx₁ hx₂ (Option.some.inj huv))
  · obtain ⟨y, hy, rfl⟩ := (mem_ball_optRel_some R₂ d c₂ v).1 hv
    obtain ⟨x, hx, rfl⟩ := hsurj hy
    exact ⟨some x, (mem_ball_optRel_some R₁ d c₁ (some x)).2 ⟨x, hx, rfl⟩, rfl⟩
  · cases R
    obtain ⟨x₀, hx₀, hx₀_eq⟩ := (mem_ball_optRel_some R₁ d c₁ (t 0)).1 (ht 0)
    obtain ⟨x₁, hx₁, hx₁_eq⟩ := (mem_ball_optRel_some R₁ d c₁ (t 1)).1 (ht 1)
    have hiff := hrel adj ![x₀, x₁] (fun i => by fin_cases i <;> assumption)
    rw [relMap_adj_relStructure R₂ (h ∘ ![x₀, x₁]), relMap_adj_relStructure R₁ ![x₀, x₁] ] at hiff
    rw [relMap_adj_relStructure (optRel R₂) (Option.map h ∘ t),
      relMap_adj_relStructure (optRel R₁) t]
    dsimp only [Function.comp_apply] at hiff ⊢
    rw [hx₀_eq, hx₁_eq]
    exact hiff

private theorem hanfEquiv_optRel_none {V₁ V₂ : Type*} {R₁ : V₁ → V₁ → Prop}
    {R₂ : V₂ → V₂ → Prop} {d : ℕ}
    (H : @HanfEquiv Language.graph V₁ V₂ (relStructure R₁) (relStructure R₂) 0 d
      Fin.elim0 Fin.elim0) :
    @HanfEquiv Language.graph (Option V₁) (Option V₂) (relStructure (optRel R₁))
      (relStructure (optRel R₂)) 1 d (fun _ => none) (fun _ => none) := by
  obtain ⟨f, hf⟩ := (@hanfEquiv_zero_iff Language.graph V₁ V₂ (relStructure R₁)
    (relStructure R₂) d Fin.elim0 Fin.elim0).1 H
  refine (@hanfEquiv_iff Language.graph (Option V₁) (Option V₂) (relStructure (optRel R₁))
    (relStructure (optRel R₂)) 1 d (fun _ => none) (fun _ => none)).2 ⟨Equiv.optionCongr f,
      fun w => ?_⟩
  cases w with
  | none =>
    rw [Equiv.optionCongr_apply, Option.map_none,
      show (Fin.snoc (fun _ : Fin 1 => (none : Option V₁)) none : Fin 2 → Option V₁) =
        fun _ => none from funext (Fin.forall_fin_two.2 ⟨rfl, rfl⟩),
      show (Fin.snoc (fun _ : Fin 1 => (none : Option V₂)) none : Fin 2 → Option V₂) =
        fun _ => none from funext (Fin.forall_fin_two.2 ⟨rfl, rfl⟩)]
    exact @IsNbhdIso.nbhdIso Language.graph (Option V₁) (Option V₂)
      (relStructure (optRel R₁)) (relStructure (optRel R₂)) 2 d _ _ _
      (isNbhdIso_optRel_none R₁ R₂ d)
  | some c =>
    obtain ⟨h₂, H₂⟩ := (@nbhdIso_iff Language.graph (Option V₁) (Option V₂)
      (relStructure (optRel R₁)) (relStructure (optRel R₂)) 1 d _ _).1 (nbhdIso_optRel_some (hf c))
    exact (@IsNbhdIso.snoc Language.graph (Option V₁) (Option V₂)
      (relStructure (optRel R₁)) (relStructure (optRel R₂)) 1 d
      (fun _ => none) (fun _ => none) _ _ _ _ (isNbhdIso_optRel_none R₁ R₂ d (k := 1)) H₂)
      (fun _ => by rw [edist_optRel_none_some]; exact ENat.natCast_lt_top _)
      (fun _ => by rw [edist_optRel_none_some]; exact ENat.natCast_lt_top _)

private theorem realize_distLE_optRel {V : Type*} (R : V → V → Prop) (k : ℕ) :
    ∀ u v : Option V,
      (letI := relStructure (optRel R); (distLE k).Realize ![u, v]) ↔
        match u, v with
        | some x, some y => (letI := relStructure R; (distLE k).Realize ![x, y])
        | none, none => True
        | _, _ => False := by
  induction k with
  | zero =>
    rintro (_ | x) (_ | y) <;>
      simp [@realize_distLE_zero _ (relStructure (optRel R)),
        @realize_distLE_zero _ (relStructure R), relMap_relStructure, optRel]
  | succ k ih =>
    rintro (_ | x) (_ | y) <;>
      simp [@realize_distLE_succ _ (relStructure (optRel R)),
        @realize_distLE_succ _ (relStructure R), Option.exists, ih]

private theorem realize_loopReach_optRel {V : Type*} (R : V → V → Prop) (n : ℕ) :
    ∀ u : Option V,
      (letI := relStructure (optRel R); (loopReach n).Realize ![u]) ↔
        match u with
        | some x => (letI := relStructure R; (loopReach n).Realize ![x])
        | none => False := by
  induction n with
  | zero =>
    rintro (_ | x) <;>
      simp [@realize_loopReach_zero _ (relStructure (optRel R)),
        @realize_loopReach_zero _ (relStructure R), relMap_relStructure, optRel]
  | succ k ih =>
    rintro (_ | x) <;>
      simp [@realize_loopReach_succ _ (relStructure (optRel R)),
        @realize_loopReach_succ _ (relStructure R), Option.exists, realize_distLE_optRel, ih]

private theorem realize_fwdStrict_optRel {V : Type*} (R : V → V → Prop) (k : ℕ) :
    ∀ w : Option V,
      (letI := relStructure (optRel R); (fwdStrict k).Realize ![w]) ↔
        match w with
        | some z => (letI := relStructure R; (fwdStrict k).Realize ![z])
        | none => False := by
  induction k with
  | zero =>
    rintro (_ | z) <;>
      simp [@realize_fwdStrict_zero _ (relStructure (optRel R)),
        @realize_fwdStrict_zero _ (relStructure R),
        @realize_strictEdge _ (relStructure (optRel R)),
        @realize_strictEdge _ (relStructure R),
        Option.exists, realize_loopReach_optRel, relMap_relStructure, optRel]
  | succ k ih =>
    rintro (_ | z) <;>
      simp [@realize_fwdStrict_succ _ (relStructure (optRel R)),
        @realize_fwdStrict_succ _ (relStructure R), Option.exists, ih, realize_distLE_optRel]

private theorem realize_twoLoopSentence_optRel {V : Type*} (R : V → V → Prop) (k : ℕ) :
    (letI := relStructure (optRel R); Option V ⊨ twoLoopSentence k) ↔
      (letI := relStructure R; V ⊨ twoLoopSentence k) := by
  simp [@realize_twoLoopSentence _ (relStructure (optRel R)),
    @realize_twoLoopSentence _ (relStructure R), Option.exists,
    realize_fwdStrict_optRel, realize_loopReach_optRel]

/-- **Exactness of the Hanf locality rank `2 ^ (n - 1) - 1` for `1`-tuples**
([Libkin, Exercise 4.11][Libkin2004]): for every `n ≥ 2` and `d < 2 ^ (n - 1) - 1`, there exist
finite nonempty `Language.graph`-structures `M` and `N`, `1`-tuples `a` and `b`, and a formula `φ`
of quantifier rank `n` such that `(M, a) ⇆_d (N, b)` while `φ` holds of `a` and fails of `b`. -/
theorem exists_hanfEquiv_formula_not_realize_iff {n d : ℕ} (hn : 2 ≤ n)
    (hd : d < 2 ^ (n - 1) - 1) :
    ∃ (M N : Type) (_ : Finite M) (_ : Nonempty M)
      (_ : Language.graph.Structure M) (_ : Language.graph.Structure N)
      (a : Fin 1 → M) (b : Fin 1 → N) (φ : Language.graph.Formula (Fin 1)),
      quantifierRank φ = n ∧
      HanfEquiv Language.graph d a b ∧
      φ.Realize a ∧ ¬ φ.Realize b := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  obtain ⟨m, _, S₁, S₂, hHanf, hM₁, hM₂⟩ := exists_dirSumPath_hanfEquiv hd
  refine ⟨Option (Fin m ⊕ Fin m), Option (Fin m ⊕ Fin m), inferInstance, ⟨none⟩,
    relStructure (optRel (dirSumPathRel S₁)), relStructure (optRel (dirSumPathRel S₂)),
    fun _ => none, fun _ => none, Formula.relabel Empty.elim (twoLoopSentence k),
    ?_, hanfEquiv_optRel_none hHanf, ?_, ?_⟩
  · rw [quantifierRank_formula_relabel, quantifierRank_twoLoopSentence]
  · rw [@Formula.realize_relabel _ _ (relStructure (optRel (dirSumPathRel S₁))),
      Subsingleton.elim ((fun _ : Fin 1 => none) ∘ Empty.elim) (@default _ Unique.instInhabited)]
    simpa only [Sentence.Realize] using (realize_twoLoopSentence_optRel (dirSumPathRel S₁) k).2 hM₁
  · rw [@Formula.realize_relabel _ _ (relStructure (optRel (dirSumPathRel S₂))),
      Subsingleton.elim ((fun _ : Fin 1 => none) ∘ Empty.elim) (@default _ Unique.instInhabited)]
    exact mt (fun h => (realize_twoLoopSentence_optRel (dirSumPathRel S₂) k).1
      (by simpa only [Sentence.Realize] using h)) hM₂

/-- **Optimality of the Hanf locality rank `2 ^ (n - 1) - 1` for sentences**
([Libkin, Exercise 4.11][Libkin2004]): any radius function `ρ` giving Hanf locality on finite
nonempty `Language.graph`-structures for sentences of quantifier rank at most `n` satisfies
`2 ^ (n - 1) - 1 ≤ ρ n` for every `n`. -/
theorem two_pow_pred_sub_one_le_of_hanf_sentence_radius {ρ : ℕ → ℕ}
    (hρ : ∀ (n : ℕ) (M N : Type) [Finite M] [Nonempty M]
      [Language.graph.Structure M] [Language.graph.Structure N]
      (σ : Language.graph.Sentence), quantifierRank σ ≤ n →
      HanfEquiv Language.graph (ρ n) (Fin.elim0 : Fin 0 → M) (Fin.elim0 : Fin 0 → N) →
      (M ⊨ σ ↔ N ⊨ σ)) (n : ℕ) :
    2 ^ (n - 1) - 1 ≤ ρ n := by
  by_cases hn : 2 ≤ n
  · by_contra hlt
    obtain ⟨M, N, _, _, _, _, σ, hσ, hMN, hM, hN⟩ :=
      exists_hanfEquiv_sentence_not_realize_iff hn (not_le.1 hlt)
    exact hN ((hρ n M N σ hσ.le hMN).1 hM)
  · rcases (by omega : n = 0 ∨ n = 1) with rfl | rfl <;> simp

/-- **Optimality of the Hanf locality rank `2 ^ (n - 1) - 1` for `1`-tuples**
([Libkin, Exercise 4.11][Libkin2004]): any radius function `ρ` giving Hanf locality on finite
nonempty `Language.graph`-structures for `1`-tuples and formulas of quantifier rank at most `n`
satisfies `2 ^ (n - 1) - 1 ≤ ρ n` for every `n`. -/
theorem two_pow_pred_sub_one_le_of_hanf_radius {ρ : ℕ → ℕ}
    (hρ : ∀ (n : ℕ) (M N : Type) [Finite M] [Nonempty M]
      [Language.graph.Structure M] [Language.graph.Structure N]
      (a : Fin 1 → M) (b : Fin 1 → N) (φ : Language.graph.Formula (Fin 1)),
      quantifierRank φ ≤ n → HanfEquiv Language.graph (ρ n) a b →
      (φ.Realize a ↔ φ.Realize b)) (n : ℕ) :
    2 ^ (n - 1) - 1 ≤ ρ n := by
  by_cases hn : 2 ≤ n
  · by_contra hlt
    obtain ⟨M, N, _, _, _, _, a, b, φ, hφ, hab, ha, hb⟩ :=
      exists_hanfEquiv_formula_not_realize_iff hn (not_le.1 hlt)
    exact hb ((hρ n M N a b φ hφ.le hab).1 ha)
  · rcases (by omega : n = 0 ∨ n = 1) with rfl | rfl <;> simp

end LowerBounds

end Cslib.Logic.FO.Locality
