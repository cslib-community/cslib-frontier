/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.CuckooHashing.HashFamily
public import CslibFrontier.Languages.Probabilistic.RandomOracle
public import CslibFrontier.Probability.KWiseIndependent.DoubleTabulation
public import CslibFrontier.Probability.KWiseIndependent.Trinomial
public import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Foundations.Data.Nat.Power
import CslibFrontier.Probability.KWiseIndependent.DoubleTabulation.Parameters
import CslibFrontier.Probability.KWiseIndependent.Restriction
import CslibFrontier.Probability.PMF.UniformBound
import CslibFrontier.Tactic.UniformRelabel

/-!
# Pagh–Rodler Cuckoo Graph Dichotomy and Walk Tail Bounds for Highly Independent Hash Pairs

This module formalizes the cuckoo graph walk dichotomy and tail-bound analysis of Rasmus Pagh and
Flemming Friche Rodler, *"Cuckoo hashing"* (author-hosted journal manuscript dated 8 December 2003,
<https://www.rasmuspagh.net/papers/cuckoo-jour.pdf>, published in *Journal of Algorithms*
51(2):122–144, 2004) [PaghRodler2004], Section 2.3 ("Analysis", manuscript pp. 6–10; Lemma 1 on
manuscript p. 7, Eqs. (1)–(3) on manuscript p. 9, and the rehash analysis on manuscript p. 10). For
every capacity `n_max : ℕ`, it proves that any independent pair of `(2 * MaxLoop + 2)`-wise
independent hash functions into sub-tables of size `32 * max n_max 4 ≤ m` with eviction cap
`maxEvictions n_max ≤ MaxLoop ≤ m` satisfies `IsCuckooHashPair` with constants `C_walk = 2` and
`C_reh = 3`.

## Scope and Word-RAM specialization

This module establishes `IsCuckooHashPair` for uniform random hash pairs
(`isCuckooHashPair_uniform`, connected to lazy random-oracle evaluation via
`uniform_interpret_eq_lazy_hashPair`), for explicit `(2 * MaxLoop + 2)`-wise independent
polynomial hash pairs (`isCuckooHashPair_trinomialPolyHash`), for Mikkel Thorup's double-tabulation
hash family (`isCuckooHashPair_doubleTabHash`). It imports no Word-RAM modules. The concrete
regime-switched hash pair is connected to this analysis by
`CslibFrontier.DataStructure.Dictionary.WordRAM.CuckooHashing.Analysis`, whose
`isCuckooHashPair_provableFamily` discharges `IsCuckooHashFamily` (`C_walk = 3`, `C_reh = 4`)
for every `n_max : ℕ` whenever `U ≤ max n_max 4 ^ c_exp` and `32 * max n_max 4 ≤ 2 ^ M`.

## Source statements, assumptions, and notation mapping

In Pagh and Rodler [PaghRodler2004] (8 December 2003 manuscript,
<https://www.rasmuspagh.net/papers/cuckoo-jour.pdf>):
* **Table size and eviction limit (Section 2, manuscript pp. 3–4; Section 2.3, manuscript p. 10)**:
  Two hash tables `T₁, T₂` each consist of `r` words holding a set `S` of `n = |S|` keys (p. 3),
  *"assuming `r ≥ (1 + ε) n` for some constant `ε > 0`"* (pp. 3–4), with
  `MaxLoop = ⌈3 log_{1+ε} r⌉` (p. 10). The Lean theorems below assume the stronger linear-space
  condition `32 * max n_max 4 ≤ m` (`S.card ≤ n_max`) and eviction cap
  `maxEvictions n_max = 6 * (Nat.clog 2 (max n_max 2) + 2) ≤ MaxLoop ≤ m`.
* **Hash-function assumption (Section 1.1, Definition 1, manuscript p. 3; Section 2.1, manuscript
  p. 5; Section 2.3, manuscript p. 7)**: Definition 1 (p. 3) defines a family `{h_i}_{i ∈ I}`,
  `h_i : U → R`, as `(c, k)`-universal if *"for any `k` distinct elements `x₁, …, x_k ∈ U`, any
  `y₁, …, y_k ∈ R`, and uniformly random `i ∈ I`,
  `Pr[h_i(x₁) = y₁, …, h_i(x_k) = y_k] ≤ c / |R|^k`"*.
  Section 2.1 (p. 5) invokes Siegel's construction for *"a hash function family that, when
  restricted to any set of `r²` keys, is `(1, n^δ)`-universal, for some constant `δ > 0`, with
  probability `1 - O(1/n²)`"*, so for `MaxLoop < n^δ` *"with high probability the family will be
  `(1, MaxLoop)`-universal. This means that `h₁` and `h₂` will act like truly random functions on
  any set of keys processed during the insertion loop"* (and Section 2.3, situation (1) on
  manuscript p. 7 separately bounds the event that *"The hash function family used is not
  `(1, MaxLoop)`-universal when restricted to the set of keys in the dictionary (including the key
  being inserted)"* by `O(1/n²)`). The Lean theorems below assume the stronger hypothesis that `h₁`
  and `h₂` are independent families each satisfying `IsKWiseIndependentHash (2 * MaxLoop + 2)` on
  the full universe `Fin U → Fin m` (exact `(1, 2 * MaxLoop + 2)`-universality with zero failure
  probability).
* **Lemma 1 (Section 2.3, manuscript p. 7)**: *"Suppose that the insertion procedure does not enter
  a closed loop. Then for any prefix `x₁, x₂, …, x_p` of the sequence of nestless keys, there must
  be a subsequence of at least `p / 3` consecutive keys without repetitions, starting with an
  occurrence of the key `x₁`, i.e., the key being inserted."* In Lean,
  `cuckooWalk_dichotomy_bicyclic` and `cuckooWalk_dichotomy` prove that any non-terminating
  `r`-round (`p = 2 * r` half-step) eviction walk from `u ∉ S` produces either a simple alternating
  path of length `ℓ = (2 * r + 2) / 3` starting at `u` (`HasAltPath`, Case B) or a bicyclic prefix
  of `L + 1` distinct keys (`2 ≤ L < 2 * r`) satisfying `L + 2` hash-collision equations
  (`HasBicyclicPrefix` and `HasExcessSubset`, Case A).
* **Closed-loop and path tail bounds, expected rounds, and rehash bounds (Section 2.3, manuscript
  pp. 7–10; Eqs. (1)–(3) on p. 9)**: For closed loops (situation (2), introduced on p. 7 and
  bounded on p. 9 following Sanders and Vöcking), the manuscript counts configurations of `v ≤ l`
  distinct nestless keys by `v³ r^{v-1} n^{v-1}` (*"`v²` possible values for `i` and `j`, `v`
  possible positions for `x_l`, `r^{v-1}` possible choices of cells, and `n^{v-1}` possible choices
  of keys other than `x₁`"*), each occurring with probability at most `r^{-2v}`, summing to
  `O(1 / n²)` (p. 9). For simple alternating paths (situation (3), introduced on pp. 7–8 and
  bounded in Eqs. (1)–(2) on p. 9), a sequence of `v = ⌈(2t - 1) / 3⌉` distinct keys (`ℓ = v - 1`
  steps) occurs with probability at most `2 * (n / r)^{v - 1}` (p. 9). Summing over rounds gives
  expected walk length `O(1)` (Eq. (3), p. 9; `expected_walk_le` with `C_walk = 2`) and bounds the
  per-insertion and full-set rehash probabilities (p. 10; `step_rehash_prob_le` with `C_reh = 3`
  and `rehash_prob_le_half`).
* **Original adaptations**:
  - `GoodForSet` (requiring `pureReplay` to succeed for *all* duplicate-free insertion orders
    `ks ⊆ S` simultaneously) and `cuckooWalkRounds` (taking the supremum of `evictRounds` over
    *all* `ValidPlacement h₁ h₂ S tbl` and slot indices) are strengthened definitions from
    `CslibFrontier/DataStructure/Dictionary/CuckooHashing/Basic.lean`;
    because neither `HasBicyclicPrefix` / `HasExcessSubset` nor `HasAltPath`
    depends on `tbl` or the insertion order `ks`, the walk dichotomy bounds both uniformly over all
    valid placements and insertion orders.
  - In place of enumerating `r^{v-1}` cell tuples as in `v³ r^{v-1} n^{v-1}` on p. 9, both Case A
    (`HasBicyclicPrefix`) and Case B (`HasAltPath`) are bounded via an original elementary fresh-key
    equation-chain seed-counting argument (`ValidEqChain`), which counts index triples `(p, s, j)`
    (`≤ (L + 1)³` for `v = L + 1`) and key tuples (`≤ S.card^L`) and uses `(2 * MaxLoop + 2)`-wise
    independence directly on `L + 2` fresh-key collision equations (probability `m^{-(L+2)}`). The
    set-level excess-`≥ 1` subgraph predicate `HasExcessSubset` and reduction
    `hasBicyclicPrefix_imp_hasExcessSubset` are likewise original adaptations.

## Main definitions

* `Cslib.DataStructure.Dictionary.CuckooHashing.HasAltPath`: Case B of the walk dichotomy —
  existence of a simple alternating path of length `ℓ` starting at `u` with subsequent keys in `S`.
* `Cslib.DataStructure.Dictionary.CuckooHashing.HasBicyclicPrefix`: Case A of the walk dichotomy —
  existence of a walk prefix of `L + 1` distinct keys (`u` and `L` keys in `S`) closing two cycles
  across `L + 2` independent hash-collision equations.
* `Cslib.DataStructure.Dictionary.CuckooHashing.HasExcessSubset`: set-level Case A predicate —
  existence of a subset `K ⊆ insert u S` containing `u` with `3 ≤ K.card ≤ maxCard` and
  `|(K.image h₁)| + |(K.image h₂)| + 1 ≤ K.card`.

## Main results

* `Cslib.DataStructure.Dictionary.CuckooHashing.hasAltPath_iff`,
  `Cslib.DataStructure.Dictionary.CuckooHashing.hasBicyclicPrefix_iff`: plain characterizations of
  `HasAltPath` and `HasBicyclicPrefix` directly in terms of injective key sequences and alternating
  / cycle-closing hash collisions, without internal equation-chain helpers.
* `Cslib.DataStructure.Dictionary.CuckooHashing.hasBicyclicPrefix_imp_hasExcessSubset`: any
  bicyclic prefix of length `L ∈ [2, 2 * r)` yields an excess-`≥ 1` subset `K ⊆ insert u S` of size
  `3 ≤ K.card ≤ 2 * r`.
* `Cslib.DataStructure.Dictionary.CuckooHashing.cuckooWalk_dichotomy_bicyclic`,
  `Cslib.DataStructure.Dictionary.CuckooHashing.cuckooWalk_dichotomy`,
  `Cslib.DataStructure.Dictionary.CuckooHashing.lt_cuckooWalkRounds_imp_dichotomy`: Pagh and Rodler
  [PaghRodler2004], Section 2.3, Lemma 1 (manuscript p. 7) — any non-terminating `r`-round cuckoo
  walk from `u ∉ S` produces either `HasAltPath` of length `(2 * r + 2) / 3` or `HasBicyclicPrefix`
  of length `2 ≤ L < 2 * r` (and `HasExcessSubset` of size `≤ 2 * r`).
* `Cslib.DataStructure.Dictionary.CuckooHashing.isCuckooHashPair_of_kWiseIndependent`: Pagh and
  Rodler [PaghRodler2004], Section 2.3 (Lemma 1, manuscript p. 7; Eq. (3), manuscript p. 9; rehash
  analysis, manuscript p. 10) — any independent pair of `(2 * MaxLoop + 2)`-wise independent
  hash families satisfies `IsCuckooHashPair` (`C_walk = 2`, `C_reh = 3`) under
  `32 * max n_max 4 ≤ m` and `maxEvictions n_max ≤ MaxLoop ≤ m`.
* `Cslib.DataStructure.Dictionary.CuckooHashing.isCuckooHashPair_of_whp_kWiseIndependent`: black-box
  conditioning bridge showing that any two-level hash family whose top-level seed yields a
  `(2 * MaxLoop + 2)`-wise independent bottom-level family with failure probability at most
  `1 / (2 * max n_max 1 * max MaxLoop 1)` satisfies `IsCuckooHashPair` (`C_walk = 3`, `C_reh = 4`).
* `Cslib.DataStructure.Dictionary.CuckooHashing.isCuckooHashPair_doubleTabHash`:
  `IsCuckooHashPair` for Mikkel Thorup's double-tabulation hash family [Thorup2013], under the
  displayed independence, table-size, eviction-cap, and code-count bounds.
* `Cslib.DataStructure.Dictionary.CuckooHashing.isCuckooHashPair_trinomialPolyHash`,
  `Cslib.DataStructure.Dictionary.CuckooHashing.isCuckooHashPair_uniform`,
  `Cslib.DataStructure.Dictionary.CuckooHashing.uniform_interpret_eq_lazy_hashPair`:
  specializations to
  explicit trinomial-field polynomial hashing and uniform random hash pairs, plus lazy random-oracle
  equivalence via `Cslib.RandomOracle.uniform_interpret_eq_lazy`.

## References

* [R. Pagh and F. F. Rodler, "Cuckoo hashing"][PaghRodler2004] (8 December 2003 author manuscript,
  <https://www.rasmuspagh.net/papers/cuckoo-jour.pdf>, Section 2.3, "Analysis", pp. 6–10: Lemma 1,
  p. 7; Eqs. (1)–(3), p. 9; rehash analysis, p. 10).
* [M. Thorup, *Simple Tabulation, Fast Expanders, Double Tabulation,
  and High Independence*][Thorup2013]
* [M. Mitzenmacher and E. Upfal, *Probability and Computing*, 2nd ed.][MitzenmacherUpfal2017]
* [M. N. Wegman and J. L. Carter, *New hash functions and their use in authentication and set
  equality*][WegmanCarter1981]
-/

public section

namespace Cslib.DataStructure.Dictionary.CuckooHashing

open Cslib.Probability
open scoped BigOperators ENNReal Finset

/-! ## Section 1: Fresh-key equation chains and `k`-wise independent counting -/

/-- Conjunction of hash-collision equations `f w = f v` for each pair `(w, v)` in `eqs`. -/
private def EquationChain {U m : ℕ} (f : Fin U → Fin m) : List (Fin U × Fin U) → Prop
  | [] => True
  | (w, v) :: rest => f w = f v ∧ EquationChain f rest

private instance {U m : ℕ} (f : Fin U → Fin m) (eqs : List (Fin U × Fin U)) :
    Decidable (EquationChain f eqs) := by
  induction eqs with
  | nil => exact isTrue trivial
  | cons p rest ih =>
    rcases p with ⟨w, v⟩
    exact @instDecidableAnd _ _ (inferInstanceAs (Decidable (f w = f v))) ih

/-- Finset of all keys appearing in a list of collision equations `eqs`. -/
private def eqChainKeys {U : ℕ} : List (Fin U × Fin U) → Finset (Fin U)
  | [] => ∅
  | (w, v) :: rest => insert w (insert v (eqChainKeys rest))

/-- An equation chain is valid (`ValidEqChain`) if at each head equation `(w, v) :: rest`, the
constrained key `w` is distinct from `v` and does not appear anywhere in `rest`. -/
private def ValidEqChain {U : ℕ} : List (Fin U × Fin U) → Prop
  | [] => True
  | (w, v) :: rest => w ≠ v ∧ w ∉ eqChainKeys rest ∧ ValidEqChain rest

private instance {U : ℕ} (eqs : List (Fin U × Fin U)) : Decidable (ValidEqChain eqs) := by
  induction eqs with
  | nil => exact isTrue trivial
  | cons p rest ih =>
    rcases p with ⟨w, v⟩
    exact @instDecidableAnd _ _ (inferInstanceAs (Decidable (w ≠ v)))
      (@instDecidableAnd _ _ (inferInstanceAs (Decidable (w ∉ eqChainKeys rest))) ih)

private theorem equationChain_congr_of_eqOn {U m : ℕ} {f₁ f₂ : Fin U → Fin m}
    {eqs : List (Fin U × Fin U)} {T : Finset (Fin U)}
    (hsub : eqChainKeys eqs ⊆ T) (heq : ∀ x ∈ T, f₁ x = f₂ x) :
    EquationChain f₁ eqs ↔ EquationChain f₂ eqs := by
  induction eqs with
  | nil => rfl
  | cons p rest ih =>
    rcases p with ⟨w, v⟩
    simp only [eqChainKeys, Finset.insert_subset_iff] at hsub
    rcases hsub with ⟨hw, hv, hrest⟩
    simp only [EquationChain, heq w hw, heq v hv, ih hrest]

/-- Extending `y : T → Fin m` to `insert w T` by assigning `w` the value `y ⟨v, hv⟩`. -/
private def extendRestrict {U m : ℕ} {T : Finset (Fin U)} (w : Fin U) {v : Fin U} (hv : v ∈ T)
    (y : T → Fin m) (x : ↥(insert w T)) : Fin m :=
  if hxw : x.val = w then y ⟨v, hv⟩
  else y ⟨x.val, Finset.mem_of_mem_insert_of_ne x.property hxw⟩

private theorem restrict_insert_eq_extendRestrict_iff {U m : ℕ} {T : Finset (Fin U)} {w v : Fin U}
    (hw : w ∉ T) (hv : v ∈ T) (f : Fin U → Fin m) (y : T → Fin m) :
    (insert w T).restrict f = extendRestrict w hv y ↔ f w = f v ∧ T.restrict f = y := by
  constructor
  · intro h
    have hT : T.restrict f = y := funext fun ⟨x, hx⟩ => by
      simpa [Finset.restrict, extendRestrict, show x ≠ w from fun h' => hw (h' ▸ hx)] using
        congrFun h ⟨x, Finset.mem_insert_of_mem hx⟩
    exact ⟨by simpa [Finset.restrict, extendRestrict, ← hT] using
      congrFun h ⟨w, Finset.mem_insert_self w T⟩, hT⟩
  · rintro ⟨hwv, rfl⟩
    funext ⟨x, hx⟩
    simp only [Finset.restrict, extendRestrict]
    split_ifs with hxw
    · exact hxw ▸ hwv
    · rfl

/-- For each fixed assignment `y : T → Fin m`, adding a fresh key `w ∉ T` constrained by
`h θ w = h θ v` (`v ∈ T`) divides the surviving seed count by `m`. -/
private theorem card_filter_eq_and_restrict_eq {Θ : Type*} [Fintype Θ] {U m k : ℕ} (hm : 0 < m)
    {h : Θ → Fin U → Fin m} (hh : IsKWiseIndependentHash k h)
    {T : Finset (Fin U)} {w v : Fin U} (hw : w ∉ T) (hv : v ∈ T)
    (hcard : #T + 1 ≤ k) (y : T → Fin m) :
    m * #{θ : Θ | h θ w = h θ v ∧ T.restrict (h θ) = y} =
      #{θ : Θ | T.restrict (h θ) = y} := by
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have hcard_ins : #(insert w T) = #T + 1 := Finset.card_insert_of_notMem hw
  have h1 := hh.card_filter_restrict_eq (hcard_ins.le.trans hcard) (extendRestrict w hv y)
  have h2 := hh.card_filter_restrict_eq (by omega : #T ≤ k) y
  simp only [Fintype.card_fin, restrict_insert_eq_extendRestrict_iff hw hv, hcard_ins, pow_succ,
    mul_assoc] at h1 h2
  exact Nat.eq_of_mul_eq_mul_left (Nat.pow_pos hm) (h1.trans h2.symm)

/-- **Single-Equation Elimination Lemma**: if `w ∉ T`, `v ∈ T`, `#T + 1 ≤ k`, and `P` depends only
on `T.restrict`, then requiring `h θ w = h θ v` multiplies the surviving seed count by `1 / m`. -/
private theorem card_filter_eq_of_notMem {Θ : Type*} [Fintype Θ] {U m k : ℕ} (hm : 0 < m)
    {h : Θ → Fin U → Fin m} (hh : IsKWiseIndependentHash k h)
    {T : Finset (Fin U)} {w v : Fin U} (hw : w ∉ T) (hv : v ∈ T) (hcard : #T + 1 ≤ k)
    (P : (T → Fin m) → Prop) [DecidablePred P] :
    m * #{θ : Θ | h θ w = h θ v ∧ P (T.restrict (h θ))} =
      #{θ : Θ | P (T.restrict (h θ))} := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := fun θ => T.restrict (h θ)) (t := {y | P y})
      (by simp [Set.MapsTo]),
    Finset.card_eq_sum_card_fiberwise (f := fun θ => T.restrict (h θ)) (t := {y | P y})
      (by simp [Set.MapsTo]), Finset.mul_sum]
  refine Finset.sum_congr rfl fun y hy => ?_
  have (θ : Θ) : P (T.restrict (h θ)) ∧ T.restrict (h θ) = y ↔ T.restrict (h θ) = y :=
    ⟨And.right, fun e => ⟨e ▸ (Finset.mem_filter.mp hy).2, e⟩⟩
  simpa only [Finset.filter_filter, and_assoc, this] using
    card_filter_eq_and_restrict_eq hm hh hw hv hcard y

/-- **Exact seed count for any valid equation chain**: if `ValidEqChain eqs` holds and `eqs`
mentions at most `k` distinct keys, then `m ^ eqs.length` times the number of seeds satisfying
`EquationChain (h θ) eqs` equals `Fintype.card Θ`. -/
private theorem card_filter_equationChain_eq {Θ : Type*} [Fintype Θ] {U m k : ℕ} (hm : 0 < m)
    {h : Θ → Fin U → Fin m} (hh : IsKWiseIndependentHash k h) :
    ∀ {eqs : List (Fin U × Fin U)}, ValidEqChain eqs → #(eqChainKeys eqs) ≤ k →
      m ^ eqs.length * #{θ : Θ | EquationChain (h θ) eqs} = Fintype.card Θ
  | [], _, _ => by
    rw [Finset.filter_true_of_mem (p := fun θ => EquationChain (h θ) []) fun _ _ => trivial]
    simp
  | (w, v) :: rest, ⟨hwv, hwnot, hvalid_rest⟩, hcard => by
    let T : Finset (Fin U) := insert v (eqChainKeys rest)
    have hw_not_T : w ∉ T := by simp [T, hwv, hwnot]
    have hT_le : #T + 1 ≤ k := Finset.card_insert_of_notMem hw_not_T ▸ hcard
    have hrest_sub : eqChainKeys rest ⊆ T := Finset.subset_insert v _
    have hstep := card_filter_eq_of_notMem hm hh hw_not_T (Finset.mem_insert_self v _) hT_le
      fun y => EquationChain (fun x => if hx : x ∈ T then y ⟨x, hx⟩ else ⟨0, hm⟩) rest
    have hP (θ : Θ) : EquationChain
        (fun x => if hx : x ∈ T then T.restrict (h θ) ⟨x, hx⟩ else ⟨0, hm⟩) rest ↔
        EquationChain (h θ) rest :=
      equationChain_congr_of_eqOn hrest_sub fun x hx => by simp [Finset.restrict, hx]
    simp only [hP] at hstep
    rw [← card_filter_equationChain_eq hm hh hvalid_rest
      ((Finset.card_le_card hrest_sub).trans (by omega)), ← hstep, List.length_cons, pow_succ,
      mul_assoc]
    congr!

/-! ## Section 1B: Index-level equation chains for alternating paths and bicyclic prefixes -/

/-- Index-level equation chain on `Fin N`: at each `(a, b) :: rest`, `a ≠ b` and `a` does not
appear anywhere in `rest`. -/
private def ValidIdxChain {N : ℕ} : List (Fin N × Fin N) → Prop
  | [] => True
  | (a, b) :: rest => a ≠ b ∧ (∀ p ∈ rest, a ≠ p.1 ∧ a ≠ p.2) ∧ ValidIdxChain rest

/-- Map an index-level equation chain on `Fin N` through `g : Fin N → Fin U`. -/
private def mapIdxChain {N U : ℕ} (g : Fin N → Fin U) (eqs : List (Fin N × Fin N)) :
    List (Fin U × Fin U) :=
  eqs.map fun p => (g p.1, g p.2)

@[simp]
private theorem length_mapIdxChain {N U : ℕ} (g : Fin N → Fin U) (eqs : List (Fin N × Fin N)) :
    (mapIdxChain g eqs).length = eqs.length :=
  List.length_map _

private theorem mem_eqChainKeys_mapIdxChain {N U : ℕ} {g : Fin N → Fin U}
    {eqs : List (Fin N × Fin N)} {x : Fin U} (hx : x ∈ eqChainKeys (mapIdxChain g eqs)) :
    ∃ a : Fin N, (∃ p ∈ eqs, a = p.1 ∨ a = p.2) ∧ g a = x := by
  induction eqs with
  | nil => simp [mapIdxChain, eqChainKeys] at hx
  | cons p rest ih =>
    simp only [mapIdxChain, List.map_cons, eqChainKeys, Finset.mem_insert] at hx ih
    grind

private theorem eqChainKeys_mapIdxChain_subset {N U : ℕ} (g : Fin N → Fin U)
    (eqs : List (Fin N × Fin N)) : eqChainKeys (mapIdxChain g eqs) ⊆ Finset.univ.image g :=
  fun x hx => by
    obtain ⟨a, _, rfl⟩ := mem_eqChainKeys_mapIdxChain hx
    exact Finset.mem_image_of_mem g (Finset.mem_univ a)

private theorem validEqChain_mapIdxChain {N U : ℕ} {g : Fin N → Fin U} (hg : Function.Injective g)
    {eqs : List (Fin N × Fin N)} (hvalid : ValidIdxChain eqs) :
    ValidEqChain (mapIdxChain g eqs) := by
  induction eqs with
  | nil => trivial
  | cons p rest ih =>
    rcases p with ⟨a, b⟩
    rcases hvalid with ⟨hab, hnot, hrest⟩
    refine ⟨fun h => hab (hg h), fun hmem => ?_, ih hrest⟩
    obtain ⟨c, ⟨q, hq, rfl | rfl⟩, hgc⟩ := mem_eqChainKeys_mapIdxChain hmem
    · exact (hnot q hq).1 (hg hgc).symm
    · exact (hnot q hq).2 (hg hgc).symm

private theorem card_eqChainKeys_mapIdxChain_le {N U : ℕ} (g : Fin N → Fin U)
    (eqs : List (Fin N × Fin N)) :
    #(eqChainKeys (mapIdxChain g eqs)) ≤ N :=
  (Finset.card_le_card (eqChainKeys_mapIdxChain_subset g eqs)).trans
    (Finset.card_image_le.trans (by simp))

/-- Product-space seed count on `Θ₁ × Θ₂` for a pair of valid index chains of total length `n`
mapped through an injective key tuple `y : Fin N → Fin U` with `N ≤ k`. -/
private theorem card_filter_prod_equationChain_eq {Θ₁ Θ₂ : Type*} [Fintype Θ₁] [Fintype Θ₂]
    {U m k N n : ℕ} (hm : 0 < m)
    {h₁ : Θ₁ → Fin U → Fin m} {h₂ : Θ₂ → Fin U → Fin m}
    (hh₁ : IsKWiseIndependentHash k h₁) (hh₂ : IsKWiseIndependentHash k h₂) (hNk : N ≤ k)
    {y : Fin N → Fin U} (hy : Function.Injective y)
    {chains : List (Fin N × Fin N) × List (Fin N × Fin N)}
    (hvalid : ValidIdxChain chains.1 ∧ ValidIdxChain chains.2)
    (hlen : chains.1.length + chains.2.length = n) :
    m ^ n * #{θ : Θ₁ × Θ₂ | EquationChain (h₁ θ.1) (mapIdxChain y chains.1) ∧
      EquationChain (h₂ θ.2) (mapIdxChain y chains.2)} = Fintype.card (Θ₁ × Θ₂) := by
  rw [Fintype.card_prod,
    ← card_filter_equationChain_eq hm hh₁ (validEqChain_mapIdxChain hy hvalid.1)
      ((card_eqChainKeys_mapIdxChain_le y _).trans hNk),
    ← card_filter_equationChain_eq hm hh₂ (validEqChain_mapIdxChain hy hvalid.2)
      ((card_eqChainKeys_mapIdxChain_le y _).trans hNk),
    length_mapIdxChain, length_mapIdxChain, mul_mul_mul_comm, ← pow_add, hlen,
    ← Finset.card_product]
  congr 2
  ext ⟨θ₁, θ₂⟩
  simp

/-- Prepend a pair `q` to the first or second list according to `tab`. -/
private def prependToTable {α : Type*} (tab : Bool) (q : α) (chains : List α × List α) :
    List α × List α :=
  if tab then (chains.1, q :: chains.2) else (q :: chains.1, chains.2)

private theorem mem_prependToTable_iff {α : Type*} (tab₁ tab₂ : Bool) (x q : α)
    (chains : List α × List α) :
    q ∈ (if tab₂ then (prependToTable tab₁ x chains).2 else (prependToTable tab₁ x chains).1) ↔
      (q = x ∧ tab₁ = tab₂) ∨ q ∈ (if tab₂ then chains.2 else chains.1) := by
  unfold prependToTable
  cases tab₁ <;> cases tab₂ <;> simp

private theorem length_prependToTable {α : Type*} (tab : Bool) (q : α) (chains : List α × List α) :
    (prependToTable tab q chains).1.length + (prependToTable tab q chains).2.length =
      chains.1.length + chains.2.length + 1 := by
  unfold prependToTable
  cases tab <;> simp <;> omega

private theorem validIdxChain_prependToTable {N : ℕ} (tab : Bool) (a b : Fin N)
    {chains : List (Fin N × Fin N) × List (Fin N × Fin N)}
    (hvalid : ValidIdxChain chains.1 ∧ ValidIdxChain chains.2)
    (hab : a ≠ b)
    (hnot : ∀ q ∈ (if tab then chains.2 else chains.1), a ≠ q.1 ∧ a ≠ q.2) :
    ValidIdxChain (prependToTable tab (a, b) chains).1 ∧
    ValidIdxChain (prependToTable tab (a, b) chains).2 := by
  rcases hvalid with ⟨hv1, hv2⟩
  unfold prependToTable
  cases tab
  · exact ⟨⟨hab, hnot, hv1⟩, hv2⟩
  · exact ⟨hv1, ⟨hab, hnot, hv2⟩⟩

private theorem equationChain_prependToTable_iff {U m L : ℕ} (h₁ h₂ : Fin U → Fin m) (tab : Bool)
    (q : Fin (L + 1) × Fin (L + 1)) (y : Fin (L + 1) → Fin U)
    (chains : List (Fin (L + 1) × Fin (L + 1)) × List (Fin (L + 1) × Fin (L + 1))) :
    (EquationChain h₁ (mapIdxChain y (prependToTable tab q chains).1) ∧
      EquationChain h₂ (mapIdxChain y (prependToTable tab q chains).2)) ↔
      (if tab then h₂ (y q.1) = h₂ (y q.2) else h₁ (y q.1) = h₁ (y q.2)) ∧
        (EquationChain h₁ (mapIdxChain y chains.1) ∧
          EquationChain h₂ (mapIdxChain y chains.2)) := by
  unfold prependToTable mapIdxChain
  cases tab <;> simp [EquationChain, and_assoc, and_left_comm]

/-- Predecessor index at fresh step `i` (`0 ≤ i < L`) in a walk whose first cycle closes at `p`:
step `i = p` starts the second path from `0` (`u`), while every other step `i` continues from
`i`. -/
private def stepPred (p i : ℕ) : ℕ :=
  if i = p then 0 else i

/-- Sub-table polarity (`false` for `T₁`/`h₁`, `true` for `T₂`/`h₂`) of fresh step `i` when the
first cycle closes at `p` and the initial step uses polarity `b`. -/
private def stepTable (b : Bool) (p i : ℕ) : Bool :=
  if i < p then (i % 2 == 1) != b else ((i - p + 1) % 2 == 1) != b

/-- Build the pair of index-level equation chains `(eqs₁, eqs₂)` on `Fin (L + 1)` for the first
`m ≤ L` fresh steps. -/
private def buildFreshChains (L : ℕ) (b : Bool) (p : ℕ) :
    (m : ℕ) → m ≤ L → List (Fin (L + 1) × Fin (L + 1)) × List (Fin (L + 1) × Fin (L + 1))
  | 0, _ => ([], [])
  | i + 1, hi =>
    let prev := buildFreshChains L b p i (by omega)
    let pair : Fin (L + 1) × Fin (L + 1) :=
      (⟨i + 1, by omega⟩, ⟨stepPred p i, by unfold stepPred; split_ifs <;> omega⟩)
    if stepTable b p i then (prev.1, pair :: prev.2) else (pair :: prev.1, prev.2)

private theorem buildFreshChains_succ (L : ℕ) (b : Bool) (p i : ℕ) (hi : i + 1 ≤ L) :
    buildFreshChains L b p (i + 1) hi = prependToTable (stepTable b p i)
      (⟨i + 1, by omega⟩, ⟨stepPred p i, by unfold stepPred; split_ifs <;> omega⟩)
      (buildFreshChains L b p i (by omega)) :=
  rfl

private theorem length_buildFreshChains (L : ℕ) (b : Bool) (p : ℕ) :
    ∀ (m : ℕ) (hm : m ≤ L),
      (buildFreshChains L b p m hm).1.length + (buildFreshChains L b p m hm).2.length = m
  | 0, _ => rfl
  | i + 1, hi => by
    rw [buildFreshChains_succ, length_prependToTable, length_buildFreshChains L b p i]

/-- Every pair in the `tab`-side chain of `buildFreshChains L b p m` is a fresh step
`(i + 1, stepPred p i)` with `i < m` and `stepTable b p i = tab`. -/
private theorem mem_buildFreshChains (L : ℕ) (b : Bool) (p : ℕ) (tab : Bool) :
    ∀ (m : ℕ) (hm : m ≤ L) (q : Fin (L + 1) × Fin (L + 1)),
      q ∈ (if tab then (buildFreshChains L b p m hm).2 else (buildFreshChains L b p m hm).1) →
      1 ≤ q.1.val ∧ q.1.val ≤ m ∧ q.2.val = stepPred p (q.1.val - 1) ∧
        stepTable b p (q.1.val - 1) = tab
  | 0, _, q, hq => by cases tab <;> simp [buildFreshChains] at hq
  | i + 1, hi, q, hq => by
    rw [buildFreshChains_succ, mem_prependToTable_iff] at hq
    rcases hq with ⟨rfl, rfl⟩ | hq
    · exact ⟨Nat.le_add_left 1 i, le_rfl, rfl, rfl⟩
    · obtain ⟨h1, h2, h3, h4⟩ := mem_buildFreshChains L b p tab i (by omega) q hq
      exact ⟨h1, by omega, h3, h4⟩

private theorem validIdxChain_buildFreshChains (L : ℕ) (b : Bool) (p : ℕ) :
    ∀ (m : ℕ) (hm : m ≤ L),
      ValidIdxChain (buildFreshChains L b p m hm).1 ∧
      ValidIdxChain (buildFreshChains L b p m hm).2
  | 0, _ => ⟨trivial, trivial⟩
  | i + 1, hi => by
    rw [buildFreshChains_succ]
    refine validIdxChain_prependToTable _ _ _ (validIdxChain_buildFreshChains L b p i (by omega))
      (by grind [stepPred]) fun q hq => ?_
    obtain ⟨h1, h2, h3, _⟩ := mem_buildFreshChains L b p _ i (by omega) q hq
    grind [stepPred]

/-- Index-level equation chains for a simple alternating path of length `ℓ` starting with
polarity `b`. -/
private def altPathChains (ℓ : ℕ) (b : Bool) :
    List (Fin (ℓ + 1) × Fin (ℓ + 1)) × List (Fin (ℓ + 1) × Fin (ℓ + 1)) :=
  buildFreshChains ℓ b (ℓ + 1) ℓ le_rfl

private theorem validIdxChain_altPathChains (ℓ : ℕ) (b : Bool) :
    ValidIdxChain (altPathChains ℓ b).1 ∧ ValidIdxChain (altPathChains ℓ b).2 :=
  validIdxChain_buildFreshChains ℓ b (ℓ + 1) ℓ le_rfl

private theorem length_altPathChains (ℓ : ℕ) (b : Bool) :
    (altPathChains ℓ b).1.length + (altPathChains ℓ b).2.length = ℓ :=
  length_buildFreshChains ℓ b (ℓ + 1) ℓ le_rfl

private theorem equationChain_buildFreshChains_iff {U m : ℕ} (h₁ h₂ : Fin U → Fin m)
    (L : ℕ) (b : Bool) (p : ℕ) (y : Fin (L + 1) → Fin U) :
    ∀ (k : ℕ) (hk : k ≤ L),
      (EquationChain h₁ (mapIdxChain y (buildFreshChains L b p k hk).1) ∧
        EquationChain h₂ (mapIdxChain y (buildFreshChains L b p k hk).2)) ↔
      ∀ i < k, ∀ (hi : i < L),
        if stepTable b p i then
          h₂ (y ⟨i + 1, by omega⟩) =
            h₂ (y ⟨stepPred p i, by unfold stepPred; split_ifs <;> omega⟩)
        else
          h₁ (y ⟨i + 1, by omega⟩) =
            h₁ (y ⟨stepPred p i, by unfold stepPred; split_ifs <;> omega⟩)
  | 0, _ => by
    simp [buildFreshChains, mapIdxChain, EquationChain]
  | i + 1, hi => by
    rw [buildFreshChains_succ, equationChain_prependToTable_iff,
      equationChain_buildFreshChains_iff h₁ h₂ L b p y i (by omega)]
    refine ⟨fun ⟨h, ih⟩ j hj hjL => ?_,
      fun h => ⟨h i (by omega) (by omega), fun j hj => h j (by omega)⟩⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    exacts [ih j hj hjL, h]

/-- **Case B (`HasAltPath`)**: there exists a simple alternating path of length `ℓ` starting at `u`
with all subsequent keys in `S`. -/
def HasAltPath {U m : ℕ} (h₁ h₂ : Fin U → Fin m) (S : Finset (Fin U)) (u : Fin U) (ℓ : ℕ) :
    Prop :=
  ∃ (b : Bool) (y : Fin (ℓ + 1) → Fin U),
    Function.Injective y ∧ y 0 = u ∧ (∀ i : Fin ℓ, y i.succ ∈ S) ∧
    EquationChain h₁ (mapIdxChain y (altPathChains ℓ b).1) ∧
    EquationChain h₂ (mapIdxChain y (altPathChains ℓ b).2)

/-- Plain characterization of `HasAltPath` without internal equation-chain helpers: `HasAltPath`
holds iff there exist an initial table polarity `b : Bool` and an injective sequence
`y : Fin (ℓ + 1) → Fin U` starting at `y 0 = u` with `y i.succ ∈ S` whose consecutive keys collide
alternately under `h₁` (`false`) and `h₂` (`true`). -/
theorem hasAltPath_iff {U m : ℕ} (h₁ h₂ : Fin U → Fin m) (S : Finset (Fin U)) (u : Fin U)
    (ℓ : ℕ) :
    HasAltPath h₁ h₂ S u ℓ ↔
      ∃ (b : Bool) (y : Fin (ℓ + 1) → Fin U),
        Function.Injective y ∧ y 0 = u ∧ (∀ i : Fin ℓ, y i.succ ∈ S) ∧
        ∀ i : Fin ℓ,
          if (i.val % 2 == 1) != b then h₂ (y i.succ) = h₂ (y i.castSucc)
          else h₁ (y i.succ) = h₁ (y i.castSucc) := by
  unfold HasAltPath altPathChains
  refine exists_congr fun b => exists_congr fun y => and_congr_right fun _ =>
    and_congr_right fun _ => and_congr_right fun _ => ?_
  rw [equationChain_buildFreshChains_iff h₁ h₂ ℓ b (ℓ + 1) y ℓ le_rfl]
  refine ⟨fun h ⟨i, hi⟩ => ?_, fun h i hi _ => ?_⟩
  · simpa [stepTable, stepPred, Nat.lt_succ_of_lt hi, (Nat.lt_succ_of_lt hi).ne] using h i hi hi
  · simpa [stepTable, stepPred, Nat.lt_succ_of_lt hi, (Nat.lt_succ_of_lt hi).ne] using h ⟨i, hi⟩

instance {U m : ℕ} (h₁ h₂ : Fin U → Fin m) (S : Finset (Fin U)) (u : Fin U) (ℓ : ℕ) :
    Decidable (HasAltPath h₁ h₂ S u ℓ) :=
  decidable_of_iff' _ (hasAltPath_iff h₁ h₂ S u ℓ)

/-- Validity condition on index triple `(p, s, j)` for a bicyclic walk prefix of `L` keys in `S`. -/
private def ValidBicyclicIdx (L : ℕ) (p s j : Fin (L + 1)) : Prop :=
  2 ≤ p.val ∧ s.val < p.val ∧ s.val % 2 = p.val % 2 ∧
    (if p.val = L then 1 ≤ j.val ∧ j.val < L else j.val < L)

private instance (L : ℕ) (p s j : Fin (L + 1)) : Decidable (ValidBicyclicIdx L p s j) := by
  unfold ValidBicyclicIdx
  infer_instance

/-- Index-level equation chains for a bicyclic walk prefix of `L` keys with parameters `(p, s, j)`.
-/
private def bicyclicChains (L : ℕ) (p s j : Fin (L + 1)) :
    List (Fin (L + 1) × Fin (L + 1)) × List (Fin (L + 1) × Fin (L + 1)) :=
  let base := buildFreshChains L false p.val L le_rfl
  let c1 := prependToTable (p.val % 2 == 1) (p, s) base
  let endIdx : Fin (L + 1) := ⟨if p.val = L then 0 else L, by split_ifs <;> omega⟩
  prependToTable ((L - p.val + 1) % 2 == 1) (endIdx, j) c1

private theorem length_bicyclicChains (L : ℕ) (p s j : Fin (L + 1)) :
    (bicyclicChains L p s j).1.length + (bicyclicChains L p s j).2.length = L + 2 := by
  unfold bicyclicChains
  dsimp only
  rw [length_prependToTable, length_prependToTable, length_buildFreshChains]

private theorem validIdxChain_bicyclicChains {L : ℕ} {p s j : Fin (L + 1)}
    (hidx : ValidBicyclicIdx L p s j) :
    ValidIdxChain (bicyclicChains L p s j).1 ∧ ValidIdxChain (bicyclicChains L p s j).2 := by
  obtain ⟨hp2, hslt, hspar, hj⟩ := hidx
  have hpL : p.val ≤ L := Nat.lt_succ_iff.mp p.isLt
  refine validIdxChain_prependToTable _ _ j (validIdxChain_prependToTable _ p s
    (validIdxChain_buildFreshChains L false p.val L le_rfl) (by grind) fun q hq => ?_)
    (by grind) fun q hq => ?_
  -- `p` does not occur in the base chain on its side: a fresh step `q = (i + 1, stepPred p i)`
  -- there has the polarity of `p`, which excludes `i + 1 = p`, and `stepPred p i ≠ p` as `2 ≤ p`.
  · obtain ⟨hq1, hq2, hq3, hq4⟩ := mem_buildFreshChains L false p.val _ L le_rfl q hq
    grind [stepTable, stepPred]
  -- The end index (`0` if `p = L`, else `L`) occurs neither in `(p, s)` nor in the base chain on
  -- its side, again by comparing polarities.
  · rw [mem_prependToTable_iff] at hq
    rcases hq with ⟨rfl, htab⟩ | hq
    · grind
    · obtain ⟨hq1, hq2, hq3, hq4⟩ := mem_buildFreshChains L false p.val _ L le_rfl q hq
      grind [stepTable, stepPred]

/-- **Case A (`HasBicyclicPrefix`)**: there exists a walk prefix of `L + 1` pairwise distinct keys
starting at `u` (`y 0 = u`, `y 1, ..., y L ∈ S`) that closes two distinct cycles, forming an
independent system of `L + 2` hash-collision equations across `(h₁, h₂)`. -/
def HasBicyclicPrefix {U m : ℕ} (h₁ h₂ : Fin U → Fin m) (S : Finset (Fin U)) (u : Fin U)
    (L : ℕ) : Prop :=
  ∃ (p s j : Fin (L + 1)) (y : Fin (L + 1) → Fin U),
    ValidBicyclicIdx L p s j ∧
    Function.Injective y ∧ y 0 = u ∧ (∀ i : Fin L, y i.succ ∈ S) ∧
    EquationChain h₁ (mapIdxChain y (bicyclicChains L p s j).1) ∧
    EquationChain h₂ (mapIdxChain y (bicyclicChains L p s j).2)

/-- Plain characterization of `HasBicyclicPrefix` without internal equation-chain helpers:
`HasBicyclicPrefix h₁ h₂ S u L` holds iff there exist cycle indices `p, s, j : Fin (L + 1)` and an
injective sequence `y : Fin (L + 1) → Fin U` (`y 0 = u`, `y i.succ ∈ S`) satisfying the two
cycle-closing collision equations together with the `L` fresh-step collision equations. -/
theorem hasBicyclicPrefix_iff {U m : ℕ} (h₁ h₂ : Fin U → Fin m) (S : Finset (Fin U)) (u : Fin U)
    (L : ℕ) :
    HasBicyclicPrefix h₁ h₂ S u L ↔
      ∃ (p s j : Fin (L + 1)) (y : Fin (L + 1) → Fin U),
        (2 ≤ p.val ∧ s.val < p.val ∧ s.val % 2 = p.val % 2 ∧
          (if p.val = L then 1 ≤ j.val ∧ j.val < L else j.val < L)) ∧
        Function.Injective y ∧ y 0 = u ∧ (∀ i : Fin L, y i.succ ∈ S) ∧
        (let endIdx : Fin (L + 1) := ⟨if p.val = L then 0 else L, by split_ifs <;> omega⟩
         if (L - p.val + 1) % 2 == 1 then h₂ (y endIdx) = h₂ (y j)
         else h₁ (y endIdx) = h₁ (y j)) ∧
        (if p.val % 2 == 1 then h₂ (y p) = h₂ (y s) else h₁ (y p) = h₁ (y s)) ∧
        ∀ i : Fin L,
          let pred : Fin (L + 1) := ⟨if i.val = p.val then 0 else i.val, by split_ifs <;> omega⟩
          if (if i.val < p.val then i.val % 2 == 1 else (i.val - p.val + 1) % 2 == 1) then
            h₂ (y i.succ) = h₂ (y pred)
          else
            h₁ (y i.succ) = h₁ (y pred) := by
  unfold HasBicyclicPrefix ValidBicyclicIdx bicyclicChains
  refine exists_congr fun p => exists_congr fun s => exists_congr fun j => exists_congr fun y =>
    and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ =>
    and_congr_right fun _ => ?_
  dsimp only
  rw [equationChain_prependToTable_iff, equationChain_prependToTable_iff,
    equationChain_buildFreshChains_iff h₁ h₂ L false p.val y L le_rfl]
  refine and_congr_right fun _ => and_congr_right fun _ => ⟨fun h i => ?_, fun h i hi _ => ?_⟩
  · simpa [stepTable, stepPred, Fin.succ] using h i.val i.isLt i.isLt
  · simpa [stepTable, stepPred, Fin.succ] using h ⟨i, hi⟩

instance {U m : ℕ} (h₁ h₂ : Fin U → Fin m) (S : Finset (Fin U)) (u : Fin U) (L : ℕ) :
    Decidable (HasBicyclicPrefix h₁ h₂ S u L) :=
  decidable_of_iff' _ (hasBicyclicPrefix_iff h₁ h₂ S u L)

/-- **Set-level excess-`≥ 1` subgraph (`HasExcessSubset`)**: there exists a subset
`K ⊆ insert u S` containing `u` of size `3 ≤ K.card ≤ maxCard` whose images under `h₁` and `h₂`
have combined size at most `K.card - 1`. -/
@[expose]
def HasExcessSubset {U m : ℕ} (h₁ h₂ : Fin U → Fin m) (S : Finset (Fin U)) (u : Fin U)
    (maxCard : ℕ) : Prop :=
  ∃ K ∈ (insert u S).powerset, u ∈ K ∧ 3 ≤ K.card ∧ K.card ≤ maxCard ∧
    (K.image h₁).card + (K.image h₂).card + 1 ≤ K.card

instance {U m : ℕ} (h₁ h₂ : Fin U → Fin m) (S : Finset (Fin U)) (u : Fin U) (maxCard : ℕ) :
    Decidable (HasExcessSubset h₁ h₂ S u maxCard) := by
  unfold HasExcessSubset
  infer_instance

/-- Build a tuple `Fin (N + 1) → U` with head `u` and tail in `S`. -/
private def tupleFromFinset {U : Type*} (S : Finset U) (u : U) {N : ℕ} (g : Fin N → S)
    (i : Fin (N + 1)) : U :=
  Fin.cases u (fun j => (g j).val) i

private theorem exists_tupleFromFinset {U : Type*} {S : Finset U} {u : U} {N : ℕ}
    {y : Fin (N + 1) → U} (hy0 : y 0 = u) (hmem : ∀ i : Fin N, y i.succ ∈ S) :
    ∃ g : Fin N → S, tupleFromFinset S u g = y := by
  refine ⟨fun j => ⟨y j.succ, hmem j⟩, funext fun i => ?_⟩
  refine Fin.cases ?_ (fun j => rfl) i
  exact hy0.symm

/-- Union bound over a finite index type: if every `θ` satisfying `Q` lies in some `E i` with
`c * #(E i) ≤ M`, then `c * #{θ | Q θ} ≤ Fintype.card ι * M`. -/
private theorem mul_card_filter_le_card_mul {Θ ι : Type*} [Fintype Θ] [Fintype ι] {c M : ℕ}
    {Q : Θ → Prop} [DecidablePred Q] (E : ι → Finset Θ)
    (hQ : ∀ θ, Q θ → ∃ i, θ ∈ E i ∧ c * #(E i) ≤ M) :
    c * #{θ | Q θ} ≤ Fintype.card ι * M := by
  classical
  calc c * #{θ | Q θ} ≤ c * #(({i | c * #(E i) ≤ M} : Finset ι).biUnion E) :=
        Nat.mul_le_mul_left _ (Finset.card_le_card fun θ hθ => by
          obtain ⟨i, hi, hc⟩ := hQ θ (Finset.mem_filter.mp hθ).2
          exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩, hi⟩)
    _ ≤ ∑ i with c * #(E i) ≤ M, c * #(E i) :=
        (Nat.mul_le_mul_left _ Finset.card_biUnion_le).trans_eq (Finset.mul_sum ..)
    _ ≤ ∑ i with c * #(E i) ≤ M, M := Finset.sum_le_sum fun i hi => (Finset.mem_filter.mp hi).2
    _ ≤ Fintype.card ι * M := by
        rw [Finset.sum_const, smul_eq_mul]
        exact Nat.mul_le_mul_right _ (Finset.card_filter_le _ _)

/-- Seed-count bound for `HasAltPath`: for any `k`-wise independent pair `(h₁, h₂)` with
`ℓ + 1 ≤ k`, the number of seed pairs satisfying `HasAltPath (h₁ θ.1) (h₂ θ.2) S u ℓ` is at most
`2 * S.card ^ ℓ * Fintype.card (Θ₁ × Θ₂) / m ^ ℓ`. -/
private theorem card_filter_hasAltPath_le {Θ₁ Θ₂ : Type*} [Fintype Θ₁] [Fintype Θ₂]
    {U m k ℓ : ℕ} (hm : 0 < m)
    {h₁ : Θ₁ → Fin U → Fin m} {h₂ : Θ₂ → Fin U → Fin m}
    (hk₁ : IsKWiseIndependentHash k h₁) (hk₂ : IsKWiseIndependentHash k h₂)
    (S : Finset (Fin U)) (u : Fin U) (hℓk : ℓ + 1 ≤ k) :
    m ^ ℓ * #{θ : Θ₁ × Θ₂ | HasAltPath (h₁ θ.1) (h₂ θ.2) S u ℓ} ≤
      2 * S.card ^ ℓ * Fintype.card (Θ₁ × Θ₂) := by
  classical
  refine (mul_card_filter_le_card_mul (M := Fintype.card (Θ₁ × Θ₂))
    (fun p : Bool × (Fin ℓ → S) => ({θ |
      EquationChain (h₁ θ.1) (mapIdxChain (tupleFromFinset S u p.2) (altPathChains ℓ p.1).1) ∧
      EquationChain (h₂ θ.2) (mapIdxChain (tupleFromFinset S u p.2) (altPathChains ℓ p.1).2)} :
      Finset (Θ₁ × Θ₂))) fun θ ⟨b, y, hinj, hy0, hmem, heq⟩ => ?_).trans_eq
    (by simp [Fintype.card_coe])
  obtain ⟨g, rfl⟩ := exists_tupleFromFinset hy0 hmem
  exact ⟨(b, g), by simpa using heq, (card_filter_prod_equationChain_eq hm hk₁ hk₂ hℓk hinj
    (validIdxChain_altPathChains ℓ b) (length_altPathChains ℓ b)).le⟩

/-- Seed-count bound for `HasBicyclicPrefix`: for any `k`-wise independent pair `(h₁, h₂)` with
`L + 1 ≤ k`, the number of seed pairs satisfying `HasBicyclicPrefix (h₁ θ.1) (h₂ θ.2) S u L` is at
most `(L + 1) ^ 3 * S.card ^ L * Fintype.card (Θ₁ × Θ₂) / m ^ (L + 2)`. -/
private theorem card_filter_hasBicyclicPrefix_le {Θ₁ Θ₂ : Type*} [Fintype Θ₁] [Fintype Θ₂]
    {U m k L : ℕ} (hm : 0 < m)
    {h₁ : Θ₁ → Fin U → Fin m} {h₂ : Θ₂ → Fin U → Fin m}
    (hk₁ : IsKWiseIndependentHash k h₁) (hk₂ : IsKWiseIndependentHash k h₂)
    (S : Finset (Fin U)) (u : Fin U) (hLk : L + 1 ≤ k) :
    m ^ (L + 2) * #{θ : Θ₁ × Θ₂ | HasBicyclicPrefix (h₁ θ.1) (h₂ θ.2) S u L} ≤
      (L + 1) ^ 3 * S.card ^ L * Fintype.card (Θ₁ × Θ₂) := by
  classical
  refine (mul_card_filter_le_card_mul (M := Fintype.card (Θ₁ × Θ₂))
    (fun p : Fin (L + 1) × Fin (L + 1) × Fin (L + 1) × (Fin L → S) => ({θ |
      EquationChain (h₁ θ.1)
        (mapIdxChain (tupleFromFinset S u p.2.2.2) (bicyclicChains L p.1 p.2.1 p.2.2.1).1) ∧
      EquationChain (h₂ θ.2)
        (mapIdxChain (tupleFromFinset S u p.2.2.2) (bicyclicChains L p.1 p.2.1 p.2.2.1).2)} :
      Finset (Θ₁ × Θ₂))) fun θ ⟨p, s, j, y, hidx, hinj, hy0, hmem, heq⟩ => ?_).trans_eq
    (by simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_fun, Fintype.card_coe]; ring)
  obtain ⟨g, rfl⟩ := exists_tupleFromFinset hy0 hmem
  exact ⟨(p, s, j, g), by simpa using heq, (card_filter_prod_equationChain_eq hm hk₁ hk₂ hLk hinj
    (validIdxChain_bicyclicChains hidx) (length_bicyclicChains L p s j)).le⟩

/-! ## Section 2: Half-step trace of `pureEvict` and Pagh–Rodler Lemma 1 (`cuckooWalk_dichotomy`) -/

/-- Every valid equation chain `eqs` whose keys lie in `K` reduces the image cardinality
`(K.image h).card` by at least `eqs.length`: `(K.image h).card + eqs.length ≤ K.card`. -/
private theorem card_image_add_length_le_of_validEqChain {U m : ℕ} (h : Fin U → Fin m) :
    ∀ {eqs : List (Fin U × Fin U)} {K : Finset (Fin U)},
      ValidEqChain eqs → eqChainKeys eqs ⊆ K → EquationChain h eqs →
      (K.image h).card + eqs.length ≤ K.card
  | [], K, _, _, _ => Finset.card_image_le
  | (w, v) :: rest, K, ⟨hw_ne_v, hw_not_rest, hvalid_rest⟩, hsub, ⟨hw_eq_v, heq_rest⟩ => by
    simp only [eqChainKeys, Finset.insert_subset_iff] at hsub
    have ih := card_image_add_length_le_of_validEqChain h hvalid_rest (K := K.erase w)
      (fun x hx => Finset.mem_erase.mpr ⟨fun hxw => hw_not_rest (hxw ▸ hx), hsub.2.2 hx⟩) heq_rest
    have himg_eq : K.image h = (K.erase w).image h := by grind
    rw [himg_eq, List.length_cons, ← Finset.card_erase_add_one hsub.1]
    omega

/-- Any bicyclic walk prefix of parameter `L ∈ [2, 2 * r)` yields a subset `K ⊆ insert u S`
containing `u` with `3 ≤ K.card ≤ 2 * r` and `(K.image h₁).card + (K.image h₂).card + 1 ≤ K.card`.
-/
theorem hasBicyclicPrefix_imp_hasExcessSubset {U m r L : ℕ}
    {h₁ h₂ : Fin U → Fin m} {S : Finset (Fin U)} {u : Fin U}
    (hL2 : 2 ≤ L) (hLr : L < 2 * r) (hbic : HasBicyclicPrefix h₁ h₂ S u L) :
    HasExcessSubset h₁ h₂ S u (2 * r) := by
  obtain ⟨p, s, j, y, hidx, hinj, hy0, hmem, heq1, heq2⟩ := hbic
  have hvalid := validIdxChain_bicyclicChains hidx
  have himg1 := card_image_add_length_le_of_validEqChain h₁
    (validEqChain_mapIdxChain hinj hvalid.1) (eqChainKeys_mapIdxChain_subset y _) heq1
  have himg2 := card_image_add_length_le_of_validEqChain h₂
    (validEqChain_mapIdxChain hinj hvalid.2) (eqChainKeys_mapIdxChain_subset y _) heq2
  have hlen := length_bicyclicChains L p s j
  have hK_card : (Finset.univ.image y).card = L + 1 := by
    simp [Finset.card_image_of_injective _ hinj]
  rw [length_mapIdxChain] at himg1 himg2
  refine ⟨Finset.univ.image y, Finset.mem_powerset.mpr fun x hx => ?_,
    hy0 ▸ Finset.mem_image_of_mem y (Finset.mem_univ 0), by omega, by omega, by omega⟩
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
  exact Fin.cases (hy0 ▸ Finset.mem_insert_self u S) (fun k => Finset.mem_insert_of_mem (hmem k)) i

/-- Read a slot from the unified two-table slot space `Fin m ⊕ Fin m`. -/
private def readSlot {U m : ℕ} (tbl : PureTable U m) : Fin m ⊕ Fin m → Option (SlotEntry U)
  | Sum.inl i => tbl.t1 i
  | Sum.inr i => tbl.t2 i

/-- Target slot in `Fin m ⊕ Fin m` probed at half-step `step` for key `k`. -/
private def stepSlot {U m : ℕ} (h₁ h₂ : Fin U → Fin m) (step : ℕ) (k : Fin U) : Fin m ⊕ Fin m :=
  if step % 2 = 0 then Sum.inl (h₁ k) else Sum.inr (h₂ k)

@[simp]
private theorem stepSlot_add_two {U m : ℕ} (h₁ h₂ : Fin U → Fin m) (step : ℕ) (k : Fin U) :
    stepSlot h₁ h₂ (step + 2) k = stepSlot h₁ h₂ step k := by
  unfold stepSlot
  rw [Nat.add_mod_right]

private theorem stepSlot_congr {U m : ℕ} {h₁ h₂ : Fin U → Fin m} {i j : ℕ} (hij : i % 2 = j % 2)
    (k : Fin U) : stepSlot h₁ h₂ i k = stepSlot h₁ h₂ j k := by
  unfold stepSlot
  rw [hij]

private theorem stepSlot_eq_imp_mod_two_eq {U m : ℕ} {h₁ h₂ : Fin U → Fin m} {i j : ℕ}
    {k₁ k₂ : Fin U} (heq : stepSlot h₁ h₂ i k₁ = stepSlot h₁ h₂ j k₂) :
    i % 2 = j % 2 := by
  unfold stepSlot at heq
  rcases Nat.mod_two_eq_zero_or_one i with hi | hi <;>
    rcases Nat.mod_two_eq_zero_or_one j with hj | hj <;>
    simp [hi, hj] at heq ⊢

private theorem readSlot_putT1 {U m : ℕ} (h₁ : Fin U → Fin m) (tbl : PureTable U m)
    (e : SlotEntry U) :
    readSlot (putT1 h₁ tbl e).1 =
      Function.update (readSlot tbl) (Sum.inl (h₁ e.key)) (some e) := by
  funext s
  cases s <;> simp [readSlot, putT1, Function.update_apply]

private theorem readSlot_putT2 {U m : ℕ} (h₂ : Fin U → Fin m) (tbl : PureTable U m)
    (e : SlotEntry U) :
    readSlot (putT2 h₂ tbl e).1 =
      Function.update (readSlot tbl) (Sum.inr (h₂ e.key)) (some e) := by
  funext s
  cases s <;> simp [readSlot, putT2, Function.update_apply]

private theorem readSlot_some_imp_entryIn {U m : ℕ} {tbl : PureTable U m} {s : Fin m ⊕ Fin m}
    {d : SlotEntry U} (h : readSlot tbl s = some d) :
    EntryIn tbl d := by
  cases s with
  | inl i => exact Or.inl ⟨i, h⟩
  | inr i => exact Or.inr ⟨i, h⟩

/-- Half-step trace invariant for `N` consecutive cuckoo displacement half-steps. -/
private structure IsRawWalkTrace {U m : ℕ} (h₁ h₂ : Fin U → Fin m)
    (N : ℕ) (f : ℕ → Fin m ⊕ Fin m → Option (SlotEntry U)) (es : ℕ → SlotEntry U) : Prop where
  step_read : ∀ i < N, f i (stepSlot h₁ h₂ i (es i).key) = some (es (i + 1))
  step_update : ∀ i < N,
    f (i + 1) = Function.update (f i) (stepSlot h₁ h₂ i (es i).key) (some (es i))
  step_home : ∀ i < N,
    stepSlot h₁ h₂ i (es (i + 1)).key = stepSlot h₁ h₂ i (es i).key
  step_not_in : ∀ i ≤ N, ∀ s d, f i s = some d → d.key ≠ (es i).key

/-- Every non-terminating `r`-round execution `pureEvict h₁ h₂ r tbl₀ e₀ = none` from a well-placed
table `tbl₀` with `¬ HasKey tbl₀ e₀.key` unrolls into a `2 * r`-half-step raw walk trace. -/
private theorem exists_rawWalkTrace_of_pureEvict_eq_none {U m : ℕ} {h₁ h₂ : Fin U → Fin m} :
    ∀ (r : ℕ) {tbl₀ : PureTable U m} {e₀ : SlotEntry U},
      WellPlaced h₁ h₂ tbl₀ → ¬ HasKey tbl₀ e₀.key →
      pureEvict h₁ h₂ r tbl₀ e₀ = none →
      ∃ (f : ℕ → Fin m ⊕ Fin m → Option (SlotEntry U)) (es : ℕ → SlotEntry U),
        f 0 = readSlot tbl₀ ∧ es 0 = e₀ ∧ IsRawWalkTrace h₁ h₂ (2 * r) f es
  | 0, tbl₀, e₀, _, hno₀, _ =>
    ⟨fun _ => readSlot tbl₀, fun _ => e₀, rfl, rfl, by simp, by simp, by simp,
      fun _ _ _ d hread heq => hno₀ ⟨d, readSlot_some_imp_entryIn hread, heq⟩⟩
  | r + 1, tbl₀, e₀, hwp₀, hno₀, hev => by
    unfold pureEvict pureEvictRound at hev
    have hwp₁ : WellPlaced h₁ h₂ (putT1 h₁ tbl₀ e₀).1 := putT1_wellPlaced hwp₀ hno₀
    rcases hold₁ : (putT1 h₁ tbl₀ e₀).2 with _ | e₁ <;> rw [hold₁] at hev
    · cases hev
    have hno₁ := (putT1_some_spec hwp₀ hno₀ hold₁).1
    dsimp only at hev
    rcases hold₂ : (putT2 h₂ (putT1 h₁ tbl₀ e₀).1 e₁).2 with _ | e₂ <;>
      rw [← Prod.mk.eta (p := putT2 h₂ (putT1 h₁ tbl₀ e₀).1 e₁), hold₂] at hev
    · cases hev
    obtain ⟨f', es', hf'0, rfl, hraw'⟩ := exists_rawWalkTrace_of_pureEvict_eq_none r
      (putT2_wellPlaced hwp₁ hno₁) (putT2_some_spec hwp₁ hno₁ hold₂).1 hev
    let f : ℕ → Fin m ⊕ Fin m → Option (SlotEntry U)
      | 0 => readSlot tbl₀
      | 1 => readSlot (putT1 h₁ tbl₀ e₀).1
      | k + 2 => f' k
    let es : ℕ → SlotEntry U
      | 0 => e₀
      | 1 => e₁
      | k + 2 => es' k
    refine ⟨f, es, rfl, rfl, ?_, ?_, ?_, ?_⟩ <;> rintro (_ | _ | k) hi
    · exact hold₁
    · exact hold₂
    · simpa [f, es] using hraw'.step_read k (by omega)
    · exact readSlot_putT1 h₁ tbl₀ e₀
    · exact hf'0.trans (readSlot_putT2 h₂ _ e₁)
    · simpa [f, es] using hraw'.step_update k (by omega)
    · exact congrArg Sum.inl (hwp₀.t1_home _ e₁ hold₁)
    · exact congrArg Sum.inr (hwp₁.t2_home _ _ hold₂)
    · simpa [es] using hraw'.step_home k (by omega)
    · exact fun s d hread heq => hno₀ ⟨d, readSlot_some_imp_entryIn hread, heq⟩
    · exact fun s d hread heq => hno₁ ⟨d, readSlot_some_imp_entryIn hread, heq⟩
    · exact hraw'.step_not_in k (by omega)

/-- If slot `s` is not probed at any step `k` in `[j, i)`, then `f i s = f j s`. -/
private theorem IsRawWalkTrace.f_eq_of_forall_ne {U m N : ℕ} {h₁ h₂ : Fin U → Fin m}
    {f : ℕ → Fin m ⊕ Fin m → Option (SlotEntry U)} {es : ℕ → SlotEntry U}
    (htr : IsRawWalkTrace h₁ h₂ N f es) {j : ℕ} {s : Fin m ⊕ Fin m} :
    ∀ {i : ℕ}, j ≤ i → i ≤ N →
      (∀ k, j ≤ k → k < i → stepSlot h₁ h₂ k (es k).key ≠ s) →
      f i s = f j s
  | 0, hj0, _, _ => by rw [Nat.le_zero.mp hj0]
  | i + 1, hji, hiN, hne => by
    rcases eq_or_lt_of_le hji with rfl | hjlt
    · rfl
    · rw [htr.step_update i (by omega), Function.update_of_ne (hne i (by omega) (by omega)).symm]
      exact htr.f_eq_of_forall_ne (by omega) (by omega) fun k hjk hki => hne k hjk (by omega)

/-- **Fresh-Slot Law**: if step `i < N` probes a slot never probed before step `i`, then the
displaced entry `es (i + 1)` was already sitting in that slot at step `0`, and its key is distinct
from `(es k).key` for every `k ≤ i`. -/
private theorem IsRawWalkTrace.fresh_slot_spec {U m N : ℕ} {h₁ h₂ : Fin U → Fin m}
    {f : ℕ → Fin m ⊕ Fin m → Option (SlotEntry U)} {es : ℕ → SlotEntry U}
    (htr : IsRawWalkTrace h₁ h₂ N f es) {i : ℕ} (hi : i < N)
    (hfresh : ∀ m < i, stepSlot h₁ h₂ m (es m).key ≠ stepSlot h₁ h₂ i (es i).key) :
    f 0 (stepSlot h₁ h₂ i (es i).key) = some (es (i + 1)) ∧
      ∀ k ≤ i, (es (i + 1)).key ≠ (es k).key := by
  have key : ∀ k ≤ i, f k (stepSlot h₁ h₂ i (es i).key) = some (es (i + 1)) := fun k hki =>
    (htr.f_eq_of_forall_ne hki hi.le fun m _ hmi => hfresh m hmi).symm.trans (htr.step_read i hi)
  exact ⟨key 0 (Nat.zero_le i), fun k hki => htr.step_not_in k (by omega) _ _ (key k hki)⟩

/-- **Revisit Law**: if `k < i < N` is the most recent step before `i` that probed the slot of step
`i`, then step `i` evicts `es k` (`es (i + 1) = es k`). -/
private theorem IsRawWalkTrace.revisit_slot_spec {U m N : ℕ} {h₁ h₂ : Fin U → Fin m}
    {f : ℕ → Fin m ⊕ Fin m → Option (SlotEntry U)} {es : ℕ → SlotEntry U}
    (htr : IsRawWalkTrace h₁ h₂ N f es) {k i : ℕ} (hki : k < i) (hi : i < N)
    (heq : stepSlot h₁ h₂ k (es k).key = stepSlot h₁ h₂ i (es i).key)
    (hlast : ∀ m, k < m → m < i → stepSlot h₁ h₂ m (es m).key ≠ stepSlot h₁ h₂ i (es i).key) :
    es (i + 1) = es k := by
  have h1 := htr.f_eq_of_forall_ne (Nat.succ_le_of_lt hki) hi.le hlast
  rw [htr.step_read i hi, htr.step_update k (by omega), ← heq, Function.update_self] at h1
  exact Option.some.inj h1

/-- **Backtracking at the first revisit**: if `t₁ < N` is the first step that revisits an earlier
slot (`stepSlot h₁ h₂ s (es s).key = stepSlot h₁ h₂ t₁ (es t₁).key` with `s < t₁`, and all steps
`< t₁` are fresh), then for every `0 ≤ d ≤ s` with `t₁ + d < N`, step `t₁ + d` probes
`stepSlot h₁ h₂ (s - d) (es (s - d)).key` and evicts key `(es (s - d)).key`. -/
private theorem IsRawWalkTrace.backtrack_at_first_revisit {U m N : ℕ} {h₁ h₂ : Fin U → Fin m}
    {f : ℕ → Fin m ⊕ Fin m → Option (SlotEntry U)} {es : ℕ → SlotEntry U}
    (htr : IsRawWalkTrace h₁ h₂ N f es) {s t₁ : ℕ} (hst : s < t₁)
    (hfresh_lt : ∀ i < t₁, ∀ k < i, stepSlot h₁ h₂ k (es k).key ≠ stepSlot h₁ h₂ i (es i).key)
    (hrev : stepSlot h₁ h₂ s (es s).key = stepSlot h₁ h₂ t₁ (es t₁).key) :
    ∀ (d : ℕ), d ≤ s → t₁ + d < N →
      stepSlot h₁ h₂ (t₁ + d) (es (t₁ + d)).key = stepSlot h₁ h₂ (s - d) (es (s - d)).key ∧
        (es (t₁ + d + 1)).key = (es (s - d)).key
  | 0, _, htN =>
    ⟨hrev.symm, congrArg SlotEntry.key (htr.revisit_slot_spec hst htN hrev fun m hsm hmt heqm =>
      hfresh_lt m hmt s hsm (hrev.trans heqm.symm))⟩
  | d + 1, hds, htN => by
    obtain ⟨hb_ih, hx_ih⟩ :=
      htr.backtrack_at_first_revisit hst hfresh_lt hrev d (by omega) (by omega)
    have hpar_st : s % 2 = t₁ % 2 := stepSlot_eq_imp_mod_two_eq hrev
    have hb_cur : stepSlot h₁ h₂ (t₁ + (d + 1)) (es (t₁ + (d + 1))).key =
        stepSlot h₁ h₂ (s - (d + 1)) (es (s - (d + 1))).key := by
      have h1 := htr.step_home (s - (d + 1)) (by omega)
      rw [show s - (d + 1) + 1 = s - d by omega, ← hx_ih] at h1
      exact (stepSlot_congr (by omega) _).trans h1
    refine ⟨hb_cur, congrArg SlotEntry.key (htr.revisit_slot_spec (by omega) htN hb_cur.symm
      fun m hsm hmt heqm => ?_)⟩
    have heqm' := heqm.trans hb_cur
    by_cases hmt₁ : m < t₁
    · exact hfresh_lt m hmt₁ (s - (d + 1)) hsm heqm'.symm
    · have hb_m :=
        (htr.backtrack_at_first_revisit hst hfresh_lt hrev (m - t₁) (by omega) (by omega)).1
      rw [show t₁ + (m - t₁) = m by omega] at hb_m
      exact hfresh_lt (s - (m - t₁)) (by omega) (s - (d + 1)) (by omega) (heqm'.symm.trans hb_m)

/-- After the first revisit at step `t₁` of the slot probed at step `s`, the walk backtracks to
its start: step `t₁ + s + 1` carries the key of step `0` again. -/
private theorem IsRawWalkTrace.key_after_backtrack {U m N : ℕ} {h₁ h₂ : Fin U → Fin m}
    {f : ℕ → Fin m ⊕ Fin m → Option (SlotEntry U)} {es : ℕ → SlotEntry U}
    (htr : IsRawWalkTrace h₁ h₂ N f es) {s t₁ : ℕ} (hst : s < t₁)
    (hfresh_lt : ∀ i < t₁, ∀ k < i, stepSlot h₁ h₂ k (es k).key ≠ stepSlot h₁ h₂ i (es i).key)
    (hrev : stepSlot h₁ h₂ s (es s).key = stepSlot h₁ h₂ t₁ (es t₁).key) (htN : t₁ + s < N) :
    (es (t₁ + s + 1)).key = (es 0).key := by
  simpa using (htr.backtrack_at_first_revisit hst hfresh_lt hrev s le_rfl htN).2

/-- A slot collision between half-steps `i` and `j` is a collision under the hash function of the
sub-table probed at step `i` (`h₂` for odd `i`, `h₁` for even `i`). -/
private theorem hash_eq_of_stepSlot_eq {U m : ℕ} {h₁ h₂ : Fin U → Fin m} {i j : ℕ}
    {k₁ k₂ : Fin U} {b : Bool} (hb : b = (i % 2 == 1))
    (h : stepSlot h₁ h₂ i k₁ = stepSlot h₁ h₂ j k₂) :
    if b then h₂ k₁ = h₂ k₂ else h₁ k₁ = h₁ k₂ := by
  subst hb
  unfold stepSlot at h
  rcases Nat.mod_two_eq_zero_or_one i with hi | hi <;>
    rcases Nat.mod_two_eq_zero_or_one j with hj | hj <;> simp_all

/-- Any contiguous segment `[start, start + ℓ)` of fresh half-steps starting at `(es start).key = u`
produces a simple alternating path of length `ℓ` starting at `u` (`HasAltPath h₁ h₂ S u ℓ`). -/
private theorem IsRawWalkTrace.hasAltPath_of_fresh_segment {U m N : ℕ} {h₁ h₂ : Fin U → Fin m}
    {S : Finset (Fin U)} {u : Fin U}
    {f : ℕ → Fin m ⊕ Fin m → Option (SlotEntry U)} {es : ℕ → SlotEntry U}
    (htr : IsRawWalkTrace h₁ h₂ N f es)
    (hinit : ∀ s d, f 0 s = some d → d.key ∈ S)
    {start ℓ : ℕ} (hbound : start + ℓ ≤ N) (hstart : (es start).key = u)
    (hfresh : ∀ d < ℓ, ∀ k < start + d,
      stepSlot h₁ h₂ k (es k).key ≠ stepSlot h₁ h₂ (start + d) (es (start + d)).key) :
    HasAltPath h₁ h₂ S u ℓ := by
  refine (hasAltPath_iff h₁ h₂ S u ℓ).mpr ⟨start % 2 == 1, fun i => (es (start + i.val)).key,
    ?_, hstart, fun i => ?_, fun i => ?_⟩
  · refine Function.Injective.of_lt_imp_ne fun i₁ i₂ (hlt : i₁.val < i₂.val) heq => ?_
    have hspec := (htr.fresh_slot_spec (by omega) (hfresh (i₂.val - 1) (by omega))).2
      (start + i₁.val) (by omega)
    rw [show start + (i₂.val - 1) + 1 = start + i₂.val by omega] at hspec
    exact hspec heq.symm
  · exact hinit _ _ (htr.fresh_slot_spec (i := start + i.val) (by omega) (hfresh i.val i.isLt)).1
  · exact hash_eq_of_stepSlot_eq (by grind) (htr.step_home (start + i.val) (by omega))

/-- Map key index `i ∈ [0, L]` of a bicyclic prefix to its half-step entry index in `es`. -/
private def bicyclicKeyStep (t₁ T₁ i : ℕ) : ℕ :=
  if i ≤ t₁ then i else T₁ + (i - t₁)

/-- Map fresh step index `m ∈ [0, L)` of a bicyclic prefix to its half-step index in `es`. -/
private def bicyclicFreshStep (t₁ T₁ m : ℕ) : ℕ :=
  if m < t₁ then m else T₁ + (m - t₁)

private theorem bicyclicKeyStep_succ (t₁ T₁ m : ℕ) :
    bicyclicKeyStep t₁ T₁ (m + 1) = bicyclicFreshStep t₁ T₁ m + 1 := by
  unfold bicyclicKeyStep bicyclicFreshStep
  split_ifs <;> omega

private theorem bicyclicKeyStep_le_freshStep (t₁ T₁ i m : ℕ) (ht : t₁ ≤ T₁) (him : i ≤ m) :
    bicyclicKeyStep t₁ T₁ i ≤ bicyclicFreshStep t₁ T₁ m := by
  unfold bicyclicKeyStep bicyclicFreshStep
  split_ifs <;> omega

/-- If a walk trace has its first revisit at `t₁` (`s₀ < t₁`) and its first subsequent revisit at or
after `T₁ = t₁ + s₀ + 1` at step `t₂ < N`, then `L = t₁ + (t₂ - T₁)` satisfies `2 ≤ L < N` and
`HasBicyclicPrefix h₁ h₂ S u L`. -/
private theorem IsRawWalkTrace.hasBicyclicPrefix_of_two_revisits {U m N : ℕ} {h₁ h₂ : Fin U → Fin m}
    {S : Finset (Fin U)} {u : Fin U}
    {f : ℕ → Fin m ⊕ Fin m → Option (SlotEntry U)} {es : ℕ → SlotEntry U}
    (htr : IsRawWalkTrace h₁ h₂ N f es)
    (hu0 : (es 0).key = u)
    (hinit : ∀ s d, f 0 s = some d → d.key ∈ S)
    {s₀ t₁ t₂ : ℕ} (hst : s₀ < t₁) (ht₁₂ : t₁ + s₀ + 1 ≤ t₂) (ht₂N : t₂ < N)
    (hrev₁ : stepSlot h₁ h₂ s₀ (es s₀).key = stepSlot h₁ h₂ t₁ (es t₁).key)
    (hfresh₁ : ∀ i < t₁, ∀ k < i, stepSlot h₁ h₂ k (es k).key ≠ stepSlot h₁ h₂ i (es i).key)
    (hrev₂ : ∃ k < t₂, stepSlot h₁ h₂ k (es k).key = stepSlot h₁ h₂ t₂ (es t₂).key)
    (hfresh₂ : ∀ m, t₁ + s₀ + 1 ≤ m → m < t₂ → ∀ k < m,
      stepSlot h₁ h₂ k (es k).key ≠ stepSlot h₁ h₂ m (es m).key) :
    ∃ L ∈ Finset.Ico 2 N, HasBicyclicPrefix h₁ h₂ S u L := by
  let T₁ := t₁ + s₀ + 1
  let L := t₁ + (t₂ - T₁)
  have hpar_st : s₀ % 2 = t₁ % 2 := stepSlot_eq_imp_mod_two_eq hrev₁
  have hT₁_key : (es T₁).key = u :=
    (htr.key_after_backtrack hst hfresh₁ hrev₁ (by omega)).trans hu0
  have hfresh_step : ∀ m < L, ∀ k < bicyclicFreshStep t₁ T₁ m,
      stepSlot h₁ h₂ k (es k).key ≠
        stepSlot h₁ h₂ (bicyclicFreshStep t₁ T₁ m) (es (bicyclicFreshStep t₁ T₁ m)).key := by
    intro m hmL
    unfold bicyclicFreshStep
    split_ifs with hmt₁
    exacts [hfresh₁ m hmt₁, hfresh₂ (T₁ + (m - t₁)) (by omega) (by omega)]
  have hstep_ltN : ∀ m < L, bicyclicFreshStep t₁ T₁ m < N := fun m hmL => by
    unfold bicyclicFreshStep
    split_ifs <;> omega
  -- The second revisit may be taken to hit a step outside the backtracking window `[t₁, T₁)`.
  obtain ⟨k, hk_lt, hk_eq, hk_out⟩ : ∃ k < t₂,
      stepSlot h₁ h₂ k (es k).key = stepSlot h₁ h₂ t₂ (es t₂).key ∧ (k < t₁ ∨ T₁ ≤ k) := by
    obtain ⟨k₀, hk₀_lt, hk₀_eq⟩ := hrev₂
    by_cases hk : k₀ < t₁ ∨ T₁ ≤ k₀
    · exact ⟨k₀, hk₀_lt, hk₀_eq, hk⟩
    · have hbt :=
        (htr.backtrack_at_first_revisit hst hfresh₁ hrev₁ (k₀ - t₁) (by omega) (by omega)).1
      rw [show t₁ + (k₀ - t₁) = k₀ by omega] at hbt
      exact ⟨s₀ - (k₀ - t₁), by omega, hbt.symm.trans hk₀_eq, Or.inl (by omega)⟩
  have hpar_k : k % 2 = t₂ % 2 := stepSlot_eq_imp_mod_two_eq hk_eq
  -- Key index `j` of step `k`, and the key carried by the end index of the closing equation.
  obtain ⟨j, hjL, hj1, hyj⟩ : ∃ j < L, (t₁ = L → 1 ≤ j) ∧
      (es (bicyclicKeyStep t₁ T₁ j)).key = (es k).key := by
    rcases hk_out with hk | hk
    · exact ⟨k, by omega, by omega, by rw [bicyclicKeyStep, ite_eq_left hk.le]⟩
    · rcases hk.eq_or_lt with rfl | hk
      · exact ⟨0, by omega, by omega, by rw [bicyclicKeyStep, ite_eq_left t₁.zero_le, hu0, hT₁_key]⟩
      · exact ⟨t₁ + (k - T₁), by omega, by omega,
          by rw [bicyclicKeyStep, ite_eq_right (by omega)]; congr 2; omega⟩
  have hend : (es (bicyclicKeyStep t₁ T₁ (if t₁ = L then 0 else L))).key = (es t₂).key := by
    by_cases hL : t₁ = L
    · rw [ite_eq_left hL, bicyclicKeyStep, ite_eq_left t₁.zero_le, hu0, show t₂ = T₁ by omega,
        hT₁_key]
    · rw [ite_eq_right hL, bicyclicKeyStep, ite_eq_right (by omega)]
      congr 2; omega
  refine ⟨L, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, (hasBicyclicPrefix_iff h₁ h₂ S u L).mpr
    ⟨⟨t₁, by omega⟩, ⟨s₀, by omega⟩, ⟨j, by omega⟩,
      fun i => (es (bicyclicKeyStep t₁ T₁ i.val)).key,
      ⟨show 2 ≤ t₁ by omega, hst, hpar_st, by split_ifs with h; exacts [⟨hj1 h, hjL⟩, hjL]⟩,
      ?_, ?_, fun i => ?_, ?_, ?_, fun i => ?_⟩⟩
  · refine Function.Injective.of_lt_imp_ne fun i₁ i₂ (hlt : i₁.val < i₂.val) heq => ?_
    have hm : i₂.val - 1 < L := by omega
    have hspec := (htr.fresh_slot_spec (hstep_ltN _ hm) (hfresh_step _ hm)).2 _
      (bicyclicKeyStep_le_freshStep t₁ T₁ i₁.val (i₂.val - 1) (by omega) (by omega))
    rw [← bicyclicKeyStep_succ, Nat.sub_add_cancel (by omega)] at hspec
    exact hspec heq.symm
  · simpa [bicyclicKeyStep] using hu0
  · have hspec := (htr.fresh_slot_spec (hstep_ltN i i.isLt) (hfresh_step i i.isLt)).1
    rw [← bicyclicKeyStep_succ] at hspec
    exact hinit _ _ hspec
  · dsimp only
    rw [hend, hyj]
    exact hash_eq_of_stepSlot_eq (by congr 1; omega) hk_eq.symm
  · simpa [bicyclicKeyStep, hst.le] using hash_eq_of_stepSlot_eq rfl hrev₁.symm
  · dsimp only
    have hhome := htr.step_home _ (hstep_ltN i i.isLt)
    have hpred : (es (bicyclicKeyStep t₁ T₁ (if i.val = t₁ then 0 else i.val))).key =
        (es (bicyclicFreshStep t₁ T₁ i.val)).key := by
      rcases lt_trichotomy i.val t₁ with h | h | h
      · rw [ite_eq_right h.ne, bicyclicKeyStep, ite_eq_left h.le, bicyclicFreshStep, ite_eq_left h]
      · rw [ite_eq_left h, bicyclicKeyStep, ite_eq_left t₁.zero_le, bicyclicFreshStep,
          ite_eq_right (by omega), hu0, h, Nat.sub_self]
        exact hT₁_key.symm
      · rw [ite_eq_right h.ne', bicyclicKeyStep, ite_eq_right (by omega), bicyclicFreshStep,
          ite_eq_right (by omega)]
    rw [← bicyclicKeyStep_succ, ← hpred] at hhome
    exact hash_eq_of_stepSlot_eq
      (by unfold bicyclicFreshStep; split_ifs <;> first | rfl | (congr 1; omega)) hhome

/-- Predicate that half-step `i` probes a slot already probed at some earlier step `s < i`. -/
private def IsRevisit {U m : ℕ} (h₁ h₂ : Fin U → Fin m) (es : ℕ → SlotEntry U) (i : ℕ) : Prop :=
  ∃ s ∈ Finset.range i, stepSlot h₁ h₂ s (es s).key = stepSlot h₁ h₂ i (es i).key

private instance {U m : ℕ} (h₁ h₂ : Fin U → Fin m) (es : ℕ → SlotEntry U) (i : ℕ) :
    Decidable (IsRevisit h₁ h₂ es i) := by
  unfold IsRevisit
  infer_instance

/-- **Pagh & Rodler (2004), Section 2.3, Lemma 1 (half-step trace dichotomy)**:
In any `N`-half-step walk trace (`2 ≤ N`) starting at `(es 0).key = u` with initial table entries in
`S`, either there is a simple alternating path of length `(N + 2) / 3` starting at `u`, or there is
a bicyclic prefix of length `L ∈ [2, N)` starting at `u`. -/
private theorem IsRawWalkTrace.dichotomy {U m N : ℕ} {h₁ h₂ : Fin U → Fin m}
    {S : Finset (Fin U)} {u : Fin U}
    {f : ℕ → Fin m ⊕ Fin m → Option (SlotEntry U)} {es : ℕ → SlotEntry U}
    (htr : IsRawWalkTrace h₁ h₂ N f es) (hN : 2 ≤ N)
    (hu0 : (es 0).key = u)
    (hinit : ∀ s d, f 0 s = some d → d.key ∈ S) :
    HasAltPath h₁ h₂ S u ((N + 2) / 3) ∨
      ∃ L ∈ Finset.Ico 2 N, HasBicyclicPrefix h₁ h₂ S u L := by
  by_cases hrev1 : ∃ i, i < N ∧ IsRevisit h₁ h₂ es i
  · let t₁ := Nat.find hrev1
    obtain ⟨ht₁_lt, s₀, hs₀_mem, hs₀_eq⟩ := Nat.find_spec hrev1
    have hs₀_lt : s₀ < t₁ := Finset.mem_range.mp hs₀_mem
    have hfresh₁ : ∀ i < t₁, ∀ k < i,
        stepSlot h₁ h₂ k (es k).key ≠ stepSlot h₁ h₂ i (es i).key := fun i hi k hk heq =>
      Nat.find_min hrev1 hi ⟨by omega, k, Finset.mem_range.mpr hk, heq⟩
    by_cases hrev2 : ∃ m, t₁ + s₀ + 1 ≤ m ∧ m < N ∧ IsRevisit h₁ h₂ es m
    · obtain ⟨hT₁_le, ht₂_lt, s₂, hs₂_mem, hs₂_eq⟩ := Nat.find_spec hrev2
      exact Or.inr (htr.hasBicyclicPrefix_of_two_revisits hu0 hinit hs₀_lt hT₁_le ht₂_lt hs₀_eq
        hfresh₁ ⟨s₂, Finset.mem_range.mp hs₂_mem, hs₂_eq⟩ fun m hTm hmt₂ k hk heq =>
        Nat.find_min hrev2 hmt₂ ⟨hTm, by omega, k, Finset.mem_range.mpr hk, heq⟩)
    · by_cases hℓ_le : (N + 2) / 3 ≤ t₁
      · refine Or.inl (htr.hasAltPath_of_fresh_segment hinit (start := 0) (by omega) hu0
          fun d hd k hk => ?_)
        simp only [Nat.zero_add] at hk ⊢
        exact hfresh₁ d (by omega) k hk
      · exact Or.inl (htr.hasAltPath_of_fresh_segment hinit (start := t₁ + s₀ + 1) (by omega)
          ((htr.key_after_backtrack hs₀_lt hfresh₁ hs₀_eq (by omega)).trans hu0)
          fun d hd k hk heq => hrev2 ⟨_, by omega, by omega, k, Finset.mem_range.mpr hk, heq⟩)
  · refine Or.inl (htr.hasAltPath_of_fresh_segment hinit (start := 0) (by omega) hu0
      fun d hd k hk heq => ?_)
    simp only [Nat.zero_add] at hk heq
    exact hrev1 ⟨d, by omega, k, Finset.mem_range.mpr hk, heq⟩

/-- **Pagh & Rodler (2004), Section 2.3, Lemma 1 (bicyclic form)**:
If `pureEvict h₁ h₂ r tbl₀ e₀ = none` (`1 ≤ r`) from a valid placement `tbl₀` of `S` with
`e₀.key = u ∉ S`, then either `HasAltPath h₁ h₂ S u ((2 * r + 2) / 3)` holds or there is some
`L ∈ Finset.Ico 2 (2 * r)` with `HasBicyclicPrefix h₁ h₂ S u L`. -/
theorem cuckooWalk_dichotomy_bicyclic {U m r : ℕ} {h₁ h₂ : Fin U → Fin m}
    {S : Finset (Fin U)} {u : Fin U} {tbl₀ : PureTable U m} {e₀ : SlotEntry U}
    (hr : 1 ≤ r) (hvp : ValidPlacement h₁ h₂ S tbl₀) (hu : u ∉ S) (he₀ : e₀.key = u)
    (hev : pureEvict h₁ h₂ r tbl₀ e₀ = none) :
    HasAltPath h₁ h₂ S u ((2 * r + 2) / 3) ∨
      ∃ L ∈ Finset.Ico 2 (2 * r), HasBicyclicPrefix h₁ h₂ S u L := by
  obtain ⟨f, es, hf0, hes0, htr⟩ := exists_rawWalkTrace_of_pureEvict_eq_none r hvp.1
    (fun hkey => hu (hvp.2 u (he₀ ▸ hkey))) hev
  exact htr.dichotomy (by omega) (by rw [hes0, he₀]) fun s d hread =>
    hvp.2 d.key ⟨d, readSlot_some_imp_entryIn (hf0 ▸ hread), rfl⟩

/-- **Pagh & Rodler (2004), Section 2.3, Lemma 1 (excess-subset form)**:
If `pureEvict h₁ h₂ r tbl₀ e₀ = none` (`1 ≤ r`) from a valid placement `tbl₀` of `S` with
`e₀.key = u ∉ S`, then either `HasAltPath h₁ h₂ S u ((2 * r + 2) / 3)` (Case B) or
`HasExcessSubset h₁ h₂ S u (2 * r)` (Case A) holds. -/
theorem cuckooWalk_dichotomy {U m r : ℕ} {h₁ h₂ : Fin U → Fin m}
    {S : Finset (Fin U)} {u : Fin U} {tbl₀ : PureTable U m} {e₀ : SlotEntry U}
    (hr : 1 ≤ r) (hvp : ValidPlacement h₁ h₂ S tbl₀) (hu : u ∉ S) (he₀ : e₀.key = u)
    (hev : pureEvict h₁ h₂ r tbl₀ e₀ = none) :
    HasAltPath h₁ h₂ S u ((2 * r + 2) / 3) ∨ HasExcessSubset h₁ h₂ S u (2 * r) :=
  (cuckooWalk_dichotomy_bicyclic hr hvp hu he₀ hev).imp_right fun ⟨_, hL, hbic⟩ =>
    hasBicyclicPrefix_imp_hasExcessSubset (Finset.mem_Ico.mp hL).1 (Finset.mem_Ico.mp hL).2 hbic

/-- If `r < evictRounds h₁ h₂ maxLoop tbl e`, then `pureEvict h₁ h₂ r tbl e = none`. -/
private theorem pureEvict_eq_none_of_lt_evictRounds {U m : ℕ} (h₁ h₂ : Fin U → Fin m) :
    ∀ {r maxLoop : ℕ} {tbl : PureTable U m} {e : SlotEntry U},
      r < evictRounds h₁ h₂ maxLoop tbl e → pureEvict h₁ h₂ r tbl e = none
  | 0, _, _, _, _ => rfl
  | r + 1, 0, _, _, hlt => by simp [evictRounds] at hlt
  | r + 1, fuel + 1, tbl, e, hlt => by
    unfold evictRounds at hlt
    unfold pureEvict
    rcases h : pureEvictRound h₁ h₂ tbl e with ⟨tbl', _ | e'⟩ <;> rw [h] at hlt <;>
      dsimp only at hlt ⊢
    · omega
    · exact pureEvict_eq_none_of_lt_evictRounds h₁ h₂ (maxLoop := fuel) (by omega)

/-- If `1 ≤ r` and `r < cuckooWalkRounds h₁ h₂ maxLoop S u` with `u ∉ S`, then either
`HasAltPath h₁ h₂ S u ((2 * r + 2) / 3)` holds or there is `L ∈ Finset.Ico 2 (2 * r)` with
`HasBicyclicPrefix h₁ h₂ S u L`. -/
theorem lt_cuckooWalkRounds_imp_dichotomy {U m maxLoop r : ℕ} {h₁ h₂ : Fin U → Fin m}
    {S : Finset (Fin U)} {u : Fin U} (hr : 1 ≤ r) (hu : u ∉ S)
    (hlt : r < cuckooWalkRounds h₁ h₂ maxLoop S u) :
    HasAltPath h₁ h₂ S u ((2 * r + 2) / 3) ∨
      ∃ L ∈ Finset.Ico 2 (2 * r), HasBicyclicPrefix h₁ h₂ S u L := by
  unfold cuckooWalkRounds at hlt
  obtain ⟨r', ⟨tbl, hvp, idx, rfl⟩, hr'⟩ := exists_lt_of_lt_csSup (by exact ⟨_, PureTable.empty U m,
    ⟨wellPlaced_empty h₁ h₂, fun k hk => (not_hasKey_empty k hk).elim⟩, 0, rfl⟩) hlt
  exact cuckooWalk_dichotomy_bicyclic hr hvp hu rfl (pureEvict_eq_none_of_lt_evictRounds h₁ h₂ hr')

/-! ## Section 3: Seed-count tail bounds and rehash union bounds -/

/-- Whether some `L ∈ [2, 2 * r)` satisfies `HasBicyclicPrefix h₁ h₂ S u L`. -/
private def HasSomeBicyclicPrefix {U m : ℕ} (h₁ h₂ : Fin U → Fin m) (S : Finset (Fin U)) (u : Fin U)
    (r : ℕ) : Prop :=
  ∃ L ∈ Finset.Ico 2 (2 * r), HasBicyclicPrefix h₁ h₂ S u L

private instance {U m : ℕ} (h₁ h₂ : Fin U → Fin m) (S : Finset (Fin U)) (u : Fin U) (r : ℕ) :
    Decidable (HasSomeBicyclicPrefix h₁ h₂ S u r) := by
  unfold HasSomeBicyclicPrefix
  infer_instance

/-- Bad-walk event at round `r` for key `u` and set `S`: either `HasAltPath` of length
`(2 * r + 2) / 3` or `HasSomeBicyclicPrefix` at round `r`. -/
private def WalkBadAt {U m : ℕ} (h₁ h₂ : Fin U → Fin m) (S : Finset (Fin U)) (u : Fin U) (r : ℕ) :
    Prop :=
  HasAltPath h₁ h₂ S u ((2 * r + 2) / 3) ∨ HasSomeBicyclicPrefix h₁ h₂ S u r

private instance {U m : ℕ} (h₁ h₂ : Fin U → Fin m) (S : Finset (Fin U)) (u : Fin U) (r : ℕ) :
    Decidable (WalkBadAt h₁ h₂ S u r) := by
  unfold WalkBadAt
  infer_instance

private theorem walkBadAt_card_le {Θ₁ Θ₂ : Type*} [Fintype Θ₁] [Fintype Θ₂]
    {U m r : ℕ}
    (h₁ : Θ₁ → Fin U → Fin m) (h₂ : Θ₂ → Fin U → Fin m)
    (S : Finset (Fin U)) (u : Fin U) :
    #{θ : Θ₁ × Θ₂ | WalkBadAt (h₁ θ.1) (h₂ θ.2) S u r} ≤
      #{θ : Θ₁ × Θ₂ | HasAltPath (h₁ θ.1) (h₂ θ.2) S u ((2 * r + 2) / 3)} +
        #{θ : Θ₁ × Θ₂ | HasSomeBicyclicPrefix (h₁ θ.1) (h₂ θ.2) S u r} := by
  classical
  refine (Finset.card_le_card fun θ hθ => ?_).trans (Finset.card_union_le _ _)
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hθ ⊢
  exact hθ

/-- If replaying `ks` succeeds and replaying `ks ++ [u]` fails (with `ks.Nodup`, `u ∉ ks`, and
`1 ≤ maxLoop`), then `WalkBadAt h₁ h₂ ks.toFinset u maxLoop` holds. -/
private theorem step_rehash_imp_walkBadAt {U m maxLoop : ℕ} {h₁ h₂ : Fin U → Fin m}
    (hloop : 1 ≤ maxLoop) {ks : List (Fin U)} {u : Fin U}
    (hnodup : ks.Nodup) (hu : u ∉ ks)
    (hstep : (pureReplay h₁ h₂ maxLoop ks).isSome ∧
      (pureReplay h₁ h₂ maxLoop (ks ++ [u])).isNone) :
    WalkBadAt h₁ h₂ ks.toFinset u maxLoop := by
  obtain ⟨tbl, hrep⟩ := Option.isSome_iff_exists.mp hstep.1
  have hev := hstep.2
  rw [pureReplay_append_singleton, hrep, Option.bind_some, Option.isNone_iff_eq_none] at hev
  exact cuckooWalk_dichotomy_bicyclic hloop
    (pureReplay_validPlacement hnodup (fun v hv => List.mem_toFinset.mpr hv) hrep)
    (fun h => hu (List.mem_toFinset.mp h)) rfl hev

/-- If `¬ GoodForSet h₁ h₂ maxLoop S` (`1 ≤ maxLoop`), then there is some key `u ∈ S` such that
`WalkBadAt h₁ h₂ (S.erase u) u maxLoop` holds. -/
private theorem not_goodForSet_imp_exists_walkBadAt {U m maxLoop : ℕ} {h₁ h₂ : Fin U → Fin m}
    (hloop : 1 ≤ maxLoop) {S : Finset (Fin U)}
    (hbad : ¬ GoodForSet h₁ h₂ maxLoop S) :
    ∃ u ∈ S, WalkBadAt h₁ h₂ (S.erase u) u maxLoop := by
  unfold GoodForSet at hbad
  push Not at hbad
  rcases hbad with ⟨ks, hnodup, hsub, hnone⟩
  induction ks using List.reverseRecOn with
  | nil => simp [pureReplay] at hnone
  | append_singleton ks u ih =>
    rw [List.nodup_append_comm, List.singleton_append, List.nodup_cons] at hnodup
    have hsub_ks : ∀ v ∈ ks, v ∈ S := fun v hv => hsub v (List.mem_append_left [u] hv)
    by_cases hrep : (pureReplay h₁ h₂ maxLoop ks).isSome
    · have hsub_erase : ∀ v ∈ ks.toFinset, v ∈ S.erase u := fun v hv => Finset.mem_erase.mpr
        ⟨fun hvu => hnodup.1 (hvu ▸ List.mem_toFinset.mp hv), hsub_ks v (List.mem_toFinset.mp hv)⟩
      refine ⟨u, hsub u (by simp), ?_⟩
      rcases step_rehash_imp_walkBadAt hloop hnodup.2 hnodup.1 ⟨hrep, by simpa using hnone⟩ with
        ⟨b, y, hinj, hy0, hymem, heq⟩ | ⟨L, hL, p, s, j, y, hidx, hinj, hy0, hymem, heq⟩
      · exact Or.inl ⟨b, y, hinj, hy0, fun i => hsub_erase _ (hymem i), heq⟩
      · exact Or.inr ⟨L, hL, p, s, j, y, hidx, hinj, hy0, fun i => hsub_erase _ (hymem i), heq⟩
    · exact ih hnodup.2 hsub_ks hrep

/-- Elementary dyadic sum bound in `ℕ`: if `2 ^ (r + 1) * f r ≤ M` for all `r < K`, then
`2 ^ K * (∑ r ∈ Finset.range K, f r) + M ≤ 2 ^ K * M`, and in particular
`∑ r ∈ Finset.range K, f r ≤ M`. -/
private theorem two_pow_mul_sum_range_add_le {f : ℕ → ℕ} {M : ℕ} :
    ∀ (K : ℕ), (∀ r < K, 2 ^ (r + 1) * f r ≤ M) →
      2 ^ K * (∑ r ∈ Finset.range K, f r) + M ≤ 2 ^ K * M
  | 0, _ => by simp
  | K + 1, hle => by
    have ih := two_pow_mul_sum_range_add_le K fun r hr => hle r (by omega)
    have hK := hle K (by omega)
    rw [Finset.sum_range_succ]
    rw [pow_succ'] at hK ⊢
    linarith

private theorem sum_range_le_of_two_pow_mul_le {f : ℕ → ℕ} {M K : ℕ}
    (hle : ∀ r < K, 2 ^ (r + 1) * f r ≤ M) :
    ∑ r ∈ Finset.range K, f r ≤ M := by
  have h1 := two_pow_mul_sum_range_add_le K hle
  exact Nat.le_of_mul_le_mul_left (by omega) (Nat.two_pow_pos K)

private theorem two_pow_le_thirty_two_pow {e ℓ : ℕ} (h : e ≤ 5 * ℓ) : 2 ^ e ≤ 32 ^ ℓ :=
  (Nat.pow_le_pow_right two_pos h).trans_eq (pow_mul 2 5 ℓ)

/-- Elementary polynomial-vs-exponential bound `(d + 3) ^ 3 ≤ 27 * 4 ^ d` for all `d : ℕ`. -/
private theorem add_three_pow_three_le : ∀ d : ℕ, (d + 3) ^ 3 ≤ 27 * 4 ^ d
  | 0 => by decide
  | d + 1 => by
    have ih := add_three_pow_three_le d
    grind

/-- Under `32 * max n_max 4 ≤ m` and `S.card ≤ max n_max 4`, the number of seeds satisfying
`HasAltPath` of length `ℓ` (`ℓ + 1 ≤ k`) satisfies
`32 ^ ℓ * #{θ | HasAltPath ... ℓ} ≤ 2 * Fintype.card (Θ₁ × Θ₂)`. -/
private theorem thirty_two_pow_mul_card_hasAltPath_le {Θ₁ Θ₂ : Type*} [Fintype Θ₁] [Fintype Θ₂]
    {U m k n_max ℓ : ℕ}
    {h₁ : Θ₁ → Fin U → Fin m} {h₂ : Θ₂ → Fin U → Fin m}
    (hk₁ : IsKWiseIndependentHash k h₁) (hk₂ : IsKWiseIndependentHash k h₂)
    (hm : 32 * max n_max 4 ≤ m)
    {S : Finset (Fin U)} (hS : S.card ≤ max n_max 4) (u : Fin U) (hℓk : ℓ + 1 ≤ k) :
    32 ^ ℓ * #{θ : Θ₁ × Θ₂ | HasAltPath (h₁ θ.1) (h₂ θ.2) S u ℓ} ≤
      2 * Fintype.card (Θ₁ × Θ₂) := by
  have h1 := card_filter_hasAltPath_le (show 0 < m by omega) hk₁ hk₂ S u hℓk
  generalize #{θ : Θ₁ × Θ₂ | HasAltPath (h₁ θ.1) (h₂ θ.2) S u ℓ} = A at h1 ⊢
  refine Nat.le_of_mul_le_mul_right (c := max n_max 4 ^ ℓ) ?_ (by positivity)
  calc 32 ^ ℓ * A * max n_max 4 ^ ℓ = (32 * max n_max 4) ^ ℓ * A := by ring
    _ ≤ m ^ ℓ * A := by gcongr
    _ ≤ 2 * S.card ^ ℓ * Fintype.card (Θ₁ × Θ₂) := h1
    _ ≤ 2 * Fintype.card (Θ₁ × Θ₂) * max n_max 4 ^ ℓ := by rw [mul_right_comm]; gcongr

/-- Under `32 * max n_max 4 ≤ m` and `S.card ≤ max n_max 4`, the number of seeds satisfying
`HasBicyclicPrefix` of length `L = d + 2` (`d + 3 ≤ k`) satisfies
`32 * m ^ 2 * 8 ^ d * #{θ | HasBicyclicPrefix ... (d + 2)} ≤ Fintype.card (Θ₁ × Θ₂)`. -/
private theorem card_hasBicyclicPrefix_add_two_le {Θ₁ Θ₂ : Type*} [Fintype Θ₁] [Fintype Θ₂]
    {U m k n_max d : ℕ}
    {h₁ : Θ₁ → Fin U → Fin m} {h₂ : Θ₂ → Fin U → Fin m}
    (hk₁ : IsKWiseIndependentHash k h₁) (hk₂ : IsKWiseIndependentHash k h₂)
    (hm : 32 * max n_max 4 ≤ m)
    {S : Finset (Fin U)} (hS : S.card ≤ max n_max 4) (u : Fin U) (hdk : d + 3 ≤ k) :
    32 * m ^ 2 * 8 ^ d * #{θ : Θ₁ × Θ₂ | HasBicyclicPrefix (h₁ θ.1) (h₂ θ.2) S u (d + 2)} ≤
      Fintype.card (Θ₁ × Θ₂) := by
  have h1 := card_filter_hasBicyclicPrefix_le (show 0 < m by omega) hk₁ hk₂ S u hdk
  generalize #{θ : Θ₁ × Θ₂ | HasBicyclicPrefix (h₁ θ.1) (h₂ θ.2) S u (d + 2)} = A at h1 ⊢
  have hcube : (d + 2 + 1) ^ 3 ≤ 32 * 4 ^ d :=
    (add_three_pow_three_le d).trans (Nat.mul_le_mul_right _ (by decide))
  refine Nat.le_of_mul_le_mul_right (c := 32 * 4 ^ d * max n_max 4 ^ (d + 2)) ?_ (by positivity)
  calc 32 * m ^ 2 * 8 ^ d * A * (32 * 4 ^ d * max n_max 4 ^ (d + 2))
      = m ^ 2 * (32 * max n_max 4) ^ (d + 2) * A := by
        rw [mul_pow, pow_add 32 d 2, show (32 : ℕ) ^ d = 8 ^ d * 4 ^ d from mul_pow 8 4 d]
        ring
    _ ≤ m ^ 2 * m ^ (d + 2) * A := by gcongr
    _ = m ^ (d + 2 + 2) * A := by ring
    _ ≤ (d + 2 + 1) ^ 3 * S.card ^ (d + 2) * Fintype.card (Θ₁ × Θ₂) := h1
    _ ≤ Fintype.card (Θ₁ × Θ₂) * (32 * 4 ^ d * max n_max 4 ^ (d + 2)) := by
        rw [mul_comm]
        gcongr

/-- Union-bounding `HasBicyclicPrefix` over all `L ∈ Finset.Ico 2 (2 * r)` (`2 * r + 1 ≤ k`) yields
`4 * m ^ 2 * #{θ | HasSomeBicyclicPrefix ... r} ≤ Fintype.card (Θ₁ × Θ₂)`. -/
private theorem four_mul_m_sq_card_hasSomeBicyclicPrefix_le {Θ₁ Θ₂ : Type*}
    [Fintype Θ₁] [Fintype Θ₂] {U m k n_max r : ℕ}
    {h₁ : Θ₁ → Fin U → Fin m} {h₂ : Θ₂ → Fin U → Fin m}
    (hk₁ : IsKWiseIndependentHash k h₁) (hk₂ : IsKWiseIndependentHash k h₂)
    (hm : 32 * max n_max 4 ≤ m)
    {S : Finset (Fin U)} (hS : S.card ≤ max n_max 4) (u : Fin U) (hrk : 2 * r + 1 ≤ k) :
    4 * m ^ 2 *
      #{θ : Θ₁ × Θ₂ | HasSomeBicyclicPrefix (h₁ θ.1) (h₂ θ.2) S u r} ≤
      Fintype.card (Θ₁ × Θ₂) := by
  classical
  have hsub : ({θ | HasSomeBicyclicPrefix (h₁ θ.1) (h₂ θ.2) S u r} : Finset (Θ₁ × Θ₂)) ⊆
      (Finset.range (2 * r - 2)).biUnion fun d =>
        {θ | HasBicyclicPrefix (h₁ θ.1) (h₂ θ.2) S u (d + 2)} := fun θ hθ => by
    obtain ⟨L, hL, hbic⟩ := (Finset.mem_filter.mp hθ).2
    rw [Finset.mem_Ico] at hL
    exact Finset.mem_biUnion.mpr ⟨L - 2, Finset.mem_range.mpr (by omega),
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rwa [Nat.sub_add_cancel hL.1]⟩⟩
  refine (Nat.mul_le_mul_left _ ((Finset.card_le_card hsub).trans Finset.card_biUnion_le)).trans ?_
  rw [Finset.mul_sum]
  refine sum_range_le_of_two_pow_mul_le fun d hd => ?_
  calc 2 ^ (d + 1) * (4 * m ^ 2 * _) ≤ 8 ^ (d + 1) * (4 * m ^ 2 * _) := by gcongr; norm_num
    _ = 32 * m ^ 2 * 8 ^ d * _ := by ring
    _ ≤ _ := card_hasBicyclicPrefix_add_two_le hk₁ hk₂ hm hS u (by omega)

/-- Summing `WalkBadAt` seed counts over `1 ≤ r < MaxLoop` yields at most
`Fintype.card (Θ₁ × Θ₂)`. -/
private theorem sum_walkBadAt_le {Θ₁ Θ₂ : Type*} [Fintype Θ₁] [Fintype Θ₂]
    {U m n_max MaxLoop : ℕ}
    {h₁ : Θ₁ → Fin U → Fin m} {h₂ : Θ₂ → Fin U → Fin m}
    (hk₁ : IsKWiseIndependentHash (2 * MaxLoop + 2) h₁)
    (hk₂ : IsKWiseIndependentHash (2 * MaxLoop + 2) h₂)
    (hm : 32 * max n_max 4 ≤ m) (hloop_le : MaxLoop ≤ m)
    {S : Finset (Fin U)} (hS : S.card ≤ max n_max 4) (u : Fin U) :
    ∑ r ∈ Finset.Ico 1 MaxLoop,
      #{θ : Θ₁ × Θ₂ | WalkBadAt (h₁ θ.1) (h₂ θ.2) S u r} ≤
      Fintype.card (Θ₁ × Θ₂) := by
  have halt : ∀ i < MaxLoop - 1, 2 ^ (i + 1) * (2 * #{θ : Θ₁ × Θ₂ |
      HasAltPath (h₁ θ.1) (h₂ θ.2) S u ((2 * (1 + i) + 2) / 3)}) ≤ Fintype.card (Θ₁ × Θ₂) := by
    intro i hi
    have hstep := thirty_two_pow_mul_card_hasAltPath_le hk₁ hk₂ hm hS u
      (ℓ := (2 * (1 + i) + 2) / 3) (by omega)
    have hpow : 4 * 2 ^ (i + 1) ≤ 32 ^ ((2 * (1 + i) + 2) / 3) :=
      (by ring : 4 * 2 ^ (i + 1) = 2 ^ (i + 3)).trans_le (two_pow_le_thirty_two_pow (by omega))
    generalize #{θ : Θ₁ × Θ₂ | HasAltPath (h₁ θ.1) (h₂ θ.2) S u ((2 * (1 + i) + 2) / 3)} = A
      at hstep ⊢
    linarith [Nat.mul_le_mul_right A hpow]
  have hbic : ∀ i ∈ Finset.range (MaxLoop - 1), 2 * m * #{θ : Θ₁ × Θ₂ |
      HasSomeBicyclicPrefix (h₁ θ.1) (h₂ θ.2) S u (1 + i)} ≤ Fintype.card (Θ₁ × Θ₂) := by
    intro i hi
    rw [Finset.mem_range] at hi
    exact (Nat.mul_le_mul_right _ (by nlinarith : 2 * m ≤ 4 * m ^ 2)).trans
      (four_mul_m_sq_card_hasSomeBicyclicPrefix_le hk₁ hk₂ hm hS u (r := 1 + i) (by omega))
  have h1 := sum_range_le_of_two_pow_mul_le halt
  have h2 := Finset.sum_le_card_nsmul _ _ _ hbic
  have h3 := Finset.sum_le_sum fun i (_ : i ∈ Finset.range (MaxLoop - 1)) =>
    walkBadAt_card_le h₁ h₂ S u (r := 1 + i)
  rw [← Finset.mul_sum] at h1 h2
  rw [Finset.card_range, smul_eq_mul] at h2
  rw [Finset.sum_add_distrib] at h3
  have hK := Nat.mul_le_mul_right (Fintype.card (Θ₁ × Θ₂)) (show MaxLoop - 1 ≤ m by omega)
  have h2' : 2 * ∑ i ∈ Finset.range (MaxLoop - 1),
      #{θ : Θ₁ × Θ₂ | HasSomeBicyclicPrefix (h₁ θ.1) (h₂ θ.2) S u (1 + i)} ≤
        Fintype.card (Θ₁ × Θ₂) :=
    Nat.le_of_mul_le_mul_left (by linarith) (show 0 < m by omega)
  rw [Finset.sum_Ico_eq_sum_range]
  omega

/-- Every `c ≤ MaxLoop` is bounded by `1 + #{r ∈ Ico 1 MaxLoop | r < c}`. -/
private theorem le_one_add_card_filter_Ico {c MaxLoop : ℕ} (hc : c ≤ MaxLoop) :
    c ≤ 1 + ((Finset.Ico 1 MaxLoop).filter (fun r => r < c)).card := by
  have hfilter : (Finset.Ico 1 MaxLoop).filter (fun r => r < c) = Finset.Ico 1 c := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_Ico]
    omega
  rw [hfilter, Nat.card_Ico]
  omega

/-- The sum of `cuckooWalkRounds` over all seed pairs in `Θ₁ × Θ₂` is at most
`2 * Fintype.card (Θ₁ × Θ₂)`. -/
private theorem sum_cuckooWalkRounds_le {Θ₁ Θ₂ : Type*} [Fintype Θ₁] [Fintype Θ₂]
    {U m n_max MaxLoop : ℕ}
    {h₁ : Θ₁ → Fin U → Fin m} {h₂ : Θ₂ → Fin U → Fin m}
    (hk₁ : IsKWiseIndependentHash (2 * MaxLoop + 2) h₁)
    (hk₂ : IsKWiseIndependentHash (2 * MaxLoop + 2) h₂)
    (hm : 32 * max n_max 4 ≤ m) (hloop_le : MaxLoop ≤ m)
    {S : Finset (Fin U)} (hS : S.card < n_max) {u : Fin U} (hu : u ∉ S) :
    ∑ θ : Θ₁ × Θ₂, cuckooWalkRounds (h₁ θ.1) (h₂ θ.2) MaxLoop S u ≤
      2 * Fintype.card (Θ₁ × Θ₂) := by
  classical
  have htail := sum_walkBadAt_le hk₁ hk₂ hm hloop_le (show S.card ≤ max n_max 4 by omega) u
  calc ∑ θ : Θ₁ × Θ₂, cuckooWalkRounds (h₁ θ.1) (h₂ θ.2) MaxLoop S u
      ≤ ∑ θ : Θ₁ × Θ₂, (1 + ∑ r ∈ Finset.Ico 1 MaxLoop,
          if r < cuckooWalkRounds (h₁ θ.1) (h₂ θ.2) MaxLoop S u then 1 else 0) :=
        Finset.sum_le_sum fun θ _ => by
          rw [← Finset.card_filter]
          exact le_one_add_card_filter_Ico (cuckooWalkRounds_le_maxLoop ..)
    _ = Fintype.card (Θ₁ × Θ₂) + ∑ r ∈ Finset.Ico 1 MaxLoop,
          #{θ : Θ₁ × Θ₂ | r < cuckooWalkRounds (h₁ θ.1) (h₂ θ.2) MaxLoop S u} := by
        simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one,
          Finset.card_filter]
        rw [Finset.sum_comm]
    _ ≤ Fintype.card (Θ₁ × Θ₂) + ∑ r ∈ Finset.Ico 1 MaxLoop,
          #{θ : Θ₁ × Θ₂ | WalkBadAt (h₁ θ.1) (h₂ θ.2) S u r} :=
        Nat.add_le_add_left (Finset.sum_le_sum fun r hr => Finset.card_le_card
          (Finset.monotone_filter_right _ fun θ _ hθ =>
            lt_cuckooWalkRounds_imp_dichotomy (Finset.mem_Ico.mp hr).1 hu hθ)) _
    _ ≤ 2 * Fintype.card (Θ₁ × Θ₂) := by omega

/-- At `r = MaxLoop ≥ maxEvictions n_max`, the number of seeds satisfying `WalkBadAt` is bounded by
`2 * (max n_max 1 * max MaxLoop 1) * #{θ | WalkBadAt ... MaxLoop} ≤ Fintype.card (Θ₁ × Θ₂)`. -/
private theorem two_mul_walkBadAt_maxLoop_le {Θ₁ Θ₂ : Type*} [Fintype Θ₁] [Fintype Θ₂]
    {U m n_max MaxLoop : ℕ}
    {h₁ : Θ₁ → Fin U → Fin m} {h₂ : Θ₂ → Fin U → Fin m}
    (hk₁ : IsKWiseIndependentHash (2 * MaxLoop + 2) h₁)
    (hk₂ : IsKWiseIndependentHash (2 * MaxLoop + 2) h₂)
    (hm : 32 * max n_max 4 ≤ m)
    (hloop_ge : maxEvictions n_max ≤ MaxLoop) (hloop_le : MaxLoop ≤ m)
    {S : Finset (Fin U)} (hS : S.card ≤ max n_max 4) (u : Fin U) :
    2 * (max n_max 1 * max MaxLoop 1) *
      #{θ : Θ₁ × Θ₂ | WalkBadAt (h₁ θ.1) (h₂ θ.2) S u MaxLoop} ≤
      Fintype.card (Θ₁ × Θ₂) := by
  have h18 : 18 ≤ MaxLoop := (eighteen_le_maxEvictions n_max).trans hloop_ge
  have hdef : 6 * (Nat.clog 2 (max n_max 2) + 2) ≤ MaxLoop := hloop_ge
  have hbad := walkBadAt_card_le h₁ h₂ S u (r := MaxLoop)
  have halt := thirty_two_pow_mul_card_hasAltPath_le hk₁ hk₂ hm hS u
    (ℓ := (2 * MaxLoop + 2) / 3) (by omega)
  have hbic := four_mul_m_sq_card_hasSomeBicyclicPrefix_le hk₁ hk₂ hm hS u (r := MaxLoop)
    (by omega)
  have hpow : 8 * (max n_max 1 * max MaxLoop 1) ≤ 32 ^ ((2 * MaxLoop + 2) / 3) :=
    calc 8 * (max n_max 1 * max MaxLoop 1)
        ≤ 2 ^ 3 * (2 ^ Nat.clog 2 (max n_max 2) * 2 ^ MaxLoop) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul
            ((max_le_max_left _ one_le_two).trans (Nat.le_pow_clog one_lt_two _))
            (max_le Nat.lt_two_pow_self.le Nat.one_le_two_pow))
      _ = 2 ^ (3 + (Nat.clog 2 (max n_max 2) + MaxLoop)) := by rw [pow_add, pow_add]
      _ ≤ 32 ^ ((2 * MaxLoop + 2) / 3) := two_pow_le_thirty_two_pow (by omega)
  have hprod : max n_max 1 * max MaxLoop 1 ≤ m ^ 2 :=
    (Nat.mul_le_mul (by omega) (by omega)).trans_eq (sq m).symm
  generalize max n_max 1 * max MaxLoop 1 = B at hpow hprod ⊢
  linarith [Nat.mul_le_mul_right #{θ : Θ₁ × Θ₂ |
      HasAltPath (h₁ θ.1) (h₂ θ.2) S u ((2 * MaxLoop + 2) / 3)} hpow,
    Nat.mul_le_mul_right #{θ : Θ₁ × Θ₂ | HasSomeBicyclicPrefix (h₁ θ.1) (h₂ θ.2) S u MaxLoop}
      hprod, Nat.mul_le_mul_left B hbad]

open Classical in
/-- Union-bounding `WalkBadAt` over `u ∈ S` shows that at most a quarter of the seed pairs fail
`GoodForSet` for `S` (`S.card ≤ n_max`). -/
private theorem four_mul_card_not_goodForSet_le {Θ₁ Θ₂ : Type*} [Fintype Θ₁] [Fintype Θ₂]
    {U m n_max MaxLoop : ℕ}
    {h₁ : Θ₁ → Fin U → Fin m} {h₂ : Θ₂ → Fin U → Fin m}
    (hk₁ : IsKWiseIndependentHash (2 * MaxLoop + 2) h₁)
    (hk₂ : IsKWiseIndependentHash (2 * MaxLoop + 2) h₂)
    (hm : 32 * max n_max 4 ≤ m)
    (hloop_ge : maxEvictions n_max ≤ MaxLoop) (hloop_le : MaxLoop ≤ m)
    {S : Finset (Fin U)} (hS : S.card ≤ n_max) :
    4 * (Finset.univ.filter (fun θ : Θ₁ × Θ₂ =>
      ¬ GoodForSet (h₁ θ.1) (h₂ θ.2) MaxLoop S)).card ≤
      Fintype.card (Θ₁ × Θ₂) := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp
  · have h18 : 18 ≤ MaxLoop := (eighteen_le_maxEvictions n_max).trans hloop_ge
    have key := mul_card_filter_le_card_mul (c := 4 * S.card) (M := Fintype.card (Θ₁ × Θ₂))
      (Q := fun θ : Θ₁ × Θ₂ => ¬ GoodForSet (h₁ θ.1) (h₂ θ.2) MaxLoop S)
      (fun u : S => ({θ | WalkBadAt (h₁ θ.1) (h₂ θ.2) (S.erase u) u MaxLoop} :
        Finset (Θ₁ × Θ₂))) fun θ hθ => by
        obtain ⟨u, huS, hbad⟩ := not_goodForSet_imp_exists_walkBadAt (by omega) hθ
        refine ⟨⟨u, huS⟩, by simpa using hbad, (Nat.mul_le_mul_right _ ?_).trans
          (two_mul_walkBadAt_maxLoop_le hk₁ hk₂ hm hloop_ge hloop_le (S := S.erase u)
            (by grind) u)⟩
        nlinarith [show S.card ≤ max n_max 1 by omega, show 2 ≤ max MaxLoop 1 by omega]
    rw [Fintype.card_coe] at key
    exact Nat.le_of_mul_le_mul_left (by linarith) hne.card_pos

/-- A fresh key `u` makes the replay of `ks` rehash only when its walk is bad
(`step_rehash_imp_walkBadAt`), so under `(2 * MaxLoop + 2)`-wise independence at most a
`3 / (max n_max 1 * max MaxLoop 1)` fraction of seed pairs make that step rehash. -/
private theorem mul_card_stepRehash_le {Θ₁ Θ₂ : Type*} [Fintype Θ₁] [Fintype Θ₂]
    {U m n_max MaxLoop : ℕ}
    {h₁ : Θ₁ → Fin U → Fin m} {h₂ : Θ₂ → Fin U → Fin m}
    (hk₁ : IsKWiseIndependentHash (2 * MaxLoop + 2) h₁)
    (hk₂ : IsKWiseIndependentHash (2 * MaxLoop + 2) h₂)
    (hm : 32 * max n_max 4 ≤ m)
    (hloop_ge : maxEvictions n_max ≤ MaxLoop) (hloop_le : MaxLoop ≤ m)
    {ks : List (Fin U)} {u : Fin U}
    (hnodup : ks.Nodup) (hlen : ks.length < n_max) (hu : u ∉ ks) :
    (max n_max 1 * max MaxLoop 1) * (Finset.univ.filter (fun θ : Θ₁ × Θ₂ =>
      (pureReplay (h₁ θ.1) (h₂ θ.2) MaxLoop ks).isSome ∧
        (pureReplay (h₁ θ.1) (h₂ θ.2) MaxLoop (ks ++ [u])).isNone)).card ≤
      3 * Fintype.card (Θ₁ × Θ₂) := by
  have h18 : 18 ≤ MaxLoop := (eighteen_le_maxEvictions n_max).trans hloop_ge
  have hwalk := two_mul_walkBadAt_maxLoop_le hk₁ hk₂ hm hloop_ge hloop_le (S := ks.toFinset)
    (by have := List.toFinset_card_le ks; omega) u
  have hsub := Nat.mul_le_mul_left (max n_max 1 * max MaxLoop 1) (Finset.card_le_card
    (Finset.monotone_filter_right Finset.univ fun (θ : Θ₁ × Θ₂) _ hθ =>
      step_rehash_imp_walkBadAt (h₁ := h₁ θ.1) (h₂ := h₂ θ.2) (show 1 ≤ MaxLoop by omega)
        hnodup hu hθ))
  linarith

/-- Turns a seed count against the load factor `max n_max 1 * max MaxLoop 1` into the
`IsCuckooHashPair` form of a probability bound under the uniform seed law. -/
private theorem toOuterMeasure_le_div_maxLoad {α : Type*} [Fintype α] [Nonempty α]
    {P : α → Prop} [DecidablePred P] {n_max MaxLoop A : ℕ}
    (hle : (max n_max 1 * max MaxLoop 1) * (Finset.univ.filter P).card ≤
      A * Fintype.card α) :
    (PMF.uniformOfFintype α).toOuterMeasure {a : α | P a} ≤
      (A : ℝ≥0∞) / ((max n_max 1 : ℝ≥0∞) * (max MaxLoop 1 : ℝ≥0∞)) := by
  have hmeas := PMF.toOuterMeasure_uniformOfFintype_le_div (by positivity) hle
  rwa [Nat.cast_mul, Nat.mono_cast.map_max, Nat.mono_cast.map_max, Nat.cast_one] at hmeas

/-! ## Section 4: `IsCuckooHashPair` instances and lazy random-oracle equivalence -/

/-- **Pagh & Rodler (2004), Section 2.3 (`IsCuckooHashPair` for `(2 * MaxLoop + 2)`-wise
independent hash pairs)**:
For any capacity `n_max : ℕ`, sub-table size `m` with `32 * max n_max 4 ≤ m`, eviction cap
`MaxLoop` with `maxEvictions n_max ≤ MaxLoop ≤ m`, and independent hash families
`h₁ : Θ₁ → Fin U → Fin m` and `h₂ : Θ₂ → Fin U → Fin m` each satisfying
`IsKWiseIndependentHash (2 * MaxLoop + 2)`, the uniform product distribution on `Θ₁ × Θ₂` satisfies
`IsCuckooHashPair` with universal constants `C_walk = 2` and `C_reh = 3`. -/
theorem isCuckooHashPair_of_kWiseIndependent {Θ₁ Θ₂ : Type*}
    [Fintype Θ₁] [Nonempty Θ₁]
    [Fintype Θ₂] [Nonempty Θ₂]
    {U m : ℕ} (n_max MaxLoop : ℕ)
    {h₁ : Θ₁ → Fin U → Fin m} {h₂ : Θ₂ → Fin U → Fin m}
    (hk₁ : IsKWiseIndependentHash (2 * MaxLoop + 2) h₁)
    (hk₂ : IsKWiseIndependentHash (2 * MaxLoop + 2) h₂)
    (hm : 32 * max n_max 4 ≤ m)
    (hloop_ge : maxEvictions n_max ≤ MaxLoop) (hloop_le : MaxLoop ≤ m) :
    IsCuckooHashPair (PMF.uniformOfFintype (Θ₁ × Θ₂))
      (fun θ : Θ₁ × Θ₂ => h₁ θ.1) (fun θ : Θ₁ × Θ₂ => h₂ θ.2)
      n_max MaxLoop 2 3 where
  expected_walk_le S u hS hu :=
    mod_cast PMF.tsum_uniformOfFintype_le_of_sum_le
      (sum_cuckooWalkRounds_le hk₁ hk₂ hm hloop_le hS hu)
  rehash_prob_le_half S hS := by
    classical
    have hcard := four_mul_card_not_goodForSet_le hk₁ hk₂ hm hloop_ge hloop_le hS
    exact mod_cast PMF.toOuterMeasure_uniformOfFintype_le_div (A := 1) two_pos (by omega)
  step_rehash_prob_le ks u hnodup hlen hu :=
    toOuterMeasure_le_div_maxLoad
      (mul_card_stepRehash_le hk₁ hk₂ hm hloop_ge hloop_le hnodup hlen hu)

/-- **`IsCuckooHashPair` for two independent `trinomialPolyHash` polynomials**:
When `U ≤ 2 ^ (2 * 3 ^ t)`, `M ≤ 2 * 3 ^ t`, `32 * max n_max 4 ≤ 2 ^ M`, and
`maxEvictions n_max ≤ MaxLoop ≤ 2 ^ M`, two independent degree-`< k` (`2 * MaxLoop + 2 ≤ k`)
trinomial-field polynomial hashes `trinomialPolyHash t k U M` satisfy `IsCuckooHashPair` with
`C_walk = 2` and `C_reh = 3`. -/
theorem isCuckooHashPair_trinomialPolyHash {t k U M : ℕ}
    (hU : U ≤ 2 ^ (2 * 3 ^ t)) (hM : M ≤ 2 * 3 ^ t)
    (n_max MaxLoop : ℕ)
    (hdeg : 2 * MaxLoop + 2 ≤ k)
    (hm : 32 * max n_max 4 ≤ 2 ^ M)
    (hloop_ge : maxEvictions n_max ≤ MaxLoop) (hloop_le : MaxLoop ≤ 2 ^ M) :
    IsCuckooHashPair
      (PMF.uniformOfFintype
        ((Fin k → Fin (2 ^ (2 * 3 ^ t))) × (Fin k → Fin (2 ^ (2 * 3 ^ t)))))
      (fun θ => trinomialPolyHash t k U M θ.1)
      (fun θ => trinomialPolyHash t k U M θ.2)
      n_max MaxLoop 2 3 := by
  have hk := (isKWiseIndependentHash_trinomialPolyHash (k := k) hU hM).mono hdeg
  exact isCuckooHashPair_of_kWiseIndependent n_max MaxLoop hk hk hm hloop_ge hloop_le

/-- **`IsCuckooHashPair` for a uniform random hash pair**:
When `32 * max n_max 4 ≤ m` and `maxEvictions n_max ≤ MaxLoop ≤ m`, sampling `(h₁, h₂)` uniformly
at random from `(Fin U → Fin m) × (Fin U → Fin m)` satisfies `IsCuckooHashPair` with `C_walk = 2`
and `C_reh = 3`. -/
theorem isCuckooHashPair_uniform {U m : ℕ} [NeZero m] (n_max MaxLoop : ℕ)
    (hm : 32 * max n_max 4 ≤ m)
    (hloop_ge : maxEvictions n_max ≤ MaxLoop) (hloop_le : MaxLoop ≤ m) :
    IsCuckooHashPair
      (PMF.uniformOfFintype ((Fin U → Fin m) × (Fin U → Fin m)))
      Prod.fst Prod.snd n_max MaxLoop 2 3 := by
  have hid := isKWiseIndependentHash_id (X := Fin U) (Y := Fin m) (2 * MaxLoop + 2)
  exact isCuckooHashPair_of_kWiseIndependent n_max MaxLoop hid hid hm hloop_ge hloop_le

/-- **Lazy random-oracle equivalence for the uniform cuckoo hash pair**:
Sampling `(h₁, h₂)` eagerly from `PMF.uniformOfFintype ((Fin U → Fin m) × (Fin U → Fin m))` and
interpreting queries `(b, x) : Bool × Fin U` via `if b then h₂ x else h₁ x` has the exact same
output distribution as answering each distinct query `(b, x)` lazily on demand with an independent
uniform bucket in `Fin m` via `RandomOracle.answer`. -/
theorem uniform_interpret_eq_lazy_hashPair {U m : ℕ} [NeZero m] {α : Type}
    (program : OracleComp (fun _ : Bool × Fin U => Fin m) α) :
    (do
      let p ← PMF.uniformOfFintype ((Fin U → Fin m) × (Fin U → Fin m))
      OracleComp.interpret (fun q : Bool × Fin U => PMF.pure (if q.1 then p.2 q.2 else p.1 q.2))
        program) =
      ((OracleComp.interpret (RandomOracle.answer (fun _ => PMF.uniformOfFintype (Fin m)))
        program).run (fun _ => none)).map Prod.fst := by
  rw [← RandomOracle.uniform_interpret_eq_lazy program]
  relabel_uniform (fun (p : (Fin U → Fin m) × (Fin U → Fin m)) (q : Bool × Fin U) =>
    if q.1 then p.2 q.2 else p.1 q.2)
  · rintro ⟨f₁, g₁⟩ ⟨f₂, g₂⟩ h
    exact Prod.ext (funext fun x => congr_fun h (false, x))
      (funext fun x => congr_fun h (true, x))
  · simp [Fintype.card_prod, ← pow_add, two_mul]

/-! ## Section 5: High-probability `k`-wise independence bridge and Double Tabulation -/

private theorem card_badTopPair_le {Θ_top : Type*} [Fintype Θ_top] [DecidableEq Θ_top]
    (GoodTop : Finset Θ_top) :
    (Finset.univ \ (GoodTop ×ˢ GoodTop)).card ≤
      2 * (Fintype.card Θ_top - GoodTop.card) * Fintype.card Θ_top := by
  have hsub : Finset.univ \ (GoodTop ×ˢ GoodTop) ⊆
      (GoodTopᶜ ×ˢ Finset.univ) ∪ (Finset.univ ×ˢ GoodTopᶜ) := fun ⟨α₁, α₂⟩ h => by
    simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_product, Finset.mem_union,
      Finset.mem_compl, true_and, and_true] at h ⊢
    tauto
  refine (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans_eq ?_)
  rw [Finset.card_product, Finset.card_product, Finset.card_univ, Finset.card_compl]
  ring

private theorem sum_prodProd_le_of_goodTop {Θ_top Θ_bot : Type*}
    [Fintype Θ_top] [DecidableEq Θ_top] [Fintype Θ_bot]
    (GoodTop : Finset Θ_top)
    (f : (Θ_top × Θ_bot) × (Θ_top × Θ_bot) → ℕ)
    {C_good C_bad : ℕ}
    (hgood : ∀ α₁ ∈ GoodTop, ∀ α₂ ∈ GoodTop,
      ∑ β : Θ_bot × Θ_bot, f ((α₁, β.1), (α₂, β.2)) ≤ C_good * Fintype.card (Θ_bot × Θ_bot))
    (hbad : ∀ θ, f θ ≤ C_bad) :
    ∑ θ : (Θ_top × Θ_bot) × (Θ_top × Θ_bot), f θ ≤
      (C_good * Fintype.card (Θ_top × Θ_top) +
        (Finset.univ \ (GoodTop ×ˢ GoodTop)).card * C_bad) *
      Fintype.card (Θ_bot × Θ_bot) := by
  have hreindex : ∑ θ : (Θ_top × Θ_bot) × (Θ_top × Θ_bot), f θ =
      ∑ α : Θ_top × Θ_top, ∑ β : Θ_bot × Θ_bot, f ((α.1, β.1), (α.2, β.2)) := by
    rw [← Equiv.sum_comp (Equiv.prodProdProdComm Θ_top Θ_bot Θ_top Θ_bot).symm f,
      Fintype.sum_prod_type]
    rfl
  rw [hreindex, ← Finset.sum_sdiff (Finset.subset_univ (GoodTop ×ˢ GoodTop)), add_comm, add_mul]
  refine Nat.add_le_add ((Finset.sum_le_card_nsmul _ _ _ fun α hα =>
      hgood α.1 (Finset.mem_product.mp hα).1 α.2 (Finset.mem_product.mp hα).2).trans ?_)
    ((Finset.sum_le_card_nsmul _ _ _ fun α _ =>
      Finset.sum_le_card_nsmul _ _ _ fun β _ => hbad _).trans_eq ?_)
  · rw [smul_eq_mul, mul_left_comm, mul_assoc]
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Finset.card_le_univ _))
  · rw [smul_eq_mul, smul_eq_mul, Finset.card_univ]
    ring

private theorem sum_ite_eq_mul_card_filter {γ : Type*} [Fintype γ]
    (Q : γ → Prop) [DecidablePred Q] (K : ℕ) :
    (∑ x : γ, if Q x then K else 0) = K * (Finset.univ.filter Q).card := by
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul,
    Nat.mul_comm]

private theorem card_filter_prodProd_le_of_goodTop {Θ_top Θ_bot : Type*}
    [Fintype Θ_top] [DecidableEq Θ_top] [Fintype Θ_bot]
    (GoodTop : Finset Θ_top)
    (P : (Θ_top × Θ_bot) × (Θ_top × Θ_bot) → Prop) [DecidablePred P]
    {K A_good : ℕ}
    (hgood : ∀ α₁ ∈ GoodTop, ∀ α₂ ∈ GoodTop,
      K * (Finset.univ.filter fun β : Θ_bot × Θ_bot => P ((α₁, β.1), (α₂, β.2))).card ≤
        A_good * Fintype.card (Θ_bot × Θ_bot)) :
    K * (Finset.univ.filter P).card ≤
      (A_good * Fintype.card (Θ_top × Θ_top) +
        (Finset.univ \ (GoodTop ×ˢ GoodTop)).card * K) *
      Fintype.card (Θ_bot × Θ_bot) := by
  rw [← sum_ite_eq_mul_card_filter P K]
  refine sum_prodProd_le_of_goodTop GoodTop (fun θ => if P θ then K else 0)
    (fun α₁ hα₁ α₂ hα₂ => ?_) (fun θ => ?_)
  · rw [sum_ite_eq_mul_card_filter]
    exact hgood α₁ hα₁ α₂ hα₂
  · split_ifs <;> omega

/-- **Black-box high-probability `k`-wise independence conditioning bridge into
`IsCuckooHashPair`**:
Given a two-level hash family `H : Θ_top → Θ_bot → Fin U → Fin m` and a good top-seed set
`GoodTop : Finset Θ_top` such that:
1. `H α` is `(2 * MaxLoop + 2)`-wise independent for every `α ∈ GoodTop`, and
2. `2 * (|Θ_top| - |GoodTop|) * (max n_max 1 * max MaxLoop 1) ≤ |Θ_top|`,
under `32 * max n_max 4 ≤ m` and `maxEvictions n_max ≤ MaxLoop ≤ m`, two independent draws from
`Θ_top × Θ_bot` satisfy `IsCuckooHashPair` with constants `C_walk = 3` and `C_reh = 4`. -/
theorem isCuckooHashPair_of_whp_kWiseIndependent {Θ_top Θ_bot : Type*}
    [Fintype Θ_top] [Nonempty Θ_top]
    [Fintype Θ_bot] [Nonempty Θ_bot]
    {U m : ℕ} (n_max MaxLoop : ℕ)
    {H : Θ_top → Θ_bot → Fin U → Fin m}
    (GoodTop : Finset Θ_top)
    (hk : ∀ α ∈ GoodTop, IsKWiseIndependentHash (2 * MaxLoop + 2) (H α))
    (hwhp : 2 * (Fintype.card Θ_top - GoodTop.card) * (max n_max 1 * max MaxLoop 1) ≤
      Fintype.card Θ_top)
    (hm : 32 * max n_max 4 ≤ m)
    (hloop_ge : maxEvictions n_max ≤ MaxLoop) (hloop_le : MaxLoop ≤ m) :
    IsCuckooHashPair
      (PMF.uniformOfFintype ((Θ_top × Θ_bot) × (Θ_top × Θ_bot)))
      (fun ((top₁, bottom₁), _) => H top₁ bottom₁)
      (fun (_, (top₂, bottom₂)) => H top₂ bottom₂)
      n_max MaxLoop 3 4 := by
  classical
  have h18 : 18 ≤ MaxLoop := (eighteen_le_maxEvictions n_max).trans hloop_ge
  -- Bad top-seed pairs cost at most one extra unit of the constant: `X ≤ (A + 1) * |Θ|`.
  have hclose {X A K : ℕ} (hK : K ≤ max n_max 1 * max MaxLoop 1)
      (hX : X ≤ (A * Fintype.card (Θ_top × Θ_top) +
        (Finset.univ \ (GoodTop ×ˢ GoodTop)).card * K) * Fintype.card (Θ_bot × Θ_bot)) :
      X ≤ (A + 1) * Fintype.card ((Θ_top × Θ_bot) × (Θ_top × Θ_bot)) := by
    have hBad : (Finset.univ \ (GoodTop ×ˢ GoodTop)).card * K ≤ Fintype.card (Θ_top × Θ_top) :=
      calc _ ≤ 2 * (Fintype.card Θ_top - GoodTop.card) * Fintype.card Θ_top *
            (max n_max 1 * max MaxLoop 1) := Nat.mul_le_mul (card_badTopPair_le GoodTop) hK
        _ = 2 * (Fintype.card Θ_top - GoodTop.card) * (max n_max 1 * max MaxLoop 1) *
            Fintype.card Θ_top := by ring
        _ ≤ Fintype.card (Θ_top × Θ_top) :=
          (Nat.mul_le_mul_right _ hwhp).trans_eq (Fintype.card_prod ..).symm
    refine hX.trans ((Nat.mul_le_mul_right _ (Nat.add_le_add_left hBad _)).trans_eq ?_)
    simp only [Fintype.card_prod]
    ring
  refine ⟨fun S u hS hu => ?_, fun S hS => ?_, fun ks u hnodup hlen hu => ?_⟩
  · exact mod_cast PMF.tsum_uniformOfFintype_le_of_sum_le (hclose
      ((one_mul MaxLoop).symm.trans_le (Nat.mul_le_mul (by omega) (by omega)))
      (sum_prodProd_le_of_goodTop GoodTop
        (fun θ => cuckooWalkRounds (H θ.1.1 θ.1.2) (H θ.2.1 θ.2.2) MaxLoop S u)
        (fun α₁ hα₁ α₂ hα₂ => sum_cuckooWalkRounds_le (hk α₁ hα₁) (hk α₂ hα₂) hm hloop_le hS hu)
        (fun θ => cuckooWalkRounds_le_maxLoop (H θ.1.1 θ.1.2) (H θ.2.1 θ.2.2) MaxLoop S u)))
  · have hfilt := hclose (K := 4)
      ((show 4 ≤ 1 * 18 by decide).trans (Nat.mul_le_mul (by omega) (by omega)))
      (card_filter_prodProd_le_of_goodTop GoodTop
        (fun θ => ¬ GoodForSet (H θ.1.1 θ.1.2) (H θ.2.1 θ.2.2) MaxLoop S) (A_good := 1)
        fun α₁ hα₁ α₂ hα₂ => by
          simpa only [one_mul] using
            four_mul_card_not_goodForSet_le (hk α₁ hα₁) (hk α₂ hα₂) hm hloop_ge hloop_le hS)
    exact mod_cast PMF.toOuterMeasure_uniformOfFintype_le_div (A := 1) two_pos
      (by omega : 2 * #{θ : (Θ_top × Θ_bot) × (Θ_top × Θ_bot) |
        ¬ GoodForSet (H θ.1.1 θ.1.2) (H θ.2.1 θ.2.2) MaxLoop S} ≤ 1 * _)
  · exact toOuterMeasure_le_div_maxLoad (hclose le_rfl
      (card_filter_prodProd_le_of_goodTop GoodTop
        (fun θ => (pureReplay (H θ.1.1 θ.1.2) (H θ.2.1 θ.2.2) MaxLoop ks).isSome ∧
          (pureReplay (H θ.1.1 θ.1.2) (H θ.2.1 θ.2.2) MaxLoop (ks ++ [u])).isNone)
        (A_good := 3) fun α₁ hα₁ α₂ hα₂ =>
          mul_card_stepRehash_le (hk α₁ hα₁) (hk α₂ hα₂) hm hloop_ge hloop_le hnodup hlen hu))

/-- **`IsCuckooHashPair` for Mikkel Thorup's Double Tabulation (`[Thorup2013]`, Theorem 1(a),
p. 4)**:
When `1 ≤ c`, `U ≤ 2 ^ (c * b)`, `32 * max n_max 4 ≤ 2 ^ M`,
`maxEvictions n_max ≤ MaxLoop ≤ 2 ^ M`, and
`2 * (max n_max 1 * max MaxLoop 1) * doubleTabCodeBound c (8 * c) 4 (2 * MaxLoop + 2) ≤`
`2 ^ (3 * b)`,
two independent draws from `DoubleTabTopSeed c (8 * c) b × DoubleTabBotSeed (8 * c) b M` satisfy
`IsCuckooHashPair` with constants `C_walk = 3` and `C_reh = 4`. -/
theorem isCuckooHashPair_doubleTabHash {c b U M : ℕ}
    (hc : 1 ≤ c) (hU : U ≤ 2 ^ (c * b))
    (n_max MaxLoop : ℕ)
    (hm : 32 * max n_max 4 ≤ 2 ^ M)
    (hloop_ge : maxEvictions n_max ≤ MaxLoop) (hloop_le : MaxLoop ≤ 2 ^ M)
    (hbound : 2 * (max n_max 1 * max MaxLoop 1) *
      doubleTabCodeBound c (8 * c) 4 (2 * MaxLoop + 2) ≤ 2 ^ (3 * b)) :
    IsCuckooHashPair
      (PMF.uniformOfFintype
        ((DoubleTabTopSeed c (8 * c) b × DoubleTabBotSeed (8 * c) b M) ×
         (DoubleTabTopSeed c (8 * c) b × DoubleTabBotSeed (8 * c) b M)))
      (fun ((top₁, bottom₁), _) => doubleTabHash c (8 * c) b U M top₁ bottom₁)
      (fun (_, (top₂, bottom₂)) => doubleTabHash c (8 * c) b U M top₂ bottom₂)
      n_max MaxLoop 3 4 := by
  classical
  refine isCuckooHashPair_of_whp_kWiseIndependent n_max MaxLoop
    ({T₁ | IsKUnique (2 * MaxLoop + 2) (simpleTabTuple T₁)} :
      Finset (DoubleTabTopSeed c (8 * c) b))
    (fun T₁ hT₁ => isKWiseIndependentHash_doubleTabHash_of_isKUnique hU
      (Finset.mem_filter.mp hT₁).2) ?_ hm hloop_ge hloop_le
  rw [← Finset.card_compl, Finset.compl_filter]
  exact two_mul_card_not_isKUnique_mul_le hc (Nat.mul_pos (by omega) (by omega)) hbound

end Cslib.DataStructure.Dictionary.CuckooHashing
