/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Query.MinimumSpanningForest.Certificate.History
public import CslibFrontier.Algorithms.Lean.Query.MinimumSpanningForest.PathMaxima
public import CslibFrontier.Algorithms.Lean.Query.FreeM.Tabulate
public import CslibFrontier.Foundations.Combinatorics.SeparatingCoordinates
import CslibFrontier.Foundations.Data.Nat.Choose.Real
import Mathlib.Tactic.FieldSimp

/-!
# Estimating preferred actions

The preference estimator of [Khanna, Putterman and Song][KhannaPuttermanSong2026] (§3.5, Claim 3.12,
p. 22) as a comparison program `Cslib.Query.Certificate.estimator`, with its error count and its
comparison count. These are steps in the proof of [KhannaPuttermanSong2026] Theorem 4.1 (#8325),
not results of their own.

In a round with state `st` (spokes `σ`, forest `F`) and acting edges `I` (`mᵢ = |I|`), the
estimator

1. takes the family `A = prefFamily st I` of preference vectors that `σ` and `F` allow
   (`Cslib.Query.Certificate.prefFamily`, at most `C(mᵢ + 2n, 2n)` of them);
2. picks, without comparisons, a set `S* ⊆ I` of at most `⌈2t log |A|⌉` edges such that two vectors
   of `A` that agree on `S*` differ in at most `mᵢ / t` edges of `I`
   (`Cslib.Query.Certificate.separatingSet`, from M5's `Cslib.exists_separating_coordinates`);
3. computes the true preferences on `S*` (`Cslib.Query.Certificate.queryPref`): one call of M2's
   `Cslib.Query.pathMaxima` on `F` with the ends of the edges of `S*` as queries, then at most two
   comparisons per edge. An edge that is not projectable prefers *find*; a projectable edge whose
   ends `F` does not join (path maximum `none`) prefers *project*; otherwise, with path maximum
   `f`, it prefers *find* exactly when `f` is no heavier than one of its spokes;
4. returns a vector of `A` consistent with these answers
   (`Cslib.Query.Certificate.consistentWith`). The true vector is one, so the estimate differs from
   it in at most `mᵢ / t` edges (`Cslib.Query.Certificate.card_estimator_ne_pref_le`).

The comparisons of a round number at most `16 |F| + 7 |S*|`
(`Cslib.Query.Certificate.countQueries_estimator_le`), so at most `16 n + 49 t √(mᵢ n)`, and over
the `t²` rounds of a call at most `16 t² n + 49 t² √(m n)` by Cauchy–Schwarz
(`Cslib.Query.Certificate.sum_countQueries_estimator_le`). Over a call, at most `m / t` edges act
with a wrong estimate (`Cslib.Query.Certificate.card_estimate_ne_prefSeq_le`).

**Deviations from the paper.** The paper samples `k = 2t (log |A| + 1)` edges; M5's bound
`⌈2t log |A|⌉` needs no `+ 1`. A round with no acting edge has `S* = ∅` and makes only the
comparisons of `pathMaxima` on `F` with no query; the paper's `O(n)` covers them.

## Main definitions

* `Cslib.Query.Certificate.queryPref`, `Cslib.Query.Certificate.separatingSet`,
  `Cslib.Query.Certificate.consistentWith`, `Cslib.Query.Certificate.estimator`.

## Main results

* `Cslib.Query.Certificate.eval_queryPref`: the queried preferences are the true ones.
* `Cslib.Query.Certificate.card_estimator_ne_pref_le`: **Claim 3.12** and its use, at most
  `mᵢ / t` errors per round.
* `Cslib.Query.Certificate.countQueries_estimator_le_real`: at most `16 n + 49 t √(mᵢ n)`
  comparisons per round.
* `Cslib.Query.Certificate.sum_countQueries_estimator_le`,
  `Cslib.Query.Certificate.card_estimate_ne_prefSeq_le`: the totals over a call (p. 22).

## References

* [S. Khanna, A. Putterman and J. Song, *A Deterministic Linear Time Algorithm for Minimum
  Spanning Tree*][KhannaPuttermanSong2026], §3.5, p. 22.
-/

public section

namespace Cslib.Query.Certificate

open Finset Multigraph

variable {V E W : Type} [DecidableEq V] [DecidableEq E]

/-! ### The program -/

/-- The ends of `e` as an ordered pair: a fixed representative of `st.ends e`. -/
noncomputable def endsPair (st : State V E) (e : E) : V × V :=
  Quot.out (st.ends e)

omit [DecidableEq V] [DecidableEq E] in
theorem ends_eq_endsPair (st : State V E) (e : E) :
    st.ends e = s((endsPair st e).1, (endsPair st e).2) :=
  (Quot.out_eq _).symm

/-- Whether some edge of the list weighs at least `f`, one comparison per edge, stopping at the
first such edge. -/
private def anyGe (f : E) : List E → FreeM (LEQuery E) Bool
  | [] => pure false
  | s :: l => do if ← LEQuery.ask f s then pure true else anyGe f l

open scoped Classical in
/-- **The true preference of an edge** `e` (p. 22), from the path maxima `pm` of the forest:
*find* when `e` is not projectable; otherwise *project* when the forest does not join its ends,
and else *find* exactly when the path maximum is no heavier than one of the spokes of `e`. -/
noncomputable def queryPref (st : State V E) (pm : V → V → Option E) (e : E) :
    FreeM (LEQuery E) Action :=
  if Projectable st e then
    match pm (endsPair st e).1 (endsPair st e).2 with
    | none => pure .project
    | some f => do if ← anyGe f (spokes st e).toList then pure .find else pure .project
  else pure .find

open scoped Classical in
/-- **The separating set** `S*` of Claim 3.12 (p. 22): edges of `I`, at most `⌈2t log |A|⌉` of
them, on which two vectors of `A` agreeing differ in at most `|I| / t` edges of `I`. It is chosen
by M5's `Cslib.exists_separating_coordinates`, without comparisons; it is empty when `t = 0`. -/
noncomputable def separatingSet (t : ℕ) (I : Finset E) (A : Finset (E → Action)) : Finset E :=
  if ht : 0 < t then
    (exists_separating_coordinates I A (t := (t : ℝ)) (by exact_mod_cast ht)).choose
  else ∅

open scoped Classical in
/-- A vector of `A` consistent with the answers `ans` on `S` (p. 22), if any. -/
noncomputable def consistentWith (A : Finset (E → Action)) (S : Finset E)
    (ans : E → Option Action) : E → Action :=
  if h : ∃ b ∈ A, ∀ e ∈ S, ans e = some (b e) then h.choose else fun _ => .find

/-- **The preference estimator** (§3.5, p. 22): compute the true preferences on the separating set
`S*` of the family `prefFamily st I`, by one path maxima computation on the forest and at most two
comparisons per edge, and return a vector of the family consistent with them. -/
noncomputable def estimator (γ : ℕ) (inst : Instance V E) (st : State V E) (I : Finset E) :
    FreeM (LEQuery E) (E → Action) := do
  let S := separatingSet (levelT γ inst.level) I (prefFamily st I)
  let pm ← pathMaxima st.ends st.forest (S.toList.map (endsPair st))
  let ans ← FreeM.tabulateList (queryPref st pm) S.toList
  pure (consistentWith (prefFamily st I) S ans)

/-! ### Correctness -/

section Correctness

variable [LinearOrder W] {w : E → W}

omit [DecidableEq V] [DecidableEq E] in
private theorem eval_anyGe (w : E → W) (f : E) (l : List E) :
    (anyGe f l).eval (LEQuery.keyOracle w) = decide (∃ s ∈ l, w f ≤ w s) := by
  induction l with
  | nil => simp [anyGe]
  | cons s l ih =>
    by_cases h : w f ≤ w s <;> simp [anyGe, h, ih]

omit [DecidableEq V] [DecidableEq E] [LinearOrder W] in
private theorem countQueries_anyGe_le (o : {ι : Type} → LEQuery E ι → ι) (f : E) (l : List E) :
    (anyGe f l).countQueries o ≤ l.length := by
  induction l with
  | nil => simp [anyGe]
  | cons s l ih =>
    simp only [anyGe, FreeM.countQueries_bind, FreeM.countQueries_lift, List.length_cons]
    split
    · simp
    · omega

/-- **The queried preferences are the true ones** (p. 22): for injective weights and an acyclic
forest, when the ends of `e` are among the queries of the path maxima computation. -/
theorem eval_queryPref (hw : Function.Injective w) {st : State V E}
    (hF : IsAcyclic st.ends (st.forest : Set E)) {qs : List (V × V)} {e : E}
    (hq : endsPair st e ∈ qs) :
    (queryPref st ((pathMaxima st.ends st.forest qs).eval (LEQuery.keyOracle w)) e).eval
      (LEQuery.keyOracle w) = pref w st e := by
  classical
  have horacle : ∀ a b, LEQuery.keyOracle w (.le a b) = decide (w a ≤ w b) :=
    fun a b => LEQuery.keyOracle_le w a b
  set u := (endsPair st e).1
  set v := (endsPair st e).2
  have huv : st.ends e = s(u, v) := ends_eq_endsPair st e
  have hq' : (u, v) ∈ qs := hq
  unfold queryPref
  by_cases hp : Projectable st e
  · simp only [hp, ↓reduceIte]
    obtain ⟨su, sv, hsu, hsv, hne⟩ : ∃ su sv, st.spoke u = some su ∧ st.spoke v = some sv ∧
        st.proj u ≠ st.proj v := by
      obtain ⟨su, hsu⟩ := Option.isSome_iff_exists.1
        (hp.isSome_spoke (by rw [huv]; exact Sym2.mem_mk_left u v))
      obtain ⟨sv, hsv⟩ := Option.isSome_iff_exists.1
        (hp.isSome_spoke (by rw [huv]; exact Sym2.mem_mk_right u v))
      have hne := hp.not_isDiag
      rw [huv, Sym2.map_mk, Sym2.mk_isDiag_iff] at hne
      exact ⟨su, sv, hsu, hsv, hne⟩
    have hspokes : ∀ s, s ∈ spokes st e ↔ s = su ∨ s = sv := fun s => by
      rw [spokes_eq huv, hsu, hsv]
      simp [eq_comm]
    have hpf := prefersFind_iff (w := w) huv hsu hsv
    rcases hpm : (pathMaxima st.ends st.forest qs).eval (LEQuery.keyOracle w) u v with _ | f
    · -- the forest does not join the ends
      rw [pathMaxima_eq_none_iff hw horacle hF hq'] at hpm
      have huv' : u ≠ v := fun h => hne (h ▸ rfl)
      have hnj := hpm.resolve_left huv'
      simp only [FreeM.eval_pure]
      refine (pref_eq_project_iff.2 fun h => ?_).symm
      rcases hpf.1 h with h | h
      · exact hne h
      · refine hnj (h.mono ?_)
        rintro g ⟨hg, -⟩
        exact hg
    · rw [pathMaxima_eq_some_iff hw horacle hF hq'] at hpm
      obtain ⟨hfF, hle, hlt⟩ := hpm
      have key : PrefersFind w st e ↔ w f ≤ w su ∨ w f ≤ w sv := by
        rw [hpf, or_iff_right hne, ← le_max_iff]
        constructor
        · intro h
          by_contra hfm
          refine hlt (h.mono ?_)
          rintro g ⟨hg, hgm⟩
          exact ⟨hg, hgm.trans_lt (not_le.1 hfm)⟩
        · intro h
          refine hle.mono ?_
          rintro g ⟨hg, hgf⟩
          exact ⟨hg, hgf.trans h⟩
      simp only [FreeM.eval_bind, eval_anyGe, mem_toList]
      by_cases hf : w f ≤ w su ∨ w f ≤ w sv
      · have : ∃ s ∈ spokes st e, w f ≤ w s := by
          rcases hf with hf | hf
          · exact ⟨su, (hspokes su).2 (Or.inl rfl), hf⟩
          · exact ⟨sv, (hspokes sv).2 (Or.inr rfl), hf⟩
        simp only [this, decide_true, ↓reduceIte, FreeM.eval_pure]
        exact (pref_eq_find_iff.2 (key.2 hf)).symm
      · have : ¬∃ s ∈ spokes st e, w f ≤ w s := by
          rintro ⟨s, hs, hfs⟩
          rcases (hspokes s).1 hs with rfl | rfl
          · exact hf (Or.inl hfs)
          · exact hf (Or.inr hfs)
        simp only [this, decide_false, Bool.false_eq_true, ↓reduceIte, FreeM.eval_pure]
        exact (pref_eq_project_iff.2 (mt key.1 hf)).symm
  · simp only [hp, ↓reduceIte, FreeM.eval_pure]
    exact (pref_eq_find_iff.2 (prefersFind_of_not_projectable hp)).symm

omit [LinearOrder W] in
/-- At most two comparisons per queried edge. -/
private theorem countQueries_queryPref_le (o : {ι : Type} → LEQuery E ι → ι) (st : State V E)
    (pm : V → V → Option E) (e : E) : (queryPref st pm e).countQueries o ≤ 2 := by
  classical
  unfold queryPref
  split
  · split
    · simp
    · rename_i f _
      simp only [FreeM.countQueries_bind]
      have h := (countQueries_anyGe_le o f (spokes st e).toList).trans_eq (length_toList _)
      have h2 := card_spokes_le st e
      split <;> simp <;> omega
  · simp

omit [DecidableEq V] [DecidableEq E] in
/-- The separating set has the properties of Claim 3.12 (p. 22). -/
theorem separatingSet_spec {t : ℕ} (ht : 0 < t) (I : Finset E) (A : Finset (E → Action)) :
    separatingSet t I A ⊆ I ∧ #(separatingSet t I A) ≤ ⌈2 * t * Real.log #A⌉₊ ∧
      ∀ a ∈ A, ∀ b ∈ A, (∀ e ∈ separatingSet t I A, a e = b e) →
        (#{e ∈ I | a e ≠ b e} : ℝ) ≤ #I / t := by
  classical
  unfold separatingSet
  simp only [ht, ↓reduceDIte]
  exact (exists_separating_coordinates I A (t := (t : ℝ)) (by exact_mod_cast ht)).choose_spec

private theorem eval_estimator (o : {ι : Type} → LEQuery E ι → ι) (γ : ℕ) (inst : Instance V E)
    (st : State V E) (I : Finset E) :
    (estimator γ inst st I).eval o =
      consistentWith (prefFamily st I) (separatingSet (levelT γ inst.level) I (prefFamily st I))
        fun x => if x ∈ separatingSet (levelT γ inst.level) I (prefFamily st I) then
          some ((queryPref st ((pathMaxima st.ends st.forest
            ((separatingSet (levelT γ inst.level) I (prefFamily st I)).toList.map
              (endsPair st))).eval o) x).eval o)
          else none := by
  simp [estimator, FreeM.eval_tabulateList]

/-- A step in the proof of Theorem 4.1 of [KhannaPuttermanSong2026] (#8325): the estimation errors
of a round (§3.5, Claim 3.12 and its use, p. 22). For injective weights, an acyclic forest and
`t > 0`, the estimate differs from the true preferences in at most `|I| / t` edges of `I`. -/
theorem card_estimator_ne_pref_le (hw : Function.Injective w) {γ : ℕ} {inst : Instance V E}
    (ht : 0 < levelT γ inst.level) {st : State V E} (hF : IsAcyclic st.ends (st.forest : Set E))
    (I : Finset E) :
    (#{e ∈ I | (estimator γ inst st I).eval (LEQuery.keyOracle w) e ≠ pref w st e} : ℝ) ≤
      #I / levelT γ inst.level := by
  classical
  set A := prefFamily st I
  set S := separatingSet (levelT γ inst.level) I A
  obtain ⟨hSI, -, hsep⟩ := separatingSet_spec ht I A
  have hmem := prefVector_mem_prefFamily hw hF I
  rw [eval_estimator]
  set ans : E → Option Action := fun x => if x ∈ S then
    some ((queryPref st ((pathMaxima st.ends st.forest (S.toList.map (endsPair st))).eval
      (LEQuery.keyOracle w)) x).eval (LEQuery.keyOracle w)) else none
  have hans : ∀ e ∈ S, ans e = some (prefVector w st I e) := fun e he => by
    simp only [ans, he, ↓reduceIte, prefVector_of_mem (hSI he)]
    rw [eval_queryPref hw hF (List.mem_map_of_mem (mem_toList.2 he))]
  have hex : ∃ b ∈ A, ∀ e ∈ S, ans e = some (b e) := ⟨_, hmem, hans⟩
  have hc : consistentWith A S ans = hex.choose := by
    unfold consistentWith
    simp only [hex, ↓reduceDIte]
  rw [hc]
  obtain ⟨hbA, hbS⟩ := hex.choose_spec
  have hagree : ∀ e ∈ S, hex.choose e = prefVector w st I e := fun e he => by
    have := (hbS e he).symm.trans (hans e he)
    exact Option.some.inj this
  have := hsep _ hbA _ hmem hagree
  refine le_of_eq_of_le ?_ this
  congr 2
  refine filter_congr fun e he => ?_
  rw [prefVector_of_mem he]

end Correctness

/-! ### Comparisons -/

section Cost

variable [LinearOrder W]

/-- **The comparisons of a round** (p. 22): one path maxima computation, at most `16 |F| + 5 |S*|`
comparisons by M2's `Cslib.Query.countQueries_pathMaxima_le`, and at most two comparisons per edge
of `S*`. -/
theorem countQueries_estimator_le (w : E → W) (γ : ℕ) (inst : Instance V E) {st : State V E}
    (hF : IsAcyclic st.ends (st.forest : Set E)) (I : Finset E) :
    (estimator γ inst st I).countQueries (LEQuery.keyOracle w) ≤
      16 * #st.forest + 7 * #(separatingSet (levelT γ inst.level) I (prefFamily st I)) := by
  simp only [estimator, FreeM.countQueries_bind, FreeM.countQueries_pure, add_zero]
  rw [FreeM.countQueries_eq_cost_one _ (FreeM.tabulateList _ _), FreeM.cost_tabulateList]
  set S := separatingSet (levelT γ inst.level) I (prefFamily st I)
  have hpm := countQueries_pathMaxima_le (w := w) (oracle := LEQuery.keyOracle w)
    (fun a b => LEQuery.keyOracle_le w a b) hF (S.toList.map (endsPair st))
  rw [List.length_map, length_toList] at hpm
  have htab : (S.toList.map fun a => (queryPref st ((pathMaxima st.ends st.forest
      (S.toList.map (endsPair st))).eval (LEQuery.keyOracle w)) a).cost
        (LEQuery.keyOracle w) (fun _ => 1)).sum ≤ 2 * #S := by
    have := List.sum_le_length_nsmul (S.toList.map fun a => (queryPref st ((pathMaxima st.ends
      st.forest (S.toList.map (endsPair st))).eval (LEQuery.keyOracle w)) a).cost
        (LEQuery.keyOracle w) (fun _ => 1)) 2 (by
      intro x hx
      obtain ⟨a, -, rfl⟩ := List.mem_map.1 hx
      rw [← FreeM.countQueries_eq_cost_one]
      exact countQueries_queryPref_le _ st _ a)
    simpa [mul_comm] using this
  omega

/-- **The comparisons of a round, in real form** (p. 22): with `n` vertices carrying the spokes
and the ends of `I`, a forest of at most `n` edges, and `t = γ d³`, at most `16 n + 49 t √(|I| n)`
comparisons. -/
theorem countQueries_estimator_le_real (w : E → W) (γ : ℕ) (inst : Instance V E)
    {st : State V E} (hF : IsAcyclic st.ends (st.forest : Set E))
    (hFX : #st.forest ≤ #st.vertices) (hσ : ∀ v s, st.spoke v = some s → v ∈ st.vertices)
    {I : Finset E} (hI : ∀ e ∈ I, ∀ v ∈ st.ends e, v ∈ st.vertices) :
    ((estimator γ inst st I).countQueries (LEQuery.keyOracle w) : ℝ) ≤
      16 * #st.vertices + 49 * levelT γ inst.level * √(#I * #st.vertices) := by
  set t := levelT γ inst.level
  set n := #st.vertices
  set S := separatingSet t I (prefFamily st I)
  have hc := countQueries_estimator_le w γ inst hF I
  have hS : (#S : ℝ) ≤ 7 * t * √(#I * n) := by
    rcases S.eq_empty_or_nonempty with hS0 | ⟨e, he⟩
    · rw [hS0, card_empty, Nat.cast_zero]
      positivity
    have ht : 0 < t := by
      rcases Nat.eq_zero_or_pos t with h | h
      · simp [S, separatingSet, h] at he
      · exact h
    obtain ⟨hSI, hScard, -⟩ := separatingSet_spec ht I (prefFamily st I)
    have heI := hSI he
    have hn : 1 ≤ n := by
      obtain ⟨⟨a, b⟩, hab⟩ := Quot.exists_rep (st.ends e)
      exact card_pos.2 ⟨a, hI e heI a (by rw [← hab]; exact Sym2.mem_mk_left a b)⟩
    have hm : 1 ≤ #I := card_pos.2 ⟨e, heI⟩
    have hlogA : Real.log #(prefFamily st I) ≤ 2 * √(#I * (2 * n : ℕ)) := by
      have h1 := card_prefFamily_le_choose hσ hFX I
      have h2 := Cslib.log_add_choose_le_two_mul_sqrt #I (2 * n)
      refine le_trans ?_ h2
      rcases Nat.eq_zero_or_pos #(prefFamily st I) with h0 | h0
      · rw [h0, Nat.cast_zero, Real.log_zero]
        exact Real.log_natCast_nonneg _
      · exact Real.log_le_log (by exact_mod_cast h0) (by exact_mod_cast h1)
    have hlog0 : 0 ≤ Real.log #(prefFamily st I) := Real.log_natCast_nonneg _
    have hceil := Nat.ceil_lt_add_one (show 0 ≤ 2 * (t : ℝ) * Real.log #(prefFamily st I) by
      positivity)
    have hS' : (#S : ℝ) ≤ ⌈2 * (t : ℝ) * Real.log #(prefFamily st I)⌉₊ := by exact_mod_cast hScard
    have hsq : √((#I : ℝ) * (2 * n : ℕ)) = √2 * √(#I * n) := by
      push_cast
      rw [show (#I : ℝ) * (2 * n) = 2 * (#I * n) by ring, Real.sqrt_mul (by norm_num)]
    have hs2 : √2 ≤ 3 / 2 := Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num⟩
    have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
    have hmn : (1 : ℝ) ≤ √(#I * n) := by
      rw [Real.one_le_sqrt]
      have : (1 : ℝ) ≤ #I := by exact_mod_cast hm
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith
    rw [hsq] at hlogA
    have h0 : 0 ≤ √((#I : ℝ) * n) := Real.sqrt_nonneg _
    have : (t : ℝ) * Real.log #(prefFamily st I) ≤ t * (3 * √(#I * n)) := by
      gcongr
      nlinarith
    nlinarith
  have hFn : (#st.forest : ℝ) ≤ n := by exact_mod_cast hFX
  have hc' : ((estimator γ inst st I).countQueries (LEQuery.keyOracle w) : ℝ) ≤
      16 * #st.forest + 7 * #S := by exact_mod_cast hc
  linarith

end Cost

/-! ### Totals over a call -/

section Call

variable [LinearOrder W] (cfg : Config V E) (w : E → W)

/-- **The comparisons of the estimator over a call** (p. 22): over the `t²` rounds of a call on `n`
vertices and `m` edges, the estimator at the states of the run makes at most
`16 t² n + 49 t² √(m n)` comparisons, by Cauchy–Schwarz on `∑ᵢ √mᵢ`. -/
theorem sum_countQueries_estimator_le (hw : Function.Injective w) (hmsf : cfg.ExactMsf w)
    {inst : Instance V E} (hwf : inst.WellFormed) :
    ∑ i ∈ range (levelT cfg.γ inst.level ^ 2),
      ((estimator cfg.γ inst (snapshot cfg (LEQuery.keyOracle w) inst i).state
        (acting cfg inst i)).countQueries (LEQuery.keyOracle w) : ℝ) ≤
      16 * (levelT cfg.γ inst.level : ℝ) ^ 2 * #inst.vertices +
        49 * (levelT cfg.γ inst.level : ℝ) ^ 2 * √(#inst.edges * #inst.vertices) := by
  set t := levelT cfg.γ inst.level
  set n := #inst.vertices
  have hround : ∀ i ∈ range (t ^ 2),
      ((estimator cfg.γ inst (snapshot cfg (LEQuery.keyOracle w) inst i).state
        (acting cfg inst i)).countQueries (LEQuery.keyOracle w) : ℝ) ≤
        16 * n + 49 * t * (√(#(acting cfg inst i)) * √n) := fun i _ => by
    have hinv := invariant_snapshot hw hmsf hwf i
    have hvx := vertices_snapshot cfg (LEQuery.keyOracle w) inst i
    have hends := ends_snapshot cfg (LEQuery.keyOracle w) inst i
    have h := countQueries_estimator_le_real w cfg.γ inst hinv.state.forest_acyclic
      (hinv.state.card_forest_le.trans (Nat.sub_le _ _)) hinv.state.mem_vertices_of_spoke
      (I := acting cfg inst i) (fun e he v hv => by
        rw [hvx]
        rw [hends] at hv
        exact hwf.ends_mem e (mem_filter.1 he).1 v hv)
    rw [hvx, Real.sqrt_mul (Nat.cast_nonneg _)] at h
    exact h
  refine (sum_le_sum hround).trans ?_
  rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul, ← mul_sum, ← sum_mul]
  have hcs := Real.sum_sqrt_mul_sqrt_le (range (t ^ 2))
    (f := fun i => (#(acting cfg inst i) : ℝ)) (g := fun _ => 1) (fun _ => Nat.cast_nonneg _)
    (fun _ => zero_le_one)
  simp only [Real.sqrt_one, mul_one, sum_const, card_range, nsmul_eq_mul] at hcs
  have hm : ∑ i ∈ range (t ^ 2), (#(acting cfg inst i) : ℝ) = #inst.edges := by
    exact_mod_cast sum_card_acting cfg inst
  rw [hm, Nat.cast_pow, Real.sqrt_sq (Nat.cast_nonneg _)] at hcs
  have hsq : √((#inst.edges : ℝ) * n) = √(#inst.edges : ℝ) * √(n : ℝ) :=
    Real.sqrt_mul (Nat.cast_nonneg _) _
  rw [hsq]
  push_cast
  have h0 : 0 ≤ √(n : ℝ) := Real.sqrt_nonneg _
  have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg _
  have := mul_le_mul_of_nonneg_right hcs h0
  nlinarith

open scoped Classical in
/-- **The estimation errors over a call** (p. 22): when the configuration uses the estimator and
`γ > 0`, at most `m / t` edges of a call act with an estimate that differs from their true
preference, `∑ᵢ mᵢ / t = m / t`. -/
theorem card_estimate_ne_prefSeq_le (hw : Function.Injective w) (hmsf : cfg.ExactMsf w)
    {inst : Instance V E} (hwf : inst.WellFormed) (hγ : 0 < cfg.γ)
    (he : cfg.est = estimator cfg.γ) :
    (#{e ∈ inst.edges | estimate cfg (LEQuery.keyOracle w) inst (cfg.sched inst e) e ≠
        prefSeq cfg w inst e (cfg.sched inst e)} : ℝ) ≤
      #inst.edges / levelT cfg.γ inst.level := by
  set t := levelT cfg.γ inst.level
  have ht : 0 < t := Nat.mul_pos hγ (pow_pos inst.level.pos 3)
  set B := {e ∈ inst.edges | estimate cfg (LEQuery.keyOracle w) inst (cfg.sched inst e) e ≠
    prefSeq cfg w inst e (cfg.sched inst e)}
  rw [card_eq_sum_card_fiberwise (f := fun e => (cfg.sched inst e : ℕ)) (t := range (t ^ 2))
    (fun e _ => mem_range.2 (cfg.sched inst e).2)]
  have hfiber : ∀ i ∈ range (t ^ 2), (#{e ∈ B | (cfg.sched inst e : ℕ) = i} : ℝ) ≤
      #(acting cfg inst i) / t := fun i _ => by
    set st := (snapshot cfg (LEQuery.keyOracle w) inst i).state
    have hinv := invariant_snapshot hw hmsf hwf i
    have h := card_estimator_ne_pref_le hw (γ := cfg.γ) (inst := inst) ht
      hinv.state.forest_acyclic (acting cfg inst i) (w := w) (st := st)
    refine le_trans ?_ h
    gcongr
    intro e hx
    obtain ⟨heB, hsi⟩ := mem_filter.1 hx
    obtain ⟨heE, hne⟩ := mem_filter.1 heB
    refine mem_filter.2 ⟨mem_filter.2 ⟨heE, hsi⟩, ?_⟩
    rw [hsi, prefSeq_eq] at hne
    have := ne_of_maskAction_ne hne
    rwa [he] at this
  push_cast
  refine (sum_le_sum hfiber).trans ?_
  simp only [div_eq_mul_inv]
  rw [← sum_mul]
  gcongr
  exact_mod_cast (sum_card_acting cfg inst).le

end Call

end Cslib.Query.Certificate
