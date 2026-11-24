/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Query.MinimumSpanningForest.Boruvka
public import CslibFrontier.Algorithms.Lean.Query.MinimumSpanningForest.PathMaxima
public import CslibFrontier.Algorithms.Lean.Query.MinimumSpanningForest.Certificate.Accounting
public import CslibFrontier.Algorithms.Lean.Query.FreeM.Tabulate

/-!
# Minimum spanning forests with a linear number of comparisons (Theorem 4.1)

Theorem 4.1 of [Khanna, Putterman and Song][KhannaPuttermanSong2026] (§4, p. 25): the
deterministic comparison (decision-tree) complexity of minimum spanning forests is `O(m)`.
`Cslib.Query.exists_msf_program_countQueries_le` states it: one absolute constant `C` such that
every finite multigraph with `m` edges has a comparison program that computes its minimum spanning
forest with at most `C m` comparisons, for every assignment of distinct weights. Its docstring maps
the statement to the paper's definition of `T*` (p. 5). The running time of Theorem 1.1 and
Corollary 4.2, which rests on Pettie and Ramachandran's optimal algorithm, is not proved.

## Algorithm 2 (p. 25)

`Cslib.Query.linearMsf k ends S` is the paper's Algorithm 2 as a comparison program in
`FreeM (LEQuery E)`:

1. run `k` Borůvka steps (`Cslib.Query.boruvka`, Definition 2.8), which select the edges `chosen`,
   contract them and drop the self-loops, leaving the edges `rest` of the contracted multigraph;
2. if `rest` is empty, return `chosen`;
3. run the certificate procedure (`Cslib.Query.Certificate.certificate`, Algorithm 1, with the
   derandomized schedule and estimator and `γ = 32`) on `rest`, with the non-isolated vertices of
   the contracted multigraph, obtaining a forest `F`;
4. compute the edges `U(F)` of `rest` that `F` does not support, by path maxima on `F`
   (`Cslib.Query.unsupportedEdges`, Lemma 2.9), with one more comparison per edge;
5. return `chosen ∪ MSF(F ∪ U(F))`.

**Tying the knot.** The certificate procedure and line 5 make exact minimum spanning forest calls.
`linearMsf` answers each by a recursive call when its input has fewer edges than `S`, and
otherwise by Borůvka's algorithm run to completion (`Cslib.Query.boruvkaMsf`), which is always
correct. The definition is by well-founded recursion on `|S|`. So every exact call is correct for
distinct weights, by strong induction, and `Cslib.Query.eval_linearMsf` holds for every `k`.

**The constants.** `γ = 32` makes the `8 m / γ` term of Lemma 3.1
(`Cslib.Query.Certificate.certificate_derandomized_accounting`) equal to `m / 4`. The number of
Borůvka steps `k = Cslib.Query.linearMsfSteps` satisfies `32 C² ≤ 2 ^ k` for the constant `C` of
Lemma 3.1, so that the `C √(m' n')` term is at most `m / 4`: the contracted multigraph has
`n' ≤ 2 m / 2 ^ k` non-isolated vertices and `m' ≤ m` edges. Then `|F| + |U(F)| + ∑ |E_i| ≤ m / 2`,
every exact call has fewer than `m` edges (when `rest` is nonempty, `m ≥ 1`), and the fallback
never runs. Strong induction gives `T(m) ≤ c m + 2 c (m / 2) = 2 c m`, where
`c = 2 k + |C'| + 22` collects the Borůvka steps (`2 k m`), the certificate procedure outside its
exact calls (`C' m`) and the unsupported edges (`16 |F| + 6 m'`)
(`Cslib.Query.countQueries_linearMsf_le`).

## Comparison with §4

* The paper removes isolated vertices from the contracted multigraph (line 3). Here the
  certificate procedure runs on the non-isolated vertices `X` of `rest` in the contracted
  multigraph, `|X| ≤ 2 |rest|` (`Cslib.Multigraph.card_support_le`), and the halving of M1
  (`Cslib.Query.card_support_boruvka_le`) bounds `|X|` by the non-isolated vertices of `S`
  divided by `2 ^ k`, so `n' ≤ 2 m / 2 ^ k` with no assumption on isolated vertices of the input.
* Self-loops, of the input and those created by contraction, are dropped by the Borůvka steps,
  which is what the paper's "contracted graph" means.
* The paper chooses `k` with `C_{1/8} 2^{(1-k)/2} ≤ 3/8` and `ε = 1/8`; here the `m`-term of
  Lemma 3.1 is `8 m / γ` rather than `16 m / γ` (M7c), and `k` is chosen with
  `C √(2 / 2 ^ k) ≤ 1/4`. The recurrence `T(m) ≤ ∑ T(m_i) + O(m)` with `∑ m_i ≤ m / 2` is the
  paper's.

No step of §4 needed repair.

## Main definitions

* `Cslib.Query.linearMsf`: Algorithm 2 with `k` Borůvka steps.
* `Cslib.Query.linearMsfSteps`: the number of Borůvka steps of Theorem 4.1.
* `Cslib.Query.unsupportedEdges`: the edges unsupported by a forest, by path maxima.
* `Cslib.Query.boruvkaMsf`: Borůvka's algorithm run to completion, the fallback exact call.

## Main results

* `Cslib.Query.exists_msf_program_countQueries_le`: **Theorem 4.1**.
* `Cslib.Query.eval_linearMsf`, `Cslib.Query.countQueries_linearMsf_le`: correctness and the
  comparison count of Algorithm 2.
* `Cslib.Query.linearMsf_isSpanningForest_and_sum_le`: its output is a minimum-weight spanning
  forest.

## References

* [S. Khanna, A. Putterman and J. Song, *A Deterministic Linear Time Algorithm for Minimum
  Spanning Tree*][KhannaPuttermanSong2026], §1.1, p. 5 (the definition of `T*`), §2, pp. 11–12,
  and §4, pp. 25–26.
* [O. Borůvka, *O jistém problému minimálním*][Boruvka1926].
-/

public section

namespace Cslib.Query

open Finset Multigraph

variable {V E : Type} [DecidableEq V] [DecidableEq E]

/-! ### Borůvka's algorithm run to completion -/

/-- A step in the proof of Theorem 4.1 of [KhannaPuttermanSong2026] (#8325): **Borůvka's
algorithm** ([Boruvka1926]) run to completion, as a comparison program. After `|S| + 1` Borůvka
steps no edge remains, so the selected edges are the minimum spanning forest
(`Cslib.Query.eval_boruvkaMsf`). `Cslib.Query.linearMsf` falls back on it for an exact call on at
least as many edges as its own input, which never happens for distinct weights; it makes its
decisions by comparisons only, so the fallback is an honest exact subroutine. -/
noncomputable def boruvkaMsf (ends : E → Sym2 V) (S : Finset E) :
    FreeM (LEQuery E) (Finset E) :=
  BoruvkaResult.chosen <$> boruvka ends S (#S + 1)

/-- A step in the proof of Theorem 4.1 of [KhannaPuttermanSong2026] (#8325): **Borůvka's
algorithm computes the minimum spanning forest** for distinct weights (§2, p. 12). `|S| + 1` steps
leave at most `2 |S| / 2 ^ (|S| + 1) < 1` non-isolated vertices, so no edge remains. -/
theorem eval_boruvkaMsf {W : Type} [LinearOrder W] (ends : E → Sym2 V) (S : Finset E)
    {w : E → W} (hw : Function.Injective w) :
    (boruvkaMsf ends S).eval (LEQuery.keyOracle w) = msf ends w S := by
  set r := (boruvka ends S (#S + 1)).eval (LEQuery.keyOracle w) with hr
  have hrest : r.rest = ∅ := by
    have h := card_support_boruvka_le ends S (#S + 1) (LEQuery.keyOracle w) hr.symm
    have hlt : #(support ends S) < 2 ^ (#S + 1) := by
      have h₁ := card_support_le ends S
      have h₂ : #S < 2 ^ #S := Nat.lt_two_pow_self
      rw [pow_succ]
      omega
    rw [Nat.div_eq_of_lt hlt, Nat.le_zero, card_eq_zero] at h
    refine eq_empty_of_forall_notMem fun e he => ?_
    have hd := (isContraction_boruvka ends S (#S + 1) (LEQuery.keyOracle w)).not_isDiag e he
    obtain ⟨⟨v, b⟩, hvb⟩ := Quot.exists_rep (Sym2.map r.proj (ends e))
    have hv : v ∈ Sym2.map r.proj (ends e) := hvb ▸ Sym2.mem_mk_left v b
    have : v ∈ support (Sym2.map r.proj ∘ ends) r.rest := mem_support.2 ⟨e, he, hd, hv⟩
    rw [h] at this
    exact notMem_empty _ this
  rw [msf_eq_union_boruvka ends S (#S + 1) w hw hr.symm, hrest]
  have h0 : msf (Sym2.map r.proj ∘ ends) w ∅ = ∅ := subset_empty.1 (msf_subset w)
  simp [boruvkaMsf, ← hr, h0]

/-! ### The unsupported edges by path maxima -/

/-- Whether the edge `e` is unsupported, from the answer `pm` of path maxima on the forest: with
no heaviest edge on the path between its ends, `e` is unsupported exactly when its ends differ;
with a heaviest edge `f`, exactly when `f` is heavier than `e`, which takes one comparison. -/
private noncomputable def unsupportedTest (ends : E → Sym2 V) (pm : V → V → Option E) (e : E) :
    FreeM (LEQuery E) Bool :=
  match pm (Quot.out (ends e)).1 (Quot.out (ends e)).2 with
  | none => pure (decide ((Quot.out (ends e)).1 ≠ (Quot.out (ends e)).2))
  | some f => do return !(← LEQuery.ask f e)

/-- A step in the proof of Theorem 4.1 of [KhannaPuttermanSong2026] (#8325): **the edges of `S`
unsupported by a forest `F`** (§4, Algorithm 2, line 7, p. 25). Answer the path maximum query of
every edge of `S` on `F` (`Cslib.Query.pathMaxima`, the paper's Lemma 2.9), then compare each edge
with its path maximum: `e` is supported exactly when the heaviest edge on the path of `F` between
its ends is no heavier than `e`. -/
noncomputable def unsupportedEdges (ends : E → Sym2 V) (F S : Finset E) :
    FreeM (LEQuery E) (Finset E) := do
  let pm ← pathMaxima ends F (S.toList.map fun e => Quot.out (ends e))
  let t ← FreeM.tabulateList (unsupportedTest ends pm) S.toList
  return {e ∈ S | t e = some true}

section Unsupported

variable {W : Type} [LinearOrder W] {w : E → W}

/-- A step in the proof of Theorem 4.1 of [KhannaPuttermanSong2026] (#8325): for distinct
weights and an acyclic `F`, `Cslib.Query.unsupportedEdges` computes the edges of `S` that `F`
does not support (§4, p. 25). -/
theorem eval_unsupportedEdges (hw : Function.Injective w) {ends : E → Sym2 V} {F : Finset E}
    (hF : IsAcyclic ends (F : Set E)) (S : Finset E) :
    (unsupportedEdges ends F S).eval (LEQuery.keyOracle w) = unsupported ends w F S := by
  classical
  ext e
  simp only [unsupportedEdges, FreeM.eval_bind, FreeM.eval_pure, FreeM.eval_tabulateList,
    mem_filter, mem_toList, mem_unsupported]
  refine and_congr_right fun he => ?_
  set u := (Quot.out (ends e)).1
  set v := (Quot.out (ends e)).2
  have huv : ends e = s(u, v) := (Sym2.mk_fst_out_snd_out _).symm
  have hq : (u, v) ∈ S.toList.map fun e => Quot.out (ends e) :=
    List.mem_map.2 ⟨e, mem_toList.2 he, rfl⟩
  have horacle : ∀ a b, LEQuery.keyOracle w (.le a b) = decide (w a ≤ w b) := fun _ _ => rfl
  rw [supported_iff w huv]
  simp only [he, ↓reduceIte, Option.some.injEq, unsupportedTest]
  split
  · next h =>
    rw [pathMaxima_eq_none_iff hw horacle hF hq] at h
    simp only [FreeM.eval_pure, decide_eq_true_eq]
    constructor
    · intro hne hj
      exact (h.resolve_left hne) (hj.mono (show {g | g ∈ (F : Set E) ∧ w g ≤ w e} ⊆ (F : Set E)
        from fun g hg => hg.1))
    · intro hn heq
      apply hn
      rw [show u = v from heq]
  · next f h =>
    obtain ⟨-, hle, hlt⟩ := (pathMaxima_eq_some_iff hw horacle hF hq f).1 h
    simp only [FreeM.eval_bind, LEQuery.eval_ask, LEQuery.keyOracle_le, FreeM.eval_pure,
      Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, not_le]
    constructor
    · intro hef hj
      exact hlt (hj.mono (by rintro g ⟨hg, hge⟩; exact ⟨hg, hge.trans_lt hef⟩))
    · intro hn
      by_contra hfe
      exact hn (hle.mono (by rintro g ⟨hg, hgf⟩; exact ⟨hg, hgf.trans (not_lt.1 hfe)⟩))

/-- A step in the proof of Theorem 4.1 of [KhannaPuttermanSong2026] (#8325): against an oracle
of weights, `Cslib.Query.unsupportedEdges` on an acyclic `F` makes at most `16 |F| + 6 |S|`
comparisons, `16 |F| + 5 |S|` for the path maxima and one more per edge (§4, p. 25). -/
theorem countQueries_unsupportedEdges_le {ends : E → Sym2 V} {F : Finset E}
    (hF : IsAcyclic ends (F : Set E)) (S : Finset E) :
    (unsupportedEdges ends F S).countQueries (LEQuery.keyOracle w) ≤ 16 * #F + 6 * #S := by
  have horacle : ∀ a b, LEQuery.keyOracle w (.le a b) = decide (w a ≤ w b) := fun _ _ => rfl
  have h₁ := countQueries_pathMaxima_le horacle hF (S.toList.map fun e => Quot.out (ends e))
  simp only [List.length_map, length_toList] at h₁
  have h₂ : ∀ pm : V → V → Option E,
      (FreeM.tabulateList (unsupportedTest ends pm) S.toList).countQueries
        (LEQuery.keyOracle w) ≤ #S := fun pm => by
    rw [FreeM.countQueries_eq_cost_one, FreeM.cost_tabulateList, ← length_toList]
    refine (List.sum_le_length_nsmul _ 1 fun x hx => ?_).trans (by simp)
    obtain ⟨e, -, rfl⟩ := List.mem_map.1 hx
    rw [← FreeM.countQueries_eq_cost_one, unsupportedTest]
    split <;> simp
  simp only [unsupportedEdges, FreeM.countQueries_bind, FreeM.countQueries_pure, add_zero]
  have := h₂ ((pathMaxima ends F (S.toList.map fun e => Quot.out (ends e))).eval
    (LEQuery.keyOracle w))
  omega

end Unsupported

/-! ### Algorithm 2 -/

open Certificate

/-- A step in the proof of Theorem 4.1 of [KhannaPuttermanSong2026] (#8325): **Algorithm 2**
(§4, p. 25), with `k` Borůvka steps and the certificate procedure's parameter `γ = 32`. Run `k`
Borůvka steps, which select the edges `chosen`, contract them and drop self-loops; if no edge
remains, return `chosen`. Otherwise run the certificate procedure on the remaining edges `rest` of
the contracted multigraph, with its non-isolated vertices, obtaining a forest `F`; compute the
edges `U(F)` of `rest` that `F` does not support; and return `chosen` together with the minimum
spanning forest of `F ∪ U(F)`.

Every exact minimum spanning forest call, those of the certificate procedure and the final one,
is a recursive call when its input has fewer edges than `S`, and is otherwise Borůvka's algorithm
run to completion (`Cslib.Query.boruvkaMsf`). The guard ties the knot by well-founded recursion on
the number of edges; for distinct weights and the constant `k = Cslib.Query.linearMsfSteps` it
never fails, since every exact call then has at most `|S| / 2` edges. Correctness holds for every
`k` (`Cslib.Query.eval_linearMsf`). -/
noncomputable def linearMsf (k : ℕ) (ends : E → Sym2 V) (S : Finset E) :
    FreeM (LEQuery E) (Finset E) := do
  let r ← boruvka ends S k
  if r.rest = ∅ then return r.chosen
  else
    let ends' := Sym2.map r.proj ∘ ends
    let sub := fun (ends'' : E → Sym2 V) (S' : Finset E) =>
      if _ : #S' < #S then linearMsf k ends'' S' else boruvkaMsf ends'' S'
    let res ← certificate (Config.derandomized 32 (by norm_num) sub)
      (Instance.root (support ends' r.rest) ends' r.rest)
    let U ← unsupportedEdges ends' res.forest r.rest
    let M ← sub ends' (res.forest ∪ U)
    return r.chosen ∪ M
termination_by #S

/-- A step in the proof of Theorem 4.1 of [KhannaPuttermanSong2026] (#8325): **correctness of
Algorithm 2** (§4, p. 26), for every number `k` of Borůvka steps. For distinct weights,
`Cslib.Query.linearMsf` computes the minimum spanning forest: `MSF(S) = chosen ∪ MSF(rest)` by the
Borůvka steps, `MSF(rest) = MSF(F ∪ U(F))` by filtering, and every exact call is correct by strong
induction on the number of edges or by `Cslib.Query.eval_boruvkaMsf`. -/
theorem eval_linearMsf (k : ℕ) {W : Type} [LinearOrder W] {w : E → W}
    (hw : Function.Injective w) (ends : E → Sym2 V) (S : Finset E) :
    (linearMsf k ends S).eval (LEQuery.keyOracle w) = msf ends w S := by
  induction hn : #S using Nat.strong_induction_on generalizing ends S with
  | _ n ih =>
  subst hn
  have hsub : ∀ (ends'' : E → Sym2 V) (S' : Finset E), (if _ : #S' < #S then linearMsf k ends'' S'
      else boruvkaMsf ends'' S').eval (LEQuery.keyOracle w) = msf ends'' w S' := by
    intro ends'' S'
    split
    · exact ih _ ‹_› _ _ rfl
    · exact eval_boruvkaMsf ends'' S' hw
  have hexact : (Config.derandomized 32 (by norm_num) fun (ends'' : E → Sym2 V) (S' : Finset E) =>
      if _ : #S' < #S then linearMsf k ends'' S' else boruvkaMsf ends'' S').ExactMsf w :=
    (Config.exactMsf_iff _ _).2 hsub
  rw [linearMsf]
  simp only [FreeM.eval_bind]
  set r := (boruvka ends S k).eval (LEQuery.keyOracle w) with hr
  rw [msf_eq_union_boruvka ends S k w hw hr.symm]
  have hrest := (isContraction_boruvka ends S k (LEQuery.keyOracle w))
  rw [← hr] at hrest
  split
  · next h =>
    rw [h, subset_empty.1 (msf_subset w), union_empty, FreeM.eval_pure]
  · set ends' := Sym2.map r.proj ∘ ends
    have hX : ∀ e ∈ r.rest, ∀ v ∈ ends' e, v ∈ support ends' r.rest := fun e he v hv =>
      mem_support.2 ⟨e, he, hrest.not_isDiag e he, hv⟩
    have hs := sound_certificate hw hexact _ (Instance.wellFormed_root hX)
    have hF := hs.forest_acyclic
    have hFS := hs.forest_subset
    rw [show (Instance.root (support ends' r.rest) ends' r.rest).ends = ends' from
      funext (Instance.root_ends _ _ _)] at hF
    rw [Instance.root_edges] at hFS
    simp only [FreeM.eval_bind, FreeM.eval_pure, hsub]
    rw [eval_unsupportedEdges hw hF, msf_union_unsupported w hw hFS]

/-! ### The comparison count -/

/-- The constant `C` of Lemma 3.1 for `γ = 32`
(`Cslib.Query.Certificate.certificate_derandomized_accounting`): the certificate procedure
leaves `|F| + |U(F)| + ∑ |E_i| ≤ 8 m / 32 + C √(m n)` edges. -/
private noncomputable def certC : ℝ :=
  Classical.choose (certificate_derandomized_accounting 32 (by norm_num))

private theorem exists_steps : ∃ k : ℕ, 32 * certC ^ 2 ≤ 2 ^ k :=
  (pow_unbounded_of_one_lt _ (by norm_num : (1 : ℝ) < 2)).imp fun _ h => h.le

/-- A step in the proof of Theorem 4.1 of [KhannaPuttermanSong2026] (#8325): **the number of
Borůvka steps** of Algorithm 2, a `k` with `32 C² ≤ 2 ^ k`, where `C` is the constant of Lemma 3.1
for `γ = 32` (`Cslib.Query.Certificate.certificate_derandomized_accounting`). The paper chooses
`k` with `C_{1/8} 2^{(1-k)/2} ≤ 3/8` (§4, p. 25); here `32 C² ≤ 2 ^ k` gives
`C √(m · 2m / 2 ^ k) ≤ m / 4`, which with `8 m / γ = m / 4` bounds the exact calls by `m / 2`
edges. -/
noncomputable def linearMsfSteps : ℕ :=
  Classical.choose exists_steps

private theorem linearMsfSteps_spec : 32 * certC ^ 2 ≤ 2 ^ linearMsfSteps :=
  Classical.choose_spec exists_steps

/-- With `32 C² ≤ 2 ^ k`, the exact calls of Algorithm 2 on `m` edges have at most `m / 2` edges:
`8 ρ / 32 + C √(ρ x) ≤ m / 2` when `ρ ≤ m` and `2 ^ k x ≤ 2 m`. -/
private theorem bound_le_half {C ρ x m : ℝ} {k : ℕ} (hk : 32 * C ^ 2 ≤ 2 ^ k) (hρ0 : 0 ≤ ρ)
    (hρ : ρ ≤ m) (hx0 : 0 ≤ x) (hx : 2 ^ k * x ≤ 2 * m) :
    8 * ρ / 32 + C * √(ρ * x) ≤ m / 2 := by
  have hm : 0 ≤ m := hρ0.trans hρ
  have hs := Real.sq_sqrt (mul_nonneg hρ0 hx0)
  have hs0 := Real.sqrt_nonneg (ρ * x)
  have hC : C * √(ρ * x) ≤ m / 4 := by
    rcases le_or_gt C 0 with hC | hC
    · nlinarith
    · have h2k : (0 : ℝ) < 2 ^ k := by positivity
      -- `32 C² ρ x ≤ 2 ^ k ρ x ≤ 2 m²`
      have h1 : 32 * C ^ 2 * (ρ * x) ≤ 2 * m * m := by
        have := mul_le_mul_of_nonneg_right hk (mul_nonneg hρ0 hx0)
        nlinarith [mul_le_mul_of_nonneg_left hx hρ0]
      nlinarith [sq_nonneg (C * √(ρ * x) - m / 4)]
  linarith

open scoped Classical in
/-- A step in the proof of Theorem 4.1 of [KhannaPuttermanSong2026] (#8325): **the comparison
count of Algorithm 2** (§4, pp. 25–26). With `k = Cslib.Query.linearMsfSteps` Borůvka steps,
`Cslib.Query.linearMsf` makes at most `D |S|` comparisons for distinct weights, for one absolute
constant `D`. By strong induction on `|S|`: every exact call has at most `|S| / 2` edges in all,
so the knot's guard never fails, and `T(m) ≤ c m + 2 c (m / 2)`. -/
theorem countQueries_linearMsf_le : ∃ D : ℝ, ∀ {V E W : Type} [DecidableEq V] [DecidableEq E]
    [LinearOrder W] (ends : E → Sym2 V) (S : Finset E) (w : E → W), Function.Injective w →
    ((linearMsf linearMsfSteps ends S).countQueries (LEQuery.keyOracle w) : ℝ) ≤ D * #S := by
  obtain ⟨C', hacc⟩ := Classical.choose_spec (certificate_derandomized_accounting 32
    (by norm_num))
  set k := linearMsfSteps
  set c : ℝ := 2 * k + |C'| + 22
  have hc : 0 ≤ c := by positivity
  refine ⟨2 * c, fun {V E W} _ _ _ ends S w hw => ?_⟩
  induction hn : #S using Nat.strong_induction_on generalizing ends S with
  | _ n ih =>
  subst hn
  have hexact : (Config.derandomized 32 (by norm_num) fun (ends'' : E → Sym2 V) (S' : Finset E) =>
      if _ : #S' < #S then linearMsf k ends'' S' else boruvkaMsf ends'' S').ExactMsf w := by
    refine (Config.exactMsf_iff _ _).2 fun ends'' S' => ?_
    simp only [Config.derandomized_msfSub]
    split
    · exact eval_linearMsf k hw _ _
    · exact eval_boruvkaMsf _ _ hw
  rw [linearMsf]
  simp only [FreeM.countQueries_bind]
  set r := (boruvka ends S k).eval (LEQuery.keyOracle w) with hr
  have hB := countQueries_boruvka_le ends S k (LEQuery.keyOracle w)
  have hm0 : (0 : ℝ) ≤ #S := Nat.cast_nonneg _
  split
  · simp only [FreeM.countQueries_pure, add_zero]
    have : ((2 * k * #S : ℕ) : ℝ) ≤ 2 * c * #S := by
      push_cast
      nlinarith [abs_nonneg C']
    exact (Nat.cast_le.2 hB).trans this
  · next hne =>
    set ends' := Sym2.map r.proj ∘ ends
    set X := support ends' r.rest
    set msfSub := fun (ends'' : E → Sym2 V) (S' : Finset E) =>
      if _ : #S' < #S then linearMsf k ends'' S' else boruvkaMsf ends'' S' with hmsfSub
    have hrest := isContraction_boruvka ends S k (LEQuery.keyOracle w)
    rw [← hr] at hrest
    have hX : ∀ e ∈ r.rest, ∀ v ∈ ends' e, v ∈ X := fun e he v hv =>
      mem_support.2 ⟨e, he, hrest.not_isDiag e he, hv⟩
    obtain ⟨hsize, hcost, -⟩ := hacc msfSub w X ends' r.rest hw hexact hX
      (card_support_le _ _)
    have hs := sound_certificate hw hexact _ (Instance.wellFormed_root hX)
    set F := ((certificate (Config.derandomized 32 (by norm_num) msfSub)
      (Instance.root X ends' r.rest)).eval (LEQuery.keyOracle w)).forest
    have hF := hs.forest_acyclic
    have hFS := hs.forest_subset
    rw [show (Instance.root X ends' r.rest).ends = ends' from
      funext (Instance.root_ends _ _ _)] at hF
    rw [Instance.root_edges] at hFS
    set U := unsupported ends' w F r.rest
    -- the sizes
    have hρ : #r.rest ≤ #S := card_le_card hrest.rest_subset
    have hρF : #F ≤ #r.rest := card_le_card hFS
    have hxk : 2 ^ k * #X ≤ 2 * #S := by
      have h₁ := card_support_boruvka_le ends S k (LEQuery.keyOracle w) hr.symm
      exact (Nat.mul_le_mul_left _ h₁).trans ((Nat.mul_div_le _ _).trans (card_support_le _ _))
    have hhalf := bound_le_half (C := Classical.choose (certificate_derandomized_accounting 32
      (by norm_num))) linearMsfSteps_spec (Nat.cast_nonneg #r.rest) (Nat.cast_le.2 hρ)
      (Nat.cast_nonneg #X) (by exact_mod_cast hxk)
    have hpos : 0 < #S := card_pos.2 (by
      obtain ⟨e, he⟩ := nonempty_iff_ne_empty.2 hne
      exact ⟨e, hrest.rest_subset he⟩)
    have hlt : (#S : ℝ) / 2 < #S := by
      have : (0 : ℝ) < #S := by exact_mod_cast hpos
      linarith
    set tot := ((calls (Config.derandomized 32 (by norm_num) msfSub) (LEQuery.keyOracle w)
      (Instance.root X ends' r.rest)).map fun c => ((msfInputs (Config.derandomized 32
        (by norm_num) msfSub) (LEQuery.keyOracle w) c).map fun S' => (#S' : ℝ)).sum).sum
    have htot0 : 0 ≤ tot := List.sum_nonneg fun y hy => by
      obtain ⟨_, -, rfl⟩ := List.mem_map.1 hy
      exact List.sum_nonneg fun z hz => by obtain ⟨_, -, rfl⟩ := List.mem_map.1 hz; positivity
    simp only [Nat.cast_ofNat] at hsize
    -- every exact call of the certificate procedure has fewer than `|S|` edges
    have hin : ∀ cl ∈ calls (Config.derandomized 32 (by norm_num) msfSub) (LEQuery.keyOracle w)
        (Instance.root X ends' r.rest), ∀ S' ∈ msfInputs (Config.derandomized 32 (by norm_num)
          msfSub) (LEQuery.keyOracle w) cl, ((msfSub cl.ends S').countQueries
            (LEQuery.keyOracle w) : ℝ) ≤ 2 * c * #S' := by
      intro cl hc S' hS'
      have hle : (#S' : ℝ) ≤ tot := by
        refine (List.single_le_sum (fun x hx => ?_) _
          (List.mem_map_of_mem (f := fun S' => (#S' : ℝ)) hS')).trans
          (List.single_le_sum (fun x hx => ?_) _ (List.mem_map_of_mem
            (f := fun cl => ((msfInputs (Config.derandomized 32 (by norm_num) msfSub)
              (LEQuery.keyOracle w) cl).map fun S' => (#S' : ℝ)).sum) hc))
        · obtain ⟨_, -, rfl⟩ := List.mem_map.1 hx; positivity
        · obtain ⟨_, -, rfl⟩ := List.mem_map.1 hx
          exact List.sum_nonneg fun y hy => by obtain ⟨_, -, rfl⟩ := List.mem_map.1 hy; positivity
      have h' : #S' < #S := by
        have : (#S' : ℝ) < #S := by
          have : (0 : ℝ) ≤ #F + #U := by positivity
          linarith
        exact_mod_cast this
      simp only [hmsfSub, h', ↓reduceDIte]
      exact ih _ h' _ _ rfl
    have hcalls := List.sum_le_sum fun cl hc => List.sum_le_sum fun S' hS' => hin cl hc S' hS'
    simp only [List.sum_map_mul_left] at hcalls
    -- the final exact call has fewer than `|S|` edges
    have hFU : (#(F ∪ U) : ℝ) ≤ #F + #U := by exact_mod_cast card_union_le F U
    have hfin : #(F ∪ U) < #S := by
      have : (#(F ∪ U) : ℝ) < #S := by linarith
      exact_mod_cast this
    have hfinal := ih _ hfin ends' (F ∪ U) rfl
    have hun := countQueries_unsupportedEdges_le (w := w) hF r.rest
    simp only [FreeM.countQueries_bind, FreeM.countQueries_pure, add_zero]
    rw [eval_unsupportedEdges hw hF, dite_eq_left_of_eq_true (eq_true hfin)]
    push_cast
    have hC' : C' * #r.rest ≤ |C'| * #S :=
      (mul_le_mul_of_nonneg_right (le_abs_self C') (Nat.cast_nonneg _)).trans
        (mul_le_mul_of_nonneg_left (Nat.cast_le.2 hρ) (abs_nonneg _))
    have hB' : ((2 * k * #S : ℕ) : ℝ) = 2 * k * #S := by push_cast; ring
    have hun' : ((16 * #F + 6 * #r.rest : ℕ) : ℝ) ≤ 22 * #S := by
      push_cast
      have : (#F : ℝ) ≤ #S := by exact_mod_cast hρF.trans hρ
      have : (#r.rest : ℝ) ≤ #S := by exact_mod_cast hρ
      linarith
    have h1 := (Nat.cast_le (α := ℝ)).2 hB
    have h2 := (Nat.cast_le (α := ℝ)).2 hun
    have h3 : 2 * c * (#(F ∪ U) : ℝ) ≤ 2 * c * (#F + #U) :=
      mul_le_mul_of_nonneg_left hFU (by positivity)
    have h4 : 2 * c * (#F + #U + tot) ≤ 2 * c * (#S / 2) :=
      mul_le_mul_of_nonneg_left (hsize.trans hhalf) (by positivity)
    rw [hB'] at h1
    nlinarith

/-! ### Theorem 4.1 -/

/-- **Theorem 4.1 of [KhannaPuttermanSong2026]** (§4, p. 25): the deterministic comparison
(decision-tree) complexity of minimum spanning forests is linear, `T*(m, n) = O(m)`. There is one
absolute constant `C` such that for every finite multigraph, given by `ends : E → Sym2 V` and its
edge set `S`, there is a comparison program `p` that, for every assignment `w` of distinct weights
to the edges, computes the minimum spanning forest of `S` with at most `C · |S|` comparisons.

How the statement maps to the source:

* **The comparison model.** `p : FreeM (LEQuery E) (Finset E)` is a decision tree whose internal
  nodes compare two edges, `w a ≤ w b`, and whose leaves are labelled by edge sets; `p.eval`
  follows the path that the answers of the oracle `LEQuery.keyOracle w` select, and
  `p.countQueries` counts the comparisons on that path, which is at most `C · |S|` for every
  assignment of distinct weights. Branches of `p` that no such assignment reaches may be deeper,
  but they can be pruned (replaced by an arbitrary leaf) without changing the output on any
  distinct-weight assignment, so the minimum depth of a correct comparison tree for the graph is
  at most `C · |S|`, which is what `T*` measures (p. 5).
  Computation between comparisons is free, as in the decision-tree model: the program's
  exhaustive searches for a schedule (Lemma 3.11) and a separating set (Claim 3.12) cost nothing.
* **Quantifiers and non-uniformity.** `C` comes first and is absolute. The program may depend on
  the graph (`p` is chosen after `ends` and `S`), but not on the weights (`w` and its type `W` are
  chosen after `p`), as in the definition of `T*(m, n) = max_H min_T depth(T)` on p. 5. In fact the
  witness is one program family, `Cslib.Query.linearMsf Cslib.Query.linearMsfSteps ends S`.
* **Graphs.** The paper's `T*` ranges over simple graphs with `m` edges and `n` vertices,
  including disconnected ones; here `ends` is any multigraph, with parallel edges and self-loops
  allowed, and the bound depends only on `m = |S|`, so it covers every `n`. Isolated vertices
  play no role.
* **Weights.** The weights are an injective `w : E → W` into any linear order: the paper assumes
  distinct weights, with ties broken by edge index (§2, p. 11). Taking `W : Type` (universe 0)
  is no restriction: injective weights into a linear order in any universe induce, by
  `LinearOrder.lift'`, a linear order on `E` whose comparison oracle gives the same answers, so
  the same path of `p` and the same `msf`. Neither is injectivity on all of `E`, rather than on
  `S`: `E` can be taken to be the graph's edge set. The minimum spanning forest is
  `Cslib.Multigraph.msf`, the edges whose ends the strictly lighter edges do not join; by
  `Cslib.Multigraph.isSpanningForest_msf` and `Cslib.Multigraph.sum_msf_le` it is a spanning
  forest of least total weight (`Cslib.Query.linearMsf_isSpanningForest_and_sum_le`).

**Not proved: running time.** Theorem 1.1 and Corollary 4.2 of the paper (a deterministic
`O(m + n)`-time algorithm) combine this theorem with Pettie and Ramachandran's optimal algorithm
(JACM 2002, Theorem 5.8, the paper's Theorem 2.6), which is not formalized; it stays open in
#8325. Nothing here is a running-time claim.

The proof assembles Algorithm 2 (`Cslib.Query.linearMsf`): its correctness for every number of
Borůvka steps (`Cslib.Query.eval_linearMsf`) and its comparison count by strong induction on the
number of edges (`Cslib.Query.countQueries_linearMsf_le`). -/
theorem exists_msf_program_countQueries_le : ∃ C : ℕ, ∀ {V E : Type} [DecidableEq V]
    [DecidableEq E] (ends : E → Sym2 V) (S : Finset E), ∃ p : FreeM (LEQuery E) (Finset E),
      ∀ {W : Type} [LinearOrder W] (w : E → W), Function.Injective w →
        p.eval (LEQuery.keyOracle w) = msf ends w S ∧
          p.countQueries (LEQuery.keyOracle w) ≤ C * #S := by
  obtain ⟨D, hD⟩ := countQueries_linearMsf_le
  refine ⟨⌈D⌉₊, fun {V E} _ _ ends S => ⟨linearMsf linearMsfSteps ends S,
    fun {W} _ w hw => ⟨eval_linearMsf _ hw ends S, ?_⟩⟩⟩
  have h := (hD ends S w hw).trans
    (mul_le_mul_of_nonneg_right (Nat.le_ceil D) (Nat.cast_nonneg _))
  exact_mod_cast h

/-- A step in the proof of Theorem 4.1 of [KhannaPuttermanSong2026] (#8325): **optimality of the
output of Algorithm 2.** For distinct weights in an ordered additive monoid,
`Cslib.Query.linearMsf` returns a spanning forest of `S` of least total weight: the minimum
spanning forest of Theorem 4.1 is a minimum-weight spanning forest, by
`Cslib.Multigraph.isSpanningForest_msf` and `Cslib.Multigraph.sum_msf_le`. -/
theorem linearMsf_isSpanningForest_and_sum_le (k : ℕ) {W : Type} [LinearOrder W]
    [AddCommMonoid W] [IsOrderedAddMonoid W] {w : E → W} (hw : Function.Injective w)
    (ends : E → Sym2 V) (S : Finset E) :
    IsSpanningForest ends S ((linearMsf k ends S).eval (LEQuery.keyOracle w)) ∧
      ∀ F, IsSpanningForest ends S F →
        ∑ e ∈ (linearMsf k ends S).eval (LEQuery.keyOracle w), w e ≤ ∑ e ∈ F, w e := by
  rw [eval_linearMsf k hw]
  exact ⟨isSpanningForest_msf w hw, fun _ hF => sum_msf_le w hw hF⟩

end Cslib.Query
